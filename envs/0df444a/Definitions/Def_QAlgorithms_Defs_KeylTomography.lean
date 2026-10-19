-- Prove2me | Definitions.Def_QAlgorithms_Defs_KeylTomography
-- name    : QAlgorithms_Defs_KeylTomography
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:44:06.563572+00:00
-- url     : https://prove2.me/theorems/9590d573-b5b6-4f9d-b212-31ae5235cff6
-- title:
--   KeylTomography
-- statement:
--   KeylTomography
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\KeylTomography.lean

import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open MeasureTheory
open scoped Matrix ENNReal Matrix.Norms.L2Operator

namespace QAlgorithms.Tomography

/-- A public orthonormal coordinate system for the constructed Schur factor.
It is fixed by the shape, independently of the unknown state
(1508.01907 pp.4,7, V_lambda^d). -/
def schurCoordinates {d n : ℕ} (lambda : Schur.Partition d n) :=
  stdOrthonormalBasis ℂ (Schur.schurModule lambda)

/-- The polynomial representation in those public orthonormal coordinates,
including singular matrices (1508.01907 pp.4,7-8). -/
def schurActionMatrix {d n : ℕ} (lambda : Schur.Partition d n)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (Module.finrank ℂ (Schur.schurModule lambda)))
      (Fin (Module.finrank ℂ (Schur.schurModule lambda))) ℂ :=
  Matrix.of fun i j => inner ℂ (schurCoordinates lambda i)
    (Schur.polynomialRepresentation lambda A (schurCoordinates lambda j))

/-- Pointwise density of Keyl's highest-weight POVM, relative to probability
Haar: dim(V_lambda^d) pi_lambda(U)|T_lambda><T_lambda|pi_lambda(U) dagger.
The representation and vector are computed from the public shape
(1508.01907 p.7, definition of M(F)). -/
def keylPointDensity {d n : ℕ} (lambda : Schur.Partition d n)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (Fin (Module.finrank ℂ (Schur.schurModule lambda)))
      (Fin (Module.finrank ℂ (Schur.schurModule lambda))) ℂ :=
  (Module.finrank ℂ (Schur.schurModule lambda) : ℂ) •
    pureDensity ((schurCoordinates lambda).repr
      (Schur.polynomialRepresentation lambda (U : Matrix _ _ ℂ)
        (Schur.highestWeightVector lambda)))

/-- Keyl's operator assigned to a Borel event F: the restricted integral of
its computed highest-weight density, with probability Haar reference
(1508.01907 pp.7-8, M(F)). Normalization is a representation-theoretic
verification obligation, not a premise or an accuracy certificate. -/
def keylDensity {d n : ℕ} (lambda : Schur.Partition d n)
    (F : Set (Matrix.unitaryGroup (Fin d) ℂ)) :
    Matrix (Fin (Module.finrank ℂ (Schur.schurModule lambda)))
      (Fin (Module.finrank ℂ (Schur.schurModule lambda))) ℂ :=
  ∫ U in F, keylPointDensity lambda U ∂Schur.unitaryHaar d

/-- The actual conditional Born distribution from Keyl's second-stage POVM
on pi_lambda(rho)/Tr(pi_lambda(rho)). The zero-probability Schur branch is
completed by probability Haar, since its joint weight is zero
(1508.01907 pp.7-8, Eqs.(10)-(11)). The normalizer lies outside pi_lambda;
the displayed scalar-inside-pi typo on p.8 is read using the state on p.7. -/
def keylConditionalLaw {d n : ℕ} (_hd : 0 < d) (_hn : 0 < n)
    (lambda : Schur.Partition d n) (rho : Matrix (Fin d) (Fin d) ℂ)
    (_density : IsDensityMatrix rho) : Measure (Matrix.unitaryGroup (Fin d) ℂ) :=
  let sigma := schurActionMatrix lambda rho
  if sigma.trace.re = 0 then Schur.unitaryHaar d else
    (Schur.unitaryHaar d).withDensity (fun U =>
      ENNReal.ofReal (effectProb (keylPointDensity lambda U) ((sigma.trace.re : ℂ)⁻¹ • sigma)))

/-- An empty second-stage outcome event has zero operator, including for
singular true states (1508.01907 p.7, operator measure M). -/
example {d n : ℕ} (lambda : Schur.Partition d n) : keylDensity lambda ∅ = 0 := by
  simp [keylDensity]


/-- Generalized power Delta_lambda(Z): leading principal minors to the
padded row differences lambda_k-lambda_(k+1). PSD inputs have real
nonnegative minors (1508.01907 p.8, Notation 4.1). -/
def keylGeneralizedPower {d n : ℕ} (lambda : Schur.Partition d n)
    (Z : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  ∏ k : Fin d,
    ((Z.submatrix (fun i : Fin (k.val+1) => (⟨i.val,by omega⟩ : Fin d))
      (fun i : Fin (k.val+1) => (⟨i.val,by omega⟩ : Fin d))).det) ^
      (lambda.val.rowLen k.val-lambda.val.rowLen (k.val+1))

/-- Complete two-stage Keyl Born law. Multiplying weak weight
dim(Sp_lambda) s_lambda(alpha) by the conditional Keyl density cancels
s_lambda(alpha), giving dim(Sp_lambda) dim(V_lambda)
Delta_lambda(U dagger rho U). This is also the scalar Born density of the
transported Specht-identity tensor highest-weight POVM. No conditional
division is used on a zero-weight shape, and no true-state law or
correctness certificate is supplied (1508.01907 pp.6-8, Eqs.(8)-(12)). -/
def keylJointLaw {d n : ℕ} (_hd : 0 < d) (_hn : 0 < n)
    (rho : Matrix (Fin d) (Fin d) ℂ) (_density : IsDensityMatrix rho) :
    Measure (Schur.Partition d n × Matrix.unitaryGroup (Fin d) ℂ) :=
  (Measure.count.prod (Schur.unitaryHaar d)).withDensity (fun outcome =>
    ENNReal.ofReal ((Module.finrank ℂ (Schur.spechtSpace outcome.1) : ℝ) *
      Schur.schurDimension outcome.1 * (keylGeneralizedPower outcome.1
        (star (outcome.2 : Matrix _ _ ℂ) * rho * (outcome.2 : Matrix _ _ ℂ))).re))

/-- Expected Frobenius-squared loss under the computed two-stage law, in
nonnegative extended reals. A nonintegrable loss cannot default to zero;
finite bounded-loss and normalization identities remain supporting work
(1508.01907 pp.2,8,10-11, Theorem 1.2). -/
def keylSquaredRisk {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (rho : Matrix (Fin d) (Fin d) ℂ) (density : IsDensityMatrix rho) : ℝ≥0∞ :=
  ∫⁻ outcome, ENNReal.ofReal
    (frobNorm (Schur.estimate hd hn outcome.1 outcome.2-rho)^2)
      ∂keylJointLaw hd hn rho density

/-- Zero exponents give generalized power one, even on a singular matrix
(1508.01907 p.8, Notation 4.1). -/
example {d : ℕ} (lambda : Schur.Partition d 0)
    (hrows : ∀ i, lambda.val.rowLen i = 0) (Z : Matrix (Fin d) (Fin d) ℂ) :
    keylGeneralizedPower lambda Z = 1 := by simp [keylGeneralizedPower,hrows]

/-- The scalar one-copy report and true state are [1], with zero risk
(1508.01907 p.2, Theorem 1.2). -/
example (rho : Matrix (Fin 1) (Fin 1) ℂ) (density : IsDensityMatrix rho)
    (hrows : ∀ lambda : Schur.Partition 1 1, lambda.val.rowLen 0 = 1) :
    keylSquaredRisk (n:=1) (by omega) (by omega) rho density = 0 := by
  have hrho : rho = 1 := by
    ext i j
    have ht := density.2
    fin_cases i; fin_cases j
    simpa [Matrix.trace,Matrix.diag] using ht
  have he : ∀ lambda : Schur.Partition 1 1, ∀ U : Matrix.unitaryGroup (Fin 1) ℂ,
      Schur.estimate (by omega) (by omega) lambda U = 1 := by
    intro lambda U
    have hdiag : Schur.normalizedDiagram (by omega) (by omega) lambda = 1 := by
      ext i j
      fin_cases i; fin_cases j
      simp [Schur.normalizedDiagram,Schur.normalizedRows,hrows]
    rw [Schur.estimate,hdiag,mul_one]
    exact Unitary.mul_star_self_of_mem U.property
  have hz : frobNorm (0 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
    exact @norm_zero (Matrix (Fin 1) (Fin 1) ℂ)
      (@SeminormedAddCommGroup.toSeminormedAddGroup (Matrix (Fin 1) (Fin 1) ℂ)
        (@NormedAddCommGroup.toSeminormedAddCommGroup (Matrix (Fin 1) (Fin 1) ℂ)
          Matrix.frobeniusNormedAddCommGroup))
  simp [keylSquaredRisk,hrho,he,hz]

end QAlgorithms.Tomography


