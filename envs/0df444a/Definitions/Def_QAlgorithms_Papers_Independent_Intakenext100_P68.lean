-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P68
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P68
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T07:26:41.956772+00:00
-- url     : https://prove2.me/theorems/3c3ffae6-9898-4655-8af5-4844ff0f5b5f
-- title:
--   Definitions for Separability Criterion for all bipartite Gaussian States
-- statement:
--   The objects the formalized statements of *Separability Criterion for all bipartite Gaussian States* (arXiv:quant-ph/0104050) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `interleavedJ`: PDF p.1, Eq.(1): J has J_XP=-1 and J_PX=+1.
--   - `Uncertainty`: PDF p.1: the uncertainty inequality A >= iJ, in Loewner order.
--   - `IsCM`: PDF p.1: a CM is real, symmetric and satisfies uncertainty.
--   - `CovarianceBlocks`: PDF p.1, Eq.(2): initial bipartite blocks with a rectangular C.
--   - `covarianceBlockMatrix`: PDF p.1, Eq.(2): the actual real symmetric-block assembly.
--   - `realCovarianceSum`: PDF p.1 [9]: direct sum, retaining the displayed bipartition.
--   - `IsPhysicalCovariance`: PDF p.1, Eq.(2): physical bipartite covariance; symmetry is explicit.
--   - `DominatesLocalCovariances`: PDF pp.1--2, Eq.(3): a local witness inequality, not separability.
--   - `hermitianInverse`: PDF p.4 [11]: spectral Moore--Penrose inverse on the Hermitian domain. Each eigenvalue t is sent to t^{-1}, with 0^{-1}=0. The off-domain zero is irrelevant to the Hermitian/PSD inputs in all statements.
--   - `updateX`: PDF p.2, Eq.(4): X=C(B-iJ)^+ C^T, including singular B-iJ.
--   - `covarianceStep`: PDF p.2, Eq.(4): nonphysical inputs give zero; physical inputs follow (4a,b). The output split is always n|n, even when the input split is n|m.
--   - `tail`: PDF p.2: tail g k is gamma_(k+1), constructed only from g=gamma_0.
--   - `euclideanOpNorm`: PDF p.4 [12]: Euclidean induced operator norm, not the matrix infinity norm.
--   - `lowerWitness`: PDF p.2, Eq.(6): the constructed acceptance witness L=A-||C||_op I.
--   - `secondWitness`: PDF p.2, corrected Eq.(5): B-C^T(A-U)^+C. Printed: B-C(A-U)^(-1)C^T. Changed: transpose the first C, not the last. Why: the print is ill-typed for n != m; Prop.1's proof and Appendix Lemma 1(iii) use this corrected Schur complement.
--   - `averageWitness`: PDF p.2, Cor.1: average using the constructed second witness.
--   - `recoverFirst`: PDF p.2 following Thm.1: descend from gamma_(k+1) to gamma_1, using Cor.1 at the preceding matrix at each recursive call.
--   - `bipartiteGroupedIndex`: PDF pp.1,4 [8]: accepted grouped Weyl coordinates to the source's two interleaved local quadrature lists; this is a permutation, without rescaling.
--   - `HasGaussianCovariance`: PDF pp.1,4 [8]: actual Gaussian density with symmetric physical covariance and arbitrary mean. The accepted Weyl convention has vacuum I and hbar=1. Summability guards the iterated trace/Weyl pairing. The defective frozen HasBipartiteMoments predicate is not used.
--   - `SeparableCM`: PDF pp.1--2: existence of an actual separable Gaussian density, independent of local witness inequality (3).
--   - `momentumFlip`: PDF pp.1--3: partial transposition reverses the second party's P coordinates.
--   - `partialTransposeCovariance`: PDF pp.1--3: covariance of the partially transposed Gaussian operator.
-- source:
--   Separability Criterion for all bipartite Gaussian States, arXiv:quant-ph/0104050v1, https://arxiv.org/abs/quant-ph/0104050v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19

/-!
Giedke--Kraus--Lewenstein--Cirac, arXiv:quant-ph/0104050v1, PDF pp.1--4.
Interleaved quadratures, doubled covariance, vacuum I. All inequalities below
are Loewner inequalities. The initial n|m matrix is separate from the n|n tail:
`tail g k` denotes gamma_(k+1). Full oscillator states and trace-norm separability
come from the pinned accepted library. No moments predicate from P47 is used.
Exact accepted coordinate, covariance, complexification and occupation definitions
are imported. Distinct Gaussian objects use descriptive names: accepted short-name
matches for Blocks, Physical, Dominates and step denote unrelated objects.
Compilation and independent moderation are pending the separate batch handoff.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsSeparable IsBarycenter productCoeff)

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

/-- PDF p.1, Eq.(1): J has J_XP=-1 and J_PX=+1. -/
def interleavedJ (n : ℕ) : Cov n :=
  fun i j => if i.1 = j.1 then
    if i.2 = j.2 then 0 else if i.2 = 0 then -1 else 1
  else 0

/-- PDF p.1: the uncertainty inequality A >= iJ, in Loewner order. -/
def Uncertainty {n : ℕ} (A : Cov n) : Prop :=
  (complexify A - Complex.I • complexify (interleavedJ n)).PosSemidef

/-- PDF p.1: a CM is real, symmetric and satisfies uncertainty. -/
def IsCM {n : ℕ} (A : Cov n) : Prop := A.transpose = A ∧ Uncertainty A

/-- PDF p.1, Eq.(2): initial bipartite blocks with a rectangular C. -/
structure CovarianceBlocks (n m : ℕ) where
  A : Cov n
  B : Cov m
  C : Matrix (QuadratureIndex n) (QuadratureIndex m) ℝ

/-- PDF p.1, Eq.(2): the actual real symmetric-block assembly. -/
def covarianceBlockMatrix {n m : ℕ} (g : CovarianceBlocks n m) :
    Matrix (QuadratureIndex n ⊕ QuadratureIndex m) (QuadratureIndex n ⊕ QuadratureIndex m) ℝ :=
  Matrix.fromBlocks g.A g.C g.C.transpose g.B

/-- PDF p.1 [9]: direct sum, retaining the displayed bipartition. -/
def realCovarianceSum {I J : Type} [DecidableEq I] [DecidableEq J]
    (A : Matrix I I ℝ) (B : Matrix J J ℝ) : Matrix (I ⊕ J) (I ⊕ J) ℝ :=
  Matrix.fromBlocks A 0 0 B

/-- PDF p.1, Eq.(2): physical bipartite covariance; symmetry is explicit. -/
def IsPhysicalCovariance {n m : ℕ} (g : CovarianceBlocks n m) : Prop :=
  (covarianceBlockMatrix g).transpose = covarianceBlockMatrix g ∧
    (complexify (covarianceBlockMatrix g) -
      Complex.I • complexify (realCovarianceSum (interleavedJ n) (interleavedJ m))).PosSemidef

/-- PDF pp.1--2, Eq.(3): a local witness inequality, not separability. -/
def DominatesLocalCovariances {n m : ℕ} (g : CovarianceBlocks n m) (U : Cov n) (V : Cov m) : Prop :=
  (covarianceBlockMatrix g - realCovarianceSum U V).PosSemidef

/-- PDF p.4 [11]: spectral Moore--Penrose inverse on the Hermitian domain.
Each eigenvalue t is sent to t^{-1}, with 0^{-1}=0. The off-domain zero
is irrelevant to the Hermitian/PSD inputs in all statements. -/
def hermitianInverse {K I : Type} [RCLike K] [Fintype I] [DecidableEq I]
    (A : Matrix I I K) : Matrix I I K :=
  if h : A.IsHermitian then h.cfc (fun t : ℝ => t⁻¹) else 0

/-- PDF p.2, Eq.(4): X=C(B-iJ)^+ C^T, including singular B-iJ. -/
def updateX {n m : ℕ} (g : CovarianceBlocks n m) : Matrix (QuadratureIndex n) (QuadratureIndex n) ℂ :=
  complexify g.C *
    hermitianInverse (complexify g.B - Complex.I • complexify (interleavedJ m)) *
    complexify g.C.transpose

/-- PDF p.2, Eq.(4): nonphysical inputs give zero; physical inputs follow (4a,b).
The output split is always n|n, even when the input split is n|m. -/
def covarianceStep {n m : ℕ} (g : CovarianceBlocks n m) : CovarianceBlocks n n :=
  if IsPhysicalCovariance g then
    { A := g.A - (updateX g).map Complex.re
      B := g.A - (updateX g).map Complex.re
      C := -(updateX g).map Complex.im }
  else { A := 0, B := 0, C := 0 }

/-- PDF p.2: tail g k is gamma_(k+1), constructed only from g=gamma_0. -/
def tail {n m : ℕ} (g : CovarianceBlocks n m) : ℕ → CovarianceBlocks n n
  | 0 => covarianceStep g
  | k + 1 => covarianceStep (tail g k)

/-- PDF p.4 [12]: Euclidean induced operator norm, not the matrix infinity norm. -/
def euclideanOpNorm {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (C : Matrix I J ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin C).toContinuousLinearMap‖

/-- PDF p.2, Eq.(6): the constructed acceptance witness L=A-||C||_op I. -/
def lowerWitness {n : ℕ} (g : CovarianceBlocks n n) : Cov n :=
  g.A - euclideanOpNorm g.C • (1 : Cov n)

/-- PDF p.2, corrected Eq.(5): B-C^T(A-U)^+C.
Printed: B-C(A-U)^(-1)C^T. Changed: transpose the first C, not the last.
Why: the print is ill-typed for n != m; Prop.1's proof and Appendix
Lemma 1(iii) use this corrected Schur complement. -/
def secondWitness {n m : ℕ} (g : CovarianceBlocks n m) (U : Cov n) : Cov m :=
  g.B - g.C.transpose * hermitianInverse (g.A - U) * g.C

/-- PDF p.2, Cor.1: average using the constructed second witness. -/
def averageWitness {n : ℕ} (g : CovarianceBlocks n n) (U : Cov n) : Cov n :=
  (1 / 2 : ℝ) • (U + secondWitness g U)

/-- PDF p.2 following Thm.1: descend from gamma_(k+1) to gamma_1,
using Cor.1 at the preceding matrix at each recursive call. -/
def recoverFirst {n m : ℕ} (g : CovarianceBlocks n m) : ℕ → Cov n → Cov n
  | 0, U => U
  | k + 1, U => recoverFirst g k (averageWitness (tail g k) U)

/-- PDF pp.1,4 [8]: accepted grouped Weyl coordinates to the source's two
interleaved local quadrature lists; this is a permutation, without rescaling. -/
def bipartiteGroupedIndex {n m : ℕ} :
    (Fin n ⊕ Fin m) ⊕ (Fin n ⊕ Fin m) → QuadratureIndex n ⊕ QuadratureIndex m
  | Sum.inl (Sum.inl i) => Sum.inl (i, 0)
  | Sum.inl (Sum.inr j) => Sum.inr (j, 0)
  | Sum.inr (Sum.inl i) => Sum.inl (i, 1)
  | Sum.inr (Sum.inr j) => Sum.inr (j, 1)

/-- PDF pp.1,4 [8]: actual Gaussian density with symmetric physical covariance
and arbitrary mean. The accepted Weyl convention has vacuum I and hbar=1.
Summability guards the iterated trace/Weyl pairing. The defective frozen
HasBipartiteMoments predicate is not used. -/
def HasGaussianCovariance {n m : ℕ}
    (rho : State (Occupation (Fin n) × Occupation (Fin m))) (g : CovarianceBlocks n m)
    (d : QuadratureIndex n ⊕ QuadratureIndex m → ℝ) : Prop :=
  IsPhysicalCovariance g ∧ ∀ xi : (Fin n ⊕ Fin m) ⊕ (Fin n ⊕ Fin m) → ℝ,
    (∀ u, Summable (fun v => rho.coefficients u v *
      QAlgorithms.Papers.Independent.Claimed50.P47.bipartiteWeyl xi v u)) ∧
    Summable (fun u => ∑' v, rho.coefficients u v *
      QAlgorithms.Papers.Independent.Claimed50.P47.bipartiteWeyl xi v u) ∧
    QAlgorithms.Papers.Independent.Claimed50.P47.bipartiteCharacteristic
      rho.coefficients xi =
    QAlgorithms.Papers.Independent.Claimed50.P47.gaussianStateCharacteristic
      (d ∘ bipartiteGroupedIndex) ((covarianceBlockMatrix g).submatrix bipartiteGroupedIndex bipartiteGroupedIndex) xi

/-- PDF pp.1--2: existence of an actual separable Gaussian density,
independent of local witness inequality (3). -/
def SeparableCM {n m : ℕ} (g : CovarianceBlocks n m) : Prop :=
  ∃ (rho : State (Occupation (Fin n) × Occupation (Fin m))) (d : QuadratureIndex n ⊕ QuadratureIndex m → ℝ),
    HasGaussianCovariance rho g d ∧ IsSeparable rho.coefficients

/-- PDF pp.1--3: partial transposition reverses the second party's P coordinates. -/
def momentumFlip (m : ℕ) : Cov m :=
  Matrix.diagonal (fun i => if i.2 = 0 then 1 else -1)

/-- PDF pp.1--3: covariance of the partially transposed Gaussian operator. -/
def partialTransposeCovariance {n m : ℕ} (g : CovarianceBlocks n m) : CovarianceBlocks n m :=
  { A := g.A
    B := momentumFlip m * g.B * momentumFlip m
    C := g.C * momentumFlip m }

/-! Small definitional sanity checks; source results remain unproved. -/

example : interleavedJ 1 (0, 0) (0, 1) = -1 := by
  norm_num [interleavedJ]

example : interleavedJ 1 (0, 1) (0, 0) = 1 := by
  norm_num [interleavedJ]

example {n m : ℕ} (g : CovarianceBlocks n m) (i j : QuadratureIndex n) :
    covarianceBlockMatrix g (Sum.inl i) (Sum.inl j) = g.A i j := rfl

example {K I : Type} [RCLike K] [Fintype I] [DecidableEq I]
    (A : Matrix I I K) (h : A.IsHermitian) :
    hermitianInverse A = h.cfc (fun t : ℝ => t⁻¹) := by
  simp only [hermitianInverse, dif_pos h]

example {n m : ℕ} (g : CovarianceBlocks n m) (h : ¬ IsPhysicalCovariance g) :
    covarianceStep g = { A := 0, B := 0, C := 0 } := by
  simp only [covarianceStep, if_neg h]

example {n m : ℕ} (g : CovarianceBlocks n m) : tail g 0 = covarianceStep g := rfl

example {n m : ℕ} (g : CovarianceBlocks n m) (U : Cov n) : recoverFirst g 0 U = U := rfl

example {n m : ℕ} (i : Fin n) :
    (bipartiteGroupedIndex (n := n) (m := m)) (Sum.inr (Sum.inl i)) = Sum.inl (i, 1) := rfl

example : momentumFlip 1 (0, 1) (0, 1) = -1 := by
  norm_num [momentumFlip, Matrix.diagonal]

end QAlgorithms.Papers.Independent.Intakenext100.P68


