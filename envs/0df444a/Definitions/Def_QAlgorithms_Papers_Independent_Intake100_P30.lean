-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30
-- name    : QAlgorithms_Papers_Independent_Intake100_P30
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T17:37:43.991694+00:00
-- url     : https://prove2.me/theorems/bd12c8de-5629-4ac1-a9a2-67cfb35cb686
-- title:
--   Definitions for Graphical calculus for Gaussian pure states
-- statement:
--   The objects the formalized statements of *Graphical calculus for Gaussian pure states* (arXiv:1007.0725) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `realPart`: Entrywise real part, PDF p.6, (2.22).
--   - `imagPart`: Entrywise imaginary part, PDF p.6, (2.22).
--   - `ValidGraph`: Physical finite Gaussian graph domain, PDF pp.6,19–20.
--   - `graphCovariance`: Graph covariance, in grouped order and hbar=1, PDF p.6, (2.19).
--   - `targetError`: Fixed-A real nullifier covariance, computed by congruence from Sigma, PDF pp.3–4,8, (2.3),(2.41). The target A need not equal Re Z.
--   - `graphError`: Scalar approximation error, PDF p.8, (2.42).
--   - `graphBlockSymplectic`: Symplecticity in the source's grouped order, PDF p.5, (2.11).
--   - `mobius`: General Gaussian graph update, PDF p.6, (2.24). All theorems using inverse assert denominator invertibility as a conclusion.
--   - `graphLocalMobius`: n-local operation extended by the identity on untouched nodes, p.9 (3.2).
--   - `oneGraph`: One distinguished node and its neighborhood, PDF p.10 (3.9).
--   - `oneAction`: One-node symplectic action, PDF pp.9–10 (3.8)–(3.9).
--   - `graphPhaseMobius`: Phase-plane rotation with the source sign, PDF pp.11,13 (3.17),(4.1).
--   - `phaseError`: Error as a function of local phases, PDF p.13 (4.2).
--   - `phaseHessian`: The Hessian of one-half tr Im Z under phase shifts, PDF p.22 (B15).
--   - `canonicalGraph`: Canonical finite-squeezing graph, PDF p.7 (2.29).
--   - `sechGraph`: The second cluster family, PDF p.7 (2.31).
--   - `hGraph`: H-graph coordinate, PDF p.7 (2.32). This is a matrix definition; the separate Hamiltonian-generation assertion is deferred.
--   - `NormalizedWave`: Actual L2 normalization of a wavefunction, PDF pp.4–6.
--   - `NormalizedGaussian`: Centered Gaussian shape is a quadratic exponential, not a graph tuple; normalization excludes the zero vector, PDF p.6 (2.21).
--   - `HasQuadratureForms`: First and second quadrature form integrability on the concrete Gaussian function domain, PDF pp.5–7. No unbounded CCR operator is made bounded.
--   - `secondMoment`: Ordered second moment as a quadratic form, PDF p.7 (2.27).
--   - `qMoment`: Q=<qq^T>, PDF p.7 (2.27), vacuum Q=I/2.
--   - `qpMoment`: P=<qp^T>, PDF p.7 (2.27), vacuum P=iI/2.
--   - `symQpMoment`: Symmetrized <{q,p^T}>, PDF p.7 (2.27).
--   - `extractedGraph`: Expectation-defined graph; no outer one-half on Q^{-1}P, PDF pp.7,19.
--   - `centeredGraph`: Centered extraction for displaced states, PDF p.11 displacement rule.
--   - `IsGaussianVector`: A normalized centered Gaussian vector in the actual oscillator L2 space.
--   - `GaussianGraphRepresents`: Representation ties graph to actual expectation values on an L2 vector, not to a stipulated matrix-state correspondence, PDF pp.19–20.
--   - `nullifier`: Concrete nullifier or its formal adjoint on smooth functions, PDF p.8.
--   - `complexNullifierCovariance`: Symmetrized complex nullifier covariance, PDF p.8 (2.40). Adjoint coefficients are conjugated; the second form has reversed indices.
--   - `realNullifierCovariance`: Real nullifier quadratic form, PDF p.8 (2.41)–(2.42).
--   - `HasIsotropicMarginals`: Single-mode marginal isotropy in the source's resource sense, PDF p.15 (4.12), not computational efficiency.
--   - `twoEdge`: Two-mode unweighted edge, PDF p.14 (4.7).
--   - `beamRotation`: Beamsplitter convention, PDF p.10 (3.10).
--   - `siegelDiscCoordinate`: Cayley/Siegel-disc coordinate, PDF p.21 (B1); K^{-1} is never used.
--   - `HasSymplecticSpectrum`: Symplectic spectrum with multiplicity: the characteristic polynomial of Sigma Omega is product_j (X^2+sigma_j^2), PDF pp.17–18, (4.35),(4.38). For an empty subsystem the product and characteristic polynomial are both 1.
--   - `FactorsAt`: Pure-wave product structure across one node versus the rest, PDF p.18. The factors are genuine square-integrable functions.
--   - `nodeSpectrum`: One-node symplectic eigenvalue, PDF p.18 (4.41); self-loop excluded.
--   - `gaussianSpectralEntropy`: Entropy of a one-mode Gaussian marginal from its symplectic eigenvalue, PDF p.18 (background entropy characterization). Logarithm base b>1 is a parameter, so no unstated choice of bits versus nats is imposed. At sigma=1/2 the convention 0 log 0=0 gives zero entropy.
--   - `clusterStabilizer`: Concrete ordered finite-squeezing stabilizer X_j(s)Z_j(i eps_j s) product_neighbor Z_l(s), including its nonunit Gaussian scalar, PDF p.23 (C7). Translation is performed after the multiplication factors, as operator order requires; A is hollow in the theorem below.
--   - `passiveA`: Passive-optics nullifier coefficient A=X+i D Y, with row squeezing D on the LEFT, PDF p.23 (C15).
--   - `passiveB`: Passive-optics coefficient B=i D X-Y, PDF p.23 (C16).
--   - `covarianceGraph`: Covariance-based centered graph extraction for a PURE covariance. For the Appendix-D mixed family, first divide the covariance by kappa, PDF pp.7,24. Direct extraction on the mixed covariance would be wrong.
--   - `qConditionedCovariance`: Conditioning covariance on the measured q of the distinguished first mode, retaining both quadratures of every unmeasured mode, Appendix D p.24 in the Section III.D measurement context.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, https://arxiv.org/abs/1007.0725v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

/-!
Menicucci–Flammia–van Loock, arXiv:1007.0725v3. Grouped q,p order,
hbar=1, vacuum covariance I/2. Actual normalized Gaussian functions and L2
vectors are used for state assertions; graph algebra uses the Siegel domain.
Ideal limits are matrix limits, never normalized infinite-squeezing vectors.
Accepted P41 has gaussianWave(u,v) with v=-V in this paper's convention.
Compilation is pending the separate mechanical stage. Explicit deferrals are
in this paper's HARD.md; no deferred result is silently replaced by a lemma.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- Entrywise real part, PDF p.6, (2.22). -/
def realPart {I J : Type*} (Z : Matrix I J ℂ) : Matrix I J ℝ := fun i j => (Z i j).re

/-- Entrywise imaginary part, PDF p.6, (2.22). -/
def imagPart {I J : Type*} (Z : Matrix I J ℂ) : Matrix I J ℝ := fun i j => (Z i j).im

/-- Physical finite Gaussian graph domain, PDF pp.6,19–20. -/
def ValidGraph {I : Type*} [Fintype I] [DecidableEq I] (Z : Matrix I I ℂ) : Prop :=
  Z.IsSymm ∧ (imagPart Z).PosDef

/-- Graph covariance, in grouped order and hbar=1, PDF p.6, (2.19). -/
def graphCovariance {I : Type*} [Fintype I] [DecidableEq I]
    (Z : Matrix I I ℂ) : Matrix (I ⊕ I) (I ⊕ I) ℝ :=
  let U := imagPart Z
  let V := realPart Z
  (1 / 2 : ℝ) • Matrix.fromBlocks U⁻¹ (U⁻¹ * V) (V * U⁻¹) (U + V * U⁻¹ * V)

/-- Fixed-A real nullifier covariance, computed by congruence from Sigma,
PDF pp.3–4,8, (2.3),(2.41). The target A need not equal Re Z. -/
def targetError {I : Type*} [Fintype I] [DecidableEq I]
    (Z : Matrix I I ℂ) (A : Matrix I I ℝ) : Matrix I I ℝ :=
  let S := graphCovariance Z
  S.submatrix Sum.inr Sum.inr - A * S.submatrix Sum.inl Sum.inr -
    S.submatrix Sum.inr Sum.inl * A.transpose +
    A * S.submatrix Sum.inl Sum.inl * A.transpose

/-- Scalar approximation error, PDF p.8, (2.42). -/
def graphError {I : Type*} [Fintype I] (Z : Matrix I I ℂ) : ℝ :=
  Matrix.trace (imagPart Z) / 2

/-- Symplecticity in the source's grouped order, PDF p.5, (2.11). -/
def graphBlockSymplectic {I : Type*} [Fintype I] [DecidableEq I]
    (A B C D : Matrix I I ℝ) : Prop :=
  let S := Matrix.fromBlocks A B C D
  S * Matrix.fromBlocks 0 1 (-1) 0 * S.transpose = Matrix.fromBlocks 0 1 (-1) 0

/-- General Gaussian graph update, PDF p.6, (2.24).
All theorems using inverse assert denominator invertibility as a conclusion. -/
def mobius {I : Type*} [Fintype I] [DecidableEq I]
    (A B C D : Matrix I I ℝ) (Z : Matrix I I ℂ) : Matrix I I ℂ :=
  (complexify C + complexify D * Z) * (complexify A + complexify B * Z)⁻¹

/-- n-local operation extended by the identity on untouched nodes, p.9 (3.2). -/
def graphLocalMobius {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A B C D : Matrix I I ℝ)
    (Z : Matrix (I ⊕ J) (I ⊕ J) ℂ) : Matrix (I ⊕ J) (I ⊕ J) ℂ :=
  mobius (Matrix.fromBlocks A 0 0 1) (Matrix.fromBlocks B 0 0 0)
    (Matrix.fromBlocks C 0 0 0) (Matrix.fromBlocks D 0 0 1) Z

/-- One distinguished node and its neighborhood, PDF p.10 (3.9). -/
def oneGraph {J : Type*} (t : ℂ) (r : J → ℂ) (W : Matrix J J ℂ) :
    Matrix (Unit ⊕ J) (Unit ⊕ J) ℂ :=
  Matrix.fromBlocks (fun _ _ => t) (fun _ j => r j) (fun j _ => r j) W

/-- One-node symplectic action, PDF pp.9–10 (3.8)–(3.9). -/
def oneAction {J : Type*} [Fintype J] [DecidableEq J] (a b c d : ℝ)
    (Z : Matrix (Unit ⊕ J) (Unit ⊕ J) ℂ) : Matrix (Unit ⊕ J) (Unit ⊕ J) ℂ :=
  graphLocalMobius (fun _ _ => a) (fun _ _ => b) (fun _ _ => c) (fun _ _ => d) Z

/-- Phase-plane rotation with the source sign, PDF pp.11,13 (3.17),(4.1). -/
def graphPhaseMobius {I : Type*} [Fintype I] [DecidableEq I]
    (Z : Matrix I I ℂ) (theta : I → ℝ) : Matrix I I ℂ :=
  mobius (Matrix.diagonal (fun j => Real.cos (theta j)))
    (Matrix.diagonal (fun j => Real.sin (theta j)))
    (Matrix.diagonal (fun j => -Real.sin (theta j)))
    (Matrix.diagonal (fun j => Real.cos (theta j))) Z

/-- Error as a function of local phases, PDF p.13 (4.2). -/
def phaseError {I : Type*} [Fintype I] [DecidableEq I]
    (Z : Matrix I I ℂ) (theta : I → ℝ) : ℝ := graphError (graphPhaseMobius Z theta)

/-- The Hessian of one-half tr Im Z under phase shifts, PDF p.22 (B15). -/
def phaseHessian {I : Type*} [Fintype I] [DecidableEq I]
    (Z : Matrix I I ℂ) : Matrix I I ℝ :=
  imagPart (fun j k => ((1 : Matrix I I ℂ) + Z * Z) j k * Z j k)

/-- Canonical finite-squeezing graph, PDF p.7 (2.29). -/
def canonicalGraph {I : Type*} [DecidableEq I] (A : Matrix I I ℝ) (r : ℝ) : Matrix I I ℂ :=
  complexify A + (Complex.I * (Real.exp (-2 * r) : ℂ)) • 1

/-- The second cluster family, PDF p.7 (2.31). -/
def sechGraph {I : Type*} [DecidableEq I] (A : Matrix I I ℝ) (alpha : ℝ) : Matrix I I ℂ :=
  (Real.tanh (2 * alpha) : ℂ) • complexify A +
    (Complex.I * ((Real.cosh (2 * alpha))⁻¹ : ℂ)) • 1

/-- H-graph coordinate, PDF p.7 (2.32). This is a matrix definition;
the separate Hamiltonian-generation assertion is deferred. -/
def hGraph {I : Type*} [Fintype I] [DecidableEq I] (G : Matrix I I ℝ) (alpha : ℝ) : Matrix I I ℂ :=
  Complex.I • complexify (NormedSpace.exp ((-2 * alpha) • G))

/-- Actual L2 normalization of a wavefunction, PDF pp.4–6. -/
def NormalizedWave {n : ℕ} (f : (Fin n → ℝ) → ℂ) : Prop :=
  MemLp f 2 volume ∧ (∫ q, Complex.normSq (f q)) = 1

/-- Centered Gaussian shape is a quadratic exponential, not a graph tuple;
normalization excludes the zero vector, PDF p.6 (2.21). -/
def NormalizedGaussian {n : ℕ} (f : (Fin n → ℝ) → ℂ) : Prop :=
  IsCenteredGaussianFunction f ∧ NormalizedWave f

/-- First and second quadrature form integrability on the concrete Gaussian
function domain, PDF pp.5–7. No unbounded CCR operator is made bounded. -/
def HasQuadratureForms {n : ℕ} (f : (Fin n → ℝ) → ℂ) : Prop :=
  (∀ a : Phase n, Integrable (fun q => star (f q) * quadratureFunction a f q)) ∧
  ∀ a b : Phase n, Integrable (fun q =>
    star (quadratureFunction a f q) * quadratureFunction b f q)

/-- Ordered second moment as a quadratic form, PDF p.7 (2.27). -/
def secondMoment {n : ℕ} (f : (Fin n → ℝ) → ℂ) (a b : Phase n) : ℂ :=
  ∫ q, star (quadratureFunction a f q) * quadratureFunction b f q

/-- Q=<qq^T>, PDF p.7 (2.27), vacuum Q=I/2. -/
def qMoment {n : ℕ} (f : (Fin n → ℝ) → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => secondMoment f (Sum.inl j) (Sum.inl k)

/-- P=<qp^T>, PDF p.7 (2.27), vacuum P=iI/2. -/
def qpMoment {n : ℕ} (f : (Fin n → ℝ) → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => secondMoment f (Sum.inl j) (Sum.inr k)

/-- Symmetrized <{q,p^T}>, PDF p.7 (2.27). -/
def symQpMoment {n : ℕ} (f : (Fin n → ℝ) → ℂ) : Matrix (Fin n) (Fin n) ℝ :=
  fun j k => 2 * (qpMoment f j k).re

/-- Expectation-defined graph; no outer one-half on Q^{-1}P, PDF pp.7,19. -/
def extractedGraph {n : ℕ} (f : (Fin n → ℝ) → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (qMoment f)⁻¹ * qpMoment f

/-- Centered extraction for displaced states, PDF p.11 displacement rule. -/
def centeredGraph {n : ℕ} (f : (Fin n → ℝ) → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  let S := waveCovariance f
  (complexify (S.submatrix Sum.inl Sum.inl))⁻¹ *
    (complexify (S.submatrix Sum.inl Sum.inr) + (Complex.I / 2) • 1)

/-- A normalized centered Gaussian vector in the actual oscillator L2 space. -/
def IsGaussianVector {n : ℕ} (psi : Schrodinger n) : Prop :=
  ∃ f : (Fin n → ℝ) → ℂ, NormalizedGaussian f ∧ (fun q => psi q) =ᵐ[volume] f

/-- Representation ties graph to actual expectation values on an L2 vector,
not to a stipulated matrix-state correspondence, PDF pp.19–20. -/
def GaussianGraphRepresents {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (psi : Schrodinger n) : Prop :=
  ∃ f : (Fin n → ℝ) → ℂ, NormalizedGaussian f ∧
    (fun q => psi q) =ᵐ[volume] f ∧ Z = extractedGraph f

/-- Concrete nullifier or its formal adjoint on smooth functions, PDF p.8. -/
def nullifier {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ)
    (f : (Fin n → ℝ) → ℂ) (j : Fin n) (q : Fin n → ℝ) : ℂ :=
  quadratureFunction (Sum.inr j) f q -
    ∑ k, Z j k * quadratureFunction (Sum.inl k) f q

/-- Symmetrized complex nullifier covariance, PDF p.8 (2.40).
Adjoint coefficients are conjugated; the second form has reversed indices. -/
def complexNullifierCovariance {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ)
    (f : (Fin n → ℝ) → ℂ) : Matrix (Fin n) (Fin n) ℂ := fun j k =>
  (1 / 2 : ℂ) * ((∫ q, star (nullifier Z f j q) * nullifier Z f k q) +
    ∫ q, star (nullifier (fun a b => star (Z a b)) f k q) *
      nullifier (fun a b => star (Z a b)) f j q)

/-- Real nullifier quadratic form, PDF p.8 (2.41)–(2.42). -/
def realNullifierCovariance {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (f : (Fin n → ℝ) → ℂ) : Matrix (Fin n) (Fin n) ℝ := fun j k =>
  (∫ q, star (nullifier (complexify A) f j q) * nullifier (complexify A) f k q).re

/-- Single-mode marginal isotropy in the source's resource sense,
PDF p.15 (4.12), not computational efficiency. -/
def HasIsotropicMarginals {I : Type*} [Fintype I] [DecidableEq I] (Z : Matrix I I ℂ) : Prop :=
  ∀ j, graphCovariance Z (Sum.inl j) (Sum.inl j) =
      graphCovariance Z (Sum.inr j) (Sum.inr j) ∧
    graphCovariance Z (Sum.inl j) (Sum.inr j) = 0

/-- Two-mode unweighted edge, PDF p.14 (4.7). -/
def twoEdge : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- Beamsplitter convention, PDF p.10 (3.10). -/
def beamRotation (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos theta, -Real.sin theta; Real.sin theta, Real.cos theta]

/-- Cayley/Siegel-disc coordinate, PDF p.21 (B1); K^{-1} is never used. -/
def siegelDiscCoordinate {I : Type*} [Fintype I] [DecidableEq I] (Z : Matrix I I ℂ) : Matrix I I ℂ :=
  (1 + Complex.I • Z) * (1 - Complex.I • Z)⁻¹

example {I J : Type*} (Z : Matrix I J ℂ) (i : I) (j : J) : realPart Z i j = (Z i j).re := rfl

example {J : Type*} (t : ℂ) (r : J → ℂ) (W : Matrix J J ℂ) :
    oneGraph t r W (Sum.inl ()) (Sum.inl ()) = t := rfl

example {I : Type*} [DecidableEq I] (A : Matrix I I ℝ) :
    canonicalGraph A 0 = complexify A + Complex.I • 1 := by
  simp [canonicalGraph]

example : beamRotation 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [beamRotation, Matrix.one_apply]

example {n : ℕ} (f : (Fin n → ℝ) → ℂ) : qMoment f =
    (fun j k => secondMoment f (Sum.inl j) (Sum.inl k)) := rfl

example : twoEdge 0 1 = 1 := rfl

/-- Symplectic spectrum with multiplicity: the characteristic polynomial
of Sigma Omega is product_j (X^2+sigma_j^2), PDF pp.17–18, (4.35),(4.38).
For an empty subsystem the product and characteristic polynomial are both 1. -/
def HasSymplecticSpectrum {n : ℕ} (S : Matrix (Phase n) (Phase n) ℝ) (s : Fin n → ℝ) : Prop :=
  (∀ j, 0 < s j) ∧ (S * sigma n).charpoly =
    ∏ j, (Polynomial.X^2 + Polynomial.C ((s j)^2))

/-- Pure-wave product structure across one node versus the rest,
PDF p.18. The factors are genuine square-integrable functions. -/
def FactorsAt {n : ℕ} (f : (Fin n → ℝ) → ℂ) (k : Fin n) : Prop :=
  ∃ a : ℝ → ℂ, ∃ b : ({i : Fin n // i ≠ k} → ℝ) → ℂ,
    MemLp a 2 volume ∧ MemLp b 2 volume ∧
    ∀ᵐ q ∂volume, f q = a (q k) * b (fun i => q i.val)

/-- One-node symplectic eigenvalue, PDF p.18 (4.41); self-loop excluded. -/
def nodeSpectrum {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (k : Fin n) : ℝ :=
  Real.sqrt (1 + Real.exp (4*r) * ∑ l ∈ Finset.univ.erase k, (V k l)^2) / 2

/-- Entropy of a one-mode Gaussian marginal from its symplectic eigenvalue,
PDF p.18 (background entropy characterization). Logarithm base b>1 is a
parameter, so no unstated choice of bits versus nats is imposed. At sigma=1/2
the convention 0 log 0=0 gives zero entropy. -/
def gaussianSpectralEntropy (b s : ℝ) : ℝ :=
  ((s + 1/2) * Real.log (s + 1/2) - (s - 1/2) * Real.log (s - 1/2)) / Real.log b

example (r : ℝ) : nodeSpectrum (0 : Matrix (Fin 1) (Fin 1) ℝ) r 0 = 1/2 := by
  simp [nodeSpectrum]

example (b : ℝ) : gaussianSpectralEntropy b (1/2) = 0 := by
  norm_num [gaussianSpectralEntropy]

/-- Concrete ordered finite-squeezing stabilizer X_j(s)Z_j(i eps_j s)
product_neighbor Z_l(s), including its nonunit Gaussian scalar, PDF p.23 (C7).
Translation is performed after the multiplication factors, as operator order
requires; A is hollow in the theorem below. -/
def clusterStabilizer {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (eps : Fin n → ℝ)
    (j : Fin n) (s : ℝ) (f : (Fin n → ℝ) → ℂ) (q : Fin n → ℝ) : ℂ :=
  let qShift := Function.update q j (q j - s)
  (Real.exp (-(eps j)*s^2/2) : ℂ) *
    Complex.exp (-((eps j * s * qShift j : ℝ) : ℂ)) *
    Complex.exp (Complex.I * ((s * ∑ l, A j l * qShift l : ℝ) : ℂ)) * f qShift

example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (eps : Fin n → ℝ)
    (j : Fin n) (f : (Fin n → ℝ) → ℂ) : clusterStabilizer A eps j 0 f = f := by
  funext q
  simp [clusterStabilizer]

/-- Passive-optics nullifier coefficient A=X+i D Y, with row squeezing D
on the LEFT, PDF p.23 (C15). -/
def passiveA {n : ℕ} (r : Fin n → ℝ) (X Y : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  complexify X + Complex.I • complexify (Matrix.diagonal (fun j => Real.exp (-2*r j)) * Y)

/-- Passive-optics coefficient B=i D X-Y, PDF p.23 (C16). -/
def passiveB {n : ℕ} (r : Fin n → ℝ) (X Y : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Complex.I • complexify (Matrix.diagonal (fun j => Real.exp (-2*r j)) * X) - complexify Y

example {n : ℕ} (r : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    passiveA r X 0 = complexify X := by
  have hz : complexify (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
    ext i j
    simp [complexify]
  simp only [passiveA, Matrix.mul_zero, hz, smul_zero, add_zero]

/-- Covariance-based centered graph extraction for a PURE covariance.
For the Appendix-D mixed family, first divide the covariance by kappa,
PDF pp.7,24. Direct extraction on the mixed covariance would be wrong. -/
def covarianceGraph {n : ℕ} (S : Matrix (Phase n) (Phase n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (complexify (S.submatrix Sum.inl Sum.inl))⁻¹ *
    (complexify (S.submatrix Sum.inl Sum.inr) + (Complex.I / 2) • 1)

/-- Conditioning covariance on the measured q of the distinguished first
mode, retaining both quadratures of every unmeasured mode, Appendix D p.24
in the Section III.D measurement context. -/
def qConditionedCovariance {J : Type*} [Fintype J] [DecidableEq J]
    (S : Matrix ((Unit ⊕ J) ⊕ (Unit ⊕ J)) ((Unit ⊕ J) ⊕ (Unit ⊕ J)) ℝ) :
    Matrix (J ⊕ J) (J ⊕ J) ℝ :=
  let e : J ⊕ J → (Unit ⊕ J) ⊕ (Unit ⊕ J) := Sum.map Sum.inr Sum.inr
  let a : (Unit ⊕ J) ⊕ (Unit ⊕ J) := Sum.inl (Sum.inl ())
  fun i j => S (e i) (e j) - S (e i) a * S a (e j) / S a a

example {n : ℕ} (f : (Fin n → ℝ) → ℂ) :
    centeredGraph f = covarianceGraph (waveCovariance f) := rfl

end QAlgorithms.Papers.Independent.Intake100.P30


