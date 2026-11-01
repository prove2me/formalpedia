-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P92
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P92
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T08:32:02.405289+00:00
-- url     : https://prove2.me/theorems/269f4861-ddef-41d0-a5b2-7faceba3aa1e
-- title:
--   Definitions for Peres-Horodecki separability criterion for continuous variable systems
-- statement:
--   The objects the formalized statements of *Peres-Horodecki separability criterion for continuous variable systems* (arXiv:quant-ph/9909044) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `LocalMatrix`: PDF p.3, (15): one-mode canonical matrices; both quadratures are retained.
--   - `quadratureVariance`: PDF pp.2--3, (6),(8): variance of the linear observable x^T xi.
--   - `TwoModeMoments`: PDF p.2, (6): actual finite moments of this normalized oscillator density. Finite energy supplies the quadratic-form domain. Directional Weyl derivatives fix all first and second moments; explicit symmetry fixes the antisymmetric part that directional derivatives alone cannot detect. No uncertainty or PPT condition is assumed. The characteristic uses exp(i x^T xi).
--   - `bobTranspose`: PDF pp.2,4: Bob transpose in the real Hermite/Fock basis, not the adjoint.
--   - `reflectionMatrix`: PDF p.2, (5): Lambda=diag(1,1,1,-1).
--   - `reflectedCovariance`: PDF p.3, (9): reflected covariance; physicality of this matrix is a test.
--   - `ReflectedUncertainty`: PDF p.3, (10): V+i Lambda Omega Lambda/2 is positive semidefinite.
--   - `simonInvariant`: PDF pp.3--4: I1,I2,I3,I4 in Simon's order. The fourth is the trace contraction, whereas the accepted discord invariant with index 3 is det V.
--   - `SimonCriterion`: PDF p.4, (19): the invariant second-moment inequality, independent of separability and of any operator positivity assertion about partial transpose.
--   - `localArea`: PDF p.3, (11): the two independent local symplectic products.
--   - `SeparableVarianceBound`: PDF p.3, (11): uncertainty sum, quantified over every real pair.
--   - `LocalSymplectic`: PDF pp.3--4, (15): active local canonical transformation.
--   - `localCovarianceAction`: PDF pp.3--4, (14)--(15): active, rather than passive, covariance congruence.
--   - `localReflection`: PDF p.4: local sigma3=diag(1,-1), in one-mode coordinate labels.
--   - `exampleX`: PDF p.3 example: X=q1+p1+q2+p2.
--   - `exampleY`: PDF p.3 example: Y=q1-p1-q2+p2.
--   - `lowerAction`: PDF pp.1--3: annihilation on the algebraic number-state core. This formula is used on finite-support vectors; no bounded annihilation operator is claimed.
--   - `raiseAction`: PDF pp.1--3: creation on the same core; the vacuum boundary is explicit.
--   - `quadratureAction`: PDF pp.1--3: q=(a+a^dagger)/sqrt(2), p=(a-a^dagger)/(i sqrt(2)).
--   - `linearAction`: PDF p.2, (8): actual linear canonical observable on the finite-particle core.
--   - `coherentProductKernel`: PDF pp.4--5: coherent product projector, using normalized full-space Fock coefficients. No choice of an unrealized vector or photon cutoff occurs.
--   - `IsClassicalTwo`: PDF pp.4--5: positive generalized P representation as a probability measure. All coefficient integrals are explicitly integrable. Dirac and other singular measures are allowed; this is not a smooth-P-density restriction.
--   - `localUnitaryCoefficients`: PDF pp.4--5: actual tensor-product coefficients of local oscillator unitaries. Fin 1 -> Nat is explicitly relabeled by its sole occupation coordinate.
--   - `localStateAction`: PDF pp.4--5: actual (U1 tensor U2) rho (U1 tensor U2)^dagger.
-- source:
--   Peres-Horodecki separability criterion for continuous variable systems, arXiv:quant-ph/9909044v1, https://arxiv.org/abs/quant-ph/9909044v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P48
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P47

/-!
R. Simon, arXiv:quant-ph/9909044v1, PDF pp.1--5.
Two complete oscillator modes, Alice | Bob; hbar=1; interleaved q1,p1,q2,p2;
half-anticommutator covariance, vacuum I/2. Accepted paper modules are used
only as pinned definition providers under the independent-paper override.
No theorem of another paper is used as a substitute for a source result.
The all-input L2 Wigner interface and two source ambiguities are deferred.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P92

open MeasureTheory
open scoped BigOperators ENNReal ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsDensity IsSeparable IsBarycenter)
open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)
open QAlgorithms.Papers.Independent.Advance50.P48
  (TwoKernel GaussianTwo IsDiscordCovariance characteristicTwo
   covarianceModeBlock totalPhotonEnergy)
open QAlgorithms.Papers.Independent.Frontier30.P04 (modePhase Covariance twoModeStandard)
open QAlgorithms.Papers.Independent.Claimed50.P30 (canonicalOmega)
open QAlgorithms.Papers.Independent.Gap48.P47 (localSymplecticMatrix)
open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)
open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel unitaryCoeff)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, (15): one-mode canonical matrices; both quadratures are retained. -/
abbrev LocalMatrix := Matrix (modePhase 1) (modePhase 1) ℝ

/-- PDF pp.2--3, (6),(8): variance of the linear observable x^T xi. -/
def quadratureVariance (V : Covariance 2) (x : (modePhase 2) → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * V i j * x j

/-- PDF p.2, (6): actual finite moments of this normalized oscillator density.
Finite energy supplies the quadratic-form domain. Directional Weyl derivatives
fix all first and second moments; explicit symmetry fixes the antisymmetric
part that directional derivatives alone cannot detect. No uncertainty or PPT
condition is assumed. The characteristic uses exp(i x^T xi). -/
structure TwoModeMoments (rho : TwoKernel) (d : (modePhase 2) → ℝ) (V : Covariance 2) : Prop where
  density : IsDensity rho
  symmetric : V.IsSymm
  finiteEnergy : totalPhotonEnergy rho < ⊤
  firstDerivative : ∀ x : (modePhase 2) → ℝ,
    HasDerivAt (fun t : ℝ => characteristicTwo rho (t • x))
      (Complex.I * ((∑ i, d i * x i : ℝ) : ℂ)) 0
  secondDerivative : ∀ x : (modePhase 2) → ℝ,
    HasDerivAt (deriv (fun t : ℝ => characteristicTwo rho (t • x)))
      (((-quadratureVariance V x - (∑ i, d i * x i) ^ 2 : ℝ) : ℂ)) 0

/-- PDF pp.2,4: Bob transpose in the real Hermite/Fock basis, not the adjoint. -/
def bobTranspose (rho : TwoKernel) : TwoKernel :=
  fun m n => rho (m.1, n.2) (n.1, m.2)

/-- PDF p.2, (5): Lambda=diag(1,1,1,-1). -/
def reflectionMatrix : Covariance 2 :=
  Matrix.diagonal (fun i => if i.1 = 1 ∧ i.2 = 1 then -1 else 1)

/-- PDF p.3, (9): reflected covariance; physicality of this matrix is a test. -/
def reflectedCovariance (V : Covariance 2) : Covariance 2 :=
  reflectionMatrix * V * reflectionMatrix

/-- PDF p.3, (10): V+i Lambda Omega Lambda/2 is positive semidefinite. -/
def ReflectedUncertainty (V : Covariance 2) : Prop :=
  Matrix.PosSemidef (fun i j => (V i j : ℂ) + Complex.I *
    (((reflectionMatrix * canonicalOmega 2 * reflectionMatrix) i j / 2 : ℝ) : ℂ))

/-- PDF pp.3--4: I1,I2,I3,I4 in Simon's order. The fourth is the trace
contraction, whereas the accepted discord invariant with index 3 is det V. -/
def simonInvariant (V : Covariance 2) (k : Fin 4) : ℝ :=
  let A := covarianceModeBlock V 0 0
  let B := covarianceModeBlock V 1 1
  let C := covarianceModeBlock V 0 1
  let J := canonicalOmega 1
  if k = 0 then A.det else if k = 1 then B.det else if k = 2 then C.det
  else Matrix.trace (A * J * C * J * B * J * C.transpose * J)

/-- PDF p.4, (19): the invariant second-moment inequality, independent of
separability and of any operator positivity assertion about partial transpose. -/
def SimonCriterion (V : Covariance 2) : Prop :=
  (simonInvariant V 0 + simonInvariant V 1) / 4 ≤
    simonInvariant V 0 * simonInvariant V 1 +
      (1 / 4 - |simonInvariant V 2|) ^ 2 - simonInvariant V 3

/-- PDF p.3, (11): the two independent local symplectic products. -/
def localArea (x y : (modePhase 2) → ℝ) (mode : Fin 2) : ℝ :=
  x (mode,0) * y (mode,1) - x (mode,1) * y (mode,0)

/-- PDF p.3, (11): uncertainty sum, quantified over every real pair. -/
def SeparableVarianceBound (V : Covariance 2) : Prop :=
  ∀ x y : (modePhase 2) → ℝ,
    |localArea x y 0| + |localArea x y 1| ≤ quadratureVariance V x + quadratureVariance V y

/-- PDF pp.3--4, (15): active local canonical transformation. -/
def LocalSymplectic (S : LocalMatrix) : Prop :=
  S * canonicalOmega 1 * S.transpose = canonicalOmega 1

/-- PDF pp.3--4, (14)--(15): active, rather than passive, covariance congruence. -/
def localCovarianceAction (V : Covariance 2) (S1 S2 : LocalMatrix) : Covariance 2 :=
  let S := localSymplecticMatrix S1 S2
  S * V * S.transpose

/-- PDF p.4: local sigma3=diag(1,-1), in one-mode coordinate labels. -/
def localReflection : LocalMatrix :=
  Matrix.diagonal (fun i => if i.2 = 0 then 1 else -1)

/-- PDF p.3 example: X=q1+p1+q2+p2. -/
def exampleX : (modePhase 2) → ℝ := fun _ => 1

/-- PDF p.3 example: Y=q1-p1-q2+p2. -/
def exampleY : (modePhase 2) → ℝ := fun i => if i.1 = i.2 then 1 else -1

/-- PDF pp.1--3: annihilation on the algebraic number-state core. This formula
is used on finite-support vectors; no bounded annihilation operator is claimed. -/
def lowerAction (mode : Fin 2) (psi : (ℕ × ℕ) → ℂ) (m : ℕ × ℕ) : ℂ :=
  if mode = 0 then (Real.sqrt (m.1 + 1 : ℝ) : ℂ) * psi (m.1 + 1,m.2)
  else (Real.sqrt (m.2 + 1 : ℝ) : ℂ) * psi (m.1,m.2 + 1)

/-- PDF pp.1--3: creation on the same core; the vacuum boundary is explicit. -/
def raiseAction (mode : Fin 2) (psi : (ℕ × ℕ) → ℂ) (m : ℕ × ℕ) : ℂ :=
  if mode = 0 then
    if m.1 = 0 then 0 else (Real.sqrt (m.1 : ℝ) : ℂ) * psi (m.1 - 1,m.2)
  else if m.2 = 0 then 0 else (Real.sqrt (m.2 : ℝ) : ℂ) * psi (m.1,m.2 - 1)

/-- PDF pp.1--3: q=(a+a^dagger)/sqrt(2), p=(a-a^dagger)/(i sqrt(2)). -/
def quadratureAction (i : (modePhase 2)) (psi : (ℕ × ℕ) → ℂ) : (ℕ × ℕ) → ℂ :=
  fun m => if i.2 = 0 then
    (lowerAction i.1 psi m + raiseAction i.1 psi m) / (Real.sqrt 2 : ℂ)
  else (lowerAction i.1 psi m - raiseAction i.1 psi m) /
    (Complex.I * (Real.sqrt 2 : ℂ))

/-- PDF p.2, (8): actual linear canonical observable on the finite-particle core. -/
def linearAction (x : (modePhase 2) → ℝ) (psi : (ℕ × ℕ) → ℂ) : (ℕ × ℕ) → ℂ :=
  fun m => ∑ i, (x i : ℂ) * quadratureAction i psi m

/-- PDF pp.4--5: coherent product projector, using normalized full-space
Fock coefficients. No choice of an unrealized vector or photon cutoff occurs. -/
def coherentProductKernel (z : ℂ × ℂ) : TwoKernel := fun m n =>
  coherentCoefficient z.1 m.1 * star (coherentCoefficient z.1 n.1) *
    (coherentCoefficient z.2 m.2 * star (coherentCoefficient z.2 n.2))

/-- PDF pp.4--5: positive generalized P representation as a probability measure.
All coefficient integrals are explicitly integrable. Dirac and other singular
measures are allowed; this is not a smooth-P-density restriction. -/
def IsClassicalTwo (rho : TwoKernel) : Prop :=
  IsDensity rho ∧ ∃ mu : Measure (ℂ × ℂ),
    IsProbabilityMeasure mu ∧ IsBarycenter mu coherentProductKernel rho

/-- PDF pp.4--5: actual tensor-product coefficients of local oscillator unitaries.
Fin 1 -> Nat is explicitly relabeled by its sole occupation coordinate. -/
def localUnitaryCoefficients (U1 U2 : AffineMultimodeGaussianUnitary 1) : TwoKernel :=
  fun m n => unitaryCoeff U1.unitary (fun _ => m.1) (fun _ => n.1) *
    unitaryCoeff U2.unitary (fun _ => m.2) (fun _ => n.2)

/-- PDF pp.4--5: actual (U1 tensor U2) rho (U1 tensor U2)^dagger. -/
def localStateAction (U1 U2 : AffineMultimodeGaussianUnitary 1)
    (rho : TwoKernel) : TwoKernel :=
  conjugateKernel (localUnitaryCoefficients U1 U2) rho

/-! Sanity checks of local definitions; these do not prove source results. -/

example (V : Covariance 2) : quadratureVariance V 0 = 0 := by simp [quadratureVariance]

example (rho : TwoKernel) (d : (modePhase 2) → ℝ) (V : Covariance 2)
    (h : TwoModeMoments rho d V) : V.IsSymm := h.symmetric

example (rho : TwoKernel) : bobTranspose (bobTranspose rho) = rho := rfl

example : reflectionMatrix (1,1) (1,1) = -1 := by simp [reflectionMatrix]

example (V : Covariance 2) : reflectedCovariance V =
    reflectionMatrix * V * reflectionMatrix := rfl

example (V : Covariance 2) : ReflectedUncertainty V ↔
    Matrix.PosSemidef (fun i j => (V i j : ℂ) + Complex.I *
      (((reflectionMatrix * canonicalOmega 2 * reflectionMatrix) i j / 2 : ℝ) : ℂ)) := Iff.rfl

example (V : Covariance 2) : simonInvariant V 2 = (covarianceModeBlock V 0 1).det := by
  simp [simonInvariant]

example (V : Covariance 2) : SimonCriterion V ↔
    (simonInvariant V 0 + simonInvariant V 1) / 4 ≤
      simonInvariant V 0 * simonInvariant V 1 +
        (1 / 4 - |simonInvariant V 2|) ^ 2 - simonInvariant V 3 := Iff.rfl

example : localArea exampleX exampleY 0 = -2 := by norm_num [localArea, exampleX, exampleY]

example : localArea exampleX exampleY 1 = 2 := by norm_num [localArea, exampleX, exampleY]

example (V : Covariance 2) (h : SeparableVarianceBound V) :
    |localArea exampleX exampleY 0| + |localArea exampleX exampleY 1| ≤
      quadratureVariance V exampleX + quadratureVariance V exampleY := h _ _

example : LocalSymplectic (1 : LocalMatrix) := by simp [LocalSymplectic]

example (V : Covariance 2) (S1 S2 : LocalMatrix) : localCovarianceAction V S1 S2 =
    localSymplecticMatrix S1 S2 * V * (localSymplecticMatrix S1 S2).transpose := rfl

example : localReflection (0,1) (0,1) = -1 := by simp [localReflection]

example (psi : (ℕ × ℕ) → ℂ) : lowerAction 0 psi (0,0) = psi (1,0) := by
  simp [lowerAction]

example (psi : (ℕ × ℕ) → ℂ) : raiseAction 0 psi (0,0) = 0 := by simp [raiseAction]

example (psi : (ℕ × ℕ) → ℂ) : quadratureAction (0,0) psi (0,0) =
    (lowerAction 0 psi (0,0) + raiseAction 0 psi (0,0)) / (Real.sqrt 2 : ℂ) := rfl

example (psi : (ℕ × ℕ) → ℂ) : linearAction 0 psi = 0 := by
  funext m
  simp [linearAction]

example : coherentProductKernel (0,0) (0,0) (0,0) = 1 := by
  simp [coherentProductKernel, coherentCoefficient]

example (rho : TwoKernel) (h : IsClassicalTwo rho) : IsDensity rho := h.1

example (U1 U2 : AffineMultimodeGaussianUnitary 1) (m n : ℕ × ℕ) :
    localUnitaryCoefficients U1 U2 m n =
      unitaryCoeff U1.unitary (fun _ => m.1) (fun _ => n.1) *
        unitaryCoeff U2.unitary (fun _ => m.2) (fun _ => n.2) := rfl

example (U1 U2 : AffineMultimodeGaussianUnitary 1) (rho : TwoKernel) :
    localStateAction U1 U2 rho = conjugateKernel (localUnitaryCoefficients U1 U2) rho := rfl

/-! Statements, one per retained node. -/

end QAlgorithms.Papers.Independent.Intakenext100.P92


