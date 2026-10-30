-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P29
-- name    : QAlgorithms_Papers_Independent_Bridge50_P29
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T18:29:16.60302+00:00
-- url     : https://prove2.me/theorems/2c5ac1c8-26cb-41bd-a3c9-b5d7f21a51eb
-- title:
--   Definitions for Interpolation of quasi noncommutative $L_p$-spaces
-- statement:
--   The objects the formalized statements of *Interpolation of quasi noncommutative $L_p$-spaces* (arXiv:1905.08491) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `stripBoundary`: Both boundary lines, Section 3.1, PDF pp.10--11.
--   - `IsStripAnalytic`: AF(X), PDF pp.9--10: bounded in the operator norm, continuous on the closed strip, and complex differentiable in its interior. Values outside the closed strip are arbitrary extensions and do not enter any assertion.
--   - `positiveTraceValue`: Evaluate the actual weight on a positive element of M, PDF pp.3--4. The inner subtype is empty only outside the positive cone of M, where the value is defined to be zero. Inside that cone it has exactly one element, so this extended supremum equals the given weight, including an infinite value. This avoids manufacturing a positive-cone witness by an unproved assertion.
--   - `IsNSFTrace`: A normal semifinite faithful trace, Section 2.1, PDF pp.3--4. The trace identity tau(x* x)=tau(x x*) is imposed for every x in the concrete von Neumann algebra; normality, faithfulness, and semifiniteness are the independent weight properties. There is no finite-mass assumption.
--   - `tracialGauge`: Extended tracial Lp gauge of a bounded element, Section 2.1, PDF p.4: (tau((x* x)^(p/2)))^(1/p). For p=infinity use the spectral operator norm. All finite-exponent uses have 0<p<infinity. Continuous functional calculus of a positive bounded element stays positive in M, so positiveTraceValue is evaluated on its genuine domain. No normed-space instance is assigned at p<1, and infinite trace values stay infinite.
--   - `tracialBoundarySup`: Boundary suprema in Proposition 3.4, PDF p.11: all real t, with extended values even for an operator-norm-bounded function on an infinite-trace algebra.
--   - `betaLogAverage`: The beta_s logarithmic average in Section 3.3, PDF p.14, with explicit weak-limit endpoint interpretations. beta_1 dt is delta_0; beta_0 has density pi/(2(cosh(pi t)+1)). For 0<s<1 use the printed betaDensity. upperLogIntegral integrates positive and negative parts separately; all uses below have a bounded, integrable positive part but may have an infinite negative part. In particular, log(0)=-infinity never becomes Real.log(0)=0.
--   - `complexPowerScalar`: Support-zero scalar complex powers, Section 3.3, PDF pp.14--15. Only nonnegative spectral inputs and powers with positive real part are used below. At a zero eigenvalue such powers are zero.
--   - `positiveComplexPower`: Spectral powers of a positive semidefinite matrix, PDF pp.14--15. The accepted spectralFunction diagonalizes the actual Hermitian matrix, with multiplicities, and applies complexPowerScalar on its spectrum.
--   - `orderedProduct`: The ordered product A_1 ... A_n in Eq.(3.5), PDF p.14. List.prod preserves order for noncommuting matrices; the empty product is the identity.
--   - `modulusPower`: |B|^s=(B* B)^(s/2), Eq.(3.5), PDF p.14. This keeps the modulus outside the ordered product and the full outer exponent 1/r.
-- source:
--   Interpolation of quasi noncommutative Lₚ-spaces, arXiv:1905.08491v1, https://arxiv.org/abs/1905.08491v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P21

/-!
Gu--Yin--Zhang, arXiv:1905.08491v1. Four statements with their original
tracial or matrix scope. The other planned nodes are explicitly deferred in
this unit's HARD.md and GAPS.json. No abstract Haagerup object or interpolation
identity is assumed. Compilation is pending the batch handoff.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Bridge50.P29

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Next46.P33
  (PositivePart Weight IsNormalWeight IsFaithfulWeight IsSemifiniteWeight positiveOne)
open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)
open QAlgorithms.Papers.Independent.Dependency50.P21
  (extendedLog upperLogIntegral betaDensity betaZero interpolationExponent spectralFunction)

-- The frozen closedStrip is exactly the strip used in Section 2.4, PDF p.9.
open QAlgorithms.Papers.Independent.Support21.P21 (closedStrip)

/-- Both boundary lines, Section 3.1, PDF pp.10--11. -/
def stripBoundary : Set ℂ := {z | z.re = 0 ∨ z.re = 1}

/-- AF(X), PDF pp.9--10: bounded in the operator norm, continuous on the
closed strip, and complex differentiable in its interior. Values outside the
closed strip are arbitrary extensions and do not enter any assertion. -/
def IsStripAnalytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (G : ℂ → E) : Prop :=
  Bornology.IsBounded (G '' closedStrip) ∧
    ContinuousOn G closedStrip ∧
    DifferentiableOn ℂ G {z : ℂ | 0 < z.re ∧ z.re < 1}

example : (0 : ℂ) ∈ closedStrip ∧ (1 : ℂ) ∈ stripBoundary := by
  simp [closedStrip, stripBoundary]

section Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Evaluate the actual weight on a positive element of M, PDF pp.3--4.
The inner subtype is empty only outside the positive cone of M, where the
value is defined to be zero. Inside that cone it has exactly one element, so
this extended supremum equals the given weight, including an infinite value.
This avoids manufacturing a positive-cone witness by an unproved assertion. -/
def positiveTraceValue {M : VonNeumannAlgebra H} (tau : Weight M)
    (x : H →L[ℂ] H) : ℝ≥0∞ :=
  ⨆ a : {a : PositivePart M // a.val = x}, tau.value a.val

example {M : VonNeumannAlgebra H} (tau : Weight M) :
    positiveTraceValue tau 0 = 0 := by
  unfold positiveTraceValue
  apply le_antisymm
  · refine iSup_le fun a => ?_
    exact le_of_eq (tau.zero_value a.val a.property)
  · exact zero_le

/-- A normal semifinite faithful trace, Section 2.1, PDF pp.3--4.
The trace identity tau(x* x)=tau(x x*) is imposed for every x in the
concrete von Neumann algebra; normality, faithfulness, and semifiniteness
are the independent weight properties. There is no finite-mass assumption. -/
def IsNSFTrace {M : VonNeumannAlgebra H} (tau : Weight M) : Prop :=
  IsNormalWeight tau ∧ IsFaithfulWeight tau ∧ IsSemifiniteWeight tau ∧
    ∀ x : H →L[ℂ] H, x ∈ M →
      positiveTraceValue tau (star x * x) = positiveTraceValue tau (x * star x)

/-- Extended tracial Lp gauge of a bounded element, Section 2.1, PDF p.4:
(tau((x* x)^(p/2)))^(1/p). For p=infinity use the spectral operator norm.
All finite-exponent uses have 0<p<infinity. Continuous functional calculus
of a positive bounded element stays positive in M, so positiveTraceValue
is evaluated on its genuine domain. No normed-space instance is assigned
at p<1, and infinite trace values stay infinite. -/
def tracialGauge {M : VonNeumannAlgebra H} (tau : Weight M)
    (p : ℝ≥0∞) (x : H →L[ℂ] H) : ℝ≥0∞ :=
  if p = ⊤ then ENNReal.ofReal ‖x‖
  else (positiveTraceValue tau
    (cfc (fun t : ℝ => t ^ (p.toReal / 2)) (star x * x))) ^ (1 / p.toReal)

example {M : VonNeumannAlgebra H} (tau : Weight M) (x : H →L[ℂ] H) :
    tracialGauge tau ⊤ x = ENNReal.ofReal ‖x‖ := by
  simp [tracialGauge]

/-- Boundary suprema in Proposition 3.4, PDF p.11: all real t, with extended
values even for an operator-norm-bounded function on an infinite-trace algebra. -/
def tracialBoundarySup {M : VonNeumannAlgebra H} (tau : Weight M)
    (G : ℂ → (H →L[ℂ] H)) (p : ℝ≥0∞) (k : ℝ) : ℝ≥0∞ :=
  ⨆ t : ℝ, tracialGauge tau p (G ((k : ℂ) + (t : ℂ) * Complex.I))

end Tracial

/-- The beta_s logarithmic average in Section 3.3, PDF p.14, with explicit
weak-limit endpoint interpretations. beta_1 dt is delta_0; beta_0 has density
pi/(2(cosh(pi t)+1)). For 0<s<1 use the printed betaDensity. upperLogIntegral
integrates positive and negative parts separately; all uses below have a
bounded, integrable positive part but may have an infinite negative part.
In particular, log(0)=-infinity never becomes Real.log(0)=0. -/
def betaLogAverage (s : ℝ) (f : ℝ → EReal) : EReal :=
  if s = 1 then f 0
  else upperLogIntegral (fun t =>
    ((if s = 0 then betaZero t else betaDensity s t : ℝ) : EReal) * f t)

example (f : ℝ → EReal) : betaLogAverage 1 f = f 0 := by
  simp [betaLogAverage]

example : betaLogAverage 0 (fun _ => 0) = 0 := by
  simp [betaLogAverage, upperLogIntegral]

/-- Support-zero scalar complex powers, Section 3.3, PDF pp.14--15.
Only nonnegative spectral inputs and powers with positive real part are
used below. At a zero eigenvalue such powers are zero. -/
def complexPowerScalar (z : ℂ) (x : ℝ) : ℂ :=
  if x = 0 then 0 else Complex.exp (z * (Real.log x : ℂ))

example (z : ℂ) : complexPowerScalar z 0 = 0 ∧ complexPowerScalar z 1 = 1 := by
  simp [complexPowerScalar]

/-- Spectral powers of a positive semidefinite matrix, PDF pp.14--15.
The accepted spectralFunction diagonalizes the actual Hermitian matrix,
with multiplicities, and applies complexPowerScalar on its spectrum. -/
def positiveComplexPower {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (z : ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  spectralFunction (complexPowerScalar z) A

/-- The ordered product A_1 ... A_n in Eq.(3.5), PDF p.14. List.prod
preserves order for noncommuting matrices; the empty product is the identity. -/
def orderedProduct {d n : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ := (List.ofFn A).prod

example {d : ℕ} (A : Fin 0 → Matrix (Fin d) (Fin d) ℂ) : orderedProduct A = 1 := by
  simp [orderedProduct]

/-- |B|^s=(B* B)^(s/2), Eq.(3.5), PDF p.14. This keeps the modulus
outside the ordered product and the full outer exponent 1/r. -/
def modulusPower {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) (s : ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  cfc (fun t : ℝ => t ^ (s / 2)) (Bᴴ * B)

end QAlgorithms.Papers.Independent.Bridge50.P29


