-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
-- name    : QAlgorithms_Papers_Independent_Claimed50_P06
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T09:05:29.31543+00:00
-- url     : https://prove2.me/theorems/c58e8c35-171c-4ee8-b14f-71cc7a3f4486
-- title:
--   Definitions for Approximate recovery and relative entropy I. general von Neumann subalgebras
-- statement:
--   The objects the formalized statements of *Approximate recovery and relative entropy I. general von Neumann subalgebras* (arXiv:2006.08002) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsVonNeumann`: The bicommutant characterization of a unital von Neumann algebra (PDF pp.2–3). For unital complex star subalgebras, equality with the bicommutant is equivalent to ultraweak closedness. This does not impose a countability hypothesis.
--   - `StandardForm`: A standard form, PDF p.3. These are the representation axioms: conjugation, self-dual cone, commutant conjugacy, cone invariance and central compatibility. No entropy, recovery or continuity conclusion is a field of this structure.
--   - `vectorFunctional`: Vector-induced positive normal functional, PDF p.3, Eq.(2). Vectors need not be normalized; in particular the zero vector induces the zero functional.
--   - `IsNormalState`: Normal states in a standard representation, PDF p.3, Eq.(2): bounded linear functionals represented by unit vectors. In standard form these are exactly all positive ultraweakly continuous functionals with value one on the identity. The ambient dual norm gives the predual norm on this set.
--   - `SupportContained`: Support containment without a chosen support projector (PDF p.3 and Eq.(43) on p.8): null positive elements for sigma are also null for rho. For positive normal functionals this is exactly pi(rho) ≤ pi(sigma), including nonfaithful states. All positive elements are of the form a* a in a von Neumann algebra.
--   - `IsFaithful`: Faithfulness on positive elements, PDF p.3.
--   - `IsSigmaFinite`: Sigma-finiteness expressed by the existence of a faithful normal state, explicitly stated as an equivalence on PDF p.8.
--   - `vectorFidelity`: Homogeneous unsquared fidelity of vector functionals, PDF p.11, Eq.(57), p.28, Eq.(150), and p.37, Eq.(218). It is the supremum of absolute matrix coefficients of contractions in the commutant. The indexing set contains zero, and Cauchy–Schwarz bounds it by ‖v‖ * ‖w‖, so this real supremum never uses an empty or unbounded-set default. No normalization is imposed in this definition.
--   - `recoveryDensity`: The exact averaging density of Eq.(26), PDF p.6.
--   - `recoveryMeasure`: The measure p(t) dt of PDF p.28; its density is positive and has total mass one. Using withDensity lets square integrability be expressed directly.
-- source:
--   Approximate recovery and relative entropy I. general von Neumann subalgebras, arXiv:2006.08002v1, https://arxiv.org/abs/2006.08002v1

import Mathlib

/-!
Local concrete interfaces for arXiv:2006.08002v1. No dimension, separability or
trace assumption is imposed. The modular-theoretic results not constructed in
this module are explicitly deferred in the unit's HARD.md and GAPS.json.
-/

noncomputable section

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Claimed50.P06

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bicommutant characterization of a unital von Neumann algebra (PDF pp.2–3).
For unital complex star subalgebras, equality with the bicommutant is equivalent
to ultraweak closedness. This does not impose a countability hypothesis. -/
def IsVonNeumann (A : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  ∀ x : (H →L[ℂ] H),
    x ∈ A ↔ ∀ y : (H →L[ℂ] H), (y ∈ Set.centralizer (A : Set (H →L[ℂ] H))) → x * y = y * x

/-- A standard form, PDF p.3. These are the representation axioms: conjugation,
self-dual cone, commutant conjugacy, cone invariance and central compatibility.
No entropy, recovery or continuity conclusion is a field of this structure. -/
structure StandardForm (A : StarSubalgebra ℂ (H →L[ℂ] H)) where
  vonNeumann : IsVonNeumann A
  conjugation : H → H
  conjugation_add : ∀ x y, conjugation (x + y) = conjugation x + conjugation y
  conjugation_smul : ∀ (c : ℂ) x,
    conjugation (c • x) = (star c) • conjugation x
  conjugation_norm : ∀ x, ‖conjugation x‖ = ‖x‖
  conjugation_involutive : ∀ x, conjugation (conjugation x) = x
  cone : Set H
  cone_selfDual : ∀ x, x ∈ cone ↔
    ∀ y ∈ cone, (inner ℂ x y).im = 0 ∧ 0 ≤ (inner ℂ x y).re
  cone_fixed : ∀ x ∈ cone, conjugation x = x
  conjugates_algebra : ∀ x : (H →L[ℂ] H), (x ∈ Set.centralizer (A : Set (H →L[ℂ] H))) ↔
    ∃ a : A, ∀ v, x v = conjugation ((a : (H →L[ℂ] H)) (conjugation v))
  cone_invariant : ∀ (a : A) x, x ∈ cone →
    (a : (H →L[ℂ] H)) (conjugation ((a : (H →L[ℂ] H)) (conjugation x))) ∈ cone
  central_compatibility : ∀ a : A, ((a : (H →L[ℂ] H)) ∈ Set.centralizer (A : Set (H →L[ℂ] H))) →
    ∀ v, conjugation ((a : (H →L[ℂ] H)) (conjugation v)) =
      (star (a : (H →L[ℂ] H))) v

/-- Vector-induced positive normal functional, PDF p.3, Eq.(2). Vectors need not
be normalized; in particular the zero vector induces the zero functional. -/
def vectorFunctional (v : H) (a : (H →L[ℂ] H)) : ℂ := inner ℂ v (a v)

/-- Normal states in a standard representation, PDF p.3, Eq.(2): bounded linear
functionals represented by unit vectors. In standard form these are exactly all
positive ultraweakly continuous functionals with value one on the identity.
The ambient dual norm gives the predual norm on this set. -/
def IsNormalState (A : StarSubalgebra ℂ (H →L[ℂ] H)) (rho : A →L[ℂ] ℂ) : Prop :=
  ∃ v : H, ‖v‖ = 1 ∧ ∀ a : A, rho a = vectorFunctional v a

/-- Support containment without a chosen support projector (PDF p.3 and Eq.(43)
on p.8): null positive elements for sigma are also null for rho. For positive
normal functionals this is exactly pi(rho) ≤ pi(sigma), including nonfaithful
states. All positive elements are of the form a* a in a von Neumann algebra. -/
def SupportContained (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (rho sigma : A →L[ℂ] ℂ) : Prop :=
  ∀ a : A, sigma (star a * a) = 0 → rho (star a * a) = 0

/-- Faithfulness on positive elements, PDF p.3. -/
def IsFaithful (A : StarSubalgebra ℂ (H →L[ℂ] H)) (sigma : A →L[ℂ] ℂ) : Prop :=
  ∀ a : A, sigma (star a * a) = 0 → a = 0

/-- Sigma-finiteness expressed by the existence of a faithful normal state,
explicitly stated as an equivalence on PDF p.8. -/
def IsSigmaFinite (A : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  ∃ sigma : A →L[ℂ] ℂ, IsNormalState A sigma ∧ IsFaithful A sigma

/-- Homogeneous unsquared fidelity of vector functionals, PDF p.11, Eq.(57),
p.28, Eq.(150), and p.37, Eq.(218). It is the supremum of absolute matrix
coefficients of contractions in the commutant. The indexing set contains zero,
and Cauchy–Schwarz bounds it by ‖v‖ * ‖w‖, so this real supremum never uses an
empty or unbounded-set default. No normalization is imposed in this definition. -/
def vectorFidelity (A : StarSubalgebra ℂ (H →L[ℂ] H)) (v w : H) : ℝ :=
  ⨆ x : {x : (H →L[ℂ] H) // (x ∈ Set.centralizer (A : Set (H →L[ℂ] H))) ∧ ‖x‖ ≤ 1},
    ‖inner ℂ v (x.val w)‖

/-- The exact averaging density of Eq.(26), PDF p.6. -/
def recoveryDensity (t : ℝ) : ℝ := Real.pi / (Real.cosh (2 * Real.pi * t) + 1)

/-- The measure p(t) dt of PDF p.28; its density is positive and has total mass
one. Using withDensity lets square integrability be expressed directly. -/
def recoveryMeasure : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (recoveryDensity t))

example (A : StarSubalgebra ℂ (H →L[ℂ] H)) : (0 ∈ Set.centralizer (A : Set (H →L[ℂ] H))) := by
  intro a ha
  simp

example (a : (H →L[ℂ] H)) : vectorFunctional (0 : H) a = 0 := by
  simp [vectorFunctional]

example (A : StarSubalgebra ℂ (H →L[ℂ] H)) (rho : A →L[ℂ] ℂ) :
    SupportContained A rho rho := by
  intro a h
  exact h

example (A : StarSubalgebra ℂ (H →L[ℂ] H)) (v : H) :
    vectorFidelity A 0 v = 0 := by
  have hz : ((0 : (H →L[ℂ] H)) ∈ Set.centralizer (A : Set (H →L[ℂ] H))) := by
    intro a ha
    simp
  letI : Nonempty {x : (H →L[ℂ] H) // (x ∈ Set.centralizer (A : Set (H →L[ℂ] H))) ∧ ‖x‖ ≤ 1} :=
    ⟨⟨0, hz, by simp⟩⟩
  simp [vectorFidelity]

example : recoveryDensity 0 = Real.pi / 2 := by
  norm_num [recoveryDensity, Real.cosh_zero]

end QAlgorithms.Papers.Independent.Claimed50.P06


