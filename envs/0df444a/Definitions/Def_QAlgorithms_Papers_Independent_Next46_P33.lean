-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P33
-- name    : QAlgorithms_Papers_Independent_Next46_P33
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T14:27:46.985027+00:00
-- url     : https://prove2.me/theorems/cdecd9e2-c698-4362-8124-fb037452f26f
-- title:
--   Definitions for Composition Operators on Haagerup $L^p$-spaces
-- statement:
--   The objects the formalized statements of *Composition Operators on Haagerup $L^p$-spaces* (arXiv:math/0603612) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PositivePart`: Positive bounded elements of the concrete algebra, §2, PDF p.2. The order is the actual Loewner order on bounded Hilbert space operators.
--   - `Projection`: Self-adjoint idempotents in the algebra, Definition 3.1, PDF p.4.
--   - `positiveOne`: The identity as a positive element, PDF p.4.
--   - `projectionPositive`: A projection is evaluated by a weight on the positive cone, PDF p.4.
--   - `Weight`: An extended positive weight on M, §2 and Definition 3.1, PDF pp.2,4. Additivity and nonnegative homogeneity are precisely the weight axioms. The auxiliary positive element c lets the equations be written without transporting proofs of positivity. There are no normality or semifiniteness fields.
--   - `zeroWeight`: The zero weight, allowed for phi0 in §3, PDF pp.4--6.
--   - `IsNormalWeight`: Normality of a weight: preservation of suprema of nonempty increasing bounded nets of positive elements. Directed subsets and their least upper bounds express the same definition without imposing a countability restriction, §3, PDF pp.4--6. ENNReal suprema have their genuine extended values.
--   - `IsFaithfulWeight`: Faithfulness on the positive cone, §2 and Lemma 3.2, PDF pp.2,4.
--   - `IsStateWeight`: A weight is a state when its value on the identity is one. Such a weight is finite and has the unique usual positive complex-linear extension, PDF p.4. Normality is stated separately wherever required.
--   - `UltraweakTest`: A trace-class matrix coefficient defining the ultraweak topology on B(H). Both sequences are square summable; hence the coefficient series converges absolutely for every bounded operator. This describes the sigma-weak topology used for semifiniteness in Remark 3.6, PDF p.6.
--   - `ultraweakValue`: Pairing with a trace-class coefficient, Remark 3.6, PDF p.6. Mathlib inner products are conjugate-linear in the first argument.
--   - `UltraweakDenseIn`: Every finite family of ultraweak coefficients can be approximated simultaneously. This is exactly density in the induced ultraweak topology, Remark 3.6, PDF p.6; it is not density merely for vector coefficients.
--   - `finitePositiveDomain`: The finite positive domain of a weight, §2, PDF p.2.
--   - `IsSemifiniteWeight`: Semifiniteness: the finite ideal m_phi is ultraweakly dense in M. Here m_phi is its defining complex span of finite positive elements, §2, PDF p.2, and Remark 3.6, PDF p.6. This also defines semifiniteness for nonnormal weights.
--   - `IsMinimalProjection`: A nonzero minimal projection, Lemma 3.3 and Theorem 3.5, PDF pp.4--5.
--   - `IsAtomicPart`: The atomic summand is the supremum of all nonzero minimal projections. For a von Neumann algebra this supremum exists and is central. The definition specifies the actual atomic part, not a chosen arbitrary central corner, Theorem 3.5, PDF pp.5--6.
--   - `IsSemifiniteOnAtomicPart`: Semifiniteness on the atomic summand only, Theorem 3.5, PDF pp.5--6. The characterization of the atomic projection is unique and always inhabited in a von Neumann algebra. Density is tested in its corner with the induced ultraweak topology. No condition is imposed on the diffuse summand.
--   - `WeightEpsilonDelta`: Uniform epsilon-delta continuity on all projections, Definition 3.1(1), PDF p.4. The single delta is chosen before the projection.
--   - `CornerWeightEpsilonDelta`: Continuity on eMe means testing every projection f below e, Definition 3.1(1), PDF p.4. The modulus may depend on e.
--   - `WeightLocallyAbsolutelyContinuous`: Local absolute continuity is preservation of finiteness on projections, Definition 3.1(2), PDF p.4. It is not just preservation of zero sets.
--   - `SubsetAtomless`: Genuine nonatomicity on arbitrary measurable spaces, Lemma 3.4, PDF p.5: each positive measurable set has a measurable subset of strictly intermediate measure. Null singletons alone do not suffice.
--   - `MeasureEpsilonDelta`: Epsilon-delta continuity of measures on their common sigma algebra, Lemma 3.4, PDF p.5. Neither measure is converted to real-valued mass.
-- source:
--   Composition Operators on Haagerup $L^p$-spaces, arXiv:math/0603612v2, https://arxiv.org/abs/math/0603612v2

import Mathlib

/-!
Statements from Goldstein--Labuschagne, arXiv:math/0603612v2.
The local definitions below concern ordinary weights only. No abstract replacement
for the modular core or the Haagerup spaces is introduced. Results requiring those
constructions are recorded as deferred in the assigned unit artifacts.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P33

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Positive bounded elements of the concrete algebra, §2, PDF p.2.
The order is the actual Loewner order on bounded Hilbert space operators. -/
abbrev PositivePart (M : VonNeumannAlgebra H) :=
  {a : H →L[ℂ] H // a ∈ M ∧ 0 ≤ a}

/-- Self-adjoint idempotents in the algebra, Definition 3.1, PDF p.4. -/
abbrev Projection (M : VonNeumannAlgebra H) :=
  {e : H →L[ℂ] H // e ∈ M ∧ IsStarProjection e}

/-- The identity as a positive element, PDF p.4. -/
def positiveOne (M : VonNeumannAlgebra H) : PositivePart M :=
  ⟨1, by simp, (ContinuousLinearMap.nonneg_iff_isPositive _).2
    ContinuousLinearMap.isPositive_one⟩

/-- A projection is evaluated by a weight on the positive cone, PDF p.4. -/
def projectionPositive {M : VonNeumannAlgebra H} (e : Projection M) : PositivePart M :=
  ⟨e.val, e.property.1, (ContinuousLinearMap.nonneg_iff_isPositive _).2
    (ContinuousLinearMap.IsPositive.of_isStarProjection e.property.2)⟩

/-- An extended positive weight on M, §2 and Definition 3.1, PDF pp.2,4.
Additivity and nonnegative homogeneity are precisely the weight axioms. The
auxiliary positive element c lets the equations be written without transporting
proofs of positivity. There are no normality or semifiniteness fields. -/
structure Weight (M : VonNeumannAlgebra H) where
  value : PositivePart M → ℝ≥0∞
  zero_value : ∀ a : PositivePart M, a.val = 0 → value a = 0
  add_value : ∀ a b c : PositivePart M, c.val = a.val + b.val → value c = value a + value b
  smul_value : ∀ (r : NNReal) (a b : PositivePart M), b.val = (r : ℂ) • a.val →
    value b = (r : ℝ≥0∞) * value a

/-- The zero weight, allowed for phi0 in §3, PDF pp.4--6. -/
def zeroWeight (M : VonNeumannAlgebra H) : Weight M where
  value := fun _ => 0
  zero_value := by intros; rfl
  add_value := by intros; simp
  smul_value := by intros; simp

/-- Normality of a weight: preservation of suprema of nonempty increasing
bounded nets of positive elements. Directed subsets and their least upper bounds
express the same definition without imposing a countability restriction, §3,
PDF pp.4--6. ENNReal suprema have their genuine extended values. -/
def IsNormalWeight {M : VonNeumannAlgebra H} (w : Weight M) : Prop :=
  ∀ S : Set (PositivePart M), S.Nonempty → DirectedOn (· ≤ ·) S →
    ∀ a : PositivePart M, IsLUB S a → w.value a = ⨆ b : S, w.value b.val

/-- Faithfulness on the positive cone, §2 and Lemma 3.2, PDF pp.2,4. -/
def IsFaithfulWeight {M : VonNeumannAlgebra H} (w : Weight M) : Prop :=
  ∀ a : PositivePart M, w.value a = 0 → a.val = 0

/-- A weight is a state when its value on the identity is one. Such a weight is
finite and has the unique usual positive complex-linear extension, PDF p.4.
Normality is stated separately wherever required. -/
def IsStateWeight {M : VonNeumannAlgebra H} (w : Weight M) : Prop :=
  w.value (positiveOne M) = 1

/-- A trace-class matrix coefficient defining the ultraweak topology on B(H).
Both sequences are square summable; hence the coefficient series converges
absolutely for every bounded operator. This describes the sigma-weak topology
used for semifiniteness in Remark 3.6, PDF p.6. -/
structure UltraweakTest (H : Type*) [NormedAddCommGroup H] where
  left : ℕ → H
  right : ℕ → H
  left_summable : Summable (fun n => ‖left n‖ ^ 2)
  right_summable : Summable (fun n => ‖right n‖ ^ 2)

/-- Pairing with a trace-class coefficient, Remark 3.6, PDF p.6.
Mathlib inner products are conjugate-linear in the first argument. -/
def ultraweakValue (f : UltraweakTest H) (a : H →L[ℂ] H) : ℂ :=
  ∑' n, inner ℂ (f.left n) (a (f.right n))

/-- Every finite family of ultraweak coefficients can be approximated
simultaneously. This is exactly density in the induced ultraweak topology,
Remark 3.6, PDF p.6; it is not density merely for vector coefficients. -/
def UltraweakDenseIn (S T : Set (H →L[ℂ] H)) : Prop :=
  ∀ a ∈ T, ∀ tests : List (UltraweakTest H), ∀ eps : ℝ, 0 < eps →
    ∃ b ∈ S, ∀ f ∈ tests, ‖ultraweakValue f (b - a)‖ < eps

/-- The finite positive domain of a weight, §2, PDF p.2. -/
def finitePositiveDomain {M : VonNeumannAlgebra H} (w : Weight M) : Set (H →L[ℂ] H) :=
  {a | ∃ b : PositivePart M, b.val = a ∧ w.value b < ⊤}

/-- Semifiniteness: the finite ideal m_phi is ultraweakly dense in M.
Here m_phi is its defining complex span of finite positive elements, §2, PDF p.2,
and Remark 3.6, PDF p.6. This also defines semifiniteness for nonnormal weights. -/
def IsSemifiniteWeight {M : VonNeumannAlgebra H} (w : Weight M) : Prop :=
  UltraweakDenseIn (Submodule.span ℂ (finitePositiveDomain w) : Set (H →L[ℂ] H))
    (M : Set (H →L[ℂ] H))

/-- A nonzero minimal projection, Lemma 3.3 and Theorem 3.5, PDF pp.4--5. -/
def IsMinimalProjection {M : VonNeumannAlgebra H} (e : Projection M) : Prop :=
  e.val ≠ 0 ∧ ∀ f : Projection M, f ≤ e → f.val = 0 ∨ f = e

/-- The atomic summand is the supremum of all nonzero minimal projections.
For a von Neumann algebra this supremum exists and is central. The definition
specifies the actual atomic part, not a chosen arbitrary central corner,
Theorem 3.5, PDF pp.5--6. -/
def IsAtomicPart {M : VonNeumannAlgebra H} (z : Projection M) : Prop :=
  IsLUB {e : Projection M | IsMinimalProjection e} z

/-- Semifiniteness on the atomic summand only, Theorem 3.5, PDF pp.5--6.
The characterization of the atomic projection is unique and always inhabited in
a von Neumann algebra. Density is tested in its corner with the induced
ultraweak topology. No condition is imposed on the diffuse summand. -/
def IsSemifiniteOnAtomicPart {M : VonNeumannAlgebra H} (w : Weight M) : Prop :=
  ∀ z : Projection M, IsAtomicPart z →
    UltraweakDenseIn
      (Submodule.span ℂ {a : H →L[ℂ] H |
        a ∈ finitePositiveDomain w ∧ z.val * a * z.val = a} : Set (H →L[ℂ] H))
      {a | a ∈ M ∧ z.val * a * z.val = a}

/-- Uniform epsilon-delta continuity on all projections, Definition 3.1(1),
PDF p.4. The single delta is chosen before the projection. -/
def WeightEpsilonDelta {M : VonNeumannAlgebra H} (w0 w1 : Weight M) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
    ∀ e : Projection M,
      w1.value (projectionPositive e) < ENNReal.ofReal delta →
      w0.value (projectionPositive e) < ENNReal.ofReal eps

/-- Continuity on eMe means testing every projection f below e,
Definition 3.1(1), PDF p.4. The modulus may depend on e. -/
def CornerWeightEpsilonDelta {M : VonNeumannAlgebra H}
    (w0 w1 : Weight M) (e : Projection M) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
    ∀ f : Projection M, f ≤ e →
      w1.value (projectionPositive f) < ENNReal.ofReal delta →
      w0.value (projectionPositive f) < ENNReal.ofReal eps

/-- Local absolute continuity is preservation of finiteness on projections,
Definition 3.1(2), PDF p.4. It is not just preservation of zero sets. -/
def WeightLocallyAbsolutelyContinuous {M : VonNeumannAlgebra H}
    (w0 w1 : Weight M) : Prop :=
  ∀ e : Projection M, w1.value (projectionPositive e) < ⊤ →
    w0.value (projectionPositive e) < ⊤

/-- Genuine nonatomicity on arbitrary measurable spaces, Lemma 3.4, PDF p.5:
each positive measurable set has a measurable subset of strictly intermediate
measure. Null singletons alone do not suffice. -/
def SubsetAtomless {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) : Prop :=
  ∀ A : Set Omega, MeasurableSet A → 0 < mu A →
    ∃ B : Set Omega, MeasurableSet B ∧ B ⊆ A ∧ 0 < mu B ∧ mu B < mu A

/-- Epsilon-delta continuity of measures on their common sigma algebra,
Lemma 3.4, PDF p.5. Neither measure is converted to real-valued mass. -/
def MeasureEpsilonDelta {Omega : Type*} [MeasurableSpace Omega]
    (nu mu : Measure Omega) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
    ∀ A : Set Omega, MeasurableSet A → mu A < ENNReal.ofReal delta →
      nu A < ENNReal.ofReal eps

example (M : VonNeumannAlgebra H) (a : PositivePart M) :
    (zeroWeight M).value a = 0 := rfl

example (f : UltraweakTest H) : ultraweakValue f 0 = 0 := by
  simp [ultraweakValue]

example (M : VonNeumannAlgebra H) (w1 : Weight M) :
    WeightLocallyAbsolutelyContinuous (zeroWeight M) w1 := by
  intro e he
  simp [zeroWeight]

example {Omega : Type*} [MeasurableSpace Omega] :
    SubsetAtomless (0 : Measure Omega) := by
  intro A hA hpos
  simp at hpos

example {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) :
    MeasureEpsilonDelta mu mu := by
  intro eps heps
  exact ⟨eps, heps, fun A hA hlt => hlt⟩

end QAlgorithms.Papers.Independent.Next46.P33


