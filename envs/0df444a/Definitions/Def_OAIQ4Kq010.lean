-- Prove2me | Definitions.Def_OAIQ4Kq010
-- name    : OAIQ4Kq010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T08:42:05.392347+00:00
-- url     : https://prove2.me/theorems/9d26ab37-2937-4b83-8475-67c990d08811
-- title:
--   Definitions bundle OAIQ4Kq010 of the split of OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kaplansky.kaplansky_quasitrace_counterexample`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 3 definitions, 6 instances and 14 theorems. The definitions and types are `OAI.Kaplansky.semigroupToOrderedGroup`, `OAI.Kaplansky.twistedSlotEquiv`, `OAI.Kaplansky.twistedStandardFrames`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Kaplansky, in whole or in part: [`BundleTests_Base`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/BundleTests/Base.lean), [`BundleTests_Smooth`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/BundleTests/Smooth.lean), [`BundleTests_Twisted`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/BundleTests/Twisted.lean), [`Cuntz_Monoid`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Cuntz/Monoid.lean), [`Cuntz_State`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Cuntz/State.lean), [`IntegralHomology_ProjectiveClass`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/IntegralHomology/ProjectiveClass.lean), [`Kaplansky_TestAlgebra`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/TestAlgebra.lean), [`OrderedStates_Semigroup`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/OrderedStates/Semigroup.lean).
--
--   **Imports.** It imports the bundles `OAIQ4Kq005`, `OAIQ4Kq006`, `OAIQ4Kq007` and `OAIQ4Kq008` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ4Kq011`.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Kaplansky at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ4Kq005
import Definitions.Def_OAIQ4Kq006
import Definitions.Def_OAIQ4Kq007
import Definitions.Def_OAIQ4Kq008

section
-- module Solutions.OAIQ4_Kq.BundleTests_Base
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact bundle-test base, prefix dimensions, and retained multiplicities. -/

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology
namespace Kaplansky

instance instCompactSpaceBundleTestBase (m R : ℕ) : CompactSpace (BundleTestBase m R) := inferInstance

instance instNonemptyBundleTestBase (m R : ℕ) : Nonempty (BundleTestBase m R) := ⟨bundleTestBasePoint m R⟩

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Smooth
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.lineStageTotal_locallyCompactSpace _root_.OAI.Kaplansky.lineStage_finite _root_.OAI.Kaplansky.retainedBundle_inner _root_.OAI.Kaplansky.retainedBundle_norm _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Smooth bases and test bundles with replacement maps. -/

section
open Topology
open scoped Manifold ContDiff BigOperators
namespace Kaplansky
open ComplexGrassmann

instance instCompactSpaceSmoothTestBase (m R : ℕ) : CompactSpace (SmoothTestBase m R) := inferInstance
instance instT2SpaceSmoothTestBase (m R : ℕ) : T2Space (SmoothTestBase m R) := inferInstance

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_ProjectiveClass
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.lineStageTotal_locallyCompactSpace _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Localization, top homology, and the fundamental class of projective products. -/

section
open CategoryTheory Limits
open ComplexGrassmann

instance projectiveSpaceZero_nonempty : Nonempty (Grassmann 1 0) :=
  ⟨graphPoint (standardLineGraphFrame 0) 0⟩

open ComplexGrassmann

end

open CategoryTheory Limits

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Twisted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Twisted hyperplane bundles, zeros, graph coordinates, and frame sections. -/

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

def twistedSlotEquiv : TwistedHyperplaneSlot K h ≃
    (Σ i, Fin (twistedProjectiveDimensions K h i)) where
  toFun
    | .inl j => ⟨none,j⟩
    | .inr s => ⟨some s.1,s.2⟩
  invFun
    | ⟨none,j⟩ => .inl j
    | ⟨some i,j⟩ => .inr ⟨i,j⟩
  left_inv s := by cases s <;> rfl
  right_inv s := by obtain ⟨i,j⟩ := s; cases i <;> rfl

def twistedStandardFrames (i : Option ι) := standardLineGraphFrame (twistedProjectiveDimensions K h i)

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_Monoid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordered Cuntz monoid and compression by its order unit. -/

noncomputable section
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

/-- Every class is bounded by a natural multiple of [1_A]. -/
theorem cuntzMonoid_orderUnit (x : CuntzMonoid A) : ∃ n : ℕ, x ≤ n • cuntzUnit A 1 := by
  induction x using Quotient.inductionOn with | h x =>
  refine ⟨x.size, ?_⟩
  rw [cuntzUnit_nsmul]
  exact (cuntzClass_le _ _).mpr x.le_unit

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.OrderedStates_Semigroup
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Catalytic orders, ordered group completion, and normalized semigroup states. -/

namespace Kaplansky

section
variable (S : Type*) [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

variable {S}

/-- The actual additive map from the monoid into its ordered completion. -/
def semigroupToOrderedGroup : S →+ SemigroupOrderedGroup S where
  toFun a := semigroupDifferenceClass (a,0)
  map_zero' := rfl
  map_add' a b := by
    change semigroupDifferenceClass (a+b,0) = semigroupDifferenceClass ((a,0)+(b,0))
    congr 1
    exact Prod.ext rfl (zero_add 0).symm

theorem semigroupToOrderedGroup_le_iff (a b : S) :
    semigroupToOrderedGroup a ≤ semigroupToOrderedGroup b ↔ ∃ c : S, a+c ≤ b+c := by
  change semigroupDifferenceClass (a,0) ≤ semigroupDifferenceClass (b,0) ↔ _
  simpa only [add_zero] using semigroupDifferenceClass_le (a,0) (b,0)

theorem semigroupToOrderedGroup_monotone : Monotone (semigroupToOrderedGroup (S := S)) := by
  intro a b hab
  exact (semigroupToOrderedGroup_le_iff a b).mpr ⟨0, by simpa using hab⟩

end

section
variable {S : Type*} [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

theorem semigroupDifferenceClass_eq_sub (a b : S) :
    semigroupDifferenceClass (a,b) = semigroupToOrderedGroup a - semigroupToOrderedGroup b := by
  change semigroupDifferenceClass (a,b) = semigroupDifferenceClass ((a,0)+(0,b))
  congr 1
  exact Prod.ext (add_zero a).symm (zero_add b).symm

theorem semigroupOrderedGroup_exists_difference (x : SemigroupOrderedGroup S) :
    ∃ a b : S, x = semigroupToOrderedGroup a - semigroupToOrderedGroup b := by
  induction x using Quotient.inductionOn with | h x =>
  exact ⟨x.1,x.2,semigroupDifferenceClass_eq_sub _ _⟩

/-- The image of the unit remains order-reflecting on all natural multiples,
including after passage to the ordered group quotient. -/
theorem semigroupOrderedGroup_unit_order (u : S)
    (hf : ∀ k : ℕ, 0 < k → ¬ (2*k) • u ≤ k • u)
    (hpos : ∀ c : S, 0 ≤ c) (hbound : ∀ c : S, ∃ N : ℕ, c ≤ N • u)
    (m n : ℕ) :
    m • semigroupToOrderedGroup u ≤ n • semigroupToOrderedGroup u ↔ m ≤ n := by
  rw [← map_nsmul, ← map_nsmul, semigroupToOrderedGroup_le_iff]
  exact stabilized_unit_order_iff u (hpos u) hf hpos hbound m n

theorem semigroupOrderedGroup_unit_nonneg (u : S) (hu : 0 ≤ u) :
    0 ≤ semigroupToOrderedGroup u := by
  simpa using semigroupToOrderedGroup_monotone hu

/-- The original order-unit bound becomes a two-sided bound on every
element of the ordered group. No finite generation is needed. -/
theorem semigroupOrderedGroup_order_unit (u : S)
    (hpos : ∀ c : S, 0 ≤ c) (hbound : ∀ c : S, ∃ N : ℕ, c ≤ N • u)
    (x : SemigroupOrderedGroup S) :
    ∃ N : ℕ, -(N • semigroupToOrderedGroup u) ≤ x ∧
      x ≤ N • semigroupToOrderedGroup u := by
  obtain ⟨a,b,rfl⟩ := semigroupOrderedGroup_exists_difference x
  obtain ⟨m,hm⟩ := hbound a
  obtain ⟨n,hn⟩ := hbound b
  have ha := semigroupToOrderedGroup_monotone hm
  have hb := semigroupToOrderedGroup_monotone hn
  rw [map_nsmul] at ha hb
  have hza := semigroupOrderedGroup_unit_nonneg a (hpos a)
  have hzb := semigroupOrderedGroup_unit_nonneg b (hpos b)
  have hu := semigroupOrderedGroup_unit_nonneg u (hpos u)
  refine ⟨m+n, ?_, ?_⟩
  · have hb' : semigroupToOrderedGroup b ≤ (m+n) • semigroupToOrderedGroup u :=
      hb.trans (nsmul_le_nsmul_left hu (Nat.le_add_left n m))
    exact (neg_le_neg hb').trans (neg_le_sub_iff_le_add.mpr (by simpa using hza))
  · have ha' : semigroupToOrderedGroup a ≤ (m+n) • semigroupToOrderedGroup u :=
      ha.trans (nsmul_le_nsmul_left hu (Nat.le_add_right m n))
    exact (sub_le_self _ hzb).trans ha'

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

@[simp] theorem semigroupOrderedGroupLift_unit (f : S →+ G) (hf : Monotone f) (a : S) :
    semigroupOrderedGroupLift f hf (semigroupToOrderedGroup a) = f a := by
  change f a-f 0=f a
  simp

theorem semigroupOrderedGroupLift_monotone (f : S →+ G) (hf : Monotone f) :
    Monotone (semigroupOrderedGroupLift f hf) := by
  intro a b hab
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  exact semigroupDifference_value_mono f hf ((semigroupDifferenceClass_le _ _).mp hab)

theorem semigroup_state_iff_orderedGroup_state (u : S) :
    (∃ f : S →+ ℝ, Monotone f ∧ f u = 1) ↔
      ∃ g : SemigroupOrderedGroup S →+ ℝ, Monotone g ∧ g (semigroupToOrderedGroup u) = 1 := by
  constructor
  · rintro ⟨f,hf,hu⟩
    exact ⟨semigroupOrderedGroupLift f hf,semigroupOrderedGroupLift_monotone f hf,by simpa⟩
  · rintro ⟨g,hg,hu⟩
    exact ⟨g.comp semigroupToOrderedGroup,hg.comp semigroupToOrderedGroup_monotone,hu⟩

end

variable {S : Type*} [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

/-- State construction on a positive ordered commutative monoid with an
order unit and no properly infinite positive unit multiple. Cancellation
and unperforation are not hypotheses. This is an abstract semigroup theorem,
not yet a quasitrace on an algebra. -/
theorem positive_orderUnit_normalized_state (u : S)
    (hpos : ∀ c : S, 0 ≤ c) (hbound : ∀ c : S, ∃ N : ℕ, c ≤ N • u)
    (hf : ∀ k : ℕ, 0 < k → ¬ (2*k) • u ≤ k • u) :
    ∃ f : S →+ ℝ, Monotone f ∧ f u = 1 := by
  apply (semigroup_state_iff_orderedGroup_state u).mpr
  apply orderedGroup_normalized_state (semigroupToOrderedGroup u)
    (semigroupOrderedGroup_unit_nonneg u (hpos u))
  · intro n hn h
    have h' : n • semigroupToOrderedGroup u ≤ 0 • semigroupToOrderedGroup u := by simpa using h
    have hle := (semigroupOrderedGroup_unit_order u hf hpos hbound n 0).mp h'
    omega
  · intro x
    obtain ⟨N,hl,_⟩ := semigroupOrderedGroup_order_unit u hpos hbound x
    exact ⟨N,hl⟩

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_State
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.CuntzDimensionState.spectralMeasure_finite _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Dimension states of the Cuntz monoid and positivity. -/

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

theorem normalizedCuntzState_exists
    (hf : ∀ k : ℕ, 0 < k → ¬ ProperlyInfinite (CStarMatrix (Fin k) (Fin k) A)) :
    ∃ f : CuntzMonoid A →+ ℝ, Monotone f ∧ f (cuntzUnit A 1) = 1 := by
  apply positive_orderUnit_normalized_state (cuntzUnit A 1)
    cuntzMonoid_nonneg cuntzMonoid_orderUnit
  intro k hk h
  exact hf k hk (properlyInfinite_of_cuntzUnit_compression k h)

theorem cuntzDimensionState_nonempty
    (hf : ∀ k : ℕ, 0 < k → ¬ ProperlyInfinite (CStarMatrix (Fin k) (Fin k) A)) :
    Nonempty (CuntzDimensionState A) := by
  obtain ⟨f, hm, hu⟩ := normalizedCuntzState_exists hf
  exact ⟨⟨f, hm, hu⟩⟩

end Kaplansky

open scoped Matrix CStarAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_TestAlgebra
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.lineStageTotal_locallyCompactSpace _root_.OAI.Kaplansky.projectiveSpaceZero_nonempty _root_.OAI.Kaplansky.retainedBundle_inner _root_.OAI.Kaplansky.retainedBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Concrete test operators, their C-star algebra, and its faithful representation. -/

open Bundle Topology
open scoped BigOperators ComplexOrder
namespace Kaplansky
open ComplexGrassmann

instance instNonemptyActualTestIndex : Nonempty ActualTestIndex :=
  ⟨⟨1,1,testBaseProjectiveHomeomorph 1 1 (bundleTestBasePoint 1 1)⟩⟩

open scoped BigOperators

attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance 2000] closedSubalgebraLE closedSubalgebraPreorder

end Kaplansky

end

end OAI
end


