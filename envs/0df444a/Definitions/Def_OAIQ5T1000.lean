-- Prove2me | Definitions.Def_OAIQ5T1000
-- name    : OAIQ5T1000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T07:57:33.358675+00:00
-- url     : https://prove2.me/theorems/15049fe0-72d1-4a4e-9570-6dfef23dbd3f
-- title:
--   Definitions bundle OAIQ5T1000 of the split of OpenAI, The Partition Principle does not imply Choice
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PartitionConsistency.main_consistency`, carved from OpenAI's openai/math development (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1409 declarations of OpenAI's Lean: 404 definitions, 43 inductive types or structures, 74 instances and 888 theorems. The definitions and types are `OAI.PartitionConsistency.CardinalParameters.μ`, `OAI.PartitionConsistency.CohenForcing.Condition`, `OAI.PartitionConsistency.CohenForcing.Condition.Compatible`, `OAI.PartitionConsistency.CohenForcing.Condition.coordinatePerm`, `OAI.PartitionConsistency.CohenForcing.Condition.dom`, `OAI.PartitionConsistency.CohenForcing.Condition.fill`, `OAI.PartitionConsistency.CohenForcing.Condition.insert`, `OAI.PartitionConsistency.CohenForcing.Condition.permute`, `OAI.PartitionConsistency.CohenForcing.Condition.permuteOrderIso`, `OAI.PartitionConsistency.CohenForcing.Condition.probeDenseSet`, `OAI.PartitionConsistency.CohenForcing.Condition.pullback`, `OAI.PartitionConsistency.CohenForcing.Condition.restrict`, `OAI.PartitionConsistency.CohenForcing.Condition.rows`, `OAI.PartitionConsistency.CohenForcing.Condition.support`, `OAI.PartitionConsistency.CohenForcing.Condition.union`, `OAI.PartitionConsistency.ConcreteSystem.A`, `OAI.PartitionConsistency.ConcreteSystem.I`, `OAI.PartitionConsistency.ConcreteSystem.K`, `OAI.PartitionConsistency.ConcreteSystem.P`, `OAI.PartitionConsistency.ConcreteSystem.S`, `OAI.PartitionConsistency.ConcreteSystem.T`, `OAI.PartitionConsistency.ConcreteSystem.imageQuotient`, `OAI.PartitionConsistency.ConcreteSystem.imageQuotientGraph`, `OAI.PartitionConsistency.ConcreteSystem.κ`, `OAI.PartitionConsistency.ConditionCodeSelection.Selected`, `OAI.PartitionConsistency.ConservativeMonoids.Attachment`, `OAI.PartitionConsistency.ConservativeMonoids.Attachment.embedding`, `OAI.PartitionConsistency.ConservativeMonoids.Attachment.generator`, `OAI.PartitionConsistency.ConservativeMonoids.Attachment.parameters`, `OAI.PartitionConsistency.ConservativeMonoids.BlockIndex.Index`, `OAI.PartitionConsistency.ConservativeMonoids.BlockIndex.Interior`, `OAI.PartitionConsistency.ConservativeMonoids.BlockIndex.cut`, `OAI.PartitionConsistency.ConservativeMonoids.BlockTower`, `OAI.PartitionConsistency.ConservativeMonoids.BlockTower.flatStage`, `OAI.PartitionConsistency.ConservativeMonoids.BlockTower.flatten`, `OAI.PartitionConsistency.ConservativeMonoids.Cell`, `OAI.PartitionConsistency.ConservativeMonoids.Cell.Generators`, `OAI.PartitionConsistency.ConservativeMonoids.Cell.cast`, `OAI.PartitionConsistency.ConservativeMonoids.Cell.extension`, `OAI.PartitionConsistency.ConservativeMonoids.Cell.generator` and 407 more.
--
--   **Sources.** They come from these modules of lean/OAI/SetTheory/PartitionConsistency, in whole or in part: `PartitionConsistency_Algebra_ConservativeExtensions`, `PartitionConsistency_Algebra_DiagramOrder`, `PartitionConsistency_Algebra_DirectLimits`, `PartitionConsistency_Algebra_MergerCones`, `PartitionConsistency_Algebra_MergerWords`, `PartitionConsistency_Algebra_PersistentProfiles`, `PartitionConsistency_Algebra_PlacementExtensions`, `PartitionConsistency_Algebra_ProbeGates`, `PartitionConsistency_Algebra_ProbeMargins`, `PartitionConsistency_Algebra_ProbePresentations`, `PartitionConsistency_Algebra_ProbeWords`, `PartitionConsistency_Construction_BlockTowers`, `PartitionConsistency_Construction_CellCuts`, `PartitionConsistency_Construction_CellReorder`, `PartitionConsistency_Construction_CellTowers`, `PartitionConsistency_Construction_CompleteRounds`, `PartitionConsistency_Construction_ConservativeCells`, `PartitionConsistency_Construction_ConservativeHulls`, `PartitionConsistency_Construction_DiagramPlacements`, `PartitionConsistency_Construction_MergerPushouts`, `PartitionConsistency_Construction_MonoidBase`, `PartitionConsistency_Construction_MonoidRounds`, `PartitionConsistency_Construction_MonoidTowers`, `PartitionConsistency_Construction_SaturatedMonoids`, `PartitionConsistency_Forcing_AtomicForcing`, `PartitionConsistency_Forcing_ChoiceFailure`, `PartitionConsistency_Forcing_CohenForcing`, `PartitionConsistency_Forcing_Diagrams`, `PartitionConsistency_Forcing_ForcingNames`, `PartitionConsistency_Forcing_ForcingQuotient`, `PartitionConsistency_Forcing_ForcingTruth`, `PartitionConsistency_Forcing_ProductForcing`, `PartitionConsistency_Forcing_ProductNames`, `PartitionConsistency_Forcing_RelationCalculus`, `PartitionConsistency_Forcing_SupportFilter`, `PartitionConsistency_Forcing_SymmetricNames`, `PartitionConsistency_Forcing_SymmetricSets`, `PartitionConsistency_Logic_Completeness`, `PartitionConsistency_Logic_Proofs`, `PartitionConsistency_Models_AvailableRecords`, `PartitionConsistency_Models_ClassFibers`, `PartitionConsistency_Models_CodeCardinals`, `PartitionConsistency_Models_ComponentGluing`, `PartitionConsistency_Models_ConcreteQuotients`, `PartitionConsistency_Models_ConcreteSystem`, `PartitionConsistency_Models_GermSelectors`, `PartitionConsistency_Models_GraphFusion`, `PartitionConsistency_Models_LocalQuotients`, `PartitionConsistency_Models_LocalRecords`, `PartitionConsistency_Models_OrbitNames`, `PartitionConsistency_Models_OrdinalChoice`, `PartitionConsistency_Models_OrdinalCodes`, `PartitionConsistency_Models_OrdinalPresentation`, `PartitionConsistency_Models_PersistentCodes`, `PartitionConsistency_Models_QuotientActions`, `PartitionConsistency_Models_QuotientTransport`, `PartitionConsistency_Models_StableSelectors`, `PartitionConsistency_Models_TailGraphs`, `PartitionConsistency_Models_UniformImages`.
--
--   **Imports.** It imports the published bundle `Def_PartitionConsistency`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ5T1002`.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); definitions carved from lean/OAI/SetTheory/PartitionConsistency at commit adc7f12

import Mathlib
import Definitions.Def_PartitionConsistency

section
-- module Solutions.OAIQ5_T1.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Algebra_DiagramOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency
namespace DiagramOrder

/-- Conicality is the condition from the source, not right cancellation. -/
class IsConical (M : Type*) [Monoid M] : Prop where
  eq_one_of_mul_eq_one {x y : M} : x * y = 1 → x = 1 ∧ y = 1

/-- The underlying monoid, equipped with the left-divisibility order below. -/
def LeftDivOrder (M : Type*) := M

namespace LeftDivOrder

instance instMonoid {M : Type*} [Monoid M] : Monoid (LeftDivOrder M) :=
  inferInstanceAs (Monoid M)

instance instLeftCancelMonoid {M : Type*} [LeftCancelMonoid M] : LeftCancelMonoid (LeftDivOrder M) :=
  inferInstanceAs (LeftCancelMonoid M)

instance instIsConical {M : Type*} [Monoid M] [IsConical M] : IsConical (LeftDivOrder M) :=
  inferInstanceAs (IsConical M)

instance instPartialOrderOfIsConical {M : Type*} [LeftCancelMonoid M] [IsConical M] : PartialOrder (LeftDivOrder M) where
  le x y := ∃ z, x * z = y
  le_refl x := ⟨1, mul_one x⟩
  le_trans x y z hxy hyz := by
    obtain ⟨u, hu⟩ := hxy
    obtain ⟨v, hv⟩ := hyz
    exact ⟨u * v, by rw [← mul_assoc, hu, hv]⟩
  le_antisymm x y hxy hyx := by
    obtain ⟨u, hu⟩ := hxy
    obtain ⟨v, hv⟩ := hyx
    have huv : u * v = 1 := by
      apply mul_left_cancel (a := x)
      rw [← mul_assoc, hu, hv, mul_one]
    have hu₁ := (IsConical.eq_one_of_mul_eq_one huv).1
    simpa only [hu₁, mul_one] using hu

instance instOrderBot {M : Type*} [LeftCancelMonoid M] [IsConical M] : OrderBot (LeftDivOrder M) where
  bot := 1
  bot_le x := ⟨x, one_mul x⟩

end LeftDivOrder

variable {α : Type*} [PartialOrder α]

/-- Exact height and cost hypotheses from equation (mono-margin). For the
strict comparisons used in that equation, the set of costs is nonempty
and bounded; the real conditional supremum is therefore the ordinary one. -/
structure HeightCost (α : Type*) [PartialOrder α] where
  height : α → ℝ
  cost : α → ℝ
  height_pos : ∀ x, 0 < height x
  height_lt_one : ∀ x, height x < 1
  cost_pos : ∀ x, 0 < cost x
  cost_le_one : ∀ x, cost x ≤ 1
  margin {x y : α} : x < y →
    sSup (cost '' {d | d ≤ y ∧ ¬ d ≤ x}) < height y - height x

namespace HeightCost
variable (H : HeightCost α)

/-- Each missing divisor's positive cost is paid by the height increase. -/
theorem point_margin {x y d : α} (hxy : x < y) (hdy : d ≤ y) (hdx : ¬ d ≤ x) :
    H.cost d < H.height y - H.height x := by
  have hb : BddAbove (H.cost '' {d | d ≤ y ∧ ¬ d ≤ x}) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨a, _, rfl⟩
    exact H.cost_le_one a
  exact (le_csSup hb ⟨d, ⟨hdy, hdx⟩, rfl⟩).trans_lt (H.margin hxy)

theorem strictMono_height : StrictMono H.height := by
  intro x y hxy
  have h := H.point_margin hxy le_rfl (not_le_of_gt hxy)
  have hp := H.cost_pos y
  linarith

end HeightCost

/-- A conditional join exists exactly for pairs possessing a common upper
bound. In the divisibility order this says that the intersection of two
principal right cones, when nonempty, is a principal right cone. -/
def HasConditionalJoins (α : Type*) [PartialOrder α] : Prop :=
  ∀ x y a : α, x ≤ a → y ≤ a → ∃ j, IsLUB {x, y} j

/-- An ideal in the source's bounded cone: nonempty and downward closed,
contained in the cone, and closed under its finite nonempty joins. Closure
under binary joins suffices, since singleton joins add no new condition. -/
structure ConeIdeal (a : α) where
  carrier : Set α
  nonempty : carrier.Nonempty
  bounded : carrier ⊆ Set.Iic a
  lower : IsLowerSet carrier
  join_closed {x y j : α} : x ∈ carrier → y ∈ carrier → IsLUB {x, y} j → j ∈ carrier

namespace ConeIdeal

/-- Equality of bounded ideals is equality of their underlying subsets. -/
@[ext] theorem ext {a : α} {U V : ConeIdeal a} (h : U.carrier = V.carrier) : U = V := by
  cases U
  cases V
  cases h
  rfl

end ConeIdeal
end DiagramOrder
end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_CohenForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency
namespace CohenForcing
universe u v
variable {I : Type u} {κ : Type v}

/-- Countable partial functions `I × κ → 2`, represented by their graphs.
Countability of the graph is equivalent to countability of the domain for
these single-valued graphs. Conditions are ordered by reverse inclusion. -/
structure Condition (I : Type u) (κ : Type v) where
  graph : Set ((I × κ) × Bool)
  functional : ∀ (a : I × κ) (b c : Bool), (a, b) ∈ graph → (a, c) ∈ graph → b = c
  countable_graph : graph.Countable

namespace Condition

@[ext] theorem ext {p q : Condition I κ} (h : p.graph = q.graph) : p = q := by
  cases p; cases q; cases h; rfl

instance instPartialOrder : PartialOrder (Condition I κ) where
  le p q := q.graph ⊆ p.graph
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ hpq hqr := hqr.trans hpq
  le_antisymm _ _ hpq hqp := ext (Set.Subset.antisymm hqp hpq)

@[simp] theorem le_iff (p q : Condition I κ) : p ≤ q ↔ q.graph ⊆ p.graph := Iff.rfl

instance instOrderTop : OrderTop (Condition I κ) where
  top := ⟨∅, by simp, Set.countable_empty⟩
  le_top _ := Set.empty_subset _

@[simp] theorem graph_top : (⊤ : Condition I κ).graph = ∅ := rfl

def dom (p : Condition I κ) : Set (I × κ) := Prod.fst '' p.graph
def support (p : Condition I κ) : Set I := Prod.fst '' p.dom

theorem countable_dom (p : Condition I κ) : p.dom.Countable :=
  p.countable_graph.image _

theorem countable_support (p : Condition I κ) : p.support.Countable :=
  p.countable_dom.image _

@[simp] theorem mem_dom (p : Condition I κ) (a : I × κ) :
    a ∈ p.dom ↔ ∃ b : Bool, (a, b) ∈ p.graph := by
  constructor
  · rintro ⟨⟨a', b⟩, h, rfl⟩
    exact ⟨b, h⟩
  · rintro ⟨b, hb⟩
    exact ⟨(a, b), hb, rfl⟩

@[simp] theorem mem_support (p : Condition I κ) (j : I) :
    j ∈ p.support ↔ ∃ a : κ, ∃ b : Bool, ((j, a), b) ∈ p.graph := by
  constructor
  · rintro ⟨⟨j', a⟩, h, rfl⟩
    exact ⟨a, (mem_dom p _).1 h⟩
  · rintro ⟨a, b, hb⟩
    exact ⟨(j, a), (mem_dom p _).2 ⟨b, hb⟩, rfl⟩

/-- Compatibility is exactly agreement wherever both assignments are defined. -/
def Compatible (p q : Condition I κ) : Prop :=
  ∀ a b c, (a, b) ∈ p.graph → (a, c) ∈ q.graph → b = c

def union (p q : Condition I κ) (h : Compatible p q) : Condition I κ where
  graph := p.graph ∪ q.graph
  functional := by
    intro a b c hb hc
    rcases hb with hb | hb <;> rcases hc with hc | hc
    · exact p.functional a b c hb hc
    · exact h a b c hb hc
    · exact (h a c b hc hb).symm
    · exact q.functional a b c hb hc
  countable_graph := p.countable_graph.union q.countable_graph

@[simp] theorem union_graph (p q : Condition I κ) (h : Compatible p q) :
    (union p q h).graph = p.graph ∪ q.graph := rfl

theorem union_le_left (p q : Condition I κ) (h : Compatible p q) : union p q h ≤ p :=
  Set.subset_union_left

theorem union_le_right (p q : Condition I κ) (h : Compatible p q) : union p q h ≤ q :=
  Set.subset_union_right

theorem compatible_iff {p q : Condition I κ} :
    Compatible p q ↔ ∃ r : Condition I κ, r ≤ p ∧ r ≤ q := by
  constructor
  · intro h
    exact ⟨union p q h, union_le_left p q h, union_le_right p q h⟩
  · rintro ⟨r, hp, hq⟩ a b c hb hc
    exact r.functional a b c (hp hb) (hq hc)

/-- Restriction to a set of label coordinates. -/
def restrict (p : Condition I κ) (J : Set I) : Condition I κ where
  graph := {z | z ∈ p.graph ∧ z.1.1 ∈ J}
  functional a b c hb hc := p.functional a b c hb.1 hc.1
  countable_graph := p.countable_graph.mono (fun _ h => h.1)

@[simp] theorem mem_restrict (p : Condition I κ) (J : Set I) (z : (I × κ) × Bool) :
    z ∈ (restrict p J).graph ↔ z ∈ p.graph ∧ z.1.1 ∈ J := Iff.rfl

theorem le_restrict (p : Condition I κ) (J : Set I) : p ≤ restrict p J :=
  fun _ h => h.1

theorem support_restrict_subset (p : Condition I κ) (J : Set I) :
    (restrict p J).support ⊆ J := by
  intro j hj
  obtain ⟨a, b, hab⟩ := (mem_support _ _).1 hj
  exact hab.2

/-- Define the coordinate action on the full graph, including both the ordinal
input and its Boolean output. -/
def coordinatePerm (π : Equiv.Perm I) : Equiv.Perm ((I × κ) × Bool) :=
  (π.prodCongr (Equiv.refl κ)).prodCongr (Equiv.refl Bool)

@[simp] theorem coordinatePerm_apply (π : Equiv.Perm I) (z : (I × κ) × Bool) :
    coordinatePerm π z = ((π z.1.1, z.1.2), z.2) := rfl
@[simp] theorem coordinatePerm_symm_apply (π : Equiv.Perm I) (z : (I × κ) × Bool) :
    (coordinatePerm π).symm z = ((π.symm z.1.1, z.1.2), z.2) := rfl

def permute (π : Equiv.Perm I) (p : Condition I κ) : Condition I κ where
  graph := coordinatePerm π '' p.graph
  functional a b c hb hc :=
    p.functional (π.symm a.1, a.2) b c
      (Set.mem_image_equiv.1 hb) (Set.mem_image_equiv.1 hc)
  countable_graph := p.countable_graph.image _

@[simp] theorem mem_permute (π : Equiv.Perm I) (p : Condition I κ) (z : (I × κ) × Bool) :
    z ∈ (permute π p).graph ↔ ((π.symm z.1.1, z.1.2), z.2) ∈ p.graph :=
  Set.mem_image_equiv

@[simp] theorem permute_one (p : Condition I κ) : permute 1 p = p := by
  ext z
  simp [Equiv.Perm.one_def]

@[simp] theorem permute_mul (π σ : Equiv.Perm I) (p : Condition I κ) :
    permute (π * σ) p = permute π (permute σ p) := by
  apply ext
  ext z
  simp [Equiv.Perm.mul_def]

@[simp] theorem permute_inv_permute (π : Equiv.Perm I) (p : Condition I κ) :
    permute π⁻¹ (permute π p) = p := by
  apply ext
  ext z
  simp [Equiv.Perm.inv_def]

@[simp] theorem permute_permute_inv (π : Equiv.Perm I) (p : Condition I κ) :
    permute π (permute π⁻¹ p) = p := by
  apply ext
  ext z
  simp [Equiv.Perm.inv_def]

/-- The same label permutations used for diagrams are order automorphisms of
Cohen forcing. They can therefore act diagonally on the product. -/
def permuteOrderIso (π : Equiv.Perm I) : Condition I κ ≃o Condition I κ where
  toFun := permute π
  invFun := permute π⁻¹
  left_inv := permute_inv_permute π
  right_inv := permute_permute_inv π
  map_rel_iff' := by
    intro p q
    change coordinatePerm π '' q.graph ⊆ coordinatePerm π '' p.graph ↔ q.graph ⊆ p.graph
    exact Set.image_subset_image_iff (coordinatePerm π).injective

/-- Two conditions agreeing on their common root and having disjoint nonroot
supports are compatible. This is the Cohen half of the locality argument. -/
theorem compatible_of_disjoint_off_root (p q : Condition I κ) (J : Set I)
    (hroot : Compatible (restrict p J) (restrict q J))
    (hdisj : Disjoint (p.support \ J) (q.support \ J)) : Compatible p q := by
  intro a b c hb hc
  by_cases ha : a.1 ∈ J
  · exact hroot a b c ⟨hb, ha⟩ ⟨hc, ha⟩
  · exact False.elim (Set.disjoint_left.1 hdisj
      ⟨(mem_support p _).2 ⟨a.2, b, hb⟩, ha⟩
      ⟨(mem_support q _).2 ⟨a.2, c, hc⟩, ha⟩)

/-- Introduce one unassigned coordinate with a specified Boolean value. -/
def insert (p : Condition I κ) (a : I × κ) (b : Bool) (h : a ∉ p.dom) : Condition I κ where
  graph := Set.insert (a, b) p.graph
  functional := by
    intro x c d hc hd
    rcases hc with hc | hc <;> rcases hd with hd | hd
    · exact (congrArg Prod.snd hc).trans (congrArg Prod.snd hd).symm
    · cases hc
      exact False.elim (h ((mem_dom p _).2 ⟨d, hd⟩))
    · cases hd
      exact False.elim (h ((mem_dom p _).2 ⟨c, hc⟩))
    · exact p.functional x c d hc hd
  countable_graph := p.countable_graph.insert _

end Condition
end CohenForcing
end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Logic_Proofs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



/-! ## Logical and set-forcing foundations -/

/-! Ordinary first-order membership syntax and classical natural deduction.
Consistency is syntactic. The forcing interpretation ranges over all
hereditarily symmetric pure-set names without a rank bound. -/












namespace PartitionConsistency

namespace Formula

@[simp] theorem snoc_comp_liftRen {M : Type*} {n m} (v : Fin m → M)
    (x : M) (r : Fin n → Fin m) :
    Fin.snoc v x ∘ liftRen r = Fin.snoc (v ∘ r) x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftRen]

end Formula

/-! Finite support for first-order proof translation. -/

-- The set-theoretic sentences are defined below, with only first-order binders.
end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_ForcingQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency
/-! External generic filters and the name-quotient truth lemma.
These results do not supply the internal symmetric system or its ZF axioms.
They work on a set of name codes with specified atomic forcing relations. -/
namespace ForcingQuotient

/-- A forcing filter is an order ideal for the opposite order. -/
abbrev GenericFilter (P : Type*) [Preorder P] := Order.Ideal (OrderDual P)

variable {P : Type*} [Preorder P]

/-- Atomic forcing laws on a set of name codes. These are only the equality,
substitution and monotonicity laws; this structure contains no ZF axioms,
Choice or Partition Principle assertions. -/
structure AtomicData (P N : Type*) [Preorder P] where
  EqF : P → N → N → Prop
  MemF : P → N → N → Prop
  eq_mono {p q a b} : q ≤ p → EqF p a b → EqF q a b
  mem_mono {p q a b} : q ≤ p → MemF p a b → MemF q a b
  eq_refl (p a) : EqF p a a
  eq_symm {p a b} : EqF p a b → EqF p b a
  eq_trans {p a b c} : EqF p a b → EqF p b c → EqF p a c
  mem_congr {p a a' b b'} : EqF p a a' → EqF p b b' →
    (MemF p a b ↔ MemF p a' b')

namespace AtomicData
variable {N : Type*} (A : AtomicData P N) (G : GenericFilter P)

/-- Equality of codes after adjoining the generic filter. -/
def EqG (a b : N) : Prop := ∃ p, p ∈ G ∧ A.EqF p a b

theorem eqG_refl (a : N) : A.EqG G a a := by
  obtain ⟨p, hp⟩ := G.nonempty
  exact ⟨p, hp, A.eq_refl p a⟩

theorem eqG_symm {a b : N} (h : A.EqG G a b) : A.EqG G b a := by
  obtain ⟨p, hp, hab⟩ := h
  exact ⟨p, hp, A.eq_symm hab⟩

theorem eqG_trans {a b c : N} (h : A.EqG G a b) (k : A.EqG G b c) :
    A.EqG G a c := by
  obtain ⟨p, hp, hab⟩ := h
  obtain ⟨q, hq, hbc⟩ := k
  obtain ⟨r, hr, hrp, hrq⟩ := G.directed _ hp _ hq
  exact ⟨r, hr, A.eq_trans (A.eq_mono hrp hab) (A.eq_mono hrq hbc)⟩

end AtomicData

/-- A basis of classical first-order syntax, with last-variable binders.
All formulas in the target language translate to this basis. -/
inductive BasicFormula : ℕ → Type where
  | bot {n} : BasicFormula n
  | mem {n} (x y : Fin n) : BasicFormula n
  | equal {n} (x y : Fin n) : BasicFormula n
  | conj {n} (p q : BasicFormula n) : BasicFormula n
  | neg {n} (p : BasicFormula n) : BasicFormula n
  | ex {n} (p : BasicFormula (n + 1)) : BasicFormula n
  deriving Countable

namespace BasicFormula

def Realize {M : Type*} (E : M → M → Prop) {n} (v : Fin n → M) : BasicFormula n → Prop
  | .bot => False
  | .mem x y => E (v x) (v y)
  | .equal x y => v x = v y
  | .conj p q => Realize E v p ∧ Realize E v q
  | .neg p => ¬ Realize E v p
  | .ex p => ∃ x : M, Realize E (Fin.snoc v x) p

end BasicFormula

namespace AtomicData
variable {N : Type*} (A : AtomicData P N)

/-- Formula-by-formula forcing: existential forcing is local density, NOT a
maximum principle or selection of a single global witness name. -/
def Force (A : AtomicData P N) {n} (v : Fin n → N) (p : P) : BasicFormula n → Prop
  | .bot => False
  | .mem x y => A.MemF p (v x) (v y)
  | .equal x y => A.EqF p (v x) (v y)
  | .conj φ ψ => A.Force v p φ ∧ A.Force v p ψ
  | .neg φ => ∀ q, q ≤ p → ¬ A.Force v q φ
  | .ex φ => ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x : N, A.Force (Fin.snoc v x) r φ

theorem force_mono {n} (φ : BasicFormula n) (v : Fin n → N) {p q : P}
    (hqp : q ≤ p) (h : A.Force v p φ) : A.Force v q φ := by
  induction φ with
  | bot => exact h
  | mem => exact A.mem_mono hqp h
  | equal => exact A.eq_mono hqp h
  | conj φ ψ hφ hψ => exact ⟨hφ v h.1, hψ v h.2⟩
  | neg φ _ => exact fun r hr => h r (hr.trans hqp)
  | ex φ _ => exact fun r hr => h r (hr.trans hqp)

end AtomicData
end ForcingQuotient

namespace Formula
open ForcingQuotient

/-- Translation to the finite Boolean/existential basis used in the quotient
truth proof. This changes no set-theoretic predicate or quantifier domain. -/
def toBasic {n} : Formula n → BasicFormula n
  | .bot => .bot
  | .mem x y => .mem x y
  | .equal x y => .equal x y
  | .imp φ ψ => .neg (.conj (toBasic φ) (.neg (toBasic ψ)))
  | .conj φ ψ => .conj (toBasic φ) (toBasic ψ)
  | .disj φ ψ => .neg (.conj (.neg (toBasic φ)) (.neg (toBasic ψ)))
  | .all φ => .neg (.ex (.neg (toBasic φ)))
  | .ex φ => .ex (toBasic φ)

end Formula

end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Algebra_PlacementExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency

namespace CohenForcing.Condition
universe u v w
variable {I : Type u} {κ : Type v} {A : Type w}

@[refl] theorem Compatible.refl (p : Condition I κ) : Compatible p p := p.functional

/-- The explicit ground dense set in the probe argument for ordinal choice
(source equation `eq:probe-cohen-dense`). It contains conditions incompatible
with the common root and conditions extending one of the placed copies. -/
def probeDenseSet (root : Condition I κ) (copies : A → Condition I κ) :
    Set (Condition I κ) :=
  {c | ¬ Compatible c root ∨ ∃ a, c ≤ copies a}

end CohenForcing.Condition
end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_Diagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency
namespace DiagramForcing
universe u
variable {M I : Type u}

/-- An actual injective diagram on all of the monoid, with no finite or rank
cutoff. Stronger diagrams are the larger diagrams in the translation order. -/
structure Diagram (M I : Type u) where
  toEmbedding : M ↪ I

namespace Diagram
instance instCoeFunForall : CoeFun (Diagram M I) (fun _ => M → I) := ⟨fun r => (r.toEmbedding : M → I)⟩
@[ext] theorem ext {r s : Diagram M I} (h : ∀ x, r x = s x) : r = s :=
  by cases r; cases s; congr 1; exact Function.Embedding.ext h

theorem injective (r : Diagram M I) : Function.Injective r :=
  r.toEmbedding.injective

variable [LeftCancelMonoid M]
def sub (r : Diagram M I) (n : M) : Diagram M I :=
  ⟨⟨fun x => r (n * x), r.injective.comp (fun _ _ h => mul_left_cancel h)⟩⟩

@[simp] theorem sub_apply (r : Diagram M I) (n x : M) : sub r n x = r (n * x) := rfl
@[simp] theorem sub_one (r : Diagram M I) : sub r 1 = r := by ext; simp
@[simp] theorem sub_sub (r : Diagram M I) (n m : M) : sub (sub r n) m = sub r (n * m) := by
  ext x
  simp [mul_assoc]

theorem index_unique {r : Diagram M I} {n m : M} (h : sub r n = sub r m) : n = m := by
  have he := congrArg (fun s : Diagram M I => s 1) h
  exact r.injective (by simpa using he)

def range (r : Diagram M I) : Set I := Set.range r

theorem range_sub_subset (r : Diagram M I) (n : M) : (sub r n).range ⊆ r.range := by
  rintro i ⟨x, hx⟩
  exact ⟨n * x, hx⟩

instance instPartialOrderOfIsConical [DiagramOrder.IsConical M] : PartialOrder (Diagram M I) where
  le r s := ∃ n, sub r n = s
  le_refl r := ⟨1, sub_one r⟩
  le_trans r s t hrs hst := by
    obtain ⟨n, hn⟩ := hrs
    obtain ⟨m, hm⟩ := hst
    exact ⟨n * m, by rw [← sub_sub, hn, hm]⟩
  le_antisymm r s hrs hsr := by
    obtain ⟨n, hn⟩ := hrs
    obtain ⟨m, hm⟩ := hsr
    have he : sub r (n * m) = sub r 1 := by rw [← sub_sub, hn, hm, sub_one]
    have hn₁ := (DiagramOrder.IsConical.eq_one_of_mul_eq_one (index_unique he)).1
    simpa [hn₁] using hn

@[simp] theorem le_iff [DiagramOrder.IsConical M] (r s : Diagram M I) :
    r ≤ s ↔ ∃ n, sub r n = s := Iff.rfl

theorem range_antitone [DiagramOrder.IsConical M] :
    Antitone (range : Diagram M I → Set I) := by
  rintro r s ⟨n, rfl⟩
  exact range_sub_subset r n

/-- Label permutations act on the entire diagram, not on its monoid positions. -/
def permute (π : Equiv.Perm I) (r : Diagram M I) : Diagram M I :=
  ⟨r.toEmbedding.trans π.toEmbedding⟩

omit [LeftCancelMonoid M] in
@[simp] theorem permute_apply (π : Equiv.Perm I) (r : Diagram M I) (x : M) :
    permute π r x = π (r x) := rfl
omit [LeftCancelMonoid M] in
@[simp] theorem permute_one (r : Diagram M I) : permute 1 r = r := by ext; rfl
omit [LeftCancelMonoid M] in
@[simp] theorem permute_mul (π σ : Equiv.Perm I) (r : Diagram M I) :
    permute (π * σ) r = permute π (permute σ r) := by ext; rfl
@[simp] theorem permute_sub (π : Equiv.Perm I) (r : Diagram M I) (n : M) :
    permute π (sub r n) = sub (permute π r) n := by ext; rfl

omit [LeftCancelMonoid M] in
@[simp] theorem permute_inv_permute (π : Equiv.Perm I) (r : Diagram M I) :
    permute π⁻¹ (permute π r) = r := by ext; simp
omit [LeftCancelMonoid M] in
@[simp] theorem permute_permute_inv (π : Equiv.Perm I) (r : Diagram M I) :
    permute π (permute π⁻¹ r) = r := by ext; simp

/-- The label action preserves and reflects the forcing order. -/
def permuteOrderIso [DiagramOrder.IsConical M] (π : Equiv.Perm I) :
    Diagram M I ≃o Diagram M I where
  toFun := permute π
  invFun := permute π⁻¹
  left_inv r := by ext; simp
  right_inv r := by ext; simp
  map_rel_iff' := by
    intro r s
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have he := congrArg (permute π⁻¹) hn
      simpa using he
    · rintro ⟨n, rfl⟩
      exact ⟨n, (permute_sub _ _ _).symm⟩

end Diagram

/-- A finite overlap prescription, before transitive closure. `none` specifies
no overlap; `some (a,b)` identifies `(i,a*x)` with `(j,b*x)` for each `x`. -/
structure OverlapPrescription (M : Type u) (n : ℕ) where
  start : Fin n → Fin n → Option (M × M)

namespace OverlapPrescription
variable [Monoid M] {n : ℕ}

def Rel (P : OverlapPrescription M n) (z w : Fin n × M) : Prop :=
  if z.1 = w.1 then z.2 = w.2 else
    match P.start z.1 w.1 with
    | none => False
    | some (a, b) => ∃ t, z.2 = a * t ∧ w.2 = b * t

/-- The indicated pair identifications must already be an equivalence,
without adding further overlaps by transitive closure. Equality within a copy
is built into `Rel`. -/
def Valid (P : OverlapPrescription M n) : Prop := Equivalence P.Rel

@[simp] theorem rel_same_copy (P : OverlapPrescription M n) (i : Fin n) (x y : M) :
    P.Rel (i, x) (i, y) ↔ x = y := by simp [Rel]

end OverlapPrescription

/-- Precisely the finite-overlap realization property in `thm:monoid`, item 2.
Existence of a monoid having this property is still a separate obligation. -/
def HasFiniteMergers (M : Type u) [Monoid M] : Prop :=
  ∀ (n : ℕ) (P : OverlapPrescription M n), P.Valid →
    ∃ l : Fin n → M, ∀ z w : Fin n × M,
      l z.1 * z.2 = l w.1 * w.2 ↔ P.Rel z w

end DiagramForcing
end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Algebra_MergerWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency
namespace DiagramOrder
lemma pair_lub_iff {α : Type*} [Preorder α] (a b j : α) :
    IsLUB {a, b} j ↔ ∀ z, a ≤ z ∧ b ≤ z ↔ j ≤ z := by
  simp only [isLUB_iff_le_iff, upperBounds, Set.mem_ofPred_eq,
    Set.forall_mem_insert, Set.mem_singleton_iff, forall_eq]
  exact forall_congr' (fun _ => iff_comm)
namespace LeftDivOrder
lemma le_iff_dvd {M : Type*} [LeftCancelMonoid M] [IsConical M]
    (x y : LeftDivOrder M) : x ≤ y ↔ x ∣ y := by
  exact exists_congr (fun _ => eq_comm)
end LeftDivOrder
lemma exists_cone_join {M : Type*} [LeftCancelMonoid M] [IsConical M]
    (hM : HasConditionalJoins (LeftDivOrder M)) (x y a : M)
    (hx : x ∣ a) (hy : y ∣ a) :
    ∃ j : M, ∀ z : M, x ∣ z ∧ y ∣ z ↔ j ∣ z := by
  obtain ⟨j, hj⟩ := hM x y a ((LeftDivOrder.le_iff_dvd _ _).2 hx)
    ((LeftDivOrder.le_iff_dvd _ _).2 hy)
  refine ⟨j, ?_⟩
  intro z
  have hz := (pair_lub_iff (α := LeftDivOrder M) x y j).1 hj z
  rw [LeftDivOrder.le_iff_dvd (M := M) x z,
    LeftDivOrder.le_iff_dvd (M := M) y z,
    LeftDivOrder.le_iff_dvd (M := M) j z] at hz
  exact hz
/-- Cancellation for right divisibility in a left-cancellative monoid. -/
theorem left_mul_dvd_iff {M : Type*} [LeftCancelMonoid M] (a x y : M) :
    a * x ∣ a * y ↔ x ∣ y := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, mul_left_cancel (hz.trans (mul_assoc a x z))⟩
  · exact mul_dvd_mul_left a

/-- A nonempty inverse image of a principal right cone under left
multiplication is principal. Its initial element is the right quotient
of the conditional join. -/
theorem exists_cone_residual {M : Type*} [LeftCancelMonoid M]
    (hM : ∀ x y a : M, x ∣ a → y ∣ a → ∃ j : M, ∀ b : M, x ∣ b ∧ y ∣ b ↔ j ∣ b)
    (x a c : M) (hc : x ∣ a * c) :
    ∃ r : M, ∀ t : M, x ∣ a * t ↔ r ∣ t := by
  obtain ⟨s, hs⟩ := hM x a (a * c) hc (dvd_mul_right a c)
  obtain ⟨r, rfl⟩ := ((hs s).2 (dvd_refl s)).2
  refine ⟨r, fun t => ?_⟩
  calc
    x ∣ a * t ↔ x ∣ a * t ∧ a ∣ a * t :=
      ⟨fun h => ⟨h, dvd_mul_right _ _⟩, And.left⟩
    _ ↔ a * r ∣ a * t := hs _
    _ ↔ r ∣ t := left_mul_dvd_iff a r t

end DiagramOrder

namespace MergerAlgebra
universe u v

/-- A right action in which each orbit map is injective. This is the
property of the prescribed quotient of copies used in the merger normal
forms. It does not posit the existence of any monoid extension. -/
class RightFreeAction (M : Type u) (D : Type v) [Monoid M] where
  act : D → M → D
  act_one : ∀ d, act d 1 = d
  act_mul : ∀ d x y, act (act d x) y = act d (x * y)
  factor_injective : ∀ d, Function.Injective (act d)

namespace RightFreeAction
variable {M : Type u} {D : Type v} [Monoid M] [RightFreeAction M D]

/-- The right divisibility relation on a right monoid-set. -/
def Reaches (M : Type u) {D : Type v} [Monoid M] [RightFreeAction M D]
    (z w : D) : Prop := ∃ m : M, act z m = w

@[refl] theorem reaches_refl (z : D) : Reaches M z z := ⟨1, act_one z⟩

theorem reaches_trans {z w v : D} (hzw : Reaches M z w) (hwv : Reaches M w v) :
    Reaches M z v := by
  obtain ⟨m, hm⟩ := hzw
  obtain ⟨n, hn⟩ := hwv
  exact ⟨m * n, by rw [← act_mul, hm, hn]⟩

/-- Conditional joins expressed as exact intersections of right cones. -/
def HasConeJoins (M : Type u) (D : Type v) [Monoid M] [RightFreeAction M D] : Prop :=
  ∀ z w a : D, Reaches M z a → Reaches M w a →
    ∃ j : D, ∀ b : D, Reaches M z b ∧ Reaches M w b ↔ Reaches M j b

end RightFreeAction

/-- The literal normal forms `x z₁ ... zⱼ` of equation
`eq:mono-merger-forms`; words with no new letter are the old monoid. -/
inductive Word (M : Type u) (D : Type v) where
  | old : M → Word M D
  | snoc : Word M D → D → Word M D

namespace Word
variable {M : Type u} {D : Type v} [Monoid M] [RightFreeAction M D]

/-- Multiplication on the right by an old element acts only on the last
new letter (or on the old coefficient, if no new letter is present). -/
def act : Word M D → M → Word M D
  | old x, y => old (x * y)
  | snoc w z, y => snoc w (RightFreeAction.act z y)

@[simp] theorem act_one (w : Word M D) : act w 1 = w := by
  cases w <;> simp [act, RightFreeAction.act_one]

@[simp] theorem act_mul (w : Word M D) (x y : M) :
    act (act w x) y = act w (x * y) := by
  cases w <;> simp [act, mul_assoc, RightFreeAction.act_mul]

/-- Concatenation, absorbing the leading old coefficient of the second
normal form into the last letter of the first. -/
def product (x : Word M D) : Word M D → Word M D
  | old y => act x y
  | snoc y z => snoc (product x y) z

@[simp] theorem product_act (x y : Word M D) (m : M) :
    product x (act y m) = act (product x y) m := by
  cases y with
  | old n => exact (act_mul x n m).symm
  | snoc w d => rfl

theorem product_assoc (x y z : Word M D) :
    product (product x y) z = product x (product y z) := by
  induction z with
  | old m => exact (product_act x y m).symm
  | snoc z d ih => exact congrArg (fun w => snoc w d) ih

theorem old_one_product (w : Word M D) : product (old 1) w = w := by
  induction w with
  | old x => simp [product, act]
  | snoc w z ih => simp [product, ih]

instance instMonoid : Monoid (Word M D) where
  mul := product
  one := old 1
  mul_assoc := product_assoc
  one_mul := old_one_product
  mul_one := act_one

@[simp] theorem mul_old (w : Word M D) (x : M) : w * old x = act w x := rfl
@[simp] theorem mul_snoc (w y : Word M D) (z : D) :
    w * snoc y z = snoc (w * y) z := rfl
@[simp] theorem old_mul_old (x y : M) :
    (old x : Word M D) * old y = old (x * y) := rfl
@[simp] theorem snoc_mul_old (w : Word M D) (z : D) (y : M) :
    snoc w z * old y = snoc w (RightFreeAction.act z y) := rfl

/-- Number of new letters, used to distinguish old from genuinely new words. -/
def length : Word M D → ℕ
  | old _ => 0
  | snoc w _ => length w + 1

omit [Monoid M] [RightFreeAction M D] in
@[simp] theorem length_old (x : M) : length (old x : Word M D) = 0 := rfl
omit [Monoid M] [RightFreeAction M D] in
@[simp] theorem length_snoc (w : Word M D) (z : D) :
    length (snoc w z) = length w + 1 := rfl
@[simp] theorem length_act (w : Word M D) (x : M) : length (act w x) = length w := by
  cases w <;> rfl

@[simp] theorem length_mul (x y : Word M D) : length (x * y) = length x + length y := by
  induction y with
  | old m => simp
  | snoc y d ih => simp [ih, Nat.add_assoc]

omit [Monoid M] [RightFreeAction M D] in
theorem length_zero_iff (w : Word M D) : length w = 0 ↔ ∃ m, w = old m := by
  cases w <;> simp

section Cancellation
variable [IsLeftCancelMul M]

theorem act_injective (w : Word M D) : Function.Injective (act w) := by
  cases w with
  | old x =>
      intro y z he
      exact mul_left_cancel (Word.old.inj he)
  | snoc w d =>
      intro y z he
      exact RightFreeAction.factor_injective d (Word.snoc.inj he).2

/-- Left cancellation is proved from the displayed normal forms. Right
cancellation is neither used nor asserted. -/
theorem product_left_cancel (x : Word M D) {y z : Word M D} (h : x * y = x * z) :
    y = z := by
  induction y generalizing z with
  | old m =>
      cases z with
      | old n => exact congrArg old (act_injective x h)
      | snoc z d =>
          have hl := congrArg length h
          simp only [length_mul, length_old, length_snoc] at hl
          omega
  | snoc y d ih =>
      cases z with
      | old n =>
          have hl := congrArg length h
          simp only [length_mul, length_old, length_snoc] at hl
          omega
      | snoc z e =>
          obtain ⟨h₁, h₂⟩ := Word.snoc.inj h
          exact congrArg₂ snoc (ih h₁) h₂

instance instLeftCancelMonoid : LeftCancelMonoid (Word M D) where
  mul_left_cancel x _ _ := product_left_cancel x

end Cancellation

/-- Letter count prevents a new word from acquiring an old right multiple.
It also identifies the old right factor, rather than just reflecting order. -/
theorem factors_of_old {x y : Word M D} {a : M} (h : x * y = old a) :
    ∃ b c : M, x = old b ∧ y = old c ∧ b * c = a := by
  have hl := congrArg length h
  simp only [length_mul, length_old, Nat.add_eq_zero_iff] at hl
  obtain ⟨b, rfl⟩ := (length_zero_iff x).1 hl.1
  obtain ⟨c, rfl⟩ := (length_zero_iff y).1 hl.2
  exact ⟨b, c, rfl, rfl, Word.old.inj h⟩

instance instIsConical [DiagramOrder.IsConical M] : DiagramOrder.IsConical (Word M D) where
  eq_one_of_mul_eq_one h := by
    obtain ⟨b, c, rfl, rfl, hbc⟩ := factors_of_old h
    obtain ⟨rfl, rfl⟩ := DiagramOrder.IsConical.eq_one_of_mul_eq_one hbc
    exact ⟨rfl, rfl⟩

/-- The old monoid embeds by words with no new letters. -/
def oldHom : M →* Word M D where
  toFun := old
  map_one' := rfl
  map_mul' _ _ := rfl

theorem oldHom_injective : Function.Injective (oldHom : M →* Word M D) := fun _ _ h => Word.old.inj h

/-- The leading old coefficient of the normal form. -/
def leading : Word M D → M
  | old x => x
  | snoc w _ => leading w

omit [Monoid M] [RightFreeAction M D] in
@[simp] theorem leading_old (x : M) : leading (old x : Word M D) = x := rfl
omit [Monoid M] [RightFreeAction M D] in
@[simp] theorem leading_snoc (w : Word M D) (z : D) :
    leading (snoc w z) = leading w := rfl

@[simp] theorem leading_old_mul (x : M) (w : Word M D) :
    leading (old x * w) = x * leading w := by
  induction w with
  | old m => rfl
  | snoc w d ih => exact ih

/-- Old divisors are read solely from the old leading coefficient. -/
theorem old_dvd_iff (x : M) (w : Word M D) :
    old x ∣ w ↔ x ∣ leading w := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨leading z, leading_old_mul x z⟩
  · intro h
    induction w with
    | old y =>
        obtain ⟨a, ha⟩ := h
        exact ⟨old a, congrArg old ha⟩
    | snoc w d ih =>
        obtain ⟨q, hq⟩ := ih h
        exact ⟨snoc q d, congrArg (fun w => snoc w d) hq⟩

/-- Comparisons and common-right-multiple calculations on old entries are
unchanged in the extension, including the absence of a common multiple. -/
theorem old_common_multiple_iff (x y : M) :
    (∃ w : Word M D, old x ∣ w ∧ old y ∣ w) ↔ ∃ a : M, x ∣ a ∧ y ∣ a := by
  constructor
  · rintro ⟨w, hx, hy⟩
    exact ⟨leading w, (old_dvd_iff x w).1 hx, (old_dvd_iff y w).1 hy⟩
  · rintro ⟨a, hx, hy⟩
    exact ⟨old a, (old_dvd_iff x (old a)).2 hx, (old_dvd_iff y (old a)).2 hy⟩

/-- The entire right-cone equation for any old conditional join is preserved,
not just comparisons among old elements. -/
theorem preserve_old_cone_intersection (x y j : M)
    (hj : ∀ a : M, x ∣ a ∧ y ∣ a ↔ j ∣ a) (w : Word M D) :
    old x ∣ w ∧ old y ∣ w ↔ old j ∣ w := by
  simpa only [old_dvd_iff] using hj (leading w)

/-- Dividing a normal form with one more letter means either dividing its
prefix, or having precisely that prefix and advancing the last new letter. -/
theorem dvd_snoc_iff (x w : Word M D) (d : D) :
    x ∣ snoc w d ↔ x ∣ w ∨ ∃ z, x = snoc w z ∧ RightFreeAction.Reaches M z d := by
  constructor
  · rintro ⟨q, hq⟩
    cases q with
    | old m =>
        cases x with
        | old a => cases hq
        | snoc v z =>
            obtain ⟨hw, hd⟩ := Word.snoc.inj hq
            exact Or.inr ⟨z, congrArg (fun v => snoc v z) hw.symm, m, hd.symm⟩
    | snoc q z => exact Or.inl ⟨q, (Word.snoc.inj hq).1⟩
  · rintro (⟨q, hq⟩ | ⟨z, rfl, m, hm⟩)
    · exact ⟨snoc q d, congrArg (fun v => snoc v d) hq⟩
    · exact ⟨old m, congrArg (snoc w) hm.symm⟩

theorem length_le_of_dvd {x y : Word M D} (h : x ∣ y) : length x ≤ length y := by
  obtain ⟨q, rfl⟩ := h
  simp only [length_mul]
  omega

theorem snoc_not_dvd_prefix (w : Word M D) (z : D) : ¬ snoc w z ∣ w := by
  intro h
  have hl := length_le_of_dvd h
  simp only [length_snoc] at hl
  omega

theorem snoc_not_dvd_old (w : Word M D) (z : D) (m : M) : ¬ snoc w z ∣ old m := by
  intro h
  have hl := length_le_of_dvd h
  simp only [length_snoc, length_old] at hl
  omega

theorem snoc_dvd_snoc_iff (w v : Word M D) (z d : D) :
    snoc w z ∣ snoc v d ↔
      snoc w z ∣ v ∨ w = v ∧ RightFreeAction.Reaches M z d := by
  rw [dvd_snoc_iff]
  constructor
  · rintro (h | ⟨e, he, hea⟩)
    · exact Or.inl h
    · obtain ⟨rfl, rfl⟩ := Word.snoc.inj he
      exact Or.inr ⟨rfl, hea⟩
  · rintro (h | ⟨rfl, hz⟩)
    · exact Or.inl h
    · exact Or.inr ⟨z, rfl, hz⟩

/-- With a fixed prefix, the intersection of two word cones is exactly
controlled by the intersection of the final-letter cones in the right set. -/
theorem snoc_cone_intersection (w : Word M D) (z t j : D)
    (hj : ∀ d : D, RightFreeAction.Reaches M z d ∧ RightFreeAction.Reaches M t d ↔
      RightFreeAction.Reaches M j d) (a : Word M D) :
    snoc w z ∣ a ∧ snoc w t ∣ a ↔ snoc w j ∣ a := by
  induction a with
  | old m => simp only [snoc_not_dvd_old, false_and]
  | snoc a d ih =>
      simp only [snoc_dvd_snoc_iff]
      by_cases hw : w = a
      · subst a
        simp only [snoc_not_dvd_prefix, true_and, false_or, hj]
      · simpa only [hw, false_and, or_false] using ih

/-- Conditional joins for all normal forms, not only for translated copies.
The induction is on the normal form of a common upper bound. -/
theorem exists_cone_join
    (hM : ∀ x y a : M, x ∣ a → y ∣ a → ∃ j : M, ∀ b : M, x ∣ b ∧ y ∣ b ↔ j ∣ b)
    (hD : RightFreeAction.HasConeJoins M D) (x y a : Word M D)
    (hx : x ∣ a) (hy : y ∣ a) :
    ∃ j : Word M D, ∀ b : Word M D, x ∣ b ∧ y ∣ b ↔ j ∣ b := by
  induction a generalizing x y with
  | old m =>
      obtain ⟨qx, hqx⟩ := hx
      obtain ⟨qy, hqy⟩ := hy
      obtain ⟨r, s, rfl, rfl, hxm⟩ := factors_of_old hqx.symm
      obtain ⟨t, u, rfl, rfl, hym⟩ := factors_of_old hqy.symm
      obtain ⟨j, hj⟩ := hM r t m ⟨s, hxm.symm⟩ ⟨u, hym.symm⟩
      exact ⟨old j, preserve_old_cone_intersection r t j hj⟩
  | snoc a d ih =>
      rcases (dvd_snoc_iff x a d).1 hx with hx | ⟨z, rfl, hz⟩
      · rcases (dvd_snoc_iff y a d).1 hy with hy | ⟨t, rfl, ht⟩
        · exact ih x y hx hy
        · have hxy : x ∣ snoc a t := (dvd_snoc_iff x a t).2 (Or.inl hx)
          exact ⟨snoc a t, fun _ => ⟨And.right, fun h => ⟨hxy.trans h, h⟩⟩⟩
      · rcases (dvd_snoc_iff y a d).1 hy with hy | ⟨t, rfl, ht⟩
        · have hyx : y ∣ snoc a z := (dvd_snoc_iff y a z).2 (Or.inl hy)
          exact ⟨snoc a z, fun _ => ⟨And.left, fun h => ⟨h, hyx.trans h⟩⟩⟩
        · obtain ⟨j, hj⟩ := hD z t d hz ht
          exact ⟨snoc a j, snoc_cone_intersection a z t j hj⟩

end Word
end MergerAlgebra

namespace DiagramForcing.OverlapPrescription
universe u
variable {M : Type u} [LeftCancelMonoid M] {n : ℕ}

/-- Right multiplication respects the pair identifications themselves. No
extra transitive closure is taken. -/
theorem rel_mul (P : OverlapPrescription M n) {z w : Fin n × M}
    (h : P.Rel z w) (m : M) :
    P.Rel (z.1, z.2 * m) (w.1, w.2 * m) := by
  classical
  obtain ⟨i, x⟩ := z
  obtain ⟨j, y⟩ := w
  by_cases hij : i = j
  · subst j
    simp only [rel_same_copy] at h ⊢
    exact congrArg (· * m) h
  · simp only [Rel, hij, ↓reduceIte] at h ⊢
    cases ho : P.start i j with
    | none => simp only [ho] at h
    | some ab =>
        obtain ⟨a, b⟩ := ab
        rw [ho] at h
        obtain ⟨t, rfl, rfl⟩ := h
        exact ⟨t * m, mul_assoc _ _ _, mul_assoc _ _ _⟩

/-- The quotient of the finitely many prescribed copies. Validity, rather
than an equivalence closure, provides its setoid. -/
def copySetoid (P : OverlapPrescription M n) (hP : P.Valid) : Setoid (Fin n × M) :=
  ⟨P.Rel, hP⟩

def Copies (P : OverlapPrescription M n) (hP : P.Valid) := Quotient (P.copySetoid hP)

def copy (P : OverlapPrescription M n) (hP : P.Valid) (i : Fin n) (x : M) : P.Copies hP :=
  Quotient.mk (P.copySetoid hP) (i, x)

@[simp] theorem copy_eq_iff (P : OverlapPrescription M n) (hP : P.Valid)
    (i j : Fin n) (x y : M) :
    P.copy hP i x = P.copy hP j y ↔ P.Rel (i, x) (j, y) := Quotient.eq

theorem copy_injective (P : OverlapPrescription M n) (hP : P.Valid) (i : Fin n) :
    Function.Injective (P.copy hP i) := by
  intro x y he
  exact (P.rel_same_copy i x y).1 ((P.copy_eq_iff hP i i x y).1 he)

def copiesAct (P : OverlapPrescription M n) (hP : P.Valid) (z : P.Copies hP) (m : M) :
    P.Copies hP :=
  Quotient.map (fun z : Fin n × M => (z.1, z.2 * m)) (fun _ _ h => P.rel_mul h m) z

@[simp] theorem copiesAct_copy (P : OverlapPrescription M n) (hP : P.Valid)
    (i : Fin n) (x m : M) :
    P.copiesAct hP (P.copy hP i x) m = P.copy hP i (x * m) := rfl

/-- The injective orbit maps in the prescribed quotient follow from left
cancellation within a single original copy. -/
instance copiesRightFreeAction (P : OverlapPrescription M n) (hP : P.Valid) :
    MergerAlgebra.RightFreeAction M (P.Copies hP) where
  act := P.copiesAct hP
  act_one := by
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
        change P.copy hP z.1 (z.2 * 1) = P.copy hP z.1 z.2
        rw [mul_one]
  act_mul := by
    intro z x y
    induction z using Quotient.inductionOn with
    | h z =>
        change P.copy hP z.1 ((z.2 * x) * y) = P.copy hP z.1 (z.2 * (x * y))
        rw [mul_assoc]
  factor_injective := by
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
        intro x y he
        exact mul_left_cancel (P.copy_injective hP z.1 he)

open MergerAlgebra.RightFreeAction

@[simp] theorem reaches_copy_iff (P : OverlapPrescription M n) (hP : P.Valid)
    (i : Fin n) (x : M) (z : P.Copies hP) :
    Reaches M (P.copy hP i x) z ↔ ∃ m, P.copy hP i (x * m) = z := Iff.rfl

@[simp] theorem reaches_same_copy_iff (P : OverlapPrescription M n) (hP : P.Valid)
    (i : Fin n) (x y : M) :
    Reaches M (P.copy hP i x) (P.copy hP i y) ↔ x ∣ y := by
  rw [reaches_copy_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, (P.copy_injective hP i hm).symm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, rfl⟩

theorem same_copy_cone_intersection (P : OverlapPrescription M n) (hP : P.Valid)
    (i : Fin n) (x y j : M) (hj : ∀ a : M, x ∣ a ∧ y ∣ a ↔ j ∣ a)
    (z : P.Copies hP) :
    Reaches M (P.copy hP i x) z ∧ Reaches M (P.copy hP i y) z ↔
      Reaches M (P.copy hP i j) z := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    change P.copy hP i (x * a) = z at ha
    change P.copy hP i (y * b) = z at hb
    have hxy : x * a = y * b := P.copy_injective hP i (ha.trans hb.symm)
    obtain ⟨c, hc⟩ := (hj (x * a)).1 ⟨dvd_mul_right _ _, b, hxy⟩
    exact ⟨c, by change P.copy hP i (j * c) = z; rw [← hc, ha]⟩
  · intro h
    have hu := (hj j).2 (dvd_refl j)
    exact ⟨reaches_trans ((P.reaches_same_copy_iff hP i x j).2 hu.1) h,
      reaches_trans ((P.reaches_same_copy_iff hP i y j).2 hu.2) h⟩

/-- Intersections from different copies must pass through exactly the
specified overlap: validity ensures that the quotient adds no other equality. -/
theorem overlap_cone_intersection (P : OverlapPrescription M n) (hP : P.Valid)
    {i j : Fin n} (hij : i ≠ j) {a b : M} (hab : P.start i j = some (a, b))
    (x y : M) (z : P.Copies hP) :
    Reaches M (P.copy hP i x) z ∧ Reaches M (P.copy hP j y) z ↔
      ∃ t : M, x ∣ a * t ∧ y ∣ b * t ∧ z = P.copy hP i (a * t) := by
  constructor
  · rintro ⟨⟨m, hm⟩, ⟨k, hk⟩⟩
    change P.copy hP i (x * m) = z at hm
    change P.copy hP j (y * k) = z at hk
    have he := (P.copy_eq_iff hP i j (x * m) (y * k)).1 (hm.trans hk.symm)
    simp only [Rel, hij, ↓reduceIte, hab] at he
    obtain ⟨t, ht, ht'⟩ := he
    exact ⟨t, ⟨m, ht.symm⟩, ⟨k, ht'.symm⟩, hm.symm.trans (congrArg _ ht)⟩
  · rintro ⟨t, ⟨m, hm⟩, ⟨k, hk⟩, rfl⟩
    have he : P.copy hP i (a * t) = P.copy hP j (b * t) := by
      apply (P.copy_eq_iff hP i j _ _).2
      simp only [Rel, hij, ↓reduceIte, hab]
      exact ⟨t, rfl, rfl⟩
    exact ⟨⟨m, congrArg (P.copy hP i) hm.symm⟩,
      ⟨k, (congrArg (P.copy hP j) hk.symm).trans he.symm⟩⟩

/-- Conditional joins in the actual prescribed quotient of copies.
The sequential joins and their right quotients are constructed using only
old conditional joins; failing any one of them means there was no common
upper bound in the first place. -/
theorem copies_hasConeJoins (P : OverlapPrescription M n) (hP : P.Valid)
    (hM : ∀ x y a : M, x ∣ a → y ∣ a → ∃ j : M, ∀ b : M, x ∣ b ∧ y ∣ b ↔ j ∣ b) :
    HasConeJoins M (P.Copies hP) := by
  classical
  intro z w c hz hw
  obtain ⟨⟨i, x⟩, rfl⟩ := Quotient.exists_rep z
  obtain ⟨⟨j, y⟩, rfl⟩ := Quotient.exists_rep w
  change Reaches M (P.copy hP i x) c at hz
  change Reaches M (P.copy hP j y) c at hw
  by_cases hij : i = j
  · subst j
    obtain ⟨u, hu⟩ := (P.reaches_copy_iff hP i x c).1 hz
    obtain ⟨v, hv⟩ := (P.reaches_copy_iff hP i y c).1 hw
    have hxy : x * u = y * v := P.copy_injective hP i (hu.trans hv.symm)
    obtain ⟨k, hk⟩ := hM x y (x * u) (dvd_mul_right _ _) ⟨v, hxy⟩
    exact ⟨P.copy hP i k, P.same_copy_cone_intersection hP i x y k hk⟩
  · obtain ⟨u, hu⟩ := (P.reaches_copy_iff hP i x c).1 hz
    obtain ⟨v, hv⟩ := (P.reaches_copy_iff hP j y c).1 hw
    have he := (P.copy_eq_iff hP i j (x * u) (y * v)).1 (hu.trans hv.symm)
    simp only [Rel, hij, ↓reduceIte] at he
    cases ho : P.start i j with
    | none => simp only [ho] at he
    | some ab =>
        obtain ⟨a, b⟩ := ab
        rw [ho] at he
        obtain ⟨t₀, hxt, hyt⟩ := he
        obtain ⟨r, hr⟩ := DiagramOrder.exists_cone_residual hM x a t₀ ⟨u, hxt.symm⟩
        obtain ⟨s, hs⟩ := DiagramOrder.exists_cone_residual hM y b t₀ ⟨v, hyt.symm⟩
        obtain ⟨k, hk⟩ := hM r s t₀ ((hr t₀).1 ⟨u, hxt.symm⟩)
          ((hs t₀).1 ⟨v, hyt.symm⟩)
        have hcoeff : ∀ t, x ∣ a * t ∧ y ∣ b * t ↔ k ∣ t := fun t => by
          rw [hr t, hs t, hk t]
        refine ⟨P.copy hP i (a * k), fun z => ?_⟩
        change Reaches M (P.copy hP i x) z ∧ Reaches M (P.copy hP j y) z ↔
          Reaches M (P.copy hP i (a * k)) z
        rw [P.overlap_cone_intersection hP hij ho]
        constructor
        · rintro ⟨t, hxt, hyt, rfl⟩
          obtain ⟨m, rfl⟩ := (hcoeff t).1 ⟨hxt, hyt⟩
          exact ⟨m, congrArg (P.copy hP i) (mul_assoc a k m)⟩
        · rintro ⟨m, hm⟩
          change P.copy hP i ((a * k) * m) = z at hm
          have ht := (hcoeff (k * m)).2 (dvd_mul_right _ _)
          exact ⟨k * m, ht.1, ht.2, hm.symm.trans (congrArg _ (mul_assoc a k m))⟩

/-- The extension is constructed, not postulated: its elements are the
normal forms over the actual prescribed quotient. -/
abbrev Merger (P : OverlapPrescription M n) (hP : P.Valid) :=
  MergerAlgebra.Word M (P.Copies hP)

/-- The new roots which merge the original copies. -/
def root (P : OverlapPrescription M n) (hP : P.Valid) (i : Fin n) : P.Merger hP :=
  .snoc (.old 1) (P.copy hP i 1)

@[simp] theorem root_mul_old (P : OverlapPrescription M n) (hP : P.Valid)
    (i : Fin n) (x : M) :
    P.root hP i * .old x = .snoc (.old 1) (P.copy hP i x) := by
  change MergerAlgebra.Word.snoc (.old 1) (P.copy hP i (1 * x)) = _
  rw [one_mul]

/-- Exact realization of the given valid overlap prescription by left
translations. The right-hand side is the original pair relation, not its
transitive closure; no extra overlap is introduced. -/
theorem root_mul_eq_iff (P : OverlapPrescription M n) (hP : P.Valid)
    (z w : Fin n × M) :
    P.root hP z.1 * .old z.2 = P.root hP w.1 * .old w.2 ↔ P.Rel z w := by
  simp only [root_mul_old, MergerAlgebra.Word.snoc.injEq, true_and, copy_eq_iff]

/-- All conditional joins in the constructed finite-copy merger. -/
theorem merger_hasConditionalJoins [DiagramOrder.IsConical M]
    (P : OverlapPrescription M n) (hP : P.Valid)
    (hM : DiagramOrder.HasConditionalJoins (DiagramOrder.LeftDivOrder M)) :
    DiagramOrder.HasConditionalJoins (DiagramOrder.LeftDivOrder (P.Merger hP)) := by
  intro x y a hx hy
  have hc := DiagramOrder.exists_cone_join hM
  obtain ⟨j, hj⟩ := MergerAlgebra.Word.exists_cone_join hc
    (P.copies_hasConeJoins hP hc) x y a
    ((DiagramOrder.LeftDivOrder.le_iff_dvd (M := P.Merger hP) x a).1 hx)
    ((DiagramOrder.LeftDivOrder.le_iff_dvd (M := P.Merger hP) y a).1 hy)
  refine ⟨j, (DiagramOrder.pair_lub_iff (α := DiagramOrder.LeftDivOrder (P.Merger hP)) x y j).2 (fun z => ?_)⟩
  change (∃ q, x * q = z) ∧ (∃ q, y * q = z) ↔ ∃ q, j * q = z
  constructor
  · rintro ⟨⟨q, hq⟩, ⟨r, hr⟩⟩
    obtain ⟨s, hs⟩ := (hj z).1 ⟨⟨q, hq.symm⟩, ⟨r, hr.symm⟩⟩
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, hs⟩
    obtain ⟨⟨q, hq⟩, ⟨r, hr⟩⟩ := (hj z).2 ⟨s, hs.symm⟩
    exact ⟨⟨q, hq.symm⟩, ⟨r, hr.symm⟩⟩

end DiagramForcing.OverlapPrescription
end PartitionConsistency

namespace PartitionConsistency.MergerAlgebra.Word
universe u
variable {M D : Type u}

/-- Finite coding of a normal form; only the existing coefficient and
finitely many quotient letters are needed. -/
def letters : Word M D → List D
  | old _ => []
  | snoc w z => z :: letters w

/-- The normal-form encoding is injective, so no presentation-sized
collection beyond finite strings is required. -/
theorem code_injective : Function.Injective (fun w : Word M D => (leading w, letters w)) := by
  intro w
  induction w with
  | old m =>
      intro v hv
      cases v with
      | old n => exact congrArg old (Prod.mk.inj hv).1
      | snoc v z =>
          have he := (Prod.mk.inj hv).2
          simp [letters] at he
  | snoc w z ih =>
      intro v hv
      cases v with
      | old n =>
          have he := (Prod.mk.inj hv).2
          simp [letters] at he
      | snoc v d =>
          have hzv := List.cons.inj (Prod.mk.inj hv).2
          exact congrArg₂ snoc (ih (Prod.ext (Prod.mk.inj hv).1 hzv.2)) hzv.1

/-- The scheduling bound for the normal forms. -/
theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hM : Cardinal.mk M ≤ μ) (hD : Cardinal.mk D ≤ μ) :
    Cardinal.mk (Word M D) ≤ μ := by
  calc
    Cardinal.mk (Word M D) ≤ Cardinal.mk (M × List D) :=
      Cardinal.mk_le_of_injective code_injective
    _ = Cardinal.mk M * Cardinal.mk (List D) := by simp only [Cardinal.mk_prod, Cardinal.lift_id]
    _ ≤ max (max (Cardinal.mk M) (Cardinal.mk (List D))) Cardinal.aleph0 :=
      Cardinal.mul_le_max _ _
    _ ≤ μ := max_le (max_le hM ((Cardinal.mk_list_le_max D).trans (max_le hω hD))) hω

end PartitionConsistency.MergerAlgebra.Word

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u
variable {M : Type u} [LeftCancelMonoid M] {n : ℕ}

/-- A finite-copy merger preserves the source's infinite cardinal bound. -/
theorem merger_cardinal_le (P : OverlapPrescription M n) (hP : P.Valid)
    {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ) (hM : Cardinal.mk M ≤ μ) :
    Cardinal.mk (P.Merger hP) ≤ μ := by
  apply MergerAlgebra.Word.cardinal_le hω hM
  calc
    Cardinal.mk (P.Copies hP) ≤ Cardinal.mk (Fin n × M) := Cardinal.mk_quotient_le
    _ = n * Cardinal.mk M := by simp [Cardinal.mk_prod]
    _ ≤ max (max (n : Cardinal) (Cardinal.mk M)) Cardinal.aleph0 := Cardinal.mul_le_max _ _
    _ ≤ μ := max_le (max_le ((Cardinal.natCast_lt_aleph0 (n := n)).le.trans hω) hM) hω

end PartitionConsistency.DiagramForcing.OverlapPrescription

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Algebra_MergerCones
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency.DiagramOrder
variable {α : Type*} [PartialOrder α]

/-- A uniformly strict bound on all missed costs. This is an equivalent,
convenient form of the supremum margin for a strict comparison. -/
def UniformMargin (ρ ε : α → ℝ) (x y : α) : Prop :=
  ∃ c : ℝ, c < ρ y - ρ x ∧ ∀ d, d ≤ y → ¬ d ≤ x → ε d ≤ c

namespace UniformMargin
variable {ρ ε : α → ℝ} {x y z : α}

theorem supremum_lt (h : UniformMargin ρ ε x y) (hxy : x < y) :
    sSup (ε '' {d | d ≤ y ∧ ¬d ≤ x}) < ρ y - ρ x := by
  obtain ⟨c, hc, hb⟩ := h
  have he : (ε '' {d | d ≤ y ∧ ¬d ≤ x}).Nonempty :=
    ⟨ε y, y, ⟨le_rfl, not_le_of_gt hxy⟩, rfl⟩
  refine (csSup_le he ?_).trans_lt hc
  rintro _ ⟨d, hd, rfl⟩
  exact hb d hd.1 hd.2

/-- Margins compose across an intervening element. The proof controls the
supremum, not merely each individual cost. -/
theorem trans (hxy : x < y) (hyz : y < z) (hε : ∀ a, 0 < ε a)
    (h₁ : UniformMargin ρ ε x y) (h₂ : UniformMargin ρ ε y z) :
    UniformMargin ρ ε x z := by
  obtain ⟨a, ha, hba⟩ := h₁
  obtain ⟨b, hb, hbb⟩ := h₂
  have hapos : 0 < a := (hε y).trans_le (hba y le_rfl (not_le_of_gt hxy))
  have hbpos : 0 < b := (hε z).trans_le (hbb z le_rfl (not_le_of_gt hyz))
  refine ⟨max a b, max_lt (by linarith) (by linarith), ?_⟩
  intro d hdz hdx
  by_cases hdy : d ≤ y
  · exact (hba d hdy hdx).trans (le_max_left _ _)
  · exact (hbb d hdz hdy).trans (le_max_right _ _)
end UniformMargin

namespace HeightCost
/-- The old margin supplies one uniform upper bound for every missed cost. -/
theorem uniform_margin (H : HeightCost α) {x y : α} (hxy : x < y) :
    UniformMargin H.height H.cost x y := by
  refine ⟨sSup (H.cost '' {d | d ≤ y ∧ ¬d ≤ x}), H.margin hxy, ?_⟩
  intro d hdy hdx
  refine le_csSup (s := H.cost '' {d | d ≤ y ∧ ¬d ≤ x}) ?_ ⟨d, ⟨hdy, hdx⟩, rfl⟩
  refine ⟨1, ?_⟩
  rintro _ ⟨a, _, rfl⟩
  exact H.cost_le_one a
end HeightCost
end PartitionConsistency.DiagramOrder


namespace PartitionConsistency.MergerAlgebra
universe u v

/-- Right divisibility in a free right monoid-set, used for the quotient
letters, not for words in the new monoid. -/
def RightDivOrder (_M : Type u) (D : Type v) := D

namespace RightDivOrder
variable {M : Type u} {D : Type v} [Monoid M] [RightFreeAction M D]
  [DiagramOrder.IsConical M]

instance instRightFreeAction : RightFreeAction M (RightDivOrder M D) := inferInstanceAs (RightFreeAction M D)

instance instPartialOrder : PartialOrder (RightDivOrder M D) where
  le := RightFreeAction.Reaches M
  le_refl := RightFreeAction.reaches_refl
  le_trans _ _ _ := RightFreeAction.reaches_trans
  le_antisymm z w hzw hwz := by
    obtain ⟨m, hm⟩ := hzw
    obtain ⟨n, hn⟩ := hwz
    have he : m * n = 1 := by
      apply RightFreeAction.factor_injective z
      rw [← RightFreeAction.act_mul, hm, hn, RightFreeAction.act_one]
    have hm1 := (DiagramOrder.IsConical.eq_one_of_mul_eq_one he).1
    simpa only [hm1, RightFreeAction.act_one] using hm

end RightDivOrder
end PartitionConsistency.MergerAlgebra

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u
open Classical DiagramOrder MergerAlgebra MergerAlgebra.RightFreeAction
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {n : ℕ}
variable (P : OverlapPrescription M n) (hP : P.Valid)

/-- A coordinate of the quotient letter exists when the letter belongs to
that prescribed copy. Each such representative is unique. -/
def HasRep (i : Fin n) (z : P.Copies hP) : Prop := ∃ x : M, P.copy hP i x = z

noncomputable def coordHeight (H : HeightCost (LeftDivOrder M)) (i : Fin n)
    (z : P.Copies hP) : ℝ :=
  if h : P.HasRep hP i z then H.height h.choose else 0

noncomputable def coordCost (H : HeightCost (LeftDivOrder M)) (i : Fin n)
    (z : P.Copies hP) : ℝ :=
  if h : P.HasRep hP i z then H.cost h.choose else 1

variable (H : HeightCost (LeftDivOrder M))

@[simp] theorem coordHeight_copy (i : Fin n) (x : M) :
    P.coordHeight hP H i (P.copy hP i x) = H.height x := by
  have h : P.HasRep hP i (P.copy hP i x) := ⟨x, rfl⟩
  have hx : h.choose = x := P.copy_injective hP i h.choose_spec
  simp only [coordHeight, dite_eq_left h, hx]

@[simp] theorem coordCost_copy (i : Fin n) (x : M) :
    P.coordCost hP H i (P.copy hP i x) = H.cost x := by
  have h : P.HasRep hP i (P.copy hP i x) := ⟨x, rfl⟩
  have hx : h.choose = x := P.copy_injective hP i h.choose_spec
  simp only [coordCost, dite_eq_left h, hx]

theorem coordHeight_nonneg (i : Fin n) (z : P.Copies hP) :
    0 ≤ P.coordHeight hP H i z := by
  classical
  unfold coordHeight
  split_ifs with h
  · exact (H.height_pos _).le
  · exact le_rfl

theorem coordHeight_lt_one (i : Fin n) (z : P.Copies hP) :
    P.coordHeight hP H i z < 1 := by
  classical
  unfold coordHeight
  split_ifs with h
  · exact H.height_lt_one _
  · exact zero_lt_one

theorem coordCost_pos (i : Fin n) (z : P.Copies hP) :
    0 < P.coordCost hP H i z := by
  classical
  unfold coordCost
  split_ifs with h
  · exact H.cost_pos _
  · exact zero_lt_one

theorem coordCost_le_one (i : Fin n) (z : P.Copies hP) :
    P.coordCost hP H i z ≤ 1 := by
  classical
  unfold coordCost
  split_ifs with h
  · exact H.cost_le_one _
  · exact le_rfl

omit [IsConical M] in
/-- A representation persists when its letter is multiplied on the right. -/
theorem hasRep_of_reaches {i : Fin n} {z w : P.Copies hP}
    (hz : P.HasRep hP i z) (hzw : Reaches M z w) : P.HasRep hP i w := by
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨m, hm⟩ := hzw
  exact ⟨x * m, hm⟩

/-- Every summand of the finite average is nondecreasing. -/
theorem coordHeight_mono (i : Fin n) :
    Monotone (α := RightDivOrder M (P.Copies hP)) (P.coordHeight hP H i) := by
  classical
  intro z w hzw
  by_cases hz : P.HasRep hP i z
  · obtain ⟨x, rfl⟩ := hz
    obtain ⟨m, rfl⟩ := hzw
    change P.coordHeight hP H i (P.copy hP i x) ≤
      P.coordHeight hP H i (P.copy hP i (x * m))
    rw [coordHeight_copy, coordHeight_copy]
    exact H.strictMono_height.monotone ⟨m, rfl⟩
  · have he : P.coordHeight hP H i z = 0 := by simp only [coordHeight, dite_eq_right hz]
    rw [he]
    exact P.coordHeight_nonneg hP H i w

/-- On every represented copy, a proper quotient-letter comparison makes
that coordinate strictly increase. -/
theorem coordHeight_strict {i : Fin n} {z w : RightDivOrder M (P.Copies hP)}
    (hzw : z < w) (hz : P.HasRep hP i z) :
    P.coordHeight hP H i z < P.coordHeight hP H i w := by
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨m, rfl⟩ := hzw.le
  change P.coordHeight hP H i (P.copy hP i x) <
    P.coordHeight hP H i (P.copy hP i (x * m))
  rw [coordHeight_copy, coordHeight_copy]
  apply H.strictMono_height
  refine lt_iff_le_and_ne.2 ⟨⟨m, rfl⟩, ?_⟩
  intro he
  apply hzw.ne
  exact congrArg (P.copy hP i) he

/-- The literal finite average used in the merger height construction. -/
noncomputable def copiesHeight (z : P.Copies hP) : ℝ :=
  (∑ i : Fin n, P.coordHeight hP H i z) / n

/-- A positive choice of costs below all the source's required finite
bounds. The finite product is at most each represented old cost. -/
noncomputable def copiesCost (z : P.Copies hP) : ℝ :=
  min (H.height 1 / 2) (∏ i : Fin n, P.coordCost hP H i z) / n

theorem copiesHeight_pos (hn : 0 < n) (z : P.Copies hP) :
    0 < P.copiesHeight hP H z := by
  apply div_pos _ (Nat.cast_pos.mpr hn)
  apply Finset.sum_pos'
  · intro i _
    exact P.coordHeight_nonneg hP H i z
  · obtain ⟨⟨i, x⟩, rfl⟩ := Quotient.exists_rep z
    refine ⟨i, Finset.mem_univ i, ?_⟩
    change 0 < P.coordHeight hP H i (P.copy hP i x)
    rw [coordHeight_copy]
    exact H.height_pos x

theorem copiesHeight_lt_one (hn : 0 < n) (z : P.Copies hP) :
    P.copiesHeight hP H z < 1 := by
  apply (div_lt_one (Nat.cast_pos.mpr hn)).2
  calc
    (∑ i : Fin n, P.coordHeight hP H i z) < ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_lt_sum
      · intro i _
        exact (P.coordHeight_lt_one hP H i z).le
      · exact ⟨⟨0, hn⟩, Finset.mem_univ _, P.coordHeight_lt_one hP H _ z⟩
    _ = (n : ℝ) := by simp

theorem copiesHeight_strictMono (hn : 0 < n) :
    StrictMono (α := RightDivOrder M (P.Copies hP)) (P.copiesHeight hP H) := by
  intro z w hzw
  apply div_lt_div_of_pos_right _ (Nat.cast_pos.mpr hn)
  apply Finset.sum_lt_sum
  · intro i _
    exact P.coordHeight_mono hP H i hzw.le
  · obtain ⟨⟨i, x⟩, hx⟩ := Quotient.exists_rep z
    exact ⟨i, Finset.mem_univ _, P.coordHeight_strict hP H hzw ⟨x, hx⟩⟩

/-- Every coordinate increase is bounded by the increase of the average,
after division by the number of copies. -/
theorem copiesHeight_gap (_hn : 0 < n) (i : Fin n)
    {z w : RightDivOrder M (P.Copies hP)} (hzw : z ≤ w) :
    (P.coordHeight hP H i w - P.coordHeight hP H i z) / n ≤
      P.copiesHeight hP H w - P.copiesHeight hP H z := by
  have hc : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ P.coordHeight hP H j w - P.coordHeight hP H j z := by
    intro j _
    exact sub_nonneg.mpr (P.coordHeight_mono hP H j hzw)
  have hb := Finset.single_le_sum hc (Finset.mem_univ i)
  have hd := div_le_div_of_nonneg_right hb (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [copiesHeight, Finset.sum_sub_distrib, sub_div] using hd

theorem copiesCost_pos (hn : 0 < n) (z : P.Copies hP) :
    0 < P.copiesCost hP H z := by
  apply div_pos _ (Nat.cast_pos.mpr hn)
  apply lt_min
  · exact div_pos (H.height_pos 1) (by norm_num)
  · exact Finset.prod_pos (fun i _ => P.coordCost_pos hP H i z)

theorem copiesCost_le_cap (hn : 0 < n) (z : P.Copies hP) :
    P.copiesCost hP H z ≤ (H.height 1 / 2) / n :=
  div_le_div_of_nonneg_right (min_le_left _ _) (Nat.cast_pos.mpr hn).le

theorem copiesCost_le_one (hn : 0 < n) (z : P.Copies hP) :
    P.copiesCost hP H z ≤ 1 := by
  apply (P.copiesCost_le_cap hP H hn z).trans
  apply (div_le_one (Nat.cast_pos.mpr hn)).2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hh := H.height_lt_one 1
  linarith

/-- The chosen cost satisfies the bound from every copy representing the
letter, not just from the representative used to construct it. -/
theorem copiesCost_le_copy (hn : 0 < n) (i : Fin n) (x : M) :
    P.copiesCost hP H (P.copy hP i x) ≤ H.cost x / n := by
  have hp : (∏ j : Fin n, P.coordCost hP H j (P.copy hP i x)) ≤
      P.coordCost hP H i (P.copy hP i x) := by
    simpa only [Finset.prod_singleton] using
      (Finset.prod_le_prod_of_subset_of_le_one
        (s := {i}) (t := Finset.univ) (f := fun j => P.coordCost hP H j (P.copy hP i x))
        (Finset.subset_univ _) (fun j _ => (P.coordCost_pos hP H j _).le)
        (fun j _ _ => P.coordCost_le_one hP H j _))
  rw [coordCost_copy] at hp
  exact div_le_div_of_nonneg_right ((min_le_right _ _).trans hp) (Nat.cast_pos.mpr hn).le

/-- Comparisons within a represented copy are precisely old comparisons. -/
theorem copy_le_copy_iff (i : Fin n) (x y : M) :
    @LE.le (RightDivOrder M (P.Copies hP)) _ (P.copy hP i x) (P.copy hP i y) ↔
      @LE.le (LeftDivOrder M) _ x y := by
  change Reaches M (P.copy hP i x) (P.copy hP i y) ↔ ∃ t, x * t = y
  rw [reaches_same_copy_iff]
  exact exists_congr (fun _ => eq_comm)

/-- A strict bound for the missed costs that have a representative in a
specified copy. Crucially it is one bound for that whole class of divisors. -/
theorem copies_coordinate_margin (hn : 0 < n)
    {z w : RightDivOrder M (P.Copies hP)} (hzw : z < w) (i : Fin n) :
    ∃ c : ℝ, c < P.copiesHeight hP H w - P.copiesHeight hP H z ∧
      ∀ d : RightDivOrder M (P.Copies hP), d ≤ w → ¬ d ≤ z →
        P.HasRep hP i d → P.copiesCost hP H d ≤ c := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  by_cases hz : P.HasRep hP i z
  · obtain ⟨x, rfl⟩ := hz
    obtain ⟨m, rfl⟩ := hzw.le
    have hxm : @LT.lt (LeftDivOrder M) _ x (x * m) := by
      refine lt_iff_le_and_ne.2 ⟨⟨m, rfl⟩, ?_⟩
      intro he
      exact hzw.ne (congrArg (P.copy hP i) he)
    obtain ⟨c, hc, hbound⟩ := H.uniform_margin hxm
    have hgap := P.copiesHeight_gap hP H hn i hzw.le
    change (P.coordHeight hP H i (P.copy hP i (x * m)) -
      P.coordHeight hP H i (P.copy hP i x)) / n ≤ _ at hgap
    rw [coordHeight_copy, coordHeight_copy] at hgap
    refine ⟨c / n, (div_lt_div_of_pos_right hc hnR).trans_le hgap, ?_⟩
    intro d hdw hdz hdrep
    obtain ⟨y, rfl⟩ := hdrep
    have hdy := (P.copy_le_copy_iff hP i y (x * m)).1 hdw
    have hdn : ¬ @LE.le (LeftDivOrder M) _ y x :=
      fun h => hdz ((P.copy_le_copy_iff hP i y x).2 h)
    exact (P.copiesCost_le_copy hP H hn i y).trans
      (div_le_div_of_nonneg_right (hbound y hdy hdn) hnR.le)
  · by_cases hw : P.HasRep hP i w
    · obtain ⟨y, hy⟩ := hw
      have hz0 : P.coordHeight hP H i z = 0 := by simp only [coordHeight, dite_eq_right hz]
      have hwy : P.coordHeight hP H i w = H.height y := by
        rw [← hy, coordHeight_copy]
      have hgap := P.copiesHeight_gap hP H hn i hzw.le
      rw [hz0, hwy, sub_zero] at hgap
      have hhy : H.height 1 ≤ H.height y :=
        H.strictMono_height.monotone ⟨y, one_mul y⟩
      have hlt : H.height 1 / 2 < H.height y := by
        have hp := H.height_pos 1
        linarith
      refine ⟨(H.height 1 / 2) / n,
        (div_lt_div_of_pos_right hlt hnR).trans_le hgap, ?_⟩
      intro d _ _ _
      exact P.copiesCost_le_cap hP H hn d
    · refine ⟨0, sub_pos.mpr (P.copiesHeight_strictMono hP H hn hzw), ?_⟩
      intro d hdw _ hdrep
      exact (hw (P.hasRep_of_reaches hP hdrep hdw)).elim

/-- Finiteness of the copies converts their separate strict bounds into a
single strict bound for the complete missed-cost supremum. -/
theorem copies_uniform_margin (hn : 0 < n)
    {z w : RightDivOrder M (P.Copies hP)} (hzw : z < w) :
    UniformMargin (α := RightDivOrder M (P.Copies hP))
      (P.copiesHeight hP H) (P.copiesCost hP H) z w := by
  choose c hc hb using P.copies_coordinate_margin hP H hn hzw
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ c
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  refine ⟨c i, hc i, ?_⟩
  intro d hdw hdz
  obtain ⟨⟨j, x⟩, hx⟩ := Quotient.exists_rep d
  exact (hb j d hdw hdz ⟨x, hx⟩).trans (hmax j (Finset.mem_univ _))

/-- Actual heights and costs on the prescribed quotient, satisfying the
strict supremum margin. -/
noncomputable def copiesHeightCost (hn : 0 < n) :
    HeightCost (RightDivOrder M (P.Copies hP)) where
  height := P.copiesHeight hP H
  cost := P.copiesCost hP H
  height_pos := P.copiesHeight_pos hP H hn
  height_lt_one := P.copiesHeight_lt_one hP H hn
  cost_pos := P.copiesCost_pos hP H hn
  cost_le_one := P.copiesCost_le_one hP H hn
  margin hzw := (P.copies_uniform_margin hP H hn hzw).supremum_lt hzw

end PartitionConsistency.DiagramForcing.OverlapPrescription

namespace PartitionConsistency.MergerAlgebra.Word
universe u v
open DiagramOrder
variable {M : Type u} {D : Type v} [LeftCancelMonoid M] [IsConical M]
  [RightFreeAction M D]
variable (H : HeightCost (LeftDivOrder M)) (HD : HeightCost (RightDivOrder M D))

/-- Word heights with the source's parameters `θ = φ = 1/4`. -/
noncomputable def wordHeight : Word M D → ℝ
  | old x => H.height x
  | snoc w z => wordHeight w + (1 - wordHeight w) * (1 / 4 + HD.height z / 4)

/-- Positive costs satisfying both of the required last-letter bounds. -/
noncomputable def wordCost : Word M D → ℝ
  | old x => H.cost x
  | snoc w z => (1 - wordHeight H HD w) * min (1 / 8) (HD.cost z / 4)

@[simp] theorem wordHeight_old (x : M) : wordHeight H HD (.old x) = H.height x := rfl
@[simp] theorem wordHeight_snoc (w : Word M D) (z : D) :
    wordHeight H HD (snoc w z) =
      wordHeight H HD w + (1 - wordHeight H HD w) * (1 / 4 + HD.height z / 4) := rfl
@[simp] theorem wordCost_old (x : M) : wordCost H HD (.old x) = H.cost x := rfl
@[simp] theorem wordCost_snoc (w : Word M D) (z : D) :
    wordCost H HD (snoc w z) = (1 - wordHeight H HD w) * min (1 / 8) (HD.cost z / 4) := rfl

theorem wordHeight_bounds (w : Word M D) :
    0 < wordHeight H HD w ∧ wordHeight H HD w < 1 := by
  induction w with
  | old x => exact ⟨H.height_pos x, H.height_lt_one x⟩
  | snoc w z ih =>
      have hp : 0 < 1 - wordHeight H HD w := sub_pos.mpr ih.2
      have hz : 0 < 1 / 4 + HD.height z / 4 := by have := HD.height_pos z; linarith
      have hz1 : 1 / 4 + HD.height z / 4 < 1 := by have := HD.height_lt_one z; linarith
      have hpos := mul_pos hp hz
      have hlt := mul_lt_mul_of_pos_left hz1 hp
      simp only [wordHeight_snoc, mul_one] at *
      constructor <;> linarith

theorem wordCost_pos (w : Word M D) : 0 < wordCost H HD w := by
  cases w with
  | old x => exact H.cost_pos x
  | snoc w z =>
      apply mul_pos (sub_pos.mpr (wordHeight_bounds H HD w).2)
      exact lt_min (by norm_num) (div_pos (HD.cost_pos z) (by norm_num))

theorem wordCost_le_one (w : Word M D) : wordCost H HD w ≤ 1 := by
  cases w with
  | old x => exact H.cost_le_one x
  | snoc w z =>
      have hw := wordHeight_bounds H HD w
      have hb := mul_le_mul_of_nonneg_left
        (min_le_left (1 / 8 : ℝ) (HD.cost z / 4)) (by linarith : 0 ≤ 1 - wordHeight H HD w)
      change (1 - wordHeight H HD w) * min (1 / 8) (HD.cost z / 4) ≤ 1
      linarith

/-- Every proper one-letter extension is a strict divisibility comparison. -/
theorem prefix_lt_snoc (w : Word M D) (z : D) :
    @LT.lt (LeftDivOrder (Word M D)) _ w (snoc w z) := by
  refine lt_iff_le_and_ne.2 ⟨⟨snoc (old 1) z, ?_⟩, ?_⟩
  · change product w (snoc (old 1) z) = snoc w z
    simp only [product, act_one]
  · intro he
    have hl := congrArg length he
    simp only [length_snoc] at hl
    omega

/-- The uniform bound for the new divisors appearing at one extra letter. -/
theorem uniform_margin_snoc (w : Word M D) (z : D) :
    UniformMargin (α := LeftDivOrder (Word M D))
      (wordHeight H HD) (wordCost H HD) w (snoc w z) := by
  have hw := wordHeight_bounds H HD w
  have hz := HD.height_pos z
  refine ⟨(1 - wordHeight H HD w) / 8, ?_, ?_⟩
  · rw [wordHeight_snoc]
    nlinarith [mul_pos (by linarith : 0 < 1 - wordHeight H HD w) hz]
  · intro d hdy hdx
    have hdy' : d ∣ snoc w z := by obtain ⟨q, hq⟩ := hdy; exact ⟨q, hq.symm⟩
    rcases (dvd_snoc_iff d w z).1 hdy' with hdw | ⟨t, rfl, _⟩
    · obtain ⟨q, hq⟩ := hdw
      exact (hdx ⟨q, hq.symm⟩).elim
    · rw [wordCost_snoc]
      have hb := mul_le_mul_of_nonneg_left
        (min_le_left (1 / 8 : ℝ) (HD.cost t / 4)) (by linarith : 0 ≤ 1 - wordHeight H HD w)
      linarith

/-- For equal-length words with a common prefix, all shorter divisors are
shared and the only new missed costs are controlled by the last-letter margin. -/
theorem uniform_margin_same_prefix (w : Word M D) {z t : RightDivOrder M D}
    (hzt : z < t) :
    UniformMargin (α := LeftDivOrder (Word M D))
      (wordHeight H HD) (wordCost H HD) (snoc w z) (snoc w t) := by
  have hw := wordHeight_bounds H HD w
  have hp : 0 < 1 - wordHeight H HD w := by linarith
  obtain ⟨c, hc, hb⟩ := HD.uniform_margin hzt
  refine ⟨(1 - wordHeight H HD w) * (c / 4), ?_, ?_⟩
  · have hlt := mul_lt_mul_of_pos_left (div_lt_div_of_pos_right hc (by norm_num : (0 : ℝ) < 4)) hp
    rw [wordHeight_snoc H HD w t, wordHeight_snoc H HD w z]
    nlinarith
  · intro d hdt hdz
    have hdt' : d ∣ snoc w t := by obtain ⟨q, hq⟩ := hdt; exact ⟨q, hq.symm⟩
    rcases (dvd_snoc_iff d w t).1 hdt' with hdw | ⟨a, rfl, hat⟩
    · have hdz' := (dvd_snoc_iff d w z).2 (Or.inl hdw)
      obtain ⟨q, hq⟩ := hdz'
      exact (hdz ⟨q, hq.symm⟩).elim
    · have han : ¬ @LE.le (RightDivOrder M D) _ a z := by
        rintro ⟨m, hm⟩
        exact hdz ⟨old m, congrArg (snoc w) hm⟩
      have hcost := hb a hat han
      rw [wordCost_snoc]
      apply (mul_le_mul_of_nonneg_left (min_le_right _ _) hp.le).trans
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hcost (by norm_num)) hp.le

/-- A comparison between old words has exactly its old missed costs,
because no new word divides an old word. -/
theorem uniform_margin_old {x y : LeftDivOrder M} (hxy : x < y) :
    UniformMargin (α := LeftDivOrder (Word M D))
      (wordHeight H HD) (wordCost H HD) (old x) (old y) := by
  obtain ⟨c, hc, hb⟩ := H.uniform_margin hxy
  refine ⟨c, hc, ?_⟩
  intro d hdy hdx
  obtain ⟨q, hq⟩ := hdy
  obtain ⟨a, b, rfl, rfl, hab⟩ := factors_of_old hq
  have ha : @LE.le (LeftDivOrder M) _ a y := ⟨b, hab⟩
  have hn : ¬ @LE.le (LeftDivOrder M) _ a x := by
    rintro ⟨m, hm⟩
    exact hdx ⟨old m, congrArg old hm⟩
  exact hb a ha hn

/-- Induction through the literal normal forms verifies every strict
comparison, not just the comparisons between the adjoined roots. -/
theorem word_uniform_margin (y : Word M D) :
    ∀ x : Word M D, @LT.lt (LeftDivOrder (Word M D)) _ x y →
      UniformMargin (α := LeftDivOrder (Word M D))
        (wordHeight H HD) (wordCost H HD) x y := by
  induction y with
  | old y =>
      intro x hxy
      obtain ⟨q, hq⟩ := hxy.le
      obtain ⟨a, b, rfl, rfl, hab⟩ := factors_of_old hq
      have ha : @LT.lt (LeftDivOrder M) _ a y := by
        refine lt_iff_le_and_ne.2 ⟨⟨b, hab⟩, ?_⟩
        exact fun he => hxy.ne (congrArg old he)
      exact uniform_margin_old H HD ha
  | snoc w z ih =>
      intro x hxy
      have hxy' : x ∣ snoc w z := by obtain ⟨q, hq⟩ := hxy.le; exact ⟨q, hq.symm⟩
      rcases (dvd_snoc_iff x w z).1 hxy' with hxw | ⟨t, rfl, htz⟩
      · by_cases he : x = w
        · subst x
          exact uniform_margin_snoc H HD w z
        · have hxw' : @LT.lt (LeftDivOrder (Word M D)) _ x w := by
            obtain ⟨q, hq⟩ := hxw
            exact lt_iff_le_and_ne.2 ⟨⟨q, hq.symm⟩, he⟩
          exact UniformMargin.trans hxw' (prefix_lt_snoc w z) (wordCost_pos H HD)
            (ih x hxw') (uniform_margin_snoc H HD w z)
      · have htz' : @LT.lt (RightDivOrder M D) _ t z :=
          lt_iff_le_and_ne.2 ⟨htz, fun he => hxy.ne (congrArg (snoc w) he)⟩
        exact uniform_margin_same_prefix H HD w htz'

/-- Extension of the old height and cost to the actual merger monoid. -/
noncomputable def wordHeightCost : HeightCost (LeftDivOrder (Word M D)) where
  height := wordHeight H HD
  cost := wordCost H HD
  height_pos w := (wordHeight_bounds H HD w).1
  height_lt_one w := (wordHeight_bounds H HD w).2
  cost_pos := wordCost_pos H HD
  cost_le_one := wordCost_le_one H HD
  margin {x y} hxy := (word_uniform_margin H HD y x hxy).supremum_lt hxy

end PartitionConsistency.MergerAlgebra.Word

namespace PartitionConsistency.MergerAlgebra.Word
universe u v
open DiagramOrder
variable {M : Type u} {D : Type v} [LeftCancelMonoid M] [IsConical M]
  [RightFreeAction M D]
  (H : HeightCost (LeftDivOrder M)) (HD : HeightCost (RightDivOrder M D))

/-- The set of costs of divisors missed by an old comparison is literally
unchanged, since every divisor of an old word is itself an old word. -/
theorem old_missed_costs (x y : LeftDivOrder M) :
    (wordHeightCost H HD).cost ''
        {d : LeftDivOrder (Word M D) | d ≤ old y ∧ ¬ d ≤ old x} =
      H.cost '' {d : LeftDivOrder M | d ≤ y ∧ ¬ d ≤ x} := by
  ext r
  constructor
  · rintro ⟨d, ⟨⟨q, hq⟩, hdx⟩, hr⟩
    obtain ⟨a, b, rfl, rfl, hab⟩ := factors_of_old hq
    refine ⟨a, ⟨⟨b, hab⟩, ?_⟩, hr⟩
    rintro ⟨m, hm⟩
    exact hdx ⟨old m, congrArg old hm⟩
  · rintro ⟨a, ⟨⟨b, hab⟩, hax⟩, hr⟩
    refine ⟨old a, ⟨⟨old b, congrArg old hab⟩, ?_⟩, hr⟩
    rintro ⟨q, hq⟩
    obtain ⟨c, d, hac, hqd, hcd⟩ := factors_of_old hq
    have hac' : a = c := old.inj hac
    subst c
    exact hax ⟨d, hcd⟩

/-- In particular, the old missed-cost supremum is exactly preserved. -/
theorem old_cost_supremum (x y : LeftDivOrder M) :
    sSup ((wordHeightCost H HD).cost ''
      {d : LeftDivOrder (Word M D) | d ≤ old y ∧ ¬ d ≤ old x}) =
        sSup (H.cost '' {d : LeftDivOrder M | d ≤ y ∧ ¬ d ≤ x}) :=
  congrArg sSup (old_missed_costs H HD x y)

end PartitionConsistency.MergerAlgebra.Word

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u
open DiagramOrder MergerAlgebra
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {n : ℕ}
  (P : OverlapPrescription M n) (hP : P.Valid)
  (H : HeightCost (LeftDivOrder M))

/-- The height and cost extension for the literal finite nonempty merger,
not an assumed extension and not merely a margin on the adjoined roots. -/
noncomputable def mergerHeightCost (hn : 0 < n) :
    HeightCost (LeftDivOrder (P.Merger hP)) :=
  Word.wordHeightCost H (P.copiesHeightCost hP H hn)

@[simp] theorem merger_height_old (hn : 0 < n) (x : M) :
    (P.mergerHeightCost hP H hn).height (Word.old x) = H.height x := rfl

@[simp] theorem merger_cost_old (hn : 0 < n) (x : M) :
    (P.mergerHeightCost hP H hn).cost (Word.old x) = H.cost x := rfl

/-- Combining the old-divisor calculation with the constructed margins. -/
theorem merger_old_cost_supremum (hn : 0 < n) (x y : LeftDivOrder M) :
    sSup ((P.mergerHeightCost hP H hn).cost ''
      {d : LeftDivOrder (P.Merger hP) | d ≤ Word.old y ∧ ¬ d ≤ Word.old x}) =
        sSup (H.cost '' {d : LeftDivOrder M | d ≤ y ∧ ¬ d ≤ x}) :=
  Word.old_cost_supremum H (P.copiesHeightCost hP H hn) x y

end PartitionConsistency.DiagramForcing.OverlapPrescription

-- The main consistency proof appears after the concrete construction below.
-- In particular, no inaccessible, transitive-ground, interpretation or forcing
-- assumption has been smuggled into its signature. The open target is stated
-- in Challenge.lean only.

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Algebra_ProbeWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Probe extension: direct-limit letters and cancellative normal forms -/

namespace PartitionConsistency.ProbeAlgebra
universe u
open DiagramOrder

/-- The actual nondecreasing sequence occurring in a probe datum. The
transition and terminal factors will be derived, not additionally chosen. -/
structure Path (M : Type u) [LeftCancelMonoid M] (a : M) where
  node : ℕ → M
  zero : node 0 = 1
  increasing : ∀ {i j}, i ≤ j → node i ∣ node j
  bounded : ∀ i, node i ∣ a

namespace Path
variable {M : Type u} [LeftCancelMonoid M] {a : M} (P : Path M a)

/-- The unique right factor between two nodes of the path. -/
noncomputable def factor (i j : ℕ) (h : i ≤ j) : M := (P.increasing h).choose

@[simp] theorem node_factor (i j : ℕ) (h : i ≤ j) :
    P.node i * P.factor i j h = P.node j := (P.increasing h).choose_spec.symm

@[simp] theorem factor_self (i : ℕ) : P.factor i i le_rfl = 1 := by
  apply mul_left_cancel (a := P.node i)
  rw [node_factor, mul_one]

@[simp] theorem factor_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    P.factor i j hij * P.factor j k hjk = P.factor i k (hij.trans hjk) := by
  apply mul_left_cancel (a := P.node i)
  rw [← mul_assoc, node_factor, node_factor, node_factor]

@[simp] theorem factor_zero (i : ℕ) : P.factor 0 i (Nat.zero_le i) = P.node i := by
  have h := P.node_factor 0 i (Nat.zero_le i)
  simpa only [P.zero, one_mul] using h

/-- The unique terminal factor from a node to `a`. -/
noncomputable def terminal (i : ℕ) : M := (P.bounded i).choose

@[simp] theorem node_terminal (i : ℕ) : P.node i * P.terminal i = a :=
  (P.bounded i).choose_spec.symm

@[simp] theorem factor_terminal {i j : ℕ} (hij : i ≤ j) :
    P.factor i j hij * P.terminal j = P.terminal i := by
  apply mul_left_cancel (a := P.node i)
  rw [← mul_assoc, node_factor, node_terminal, node_terminal]

@[simp] theorem terminal_zero : P.terminal 0 = a := by
  simpa only [P.zero, one_mul] using P.node_terminal 0

/-- Right multiplication by a transition factor. This map is deliberately
not assumed injective: the construction has only left cancellation. -/
noncomputable def transition (i j : ℕ) (h : i ≤ j) : M →[M] M where
  toFun x := x * P.factor i j h
  map_smul' _ _ := mul_assoc _ _ _

@[simp] theorem transition_apply (i j : ℕ) (h : i ≤ j) (x : M) :
    P.transition i j h x = x * P.factor i j h := rfl

instance instDirectedSystemNatCoeMulActionHomIdTransition : DirectedSystem (fun _ : ℕ => M) (P.transition · · ·) where
  map_self := by intro i x; simp only [transition_apply, factor_self, mul_one]
  map_map := by intro k j i hij hjk x; simp only [transition_apply, mul_assoc, factor_trans]

/-- The direct-limit letters `[x,i]` of the probe normal forms. -/
abbrev Letters := DirectLimit (fun _ : ℕ => M) P.transition

/-- The letter at a specified finite stage. Distinct stage elements need
not have distinct images. -/
noncomputable def letter (i : ℕ) (x : M) : P.Letters := Quotient.mk _ ⟨i, x⟩

/-- Equality in the direct limit is equality at some common finite stage. -/
theorem letter_eq_iff (i j : ℕ) (x y : M) :
    P.letter i x = P.letter j y ↔
      ∃ k, ∃ hi : i ≤ k, ∃ hj : j ≤ k,
        x * P.factor i k hi = y * P.factor j k hj := Quotient.eq

@[simp] theorem letter_transition {i j : ℕ} (hij : i ≤ j) (x : M) :
    P.letter j (x * P.factor i j hij) = P.letter i x :=
  DirectLimit.mk_apply (F := fun _ : ℕ => M) (f := P.transition) i j x hij

/-- Left multiplication commutes with the right transition maps. -/
noncomputable def act (x : M) : P.Letters → P.Letters :=
  DirectLimit.map P.transition P.transition (fun _ y => x * y)
    (fun _ _ _ _ => by simp only [transition_apply, mul_assoc])

@[simp] theorem act_letter (x : M) (i : ℕ) (y : M) :
    P.act x (P.letter i y) = P.letter i (x * y) := rfl

@[simp] theorem act_one (s : P.Letters) : P.act 1 s = s := by
  induction s using DirectLimit.induction with
  | ih i x =>
    change P.act 1 (P.letter i x) = P.letter i x
    simp only [act_letter, one_mul]

@[simp] theorem act_mul (x y : M) (s : P.Letters) :
    P.act (x * y) s = P.act x (P.act y s) := by
  induction s using DirectLimit.induction with
  | ih i z =>
    change P.act (x * y) (P.letter i z) = P.act x (P.act y (P.letter i z))
    simp only [act_letter, mul_assoc]

/-- Cancellation occurs at a common finite stage. No cancellation on the
right, nor injectivity of transition maps, is used here. -/
theorem act_injective (x : M) : Function.Injective (P.act x) := by
  intro s t
  induction s using DirectLimit.induction with
  | ih i y =>
    induction t using DirectLimit.induction with
    | ih j z =>
      intro he
      obtain ⟨k, hi, hj, hk⟩ := (P.letter_eq_iff i j (x * y) (x * z)).1 he
      apply (P.letter_eq_iff i j y z).2
      exact ⟨k, hi, hj, mul_left_cancel (by simpa only [mul_assoc] using hk)⟩

/-- The map `k([x,i]) = x c_i`; compatibility uses the terminal-factor
identity, not an incorrectly presumed injective transition map. -/
noncomputable def target : P.Letters → M :=
  DirectLimit.lift P.transition (fun i x => x * P.terminal i)
    (fun i j hij x => by simp only [transition_apply, mul_assoc, factor_terminal])

@[simp] theorem target_letter (i : ℕ) (x : M) :
    P.target (P.letter i x) = x * P.terminal i := rfl

@[simp] theorem target_act (x : M) (s : P.Letters) :
    P.target (P.act x s) = x * P.target s := by
  induction s using DirectLimit.induction with
  | ih i y =>
    change P.target (P.act x (P.letter i y)) = x * P.target (P.letter i y)
    simp only [act_letter, target_letter, mul_assoc]

/-- The old element `h(s) = k(s)e` at which a letter can be consumed. -/
noncomputable def exit (e : M) (s : P.Letters) : M := P.target s * e

@[simp] theorem exit_act (e x : M) (s : P.Letters) :
    P.exit e (P.act x s) = x * P.exit e s := by
  simp only [exit, target_act, mul_assoc]

/-- Membership in an old left-translation cone of letters. -/
def InCone (x : M) (s : P.Letters) : Prop := ∃ t : P.Letters, P.act x t = s

/-- Cone membership can also be tested at a finite stage, retaining the
actual quotient rather than just the existence of an old comparison. -/
theorem inCone_letter_iff (x : M) (i : ℕ) (y : M) :
    P.InCone x (P.letter i y) ↔
      ∃ j, ∃ hij : i ≤ j, x ∣ y * P.factor i j hij := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨j, z, rfl⟩ := DirectLimit.exists_eq_mk P.transition t
    obtain ⟨k, hj, hi, hk⟩ := (P.letter_eq_iff j i (x * z) y).1 ht
    exact ⟨k, hi, ⟨z * P.factor j k hj, by simpa only [mul_assoc] using hk.symm⟩⟩
  · rintro ⟨j, hij, z, hz⟩
    refine ⟨P.letter j z, ?_⟩
    rw [act_letter, ← hz, letter_transition]

/-- Every old divisor of a letter divides its target. -/
theorem dvd_target_of_inCone {x : M} {s : P.Letters} (h : P.InCone x s) : x ∣ P.target s := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨P.target t, P.target_act x t⟩

theorem one_inCone (s : P.Letters) : P.InCone 1 s := ⟨s, P.act_one s⟩

theorem inCone_of_dvd {x y : M} {s : P.Letters} (hxy : x ∣ y) (hys : P.InCone y s) :
    P.InCone x s := by
  obtain ⟨z, rfl⟩ := hxy
  obtain ⟨t, ht⟩ := hys
  exact ⟨P.act z t, (P.act_mul x z t).symm.trans ht⟩

/-- Old cone intersections lift exactly to the direct limit, including
empty intersections. -/
theorem inCone_intersection (x y j : M)
    (hj : ∀ z : M, x ∣ z ∧ y ∣ z ↔ j ∣ z) (s : P.Letters) :
    P.InCone x s ∧ P.InCone y s ↔ P.InCone j s := by
  constructor
  · rintro ⟨⟨t, ht⟩, ⟨v, hv⟩⟩
    obtain ⟨i, u, rfl⟩ := DirectLimit.exists_eq_mk P.transition t
    obtain ⟨l, w, rfl⟩ := DirectLimit.exists_eq_mk P.transition v
    have he : P.letter i (x * u) = P.letter l (y * w) := ht.trans hv.symm
    obtain ⟨k, hi, hl, hk⟩ := (P.letter_eq_iff i l (x * u) (y * w)).1 he
    have hc : j ∣ (x * u) * P.factor i k hi := by
      apply (hj _).1
      exact ⟨⟨u * P.factor i k hi, mul_assoc _ _ _⟩,
        ⟨w * P.factor l k hl, hk.trans (mul_assoc _ _ _)⟩⟩
    obtain ⟨r, hr⟩ := hc
    refine ⟨P.letter k r, ?_⟩
    rw [act_letter, ← hr, letter_transition]
    exact ht
  · intro hs
    have hs' := (hj j).2 (dvd_refl j)
    exact ⟨P.inCone_of_dvd hs'.1 hs, P.inCone_of_dvd hs'.2 hs⟩

/-- If two old cones meet in the letters, the old monoid already contains
a common right multiple. Thus a new letter creates no old nonjoin. -/
theorem old_common_multiple_of_cones {x y : M} {s : P.Letters}
    (hx : P.InCone x s) (hy : P.InCone y s) : ∃ z : M, x ∣ z ∧ y ∣ z :=
  ⟨P.target s, P.dvd_target_of_inCone hx, P.dvd_target_of_inCone hy⟩

/-- The initial new letter has exactly the old-divisor profile given by
the lower closure of the original countable path. -/
theorem initial_profile (x : M) : P.InCone x (P.letter 0 1) ↔ ∃ i : ℕ, x ∣ P.node i := by
  rw [inCone_letter_iff]
  simp only [factor_zero, one_mul, exists_prop, Nat.zero_le, true_and]

/-- The important separation between a head and its exit cone. It uses
conicality and left cancellation, but does not use right cancellation. -/
theorem head_separation [IsConical M] {e : M} (he : e ≠ 1) (s : P.Letters) :
    ¬ P.InCone (P.exit e s) s := by
  intro h
  obtain ⟨z, hz⟩ := P.dvd_target_of_inCone h
  have heq : e * z = 1 := by
    apply mul_left_cancel (a := P.target s)
    simpa only [exit, mul_assoc, mul_one] using hz.symm
  exact he (IsConical.eq_one_of_mul_eq_one heq).1

/-- Countably many old copies suffice for the direct-limit alphabet. -/
theorem letters_cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hM : Cardinal.mk M ≤ μ) : Cardinal.mk P.Letters ≤ μ := by
  calc
    Cardinal.mk P.Letters ≤ Cardinal.mk (Σ _ : ℕ, M) := Cardinal.mk_quotient_le
    _ = Cardinal.aleph0 * Cardinal.mk M := by simp [Cardinal.mk_sigma, Cardinal.sum_const]
    _ ≤ max (max Cardinal.aleph0 (Cardinal.mk M)) Cardinal.aleph0 := Cardinal.mul_le_max _ _
    _ ≤ μ := max_le (max_le hω hM) hω

end Path
end PartitionConsistency.ProbeAlgebra

namespace PartitionConsistency.ProbeAlgebra
universe u v
open DiagramOrder

/-- The letter action and exit map used in the terminating probe normal
forms. These laws will be realized by the path direct limit above. -/
structure Alphabet (M : Type u) (S : Type v) [Monoid M] where
  act : M → S → S
  one_act : ∀ s, act 1 s = s
  mul_act : ∀ x y s, act (x * y) s = act x (act y s)
  act_injective : ∀ x, Function.Injective (act x)
  exit : S → M
  exit_act : ∀ x s, exit (act x s) = x * exit s
  separated : ∀ s, ¬ ∃ t, act (exit s) t = s

namespace Path
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}

/-- The direct limit supplies all the alphabet laws for the probe extension. -/
noncomputable def alphabet (P : Path M a) (he : e ≠ 1) : Alphabet M P.Letters where
  act := P.act
  one_act := P.act_one
  mul_act := P.act_mul
  act_injective := P.act_injective
  exit := P.exit e
  exit_act := P.exit_act e
  separated := P.head_separation he
end Path

/-- Unreduced strings, including a compulsory terminal old factor. -/
inductive Raw (M : Type u) (S : Type v) : Type (max u v)
  | old : M → Raw M S
  | cons : S → Raw M S → Raw M S

namespace Raw
variable {M : Type u} {S : Type v} [Monoid M] (A : Alphabet M S)

def headDiv (x : M) : Raw M S → Prop
  | .old y => x ∣ y
  | .cons s _ => ∃ t, A.act x t = s

def reduced (b : M) : Raw M S → Prop
  | .old _ => True
  | .cons _ w => w.reduced b ∧ ¬ w.headDiv A b

def oldAct (x : M) : Raw M S → Raw M S
  | .old y => .old (x * y)
  | .cons s w => .cons (A.act x s) w

@[simp] theorem oldAct_one (w : Raw M S) : oldAct A 1 w = w := by
  cases w with
  | old y => simp only [oldAct, one_mul]
  | cons s w => simp only [oldAct, A.one_act]

@[simp] theorem oldAct_mul (x y : M) (w : Raw M S) :
    oldAct A (x * y) w = oldAct A x (oldAct A y w) := by
  cases w with
  | old z => simp only [oldAct, mul_assoc]
  | cons s w => simp only [oldAct, A.mul_act]

@[simp] theorem reduced_oldAct (b x : M) (w : Raw M S) :
    (oldAct A x w).reduced A b ↔ w.reduced A b := by cases w <;> rfl

theorem headDiv_iff (x : M) (w : Raw M S) :
    w.headDiv A x ↔ ∃ v : Raw M S, oldAct A x v = w := by
  cases w with
  | old y =>
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨.old z, congrArg Raw.old hz.symm⟩
    · rintro ⟨v, hv⟩
      cases v with
      | old z => exact ⟨z, (Raw.old.inj hv).symm⟩
      | cons s v => cases hv
  | cons s w =>
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨.cons t w, congrArg (Raw.cons · w) ht⟩
    · rintro ⟨v, hv⟩
      cases v with
      | old z => cases hv
      | cons t v => exact ⟨t, (Raw.cons.inj hv).1⟩

theorem oldAct_injective [IsLeftCancelMul M] (x : M) :
    Function.Injective (oldAct A x) := by
  intro w v he
  cases w <;> cases v
  · exact congrArg Raw.old (mul_left_cancel (Raw.old.inj he))
  · cases he
  · cases he
  · obtain ⟨hs, hw⟩ := Raw.cons.inj he
    exact congrArg₂ Raw.cons (A.act_injective x hs) hw
end Raw

/-- Literal irreducibles for the reductions `s(bZ) ↦ h(s)Z`. -/
abbrev Word {M : Type u} {S : Type v} [Monoid M] (A : Alphabet M S) (b : M) :=
  {w : Raw M S // w.reduced A b}

namespace Word
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] (A : Alphabet M S) (b : M)

def old (x : M) : Word A b := ⟨.old x, trivial⟩

def headDiv (x : M) (w : Word A b) : Prop := w.val.headDiv A x

def cons (s : S) (w : Word A b) (hw : ¬ headDiv A b b w) : Word A b :=
  ⟨.cons s w.val, w.property, hw⟩

def oldAct (x : M) (w : Word A b) : Word A b :=
  ⟨w.val.oldAct A x, (Raw.reduced_oldAct A b x w.val).2 w.property⟩

@[simp] theorem oldAct_old (x y : M) : oldAct A b x (old A b y) = old A b (x * y) := rfl

@[simp] theorem oldAct_one (w : Word A b) : oldAct A b 1 w = w :=
  Subtype.ext (Raw.oldAct_one A w.val)

@[simp] theorem oldAct_mul (x y : M) (w : Word A b) :
    oldAct A b (x * y) w = oldAct A b x (oldAct A b y w) :=
  Subtype.ext (Raw.oldAct_mul A x y w.val)

@[simp] theorem oldAct_cons (x : M) (s : S) (w : Word A b) (hw) :
    oldAct A b x (cons A b s w hw) = cons A b (A.act x s) w hw := rfl

@[simp] theorem old_inj (x y : M) : old A b x = old A b y ↔ x = y := by
  constructor
  · exact fun h => Raw.old.inj (congrArg Subtype.val h)
  · exact congrArg (old A b)

@[simp] theorem cons_inj (s t : S) (w v : Word A b) (hw hv) :
    cons A b s w hw = cons A b t v hv ↔ s = t ∧ w = v := by
  constructor
  · intro h
    obtain ⟨hs, hv⟩ := Raw.cons.inj (congrArg Subtype.val h)
    exact ⟨hs, Subtype.ext hv⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem oldAct_injective (x : M) : Function.Injective (oldAct A b x) :=
  fun _ _ h => Subtype.ext (Raw.oldAct_injective A x (congrArg Subtype.val h))

theorem headDiv_iff (x : M) (w : Word A b) :
    headDiv A b x w ↔ ∃ v : Word A b, oldAct A b x v = w := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := (Raw.headDiv_iff A x w.val).1 h
    have hred : v.reduced A b := (Raw.reduced_oldAct A b x v).1 (hv ▸ w.property)
    exact ⟨⟨v, hred⟩, Subtype.ext hv⟩
  · rintro ⟨v, hv⟩
    exact (Raw.headDiv_iff A x w.val).2 ⟨v.val, congrArg Subtype.val hv⟩

@[simp] theorem headDiv_oldAct (x : M) (w : Word A b) :
    headDiv A b x (oldAct A b x w) := (headDiv_iff A b x _).2 ⟨w, rfl⟩

noncomputable def quotient (x : M) (w : Word A b) (h : headDiv A b x w) : Word A b :=
  ((headDiv_iff A b x w).1 h).choose

@[simp] theorem oldAct_quotient (x : M) (w : Word A b) (h : headDiv A b x w) :
    oldAct A b x (quotient A b x w h) = w := ((headDiv_iff A b x w).1 h).choose_spec

@[simp] theorem quotient_oldAct (x : M) (w : Word A b) (h) :
    quotient A b x (oldAct A b x w) h = w := by
  apply oldAct_injective A b x
  exact oldAct_quotient A b x _ h

/-- Prepending a letter performs its only possible front reduction. -/
noncomputable def letterAct (s : S) (w : Word A b) : Word A b := by
  classical
  exact if h : headDiv A b b w then oldAct A b (A.exit s) (quotient A b b w h)
    else cons A b s w h

theorem letterAct_of_headDiv (s : S) (w : Word A b) (h : headDiv A b b w) :
    letterAct A b s w = oldAct A b (A.exit s) (quotient A b b w h) := dite_eq_left h

theorem letterAct_of_not_headDiv (s : S) (w : Word A b) (h : ¬ headDiv A b b w) :
    letterAct A b s w = cons A b s w h := dite_eq_right h

@[simp] theorem letterAct_oldAct_b (s : S) (w : Word A b) :
    letterAct A b s (oldAct A b b w) = oldAct A b (A.exit s) w := by
  rw [letterAct_of_headDiv A b s _ (headDiv_oldAct A b b w), quotient_oldAct]

theorem oldAct_letterAct (x : M) (s : S) (w : Word A b) :
    oldAct A b x (letterAct A b s w) = letterAct A b (A.act x s) w := by
  classical
  by_cases h : headDiv A b b w
  · simp only [letterAct_of_headDiv A b _ _ h, A.exit_act, oldAct_mul]
  · simp only [letterAct_of_not_headDiv A b _ _ h, oldAct_cons]

theorem not_headDiv_exit_cons (s : S) (w : Word A b) (hw) :
    ¬ headDiv A b (A.exit s) (cons A b s w hw) := A.separated s

/-- The two branches of prepending have disjoint ranges by head separation. -/
theorem oldAct_exit_ne_cons (s : S) (v w : Word A b) (hw) :
    oldAct A b (A.exit s) v ≠ cons A b s w hw := by
  intro h
  exact not_headDiv_exit_cons A b s w hw (h ▸ headDiv_oldAct A b (A.exit s) v)

theorem letterAct_injective (s : S) : Function.Injective (letterAct A b s) := by
  classical
  intro w v he
  by_cases hw : headDiv A b b w <;> by_cases hv : headDiv A b b v
  · rw [letterAct_of_headDiv A b s w hw, letterAct_of_headDiv A b s v hv] at he
    have hq := oldAct_injective A b (A.exit s) he
    exact (oldAct_quotient A b b w hw).symm.trans
      ((congrArg (oldAct A b b) hq).trans (oldAct_quotient A b b v hv))
  · rw [letterAct_of_headDiv A b s w hw, letterAct_of_not_headDiv A b s v hv] at he
    exact (oldAct_exit_ne_cons A b s _ v hv he).elim
  · rw [letterAct_of_not_headDiv A b s w hw, letterAct_of_headDiv A b s v hv] at he
    exact (oldAct_exit_ne_cons A b s _ w hw he.symm).elim
  · rw [letterAct_of_not_headDiv A b s w hw, letterAct_of_not_headDiv A b s v hv] at he
    exact ((cons_inj A b _ _ _ _ _ _).1 he).2

end Word
end PartitionConsistency.ProbeAlgebra

namespace PartitionConsistency.ProbeAlgebra
universe u v
open DiagramOrder
namespace Raw
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] (A : Alphabet M S) (b : M)

/-- Evaluate a word by its successive left multipliers. -/
noncomputable def eval : Raw M S → Word A b → Word A b
  | .old x, w => Word.oldAct A b x w
  | .cons s v, w => Word.letterAct A b s (eval v w)

theorem eval_oldAct (x : M) (v : Raw M S) (w : Word A b) :
    eval A b (Raw.oldAct A x v) w = Word.oldAct A b x (eval A b v w) := by
  cases v with
  | old y => exact Word.oldAct_mul A b x y w
  | cons s v => exact (Word.oldAct_letterAct A b x s (eval A b v w)).symm

theorem eval_injective (v : Raw M S) : Function.Injective (eval A b v) := by
  induction v with
  | old x => exact Word.oldAct_injective A b x
  | cons s v ih => exact (Word.letterAct_injective A b s).comp ih
end Raw

namespace Word
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] (A : Alphabet M S) (b : M)

theorem eval_oldAct (x : M) (v w : Word A b) :
    (oldAct A b x v).val.eval A b w = oldAct A b x (v.val.eval A b w) :=
  Raw.eval_oldAct A b x v.val w

theorem eval_letterAct (s : S) (v w : Word A b) :
    (letterAct A b s v).val.eval A b w = letterAct A b s (v.val.eval A b w) := by
  classical
  by_cases h : headDiv A b b v
  · rw [letterAct_of_headDiv A b s v h, eval_oldAct]
    conv_rhs => rw [← oldAct_quotient A b b v h]
    rw [eval_oldAct, letterAct_oldAct_b]
  · rw [letterAct_of_not_headDiv A b s v h]
    rfl

noncomputable def mul (v w : Word A b) : Word A b := v.val.eval A b w

@[simp] theorem old_mul (x : M) (w : Word A b) :
    mul A b (old A b x) w = oldAct A b x w := rfl

@[simp] theorem cons_mul (s : S) (v : Word A b) (hv) (w : Word A b) :
    mul A b (cons A b s v hv) w = letterAct A b s (mul A b v w) := rfl

theorem mul_assoc (x y z : Word A b) : mul A b (mul A b x y) z = mul A b x (mul A b y z) := by
  obtain ⟨x, hx⟩ := x
  induction x with
  | old x => exact eval_oldAct A b x y z
  | cons s v ih =>
    change (letterAct A b s (v.eval A b y)).val.eval A b z =
      letterAct A b s (v.eval A b (y.val.eval A b z))
    rw [eval_letterAct]
    exact congrArg (letterAct A b s) (ih hx.1)

theorem mul_one (w : Word A b) : mul A b w (old A b 1) = w := by
  obtain ⟨w, hw⟩ := w
  induction w with
  | old x =>
    apply Subtype.ext
    exact congrArg Raw.old (_root_.mul_one x)
  | cons s v ih =>
    change letterAct A b s (v.eval A b (old A b 1)) = _
    rw [show v.eval A b (old A b 1) = (⟨v, hw.1⟩ : Word A b) from ih hw.1]
    exact letterAct_of_not_headDiv A b s (⟨v, hw.1⟩ : Word A b) hw.2

noncomputable instance instMonoid : Monoid (Word A b) where
  mul := mul A b
  one := old A b 1
  mul_assoc := mul_assoc A b
  one_mul := oldAct_one A b
  mul_one := mul_one A b

noncomputable instance instLeftCancelMonoid : LeftCancelMonoid (Word A b) where
  mul_left_cancel x _ _ he := Raw.eval_injective A b x.val he

/-- A literal conservative homomorphism of old elements into probe normal forms. -/
noncomputable def oldHom : M →* Word A b where
  toFun := old A b
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem oldHom_apply (x : M) : oldHom A b x = old A b x := rfl

theorem oldHom_injective : Function.Injective (oldHom A b) :=
  fun _ _ h => (old_inj A b _ _).1 h

theorem old_mul_eq_old_iff (x y : M) (w : Word A b) :
    old A b x * w = old A b y ↔ ∃ z : M, w = old A b z ∧ x * z = y := by
  obtain ⟨w, hw⟩ := w
  cases w with
  | old z =>
    change old A b (x * z) = old A b y ↔ ∃ t, old A b z = old A b t ∧ x * t = y
    simp only [old_inj]
    exact ⟨fun h => ⟨z, rfl, h⟩, fun ⟨t, ht, h⟩ => ht ▸ h⟩
  | cons s v =>
    constructor
    · intro h
      have he := congrArg Subtype.val h
      cases he
    · rintro ⟨z, hz, _⟩
      have he := congrArg Subtype.val hz
      cases he

@[simp] theorem old_dvd_old_iff (x y : M) : old A b x ∣ old A b y ↔ x ∣ y := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨z, _, hz⟩ := (old_mul_eq_old_iff A b x y w).1 hw.symm
    exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨old A b z, congrArg (old A b) hz⟩

@[simp] theorem old_dvd_iff_headDiv (x : M) (w : Word A b) :
    old A b x ∣ w ↔ headDiv A b x w := by
  rw [headDiv_iff]
  exact exists_congr (fun _ => eq_comm)

/-- Having no old nontrivial unit prevents a letter from being consumed into `1`. -/
theorem exit_ne_one (s : S) : A.exit s ≠ 1 := by
  intro hs
  exact A.separated s ⟨s, hs ▸ A.one_act s⟩

theorem oldAct_exit_ne_one [IsConical M] (s : S) (w : Word A b) :
    oldAct A b (A.exit s) w ≠ 1 := by
  intro h
  obtain ⟨z, _, hz⟩ := (old_mul_eq_old_iff A b (A.exit s) 1 w).1 h
  exact exit_ne_one A s (IsConical.eq_one_of_mul_eq_one hz).1

theorem letterAct_ne_one [IsConical M] (s : S) (w : Word A b) :
    letterAct A b s w ≠ 1 := by
  classical
  by_cases h : headDiv A b b w
  · rw [letterAct_of_headDiv A b s w h]
    exact oldAct_exit_ne_one A b s _
  · rw [letterAct_of_not_headDiv A b s w h]
    intro he
    have hv := congrArg Subtype.val he
    cases hv

noncomputable instance instIsConical [IsConical M] : IsConical (Word A b) where
  eq_one_of_mul_eq_one := by
    intro x y he
    obtain ⟨x, hx⟩ := x
    cases x with
    | old x =>
      obtain ⟨z, rfl, hz⟩ := (old_mul_eq_old_iff A b x 1 y).1 he
      obtain ⟨rfl, rfl⟩ := IsConical.eq_one_of_mul_eq_one hz
      exact ⟨rfl, rfl⟩
    | cons s v => exact (letterAct_ne_one A b s (v.eval A b y) he).elim

/-- The new generator represented by a letter, with terminal identity. -/
def generator [IsConical M] (hb : b ≠ 1) (s : S) : Word A b :=
  cons A b s (old A b 1) (by
    rintro ⟨z, hz⟩
    exact hb (IsConical.eq_one_of_mul_eq_one hz.symm).1)

theorem generator_mul [IsConical M] (hb : b ≠ 1) (s : S) (w : Word A b) :
    generator A b hb s * w = letterAct A b s w := by
  change letterAct A b s (oldAct A b 1 w) = _
  rw [oldAct_one]

theorem generator_mul_b [IsConical M] (hb : b ≠ 1) (s : S) :
    generator A b hb s * old A b b = old A b (A.exit s) := by
  rw [generator_mul]
  have h : old A b b = oldAct A b b (old A b 1) := by simp
  rw [h, letterAct_oldAct_b, oldAct_old, _root_.mul_one]

end Word
end PartitionConsistency.ProbeAlgebra

namespace PartitionConsistency.ProbeAlgebra
universe u v w
open DiagramOrder
namespace Word
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] (A : Alphabet M S) (b : M)
  {N : Type w} [Monoid N] (f : M →* N) (q : S → N)

/-- Evaluation in any monoid satisfying the letter equivariance and exit
relations. This will give the presentation's universal property. -/
def evalHom : Raw M S → N
  | .old x => f x
  | .cons s v => q s * evalHom v

variable (heq : ∀ x s, q (A.act x s) = f x * q s)
  (hexit : ∀ s, q s * f b = f (A.exit s))

include heq in
theorem evalHom_oldAct (x : M) (v : Raw M S) :
    evalHom f q (v.oldAct A x) = f x * evalHom f q v := by
  cases v with
  | old y => exact f.map_mul x y
  | cons s v => simp only [Raw.oldAct, evalHom, heq, _root_.mul_assoc]

include heq hexit in
theorem evalHom_letterAct (s : S) (v : Word A b) :
    evalHom f q (letterAct A b s v).val = q s * evalHom f q v.val := by
  classical
  by_cases h : headDiv A b b v
  · rw [letterAct_of_headDiv A b s v h]
    change evalHom f q ((quotient A b b v h).val.oldAct A (A.exit s)) = _
    rw [evalHom_oldAct A f q heq]
    conv_rhs => rw [← oldAct_quotient A b b v h]
    change _ = q s * evalHom f q ((quotient A b b v h).val.oldAct A b)
    rw [evalHom_oldAct A f q heq, ← _root_.mul_assoc, hexit]
  · rw [letterAct_of_not_headDiv A b s v h]
    rfl

include heq hexit in
theorem evalHom_mul (v z : Word A b) :
    evalHom f q (v * z).val = evalHom f q v.val * evalHom f q z.val := by
  obtain ⟨v, hv⟩ := v
  induction v with
  | old x => exact evalHom_oldAct A f q heq x z.val
  | cons s v ih =>
    change evalHom f q (letterAct A b s (v.eval A b z)).val = _
    rw [evalHom_letterAct A b f q heq hexit]
    exact (congrArg (q s * ·) (ih hv.1)).trans (_root_.mul_assoc _ _ _).symm

/-- No extra relations were introduced by using irreducibles: any model
of the displayed reductions and old-action relation admits this homomorphism. -/
noncomputable def liftHom : Word A b →* N where
  toFun v := evalHom f q v.val
  map_one' := f.map_one
  map_mul' := evalHom_mul A b f q heq hexit

@[simp] theorem liftHom_old (x : M) :
    liftHom A b f q heq hexit (old A b x) = f x := rfl

@[simp] theorem liftHom_generator [IsConical M] (hb : b ≠ 1) (s : S) :
    liftHom A b f q heq hexit (generator A b hb s) = q s := by
  change q s * f 1 = q s
  rw [f.map_one, _root_.mul_one]

/-- A same-headed normal form is literally a generator times its suffix. -/
theorem generator_mul_of_not_headDiv [IsConical M] (hb : b ≠ 1)
    (s : S) (v : Word A b) (hv : ¬ headDiv A b b v) :
    generator A b hb s * v = cons A b s v hv :=
  (generator_mul A b hb s v).trans (letterAct_of_not_headDiv A b s v hv)

theorem hom_ext [IsConical M] (hb : b ≠ 1) (F G : Word A b →* N)
    (hOld : ∀ x, F (old A b x) = G (old A b x))
    (hNew : ∀ s, F (generator A b hb s) = G (generator A b hb s)) : F = G := by
  apply DFunLike.ext
  rintro ⟨v, hv⟩
  induction v with
  | old x => exact hOld x
  | cons s v ih =>
    change v.reduced A b ∧ ¬ v.headDiv A b at hv
    change F (cons A b s (⟨v, hv.1⟩ : Word A b) hv.2) =
      G (cons A b s (⟨v, hv.1⟩ : Word A b) hv.2)
    rw [← generator_mul_of_not_headDiv A b hb s (⟨v, hv.1⟩ : Word A b) hv.2]
    exact (F.map_mul _ _).trans ((congrArg₂ (· * ·) (hNew s) (ih hv.1)).trans
      (G.map_mul _ _).symm)

/-- Any product with a letter that is old must have gone through its exit. -/
theorem exit_dvd_of_letterAct_eq_old (s : S) (v : Word A b) {y : M}
    (hy : letterAct A b s v = old A b y) : A.exit s ∣ y := by
  classical
  by_cases h : headDiv A b b v
  · rw [letterAct_of_headDiv A b s v h] at hy
    obtain ⟨z, _, hz⟩ := (old_mul_eq_old_iff A b (A.exit s) y _).1 hy
    exact ⟨z, hz.symm⟩
  · rw [letterAct_of_not_headDiv A b s v h] at hy
    cases congrArg Subtype.val hy

/-- The gate of a single letter is its exit. The right factor `b` witnesses
attainment rather than a merely limiting old upper bound. -/
theorem generator_dvd_old_iff [IsConical M] (hb : b ≠ 1) (s : S) (y : M) :
    generator A b hb s ∣ old A b y ↔ A.exit s ∣ y := by
  constructor
  · rintro ⟨w, hw⟩
    rw [generator_mul] at hw
    exact exit_dvd_of_letterAct_eq_old A b s w hw.symm
  · rintro ⟨z, hz⟩
    refine ⟨old A b b * old A b z, ?_⟩
    rw [← _root_.mul_assoc, generator_mul_b]
    exact congrArg (old A b) hz
end Word

namespace Path
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}
  (P : Path M a) (he : e ≠ 1) (b : M)

abbrev Extension := Word (P.alphabet he) b

/-- Preservation of the entire old-cone intersection, in every new word. -/
theorem old_cone_intersection (x y j : M)
    (hj : ∀ z : M, x ∣ z ∧ y ∣ z ↔ j ∣ z) (w : P.Extension he b) :
    Word.old (P.alphabet he) b x ∣ w ∧ Word.old (P.alphabet he) b y ∣ w ↔
      Word.old (P.alphabet he) b j ∣ w := by
  simp only [Word.old_dvd_iff_headDiv]
  obtain ⟨w, hw⟩ := w
  cases w with
  | old z => exact hj z
  | cons s w => exact P.inCone_intersection x y j hj s

/-- A new probe word cannot create a common multiple for two disjoint old
cones, even though it may itself divide an old element. -/
theorem common_multiple_reflection {x y : M} {w : P.Extension he b}
    (hx : Word.old (P.alphabet he) b x ∣ w) (hy : Word.old (P.alphabet he) b y ∣ w) :
    ∃ z : M, x ∣ z ∧ y ∣ z := by
  rw [Word.old_dvd_iff_headDiv] at hx hy
  obtain ⟨w, hw⟩ := w
  cases w with
  | old z => exact ⟨z, hx, hy⟩
  | cons s w => exact P.old_common_multiple_of_cones hx hy

variable (hb : b ≠ 1)

noncomputable def probe (i : ℕ) : P.Extension he b :=
  Word.generator (P.alphabet he) b hb (P.letter i 1)

/-- The prescribed old right factor sends every adjoined path probe to its
specified old exit. -/
theorem probe_mul_b (i : ℕ) :
    P.probe he b hb i * Word.old (P.alphabet he) b b =
      Word.old (P.alphabet he) b (P.terminal i * e) := by
  rw [probe, Word.generator_mul_b]
  congr 1
  simp only [alphabet, exit, target_letter, one_mul]

@[simp] theorem probe_zero_mul_b :
    P.probe he b hb 0 * Word.old (P.alphabet he) b b =
      Word.old (P.alphabet he) b (a * e) := by
  rw [probe_mul_b, terminal_zero]

/-- The transition relations are genuine equalities in these normal forms. -/
theorem probe_transition {i j : ℕ} (hij : i ≤ j) :
    Word.old (P.alphabet he) b (P.factor i j hij) * P.probe he b hb j =
      P.probe he b hb i := by
  apply Subtype.ext
  change Raw.cons (P.act (P.factor i j hij) (P.letter j 1)) (.old 1) =
    Raw.cons (P.letter i 1) (.old 1)
  rw [act_letter, mul_one, ← one_mul (P.factor i j hij), letter_transition]

/-- Precisely the old elements in the countable lower closure divide `p₀`. -/
theorem probe_old_profile (x : M) :
    Word.old (P.alphabet he) b x ∣ P.probe he b hb 0 ↔ ∃ i, x ∣ P.node i := by
  rw [Word.old_dvd_iff_headDiv]
  exact P.initial_profile x

/-- No right cancellation is needed to show the probe is not below `a`. -/
theorem probe_not_dvd_a :
    ¬ P.probe he b hb 0 ∣ Word.old (P.alphabet he) b a := by
  rw [probe, Word.generator_dvd_old_iff]
  change ¬ P.target (P.letter 0 1) * e ∣ a
  simp only [target_letter, terminal_zero, one_mul]
  rintro ⟨z, hz⟩
  have heq : e * z = 1 := by
    apply mul_left_cancel (a := a)
    simpa only [mul_assoc, mul_one] using hz.symm
  exact he (IsConical.eq_one_of_mul_eq_one heq).1

end Path

namespace Raw
variable {M S : Type u}

def code : Raw M S → List S × M
  | .old x => ([], x)
  | .cons s w => (s :: (code w).1, (code w).2)

theorem code_injective : Function.Injective (code : Raw M S → List S × M) := by
  intro w
  induction w with
  | old x =>
    intro v he
    cases v with
    | old y => exact congrArg Raw.old (Prod.mk.inj he).2
    | cons s v => cases (Prod.mk.inj he).1
  | cons s w ih =>
    intro v he
    cases v with
    | old y => cases (Prod.mk.inj he).1
    | cons t v =>
      obtain ⟨hst, htail⟩ := List.cons.inj (Prod.mk.inj he).1
      exact congrArg₂ Raw.cons hst (ih (Prod.ext htail (Prod.mk.inj he).2))

theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hM : Cardinal.mk M ≤ μ) (hS : Cardinal.mk S ≤ μ) : Cardinal.mk (Raw M S) ≤ μ := by
  calc
    Cardinal.mk (Raw M S) ≤ Cardinal.mk (List S × M) := Cardinal.mk_le_of_injective code_injective
    _ = Cardinal.mk (List S) * Cardinal.mk M := by simp only [Cardinal.mk_prod, Cardinal.lift_id]
    _ ≤ max (max (Cardinal.mk (List S)) (Cardinal.mk M)) Cardinal.aleph0 :=
      Cardinal.mul_le_max _ _
    _ ≤ μ := max_le (max_le ((Cardinal.mk_list_le_max S).trans (max_le hω hS)) hM) hω
end Raw

namespace Path
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}
  (P : Path M a) (he : e ≠ 1) (b : M)

/-- The probe extension also respects the infinite scheduling bound. -/
theorem extension_cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hM : Cardinal.mk M ≤ μ) : Cardinal.mk (P.Extension he b) ≤ μ :=
  (Cardinal.mk_le_of_injective Subtype.val_injective).trans
    (Raw.cardinal_le hω hM (P.letters_cardinal_le hω hM))
end Path
end PartitionConsistency.ProbeAlgebra

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Algebra_ProbeGates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Probe extension: all gates, conditional joins, and presentation -/

namespace PartitionConsistency.ProbeAlgebra
universe u v
open DiagramOrder
namespace Raw

def head {M : Type u} {S : Type v} : Raw M S → Option S
  | .old _ => none
  | .cons s _ => some s

end Raw
namespace Word
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] (A : Alphabet M S) (b : M)

def head (w : Word A b) : Option S := w.val.head

@[simp] theorem head_old (x : M) : head A b (old A b x) = none := rfl
@[simp] theorem head_cons (s : S) (w : Word A b) (hw) :
    head A b (cons A b s w hw) = some s := rfl

/-- The first-letter blocks and the old elements partition the irreducibles. -/
theorem head_eq_none_iff (w : Word A b) :
    head A b w = none ↔ ∃ x, w = old A b x := by
  obtain ⟨w, hw⟩ := w
  cases w with
  | old x => exact ⟨fun _ => ⟨x, rfl⟩, fun _ => rfl⟩
  | cons s w =>
    constructor
    · intro h; cases h
    · rintro ⟨x, hx⟩; cases congrArg Subtype.val hx

theorem head_eq_some_iff (w : Word A b) (s : S) :
    head A b w = some s ↔ ∃ v, ∃ hv, w = cons A b s v hv := by
  obtain ⟨w, hw⟩ := w
  cases w with
  | old x =>
    constructor
    · intro h; cases h
    · rintro ⟨v, hv, hx⟩; cases congrArg Subtype.val hx
  | cons t w =>
    change w.reduced A b ∧ ¬ w.headDiv A b at hw
    constructor
    · intro ht
      cases Option.some.inj ht
      exact ⟨⟨w, hw.1⟩, hw.2, rfl⟩
    · rintro ⟨v, hv, he⟩
      exact congrArg (head A b) he

/-- Membership in an old cone depends only on the head of a new form. -/
theorem headDiv_of_head_eq_some {x : M} {w : Word A b} {s : S}
    (hw : head A b w = some s) : headDiv A b x w ↔ ∃ t, A.act x t = s := by
  obtain ⟨v, hv, rfl⟩ := (head_eq_some_iff A b w s).1 hw
  rfl

theorem headDiv_of_same_head {x : M} {w z : Word A b} {s : S}
    (hw : head A b w = some s) (hz : head A b z = some s) :
    headDiv A b x w ↔ headDiv A b x z :=
  (headDiv_of_head_eq_some A b hw).trans (headDiv_of_head_eq_some A b hz).symm

theorem head_oldAct_exit_ne (s : S) (w : Word A b) :
    head A b (oldAct A b (A.exit s) w) ≠ some s := by
  intro h
  exact A.separated s ((headDiv_of_head_eq_some A b h).1
    (headDiv_oldAct A b (A.exit s) w))

/-- A prepended letter exits its original block exactly when its input is
in the distinguished old `b`-cone. -/
theorem head_letterAct_ne_iff (s : S) (w : Word A b) :
    head A b (letterAct A b s w) ≠ some s ↔ headDiv A b b w := by
  classical
  by_cases h : headDiv A b b w
  · rw [letterAct_of_headDiv A b s w h]
    exact ⟨fun _ => h, fun _ => head_oldAct_exit_ne A b s _⟩
  · rw [letterAct_of_not_headDiv A b s w h, head_cons]
    exact ⟨fun h' => (h' rfl).elim, fun h' => (h h').elim⟩

/-- A gate is an old generator for precisely the part of a right cone
lying outside its word's first-letter block. -/
def Gate (w : Word A b) (s : S) (g : M) : Prop :=
  ∀ z : Word A b, (w ∣ z ∧ head A b z ≠ some s) ↔ old A b g ∣ z

theorem Gate.dvd {w : Word A b} {s : S} {g : M} (hg : Gate A b w s g) :
    w ∣ old A b g := ((hg _).2 (dvd_refl _)).1

theorem Gate.dvd_old_iff {w : Word A b} {s : S} {g : M}
    (hg : Gate A b w s g) (y : M) : w ∣ old A b y ↔ g ∣ y := by
  rw [← old_dvd_old_iff A b g y, ← hg]
  exact ⟨fun h => ⟨h, by intro he; cases he⟩, And.left⟩

/-- An old cone either contains a whole first-letter block or is disjoint
from that block; in the latter case it sees only the gate of a word. -/
theorem Gate.old_intersection {w : Word A b} {s : S} {g x : M}
    (hg : Gate A b w s g) (hw : head A b w = some s)
    (hx : ¬ headDiv A b x w) (z : Word A b) :
    old A b x ∣ z ∧ w ∣ z ↔ old A b x ∣ z ∧ old A b g ∣ z := by
  constructor
  · rintro ⟨hxz, hwz⟩
    refine ⟨hxz, (hg z).1 ⟨hwz, ?_⟩⟩
    intro hz
    exact hx ((headDiv_of_same_head A b hw hz).2 ((old_dvd_iff_headDiv A b x z).1 hxz))
  · rintro ⟨hxz, hgz⟩
    exact ⟨hxz, hg.dvd.trans hgz⟩

/-- A principal old intersection for the suffix computes the exit cone
of the word. The quotient `u` is an old right factor of the intersection. -/
theorem gate_of_suffix_intersection (s : S) (Y : Word A b)
    (hY : ¬ headDiv A b b Y) (u : M)
    (hI : ∀ z : Word A b,
      Y ∣ z ∧ old A b b ∣ z ↔ old A b (b * u) ∣ z) :
    Gate A b (cons A b s Y hY) s (A.exit s * u) := by
  intro z
  constructor
  · rintro ⟨⟨v, hv⟩, hz⟩
    have hex : headDiv A b b (Y * v) := by
      apply (head_letterAct_ne_iff A b s _).1
      exact (congrArg (head A b) hv) ▸ hz
    have hbu : old A b (b * u) ∣ Y * v :=
      (hI _).1 ⟨dvd_mul_right _ _, (old_dvd_iff_headDiv A b b _).2 hex⟩
    obtain ⟨q, hq⟩ := hbu
    refine ⟨q, ?_⟩
    calc
      z = letterAct A b s (Y * v) := hv
      _ = letterAct A b s (oldAct A b b (oldAct A b u q)) := by
        exact congrArg (letterAct A b s) (hq.trans (oldAct_mul A b b u q))
      _ = oldAct A b (A.exit s) (oldAct A b u q) := letterAct_oldAct_b A b s _
      _ = old A b (A.exit s * u) * q := (oldAct_mul A b _ _ _).symm
  · intro hg
    obtain ⟨v, hv⟩ := ((hI (old A b (b * u))).2 (dvd_refl _)).1
    have hwg : cons A b s Y hY * v = old A b (A.exit s * u) := by
      change letterAct A b s (Y * v) = _
      rw [← hv]
      change letterAct A b s (oldAct A b b (old A b u)) = _
      rw [letterAct_oldAct_b]
      rfl
    refine ⟨(show cons A b s Y hY ∣ old A b (A.exit s * u) from ⟨v, hwg.symm⟩).trans hg, ?_⟩
    obtain ⟨q, rfl⟩ := hg
    change head A b (oldAct A b (A.exit s * u) q) ≠ some s
    rw [oldAct_mul]
    exact head_oldAct_exit_ne A b s _

/-- Only old cone intersections are required for the recursive gate
calculation. The path alphabet supplies this law from old conditional joins. -/
def OldIntersections : Prop :=
  ∀ x y : M, ∀ z : Word A b, old A b x ∣ z → old A b y ∣ z →
    ∃ j : M, ∀ v : Word A b, old A b x ∣ v ∧ old A b y ∣ v ↔ old A b j ∣ v

/-- Every genuine exit of a new word determines a least old right-multiple
cone. This induction is on literal suffix length, not on a presumed join
operation for new words. -/
theorem exists_gate_of_exit (hOld : OldIntersections A b) (w : Word A b)
    {s : S} (hs : head A b w = some s) {z : Word A b}
    (hwz : w ∣ z) (hz : head A b z ≠ some s) :
    ∃ g : M, Gate A b w s g := by
  obtain ⟨w, hw⟩ := w
  induction w generalizing s z with
  | old x => cases hs
  | cons t Y ih =>
    have hts : t = s := Option.some.inj hs
    subst t
    change Y.reduced A b ∧ ¬ Y.headDiv A b at hw
    let Y' : Word A b := ⟨Y, hw.1⟩
    obtain ⟨v, hv⟩ := hwz
    have hbyv : old A b b ∣ Y' * v := by
      apply (old_dvd_iff_headDiv A b b _).2
      apply (head_letterAct_ne_iff A b s _).1
      exact (congrArg (head A b) hv) ▸ hz
    have hInt : ∃ j : M, ∀ q : Word A b,
        Y' ∣ q ∧ old A b b ∣ q ↔ old A b j ∣ q := by
      cases heY : Y with
      | old y =>
        have hYeq : Y' = old A b y := Subtype.ext heY
        rw [hYeq] at ⊢ hbyv
        exact hOld y b (old A b y * v) (dvd_mul_right _ _) hbyv
      | cons t Z =>
        have hY' : head A b Y' = some t := by change Y.head = some t; rw [heY]; rfl
        have hne : head A b (Y' * v) ≠ some t := by
          intro hh
          exact hw.2 ((headDiv_of_same_head A b hY' hh).2
            ((old_dvd_iff_headDiv A b b _).1 hbyv))
        obtain ⟨g, hg⟩ := ih hne hw.1 hY' (dvd_mul_right Y' v)
        have hgYv : old A b g ∣ Y' * v := (hg _).1 ⟨dvd_mul_right _ _, hne⟩
        obtain ⟨j, hj⟩ := hOld g b (Y' * v) hgYv hbyv
        refine ⟨j, fun q => ?_⟩
        calc
          Y' ∣ q ∧ old A b b ∣ q ↔ old A b b ∣ q ∧ Y' ∣ q := and_comm
          _ ↔ old A b b ∣ q ∧ old A b g ∣ q := Gate.old_intersection A b hg hY' hw.2 q
          _ ↔ old A b g ∣ q ∧ old A b b ∣ q := and_comm
          _ ↔ old A b j ∣ q := hj q
    obtain ⟨j, hj⟩ := hInt
    have hbj : b ∣ j := (old_dvd_old_iff A b b j).1 (((hj _).2 (dvd_refl _)).2)
    obtain ⟨u, rfl⟩ := hbj
    exact ⟨A.exit s * u, gate_of_suffix_intersection A b s Y' hw.2 u hj⟩

/-- A common multiple in one first-letter block forces every different-
headed divisor of that multiple to divide the entire block. -/
theorem dvd_of_different_head (hOld : OldIntersections A b)
    {w v z : Word A b} {s t : S}
    (hw : head A b w = some s) (hv : head A b v = some t) (hst : s ≠ t)
    (hvz : v ∣ z) (hz : head A b z = some s) : v ∣ w := by
  have hzt : head A b z ≠ some t := by rw [hz]; exact fun h => hst (Option.some.inj h)
  obtain ⟨g, hg⟩ := exists_gate_of_exit A b hOld v hv hvz hzt
  have hgz : old A b g ∣ z := (hg z).1 ⟨hvz, hzt⟩
  have hgw : old A b g ∣ w := by
    rw [old_dvd_iff_headDiv] at ⊢ hgz
    exact (headDiv_of_same_head A b hw hz).2 hgz
  exact (Gate.dvd A b hg).trans hgw

/-- Old divisors and differently headed new divisors both divide an
entire block as soon as they divide one member of that block. -/
theorem dvd_of_other_block (hOld : OldIntersections A b)
    {w v z : Word A b} {s : S}
    (hw : head A b w = some s) (hv : head A b v ≠ some s)
    (hvz : v ∣ z) (hz : head A b z = some s) : v ∣ w := by
  cases he : head A b v with
  | none =>
    obtain ⟨x, rfl⟩ := (head_eq_none_iff A b v).1 he
    rw [old_dvd_iff_headDiv] at ⊢ hvz
    exact (headDiv_of_same_head A b hw hz).2 hvz
  | some t =>
    exact dvd_of_different_head A b hOld hw he
      (fun hst => hv (hst ▸ he)) hvz hz

/-- The nonempty intersection of an old cone and any new cone is
computed by an old join, unless the old element already divides the word. -/
theorem old_word_cone_join (hOld : OldIntersections A b) (x : M) (w z : Word A b)
    (hxz : old A b x ∣ z) (hwz : w ∣ z) :
    ∃ j : Word A b, ∀ q : Word A b, old A b x ∣ q ∧ w ∣ q ↔ j ∣ q := by
  classical
  by_cases hxw : old A b x ∣ w
  · exact ⟨w, fun _ => ⟨And.right, fun h => ⟨hxw.trans h, h⟩⟩⟩
  cases he : head A b w with
  | none =>
    obtain ⟨y, rfl⟩ := (head_eq_none_iff A b w).1 he
    obtain ⟨j, hj⟩ := hOld x y z hxz hwz
    exact ⟨old A b j, hj⟩
  | some s =>
    have hx : ¬ headDiv A b x w := fun h => hxw ((old_dvd_iff_headDiv A b x w).2 h)
    have hzs : head A b z ≠ some s := by
      intro hz
      exact hx ((headDiv_of_same_head A b he hz).2 ((old_dvd_iff_headDiv A b x z).1 hxz))
    obtain ⟨g, hg⟩ := exists_gate_of_exit A b hOld w he hwz hzs
    obtain ⟨j, hj⟩ := hOld x g z hxz ((hg z).1 ⟨hwz, hzs⟩)
    exact ⟨old A b j, fun q => (Gate.old_intersection A b hg he hx q).trans (hj q)⟩

/-- Distinct incomparable first-letter blocks can meet only through both
of their gates, and the old cone law computes that intersection. -/
theorem different_head_cone_join (hOld : OldIntersections A b)
    {w v z : Word A b} {s t : S}
    (hw : head A b w = some s) (hv : head A b v = some t) (hst : s ≠ t)
    (hwz : w ∣ z) (hvz : v ∣ z) :
    ∃ j : Word A b, ∀ q, w ∣ q ∧ v ∣ q ↔ j ∣ q := by
  classical
  by_cases hwv : w ∣ v
  · exact ⟨v, fun _ => ⟨And.right, fun h => ⟨hwv.trans h, h⟩⟩⟩
  by_cases hvw : v ∣ w
  · exact ⟨w, fun _ => ⟨And.left, fun h => ⟨h, hvw.trans h⟩⟩⟩
  have hqs : ∀ q : Word A b, v ∣ q → head A b q ≠ some s := by
    intro q hvq hq
    exact hvw (dvd_of_different_head A b hOld hw hv hst hvq hq)
  have hqt : ∀ q : Word A b, w ∣ q → head A b q ≠ some t := by
    intro q hwq hq
    exact hwv (dvd_of_different_head A b hOld hv hw hst.symm hwq hq)
  obtain ⟨g, hg⟩ := exists_gate_of_exit A b hOld w hw hwz (hqs z hvz)
  obtain ⟨k, hk⟩ := exists_gate_of_exit A b hOld v hv hvz (hqt z hwz)
  obtain ⟨j, hj⟩ := hOld g k z ((hg z).1 ⟨hwz, hqs z hvz⟩) ((hk z).1 ⟨hvz, hqt z hwz⟩)
  refine ⟨old A b j, fun q => ?_⟩
  rw [← hj q]
  constructor
  · rintro ⟨hwq, hvq⟩
    exact ⟨(hg q).1 ⟨hwq, hqs q hvq⟩, (hk q).1 ⟨hvq, hqt q hwq⟩⟩
  · rintro ⟨hgq, hkq⟩
    exact ⟨(Gate.dvd A b hg).trans hgq, (Gate.dvd A b hk).trans hkq⟩

end Word

/-- Left translation preserves an exact cone-intersection equation in a
left-cancellative monoid. -/
theorem translate_cone_intersection {N : Type*} [LeftCancelMonoid N]
    (c x y j : N) (hj : ∀ q, x ∣ q ∧ y ∣ q ↔ j ∣ q) :
    ∀ q, c * x ∣ q ∧ c * y ∣ q ↔ c * j ∣ q := by
  intro q
  constructor
  · rintro ⟨⟨r, rfl⟩, hyr⟩
    rw [_root_.mul_assoc] at hyr ⊢
    apply (left_mul_dvd_iff c j (x * r)).2
    exact (hj _).1 ⟨dvd_mul_right _ _, (left_mul_dvd_iff c y (x * r)).1 hyr⟩
  · intro hq
    have hjxy := (hj j).2 (dvd_refl j)
    exact ⟨(mul_dvd_mul_left c hjxy.1).trans hq, (mul_dvd_mul_left c hjxy.2).trans hq⟩

namespace Word
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] [IsConical M]
  (A : Alphabet M S) (b : M) (hb : b ≠ 1)

include hb in
/-- All new conditional joins exist. Only the old cone theorem was used
in constructing gates; no intermediate join theorem is assumed. -/
theorem cone_join (hOld : OldIntersections A b) (w v z : Word A b)
    (hwz : w ∣ z) (hvz : v ∣ z) :
    ∃ j : Word A b, ∀ q, w ∣ q ∧ v ∣ q ↔ j ∣ q := by
  classical
  obtain ⟨w, hw⟩ := w
  induction w generalizing v z with
  | old x => exact old_word_cone_join A b hOld x v z hwz hvz
  | cons s Y ih =>
    change Y.reduced A b ∧ ¬ Y.headDiv A b at hw
    let Y' : Word A b := ⟨Y, hw.1⟩
    change cons A b s Y' hw.2 ∣ z at hwz
    change ∃ j, ∀ q, cons A b s Y' hw.2 ∣ q ∧ v ∣ q ↔ j ∣ q
    obtain ⟨v, hv⟩ := v
    cases v with
    | old y =>
      obtain ⟨j, hj⟩ := old_word_cone_join A b hOld y (cons A b s Y' hw.2) z hvz hwz
      exact ⟨j, fun q => and_comm.trans (hj q)⟩
    | cons t Z =>
      change Z.reduced A b ∧ ¬ Z.headDiv A b at hv
      let Z' : Word A b := ⟨Z, hv.1⟩
      change cons A b t Z' hv.2 ∣ z at hvz
      change ∃ j, ∀ q, cons A b s Y' hw.2 ∣ q ∧ cons A b t Z' hv.2 ∣ q ↔ j ∣ q
      by_cases hst : s = t
      · subst t
        let c := generator A b hb s
        have hY : cons A b s Y' hw.2 = c * Y' :=
          (generator_mul_of_not_headDiv A b hb s Y' hw.2).symm
        have hZ : cons A b s Z' hv.2 = c * Z' :=
          (generator_mul_of_not_headDiv A b hb s Z' hv.2).symm
        rw [hY, hZ] at ⊢
        rw [hY] at hwz
        rw [hZ] at hvz
        obtain ⟨r, rfl⟩ := hwz
        have hZr : Z' ∣ Y' * r := by
          apply (left_mul_dvd_iff c Z' (Y' * r)).1
          exact (_root_.mul_assoc c Y' r) ▸ hvz
        obtain ⟨j, hj⟩ := ih Z' (Y' * r) hZr hw.1 (dvd_mul_right _ _)
        exact ⟨c * j, translate_cone_intersection c Y' Z' j hj⟩
      · exact different_head_cone_join A b hOld rfl rfl hst hwz hvz

end Word

namespace Path
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}
  (P : Path M a) (he : e ≠ 1) (b : M)

/-- The old cone law used above is realized by the path alphabet. -/
theorem oldIntersections (hM : HasConditionalJoins (LeftDivOrder M)) :
    Word.OldIntersections (P.alphabet he) b := by
  intro x y z hx hy
  obtain ⟨a', hxa, hya⟩ := P.common_multiple_reflection he b hx hy
  obtain ⟨j, hj⟩ := exists_cone_join hM x y a' hxa hya
  exact ⟨j, P.old_cone_intersection he b x y j hj⟩

/-- Conditional joins in the actual probe extension, not just in the
old monoid or in the direct-limit alphabet. -/
theorem extension_hasConditionalJoins (hM : HasConditionalJoins (LeftDivOrder M)) (hb : b ≠ 1) :
    HasConditionalJoins (LeftDivOrder (P.Extension he b)) := by
  intro x y z hx hy
  obtain ⟨j, hj⟩ := Word.cone_join (P.alphabet he) b hb (P.oldIntersections he b hM) x y z
    ((LeftDivOrder.le_iff_dvd _ _).1 hx) ((LeftDivOrder.le_iff_dvd _ _).1 hy)
  refine ⟨j, (pair_lub_iff (α := LeftDivOrder (P.Extension he b)) x y j).2 (fun q => ?_)⟩
  rw [LeftDivOrder.le_iff_dvd (M := P.Extension he b) x q,
    LeftDivOrder.le_iff_dvd (M := P.Extension he b) y q,
    LeftDivOrder.le_iff_dvd (M := P.Extension he b) j q]
  exact hj q

end Path
end PartitionConsistency.ProbeAlgebra

namespace PartitionConsistency.ProbeAlgebra
universe u v
open DiagramOrder
namespace Word
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] [IsConical M]
  (A : Alphabet M S) (b : M) (hb : b ≠ 1)

/-- The exit of a one-letter probe is not merely a lower bound on its
old multiples: the entire exit cone is its precise gate cone. -/
theorem generator_gate (s : S) : Gate A b (generator A b hb s) s (A.exit s) := by
  have h1 : ¬ headDiv A b b (old A b 1) := by
    rintro ⟨z, hz⟩
    exact hb (IsConical.eq_one_of_mul_eq_one hz.symm).1
  have h := gate_of_suffix_intersection A b s (old A b 1) h1 1 (fun z => by
    change (1 : Word A b) ∣ z ∧ old A b b ∣ z ↔ old A b (b * 1) ∣ z
    rw [_root_.mul_one]
    exact ⟨And.right, fun h => ⟨one_dvd z, h⟩⟩)
  simpa only [generator, _root_.mul_one] using h

theorem generator_dvd_of_head {w : Word A b} {s : S} (hw : head A b w = some s) :
    generator A b hb s ∣ w := by
  obtain ⟨v, hv, rfl⟩ := (head_eq_some_iff A b w s).1 hw
  exact ⟨v, (generator_mul_of_not_headDiv A b hb s v hv).symm⟩

omit [IsConical M] in
/-- Entering a differently headed block factors through one old element,
including the case where the entering divisor was old to begin with. -/
theorem old_factor_of_other_block (hOld : OldIntersections A b)
    {w z : Word A b} {s : S} (hw : head A b w ≠ some s)
    (hz : head A b z = some s) (hwz : w ∣ z) :
    ∃ g : M, w ∣ old A b g ∧ old A b g ∣ z := by
  cases he : head A b w with
  | none =>
    obtain ⟨x, rfl⟩ := (head_eq_none_iff A b w).1 he
    exact ⟨x, dvd_refl _, hwz⟩
  | some t =>
    have hzt : head A b z ≠ some t := by
      intro hzt
      have hts : t = s := Option.some.inj (hzt.symm.trans hz)
      exact hw (hts ▸ he)
    obtain ⟨g, hg⟩ := exists_gate_of_exit A b hOld w he hwz hzt
    exact ⟨g, Gate.dvd A b hg, (hg z).1 ⟨hwz, hzt⟩⟩

end Word
namespace Path
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}
  (P : Path M a) (he : e ≠ 1) (b : M) (hb : b ≠ 1)

/-- The gate of the initial probe is exactly the specified old `ae`. -/
theorem probe_zero_gate : Word.Gate (P.alphabet he) b
    (P.probe he b hb 0) (P.letter 0 1) (a * e) := by
  have hg := Word.generator_gate (P.alphabet he) b hb (P.letter 0 1)
  simpa only [probe, alphabet, exit, target_letter, terminal_zero, one_mul] using hg

include hb in
/-- No divisor of `a`, whether old or newly created, belongs to the first-
letter block of the initial probe. -/
theorem head_ne_initial_of_dvd_a {w : P.Extension he b}
    (hwa : w ∣ Word.old (P.alphabet he) b a) :
    Word.head (P.alphabet he) b w ≠ some (P.letter 0 1) := by
  intro hh
  have hmw := Word.generator_dvd_of_head (P.alphabet he) b hb hh
  exact P.probe_not_dvd_a he b hb (hmw.trans hwa)

/-- The full divisor profile of the initial probe, including the newly
created divisors of `a`. This is equality of the actual two downsets in
the extension, not only agreement on the old submonoid. -/
theorem probe_full_profile (hM : HasConditionalJoins (LeftDivOrder M)) (w : P.Extension he b) :
    w ∣ P.probe he b hb 0 ∧ w ∣ Word.old (P.alphabet he) b a ↔
      ∃ i : ℕ, w ∣ Word.old (P.alphabet he) b (P.node i) := by
  constructor
  · rintro ⟨hwm, hwa⟩
    have hw := P.head_ne_initial_of_dvd_a he b hb hwa
    obtain ⟨g, hwg, hgm⟩ := Word.old_factor_of_other_block (P.alphabet he) b
      (P.oldIntersections he b hM) hw rfl hwm
    obtain ⟨i, hgi⟩ := (P.probe_old_profile he b hb g).1 hgm
    exact ⟨i, hwg.trans ((Word.old_dvd_old_iff _ _ _ _).2 hgi)⟩
  · rintro ⟨i, hwi⟩
    have him := (P.probe_old_profile he b hb (P.node i)).2 ⟨i, dvd_refl _⟩
    have hia := (Word.old_dvd_old_iff (P.alphabet he) b (P.node i) a).2 (P.bounded i)
    exact ⟨hwi.trans him, hwi.trans hia⟩

/-- Every divisor of `a` outside the probe's downset has join `ae` with
the probe. Both old and new divisors are covered. -/
theorem probe_join_profile (hM : HasConditionalJoins (LeftDivOrder M))
    {w : P.Extension he b} (hwa : w ∣ Word.old (P.alphabet he) b a)
    (hwm : ¬ w ∣ P.probe he b hb 0) (z : P.Extension he b) :
    w ∣ z ∧ P.probe he b hb 0 ∣ z ↔ Word.old (P.alphabet he) b (a * e) ∣ z := by
  have hg := P.probe_zero_gate he b hb
  have hwae : w ∣ Word.old (P.alphabet he) b (a * e) :=
    hwa.trans ((Word.old_dvd_old_iff _ _ _ _).2 (dvd_mul_right a e))
  constructor
  · rintro ⟨hwz, hmz⟩
    refine (hg z).1 ⟨hmz, ?_⟩
    intro hz
    exact hwm (Word.dvd_of_other_block (P.alphabet he) b (P.oldIntersections he b hM)
      rfl (P.head_ne_initial_of_dvd_a he b hb hwa) hwz hz)
  · intro hz
    exact ⟨hwae.trans hz, (Word.Gate.dvd _ _ hg).trans hz⟩

end Path
end PartitionConsistency.ProbeAlgebra

namespace PartitionConsistency.ProbeAlgebra.Path
universe u v
open DiagramOrder
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}
  (P : Path M a) (he : e ≠ 1) (b : M) {N : Type v} [Monoid N]
  (f : M →* N) (p : ℕ → N)

omit [IsConical M] in
/-- Adjacent transition relations imply every finite-stage transition
relation, without any right cancellation in either monoid. -/
theorem transitions_from_adjacent
    (hp : ∀ i, p i = f (P.factor i (i+1) (Nat.le_succ i)) * p (i+1))
    (i j : ℕ) (hij : i ≤ j) : p i = f (P.factor i j hij) * p j := by
  induction j, hij using Nat.le_induction with
  | base => simp only [factor_self, f.map_one, one_mul]
  | succ j hij ih =>
    calc
      p i = f (P.factor i j hij) * p j := ih
      _ = f (P.factor i j hij) * (f (P.factor j (j+1) (Nat.le_succ j)) * p (j+1)) :=
        congrArg (f (P.factor i j hij) * ·) (hp j)
      _ = f (P.factor i (j+1) (hij.trans (Nat.le_succ j))) * p (j+1) := by
        rw [← mul_assoc, ← f.map_mul, factor_trans]

variable (hp : ∀ i, p i = f (P.factor i (i+1) (Nat.le_succ i)) * p (i+1))
  (hbexit : ∀ i, p i * f b = f (P.terminal i * e))

/-- A family satisfying the original presentation's transition relations
induces its equivariant interpretation on direct-limit letters. -/
noncomputable def interpretedLetter : P.Letters → N :=
  DirectLimit.lift P.transition (fun i x => f x * p i)
    (fun i j hij x => by
      simp only [transition_apply, f.map_mul, mul_assoc]
      rw [← P.transitions_from_adjacent f p hp i j hij])

omit [IsConical M] in
@[simp] theorem interpretedLetter_mk (i : ℕ) (x : M) :
    P.interpretedLetter f p hp (P.letter i x) = f x * p i := rfl

omit [IsConical M] in
@[simp] theorem interpretedLetter_act (x : M) (s : P.Letters) :
    P.interpretedLetter f p hp (P.act x s) = f x * P.interpretedLetter f p hp s := by
  induction s using DirectLimit.induction with
  | ih i y =>
    change f (x * y) * p i = f x * (f y * p i)
    rw [f.map_mul, mul_assoc]

include hbexit in
omit [IsConical M] in
@[simp] theorem interpretedLetter_exit (s : P.Letters) :
    P.interpretedLetter f p hp s * f b = f (P.exit e s) := by
  induction s using DirectLimit.induction with
  | ih i x =>
    change (f x * p i) * f b = f ((x * P.terminal i) * e)
    rw [mul_assoc, hbexit]
    simp only [mul_assoc, f.map_mul]

/-- Universal evaluation for exactly the indexed probe presentation from
the source: no gate, join, normal-form, or height law is imposed on the
target monoid. -/
noncomputable def presentedLift : P.Extension he b →* N :=
  Word.liftHom (P.alphabet he) b f (P.interpretedLetter f p hp)
    (P.interpretedLetter_act f p hp) (P.interpretedLetter_exit b f p hp hbexit)

@[simp] theorem presentedLift_old (x : M) :
    P.presentedLift he b f p hp hbexit (Word.old (P.alphabet he) b x) = f x := rfl

@[simp] theorem presentedLift_probe (hb : b ≠ 1) (i : ℕ) :
    P.presentedLift he b f p hp hbexit (P.probe he b hb i) = p i := by
  change (P.interpretedLetter f p hp (P.letter i 1)) * f 1 = p i
  simp only [interpretedLetter_mk, f.map_one, one_mul, mul_one]

/-- Old elements and the displayed indexed generators determine every
homomorphism out of the actual extension. -/
theorem presentedHom_ext (hb : b ≠ 1) (F G : P.Extension he b →* N)
    (hOld : ∀ x : M, F (Word.old (P.alphabet he) b x) = G (Word.old (P.alphabet he) b x))
    (hNew : ∀ i : ℕ, F (P.probe he b hb i) = G (P.probe he b hb i)) : F = G := by
  apply Word.hom_ext (P.alphabet he) b hb F G hOld
  intro s
  induction s using DirectLimit.induction with
  | ih i x =>
    have hg : Word.generator (P.alphabet he) b hb (P.letter i x) =
        Word.old (P.alphabet he) b x * P.probe he b hb i := by
      apply Subtype.ext
      change Raw.cons (P.letter i x) (.old 1) =
        Raw.cons (P.act x (P.letter i 1)) (.old 1)
      rw [act_letter, mul_one]
    change F (Word.generator (P.alphabet he) b hb (P.letter i x)) =
      G (Word.generator (P.alphabet he) b hb (P.letter i x))
    rw [hg, F.map_mul, G.map_mul, hOld, hNew]

end PartitionConsistency.ProbeAlgebra.Path

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Algebra_ProbeMargins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Probe extension: construction and preservation of real margins -/

namespace PartitionConsistency.ProbeAlgebra
universe u v
open DiagramOrder

/-- Numerical intervals for the first-letter blocks. These inequalities are
constructed from the old margin below, rather than supplied for the extension. -/
structure HeightIntervals {M : Type u} {S : Type v} [LeftCancelMonoid M] [IsConical M]
    (A : Alphabet M S) (H : HeightCost (LeftDivOrder M)) where
  floor : S → ℝ
  offset : S → ℝ
  scale : S → ℝ
  outsideBound : S → ℝ
  floor_pos : ∀ s, 0 < floor s
  scale_pos : ∀ s, 0 < scale s
  floor_le : ∀ s x, (∃ t, A.act x t = s) → H.height x ≤ floor s
  lower_gap : ∀ s, floor s + scale s < offset s
  outside_nonneg : ∀ s, 0 ≤ outsideBound s
  upper_gap : ∀ s, offset s + scale s + outsideBound s < H.height (A.exit s)
  inside_cost : ∀ s x d, (∃ t, A.act x t = s) → (∃ t, A.act d t = s) →
    ¬ d ∣ x → H.cost d ≤ floor s - H.height x
  outside_cost : ∀ s d, d ∣ A.exit s → ¬ (∃ t, A.act d t = s) →
    H.cost d ≤ outsideBound s

namespace Path
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}
  (P : Path M a) (he : e ≠ 1) (H : HeightCost (LeftDivOrder M))

/-- The old first-letter divisors are a bounded ideal of the old monoid. -/
def letterIdeal (s : P.Letters) : ConeIdeal (α := LeftDivOrder M) (P.target s) where
  carrier := {x | P.InCone x s}
  nonempty := ⟨1, P.one_inCone s⟩
  bounded := fun _ hx => (LeftDivOrder.le_iff_dvd _ _).2 (P.dvd_target_of_inCone hx)
  lower := fun _ _ hxy hy => P.inCone_of_dvd ((LeftDivOrder.le_iff_dvd _ _).1 hxy) hy
  join_closed {x y j} hx hy hj := by
    apply (P.inCone_intersection x y j (fun z => ?_) s).1 ⟨hx, hy⟩
    have h := (pair_lub_iff (α := LeftDivOrder M) x y j).1 hj z
    rw [LeftDivOrder.le_iff_dvd (M := M) x z, LeftDivOrder.le_iff_dvd (M := M) y z,
      LeftDivOrder.le_iff_dvd (M := M) j z] at h
    exact h

/-- The supremum of the heights of all old divisors of a new letter. -/
noncomputable def letterFloor (s : P.Letters) : ℝ :=
  sSup (H.height '' (P.letterIdeal s).carrier)

theorem letter_heights_bdd (s : P.Letters) :
    BddAbove (H.height '' (P.letterIdeal s).carrier) := by
  refine ⟨H.height (P.target s), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact H.strictMono_height.monotone ((P.letterIdeal s).bounded hx)

theorem height_le_letterFloor {s : P.Letters} {x : M} (hx : P.InCone x s) :
    H.height x ≤ P.letterFloor H s :=
  le_csSup (P.letter_heights_bdd H s) ⟨x, hx, rfl⟩

theorem letterFloor_pos (s : P.Letters) : 0 < P.letterFloor H s :=
  (H.height_pos 1).trans_le (P.height_le_letterFloor H (P.one_inCone s))

theorem letterFloor_le (s : P.Letters) : P.letterFloor H s ≤ H.height (P.target s) := by
  apply csSup_le ((P.letterIdeal s).nonempty.image H.height)
  rintro _ ⟨x, hx, rfl⟩
  exact H.strictMono_height.monotone ((P.letterIdeal s).bounded hx)

/-- Joining two old divisors inside the letter ideal provides the bound
needed for missed divisors below an old-to-new comparison. -/
theorem letter_inside_cost (hM : HasConditionalJoins (LeftDivOrder M))
    {s : P.Letters} {x d : M} (hx : P.InCone x s) (hd : P.InCone d s) (hdx : ¬ d ∣ x) :
    H.cost d ≤ P.letterFloor H s - H.height x := by
  obtain ⟨j, hj⟩ := hM x d (P.target s)
    ((P.letterIdeal s).bounded hx) ((P.letterIdeal s).bounded hd)
  have hxj : @LE.le (LeftDivOrder M) _ x j := hj.1 (Set.mem_insert _ _)
  have hdj : @LE.le (LeftDivOrder M) _ d j := hj.1 (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hdx' : ¬ @LE.le (LeftDivOrder M) _ d x := fun hh => hdx ((LeftDivOrder.le_iff_dvd _ _).1 hh)
  have hlt : @LT.lt (LeftDivOrder M) _ x j := lt_of_le_not_ge hxj (fun h => hdx' (hdj.trans h))
  have hcost := H.point_margin hlt hdj hdx'
  have hjP := (P.letterIdeal s).join_closed hx hd hj
  have hbound := P.height_le_letterFloor H hjP
  linarith

/-- The height not yet used by the letter ideal controls every divisor
of its target outside that ideal. The bound is uniform over the ideal. -/
theorem target_outside_cost {s : P.Letters} {d : M}
    (hd : d ∣ P.target s) (hdP : ¬ P.InCone d s) :
    H.cost d ≤ H.height (P.target s) - P.letterFloor H s := by
  have hu : P.letterFloor H s ≤ H.height (P.target s) - H.cost d := by
    apply csSup_le ((P.letterIdeal s).nonempty.image H.height)
    rintro _ ⟨x, hx, rfl⟩
    have hdx : ¬ @LE.le (LeftDivOrder M) _ d x := by
      intro hdx
      exact hdP (P.inCone_of_dvd ((LeftDivOrder.le_iff_dvd _ _).1 hdx) hx)
    have hxlt : @LT.lt (LeftDivOrder M) _ x (P.target s) :=
      lt_of_le_not_ge ((P.letterIdeal s).bounded hx)
        (fun hkx => hdx (((LeftDivOrder.le_iff_dvd _ _).2 hd).trans hkx))
    have hcost := H.point_margin hxlt ((LeftDivOrder.le_iff_dvd _ _).2 hd) hdx
    linarith
  linarith

include he in
/-- The target is strictly below the exit: no right cancellation is used. -/
theorem target_lt_exit (s : P.Letters) :
    @LT.lt (LeftDivOrder M) _ (P.target s) (P.exit e s) := by
  refine lt_iff_le_and_ne.2 ⟨⟨e, rfl⟩, ?_⟩
  intro h
  have he1 : e = 1 := mul_left_cancel (a := P.target s)
    ((show P.target s * e = P.target s from h.symm).trans (mul_one _).symm)
  exact he he1

include he in
/-- The source's two strict interval inequalities, with a single bound
for all the old outside costs. -/
theorem exists_letter_interval (s : P.Letters) :
    ∃ u δ K : ℝ, 0 < δ ∧ P.letterFloor H s + δ < u ∧ 0 ≤ K ∧
      u + δ + K < H.height (P.exit e s) ∧
      ∀ d : M, d ∣ P.exit e s → ¬ P.InCone d s → H.cost d ≤ K := by
  obtain ⟨C, hC, hbound⟩ := H.uniform_margin (P.target_lt_exit he s)
  let p := H.height (P.target s) - P.letterFloor H s
  let q := H.height (P.exit e s) - H.height (P.target s)
  have hp : 0 ≤ p := sub_nonneg.mpr (P.letterFloor_le H s)
  have hq : 0 < q := sub_pos.mpr (H.strictMono_height (P.target_lt_exit he s))
  have hCq : C < q := hC
  let K := max p C
  have hKpos : 0 ≤ K := hp.trans (le_max_left _ _)
  have hroom : K < H.height (P.exit e s) - P.letterFloor H s := by
    apply max_lt
    · dsimp [p] at *; linarith
    · dsimp [p, q] at *; linarith
  let δ := (H.height (P.exit e s) - P.letterFloor H s - K) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  refine ⟨P.letterFloor H s + 2 * δ, δ, K, hδ, by linarith, hKpos, ?_, ?_⟩
  · dsimp [δ]; linarith
  · intro d hd hn
    by_cases hdk : d ∣ P.target s
    · exact (P.target_outside_cost H hdk hn).trans (le_max_left _ _)
    · exact (hbound d ((LeftDivOrder.le_iff_dvd _ _).2 hd)
        (fun hl => hdk ((LeftDivOrder.le_iff_dvd _ _).1 hl))).trans (le_max_right _ _)

/-- Intervals for all the new letters of this actual probe extension. -/
noncomputable def heightIntervals (hM : HasConditionalJoins (LeftDivOrder M)) :
    HeightIntervals (P.alphabet he) H := by
  choose u δ K hδ hlo hK hup hcost using P.exists_letter_interval he H
  exact {
    floor := P.letterFloor H
    offset := u
    scale := δ
    outsideBound := K
    floor_pos := P.letterFloor_pos H
    scale_pos := hδ
    floor_le := fun _ _ hx => P.height_le_letterFloor H hx
    lower_gap := hlo
    outside_nonneg := hK
    upper_gap := hup
    inside_cost := fun _ _ _ hx hd hdx => P.letter_inside_cost H hM hx hd hdx
    outside_cost := hcost }

end Path
end PartitionConsistency.ProbeAlgebra

namespace PartitionConsistency.ProbeAlgebra.Word
universe u v
open DiagramOrder Classical
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] [IsConical M]
  (A : Alphabet M S) (b : M) (H : HeightCost (LeftDivOrder M))

/-- A least old cone containing a word's old right multiples. It is used
only to choose a cost cap; the gate theorem proves its existence when needed. -/
def OldMinimum (w : Word A b) (g : M) : Prop :=
  ∀ y : M, w ∣ old A b y ↔ g ∣ y

theorem OldMinimum.unique {w : Word A b} {g k : M}
    (hg : OldMinimum A b w g) (hk : OldMinimum A b w k) : g = k := by
  apply le_antisymm (α := LeftDivOrder M)
  · exact (LeftDivOrder.le_iff_dvd _ _).2 ((hg k).1 ((hk k).2 (dvd_refl k)))
  · exact (LeftDivOrder.le_iff_dvd _ _).2 ((hk g).1 ((hg g).2 (dvd_refl g)))

/-- The cap is the cost of the actual least old right multiple, never
that of an arbitrarily larger old multiple (costs need not be monotone). -/
noncomputable def gateCap (w : Word A b) : ℝ :=
  if h : ∃ g : M, OldMinimum A b w g then H.cost h.choose else 1

theorem gateCap_pos (w : Word A b) : 0 < gateCap A b H w := by
  classical
  unfold gateCap
  split_ifs
  · exact H.cost_pos _
  · exact zero_lt_one

theorem gateCap_le_one (w : Word A b) : gateCap A b H w ≤ 1 := by
  classical
  unfold gateCap
  split_ifs
  · exact H.cost_le_one _
  · exact le_rfl

theorem gateCap_eq {w : Word A b} {g : M} (hg : OldMinimum A b w g) :
    gateCap A b H w = H.cost g := by
  classical
  have h : ∃ g : M, OldMinimum A b w g := ⟨g, hg⟩
  rw [gateCap, dite_eq_left h, OldMinimum.unique A b h.choose_spec hg]

variable (V : HeightIntervals A H)

/-- Recursive heights on literal irreducibles; the same formula is
harmless on unreduced strings. -/
noncomputable def rawHeight : Raw M S → ℝ
  | .old x => H.height x
  | .cons s w => V.offset s + V.scale s * rawHeight w

/-- The recursive cost makes both the suffix scale and the old gate's
cost available simultaneously. -/
noncomputable def rawCost : (w : Raw M S) → w.reduced A b → ℝ
  | .old x, _ => H.cost x
  | .cons s w, hw => min (V.scale s * rawCost w hw.1) (gateCap A b H ⟨.cons s w, hw⟩)

noncomputable def height (w : Word A b) : ℝ := rawHeight A H V w.val
noncomputable def cost (w : Word A b) : ℝ := rawCost A b H V w.val w.property

@[simp] theorem height_old (x : M) : height A b H V (old A b x) = H.height x := rfl
@[simp] theorem height_cons (s : S) (w : Word A b) (hw) :
    height A b H V (cons A b s w hw) = V.offset s + V.scale s * height A b H V w := rfl
@[simp] theorem cost_old (x : M) : cost A b H V (old A b x) = H.cost x := rfl
@[simp] theorem cost_cons (s : S) (w : Word A b) (hw) :
    cost A b H V (cons A b s w hw) =
      min (V.scale s * cost A b H V w) (gateCap A b H (cons A b s w hw)) := rfl

theorem height_bounds (w : Word A b) : 0 < height A b H V w ∧ height A b H V w < 1 := by
  obtain ⟨w, hw⟩ := w
  induction w with
  | old x => exact ⟨H.height_pos x, H.height_lt_one x⟩
  | cons s w ih =>
    obtain ⟨hl, hu⟩ := ih hw.1
    change 0 < V.offset s + V.scale s * rawHeight A H V w ∧
      V.offset s + V.scale s * rawHeight A H V w < 1
    change 0 < rawHeight A H V w at hl
    change rawHeight A H V w < 1 at hu
    have hf := V.floor_pos s
    have hs := V.scale_pos s
    have ho := V.lower_gap s
    have hg := V.upper_gap s
    have hk := V.outside_nonneg s
    have he := H.height_lt_one (A.exit s)
    constructor <;> nlinarith

theorem cost_bounds (w : Word A b) : 0 < cost A b H V w ∧ cost A b H V w ≤ 1 := by
  obtain ⟨w, hw⟩ := w
  induction w with
  | old x => exact ⟨H.cost_pos x, H.cost_le_one x⟩
  | cons s w ih =>
    obtain ⟨hl, _⟩ := ih hw.1
    change 0 < min (V.scale s * rawCost A b H V w hw.1) (gateCap A b H ⟨.cons s w, hw⟩) ∧
      min (V.scale s * rawCost A b H V w hw.1) (gateCap A b H ⟨.cons s w, hw⟩) ≤ 1
    exact ⟨lt_min (mul_pos (V.scale_pos s) hl) (gateCap_pos A b H _),
      (min_le_right _ _).trans (gateCap_le_one A b H _)⟩

theorem cost_le_scale {w : Word A b} {s : S} (hw : head A b w = some s) :
    cost A b H V w ≤ V.scale s := by
  obtain ⟨Y, hY, rfl⟩ := (head_eq_some_iff A b w s).1 hw
  rw [cost_cons]
  exact (min_le_left _ _).trans
    ((mul_le_mul_of_nonneg_left (cost_bounds A b H V Y).2 (V.scale_pos s).le).trans_eq
      (_root_.mul_one _))

/-- Every new word's cost is at most that of its specific old gate. -/
theorem cost_le_gate {w : Word A b} {s : S} {g : M}
    (hw : head A b w = some s) (hg : Gate A b w s g) : cost A b H V w ≤ H.cost g := by
  obtain ⟨Y, hY, rfl⟩ := (head_eq_some_iff A b w s).1 hw
  rw [cost_cons, gateCap_eq A b H (Gate.dvd_old_iff A b hg)]
  exact min_le_right _ _

/-- Any divisor of an old element has a cost-dominating old divisor
with exactly the same old-multiple profile. -/
theorem cost_old_factor (hOld : OldIntersections A b)
    {w : Word A b} {y : M} (hwy : w ∣ old A b y) :
    ∃ g : M, OldMinimum A b w g ∧ w ∣ old A b g ∧ g ∣ y ∧ cost A b H V w ≤ H.cost g := by
  cases hs : head A b w with
  | none =>
    obtain ⟨x, rfl⟩ := (head_eq_none_iff A b w).1 hs
    exact ⟨x, old_dvd_old_iff A b x, dvd_refl _, (old_dvd_old_iff A b x y).1 hwy, le_rfl⟩
  | some s =>
    obtain ⟨g, hg⟩ := exists_gate_of_exit A b hOld w hs hwy (by intro h; cases h)
    exact ⟨g, Gate.dvd_old_iff A b hg, Gate.dvd A b hg,
      (Gate.dvd_old_iff A b hg y).1 hwy, cost_le_gate A b H V hs hg⟩

/-- The cost of an outside-block divisor is controlled by an old member
of that block's letter ideal. -/
theorem cost_other_block_factor (hOld : OldIntersections A b)
    {w z : Word A b} {s : S} (hw : head A b w ≠ some s)
    (hz : head A b z = some s) (hwz : w ∣ z) :
    ∃ g : M, w ∣ old A b g ∧ old A b g ∣ z ∧ cost A b H V w ≤ H.cost g := by
  cases ht : head A b w with
  | none =>
    obtain ⟨x, rfl⟩ := (head_eq_none_iff A b w).1 ht
    exact ⟨x, dvd_refl _, hwz, le_rfl⟩
  | some t =>
    have hzt : head A b z ≠ some t := by
      intro hzt
      have hts : t = s := Option.some.inj (hzt.symm.trans hz)
      exact hw (hts ▸ ht)
    obtain ⟨g, hg⟩ := exists_gate_of_exit A b hOld w ht hwz hzt
    exact ⟨g, Gate.dvd A b hg, (hg z).1 ⟨hwz, hzt⟩, cost_le_gate A b H V ht hg⟩

end PartitionConsistency.ProbeAlgebra.Word

namespace PartitionConsistency.ProbeAlgebra.Word
universe u v
open DiagramOrder Classical
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] [IsConical M]
  (A : Alphabet M S) (b : M) (H : HeightCost (LeftDivOrder M))
  (V : HeightIntervals A H) (hOld : OldIntersections A b)

include hOld in
/-- For old comparisons, gates dominate every new missed cost. -/
theorem uniform_margin_old {x y : LeftDivOrder M} (hxy : x < y) :
    UniformMargin (α := LeftDivOrder (Word A b)) (height A b H V) (cost A b H V)
      (old A b x) (old A b y) := by
  obtain ⟨C, hC, hbound⟩ := H.uniform_margin hxy
  refine ⟨C, hC, ?_⟩
  intro d hdy hdx
  obtain ⟨g, _, hdg, hgy, hcost⟩ := cost_old_factor A b H V hOld
    ((LeftDivOrder.le_iff_dvd _ _).1 hdy)
  apply hcost.trans
  apply hbound g ((LeftDivOrder.le_iff_dvd _ _).2 hgy)
  intro hgx
  exact hdx ((LeftDivOrder.le_iff_dvd _ _).2
    (hdg.trans ((old_dvd_old_iff A b g x).2 ((LeftDivOrder.le_iff_dvd _ _).1 hgx))))

include hOld in
/-- Margins from an old element into a new first-letter block: outside
costs use the letter-ideal floor, inside costs use the suffix scale. -/
theorem uniform_margin_old_new {x : M} {w : Word A b} {s : S}
    (hw : head A b w = some s) (hxw : old A b x ∣ w) :
    UniformMargin (α := LeftDivOrder (Word A b)) (height A b H V) (cost A b H V)
      (old A b x) w := by
  have hx : ∃ t, A.act x t = s := (headDiv_of_head_eq_some A b hw).1
    ((old_dvd_iff_headDiv A b x w).1 hxw)
  have hlo := V.lower_gap s
  have hfloor := V.floor_le s x hx
  have hscale := V.scale_pos s
  obtain ⟨Y, hY, rfl⟩ := (head_eq_some_iff A b w s).1 hw
  have hpos := (height_bounds A b H V Y).1
  refine ⟨max (V.floor s - H.height x) (V.scale s), ?_, ?_⟩
  · rw [height_cons, height_old]
    apply max_lt <;> nlinarith
  · intro d hdw hdx
    have hdw' := (LeftDivOrder.le_iff_dvd _ _).1 hdw
    by_cases hds : head A b d = some s
    · exact (cost_le_scale A b H V hds).trans (le_max_right _ _)
    · obtain ⟨g, hdg, hgw, hcost⟩ := cost_other_block_factor A b H V hOld hds rfl hdw'
      have hg : ∃ t, A.act g t = s := (headDiv_of_head_eq_some A b (w := cons A b s Y hY) rfl).1
        ((old_dvd_iff_headDiv A b g _).1 hgw)
      have hgn : ¬ g ∣ x := fun he => hdx ((LeftDivOrder.le_iff_dvd _ _).2
        (hdg.trans ((old_dvd_old_iff A b g x).2 he)))
      exact (hcost.trans (V.inside_cost s x g hx hg hgn)).trans (le_max_left _ _)

include hOld in
/-- Margins from a new first-letter block to an old multiple. The old
gate bounds all costs without presuming that costs are monotone. -/
theorem uniform_margin_new_old (hb : b ≠ 1) {w : Word A b} {s : S} {y : M}
    (hw : head A b w = some s) (hwy : w ∣ old A b y) :
    UniformMargin (α := LeftDivOrder (Word A b)) (height A b H V) (cost A b H V)
      w (old A b y) := by
  have hhey : A.exit s ∣ y := (generator_dvd_old_iff A b hb s y).1
    ((generator_dvd_of_head A b hb hw).trans hwy)
  have hheyle : @LE.le (LeftDivOrder M) _ (A.exit s) y := (LeftDivOrder.le_iff_dvd _ _).2 hhey
  obtain ⟨C, hC, hbound⟩ : ∃ C : ℝ, C ≤ H.height y - H.height (A.exit s) ∧
      ∀ d : M, d ∣ y → ¬ d ∣ A.exit s → H.cost d ≤ C := by
    by_cases he : A.exit s = y
    · exact ⟨0, by rw [← he, sub_self], fun _ hdy hds => (hds (he ▸ hdy)).elim⟩
    · obtain ⟨c, hc, hcost⟩ := H.uniform_margin (lt_iff_le_and_ne.2 ⟨hheyle, he⟩)
      exact ⟨c, hc.le, fun d hdy hds => hcost d ((LeftDivOrder.le_iff_dvd _ _).2 hdy)
        (fun he => hds ((LeftDivOrder.le_iff_dvd _ _).1 he))⟩
  have hhy := H.strictMono_height.monotone hheyle
  have hup := V.upper_gap s
  have hK := V.outside_nonneg s
  obtain ⟨Y, hY, rfl⟩ := (head_eq_some_iff A b w s).1 hw
  have hYlt := (height_bounds A b H V Y).2
  have hsp := V.scale_pos s
  refine ⟨max (V.outsideBound s) C, ?_, ?_⟩
  · rw [height_old, height_cons]
    apply max_lt <;> nlinarith
  · intro d hdy hdw
    obtain ⟨g, _, hdg, hgy, hcost⟩ := cost_old_factor A b H V hOld
      ((LeftDivOrder.le_iff_dvd _ _).1 hdy)
    have hgn : ¬ ∃ t, A.act g t = s := by
      intro hg
      have hgw : old A b g ∣ cons A b s Y hY := (old_dvd_iff_headDiv A b g _).2 hg
      exact hdw ((LeftDivOrder.le_iff_dvd _ _).2 (hdg.trans hgw))
    by_cases hgs : g ∣ A.exit s
    · exact (hcost.trans (V.outside_cost s g hgs hgn)).trans (le_max_left _ _)
    · exact (hcost.trans (hbound g hgy hgs)).trans (le_max_right _ _)

/-- Comparisons within one block are precisely suffix comparisons. -/
theorem cons_dvd_cons_iff (hb : b ≠ 1) (s : S) (Y Z : Word A b) (hY hZ) :
    cons A b s Y hY ∣ cons A b s Z hZ ↔ Y ∣ Z := by
  rw [← generator_mul_of_not_headDiv A b hb s Y hY,
    ← generator_mul_of_not_headDiv A b hb s Z hZ]
  exact left_mul_dvd_iff _ _ _

include hOld in
/-- The uniform margin in one block is the suffix margin multiplied by
its positive scale. All other-block divisors divide both endpoints. -/
theorem uniform_margin_same_head (hb : b ≠ 1) (s : S) (Y Z : Word A b) (hY hZ)
    (hmargin : UniformMargin (α := LeftDivOrder (Word A b))
      (height A b H V) (cost A b H V) Y Z) :
    UniformMargin (α := LeftDivOrder (Word A b)) (height A b H V) (cost A b H V)
      (cons A b s Y hY) (cons A b s Z hZ) := by
  obtain ⟨C, hC, hbound⟩ := hmargin
  refine ⟨V.scale s * C, ?_, ?_⟩
  · rw [height_cons, height_cons]
    have hc := mul_lt_mul_of_pos_left hC (V.scale_pos s)
    nlinarith
  · intro d hdZ hdY
    have hdZ' := (LeftDivOrder.le_iff_dvd _ _).1 hdZ
    by_cases hds : head A b d = some s
    · obtain ⟨D, hD, rfl⟩ := (head_eq_some_iff A b d s).1 hds
      have hDZ : @LE.le (LeftDivOrder (Word A b)) _ D Z :=
        (LeftDivOrder.le_iff_dvd _ _).2 ((cons_dvd_cons_iff A b hb s D Z hD hZ).1 hdZ')
      have hDnY : ¬ @LE.le (LeftDivOrder (Word A b)) _ D Y := by
        intro hDY
        exact hdY ((LeftDivOrder.le_iff_dvd _ _).2 ((cons_dvd_cons_iff A b hb s D Y hD hY).2
          ((LeftDivOrder.le_iff_dvd _ _).1 hDY)))
      rw [cost_cons]
      exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left (hbound D hDZ hDnY) (V.scale_pos s).le)
    · exact (hdY ((LeftDivOrder.le_iff_dvd _ _).2
        (dvd_of_other_block A b hOld rfl hds hdZ' rfl))).elim

omit [IsConical M] in
/-- Old elements and elements of a first-letter block are distinct. -/
theorem new_ne_old {w : Word A b} {s : S} (hw : head A b w = some s) (x : M) : w ≠ old A b x := by
  intro he
  rw [he, head_old] at hw
  cases hw

include hOld in
/-- Structural induction checks every strict comparison of irreducible
words, using an intervening old gate precisely for different new blocks. -/
theorem uniform_margin (hb : b ≠ 1) (z : Word A b) :
    ∀ w : Word A b, @LT.lt (LeftDivOrder (Word A b)) _ w z →
      UniformMargin (α := LeftDivOrder (Word A b)) (height A b H V) (cost A b H V) w z := by
  obtain ⟨z, hz⟩ := z
  induction z with
  | old y =>
    intro w hwy
    have hwy' := (LeftDivOrder.le_iff_dvd _ _).1 hwy.le
    cases hs : head A b w with
    | none =>
      obtain ⟨x, rfl⟩ := (head_eq_none_iff A b w).1 hs
      have hxy : @LT.lt (LeftDivOrder M) _ x y := lt_iff_le_and_ne.2
        ⟨(LeftDivOrder.le_iff_dvd _ _).2 ((old_dvd_old_iff A b x y).1 hwy'),
         fun he => hwy.ne (congrArg (old A b) he)⟩
      exact uniform_margin_old A b H V hOld hxy
    | some s => exact uniform_margin_new_old A b H V hOld hb hs hwy'
  | cons s Z ih =>
    intro w hwz
    let Z' : Word A b := ⟨Z, hz.1⟩
    change @LT.lt (LeftDivOrder (Word A b)) _ w (cons A b s Z' hz.2) at hwz
    change UniformMargin (α := LeftDivOrder (Word A b)) (height A b H V) (cost A b H V)
      w (cons A b s Z' hz.2)
    have hwz' := (LeftDivOrder.le_iff_dvd _ _).1 hwz.le
    by_cases hws : head A b w = some s
    · obtain ⟨Y, hY, rfl⟩ := (head_eq_some_iff A b w s).1 hws
      have hYZ : @LT.lt (LeftDivOrder (Word A b)) _ Y Z' := lt_iff_le_and_ne.2
        ⟨(LeftDivOrder.le_iff_dvd _ _).2 ((cons_dvd_cons_iff A b hb s Y Z' hY hz.2).1 hwz'),
          fun he => hwz.ne (Subtype.ext (congrArg (Raw.cons s) (congrArg Subtype.val he)))⟩
      exact uniform_margin_same_head A b H V hOld hb s Y Z' hY hz.2 (ih hz.1 Y hYZ)
    · cases ht : head A b w with
      | none =>
        obtain ⟨x, rfl⟩ := (head_eq_none_iff A b w).1 ht
        exact uniform_margin_old_new A b H V hOld rfl hwz'
      | some t =>
        obtain ⟨g, hwg, hgz⟩ := old_factor_of_other_block A b hOld hws rfl hwz'
        have hwglt : @LT.lt (LeftDivOrder (Word A b)) _ w (old A b g) :=
          lt_iff_le_and_ne.2 ⟨(LeftDivOrder.le_iff_dvd _ _).2 hwg, new_ne_old A b ht g⟩
        have hgzlt : @LT.lt (LeftDivOrder (Word A b)) _ (old A b g) (cons A b s Z' hz.2) :=
          lt_iff_le_and_ne.2 ⟨(LeftDivOrder.le_iff_dvd _ _).2 hgz, (new_ne_old A b rfl g).symm⟩
        exact UniformMargin.trans hwglt hgzlt (fun d => (cost_bounds A b H V d).1)
          (uniform_margin_new_old A b H V hOld hb ht hwg)
          (uniform_margin_old_new A b H V hOld rfl hgz)

/-- Extending height and cost data on the actual probe normal forms. -/
noncomputable def heightCost (hb : b ≠ 1) : HeightCost (LeftDivOrder (Word A b)) where
  height := height A b H V
  cost := cost A b H V
  height_pos w := (height_bounds A b H V w).1
  height_lt_one w := (height_bounds A b H V w).2
  cost_pos w := (cost_bounds A b H V w).1
  cost_le_one w := (cost_bounds A b H V w).2
  margin {w z} hwz := (uniform_margin A b H V hOld hb z w hwz).supremum_lt hwz

end PartitionConsistency.ProbeAlgebra.Word

namespace PartitionConsistency.ProbeAlgebra.Word
universe u v
open DiagramOrder Classical
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] [IsConical M]
  (A : Alphabet M S) (b : M) (H : HeightCost (LeftDivOrder M))
  (V : HeightIntervals A H) (hOld : OldIntersections A b)

include hOld in
/-- New divisors need not have old costs equal to theirs. Nevertheless,
the cost-dominating old gates preserve exactly each old missed-cost supremum. -/
theorem old_cost_supremum (x y : LeftDivOrder M) :
    sSup (cost A b H V ''
      {d : LeftDivOrder (Word A b) | d ≤ old A b y ∧ ¬ d ≤ old A b x}) =
        sSup (H.cost '' {d : LeftDivOrder M | d ≤ y ∧ ¬ d ≤ x}) := by
  let S₀ := H.cost '' {d : LeftDivOrder M | d ≤ y ∧ ¬d ≤ x}
  let S₁ := cost A b H V ''
      {d : LeftDivOrder (Word A b) | d ≤ old A b y ∧ ¬ d ≤ old A b x}
  change sSup S₁ = sSup S₀
  have hsubset : S₀ ⊆ S₁ := by
    rintro r ⟨d, ⟨hdy, hdx⟩, rfl⟩
    refine ⟨old A b d, ⟨?_, ?_⟩, rfl⟩
    · exact (LeftDivOrder.le_iff_dvd _ _).2 ((old_dvd_old_iff A b d y).2
        ((LeftDivOrder.le_iff_dvd _ _).1 hdy))
    · intro hh
      exact hdx ((LeftDivOrder.le_iff_dvd _ _).2 ((old_dvd_old_iff A b d x).1
        ((LeftDivOrder.le_iff_dvd _ _).1 hh)))
  have hdom : ∀ r ∈ S₁, ∃ c ∈ S₀, r ≤ c := by
    rintro _ ⟨d, ⟨hdy, hdx⟩, rfl⟩
    obtain ⟨g, _, hdg, hgy, hcost⟩ := cost_old_factor A b H V hOld
      ((LeftDivOrder.le_iff_dvd _ _).1 hdy)
    refine ⟨H.cost g, ⟨g, ⟨(LeftDivOrder.le_iff_dvd _ _).2 hgy, ?_⟩, rfl⟩, hcost⟩
    intro hgx
    exact hdx ((LeftDivOrder.le_iff_dvd _ _).2
      (hdg.trans ((old_dvd_old_iff A b g x).2 ((LeftDivOrder.le_iff_dvd _ _).1 hgx))))
  by_cases hS : S₀.Nonempty
  · have hT : S₁.Nonempty := hS.mono hsubset
    have hbS : BddAbove S₀ := by
      refine ⟨1, ?_⟩
      rintro _ ⟨d, _, rfl⟩
      exact H.cost_le_one d
    have hbT : BddAbove S₁ := by
      refine ⟨1, ?_⟩
      rintro _ ⟨d, _, rfl⟩
      exact (cost_bounds A b H V d).2
    apply le_antisymm
    · apply csSup_le hT
      intro r hr
      obtain ⟨c, hc, hrc⟩ := hdom r hr
      exact hrc.trans (le_csSup hbS hc)
    · exact csSup_le hS (fun _ hr => le_csSup hbT (hsubset hr))
  · have hS0 : S₀ = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have hS1 : S₁ = ∅ := Set.not_nonempty_iff_eq_empty.mp (by
      rintro ⟨r, hr⟩
      obtain ⟨c, hc, _⟩ := hdom r hr
      exact hS ⟨c, hc⟩)
    rw [hS0, hS1]

end PartitionConsistency.ProbeAlgebra.Word

namespace PartitionConsistency.ProbeAlgebra.Path
universe u
open DiagramOrder
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}
  (P : Path M a) (he : e ≠ 1) (b : M) (hb : b ≠ 1)
  (H : HeightCost (LeftDivOrder M)) (hM : HasConditionalJoins (LeftDivOrder M))

/-- Source `lem:mono-probe-heights`: admissible heights and costs on the
actual indexed probe extension, constructed by its normal forms and gates. -/
noncomputable def extensionHeightCost : HeightCost (LeftDivOrder (P.Extension he b)) :=
  Word.heightCost (P.alphabet he) b H (P.heightIntervals he H hM) (P.oldIntersections he b hM) hb

@[simp] theorem extensionHeightCost_height_old (x : M) :
    (P.extensionHeightCost he b hb H hM).height (Word.old (P.alphabet he) b x) = H.height x := rfl

@[simp] theorem extensionHeightCost_cost_old (x : M) :
    (P.extensionHeightCost he b hb H hM).cost (Word.old (P.alphabet he) b x) = H.cost x := rfl

/-- The exact supremum conservativity needed at limit stages of the tower,
including the case where the set of missed divisors is empty. -/
theorem extension_old_cost_supremum (x y : LeftDivOrder M) :
    sSup ((P.extensionHeightCost he b hb H hM).cost ''
      {d : LeftDivOrder (P.Extension he b) | d ≤ Word.old (P.alphabet he) b y ∧
        ¬ d ≤ Word.old (P.alphabet he) b x}) =
      sSup (H.cost '' {d : LeftDivOrder M | d ≤ y ∧ ¬ d ≤ x}) :=
  Word.old_cost_supremum (P.alphabet he) b H (P.heightIntervals he H hM)
    (P.oldIntersections he b hM) x y

end PartitionConsistency.ProbeAlgebra.Path

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Algebra_ConservativeExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency.DiagramOrder
universe u v w

/-- Conservation of a submonoid means more than an injective homomorphism:
right factors of old comparisons, entire old intersections, and absence of
old common right multiples are preserved. -/
structure Conservative {M : Type u} {N : Type v} [Monoid M] [Monoid N]
    (f : M →* N) : Prop where
  injective : Function.Injective f
  factors : ∀ x y : M, ∀ z : N, f x * z = f y → ∃ t : M, f t = z
  intersections : ∀ x y j : M, (∀ z : M, x ∣ z ∧ y ∣ z ↔ j ∣ z) →
    ∀ z : N, f x ∣ z ∧ f y ∣ z ↔ f j ∣ z
  common : ∀ x y : M, (∃ z : N, f x ∣ z ∧ f y ∣ z) →
    ∃ z : M, x ∣ z ∧ y ∣ z

namespace Conservative
variable {M : Type u} {N : Type v} {R : Type w} [Monoid M] [Monoid N] [Monoid R]
  {f : M →* N} (hf : Conservative f)

include hf

/-- Division is reflected together with its particular unique factor,
not by an unrelated witness to the existence of a comparison. -/
theorem factor_eq {x y : M} {z : N} (h : f x * z = f y) :
    ∃ t : M, f t = z ∧ x * t = y := by
  obtain ⟨t, ht⟩ := hf.factors x y z h
  exact ⟨t, ht, hf.injective (by rw [f.map_mul, ht, h])⟩

theorem dvd_iff (x y : M) : f x ∣ f y ↔ x ∣ y := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨t, _, ht⟩ := hf.factor_eq hz.symm
    exact ⟨t, ht.symm⟩
  · exact f.map_dvd

theorem common_iff (x y : M) :
    (∃ z : N, f x ∣ z ∧ f y ∣ z) ↔ ∃ z : M, x ∣ z ∧ y ∣ z := by
  constructor
  · exact hf.common x y
  · rintro ⟨z, hxz, hyz⟩
    exact ⟨f z, f.map_dvd hxz, f.map_dvd hyz⟩

/-- The composition law is what makes comparisons testable in the final
monoid, independently of the birth step at which a factor was computed. -/
theorem comp {g : N →* R} (hg : Conservative g) : Conservative (g.comp f) where
  injective := hg.injective.comp hf.injective
  factors x y z h := by
    obtain ⟨t, ht, he⟩ := hg.factor_eq h
    obtain ⟨s, hs⟩ := hf.factors x y t he
    exact ⟨s, by change g (f s) = z; rw [hs, ht]⟩
  intersections x y j hj := hg.intersections (f x) (f y) (f j) (hf.intersections x y j hj)
  common x y h := hf.common x y (hg.common (f x) (f y) h)

omit hf in
/-- Identity inclusions are conservative. -/
theorem id (M : Type u) [Monoid M] : Conservative (MonoidHom.id M) where
  injective := Function.injective_id
  factors _ _ z _ := ⟨z, rfl⟩
  intersections _ _ _ h := h
  common _ _ h := h

end Conservative
end PartitionConsistency.DiagramOrder

namespace PartitionConsistency.ProbeAlgebra.Path
universe u
open DiagramOrder
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}
  (P : Path M a) (he : e ≠ 1) (b : M)

/-- All four conservation requirements for the actual probe extension. -/
theorem oldHom_conservative : Conservative (Word.oldHom (P.alphabet he) b) where
  injective := Word.oldHom_injective _ _
  factors x y z hz := by
    obtain ⟨t, ht, _⟩ := (Word.old_mul_eq_old_iff (P.alphabet he) b x y z).1 hz
    exact ⟨t, ht.symm⟩
  intersections := P.old_cone_intersection he b
  common _ _ h := by
    obtain ⟨z, hx, hy⟩ := h
    exact P.common_multiple_reflection he b hx hy

end PartitionConsistency.ProbeAlgebra.Path

namespace PartitionConsistency.MergerAlgebra.Word
universe u v
open DiagramOrder
variable {M : Type u} {D : Type v} [Monoid M] [RightFreeAction M D]

/-- All four conservation requirements for merger normal forms. -/
theorem oldHom_conservative : Conservative (oldHom : M →* Word M D) where
  injective := oldHom_injective
  factors x y z hz := by
    obtain ⟨_, t, _, ht, _⟩ := factors_of_old hz
    exact ⟨t, ht.symm⟩
  intersections := preserve_old_cone_intersection
  common x y h := (old_common_multiple_iff x y).1 h

end PartitionConsistency.MergerAlgebra.Word

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u v
open DiagramOrder
variable {B : Type u} {M : Type v} [Monoid B] [Monoid M] {n : ℕ}

/-- Transport the actual overlap starts along a base homomorphism. The
pair relation remains the given one-step relation, not its transitive closure. -/
def map (P : OverlapPrescription B n) (f : B →* M) : OverlapPrescription M n where
  start i j := (P.start i j).map (fun ab => (f ab.1, f ab.2))

@[simp] theorem map_start (P : OverlapPrescription B n) (f : B →* M) (i j : Fin n) :
    (P.map f).start i j = (P.start i j).map (fun ab => (f ab.1, f ab.2)) := rfl

/-- Each prescribed identification is valid after transporting its factors. -/
theorem rel_map (P : OverlapPrescription B n) (f : B →* M)
    {i j : Fin n} {x y : B} (h : P.Rel (i,x) (j,y)) :
    (P.map f).Rel (i, f x) (j, f y) := by
  classical
  by_cases hij : i = j
  · subst j
    rw [P.rel_same_copy] at h
    exact ((P.map f).rel_same_copy i _ _).2 (congrArg f h)
  · simp only [Rel, hij, ↓reduceIte] at h ⊢
    cases he : P.start i j with
    | none => cases he ▸ h
    | some ab =>
      obtain ⟨a,b⟩ := ab
      rw [he] at h
      obtain ⟨t, rfl, rfl⟩ := h
      simp only [map_start, he, Option.map_some]
      exact ⟨f t, f.map_mul _ _, f.map_mul _ _⟩

/-- Factor conservation reflects each one-step identification, without
assuming that the prescription is valid in either monoid. -/
theorem rel_map_iff (P : OverlapPrescription B n) {f : B →* M} (hf : Conservative f)
    (i j : Fin n) (x y : B) :
    (P.map f).Rel (i, f x) (j, f y) ↔ P.Rel (i,x) (j,y) := by
  classical
  refine ⟨?_, P.rel_map f⟩
  intro h
  by_cases hij : i = j
  · subst j
    exact (P.rel_same_copy i x y).2 (hf.injective (((P.map f).rel_same_copy i _ _).1 h))
  · simp only [Rel, hij, ↓reduceIte] at h ⊢
    cases he : P.start i j with
    | none => simp only [map_start, he, Option.map_none] at h
    | some ab =>
      obtain ⟨a,b⟩ := ab
      simp only [map_start, he, Option.map_some] at h
      obtain ⟨t, hx, hy⟩ := h
      obtain ⟨u, hu⟩ := hf.factors a x t hx.symm
      exact ⟨u, hf.injective (by rw [f.map_mul, hu, ← hx]),
        hf.injective (by rw [f.map_mul, hu, ← hy])⟩

/-- Validity of a transported prescription reflects to the old monoid. -/
theorem valid_of_map (P : OverlapPrescription B n) {f : B →* M} (hf : Conservative f)
    (h : (P.map f).Valid) : P.Valid where
  refl _z := (P.rel_map_iff hf _ _ _ _).1 (h.refl _)
  symm {_z _w} hz := (P.rel_map_iff hf _ _ _ _).1 (h.symm (P.rel_map f hz))
  trans {_z _w _v} hzw hwv := (P.rel_map_iff hf _ _ _ _).1
    (h.trans (P.rel_map f hzw) (P.rel_map f hwv))

end PartitionConsistency.DiagramForcing.OverlapPrescription

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u v
open DiagramOrder
variable {B : Type u} {M : Type v} [Monoid B] [Monoid M] {n : ℕ}

theorem rel_start (P : OverlapPrescription B n) {i j : Fin n} (hij : i ≠ j)
    {a b : B} (ho : P.start i j = some (a,b)) : P.Rel (i,a) (j,b) := by
  simp only [Rel, hij, ↓reduceIte, ho]
  exact ⟨1, (mul_one _).symm, (mul_one _).symm⟩

theorem exists_starts_of_rel_map (P : OverlapPrescription B n) (f : B →* M)
    {i j : Fin n} (hij : i ≠ j) {x y : M} (h : (P.map f).Rel (i,x) (j,y)) :
    ∃ a b : B, P.start i j = some (a,b) ∧ ∃ t : M, x = f a * t ∧ y = f b * t := by
  simp only [Rel, hij, ↓reduceIte, map_start] at h
  cases hs : P.start i j with
  | none => simp only [hs, Option.map_none] at h
  | some ab =>
    obtain ⟨a,b⟩ := ab
    exact ⟨a,b,rfl,by simpa only [hs, Option.map_some] using h⟩

end PartitionConsistency.DiagramForcing.OverlapPrescription

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u v
open DiagramOrder
variable {B : Type u} {M : Type v} [LeftCancelMonoid B] [IsConical B]
  [LeftCancelMonoid M] {n : ℕ}

/-- Cone intersections, with their original right quotients, suffice to
transport a *valid* finite prescription. The transitivity check is at the
old join of the two middle-copy starts; it is not a transitive closure of
the transported prescription. Source `lem:mono-simulation`, final assertion. -/
theorem valid_map (P : OverlapPrescription B n) (hP : P.Valid)
    (hB : HasConditionalJoins (LeftDivOrder B)) {f : B →* M} (hf : Conservative f) :
    (P.map f).Valid where
  refl z := ((P.map f).rel_same_copy z.1 z.2 z.2).2 rfl
  symm := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    by_cases hij : i = j
    · subst j
      exact ((P.map f).rel_same_copy i y x).2
        (((P.map f).rel_same_copy i x y).1 h).symm
    · obtain ⟨a,b,hs,t,rfl,rfl⟩ := P.exists_starts_of_rel_map f hij h
      exact (P.map f).rel_mul (P.rel_map f (hP.symm (P.rel_start hij hs))) t
  trans := by
    rintro ⟨i,x⟩ ⟨j,y⟩ ⟨k,z⟩ hxy hyz
    by_cases hij : i = j
    · subst j
      have h := ((P.map f).rel_same_copy i x y).1 hxy
      simpa only [h] using hyz
    by_cases hjk : j = k
    · subst k
      have h := ((P.map f).rel_same_copy j y z).1 hyz
      simpa only [h] using hxy
    obtain ⟨a,b,hs,s,hx,hy⟩ := P.exists_starts_of_rel_map f hij hxy
    obtain ⟨c,d,ht,t,hy',hz⟩ := P.exists_starts_of_rel_map f hjk hyz
    obtain ⟨q,hbq,hcq⟩ := hf.common b c ⟨y,⟨s,hy⟩,⟨t,hy'⟩⟩
    obtain ⟨j₀,hj⟩ := exists_cone_join hB b c q hbq hcq
    obtain ⟨⟨r,hr⟩,⟨u,hu⟩⟩ := (hj j₀).2 (dvd_refl j₀)
    obtain ⟨v,hv⟩ := (hf.intersections b c j₀ hj y).1 ⟨⟨s,hy⟩,⟨t,hy'⟩⟩
    have hs' : s = f r * v := mul_left_cancel (show f b * s = f b * (f r * v) by
      calc f b * s = y := hy.symm
           _ = f j₀ * v := hv
           _ = f b * (f r * v) := by rw [hr, f.map_mul, mul_assoc])
    have ht' : t = f u * v := mul_left_cancel (show f c * t = f c * (f u * v) by
      calc f c * t = y := hy'.symm
           _ = f j₀ * v := hv
           _ = f c * (f u * v) := by rw [hu, f.map_mul, mul_assoc])
    have h1 := P.rel_mul (P.rel_start hij hs) r
    have h2 := P.rel_mul (P.rel_start hjk ht) u
    have hm : b * r = c * u := hr.symm.trans hu
    rw [hm] at h1
    have h3 := (P.map f).rel_mul (P.rel_map f (hP.trans h1 h2)) v
    simpa only [hx, hz, hs', ht', f.map_mul, mul_assoc] using h3

theorem valid_map_iff (P : OverlapPrescription B n)
    (hB : HasConditionalJoins (LeftDivOrder B)) {f : B →* M} (hf : Conservative f) :
    (P.map f).Valid ↔ P.Valid := ⟨P.valid_of_map hf, fun hP => P.valid_map hP hB hf⟩

end PartitionConsistency.DiagramForcing.OverlapPrescription



namespace PartitionConsistency.DiagramOrder.Conservative
universe u v
variable {B : Type u} {M : Type v} [LeftCancelMonoid B] [IsConical B]
  [LeftCancelMonoid M] {f : B →* M} (hf : Conservative f)
include hf

/-- An upper bound in the larger monoid admits an old joint lower bound
of any two specified old divisors. -/
theorem common_below (hB : HasConditionalJoins (LeftDivOrder B))
    {x y : B} {m : M} (hx : f x ∣ m) (hy : f y ∣ m) :
    ∃ j : B, x ∣ j ∧ y ∣ j ∧ f j ∣ m := by
  obtain ⟨a,hxa,hya⟩ := hf.common x y ⟨m,hx,hy⟩
  obtain ⟨j,hj⟩ := exists_cone_join hB x y a hxa hya
  have hu := (hj j).2 (dvd_refl j)
  exact ⟨j,hu.1,hu.2,(hf.intersections x y j hj m).1 ⟨hx,hy⟩⟩

/-- Residual cones of old elements are computed using the same old join
and right quotient even when queried at a new factor. -/
theorem cone_residual (hB : HasConditionalJoins (LeftDivOrder B))
    (x a : B) {t : M} (ht : f x ∣ f a * t) :
    ∃ r : B, (∀ z : B, x ∣ a * z ↔ r ∣ z) ∧
      ∀ z : M, f x ∣ f a * z ↔ f r ∣ z := by
  obtain ⟨q,hxq,haq⟩ := hf.common x a ⟨f a * t,ht,dvd_mul_right _ _⟩
  obtain ⟨j,hj⟩ := exists_cone_join hB x a q hxq haq
  obtain ⟨r,hr⟩ := ((hj j).2 (dvd_refl j)).2
  have hnew : ∀ z : M, f x ∣ f a * z ↔ f r ∣ z := by
    intro z
    calc f x ∣ f a * z ↔ f x ∣ f a * z ∧ f a ∣ f a * z :=
          ⟨fun h => ⟨h,dvd_mul_right _ _⟩,And.left⟩
      _ ↔ f j ∣ f a * z := hf.intersections x a j hj _
      _ ↔ f r ∣ z := by rw [hr,f.map_mul,left_mul_dvd_iff]
  exact ⟨r,fun z => by simpa only [← f.map_mul, hf.dvd_iff] using hnew (f z),hnew⟩
end PartitionConsistency.DiagramOrder.Conservative

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u v
open DiagramOrder MergerAlgebra.RightFreeAction
variable {B : Type u} {M : Type v} [LeftCancelMonoid B] [IsConical B]
  [LeftCancelMonoid M] {n : ℕ}
variable (P : OverlapPrescription B n) (hP : P.Valid)
  (hB : HasConditionalJoins (LeftDivOrder B)) {f : B →* M} (hf : Conservative f)

/-- The genuine copy quotient embeds under conservative base simulation. -/
def copiesMap : P.Copies hP → (P.map f).Copies (P.valid_map hP hB hf) :=
  Quotient.map (fun z : Fin n × B => (z.1, f z.2))
    (fun _ _ h => P.rel_map f h)

@[simp] theorem copiesMap_copy (i : Fin n) (x : B) :
    P.copiesMap hP hB hf (P.copy hP i x) =
      (P.map f).copy (P.valid_map hP hB hf) i (f x) := rfl

theorem copiesMap_injective : Function.Injective (P.copiesMap hP hB hf) := by
  intro z w h
  obtain ⟨⟨i,x⟩,rfl⟩ := Quotient.exists_rep z
  obtain ⟨⟨j,y⟩,rfl⟩ := Quotient.exists_rep w
  exact Quotient.sound ((P.rel_map_iff hf i j x y).1 (Quotient.exact h))

@[simp] theorem copiesMap_act (z : P.Copies hP) (x : B) :
    P.copiesMap hP hB hf (act z x) = act (P.copiesMap hP hB hf z) (f x) := by
  induction z using Quotient.inductionOn with
  | h z =>
    change (P.map f).copy (P.valid_map hP hB hf) z.1 (f (z.2 * x)) =
      (P.map f).copy (P.valid_map hP hB hf) z.1 (f z.2 * f x)
    rw [f.map_mul]

/-- A right factor between smaller-copy elements stays in the old base;
validity alone would not give this assertion. -/
theorem copiesMap_factors (z w : P.Copies hP) (m : M)
    (h : act (P.copiesMap hP hB hf z) m = P.copiesMap hP hB hf w) :
    ∃ a : B, f a = m := by
  obtain ⟨⟨i,x⟩,rfl⟩ := Quotient.exists_rep z
  obtain ⟨⟨j,y⟩,rfl⟩ := Quotient.exists_rep w
  change (P.map f).copy (P.valid_map hP hB hf) i (f x * m) =
    (P.map f).copy (P.valid_map hP hB hf) j (f y) at h
  have hr := ((P.map f).copy_eq_iff (P.valid_map hP hB hf) i j _ _).1 h
  by_cases hij : i = j
  · subst j
    exact hf.factors x y m (((P.map f).rel_same_copy i _ _).1 hr)
  · obtain ⟨a,b,_,t,hx,hy⟩ := P.exists_starts_of_rel_map f hij hr
    obtain ⟨s,hs⟩ := hf.factors b y t hy.symm
    have hm : f x * m = f (a * s) := by rw [f.map_mul,hs,hx]
    exact hf.factors x (a * s) m hm

/-- The finite-overlap cone calculation lifts an old common lower bound
below each larger common upper bound. This proves preservation both of
all old joins and of nonjoins, not just injectivity of the quotient map. -/
theorem copiesMap_common_below (z w : P.Copies hP)
    (c : (P.map f).Copies (P.valid_map hP hB hf))
    (hz : Reaches M (P.copiesMap hP hB hf z) c)
    (hw : Reaches M (P.copiesMap hP hB hf w) c) :
    ∃ j : P.Copies hP, Reaches B z j ∧ Reaches B w j ∧
      Reaches M (P.copiesMap hP hB hf j) c := by
  obtain ⟨⟨i,x⟩,rfl⟩ := Quotient.exists_rep z
  obtain ⟨⟨j,y⟩,rfl⟩ := Quotient.exists_rep w
  obtain ⟨u,hu⟩ := hz
  obtain ⟨v,hv⟩ := hw
  change (P.map f).copy (P.valid_map hP hB hf) i (f x * u) = c at hu
  change (P.map f).copy (P.valid_map hP hB hf) j (f y * v) = c at hv
  by_cases hij : i = j
  · subst j
    have hxy : f x * u = f y * v :=
      (P.map f).copy_injective (P.valid_map hP hB hf) i (hu.trans hv.symm)
    obtain ⟨k,hxk,hyk,t,ht⟩ := hf.common_below hB (dvd_mul_right (f x) u) ⟨v,hxy⟩
    refine ⟨P.copy hP i k,(P.reaches_same_copy_iff hP i x k).2 hxk,
      (P.reaches_same_copy_iff hP i y k).2 hyk,t,?_⟩
    change (P.map f).copy (P.valid_map hP hB hf) i (f k * t) = c
    rw [← ht,hu]
  · have hr := ((P.map f).copy_eq_iff (P.valid_map hP hB hf) i j _ _).1 (hu.trans hv.symm)
    obtain ⟨a,b,hs,t,hxt,hyt⟩ := P.exists_starts_of_rel_map f hij hr
    have hx : f x ∣ f a * t := ⟨u,hxt.symm⟩
    have hy : f y ∣ f b * t := ⟨v,hyt.symm⟩
    obtain ⟨r,hr,hr'⟩ := hf.cone_residual hB x a hx
    obtain ⟨s,hs₀,hs'⟩ := hf.cone_residual hB y b hy
    obtain ⟨k,hrk,hsk,d,hd⟩ := hf.common_below hB ((hr' t).1 hx) ((hs' t).1 hy)
    have hrel : P.copy hP i (a * k) = P.copy hP j (b * k) :=
      (P.copy_eq_iff hP i j _ _).2 (P.rel_mul (P.rel_start hij hs) k)
    refine ⟨P.copy hP i (a * k),(P.reaches_same_copy_iff hP i x _).2 ((hr k).2 hrk),
      ?_,d,?_⟩
    · rw [hrel]
      exact (P.reaches_same_copy_iff hP j y _).2 ((hs₀ k).2 hsk)
    · change (P.map f).copy (P.valid_map hP hB hf) i (f (a * k) * d) = c
      rw [f.map_mul,mul_assoc,← hd,← hxt,hu]

end PartitionConsistency.DiagramForcing.OverlapPrescription

namespace PartitionConsistency.MergerAlgebra.Word
universe u v w z
open DiagramOrder RightFreeAction
variable {B : Type u} {M : Type v} {D : Type w} {E : Type z}
  [Monoid B] [Monoid M]

/-- Simulation on literal merger normal forms, by transporting each
coefficient and each final-letter quotient class. -/
def transport (f : B →* M) (g : D → E) : Word B D → Word M E
  | old x => old (f x)
  | snoc t d => snoc (transport f g t) (g d)

@[simp] theorem transport_old (f : B →* M) (g : D → E) (x : B) :
    transport f g (old x) = old (f x) := rfl
@[simp] theorem transport_snoc (f : B →* M) (g : D → E) (t : Word B D) (d : D) :
    transport f g (snoc t d) = snoc (transport f g t) (g d) := rfl

variable [RightFreeAction B D] [RightFreeAction M E]
  (f : B →* M) (g : D → E)
  (hgact : ∀ d x, g (RightFreeAction.act d x) = RightFreeAction.act (g d) (f x))

include hgact in
@[simp] theorem transport_act (x : Word B D) (a : B) :
    transport f g (act x a) = act (transport f g x) (f a) := by
  cases x with
  | old x => exact congrArg old (f.map_mul x a)
  | snoc x d => exact congrArg (snoc (transport f g x)) (hgact d a)

include hgact in
@[simp] theorem transport_mul (x y : Word B D) :
    transport f g (x * y) = transport f g x * transport f g y := by
  induction y with
  | old a => exact transport_act f g hgact x a
  | snoc y d ih => exact congrArg (snoc · (g d)) ih

def transportHom : Word B D →* Word M E where
  toFun := transport f g
  map_one' := congrArg old f.map_one
  map_mul' := transport_mul f g hgact

@[simp] theorem transportHom_apply (x : Word B D) :
    transportHom f g hgact x = transport f g x := rfl

omit [RightFreeAction B D] [RightFreeAction M E] in
theorem transport_injective (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (transport f g) := by
  intro x
  induction x with
  | old x =>
    intro y he
    cases y with
    | old y => exact congrArg old (hf (Word.old.inj he))
    | snoc y d => cases he
  | snoc x d ih =>
    intro y he
    cases y with
    | old y => cases he
    | snoc y e =>
      obtain ⟨hxy,hde⟩ := Word.snoc.inj he
      exact congrArg₂ snoc (ih hxy) (hg hde)

omit [RightFreeAction B D] in
/-- Right division of two simulated normal forms produces a smaller
normal form. This is stronger than existence of some reflected divisor. -/
theorem transport_factors (hf : Conservative f)
    (hgf : ∀ d e : D, ∀ a : M, RightFreeAction.act (g d) a = g e → ∃ b : B, f b = a)
    (x y : Word B D) (q : Word M E)
    (h : transport f g x * q = transport f g y) :
    ∃ r : Word B D, transport f g r = q := by
  induction y generalizing x q with
  | old y =>
    obtain ⟨a,m,hx,rfl,ham⟩ := factors_of_old h
    cases x with
    | old x =>
      have ha := Word.old.inj hx
      obtain ⟨b,hb⟩ := hf.factors x y m (ha ▸ ham)
      exact ⟨old b,congrArg old hb⟩
    | snoc x d => cases hx
  | snoc y d ih =>
    cases q with
    | old m =>
      cases x with
      | old x => cases h
      | snoc x e =>
        obtain ⟨_,hm⟩ := Word.snoc.inj h
        obtain ⟨b,hb⟩ := hgf e d m hm
        exact ⟨old b,congrArg old hb⟩
    | snoc q e =>
      obtain ⟨hp,he⟩ := Word.snoc.inj h
      obtain ⟨r,hr⟩ := ih x q hp
      exact ⟨snoc r d,congrArg₂ snoc hr he.symm⟩

include hgact in
theorem transport_dvd_iff (hf : Conservative f) (hg : Function.Injective g)
    (hgf : ∀ d e : D, ∀ a : M, RightFreeAction.act (g d) a = g e → ∃ b : B, f b = a)
    (x y : Word B D) : transport f g x ∣ transport f g y ↔ x ∣ y := by
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨r,hr⟩ := transport_factors f g hf hgf x y q hq.symm
    refine ⟨r,transport_injective f g hf.injective hg ?_⟩
    rw [transport_mul f g hgact,hr,hq]
  · exact (transportHom f g hgact).map_dvd

end PartitionConsistency.MergerAlgebra.Word

namespace PartitionConsistency.MergerAlgebra.Word
universe u v w z
open DiagramOrder RightFreeAction
variable {B : Type u} {M : Type v} {D : Type w} {E : Type z}
  [LeftCancelMonoid B] [IsConical B] [LeftCancelMonoid M]
  [RightFreeAction B D] [RightFreeAction M E]
variable (hB : HasConditionalJoins (LeftDivOrder B))
  (f : B →* M) (g : D → E)
  (hgact : ∀ d x, g (RightFreeAction.act d x) = RightFreeAction.act (g d) (f x))
  (hf : Conservative f) (hg : Function.Injective g)
  (hgf : ∀ d e : D, ∀ a : M, RightFreeAction.act (g d) a = g e → ∃ b : B, f b = a)
  (hgc : ∀ d e : D, ∀ c : E, Reaches M (g d) c → Reaches M (g e) c →
    ∃ j : D, Reaches B d j ∧ Reaches B e j ∧ Reaches M (g j) c)

include hB hgact hf hg hgf hgc

/-- Joint lower bounds of old divisors are lifted by induction on the
literal larger upper bound. At unequal lengths the comparison reflects
by right-factor conservation; at equal lengths the final-letter cone
calculation controls the intersection. -/
theorem transport_common_below (x y : Word B D) (c : Word M E)
    (hx : transport f g x ∣ c) (hy : transport f g y ∣ c) :
    ∃ j : Word B D, x ∣ j ∧ y ∣ j ∧ transport f g j ∣ c := by
  induction c generalizing x y with
  | old m =>
    cases x with
    | snoc x d => exact (snoc_not_dvd_old _ _ _ hx).elim
    | old x =>
      cases y with
      | snoc y d => exact (snoc_not_dvd_old _ _ _ hy).elim
      | old y =>
        obtain ⟨j,hxj,hyj,hjm⟩ := hf.common_below hB
          ((old_dvd_iff (f x) (old m)).1 hx) ((old_dvd_iff (f y) (old m)).1 hy)
        exact ⟨old j,(oldHom : B →* Word B D).map_dvd hxj,
          (oldHom : B →* Word B D).map_dvd hyj,(old_dvd_iff (f j) (old m)).2 hjm⟩
  | snoc c d ih =>
    rcases (dvd_snoc_iff (transport f g x) c d).1 hx with hxc | ⟨dx,hxe,hxd⟩
    · rcases (dvd_snoc_iff (transport f g y) c d).1 hy with hyc | ⟨dy,hye,_⟩
      · obtain ⟨j,hxj,hyj,hjc⟩ := ih x y hxc hyc
        exact ⟨j,hxj,hyj,(dvd_snoc_iff _ _ _).2 (Or.inl hjc)⟩
      · have hxy : transport f g x ∣ transport f g y := by
          rw [hye]
          exact (dvd_snoc_iff _ _ _).2 (Or.inl hxc)
        exact ⟨y,(transport_dvd_iff f g hgact hf hg hgf x y).1 hxy,dvd_refl y,hy⟩
    · rcases (dvd_snoc_iff (transport f g y) c d).1 hy with hyc | ⟨dy,hye,hyd⟩
      · have hyx : transport f g y ∣ transport f g x := by
          rw [hxe]
          exact (dvd_snoc_iff _ _ _).2 (Or.inl hyc)
        exact ⟨x,dvd_refl x,(transport_dvd_iff f g hgact hf hg hgf y x).1 hyx,hx⟩
      · cases x with
        | old x => cases hxe
        | snoc x a =>
          cases y with
          | old y => cases hye
          | snoc y b =>
            obtain ⟨hxc,hax⟩ := Word.snoc.inj hxe
            obtain ⟨hyc,hby⟩ := Word.snoc.inj hye
            have hxy := transport_injective f g hf.injective hg (hxc.trans hyc.symm)
            subst y
            obtain ⟨j,haj,hbj,hjd⟩ := hgc a b d (hax ▸ hxd) (hby ▸ hyd)
            refine ⟨snoc x j,(snoc_dvd_snoc_iff _ _ _ _).2 (Or.inr ⟨rfl,haj⟩),
              (snoc_dvd_snoc_iff _ _ _ _).2 (Or.inr ⟨rfl,hbj⟩),?_⟩
            change snoc (transport f g x) (g j) ∣ snoc c d
            rw [hxc]
            exact (snoc_dvd_snoc_iff _ _ _ _).2 (Or.inr ⟨rfl,hjd⟩)

/-- The entire merger normal-form simulation is conservative. -/
theorem transport_conservative : Conservative (transportHom f g hgact) where
  injective := transport_injective f g hf.injective hg
  factors := transport_factors f g hf hgf
  intersections x y j hj c := by
    constructor
    · rintro ⟨hx,hy⟩
      obtain ⟨k,hxk,hyk,hkc⟩ := transport_common_below hB f g hgact hf hg hgf hgc x y c hx hy
      exact ((transportHom f g hgact).map_dvd ((hj k).1 ⟨hxk,hyk⟩)).trans hkc
    · intro h
      have hu := (hj j).2 (dvd_refl j)
      exact ⟨((transportHom f g hgact).map_dvd hu.1).trans h,
        ((transportHom f g hgact).map_dvd hu.2).trans h⟩
  common x y h := by
    obtain ⟨c,hx,hy⟩ := h
    obtain ⟨j,hxj,hyj,_⟩ := transport_common_below hB f g hgact hf hg hgf hgc x y c hx hy
    exact ⟨j,hxj,hyj⟩

end PartitionConsistency.MergerAlgebra.Word

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u v
open DiagramOrder MergerAlgebra
variable {B : Type u} {M : Type v} [LeftCancelMonoid B] [IsConical B]
  [LeftCancelMonoid M] {n : ℕ}
variable (P : OverlapPrescription B n) (hP : P.Valid)
  (hB : HasConditionalJoins (LeftDivOrder B)) {f : B →* M} (hf : Conservative f)

/-- Simulate exactly the smaller merger presentation in the larger base,
using the same prescribed overlap starts. -/
def mergerSimulation : Word B (P.Copies hP) →*
    Word M ((P.map f).Copies (P.valid_map hP hB hf)) :=
  Word.transportHom f (P.copiesMap hP hB hf) (P.copiesMap_act hP hB hf)

/-- Merger case of source `lem:mono-simulation`: the induced homomorphism
is conservative, including old factors, all cone intersections, and nonjoins. -/
theorem mergerSimulation_conservative : Conservative (P.mergerSimulation hP hB hf) :=
  Word.transport_conservative hB f (P.copiesMap hP hB hf) (P.copiesMap_act hP hB hf)
    hf (P.copiesMap_injective hP hB hf) (P.copiesMap_factors hP hB hf)
    (P.copiesMap_common_below hP hB hf)

@[simp] theorem mergerSimulation_old (x : B) :
    P.mergerSimulation hP hB hf (Word.old x) = Word.old (f x) := rfl

@[simp] theorem mergerSimulation_snoc (x : Word B (P.Copies hP)) (i : Fin n) (a : B) :
    P.mergerSimulation hP hB hf (Word.snoc x (P.copy hP i a)) =
      Word.snoc (P.mergerSimulation hP hB hf x)
        ((P.map f).copy (P.valid_map hP hB hf) i (f a)) := rfl

end PartitionConsistency.DiagramForcing.OverlapPrescription

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Algebra_ProbePresentations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency.ProbeAlgebra.Path
universe u v
open DiagramOrder
variable {B : Type u} {M : Type v} [LeftCancelMonoid B] [LeftCancelMonoid M]
  {a : B} (P : Path B a) (f : B →* M)

/-- The same countable probe presentation over the larger base. -/
def map : Path M (f a) where
  node i := f (P.node i)
  zero := by rw [P.zero, f.map_one]
  increasing h := f.map_dvd (P.increasing h)
  bounded i := f.map_dvd (P.bounded i)

@[simp] theorem map_node (i : ℕ) : (P.map f).node i = f (P.node i) := rfl

@[simp] theorem map_factor (i j : ℕ) (h : i ≤ j) :
    (P.map f).factor i j h = f (P.factor i j h) := by
  apply mul_left_cancel (a := f (P.node i))
  calc
    f (P.node i) * (P.map f).factor i j h = f (P.node j) := (P.map f).node_factor i j h
    _ = f (P.node i * P.factor i j h) := congrArg f (P.node_factor i j h).symm
    _ = f (P.node i) * f (P.factor i j h) := f.map_mul _ _

@[simp] theorem map_terminal (i : ℕ) :
    (P.map f).terminal i = f (P.terminal i) := by
  apply mul_left_cancel (a := f (P.node i))
  calc
    f (P.node i) * (P.map f).terminal i = f a := (P.map f).node_terminal i
    _ = f (P.node i * P.terminal i) := congrArg f (P.node_terminal i).symm
    _ = f (P.node i) * f (P.terminal i) := f.map_mul _ _

/-- Map the actual, potentially non-injective direct limits. -/
noncomputable def lettersMap : P.Letters → (P.map f).Letters :=
  DirectLimit.map P.transition (P.map f).transition (fun _ => f)
    (fun i j hij x => by simp only [transition_apply, map_factor, f.map_mul])

@[simp] theorem lettersMap_letter (i : ℕ) (x : B) :
    P.lettersMap f (P.letter i x) = (P.map f).letter i (f x) := rfl

include P in
/-- Reflection is tested at a common finite stage, not by cancellation
of the (possibly non-injective) transition maps. -/
theorem lettersMap_injective (hf : Function.Injective f) :
    Function.Injective (P.lettersMap f) := by
  intro s t he
  obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk P.transition s
  obtain ⟨j,y,rfl⟩ := DirectLimit.exists_eq_mk P.transition t
  obtain ⟨k,hi,hj,hk⟩ := ((P.map f).letter_eq_iff i j (f x) (f y)).1 he
  apply (P.letter_eq_iff i j x y).2
  refine ⟨k,hi,hj,hf ?_⟩
  simpa only [map_factor, ← f.map_mul] using hk

@[simp] theorem lettersMap_act (x : B) (s : P.Letters) :
    P.lettersMap f (P.act x s) = (P.map f).act (f x) (P.lettersMap f s) := by
  induction s using DirectLimit.induction with
  | ih i y =>
    change (P.map f).letter i (f (x * y)) = (P.map f).letter i (f x * f y)
    rw [f.map_mul]

@[simp] theorem lettersMap_exit (e : B) (s : P.Letters) :
    (P.map f).exit (f e) (P.lettersMap f s) = f (P.exit e s) := by
  induction s using DirectLimit.induction with
  | ih i y =>
    change (P.map f).exit (f e) (P.lettersMap f (P.letter i y)) = f (P.exit e (P.letter i y))
    simp only [lettersMap_letter, exit, target_letter, map_terminal, f.map_mul]

/-- Smaller-letter divisibility is reflected with its exact quotient:
a larger-stage witness can be pulled back by old-factor conservation. -/
theorem lettersMap_inCone_iff (hf : Conservative f) (x : B) (s : P.Letters) :
    (P.map f).InCone (f x) (P.lettersMap f s) ↔ P.InCone x s := by
  induction s using DirectLimit.induction with
  | ih i y =>
    change (P.map f).InCone (f x) ((P.map f).letter i (f y)) ↔ P.InCone x (P.letter i y)
    simp only [inCone_letter_iff, map_factor, ← f.map_mul, hf.dvd_iff]

end PartitionConsistency.ProbeAlgebra.Path

namespace PartitionConsistency.ProbeAlgebra
universe u v w z
open DiagramOrder

/-- A map of probe alphabets whose old divisibility tests are unchanged.
All these laws will be proved for the path direct limits; no assumptions
about joins between new words or their gates enter this definition. -/
structure AlphabetSimulation {B : Type u} {M : Type v} {S : Type w} {T : Type z}
    [LeftCancelMonoid B] [LeftCancelMonoid M]
    (A : Alphabet B S) (C : Alphabet M T) (f : B →* M) (g : S → T) : Prop where
  injective : Function.Injective g
  act : ∀ x s, g (A.act x s) = C.act (f x) (g s)
  exit : ∀ s, C.exit (g s) = f (A.exit s)
  cones : ∀ x s, (∃ t : T, C.act (f x) t = g s) ↔ ∃ t : S, A.act x t = s

namespace Path
variable {B : Type u} {M : Type v} [LeftCancelMonoid B] [IsConical B]
  [LeftCancelMonoid M] [IsConical M] {a e : B} (P : Path B a) (he : e ≠ 1)
  {f : B →* M} (hf : Conservative f)

/-- A conservative map of bases supplies an alphabet simulation for the
same generators and terminal parameter. -/
theorem alphabetSimulation : AlphabetSimulation (P.alphabet he)
    ((P.map f).alphabet (fun h => he (hf.injective (h.trans f.map_one.symm)))) f
    (P.lettersMap f) where
  injective := P.lettersMap_injective f hf.injective
  act := P.lettersMap_act f
  exit := P.lettersMap_exit f e
  cones := P.lettersMap_inCone_iff f hf

end Path

namespace Raw
variable {B : Type u} {M : Type v} {S : Type w} {T : Type z}

/-- Simulation on literal strings. Reducedness will be proved, not
postulated or hidden in a quotient of these words. -/
def transport (f : B → M) (g : S → T) : Raw B S → Raw M T
  | old x => old (f x)
  | cons s w => cons (g s) (transport f g w)

@[simp] theorem transport_old (f : B → M) (g : S → T) (x : B) :
    transport f g (old x) = old (f x) := rfl
@[simp] theorem transport_cons (f : B → M) (g : S → T) (s : S) (x : Raw B S) :
    transport f g (cons s x) = cons (g s) (transport f g x) := rfl

theorem transport_injective {f : B → M} {g : S → T}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (transport f g) := by
  intro x
  induction x with
  | old x =>
    intro y he
    cases y with
    | old y => exact congrArg old (hf (Raw.old.inj he))
    | cons s y => cases he
  | cons s x ih =>
    intro y he
    cases y with
    | old y => cases he
    | cons t y =>
      obtain ⟨hst,hxy⟩ := Raw.cons.inj he
      exact congrArg₂ cons (hg hst) (ih hxy)

variable [LeftCancelMonoid B] [LeftCancelMonoid M]
  {A : Alphabet B S} {C : Alphabet M T} {f : B →* M} {g : S → T}
  (hf : Conservative f) (hg : AlphabetSimulation A C f g)

include hf hg in
@[simp] theorem headDiv_transport (x : B) (y : Raw B S) :
    (transport f g y).headDiv C (f x) ↔ y.headDiv A x := by
  cases y with
  | old y => exact hf.dvd_iff x y
  | cons s y => exact hg.cones x s

include hf hg in
@[simp] theorem reduced_transport (b : B) (y : Raw B S) :
    (transport f g y).reduced C (f b) ↔ y.reduced A b := by
  induction y with
  | old y => rfl
  | cons s y ih =>
    change ((transport f g y).reduced C (f b) ∧ ¬ (transport f g y).headDiv C (f b)) ↔ _
    rw [ih,headDiv_transport hf hg]
    rfl

include hg in
@[simp] theorem transport_oldAct (x : B) (y : Raw B S) :
    transport f g (oldAct A x y) = oldAct C (f x) (transport f g y) := by
  cases y with
  | old y => exact congrArg old (f.map_mul x y)
  | cons s y => exact congrArg (cons · (transport f g y)) (hg.act x s)

end Raw

namespace Word
variable {B : Type u} {M : Type v} {S : Type w} {T : Type z}
  [LeftCancelMonoid B] [LeftCancelMonoid M]
  {A : Alphabet B S} {C : Alphabet M T} {f : B →* M} {g : S → T}
  (hf : Conservative f) (hg : AlphabetSimulation A C f g) (b : B)

/-- Smaller irreducible words remain irreducible in the larger presentation. -/
def transport (y : Word A b) : Word C (f b) :=
  ⟨Raw.transport f g y.val, (Raw.reduced_transport hf hg b y.val).2 y.property⟩

@[simp] theorem transport_old (x : B) :
    transport hf hg b (old A b x) = old C (f b) (f x) := rfl

@[simp] theorem transport_cons (s : S) (y : Word A b) (hy) :
    transport hf hg b (cons A b s y hy) =
      cons C (f b) (g s) (transport hf hg b y)
        (fun h => hy ((Raw.headDiv_transport hf hg b y.val).1 h)) := rfl

@[simp] theorem head_transport (y : Word A b) :
    head C (f b) (transport hf hg b y) = (head A b y).map g := by
  obtain ⟨y,hy⟩ := y
  cases y <;> rfl

@[simp] theorem headDiv_transport (x : B) (y : Word A b) :
    headDiv C (f b) (f x) (transport hf hg b y) ↔ headDiv A b x y :=
  Raw.headDiv_transport hf hg x y.val

theorem transport_injective : Function.Injective (transport hf hg b) :=
  fun _ _ h => Subtype.ext (Raw.transport_injective hf.injective hg.injective
    (congrArg Subtype.val h))

@[simp] theorem transport_oldAct (x : B) (y : Word A b) :
    transport hf hg b (oldAct A b x y) = oldAct C (f b) (f x) (transport hf hg b y) :=
  Subtype.ext (Raw.transport_oldAct hg x y.val)

@[simp] theorem transport_quotient (x : B) (y : Word A b) (hy) :
    transport hf hg b (quotient A b x y hy) =
      quotient C (f b) (f x) (transport hf hg b y)
        ((headDiv_transport hf hg b x y).2 hy) := by
  apply oldAct_injective C (f b) (f x)
  rw [← transport_oldAct, oldAct_quotient, oldAct_quotient]

@[simp] theorem transport_letterAct (s : S) (y : Word A b) :
    transport hf hg b (letterAct A b s y) =
      letterAct C (f b) (g s) (transport hf hg b y) := by
  classical
  by_cases hy : headDiv A b b y
  · rw [letterAct_of_headDiv A b s y hy,
      letterAct_of_headDiv C (f b) (g s) _ ((headDiv_transport hf hg b b y).2 hy),
      transport_oldAct,transport_quotient,hg.exit]
  · rw [letterAct_of_not_headDiv A b s y hy,
      letterAct_of_not_headDiv C (f b) (g s) _
        (fun h => hy ((headDiv_transport hf hg b b y).1 h)),transport_cons]

@[simp] theorem transport_mul (x y : Word A b) :
    transport hf hg b (x * y) = transport hf hg b x * transport hf hg b y := by
  obtain ⟨x,hx⟩ := x
  induction x with
  | old x => exact transport_oldAct hf hg b x y
  | cons s x ih =>
    change x.reduced A b ∧ ¬ x.headDiv A b at hx
    change transport hf hg b (letterAct A b s (⟨x,hx.1⟩ * y)) =
      letterAct C (f b) (g s) (transport hf hg b ⟨x,hx.1⟩ * transport hf hg b y)
    rw [transport_letterAct,ih hx.1]

/-- The literal normal-form embedding respects the defining reductions. -/
def transportHom : Word A b →* Word C (f b) where
  toFun := transport hf hg b
  map_one' := congrArg (old C (f b)) f.map_one
  map_mul' := transport_mul hf hg b

@[simp] theorem transportHom_apply (x : Word A b) :
    transportHom hf hg b x = transport hf hg b x := rfl

theorem old_dvd_transport_iff (x : B) (y : Word A b) :
    old C (f b) (f x) ∣ transport hf hg b y ↔ old A b x ∣ y := by
  rw [old_dvd_iff_headDiv,headDiv_transport,old_dvd_iff_headDiv]

end Word
end PartitionConsistency.ProbeAlgebra

namespace PartitionConsistency.ProbeAlgebra.Word
universe u v w z
open DiagramOrder
variable {B : Type u} {M : Type v} {S : Type w} {T : Type z}
  [LeftCancelMonoid B] [IsConical B] [LeftCancelMonoid M]
  {A : Alphabet B S} {C : Alphabet M T} {f : B →* M} {g : S → T}
  (hf : Conservative f) (hg : AlphabetSimulation A C f g) (b : B)
  (hB : HasConditionalJoins (LeftDivOrder B))
  (hA : Conservative (oldHom A b)) (hC : Conservative (oldHom C (f b)))

include hf hB hA hC in
/-- The old intersection used in the gate recursion is the same on both
sides, including its original right quotients. -/
theorem simulated_old_intersection (x y : B) (q : Word C (f b))
    (hx : old C (f b) (f x) ∣ q) (hy : old C (f b) (f y) ∣ q) :
    ∃ j : B, (∀ v : Word A b, old A b x ∣ v ∧ old A b y ∣ v ↔ old A b j ∣ v) ∧
      ∀ v : Word C (f b), old C (f b) (f x) ∣ v ∧ old C (f b) (f y) ∣ v ↔
        old C (f b) (f j) ∣ v := by
  obtain ⟨m,hxm,hym⟩ := (hf.comp hC).common x y ⟨q,hx,hy⟩
  obtain ⟨j,hj⟩ := exists_cone_join hB x y m hxm hym
  exact ⟨j,hA.intersections x y j hj,(hf.comp hC).intersections x y j hj⟩

include hB hA hC in
/-- An exit in the larger presentation determines exactly the same old
gate in both presentations. Induction computes gates using the transported
old joins; the existence/nonexistence of a gate is not an assumption. -/
theorem exists_simulated_gate_of_exit (x : Word A b) {s : S}
    (hx : head A b x = some s) {q : Word C (f b)}
    (hxq : transport hf hg b x ∣ q) (hq : head C (f b) q ≠ some (g s)) :
    ∃ j : B, Gate A b x s j ∧ Gate C (f b) (transport hf hg b x) (g s) (f j) := by
  obtain ⟨x,hxred⟩ := x
  induction x generalizing s q with
  | old x => cases hx
  | cons t Y ih =>
    have hts : t = s := Option.some.inj hx
    subst t
    change Y.reduced A b ∧ ¬ Y.headDiv A b at hxred
    let Y' : Word A b := ⟨Y,hxred.1⟩
    obtain ⟨v,hv⟩ := hxq
    have hbyv : old C (f b) (f b) ∣ transport hf hg b Y' * v := by
      apply (old_dvd_iff_headDiv C (f b) (f b) _).2
      apply (head_letterAct_ne_iff C (f b) (g s) _).1
      exact (congrArg (head C (f b)) hv) ▸ hq
    have hInt : ∃ j : B,
        (∀ w : Word A b, Y' ∣ w ∧ old A b b ∣ w ↔ old A b j ∣ w) ∧
        ∀ w : Word C (f b), transport hf hg b Y' ∣ w ∧ old C (f b) (f b) ∣ w ↔
          old C (f b) (f j) ∣ w := by
      cases heY : Y with
      | old y =>
        have hYeq : Y' = old A b y := Subtype.ext heY
        rw [hYeq] at ⊢ hbyv
        exact simulated_old_intersection hf b hB hA hC y b
          (transport hf hg b (old A b y) * v) (dvd_mul_right _ _) hbyv
      | cons t Z =>
        have hYhead : head A b Y' = some t := by change Y.head = some t; rw [heY]; rfl
        have hThead : head C (f b) (transport hf hg b Y') = some (g t) := by
          rw [head_transport,hYhead]; rfl
        have hbnY : ¬ headDiv C (f b) (f b) (transport hf hg b Y') :=
          fun h => hxred.2 ((headDiv_transport hf hg b b Y').1 h)
        have hex : head C (f b) (transport hf hg b Y' * v) ≠ some (g t) := by
          intro hh
          exact hbnY ((headDiv_of_same_head C (f b) hThead hh).2
            ((old_dvd_iff_headDiv C (f b) (f b) _).1 hbyv))
        obtain ⟨k,hk,hk'⟩ := ih hex hxred.1 hYhead (dvd_mul_right _ _)
        obtain ⟨j,hj,hj'⟩ := simulated_old_intersection hf b hB hA hC k b
          (transport hf hg b Y' * v) ((hk' _).1 ⟨dvd_mul_right _ _,hex⟩) hbyv
        refine ⟨j,fun w => ?_,fun w => ?_⟩
        · calc
            Y' ∣ w ∧ old A b b ∣ w ↔ old A b b ∣ w ∧ Y' ∣ w := and_comm
            _ ↔ old A b b ∣ w ∧ old A b k ∣ w := Gate.old_intersection A b hk hYhead hxred.2 w
            _ ↔ old A b k ∣ w ∧ old A b b ∣ w := and_comm
            _ ↔ old A b j ∣ w := hj w
        · calc
            transport hf hg b Y' ∣ w ∧ old C (f b) (f b) ∣ w ↔
                old C (f b) (f b) ∣ w ∧ transport hf hg b Y' ∣ w := and_comm
            _ ↔ old C (f b) (f b) ∣ w ∧ old C (f b) (f k) ∣ w :=
                Gate.old_intersection C (f b) hk' hThead hbnY w
            _ ↔ old C (f b) (f k) ∣ w ∧ old C (f b) (f b) ∣ w := and_comm
            _ ↔ old C (f b) (f j) ∣ w := hj' w
    obtain ⟨j,hj,hj'⟩ := hInt
    have hbj : b ∣ j :=
      (old_dvd_old_iff A b b j).1 (((hj _).2 (dvd_refl _)).2)
    obtain ⟨u,rfl⟩ := hbj
    refine ⟨A.exit s * u,gate_of_suffix_intersection A b s Y' hxred.2 u hj,?_⟩
    have hY' : ¬ headDiv C (f b) (f b) (transport hf hg b Y') :=
      fun h => hxred.2 ((headDiv_transport hf hg b b Y').1 h)
    have h := gate_of_suffix_intersection C (f b) (g s) (transport hf hg b Y') hY' (f u)
      (fun w => by simpa only [f.map_mul] using hj' w)
    change Gate C (f b) (cons C (f b) (g s) (transport hf hg b Y') hY') (g s)
      (f (A.exit s * u))
    simpa only [hg.exit,f.map_mul] using h

end PartitionConsistency.ProbeAlgebra.Word

namespace PartitionConsistency.ProbeAlgebra.Word
universe u v w z
open DiagramOrder
variable {B : Type u} {M : Type v} {S : Type w} {T : Type z}
  [LeftCancelMonoid B] [IsConical B] [LeftCancelMonoid M]
  {A : Alphabet B S} {C : Alphabet M T} {f : B →* M} {g : S → T}
  (hf : Conservative f) (hg : AlphabetSimulation A C f g) (b : B)

omit [IsConical B] in
@[simp] theorem head_transport_eq_some (x : Word A b) (s : S) :
    head C (f b) (transport hf hg b x) = some (g s) ↔ head A b x = some s := by
  rw [head_transport]
  cases he : head A b x with
  | none => simp
  | some t => simp only [Option.map_some, Option.some.injEq, hg.injective.eq_iff]

omit [IsConical B] in
/-- Once a comparison reflects, cancellation reflects its particular
factor, not just the existence of some factor. -/
theorem transport_factor_of_dvd (x y : Word A b) (q : Word C (f b))
    (h : transport hf hg b x * q = transport hf hg b y) (hxy : x ∣ y) :
    ∃ r : Word A b, transport hf hg b r = q := by
  obtain ⟨r,hr⟩ := hxy
  refine ⟨r,mul_left_cancel (a := transport hf hg b x) ?_⟩
  calc
    transport hf hg b x * transport hf hg b r = transport hf hg b (x * r) :=
      (transport_mul hf hg b x r).symm
    _ = transport hf hg b y := congrArg (transport hf hg b) hr.symm
    _ = transport hf hg b x * q := h.symm

variable (hB : HasConditionalJoins (LeftDivOrder B))
  (hA : Conservative (oldHom A b)) (hC : Conservative (oldHom C (f b)))

include hB hA hC in
/-- Source `lem:mono-simulation`, separate division argument for probes.
Old heads use letter-cone reflection; equal new heads cancel; an exit
factors through the shared old gate furnished by the gate recursion. -/
theorem transport_factors (x y : Word A b) (q : Word C (f b))
    (h : transport hf hg b x * q = transport hf hg b y) :
    ∃ r : Word A b, transport hf hg b r = q := by
  obtain ⟨x,hx⟩ := x
  induction x generalizing y q with
  | old x =>
    exact transport_factor_of_dvd hf hg b (old A b x) y q h
      ((old_dvd_transport_iff hf hg b x y).1 ⟨q,h.symm⟩)
  | cons s Y ih =>
    change Y.reduced A b ∧ ¬ Y.headDiv A b at hx
    let Y' : Word A b := ⟨Y,hx.1⟩
    change transport hf hg b (cons A b s Y' hx.2) * q = transport hf hg b y at h
    by_cases hys : head C (f b) (transport hf hg b y) = some (g s)
    · obtain ⟨Z,hZ,rfl⟩ := (head_eq_some_iff A b y s).1
        ((head_transport_eq_some hf hg b y s).1 hys)
      have hZ' : ¬ headDiv C (f b) (f b) (transport hf hg b Z) :=
        fun hh => hZ ((headDiv_transport hf hg b b Z).1 hh)
      have he : transport hf hg b Y' * q = transport hf hg b Z := by
        apply letterAct_injective C (f b) (g s)
        calc
          letterAct C (f b) (g s) (transport hf hg b Y' * q) =
              transport hf hg b (cons A b s Z hZ) := h
          _ = letterAct C (f b) (g s) (transport hf hg b Z) :=
            (letterAct_of_not_headDiv C (f b) (g s) _ hZ').symm
      exact ih Z q hx.1 he
    · obtain ⟨j,hj,hj'⟩ := exists_simulated_gate_of_exit hf hg b hB hA hC
        (cons A b s Y' hx.2) rfl ⟨q,h.symm⟩ hys
      have hjy : old A b j ∣ y := (old_dvd_transport_iff hf hg b j y).1
        ((hj' _).1 ⟨⟨q,h.symm⟩,hys⟩)
      exact transport_factor_of_dvd hf hg b (cons A b s Y' hx.2) y q h
        ((Gate.dvd A b hj).trans hjy)

end PartitionConsistency.ProbeAlgebra.Word

namespace PartitionConsistency.ProbeAlgebra.Word
universe u v w z
open DiagramOrder
variable {B : Type u} {M : Type v} {S : Type w} {T : Type z}
  [LeftCancelMonoid B] [IsConical B] [LeftCancelMonoid M] [IsConical M]
  {A : Alphabet B S} {C : Alphabet M T} {f : B →* M} {g : S → T}
  (hf : Conservative f) (hg : AlphabetSimulation A C f g) (b : B) (hb : b ≠ 1)

@[simp] theorem transport_generator (s : S) :
    transport hf hg b (generator A b hb s) =
      generator C (f b) (fun h => hb (hf.injective (h.trans f.map_one.symm))) (g s) := by
  apply Subtype.ext
  change Raw.cons (g s) (Raw.old (f 1)) = Raw.cons (g s) (Raw.old 1)
  rw [f.map_one]

variable (hB : HasConditionalJoins (LeftDivOrder B))
  (hA : Conservative (oldHom A b)) (hC : Conservative (oldHom C (f b)))

include hB hA hC in
omit [IsConical M] in
/-- An old/new common upper bound in the larger extension lies above a
smaller common upper bound. The latter is the new word itself, or is old
and obtained by joining its shared gate with the old divisor. -/
theorem transport_old_common_below (x : B) (y : Word A b) (q : Word C (f b))
    (hx : old C (f b) (f x) ∣ q) (hy : transport hf hg b y ∣ q) :
    ∃ j : Word A b, old A b x ∣ j ∧ y ∣ j ∧ transport hf hg b j ∣ q := by
  classical
  by_cases hxy : old A b x ∣ y
  · exact ⟨y,hxy,dvd_refl y,hy⟩
  cases he : head A b y with
  | none =>
    obtain ⟨a,rfl⟩ := (head_eq_none_iff A b y).1 he
    obtain ⟨j,hxj,haj,hjq⟩ := (hf.comp hC).common_below hB hx hy
    exact ⟨old A b j,(oldHom A b).map_dvd hxj,(oldHom A b).map_dvd haj,hjq⟩
  | some s =>
    have hys : head C (f b) (transport hf hg b y) = some (g s) :=
      (head_transport_eq_some hf hg b y s).2 he
    have hq : head C (f b) q ≠ some (g s) := by
      intro hqs
      exact hxy ((old_dvd_transport_iff hf hg b x y).1
        ((old_dvd_iff_headDiv C (f b) (f x) _).2
          ((headDiv_of_same_head C (f b) hys hqs).2
            ((old_dvd_iff_headDiv C (f b) (f x) _).1 hx))))
    obtain ⟨k,hk,hk'⟩ := exists_simulated_gate_of_exit hf hg b hB hA hC y he hy hq
    obtain ⟨j,hxj,hkj,hjq⟩ := (hf.comp hC).common_below hB hx ((hk' q).1 ⟨hy,hq⟩)
    exact ⟨old A b j,(oldHom A b).map_dvd hxj,
      (Gate.dvd A b hk).trans ((oldHom A b).map_dvd hkj),hjq⟩

include hB hA hC in
omit [IsConical M] in
/-- A larger common multiple in one smaller first-letter block puts the
other, differently headed smaller divisor below the entire smaller block. -/
theorem transport_dvd_of_different_head {x y : Word A b} {s t : S}
    (hx : head A b x = some s) (hy : head A b y = some t) (hst : s ≠ t)
    {q : Word C (f b)} (hyq : transport hf hg b y ∣ q)
    (hq : head C (f b) q = some (g s)) : y ∣ x := by
  have hqt : head C (f b) q ≠ some (g t) := by
    rw [hq]
    exact fun h => hst (hg.injective (Option.some.inj h))
  obtain ⟨j,hj,hj'⟩ := exists_simulated_gate_of_exit hf hg b hB hA hC y hy hyq hqt
  have hjx : old A b j ∣ x := (old_dvd_transport_iff hf hg b j x).1
    ((old_dvd_iff_headDiv C (f b) (f j) _).2
      ((headDiv_of_same_head C (f b) ((head_transport_eq_some hf hg b x s).2 hx) hq).2
        ((old_dvd_iff_headDiv C (f b) (f j) _).1 ((hj' q).1 ⟨hyq,hqt⟩))))
  exact (Gate.dvd A b hj).trans hjx

include hb hB hA hC in
/-- Every larger common upper bound of two simulated words lies above a
smaller common upper bound. This simultaneously conserves joins and the
absence of joins, rather than just comparisons between simulated words. -/
theorem transport_common_below (x y : Word A b) (q : Word C (f b))
    (hxq : transport hf hg b x ∣ q) (hyq : transport hf hg b y ∣ q) :
    ∃ j : Word A b, x ∣ j ∧ y ∣ j ∧ transport hf hg b j ∣ q := by
  classical
  obtain ⟨x,hx⟩ := x
  induction x generalizing y q with
  | old x => exact transport_old_common_below hf hg b hB hA hC x y q hxq hyq
  | cons s Y ih =>
    change Y.reduced A b ∧ ¬ Y.headDiv A b at hx
    let Y' : Word A b := ⟨Y,hx.1⟩
    change transport hf hg b (cons A b s Y' hx.2) ∣ q at hxq
    change ∃ j, cons A b s Y' hx.2 ∣ j ∧ y ∣ j ∧ transport hf hg b j ∣ q
    obtain ⟨y,hy⟩ := y
    cases y with
    | old y =>
      obtain ⟨j,hyj,hxj,hjq⟩ := transport_old_common_below hf hg b hB hA hC
        y (cons A b s Y' hx.2) q hyq hxq
      exact ⟨j,hxj,hyj,hjq⟩
    | cons t Z =>
      change Z.reduced A b ∧ ¬ Z.headDiv A b at hy
      let Z' : Word A b := ⟨Z,hy.1⟩
      change transport hf hg b (cons A b t Z' hy.2) ∣ q at hyq
      change ∃ j, cons A b s Y' hx.2 ∣ j ∧ cons A b t Z' hy.2 ∣ j ∧ transport hf hg b j ∣ q
      by_cases hst : s = t
      · subst t
        let c := generator A b hb s
        let c' := generator C (f b) (fun h => hb (hf.injective (h.trans f.map_one.symm))) (g s)
        have hY : cons A b s Y' hx.2 = c * Y' :=
          (generator_mul_of_not_headDiv A b hb s Y' hx.2).symm
        have hZ : cons A b s Z' hy.2 = c * Z' :=
          (generator_mul_of_not_headDiv A b hb s Z' hy.2).symm
        have hY' : transport hf hg b (cons A b s Y' hx.2) = c' * transport hf hg b Y' := by
          rw [hY,transport_mul,transport_generator]
        have hZ' : transport hf hg b (cons A b s Z' hy.2) = c' * transport hf hg b Z' := by
          rw [hZ,transport_mul,transport_generator]
        rw [hY'] at hxq
        rw [hZ'] at hyq
        obtain ⟨r,rfl⟩ := hxq
        have hZY : transport hf hg b Z' ∣ transport hf hg b Y' * r := by
          apply (left_mul_dvd_iff c' _ _).1
          exact (_root_.mul_assoc c' (transport hf hg b Y') r) ▸ hyq
        obtain ⟨j,hYj,hZj,hjr⟩ := ih Z' (transport hf hg b Y' * r)
          hZY hx.1 (dvd_mul_right _ _)
        refine ⟨c * j,?_,?_,?_⟩
        · rw [hY]; exact mul_dvd_mul_left c hYj
        · rw [hZ]; exact mul_dvd_mul_left c hZj
        · rw [transport_mul,show transport hf hg b c = c' from transport_generator hf hg b hb s,
            _root_.mul_assoc]
          exact mul_dvd_mul_left c' hjr
      · by_cases hqs : head C (f b) q = some (g s)
        · have hvw := transport_dvd_of_different_head hf hg b hB hA hC
            (x := cons A b s Y' hx.2) rfl rfl hst hyq hqs
          exact ⟨cons A b s Y' hx.2,dvd_refl _,hvw,hxq⟩
        by_cases hqt : head C (f b) q = some (g t)
        · have hwv := transport_dvd_of_different_head hf hg b hB hA hC
            (x := cons A b t Z' hy.2) rfl rfl (Ne.symm hst) hxq hqt
          exact ⟨cons A b t Z' hy.2,hwv,dvd_refl _,hyq⟩
        obtain ⟨j,hj,hj'⟩ := exists_simulated_gate_of_exit hf hg b hB hA hC
          (cons A b s Y' hx.2) rfl hxq hqs
        obtain ⟨k,hk,hk'⟩ := exists_simulated_gate_of_exit hf hg b hB hA hC
          (cons A b t Z' hy.2) rfl hyq hqt
        obtain ⟨l,hjl,hkl,hlq⟩ := (hf.comp hC).common_below hB
          ((hj' q).1 ⟨hxq,hqs⟩) ((hk' q).1 ⟨hyq,hqt⟩)
        exact ⟨old A b l,(Gate.dvd A b hj).trans ((oldHom A b).map_dvd hjl),
          (Gate.dvd A b hk).trans ((oldHom A b).map_dvd hkl),hlq⟩

include hb hB hA hC in
/-- Probe normal-form simulation conserves factors, all old cone
intersections, and old nonjoins. -/
theorem transport_conservative : Conservative (transportHom hf hg b) where
  injective := transport_injective hf hg b
  factors := transport_factors hf hg b hB hA hC
  intersections x y j hj q := by
    constructor
    · rintro ⟨hx,hy⟩
      obtain ⟨k,hxk,hyk,hkq⟩ := transport_common_below hf hg b hb hB hA hC x y q hx hy
      exact ((transportHom hf hg b).map_dvd ((hj k).1 ⟨hxk,hyk⟩)).trans hkq
    · intro hq
      have hu := (hj j).2 (dvd_refl j)
      exact ⟨((transportHom hf hg b).map_dvd hu.1).trans hq,
        ((transportHom hf hg b).map_dvd hu.2).trans hq⟩
  common x y h := by
    obtain ⟨q,hx,hy⟩ := h
    obtain ⟨j,hxj,hyj,_⟩ := transport_common_below hf hg b hb hB hA hC x y q hx hy
    exact ⟨j,hxj,hyj⟩

end PartitionConsistency.ProbeAlgebra.Word

namespace PartitionConsistency.ProbeAlgebra.Path
universe u v
open DiagramOrder
variable {B : Type u} {M : Type v} [LeftCancelMonoid B] [IsConical B]
  [LeftCancelMonoid M] [IsConical M] {a e : B} (P : Path B a) (he : e ≠ 1)
  {f : B →* M} (hf : Conservative f) (b : B)

/-- Simulate the identical countable probe presentation over the larger
base; this is a homomorphism of the actual reduced-word extensions. -/
noncomputable def simulation : P.Extension he b →*
    (P.map f).Extension (fun h => he (hf.injective (h.trans f.map_one.symm))) (f b) :=
  Word.transportHom hf (P.alphabetSimulation he hf) b

/-- Probe case of source `lem:mono-simulation`.  It conserves right
factors, whole cone intersections, and the lack of a common right multiple. -/
theorem simulation_conservative
    (hB : HasConditionalJoins (LeftDivOrder B)) (hb : b ≠ 1) :
    Conservative (P.simulation he hf b) :=
  Word.transport_conservative hf (P.alphabetSimulation he hf) b hb hB
    (P.oldHom_conservative he b)
    ((P.map f).oldHom_conservative
      (fun h => he (hf.injective (h.trans f.map_one.symm))) (f b))

@[simp] theorem simulation_old (x : B) :
    P.simulation he hf b (Word.old (P.alphabet he) b x) =
      Word.old ((P.map f).alphabet
        (fun h => he (hf.injective (h.trans f.map_one.symm)))) (f b) (f x) := rfl

@[simp] theorem simulation_probe (hb : b ≠ 1) (i : ℕ) :
    P.simulation he hf b (P.probe he b hb i) =
      (P.map f).probe (fun h => he (hf.injective (h.trans f.map_one.symm))) (f b)
        (fun h => hb (hf.injective (h.trans f.map_one.symm))) i := by
  change Word.transport hf (P.alphabetSimulation he hf) b
    (Word.generator (P.alphabet he) b hb (P.letter i 1)) = _
  simp only [Word.transport_generator, lettersMap_letter, map_one, probe]

end PartitionConsistency.ProbeAlgebra.Path

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Algebra_PersistentProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Persistence of the full probe profile at successor stages -/


namespace PartitionConsistency.DiagramOrder
universe u v

/-- The full profile of a probe, with downsets taken in the entire monoid
rather than only in the base over which the probe was adjoined. -/
structure ProbeProfile {M : Type u} [Monoid M]
    (a b e m : M) (n : ℕ → M) : Prop where
  exit : m * b = a * e
  not_divides : ¬ m ∣ a
  divisors : ∀ x : M, x ∣ a ∧ x ∣ m ↔ ∃ i : ℕ, x ∣ n i
  joins : ∀ x : M, x ∣ a → ¬ x ∣ m →
    ∀ z : M, x ∣ z ∧ m ∣ z ↔ a * e ∣ z

/-- An old gate controls both old right multiples and intersections with
old cones not containing the new element. In probe normal forms this is
exactly the first-letter exit rule. -/
structure OldGate {M : Type u} {N : Type v} [Monoid M] [Monoid N]
    (f : M →* N) (w : N) (g : M) : Prop where
  divides : w ∣ f g
  old_multiples : ∀ x : M, w ∣ f x ↔ g ∣ x
  intersections : ∀ x : M, ¬ f x ∣ w →
    ∀ z : N, w ∣ z ∧ f x ∣ z ↔ f g ∣ z ∧ f x ∣ z

/-- Only elements with an old right multiple need a gate. For mergers
all such elements are already old, so the second alternative is unused. -/
def HasOldGates {M : Type u} {N : Type v} [Monoid M] [Monoid N]
    (f : M →* N) : Prop :=
  ∀ w : N, (∃ a : M, w ∣ f a) →
    (∃ x : M, f x = w) ∨ ∃ g : M, OldGate f w g

namespace ProbeProfile
variable {M : Type u} {N : Type v} [Monoid M] [Monoid N]
  {a b e m : M} {n : ℕ → M} (h : ProbeProfile a b e m n)
  {f : M →* N} (hf : Conservative f) (hg : HasOldGates f)

include hf hg h

/-- Source `lem:mono-profile-persistence`, successor step.  The new
full downward closure of the original path, not its old set of divisors,
is the profile in the extension. -/
theorem map : ProbeProfile (f a) (f b) (f e) (f m) (f ∘ n) where
  exit := by rw [← f.map_mul, h.exit, f.map_mul]
  not_divides hm := h.not_divides ((hf.dvd_iff m a).1 hm)
  divisors x := by
    constructor
    · rintro ⟨hxa,hxm⟩
      rcases hg x ⟨a,hxa⟩ with ⟨y,rfl⟩ | ⟨g,hg⟩
      · obtain ⟨i,hi⟩ := (h.divisors y).1 ⟨(hf.dvd_iff y a).1 hxa,
          (hf.dvd_iff y m).1 hxm⟩
        exact ⟨i,f.map_dvd hi⟩
      · obtain ⟨i,hi⟩ := (h.divisors g).1 ⟨(hg.old_multiples a).1 hxa,
          (hg.old_multiples m).1 hxm⟩
        exact ⟨i,hg.divides.trans (f.map_dvd hi)⟩
    · rintro ⟨i,hi⟩
      have hni := (h.divisors (n i)).2 ⟨i,dvd_refl _⟩
      exact ⟨hi.trans (f.map_dvd hni.1),hi.trans (f.map_dvd hni.2)⟩
  joins x hxa hxm z := by
    rcases hg x ⟨a,hxa⟩ with ⟨y,rfl⟩ | ⟨g,hg⟩
    · simpa only [f.map_mul] using hf.intersections y m (a * e)
        (h.joins y ((hf.dvd_iff y a).1 hxa) (fun hy => hxm (f.map_dvd hy))) z
    · have hga := (hg.old_multiples a).1 hxa
      have hgm : ¬ g ∣ m := fun hgm => hxm ((hg.old_multiples m).2 hgm)
      have hmx : ¬ f m ∣ x := fun hmx => h.not_divides ((hf.dvd_iff m a).1 (hmx.trans hxa))
      rw [hg.intersections m hmx z]
      simpa only [f.map_mul] using hf.intersections g m (a * e) (h.joins g hga hgm) z

end ProbeProfile
end PartitionConsistency.DiagramOrder

namespace PartitionConsistency.ProbeAlgebra.Path
universe u
open DiagramOrder
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}
  (P : Path M a) (he : e ≠ 1) (b : M)

/-- The gate hypothesis of profile persistence is supplied by the actual
probe extension, including all new words, not just the adjoined generators. -/
theorem hasOldGates (hM : HasConditionalJoins (LeftDivOrder M)) :
    HasOldGates (Word.oldHom (P.alphabet he) b) := by
  intro w hw
  classical
  by_cases ho : ∃ x : M, Word.old (P.alphabet he) b x = w
  · exact Or.inl ho
  · obtain ⟨y,hy⟩ := hw
    cases hs : Word.head (P.alphabet he) b w with
    | none => exact (ho (by
        obtain ⟨x,hx⟩ := (Word.head_eq_none_iff _ _ w).1 hs
        exact ⟨x,hx.symm⟩)).elim
    | some s =>
      obtain ⟨g,hg⟩ := Word.exists_gate_of_exit (P.alphabet he) b (P.oldIntersections he b hM)
        w hs hy (by intro h; cases h)
      refine Or.inr ⟨g,Word.Gate.dvd _ _ hg,Word.Gate.dvd_old_iff _ _ hg,?_⟩
      intro x hx z
      change (w ∣ z ∧ Word.old (P.alphabet he) b x ∣ z) ↔
        Word.old (P.alphabet he) b g ∣ z ∧ Word.old (P.alphabet he) b x ∣ z
      simpa only [and_comm] using Word.Gate.old_intersection _ _ hg hs
        (fun hd => hx ((Word.old_dvd_iff_headDiv _ _ x w).2 hd)) z

/-- The profile initially holds with all downsets in the new monoid. -/
theorem probeProfile (hM : HasConditionalJoins (LeftDivOrder M)) (hb : b ≠ 1) :
    ProbeProfile (Word.old (P.alphabet he) b a) (Word.old (P.alphabet he) b b)
      (Word.old (P.alphabet he) b e) (P.probe he b hb 0)
      (fun i => Word.old (P.alphabet he) b (P.node i)) where
  exit := P.probe_zero_mul_b he b hb
  not_divides := P.probe_not_dvd_a he b hb
  divisors x := by simpa only [and_comm] using P.probe_full_profile he b hb hM x
  joins x hxa hxm z := P.probe_join_profile he b hb hM hxa hxm z

end PartitionConsistency.ProbeAlgebra.Path

namespace PartitionConsistency.MergerAlgebra.Word
universe u v
open DiagramOrder
variable {M : Type u} {D : Type v} [Monoid M] [RightFreeAction M D]

/-- A merger introduces no new divisor of any old element. -/
theorem hasOldGates : HasOldGates (oldHom : M →* Word M D) := by
  rintro w ⟨a,q,hq⟩
  obtain ⟨x,y,hx,hy,hxy⟩ := factors_of_old hq.symm
  exact Or.inl ⟨x,hx.symm⟩

end PartitionConsistency.MergerAlgebra.Word

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Algebra_DirectLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Conservative direct limits, profiles, and the exact real margin -/

noncomputable section

namespace PartitionConsistency.DiagramOrder.ConservativeLimit
universe u v
variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  {M : ι → Type v} [∀ i, LeftCancelMonoid (M i)]
  (f : ∀ i j, i ≤ j → M i →* M j)
  [DirectedSystem M (f · · ·)]

/-- Canonical maps into the directed union, represented as a direct limit.
No ambient monoid or model-existence hypothesis is needed. -/
def of (i : ι) : M i →* DirectLimit M f where
  toFun x := Quotient.mk _ ⟨i, x⟩
  map_one' := (DirectLimit.one_def (f := f) i).symm
  map_mul' x y := (DirectLimit.mul_def (f := f) i x y).symm

@[simp] theorem of_apply (i : ι) (x : M i) :
    of f i x = (Quotient.mk _ ⟨i, x⟩ : DirectLimit M f) := rfl

@[simp] theorem of_map (i j : ι) (h : i ≤ j) (x : M i) :
    of f j (f i j h x) = of f i x := DirectLimit.mk_apply i j x h

/-- Left cancellation passes to a directed limit even without injective
transition maps: each equation can be tested at a common later stage. -/
instance instLeftCancelMonoidDirectLimitMonoidHom_solutions : LeftCancelMonoid (DirectLimit M f) where
  mul_left_cancel := by
    intro x y z
    refine DirectLimit.induction₃ f (fun i a b c => ?_) x y z
    intro h
    change (Quotient.mk _ ⟨i,a⟩ : DirectLimit M f) * Quotient.mk _ ⟨i,b⟩ =
      Quotient.mk _ ⟨i,a⟩ * Quotient.mk _ ⟨i,c⟩ at h
    rw [DirectLimit.mul_def, DirectLimit.mul_def, Quotient.eq] at h
    obtain ⟨j, hij, hij', he⟩ := h
    simp only [map_mul] at he
    exact Quotient.sound ⟨j, hij, hij', mul_left_cancel he⟩

instance instIsConicalDirectLimitMonoidHom [∀ i, IsConical (M i)] : IsConical (DirectLimit M f) where
  eq_one_of_mul_eq_one := by
    intro x y
    refine DirectLimit.induction₂ f (fun i a b => ?_) x y
    intro h
    rw [DirectLimit.mul_def, DirectLimit.one_def i, Quotient.eq] at h
    obtain ⟨j, hij, hij', he⟩ := h
    simp only [map_mul, map_one] at he
    obtain ⟨ha, hb⟩ := IsConical.eq_one_of_mul_eq_one he
    constructor
    · rw [DirectLimit.one_def i, Quotient.eq]
      exact ⟨j, hij, hij, by simpa only [map_one] using ha⟩
    · rw [DirectLimit.one_def i, Quotient.eq]
      exact ⟨j, hij, hij, by simpa only [map_one] using hb⟩

variable (hf : ∀ i j h, Conservative (f i j h))
include hf

theorem of_injective (i : ι) : Function.Injective (of f i) :=
  DirectLimit.mk_injective f (fun i j h => (hf i j h).injective) i

theorem of_factors (i : ι) (x y : M i) (z : DirectLimit M f)
    (h : of f i x * z = of f i y) : ∃ t : M i, of f i t = z := by
  obtain ⟨j, z, rfl⟩ := DirectLimit.exists_eq_mk f z
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  change of f i x * of f j z = of f i y at h
  rw [← of_map f i k hik x, ← of_map f j k hjk z,
    ← of_map f i k hik y, ← map_mul] at h
  obtain ⟨t, ht⟩ := (hf i k hik).factors x y (f j k hjk z) (of_injective f hf k h)
  refine ⟨t, ?_⟩
  change of f i t = of f j z
  rw [← of_map f i k hik t, ht, of_map]

/-- Divisibility in the union between two elements of one stage is
exactly divisibility at that stage, with no new right factor. -/
theorem of_dvd_iff (i : ι) (x y : M i) : of f i x ∣ of f i y ↔ x ∣ y := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨t, rfl⟩ := of_factors f hf i x y z hz.symm
    exact ⟨t, of_injective f hf i (by rw [map_mul]; exact hz)⟩
  · exact (of f i).map_dvd

theorem of_conservative (i : ι) : Conservative (of f i) where
  injective := of_injective f hf i
  factors := of_factors f hf i
  intersections x y a ha z := by
    obtain ⟨j,z,rfl⟩ := DirectLimit.exists_eq_mk f z
    obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
    change (of f i x ∣ of f j z ∧ of f i y ∣ of f j z) ↔ of f i a ∣ of f j z
    rw [← of_map f i k hik x, ← of_map f i k hik y,
      ← of_map f i k hik a, ← of_map f j k hjk z,
      of_dvd_iff f hf, of_dvd_iff f hf, of_dvd_iff f hf]
    exact (hf i k hik).intersections x y a ha (f j k hjk z)
  common x y h := by
    obtain ⟨z,hxz,hyz⟩ := h
    obtain ⟨j,z,rfl⟩ := DirectLimit.exists_eq_mk f z
    obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
    change of f i x ∣ of f j z at hxz
    change of f i y ∣ of f j z at hyz
    rw [← of_map f i k hik x, ← of_map f j k hjk z, of_dvd_iff f hf] at hxz
    rw [← of_map f i k hik y, ← of_map f j k hjk z, of_dvd_iff f hf] at hyz
    exact (hf i k hik).common x y ⟨f j k hjk z, hxz, hyz⟩

variable [∀ i, IsConical (M i)]

/-- Conditional joins in a conservative tower remain conditional joins
in the union; pairs that never had a common right multiple acquire none. -/
theorem conditionalJoins (hM : ∀ i, HasConditionalJoins (LeftDivOrder (M i))) :
    HasConditionalJoins (LeftDivOrder (DirectLimit M f)) := by
  intro x y a hx hy
  obtain ⟨i,x,y,a,rfl,rfl,rfl⟩ := DirectLimit.exists_eq_mk₃ f x y a
  obtain ⟨z,hz⟩ := exists_cone_join (hM i) x y a
    ((of_dvd_iff f hf i x a).1 ((LeftDivOrder.le_iff_dvd (M := DirectLimit M f) _ _).1 hx))
    ((of_dvd_iff f hf i y a).1 ((LeftDivOrder.le_iff_dvd (M := DirectLimit M f) _ _).1 hy))
  refine ⟨of f i z, ?_⟩
  apply (pair_lub_iff (α := LeftDivOrder (DirectLimit M f)) _ _ _).2
  intro w
  exact ((and_congr
      (LeftDivOrder.le_iff_dvd (M := DirectLimit M f) (of f i x) w)
      (LeftDivOrder.le_iff_dvd (M := DirectLimit M f) (of f i y) w)).trans
    ((of_conservative f hf i).intersections x y z hz w)).trans
    (LeftDivOrder.le_iff_dvd (M := DirectLimit M f) (of f i z) w).symm

omit [∀ i, IsConical (M i)] in
/-- The successor persistence theorem passes to the full union. The path
remains the original path; its downward closure is taken in the final monoid. -/
theorem probeProfile (i : ι) (a b e m : M i) (n : ℕ → M i)
    (hP : ∀ j (hij : i ≤ j),
      ProbeProfile (f i j hij a) (f i j hij b) (f i j hij e)
        (f i j hij m) (fun k => f i j hij (n k))) :
    ProbeProfile (of f i a) (of f i b) (of f i e) (of f i m)
      (fun k => of f i (n k)) := by
  have hi : ProbeProfile a b e m n := by
    simpa only [DirectedSystem.map_self'] using hP i le_rfl
  refine ⟨?_,?_,?_,?_⟩
  · rw [← map_mul, hi.exit, map_mul]
  · intro h
    exact hi.not_divides ((of_dvd_iff f hf i m a).1 h)
  · intro x
    constructor
    · rintro ⟨hxa,hxm⟩
      obtain ⟨j,x,rfl⟩ := DirectLimit.exists_eq_mk f x
      obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
      have hxa' : f j k hjk x ∣ f i k hik a :=
        (of_dvd_iff f hf k _ _).1 (by simpa only [of_apply, DirectLimit.mk_apply] using hxa)
      have hxm' : f j k hjk x ∣ f i k hik m :=
        (of_dvd_iff f hf k _ _).1 (by simpa only [of_apply, DirectLimit.mk_apply] using hxm)
      obtain ⟨l,hl⟩ := ((hP k hik).divisors (f j k hjk x)).1 ⟨hxa',hxm'⟩
      exact ⟨l,by simpa only [of_apply, DirectLimit.mk_apply] using (of f k).map_dvd hl⟩
    · rintro ⟨l,hl⟩
      have hn := (hi.divisors (n l)).2 ⟨l,dvd_refl _⟩
      exact ⟨hl.trans ((of f i).map_dvd hn.1),hl.trans ((of f i).map_dvd hn.2)⟩
  · intro x hxa hxm z
    obtain ⟨j,x,rfl⟩ := DirectLimit.exists_eq_mk f x
    obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
    have hxa' : f j k hjk x ∣ f i k hik a :=
      (of_dvd_iff f hf k _ _).1 (by simpa only [of_apply, DirectLimit.mk_apply] using hxa)
    have hxm' : ¬ f j k hjk x ∣ f i k hik m := by
      intro h
      exact hxm (by simpa only [of_apply, DirectLimit.mk_apply] using (of f k).map_dvd h)
    have h := (of_conservative f hf k).intersections
      (f j k hjk x) (f i k hik m) (f i k hik a * f i k hik e)
        ((hP k hik).joins _ hxa' hxm') z
    simpa only [map_mul, of_apply, DirectLimit.mk_apply] using h

end PartitionConsistency.DiagramOrder.ConservativeLimit

namespace PartitionConsistency.DiagramOrder.ConservativeLimit
universe u v
variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  {M : ι → Type v} [∀ i, LeftCancelMonoid (M i)] [∀ i, IsConical (M i)]
  (f : ∀ i j, i ≤ j → M i →* M j)
  [DirectedSystem M (f · · ·)]
  (H : ∀ i, HeightCost (LeftDivOrder (M i)))
  (hρ : ∀ i j hij x, (H j).height (f i j hij x) = (H i).height x)
  (hε : ∀ i j hij x, (H j).cost (f i j hij x) = (H i).cost x)

def height : LeftDivOrder (DirectLimit M f) → ℝ :=
  DirectLimit.lift f (fun i => (H i).height) (fun i j h x => (hρ i j h x).symm)

def cost : LeftDivOrder (DirectLimit M f) → ℝ :=
  DirectLimit.lift f (fun i => (H i).cost) (fun i j h x => (hε i j h x).symm)

@[simp] theorem height_of (i : ι) (x : M i) :
    height f H hρ (of f i x) = (H i).height x := rfl

@[simp] theorem cost_of (i : ι) (x : M i) :
    cost f H hε (of f i x) = (H i).cost x := rfl

omit [Nonempty ι] in
theorem height_pos (x : LeftDivOrder (DirectLimit M f)) : 0 < height f H hρ x := by
  obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk f x
  exact (H i).height_pos x

omit [Nonempty ι] in
theorem height_lt_one (x : LeftDivOrder (DirectLimit M f)) : height f H hρ x < 1 := by
  obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk f x
  exact (H i).height_lt_one x

omit [Nonempty ι] in
theorem cost_pos (x : LeftDivOrder (DirectLimit M f)) : 0 < cost f H hε x := by
  obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk f x
  exact (H i).cost_pos x

omit [Nonempty ι] in
theorem cost_le_one (x : LeftDivOrder (DirectLimit M f)) : cost f H hε x ≤ 1 := by
  obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk f x
  exact (H i).cost_le_one x

variable (hf : ∀ i j h, Conservative (f i j h))
  (hSup : ∀ i j hij (x y : LeftDivOrder (M i)),
    sSup ((H j).cost '' {d : LeftDivOrder (M j) |
      d ≤ f i j hij y ∧ ¬ d ≤ f i j hij x}) =
        sSup ((H i).cost '' {d : LeftDivOrder (M i) | d ≤ y ∧ ¬ d ≤ x}))
include hf hSup

/-- Costs of all later divisors, including those not present at the old
stage, are uniformly bounded by the old missed-cost supremum. -/
theorem cost_le_old_sup (i : ι) (x y : LeftDivOrder (M i))
    (d : LeftDivOrder (DirectLimit M f))
    (hdy : d ≤ of f i y) (hdx : ¬ d ≤ of f i x) :
    cost f H hε d ≤ sSup ((H i).cost '' {a : LeftDivOrder (M i) | a ≤ y ∧ ¬ a ≤ x}) := by
  obtain ⟨j,d,rfl⟩ := DirectLimit.exists_eq_mk f d
  obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
  have hdy' : @LE.le (LeftDivOrder (M k)) _ (f j k hjk d) (f i k hik y) := by
    apply (LeftDivOrder.le_iff_dvd (M := M k) _ _).2
    apply (of_dvd_iff f hf k _ _).1
    erw [of_map f j k hjk d, of_map f i k hik y]
    exact (LeftDivOrder.le_iff_dvd (M := DirectLimit M f) _ _).1 hdy
  have hdx' : ¬ @LE.le (LeftDivOrder (M k)) _ (f j k hjk d) (f i k hik x) := by
    intro h
    apply hdx
    have hdv := (LeftDivOrder.le_iff_dvd (M := M k) _ _).1 h
    have hv := (of f k).map_dvd hdv
    erw [of_map f j k hjk d, of_map f i k hik x] at hv
    exact (LeftDivOrder.le_iff_dvd (M := DirectLimit M f) _ _).2 hv
  have hb : BddAbove ((H k).cost '' {a : LeftDivOrder (M k) |
      a ≤ f i k hik y ∧ ¬ a ≤ f i k hik x}) := by
    refine ⟨1,?_⟩
    rintro _ ⟨a,_,rfl⟩
    exact (H k).cost_le_one a
  have hc := le_csSup hb ⟨f j k hjk d,⟨hdy',hdx'⟩,rfl⟩
  rw [hSup i k hik x y, hε j k hjk d] at hc
  exact hc

/-- No supremum inflation occurs at limit stages. Merely preserving
pointwise strict inequalities would not imply this statement. -/
theorem old_cost_supremum (i : ι) (x y : LeftDivOrder (M i)) :
    sSup (cost f H hε '' {d : LeftDivOrder (DirectLimit M f) |
      d ≤ of f i y ∧ ¬ d ≤ of f i x}) =
        sSup ((H i).cost '' {d : LeftDivOrder (M i) | d ≤ y ∧ ¬ d ≤ x}) := by
  let S₀ := (H i).cost '' {d : LeftDivOrder (M i) | d ≤ y ∧ ¬ d ≤ x}
  let S₁ := cost f H hε '' {d : LeftDivOrder (DirectLimit M f) |
      d ≤ of f i y ∧ ¬ d ≤ of f i x}
  have hsubset : S₀ ⊆ S₁ := by
    rintro _ ⟨d,⟨hdy,hdx⟩,rfl⟩
    refine ⟨of f i d,⟨?_,?_⟩,rfl⟩
    · exact (LeftDivOrder.le_iff_dvd (M := DirectLimit M f) _ _).2
        ((of f i).map_dvd ((LeftDivOrder.le_iff_dvd (M := M i) _ _).1 hdy))
    · intro h
      apply hdx
      exact (LeftDivOrder.le_iff_dvd (M := M i) _ _).2
        ((of_dvd_iff f hf i d x).1
          ((LeftDivOrder.le_iff_dvd (M := DirectLimit M f) _ _).1 h))
  change sSup S₁ = sSup S₀
  by_cases hyx : y ≤ x
  · have hS₀ : S₀ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      rintro _ ⟨d,⟨hdy,hdx⟩,_⟩
      exact hdx (hdy.trans hyx)
    have hS₁ : S₁ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      rintro _ ⟨d,⟨hdy,hdx⟩,_⟩
      apply hdx
      exact hdy.trans ((LeftDivOrder.le_iff_dvd (M := DirectLimit M f) _ _).2
        ((of f i).map_dvd ((LeftDivOrder.le_iff_dvd (M := M i) _ _).1 hyx)))
    rw [hS₀,hS₁]
  · have hS₀ : S₀.Nonempty := ⟨(H i).cost y,y,⟨le_rfl,hyx⟩,rfl⟩
    have hS₁ : S₁.Nonempty := hS₀.mono hsubset
    have hb₁ : BddAbove S₁ := by
      refine ⟨1,?_⟩
      rintro _ ⟨d,_,rfl⟩
      exact cost_le_one f H hε d
    apply le_antisymm
    · apply csSup_le hS₁
      rintro _ ⟨d,⟨hdy,hdx⟩,rfl⟩
      exact cost_le_old_sup f H hε hf hSup i x y d hdy hdx
    · exact csSup_le hS₀ (fun r hr => le_csSup hb₁ (hsubset hr))

/-- Limit-stage extension of the exact real height/cost margin, using
unchanged old suprema at every transition of the tower. -/
def heightCost : HeightCost (LeftDivOrder (DirectLimit M f)) where
  height := height f H hρ
  cost := cost f H hε
  height_pos := height_pos f H hρ
  height_lt_one := height_lt_one f H hρ
  cost_pos := cost_pos f H hε
  cost_le_one := cost_le_one f H hε
  margin {x y} hxy := by
    obtain ⟨i,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ f x y
    have hxy' : @LT.lt (LeftDivOrder (M i)) _ x y := by
      apply lt_iff_le_and_ne.2
      refine ⟨?_,?_⟩
      · apply (LeftDivOrder.le_iff_dvd (M := M i) _ _).2
        exact (of_dvd_iff f hf i x y).1
          ((LeftDivOrder.le_iff_dvd (M := DirectLimit M f) _ _).1 hxy.le)
      · exact fun he => hxy.ne (congrArg (of f i) he)
    change sSup (cost f H hε '' {d : LeftDivOrder (DirectLimit M f) |
      d ≤ of f i y ∧ ¬ d ≤ of f i x}) < (H i).height y - (H i).height x
    rw [old_cost_supremum f H hε hf hSup i x y]
    exact (H i).margin hxy'

@[simp] theorem heightCost_height_of (i : ι) (x : M i) :
    (heightCost f H hρ hε hf hSup).height (of f i x) = (H i).height x := rfl

@[simp] theorem heightCost_cost_of (i : ι) (x : M i) :
    (heightCost f H hρ hε hf hSup).cost (of f i x) = (H i).cost x := rfl

end PartitionConsistency.DiagramOrder.ConservativeLimit
end

namespace PartitionConsistency.DiagramOrder.ConservativeLimit
universe u v
variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι]
  {M : ι → Type u} {F : ∀ ⦃i j : ι⦄, i ≤ j → Sort v}
  (f : ∀ i j (h : i ≤ j), F h)
  [∀ ⦃i j : ι⦄ (h : i ≤ j), FunLike (F h) (M i) (M j)]
  [DirectedSystem M (f · · ·)]

/-- The cardinal bound used at the limit stages of the schedule. This does
not require injectivity, conservativity, or an algebraic structure. -/
theorem cardinal_le {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
    (hι : Cardinal.mk ι ≤ μ) (hM : ∀ i, Cardinal.mk (M i) ≤ μ) :
    Cardinal.mk (DirectLimit M f) ≤ μ := by
  calc
    Cardinal.mk (DirectLimit M f) ≤ Cardinal.mk (Sigma M) := Cardinal.mk_quotient_le
    _ = Cardinal.sum (fun i => Cardinal.mk (M i)) := Cardinal.mk_sigma M
    _ ≤ Cardinal.sum (fun _ : ι => μ) := Cardinal.sum_le_sum _ _ hM
    _ = Cardinal.mk ι * μ := Cardinal.sum_const' ι μ
    _ ≤ μ * μ := by simpa only [mul_comm] using mul_le_mul_right hι μ
    _ = μ := Cardinal.mul_eq_self hμ

end PartitionConsistency.DiagramOrder.ConservativeLimit

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_MonoidBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Base -/

namespace PartitionConsistency.MonoidConstruction
universe u
open DiagramOrder

/-- The objects used by the construction retain the real margin together with
an actual cancellative conical monoid; no saturation property is built in. -/
structure Object where
  Carrier : Type u
  [monoid : LeftCancelMonoid Carrier]
  [conical : IsConical Carrier]
  joins : HasConditionalJoins (LeftDivOrder Carrier)
  margin : HeightCost (LeftDivOrder Carrier)
  e : Carrier
  e_ne_one : e ≠ 1

instance instCoeSortObjectType : CoeSort Object (Type u) := ⟨Object.Carrier⟩
attribute [instance] Object.monoid Object.conical

namespace Base
abbrev M := Multiplicative ℕ

def degree (x : LeftDivOrder M) : ℕ := @Multiplicative.toAdd ℕ x

instance instIsConicalM : IsConical M where
  eq_one_of_mul_eq_one {x y} h := by
    change degree x + degree y = 0 at h
    exact ⟨Nat.eq_zero_of_add_eq_zero_right h, Nat.eq_zero_of_add_eq_zero_left h⟩

theorem le_iff (x y : LeftDivOrder M) : x ≤ y ↔ degree x ≤ degree y := by
  change (∃ z : M, degree x + degree z = degree y) ↔ degree x ≤ degree y
  exact ⟨fun ⟨z,h⟩ => h ▸ Nat.le_add_right _ _,
    fun h => ⟨Multiplicative.ofAdd (degree y - degree x), Nat.add_sub_of_le h⟩⟩

theorem lt_iff (x y : LeftDivOrder M) : x < y ↔ degree x < degree y := by
  rw [lt_iff_le_not_ge, le_iff, le_iff, ← lt_iff_le_not_ge]

theorem joins : HasConditionalJoins (LeftDivOrder M) := by
  intro x y _ _ _
  refine ⟨(show LeftDivOrder M from @Multiplicative.ofAdd ℕ (max (degree x) (degree y))), ?_⟩
  apply (pair_lub_iff (α := LeftDivOrder M) _ _ _).2
  intro z
  rw [le_iff, le_iff, le_iff]
  exact max_le_iff.symm

noncomputable def height (x : LeftDivOrder M) : ℝ := 1 - (1/2:ℝ) ^ (degree x+1)
noncomputable def cost (x : LeftDivOrder M) : ℝ := (1/2:ℝ) ^ (degree x+3)

theorem height_pos (x : LeftDivOrder M) : 0 < height x := by
  have h : (1/2:ℝ) ^ (degree x+1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  exact sub_pos.mpr h

theorem height_lt_one (x : LeftDivOrder M) : height x < 1 := by
  have h : 0 < (1/2:ℝ) ^ (degree x+1) := pow_pos (by norm_num) _
  unfold height
  linarith

theorem margin {x y : LeftDivOrder M} (hxy : x < y) :
    UniformMargin height cost x y := by
  have hxy' := (lt_iff x y).1 hxy
  refine ⟨(1/2:ℝ) ^ (degree x+3), ?_, ?_⟩
  · have hp : (1/2:ℝ) ^ (degree y+1) ≤ (1/2:ℝ) ^ (degree x+2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hx : 0 < (1/2:ℝ) ^ (degree x+1) := pow_pos (by norm_num) _
    show (1/2:ℝ) ^ (degree x+3) <
      (1 - (1/2:ℝ) ^ (degree y+1)) - (1 - (1/2:ℝ) ^ (degree x+1))
    have he2 : (1/2:ℝ) ^ (degree x+2) = (1/2:ℝ) ^ (degree x+1) * (1/2) :=
      pow_succ _ _
    have he3 : (1/2:ℝ) ^ (degree x+3) = (1/2:ℝ) ^ (degree x+1) * (1/2) * (1/2) := by
      rw [pow_succ, he2]
    rw [he2] at hp
    rw [he3]
    nlinarith
  · intro d hd hdx
    have hx := (le_iff d x).not.1 hdx
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

noncomputable def heightCost : HeightCost (LeftDivOrder M) where
  height := height
  cost := cost
  height_pos := height_pos
  height_lt_one := height_lt_one
  cost_pos _ := pow_pos (by norm_num) _
  cost_le_one _ := pow_le_one₀ (by norm_num) (by norm_num)
  margin hxy := (margin hxy).supremum_lt hxy

/-- The free monoid on one generator, with the source's concrete base heights. -/
noncomputable def object : Object.{0} where
  Carrier := M
  monoid := inferInstance
  conical := inferInstance
  joins := joins
  margin := heightCost
  e := Multiplicative.ofAdd 1
  e_ne_one := by decide

end Base
end PartitionConsistency.MonoidConstruction


/-! ## Operation -/

namespace PartitionConsistency.MonoidConstruction
universe u v
open DiagramOrder
noncomputable section

/-- The amount reserved by the margin at an ordered pair. -/
def missedSup (M : Object.{u}) (x y : M) : ℝ :=
  sSup (M.margin.cost '' {d : LeftDivOrder M | d ≤ y ∧ ¬ d ≤ x})

/-- Maps of construction stages retain right factors, disjointness, and
exact old suprema. Such maps make continuous unions legitimate stages. -/
structure Hom (M : Object.{u}) (N : Object.{v}) extends M →* N where
  conservative : Conservative toMonoidHom
  map_e : toMonoidHom M.e = N.e
  height : ∀ x, N.margin.height (toMonoidHom x) = M.margin.height x
  cost : ∀ x, N.margin.cost (toMonoidHom x) = M.margin.cost x
  supremum : ∀ x y, missedSup N (toMonoidHom x) (toMonoidHom y) = missedSup M x y

instance instCoeFunHomForallCarrier {M : Object.{u}} {N : Object.{v}} : CoeFun (Hom M N) (fun _ => M → N) :=
  ⟨fun f => f.toMonoidHom⟩

namespace Hom
universe w
variable {M : Object.{u}} {N : Object.{v}} {R : Object.{w}}

@[ext] theorem ext {f g : Hom M N} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g
  congr 1
  exact MonoidHom.ext h

def id (M : Object.{u}) : Hom M M where
  toMonoidHom := MonoidHom.id M
  conservative := Conservative.id M
  map_e := rfl
  height _ := rfl
  cost _ := rfl
  supremum _ _ := rfl

def comp (g : Hom N R) (f : Hom M N) : Hom M R where
  toMonoidHom := g.toMonoidHom.comp f.toMonoidHom
  conservative := f.conservative.comp g.conservative
  map_e := by change g (f M.e) = R.e; rw [f.map_e, g.map_e]
  height x := (g.height (f x)).trans (f.height x)
  cost x := (g.cost (f x)).trans (f.cost x)
  supremum x y := (g.supremum (f x) (f y)).trans (f.supremum x y)

@[simp] theorem id_apply (x : M) : (id M) x = x := rfl
@[simp] theorem comp_apply (g : Hom N R) (f : Hom M N) (x : M) :
    (g.comp f) x = g (f x) := rfl

@[simp] theorem id_comp (f : Hom M N) : (id N).comp f = f := by ext; rfl
@[simp] theorem comp_id (f : Hom M N) : f.comp (id M) = f := by ext; rfl

theorem injective (f : Hom M N) : Function.Injective f := f.conservative.injective

end Hom

/-- A probe request has exactly the old parameters in the presentation;
its path contains its countably many transition and terminal quotients by
conservativity, not an additional saturation assumption. -/
structure ProbeData (M : Object.{u}) where
  a : M
  b : M
  b_ne_one : b ≠ 1
  path : ProbeAlgebra.Path M a

namespace ProbeData
variable {M : Object.{u}} (d : ProbeData M)

/-- Executing a request uses the established literal normal forms. -/
def extension : Object.{u} where
  Carrier := d.path.Extension M.e_ne_one d.b
  monoid := inferInstance
  conical := inferInstance
  joins := d.path.extension_hasConditionalJoins M.e_ne_one d.b M.joins d.b_ne_one
  margin := d.path.extensionHeightCost M.e_ne_one d.b d.b_ne_one M.margin M.joins
  e := ProbeAlgebra.Word.old (d.path.alphabet M.e_ne_one) d.b M.e
  e_ne_one he := M.e_ne_one
    ((d.path.oldHom_conservative M.e_ne_one d.b).injective he)

def inclusion : Hom M d.extension where
  toMonoidHom := ProbeAlgebra.Word.oldHom (d.path.alphabet M.e_ne_one) d.b
  conservative := d.path.oldHom_conservative M.e_ne_one d.b
  map_e := rfl
  height _ := rfl
  cost _ := rfl
  supremum := d.path.extension_old_cost_supremum M.e_ne_one d.b d.b_ne_one M.margin M.joins

def probe : d.extension := d.path.probe M.e_ne_one d.b d.b_ne_one 0

theorem profile : ProbeProfile (d.inclusion d.a) (d.inclusion d.b) d.extension.e
    d.probe (fun i => d.inclusion (d.path.node i)) :=
  d.path.probeProfile M.e_ne_one d.b M.joins d.b_ne_one

theorem probe_new : ¬ ∃ x : M, d.inclusion x = d.probe := by
  rintro ⟨x,hx⟩
  have h : ProbeAlgebra.Raw.old x =
    ProbeAlgebra.Raw.cons (d.path.letter 0 1) (.old 1) := congrArg Subtype.val hx
  cases h

theorem gates : HasOldGates d.inclusion.toMonoidHom :=
  d.path.hasOldGates M.e_ne_one d.b M.joins

theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hM : Cardinal.mk M ≤ μ) : Cardinal.mk d.extension ≤ μ :=
  d.path.extension_cardinal_le M.e_ne_one d.b hω hM

end ProbeData

structure MergerData (M : Object.{u}) where
  n : ℕ
  positive : 0 < n
  prescription : DiagramForcing.OverlapPrescription M n
  valid : prescription.Valid

namespace MergerData
variable {M : Object.{u}} (d : MergerData M)

def extension : Object.{u} where
  Carrier := d.prescription.Merger d.valid
  monoid := inferInstance
  conical := inferInstance
  joins := d.prescription.merger_hasConditionalJoins d.valid M.joins
  margin := d.prescription.mergerHeightCost d.valid M.margin d.positive
  e := .old M.e
  e_ne_one he := M.e_ne_one
    ((MergerAlgebra.Word.oldHom_conservative).injective he)

def inclusion : Hom M d.extension where
  toMonoidHom := MergerAlgebra.Word.oldHom
  conservative := MergerAlgebra.Word.oldHom_conservative
  map_e := rfl
  height _ := rfl
  cost _ := rfl
  supremum := d.prescription.merger_old_cost_supremum d.valid M.margin d.positive

def root (i : Fin d.n) : d.extension := d.prescription.root d.valid i

theorem gates : HasOldGates d.inclusion.toMonoidHom :=
  MergerAlgebra.Word.hasOldGates

theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hM : Cardinal.mk M ≤ μ) : Cardinal.mk d.extension ≤ μ :=
  d.prescription.merger_cardinal_le d.valid hω hM

end MergerData
end
end PartitionConsistency.MonoidConstruction

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_MonoidTowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Tower -/

namespace PartitionConsistency.MonoidConstruction
universe u
open DiagramOrder CategoryTheory CategoryTheory.Limits
noncomputable section

instance instCategoryObject : Category Object.{u} where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f
  id_comp := by intros; apply Hom.ext; intro; rfl
  comp_id := by intros; apply Hom.ext; intro; rfl
  assoc := by intros; apply Hom.ext; intro; rfl

instance instCoeFunHomObjectForallCarrier (M N : Object.{u}) : CoeFun (M ⟶ N) (fun _ => M → N) :=
  ⟨fun f => f.toMonoidHom⟩

namespace DirectedColimit
variable {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]
  (F : J ⥤ Object.{u})

abbrev Carrier (i : J) : Type u := F.obj i

def transition (i j : J) (h : i ≤ j) : F.obj i →* F.obj j :=
  (F.map (homOfLE h)).toMonoidHom

instance instDirectedSystemCarrierCoeMonoidHomCarrierObjObjectTransition : DirectedSystem (Carrier F) (transition F · · ·) where
  map_self i x := by change (F.map (homOfLE (le_refl i))) x = x; simp [homOfLE_refl, F.map_id]; rfl
  map_map i j k hkj hji x := by
    change (F.map (homOfLE hji)) ((F.map (homOfLE hkj)) x) = _
    have h := F.map_comp (homOfLE hkj) (homOfLE hji)
    exact congrArg (fun g : F.obj k ⟶ F.obj i => g x) h.symm

omit [IsDirectedOrder J] [Nonempty J] in
theorem conservative (i j : J) (h : i ≤ j) : Conservative (transition F i j h) :=
  (F.map (homOfLE h)).conservative

abbrev Limit := DirectLimit (Carrier F) (transition F)

def old (i : J) : F.obj i →* Limit F := ConservativeLimit.of (transition F) i

theorem old_map (i j : J) (h : i ≤ j) (x : F.obj i) :
    old F j (F.map (homOfLE h) x) = old F i x :=
  ConservativeLimit.of_map (transition F) i j h x

theorem old_e (i j : J) : old F i (F.obj i).e = old F j (F.obj j).e := by
  obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
  rw [← old_map F i k hik, ← old_map F j k hjk]
  exact congrArg (old F k) ((F.map (homOfLE hik)).map_e.trans (F.map (homOfLE hjk)).map_e.symm)

def margin : HeightCost (LeftDivOrder (Limit F)) :=
  ConservativeLimit.heightCost (transition F) (fun i => (F.obj i).margin)
    (fun _ _ h => (F.map (homOfLE h)).height)
    (fun _ _ h => (F.map (homOfLE h)).cost)
    (conservative F) (fun _ _ h => (F.map (homOfLE h)).supremum)

def object : Object.{u} where
  Carrier := Limit F
  monoid := inferInstance
  conical := inferInstance
  joins := ConservativeLimit.conditionalJoins (transition F) (conservative F) (fun i => (F.obj i).joins)
  margin := margin F
  e := old F (Classical.arbitrary J) (F.obj (Classical.arbitrary J)).e
  e_ne_one h := (F.obj (Classical.arbitrary J)).e_ne_one
    ((ConservativeLimit.of_conservative (transition F) (conservative F)
      (Classical.arbitrary J)).injective h)

def inclusion (i : J) : F.obj i ⟶ object F where
  toMonoidHom := old F i
  conservative := ConservativeLimit.of_conservative (transition F) (conservative F) i
  map_e := old_e F i _
  height _ := rfl
  cost _ := rfl
  supremum := ConservativeLimit.old_cost_supremum (transition F) (fun i => (F.obj i).margin)
    (fun _ _ h => (F.map (homOfLE h)).cost) (conservative F)
    (fun _ _ h => (F.map (homOfLE h)).supremum) i

def cocone : Cocone F where
  pt := object F
  ι := {
    app := inclusion F
    naturality := by
      intro i j f
      apply Hom.ext
      intro x
      exact old_map F i j (leOfHom f) x }

variable (C : Cocone F)

def liftFun : object F → C.pt :=
  DirectLimit.lift (transition F) (fun i => C.ι.app i)
    (fun i j h x => by
      have he := congrArg (fun f : F.obj i ⟶ C.pt => f x) (C.ι.naturality (homOfLE h))
      exact he.symm)

@[simp] theorem lift_old (i : J) (x : F.obj i) : liftFun F C (old F i x) = C.ι.app i x := rfl

def liftMonoidHom : object F →* C.pt where
  toFun := liftFun F C
  map_one' := by
    calc
      liftFun F C 1 = liftFun F C (old F (Classical.arbitrary J) 1) :=
        congrArg (liftFun F C) (map_one (old F (Classical.arbitrary J))).symm
      _ = 1 := (C.ι.app (Classical.arbitrary J)).map_one
  map_mul' x y := by
    obtain ⟨i,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ (transition F) x y
    calc
      liftFun F C (old F i x * old F i y) = liftFun F C (old F i (x * y)) :=
        congrArg (liftFun F C) ((old F i).map_mul x y).symm
      _ = liftFun F C (old F i x) * liftFun F C (old F i y) :=
        (C.ι.app i).map_mul x y

theorem lift_conservative : Conservative (liftMonoidHom F C) where
  injective := by
    intro x y
    obtain ⟨i,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ (transition F) x y
    intro h
    exact congrArg (old F i) ((C.ι.app i).conservative.injective h)
  factors := by
    intro x y z
    obtain ⟨i,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ (transition F) x y
    intro h
    obtain ⟨t,ht⟩ := (C.ι.app i).conservative.factors x y z h
    exact ⟨old F i t,ht⟩
  intersections := by
    intro x y j hj z
    obtain ⟨i,x,y,j,rfl,rfl,rfl⟩ := DirectLimit.exists_eq_mk₃ (transition F) x y j
    have hj' : ∀ t : F.obj i, x ∣ t ∧ y ∣ t ↔ j ∣ t := by
      intro t
      have h := hj (old F i t)
      change old F i x ∣ old F i t ∧ old F i y ∣ old F i t ↔ old F i j ∣ old F i t at h
      simpa only [old, ConservativeLimit.of_dvd_iff (transition F) (conservative F)] using h
    exact (C.ι.app i).conservative.intersections x y j hj' z
  common := by
    intro x y
    obtain ⟨i,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ (transition F) x y
    intro h
    obtain ⟨z,hx,hy⟩ := (C.ι.app i).conservative.common x y h
    exact ⟨old F i z,(old F i).map_dvd hx,(old F i).map_dvd hy⟩

def lift : object F ⟶ C.pt where
  toMonoidHom := liftMonoidHom F C
  conservative := lift_conservative F C
  map_e := (C.ι.app (Classical.arbitrary J)).map_e
  height x := by
    obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk (transition F) x
    exact (C.ι.app i).height x
  cost x := by
    obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk (transition F) x
    exact (C.ι.app i).cost x
  supremum x y := by
    obtain ⟨i,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ (transition F) x y
    exact ((C.ι.app i).supremum x y).trans ((inclusion F i).supremum x y).symm

def isColimit : IsColimit (cocone F) where
  desc C := lift F C
  fac C i := by apply Hom.ext; intro x; rfl
  uniq C m hm := by
    apply Hom.ext
    intro x
    obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk (transition F) x
    exact congrArg (fun f : F.obj i ⟶ C.pt => f x) (hm i)

end DirectedColimit

instance instHasColimitsOfShapeObjectOfIsDirectedOrderOfNonempty {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J] :
    HasColimitsOfShape J Object.{u} where
  has_colimit F := ⟨⟨⟨DirectedColimit.cocone F, DirectedColimit.isColimit F⟩⟩⟩

end
end PartitionConsistency.MonoidConstruction


/-! ## Iteration -/

namespace PartitionConsistency.ConstructionIteration
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v w u₂ v₂ w₂

section ProductColimits
variable {C : Type u} {D : Type u₂} [Category.{v} C] [Category.{v₂} D]
  {I : Type w} [Category.{w₂} I] (F : I ⥤ C × D)

def pairCocone (c : Cocone (F ⋙ CategoryTheory.Prod.fst C D))
    (d : Cocone (F ⋙ CategoryTheory.Prod.snd C D)) : Cocone F where
  pt := (c.pt, d.pt)
  ι := {
    app i := (c.ι.app i, d.ι.app i)
    naturality i j f := by
      apply Prod.ext
      · exact c.ι.naturality f
      · exact d.ι.naturality f }

def isColimitPair {c : Cocone (F ⋙ CategoryTheory.Prod.fst C D)}
    {d : Cocone (F ⋙ CategoryTheory.Prod.snd C D)} (hc : IsColimit c) (hd : IsColimit d) :
    IsColimit (pairCocone F c d) where
  desc s := (hc.desc ((CategoryTheory.Prod.fst C D).mapCocone s),
    hd.desc ((CategoryTheory.Prod.snd C D).mapCocone s))
  fac _ i := Prod.ext (hc.fac _ i) (hd.fac _ i)
  uniq s m hm := Prod.ext (hc.uniq ((CategoryTheory.Prod.fst C D).mapCocone s) m.1 (fun i => congrArg Prod.fst (hm i)))
    (hd.uniq ((CategoryTheory.Prod.snd C D).mapCocone s) m.2 (fun i => congrArg Prod.snd (hm i)))

def isColimitFst {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((CategoryTheory.Prod.fst C D).mapCocone c) where
  desc s := (hc.desc (pairCocone F s ((CategoryTheory.Prod.snd C D).mapCocone c))).1
  fac s i := congrArg Prod.fst (hc.fac _ i)
  uniq s m hm := by
    have h := hc.uniq (pairCocone F s ((CategoryTheory.Prod.snd C D).mapCocone c))
      (m, 𝟙 c.pt.2) (fun i => Prod.ext (hm i) (Category.comp_id _))
    exact congrArg Prod.fst h

def isColimitSnd {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((CategoryTheory.Prod.snd C D).mapCocone c) where
  desc s := (hc.desc (pairCocone F ((CategoryTheory.Prod.fst C D).mapCocone c) s)).2
  fac s i := congrArg Prod.snd (hc.fac _ i)
  uniq s m hm := by
    have h := hc.uniq (pairCocone F ((CategoryTheory.Prod.fst C D).mapCocone c) s)
      (𝟙 c.pt.1, m) (fun i => Prod.ext (Category.comp_id _) (hm i))
    exact congrArg Prod.snd h

instance instHasColimitsOfShapeProd_solutions [HasColimitsOfShape I C] [HasColimitsOfShape I D] :
    HasColimitsOfShape I (C × D) where
  has_colimit F := ⟨⟨⟨pairCocone F (colimit.cocone _) (colimit.cocone _),
    isColimitPair F (colimit.isColimit _) (colimit.isColimit _)⟩⟩⟩

instance instPreservesColimitsOfShapeProdFst_solutions : PreservesColimitsOfShape I (CategoryTheory.Prod.fst C D) where
  preservesColimit := { preserves hc := ⟨isColimitFst _ hc⟩ }

instance instPreservesColimitsOfShapeProdSnd_solutions : PreservesColimitsOfShape I (CategoryTheory.Prod.snd C D) where
  preservesColimit := { preserves hc := ⟨isColimitSnd _ hc⟩ }

end ProductColimits


/-- Stage-indexed iteration. The second factor records the actual stage;
limits take its supremum, rather than skipping pending operations. -/
structure Step {C : Type u} [Category.{v} C] (X : C) where
  target : C
  map : X ⟶ target

variable {C : Type u} [Category.{v} C]
  {J : Type w} [CompleteLinearOrder J] [SuccOrder J] [WellFoundedLT J]
  [HasIterationOfShape J C]

instance instHasIterationOfShapeProd_solutions : HasIterationOfShape J (C × J) where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

instance instPreservesWellOrderContinuousOfShapeProdFst_solutions : PreservesWellOrderContinuousOfShape J (CategoryTheory.Prod.fst C J) where
instance instPreservesWellOrderContinuousOfShapeProdSnd_solutions : PreservesWellOrderContinuousOfShape J (CategoryTheory.Prod.snd C J) where

variable (X₀ : C) (next : J → (X : C) → Step X)

def structureWithTime : CategoryTheory.SmallObject.SuccStruct (C × J) where
  X₀ := (X₀, ⊥)
  succ X := ((next X.2 X.1).target, Order.succ X.2)
  toSucc X := ((next X.2 X.1).map, homOfLE (Order.le_succ X.2))

abbrev fullFunctor : J ⥤ C × J := (structureWithTime X₀ next).iterationFunctor J
abbrev functor : J ⥤ C := fullFunctor X₀ next ⋙ CategoryTheory.Prod.fst C J
abbrev timeFunctor : J ⥤ J := fullFunctor X₀ next ⋙ CategoryTheory.Prod.snd C J

theorem time (j : J) : ((fullFunctor X₀ next).obj j).2 = j := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl : j = ⊥ := by simpa using hj
    exact ((CategoryTheory.Prod.snd C J).mapIso
      ((structureWithTime X₀ next).iterationFunctorObjBotIso J)).to_eq
  | succ j hj ih =>
    have h := ((CategoryTheory.Prod.snd C J).mapIso
      ((structureWithTime X₀ next).iterationFunctorObjSuccIso j hj)).to_eq
    exact h.trans (congrArg Order.succ ih)
  | isSuccLimit j hj ih =>
    have hc := (timeFunctor X₀ next).isColimitOfIsWellOrderContinuous j hj
    have hl := Preorder.isLUB_of_isColimit _ hc
    have hr : Set.range (((Set.principalSegIio j).monotone.functor ⋙
        timeFunctor X₀ next).obj) = Set.Iio j := by
      ext k
      constructor
      · rintro ⟨⟨i,hi⟩,rfl⟩
        change ((fullFunctor X₀ next).obj i).2 < j
        rw [ih i hi]
        exact hi
      · intro hk
        exact ⟨⟨k,hk⟩, ih k hk⟩
    rw [hr] at hl
    exact hl.unique hj.isLUB_Iio

def botIso : (functor X₀ next).obj ⊥ ≅ X₀ :=
  (CategoryTheory.Prod.fst C J).mapIso ((structureWithTime X₀ next).iterationFunctorObjBotIso J)

def succIso (j : J) (hj : ¬IsMax j) :
    (functor X₀ next).obj (Order.succ j) ≅ (next j ((functor X₀ next).obj j)).target :=
  (CategoryTheory.Prod.fst C J).mapIso ((structureWithTime X₀ next).iterationFunctorObjSuccIso j hj) ≪≫
    eqToIso (congrArg (fun i => (next i ((functor X₀ next).obj j)).target) (time X₀ next j))

theorem map_succ (j : J) (hj : ¬IsMax j) :
    (functor X₀ next).map (homOfLE (Order.le_succ j)) =
      (next j ((functor X₀ next).obj j)).map ≫ (succIso X₀ next j hj).inv := by
  have h := congrArg ((CategoryTheory.Prod.fst C J).map)
    ((structureWithTime X₀ next).iterationFunctor_map_succ j hj)
  dsimp only [Functor.comp_map, functor]
  rw [h]
  dsimp [succIso]
  have hn (i k : J) (h : i = k) (X : C) :
      (next i X).map = (next k X).map ≫
        (eqToIso (congrArg (fun i => (next i X).target) h)).inv := by
    cases h
    simp
  change (next ((fullFunctor X₀ next).obj j).2 ((fullFunctor X₀ next).obj j).1).map ≫ _ = _
  rw [hn _ _ (time X₀ next j)]
  exact Category.assoc _ _ _


end
end PartitionConsistency.ConstructionIteration

namespace PartitionConsistency.MonoidConstruction
open CategoryTheory CategoryTheory.Limits
universe u

instance instHasIterationOfShapeObjectOfNonempty {J : Type u} [LinearOrder J] [Nonempty J] : HasIterationOfShape J Object.{u} where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hj.nonempty_Iio.to_subtype
    infer_instance

end PartitionConsistency.MonoidConstruction

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_MonoidRounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Schedule -/

namespace PartitionConsistency.MonoidConstruction
universe u
open CategoryTheory CategoryTheory.Limits DiagramOrder
noncomputable section

namespace ProbeData
variable {M N : Object.{u}}
/-- Transport parameters, not profile conclusions, from the starting stage. -/
def map (d : ProbeData M) (f : M ⟶ N) : ProbeData N where
  a := f d.a
  b := f d.b
  b_ne_one h := d.b_ne_one (f.injective (h.trans f.map_one.symm))
  path := d.path.map f.toMonoidHom

@[simp] theorem map_a (d : ProbeData M) (f : M ⟶ N) : (d.map f).a = f d.a := rfl
@[simp] theorem map_b (d : ProbeData M) (f : M ⟶ N) : (d.map f).b = f d.b := rfl
@[simp] theorem map_node (d : ProbeData M) (f : M ⟶ N) (i : ℕ) :
    (d.map f).path.node i = f (d.path.node i) := rfl
end ProbeData

namespace MergerData
variable {M N : Object.{u}}
def map (d : MergerData M) (f : M ⟶ N) : MergerData N where
  n := d.n
  positive := d.positive
  prescription := d.prescription.map f.toMonoidHom
  valid := (d.prescription.valid_map_iff M.joins f.conservative).2 d.valid
end MergerData

/-- The two actual operations to execute in a round. -/
abbrev Request (M : Object.{u}) := ProbeData M ⊕ MergerData M

namespace Request
variable {M N : Object.{u}}
def map : Request M → (M ⟶ N) → Request N
  | .inl d, f => .inl (d.map f)
  | .inr d, f => .inr (d.map f)

def target : Request M → Object.{u}
  | .inl d => d.extension
  | .inr d => d.extension

def inclusion : (d : Request M) → M ⟶ d.target
  | .inl d => d.inclusion
  | .inr d => d.inclusion

theorem cardinal_le (d : Request M) {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hM : Cardinal.mk M ≤ μ) : Cardinal.mk d.target ≤ μ := by
  cases d with
  | inl d => exact d.cardinal_le hω hM
  | inr d => exact d.cardinal_le hω hM

theorem gates (d : Request M) : HasOldGates d.inclusion.toMonoidHom := by
  cases d with
  | inl d => exact d.gates
  | inr d => exact d.gates

theorem preserves_profile (d : Request M) {a b e m : M} {n : ℕ → M}
    (h : ProbeProfile a b e m n) : ProbeProfile (d.inclusion a) (d.inclusion b)
      (d.inclusion e) (d.inclusion m) (fun i => d.inclusion (n i)) :=
  h.map d.inclusion.conservative d.gates

end Request

instance instHasIterationOfShapeUnderObjectOfNonempty {J : Type u} [LinearOrder J] [Nonempty J] (M : Object.{u}) :
    HasIterationOfShape J (Under M) where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hj.nonempty_Iio.to_subtype
    have : IsFiltered (Set.Iio j) := inferInstance
    have : IsConnected (Set.Iio j) := IsFiltered.isConnected _
    infer_instance

instance instPreservesWellOrderContinuousOfShapeUnderObjectForgetOfNonempty {J : Type u} [LinearOrder J] [Nonempty J] (M : Object.{u}) :
    PreservesWellOrderContinuousOfShape J (Under.forget M) where
  preservesColimitsOfShape j hj := by
    have := hj.nonempty_Iio.to_subtype
    have : IsFiltered (Set.Iio j) := inferInstance
    have : IsConnected (Set.Iio j) := IsFiltered.isConnected _
    infer_instance

namespace Round
variable {J : Type u} [CompleteLinearOrder J] [SuccOrder J] [WellFoundedLT J]
  (M : Object.{u}) (schedule : J → Request M)

def step (j : J) (X : Under M) : ConstructionIteration.Step X where
  target := Under.mk (X.hom ≫ ((schedule j).map X.hom).inclusion)
  map := Under.homMk ((schedule j).map X.hom).inclusion

abbrev underFunctor : J ⥤ Under M :=
  ConstructionIteration.functor (Under.mk (𝟙 M)) (step M schedule)

abbrev functor : J ⥤ Object.{u} := underFunctor M schedule ⋙ Under.forget M

/-- Each stage has the same specified conservative map from the round's base. -/
def fromBase (j : J) : M ⟶ (functor M schedule).obj j := (underFunctor M schedule).obj j |>.hom

@[simp] theorem fromBase_naturality {i j : J} (h : i ≤ j) :
    fromBase M schedule i ≫ (functor M schedule).map (homOfLE h) = fromBase M schedule j :=
  ((underFunctor M schedule).map (homOfLE h)).w

def botIso : (functor M schedule).obj ⊥ ≅ M :=
  (Under.forget M).mapIso (ConstructionIteration.botIso (Under.mk (𝟙 M)) (step M schedule))

def succIso (j : J) (hj : ¬ IsMax j) :
    (functor M schedule).obj (Order.succ j) ≅
      ((schedule j).map (fromBase M schedule j)).target :=
  (Under.forget M).mapIso
    (ConstructionIteration.succIso (Under.mk (𝟙 M)) (step M schedule) j hj)

theorem map_succ (j : J) (hj : ¬ IsMax j) :
    (functor M schedule).map (homOfLE (Order.le_succ j)) =
      ((schedule j).map (fromBase M schedule j)).inclusion ≫ (succIso M schedule j hj).inv :=
  congrArg (Under.forget M).map
    (ConstructionIteration.map_succ (Under.mk (𝟙 M)) (step M schedule) j hj)

end Round
end
end PartitionConsistency.MonoidConstruction


/-! ## LimitProperties -/

namespace PartitionConsistency.MonoidConstruction
universe u
open CategoryTheory CategoryTheory.Limits DiagramOrder
noncomputable section

@[simp] theorem comp_apply {M N R : Object.{u}} (f : M ⟶ N) (g : N ⟶ R) (x : M) :
    (f ≫ g) x = g (f x) := rfl
@[simp] theorem identity_apply (M : Object.{u}) (x : M) : (𝟙 M) x = x := rfl

/-- The underlying equivalence of stages of a construction isomorphism. -/
def isoEquiv {M N : Object.{u}} (e : M ≅ N) : M ≃ N where
  toFun := e.hom
  invFun := e.inv
  left_inv x := congrArg (fun f : M ⟶ M => f x) e.hom_inv_id
  right_inv x := congrArg (fun f : N ⟶ N => f x) e.inv_hom_id

/-- A genuine property of a transition, not a field assumed at arbitrary limits. -/
def PreservesProfiles {M N : Object.{u}} (f : M ⟶ N) : Prop :=
  ∀ (a b e m : M) (n : ℕ → M), ProbeProfile a b e m n →
    ProbeProfile (f a) (f b) (f e) (f m) (fun i => f (n i))

namespace PreservesProfiles
variable {M N R : Object.{u}}
theorem id (M : Object.{u}) : PreservesProfiles (𝟙 M) := by intro a b e m n h; exact h

theorem comp {f : M ⟶ N} {g : N ⟶ R} (hf : PreservesProfiles f) (hg : PreservesProfiles g) :
    PreservesProfiles (f ≫ g) := by
  intro a b e m n h
  exact hg _ _ _ _ _ (hf _ _ _ _ _ h)

theorem of_surjective {f : M ⟶ N} (hf : Function.Surjective f) : PreservesProfiles f := by
  intro a b e m n h
  exact h.map f.conservative (fun x _ => Or.inl (hf x))

theorem of_iso (e : M ≅ N) : PreservesProfiles e.hom :=
  of_surjective (isoEquiv e).surjective

theorem operation (d : Request M) : PreservesProfiles d.inclusion := by
  intro a b e m n h
  exact d.preserves_profile h
end PreservesProfiles

namespace DirectedColimit
variable {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]
  (F : J ⥤ Object.{u})
  {C : Cocone F} (hc : IsColimit C)
include hc

/-- Any colimit in the stage category is a union of its stages as a monoid. -/
theorem exists_rep (y : C.pt) : ∃ i : J, ∃ x : F.obj i, C.ι.app i x = y := by
  let e := (isColimit F).coconePointUniqueUpToIso hc
  obtain ⟨i,x,hx⟩ := DirectLimit.exists_eq_mk (transition F) (e.inv y)
  refine ⟨i,x,?_⟩
  have he : inclusion F i ≫ e.hom = C.ι.app i :=
    (isColimit F).comp_coconePointUniqueUpToIso_hom hc i
  have h := congrArg e.hom hx.symm
  change e.hom (inclusion F i x) = e.hom (e.inv y) at h
  change (inclusion F i ≫ e.hom) x = (e.inv ≫ e.hom) y at h
  simpa only [he, e.inv_hom_id, identity_apply] using h

theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ) (hJ : Cardinal.mk J ≤ μ)
    (hF : ∀ i, Cardinal.mk (F.obj i) ≤ μ) : Cardinal.mk C.pt ≤ μ := by
  let e := (isColimit F).coconePointUniqueUpToIso hc
  rw [← Cardinal.mk_congr (isoEquiv e)]
  exact ConservativeLimit.cardinal_le (transition F) hω hJ hF

theorem profile (i : J) (a b e m : F.obj i) (n : ℕ → F.obj i)
    (hP : ∀ j (hij : i ≤ j), ProbeProfile
      (F.map (homOfLE hij) a) (F.map (homOfLE hij) b) (F.map (homOfLE hij) e)
      (F.map (homOfLE hij) m) (fun k => F.map (homOfLE hij) (n k))) :
    ProbeProfile (C.ι.app i a) (C.ι.app i b) (C.ι.app i e)
      (C.ι.app i m) (fun k => C.ι.app i (n k)) := by
  have h := ConservativeLimit.probeProfile (transition F) (conservative F) i a b e m n hP
  let φ := (isColimit F).coconePointUniqueUpToIso hc
  have h' := PreservesProfiles.of_iso φ _ _ _ _ _ h
  have he : inclusion F i ≫ φ.hom = C.ι.app i :=
    (isColimit F).comp_coconePointUniqueUpToIso_hom hc i
  change ProbeProfile ((inclusion F i ≫ φ.hom) a) ((inclusion F i ≫ φ.hom) b)
    ((inclusion F i ≫ φ.hom) e) ((inclusion F i ≫ φ.hom) m)
    (fun k => (inclusion F i ≫ φ.hom) (n k)) at h'
  simpa only [he] using h'

end DirectedColimit

namespace ContinuousTower
variable {J : Type u} [CompleteLinearOrder J] [SuccOrder J] [WellFoundedLT J]
  (F : J ⥤ Object.{u}) [F.IsWellOrderContinuous]

omit [SuccOrder J] [WellFoundedLT J] in
/-- Every tested element at a limit is already present at a strict earlier cut. -/
theorem exists_rep {j : J} (hj : Order.IsSuccLimit j) (x : F.obj j) :
    ∃ i : J, ∃ hij : i < j, ∃ a : F.obj i, F.map (homOfLE hij.le) a = x := by
  have := hj.nonempty_Iio.to_subtype
  obtain ⟨i,a,ha⟩ := DirectedColimit.exists_rep _ (F.isColimitOfIsWellOrderContinuous j hj) x
  exact ⟨i.1,i.2,a,ha⟩

/-- Successor persistence together with continuity proves persistence through
arbitrary limits, without supposing that the path belongs to every stage. -/
theorem preservesProfiles
    (hsucc : ∀ j, ¬ IsMax j → PreservesProfiles (F.map (homOfLE (Order.le_succ j)))) :
    ∀ (i j : J) (hij : i ≤ j), PreservesProfiles (F.map (homOfLE hij)) := by
  intro i j
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    intro hij
    have he : i = j := le_antisymm hij (hj hij)
    subst i
    simpa using PreservesProfiles.id (F.obj j)
  | succ j hj ih =>
    intro hij
    rcases hij.eq_or_lt with he | he
    · subst i
      simpa using PreservesProfiles.id (F.obj (Order.succ j))
    · have hij' : i ≤ j := (Order.lt_succ_iff_of_not_isMax hj).1 he
      have h := (ih hij').comp (hsucc j hj)
      simpa only [← F.map_comp, homOfLE_comp] using h
  | isSuccLimit j hj ih =>
    intro hij
    rcases hij.eq_or_lt with he | he
    · subst i
      simpa using PreservesProfiles.id (F.obj j)
    · intro a b e m n h
      have := hj.nonempty_Iio.to_subtype
      apply DirectedColimit.profile ((Set.principalSegIio j).monotone.functor ⋙ F)
        (F.isColimitOfIsWellOrderContinuous j hj) ⟨i,he⟩ a b e m n
      intro k hik
      exact ih k.1 k.2 hik a b e m n h

/-- Size is bounded by the size of the stage index and the existing operation
bounds. The colimit bound is a consequence, not an extra construction input. -/
theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ) (hJ : Cardinal.mk J ≤ μ)
    (h₀ : Cardinal.mk (F.obj ⊥) ≤ μ)
    (hsucc : ∀ j, ¬ IsMax j → Cardinal.mk (F.obj j) ≤ μ →
      Cardinal.mk (F.obj (Order.succ j)) ≤ μ) (j : J) : Cardinal.mk (F.obj j) ≤ μ := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    have he : j = ⊥ := by simpa using hj
    rw [he]
    exact h₀
  | succ j hj ih => exact hsucc j hj ih
  | isSuccLimit j hj ih =>
    have := hj.nonempty_Iio.to_subtype
    apply DirectedColimit.cardinal_le _ (F.isColimitOfIsWellOrderContinuous j hj) hω
    · exact (Cardinal.mk_subtype_le _).trans hJ
    · intro i; exact ih i.1 i.2

end ContinuousTower
end
end PartitionConsistency.MonoidConstruction


/-! ## Round -/

namespace PartitionConsistency.MonoidConstruction
universe u
open CategoryTheory CategoryTheory.Limits DiagramOrder
noncomputable section

namespace ProbeData
variable {M : Object.{u}} (d : ProbeData M)

theorem probe_gate : OldGate d.inclusion.toMonoidHom d.probe (d.a * M.e) := by
  have hg := d.path.probe_zero_gate M.e_ne_one d.b d.b_ne_one
  refine ⟨ProbeAlgebra.Word.Gate.dvd _ _ hg,ProbeAlgebra.Word.Gate.dvd_old_iff _ _ hg,?_⟩
  intro x hx z
  change (d.probe ∣ z ∧ ProbeAlgebra.Word.old (d.path.alphabet M.e_ne_one) d.b x ∣ z) ↔
    ProbeAlgebra.Word.old (d.path.alphabet M.e_ne_one) d.b (d.a * M.e) ∣ z ∧
      ProbeAlgebra.Word.old (d.path.alphabet M.e_ne_one) d.b x ∣ z
  simpa only [probe, and_comm] using! ProbeAlgebra.Word.Gate.old_intersection _ _ hg rfl
    (fun hd => hx ((ProbeAlgebra.Word.old_dvd_iff_headDiv _ _ x d.probe).2 hd)) z

/-- A previously inserted probe, not dividing `a`, meets the next probe
in exactly `ae`. This is why repeated requests give independent cones. -/
theorem independent (x : M) (hx : x ∣ d.a * M.e) (hxa : ¬ x ∣ d.a)
    (z : d.extension) : d.inclusion x ∣ z ∧ d.probe ∣ z ↔ d.inclusion (d.a * M.e) ∣ z := by
  have hxm : ¬ d.inclusion x ∣ d.probe := by
    intro h
    obtain ⟨i,hi⟩ := (d.path.probe_old_profile M.e_ne_one d.b d.b_ne_one x).1 h
    exact hxa (hi.trans (d.path.bounded i))
  have h := d.probe_gate.intersections x hxm z
  have hx' := d.inclusion.toMonoidHom.map_dvd hx
  constructor
  · intro hz; exact ((h).1 ⟨hz.2,hz.1⟩).1
  · intro hz
    have hm := d.probe_gate.divides.trans hz
    exact ⟨hx'.trans hz,hm⟩
end ProbeData

namespace Request
variable {M : Object.{u}}
theorem inclusion_eq_transport (d e : Request M) (h : d = e) :
    d.inclusion = e.inclusion ≫ (eqToIso (congrArg target h)).inv := by
  subst e
  simp
end Request

namespace Round
variable {J : Type u} [CompleteLinearOrder J] [SuccOrder J] [WellFoundedLT J]
  (M : Object.{u}) (schedule : J → Request M)

theorem bot_inv : (botIso M schedule).inv = fromBase M schedule ⊥ := by
  have h := (ConstructionIteration.botIso (Under.mk (𝟙 M)) (step M schedule)).inv.w
  change (𝟙 M) ≫ (botIso M schedule).inv = fromBase M schedule ⊥ at h
  simpa only [Category.id_comp] using h

theorem preservesProfiles (i j : J) (hij : i ≤ j) :
    PreservesProfiles ((functor M schedule).map (homOfLE hij)) := by
  apply ContinuousTower.preservesProfiles
  intro k hk
  rw [map_succ M schedule k hk]
  exact (PreservesProfiles.operation _).comp (PreservesProfiles.of_iso (succIso M schedule k hk).symm)

theorem fromBase_preservesProfiles (j : J) : PreservesProfiles (fromBase M schedule j) := by
  rw [← fromBase_naturality M schedule (bot_le : (⊥ : J) ≤ j), ← bot_inv]
  exact (PreservesProfiles.of_iso (botIso M schedule).symm).comp
    (preservesProfiles M schedule _ _ bot_le)

theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hJ : Cardinal.mk J ≤ μ) (hM : Cardinal.mk M ≤ μ) (j : J) :
    Cardinal.mk ((functor M schedule).obj j) ≤ μ := by
  apply ContinuousTower.cardinal_le _ hω hJ
  · rw [Cardinal.mk_congr (isoEquiv (botIso M schedule))]; exact hM
  · intro k hk h
    rw [Cardinal.mk_congr (isoEquiv (succIso M schedule k hk))]
    exact Request.cardinal_le _ hω h

end Round
end
end PartitionConsistency.MonoidConstruction


/-! ## Index -/

namespace PartitionConsistency.MonoidConstruction
universe u v
open CategoryTheory CategoryTheory.Limits DiagramOrder
noncomputable section
open scoped Classical

/-- A chosen well-order on a type of requests; nothing is quotiented or omitted. -/
def WellOrdered (A : Type u) := A
namespace WellOrdered
variable (A : Type u)
instance instLinearOrder : LinearOrder (WellOrdered A) := linearOrderOfSTO WellOrderingRel
instance instWellFoundedLT : WellFoundedLT (WellOrdered A) := ⟨WellOrderingRel.isWellOrder.wf⟩
instance instNonempty [Nonempty A] : Nonempty (WellOrdered A) := inferInstanceAs (Nonempty A)
instance instOrderBotOfNonempty [Nonempty A] : OrderBot (WellOrdered A) := WellFoundedLT.toOrderBot _
instance instConditionallyCompleteLinearOrderBotOfNonempty [Nonempty A] : ConditionallyCompleteLinearOrderBot (WellOrdered A) :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _
end WellOrdered

abbrev ScheduleIndex (A : Type u) := WithTop (WellOrdered A)
instance instWellFoundedLTScheduleIndex (A : Type u) : WellFoundedLT (ScheduleIndex A) := inferInstance
instance instSuccOrderScheduleIndex (A : Type u) : SuccOrder (ScheduleIndex A) := SuccOrder.ofLinearWellFoundedLT _

namespace Request
variable (M : Object.{u})
def defaultProbe : ProbeData M where
  a := 1
  b := M.e
  b_ne_one := M.e_ne_one
  path := ⟨fun _ => 1,rfl,fun _ => dvd_refl _,fun _ => dvd_refl _⟩
instance instNonempty : Nonempty (Request M) := ⟨.inl (defaultProbe M)⟩
end Request

end
end PartitionConsistency.MonoidConstruction

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_CompleteRounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## RequestSize -/
namespace PartitionConsistency.MonoidConstruction
universe u
noncomputable section
open scoped Classical

namespace ProbeData
variable {M : Object.{u}}
def code (d : ProbeData M) : M × M × (ℕ → M) := (d.a,d.b,d.path.node)
theorem code_injective : Function.Injective (code (M := M)) := by
  rintro ⟨a,b,hb,⟨n,h0,hi,ha⟩⟩ ⟨a',b',hb',⟨n',h0',hi',ha'⟩⟩ h
  obtain ⟨rfl,rfl,rfl⟩ := (Prod.mk.inj h).imp_right (fun h => Prod.mk.inj h)
  rfl

theorem data_cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hpow : μ ^ Cardinal.aleph0 = μ) (hM : Cardinal.mk M ≤ μ) :
    Cardinal.mk (ProbeData M) ≤ μ := by
  apply (Cardinal.mk_le_of_injective (code_injective (M := M))).trans
  simp only [Cardinal.mk_prod,Cardinal.mk_arrow,Cardinal.mk_nat,Cardinal.lift_id,Cardinal.lift_id',
    Cardinal.lift_aleph0]
  have hp : Cardinal.mk M ^ Cardinal.aleph0 ≤ μ := by
    rw [← hpow]; exact Cardinal.power_le_power_right hM
  exact (mul_le_mul' hM (mul_le_mul' hM hp)).trans_eq
    (by rw [Cardinal.mul_eq_self hω,Cardinal.mul_eq_self hω])
end ProbeData

namespace MergerData
variable {M : Object.{u}}
def code (d : MergerData M) : Σ n : ℕ, Fin n → Fin n → Option (M × M) :=
  ⟨d.n,d.prescription.start⟩

theorem code_injective : Function.Injective (code (M := M)) := by
  rintro ⟨n,hn,⟨p⟩,hp⟩ ⟨n',hn',⟨p'⟩,hp'⟩ h
  have hn : n = n' := congrArg Sigma.fst h
  subst n'
  have hh : p = p' := eq_of_heq (Sigma.mk.inj h).2
  subst p'
  rfl

theorem data_cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hpow : μ ^ Cardinal.aleph0 = μ) (hM : Cardinal.mk M ≤ μ) :
    Cardinal.mk (MergerData M) ≤ μ := by
  have hμ : μ ≠ 0 := ne_of_gt (Cardinal.aleph0_pos.trans_le hω)
  have hu : Cardinal.mk (Option (M × M)) ≤ μ := by
    simp only [Cardinal.mk_option,Cardinal.mk_prod,Cardinal.lift_id]
    exact (add_le_add ((mul_le_mul' hM hM).trans_eq (Cardinal.mul_eq_self hω))
      (Cardinal.one_le_aleph0.trans hω)).trans_eq (Cardinal.add_eq_self hω)
  have hn (n : ℕ) : Cardinal.mk (Fin n → Fin n → Option (M × M)) ≤ μ := by
    have hf : Cardinal.lift.{u} (Cardinal.mk (Fin n)) ≤ μ :=
      (Cardinal.lift_le.2 Cardinal.mk_le_aleph0).trans (by simpa using hω)
    have hfω : Cardinal.lift.{u} (Cardinal.mk (Fin n)) ≤ Cardinal.aleph0 := by
      simp
    have h : (Cardinal.mk (Option (M × M))) ^ Cardinal.lift.{u} (Cardinal.mk (Fin n)) ≤ μ :=
      ((Cardinal.power_le_power_right hu).trans (Cardinal.power_le_power_left hμ hfω)).trans_eq hpow
    simp only [Cardinal.mk_arrow,Cardinal.lift_id']
    exact ((Cardinal.power_le_power_right h).trans
      (Cardinal.power_le_power_left hμ hfω)).trans_eq hpow
  apply (Cardinal.mk_le_of_injective (code_injective (M := M))).trans
  rw [Cardinal.mk_sigma]
  apply (Cardinal.sum_le_sum _ (fun _ : ℕ => μ) hn).trans
  simpa only [Cardinal.sum_const,Cardinal.mk_nat,Cardinal.lift_aleph0,
    Cardinal.lift_id',Cardinal.lift_umax,Cardinal.mul_eq_self hω] using (mul_le_mul_left hω μ)
end MergerData

namespace Request
variable {M : Object.{u}}
theorem data_cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hpow : μ ^ Cardinal.aleph0 = μ) (hM : Cardinal.mk M ≤ μ) :
    Cardinal.mk (Request M) ≤ μ := by
  rw [Cardinal.mk_sum]
  simp only [Cardinal.lift_id]
  exact (add_le_add (ProbeData.data_cardinal_le hω hpow hM)
    (MergerData.data_cardinal_le hω hpow hM)).trans_eq (Cardinal.add_eq_self hω)
end Request
end
end PartitionConsistency.MonoidConstruction


/-! ## MergerPersistence -/
namespace PartitionConsistency
universe u v
noncomputable section
open scoped Classical
open DiagramOrder

namespace MergerAlgebra.Word
variable {M : Type u} {D : Type v} [LeftCancelMonoid M] [IsConical M]
  [RightFreeAction M D]
omit [IsConical M] in
/-- Disjoint terminal-letter cones give disjoint cones with any fixed prefix. -/
theorem snoc_cones_disjoint (w : Word M D) (s t : D)
    (hst : ∀ d : D, ¬ (RightFreeAction.Reaches M s d ∧ RightFreeAction.Reaches M t d))
    (z : Word M D) : ¬ (snoc w s ∣ z ∧ snoc w t ∣ z) := by
  induction z with
  | old x => simp only [snoc_not_dvd_old,false_and,not_false_eq_true]
  | snoc z d ih =>
    simp only [snoc_dvd_snoc_iff]
    by_cases hw : w = z
    · subst z
      simpa only [snoc_not_dvd_prefix,true_and,false_or] using hst d
    · simpa only [hw,false_and,or_false] using ih
end MergerAlgebra.Word

namespace DiagramForcing.OverlapPrescription
variable {M : Type u} [LeftCancelMonoid M] {n : ℕ}
/-- The cone form of exact realization. Unlike checking only old right factors,
this form persists under arbitrary conservative embeddings. -/
def RootSystem (P : OverlapPrescription M n) (l : Fin n → M) : Prop :=
  ∀ i j, i ≠ j → match P.start i j with
    | none => ∀ z : M, ¬ (l i ∣ z ∧ l j ∣ z)
    | some (a,b) => l i * a = l j * b ∧ ∀ z : M, l i ∣ z ∧ l j ∣ z ↔ l i * a ∣ z

namespace RootSystem
variable {P : OverlapPrescription M n} {l : Fin n → M}
theorem map {N : Type v} [LeftCancelMonoid N] {f : M →* N} (hf : Conservative f)
    (h : P.RootSystem l) : (P.map f).RootSystem (fun i => f (l i)) := by
  intro i j hij
  have h := h i j hij
  cases he : P.start i j with
  | none =>
    simp only [map_start,he,Option.map_none]
    intro z hz
    obtain ⟨x,hx⟩ := hf.common (l i) (l j) ⟨z,hz⟩
    exact (he ▸ h) x hx
  | some ab =>
    obtain ⟨a,b⟩ := ab
    simp only [he] at h
    simp only [map_start,he,Option.map_some]
    exact ⟨by simpa only [f.map_mul] using congrArg f h.1,
      fun z => by simpa only [f.map_mul] using hf.intersections (l i) (l j) (l i * a) h.2 z⟩

theorem realization (h : P.RootSystem l) (z w : Fin n × M) :
    l z.1 * z.2 = l w.1 * w.2 ↔ P.Rel z w := by
  obtain ⟨i,x⟩ := z; obtain ⟨j,y⟩ := w
  by_cases hij : i = j
  · subst j
    simp only [rel_same_copy,mul_left_cancel_iff]
  · have hspec := h i j hij
    simp only [Rel,hij,↓reduceIte]
    cases he : P.start i j with
    | none =>
      simp only
      constructor
      · intro heq
        exact (he ▸ hspec) (l i * x) ⟨dvd_mul_right _ _,heq.symm ▸ dvd_mul_right (l j) y⟩
      · exact False.elim
    | some ab =>
      obtain ⟨a,b⟩ := ab
      simp only [he] at hspec ⊢
      constructor
      · intro heq
        obtain ⟨t,ht⟩ := (hspec.2 (l i * x)).1
          ⟨dvd_mul_right _ _,heq.symm ▸ dvd_mul_right (l j) y⟩
        refine ⟨t,mul_left_cancel (ht.trans (mul_assoc _ _ _)),?_⟩
        apply mul_left_cancel (a := l j)
        rw [← heq,ht,hspec.1,mul_assoc]
      · rintro ⟨t,rfl,rfl⟩
        rw [← mul_assoc,hspec.1,mul_assoc]
end RootSystem

variable [IsConical M]
open MergerAlgebra MergerAlgebra.RightFreeAction
omit [IsConical M] in
/-- A literal merger realizes prescribed cones in its entire normal-form monoid,
not only at the old factors. -/
theorem root_system (P : OverlapPrescription M n) (hP : P.Valid) :
    (P.map (Word.oldHom : M →* P.Merger hP)).RootSystem (P.root hP) := by
  intro i j hij
  cases he : P.start i j with
  | none =>
    simp only [map_start,he,Option.map_none]
    apply Word.snoc_cones_disjoint
    rintro d ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    have h := (P.copy_eq_iff hP i j (1*x) (1*y)).1 (hx.trans hy.symm)
    simp only [Rel,hij,↓reduceIte,he] at h
  | some ab =>
    obtain ⟨a,b⟩ := ab
    simp only [map_start,he,Option.map_some]
    refine ⟨(P.root_mul_eq_iff hP (i,a) (j,b)).2 ?_,?_⟩
    · simp only [Rel,hij,↓reduceIte,he]
      exact ⟨1,(mul_one _).symm,(mul_one _).symm⟩
    · have hletters (z : P.Copies hP) :
          Reaches M (P.copy hP i 1) z ∧ Reaches M (P.copy hP j 1) z ↔
            Reaches M (P.copy hP i a) z := by
        rw [P.overlap_cone_intersection hP hij he]
        constructor
        · rintro ⟨t,_,_,hz⟩
          exact ⟨t,hz.symm⟩
        · rintro ⟨t,ht⟩
          exact ⟨t,one_dvd _,one_dvd _,ht.symm⟩
      intro z
      change P.root hP i ∣ z ∧ P.root hP j ∣ z ↔ P.root hP i * Word.old a ∣ z
      rw [root_mul_old]
      exact Word.snoc_cone_intersection (Word.old (1 : M)) _ _ _ hletters z

end DiagramForcing.OverlapPrescription

namespace MonoidConstruction.MergerData
variable {M : MonoidConstruction.Object.{u}} (d : MonoidConstruction.MergerData M)
theorem cone_realization : (d.prescription.map d.inclusion.toMonoidHom).RootSystem d.root :=
  d.prescription.root_system d.valid
end MonoidConstruction.MergerData
end
end PartitionConsistency


/-! ## RoundExecution -/
namespace PartitionConsistency
universe u v w
open CategoryTheory CategoryTheory.Limits DiagramOrder
noncomputable section
open scoped Classical
namespace DiagramForcing.OverlapPrescription
variable {M : Type u} {N : Type v} {R : Type w} [Monoid M] [Monoid N] [Monoid R]
@[simp] theorem map_comp {n : ℕ} (P : OverlapPrescription M n) (f : M →* N) (g : N →* R) :
    (P.map f).map g = P.map (g.comp f) := by
  apply OverlapPrescription.mk.injEq _ _ |>.mpr
  funext i j
  cases h : P.start i j <;> simp [map_start,h]
end DiagramForcing.OverlapPrescription

namespace MonoidConstruction.Round
variable {J : Type u} [CompleteLinearOrder J] [SuccOrder J] [WellFoundedLT J]
  (M : Object.{u}) (schedule : J → Request M)

/-- Identification of the next stage with the actual operation's normal forms. -/
def requestIso (j : J) (hj : ¬IsMax j) (d : Request M) (hd : schedule j = d) :
    (functor M schedule).obj (Order.succ j) ≅ (d.map (fromBase M schedule j)).target :=
  succIso M schedule j hj ≪≫ eqToIso (by rw [hd])

theorem map_succ_request (j : J) (hj : ¬IsMax j) (d : Request M) (hd : schedule j = d) :
    (functor M schedule).map (homOfLE (Order.le_succ j)) =
      (d.map (fromBase M schedule j)).inclusion ≫ (requestIso M schedule j hj d hd).inv := by
  rw [map_succ M schedule j hj]
  dsimp only [requestIso,Iso.trans_inv]
  rw [← Category.assoc]
  congr 1
  exact Request.inclusion_eq_transport _ _ (congrArg (fun r => r.map (fromBase M schedule j)) hd)

def afterRequestMap (j : J) (hj : ¬IsMax j) (d : Request M) (hd : schedule j = d)
    (k : J) (hjk : Order.succ j ≤ k) :
    (d.map (fromBase M schedule j)).target ⟶ (functor M schedule).obj k :=
  (requestIso M schedule j hj d hd).inv ≫ (functor M schedule).map (homOfLE hjk)

theorem inclusion_afterRequestMap (j : J) (hj : ¬IsMax j) (d : Request M) (hd : schedule j = d)
    (k : J) (hjk : Order.succ j ≤ k) :
    (d.map (fromBase M schedule j)).inclusion ≫ afterRequestMap M schedule j hj d hd k hjk =
      (functor M schedule).map (homOfLE ((Order.le_succ j).trans hjk)) := by
  dsimp only [afterRequestMap]
  rw [← Category.assoc,← map_succ_request,← Functor.map_comp,homOfLE_comp]

theorem fromBase_afterRequestMap (j : J) (hj : ¬IsMax j) (d : Request M) (hd : schedule j = d)
    (k : J) (hjk : Order.succ j ≤ k) (x : M) :
    afterRequestMap M schedule j hj d hd k hjk
      ((d.map (fromBase M schedule j)).inclusion (fromBase M schedule j x)) =
        fromBase M schedule k x := by
  change (fromBase M schedule j ≫ (d.map (fromBase M schedule j)).inclusion ≫
    afterRequestMap M schedule j hj d hd k hjk) x = _
  rw [inclusion_afterRequestMap,fromBase_naturality]

theorem afterRequestMap_preservesProfiles (j : J) (hj : ¬IsMax j) (d : Request M) (hd : schedule j = d)
    (k : J) (hjk : Order.succ j ≤ k) :
    PreservesProfiles (afterRequestMap M schedule j hj d hd k hjk) :=
  (PreservesProfiles.of_iso (requestIso M schedule j hj d hd).symm).comp
    (preservesProfiles M schedule _ _ hjk)

/-- Each scheduled finite merger stays exact at every subsequent cut,
including for the new right factors at that cut. -/
theorem creates_merger (j : J) (hj : ¬IsMax j) (d : MergerData M)
    (hd : schedule j = .inr d) (k : J) (hjk : Order.succ j ≤ k) :
    ∃ l : Fin d.n → (functor M schedule).obj k,
      (d.prescription.map (fromBase M schedule k).toMonoidHom).RootSystem l := by
  let d' := d.map (fromBase M schedule j)
  let f : d'.extension ⟶ (functor M schedule).obj k :=
    afterRequestMap M schedule j hj (.inr d) hd k hjk
  refine ⟨fun i => f (d'.root i),?_⟩
  have h := d'.cone_realization.map f.conservative
  have he : (f.toMonoidHom.comp d'.inclusion.toMonoidHom).comp
      (fromBase M schedule j).toMonoidHom = (fromBase M schedule k).toMonoidHom := by
    ext x
    exact fromBase_afterRequestMap M schedule j hj (.inr d) hd k hjk x
  change (((d.prescription.map (fromBase M schedule j).toMonoidHom).map
    d'.inclusion.toMonoidHom).map f.toMonoidHom).RootSystem _ at h
  simp only [DiagramForcing.OverlapPrescription.map_comp,← MonoidHom.comp_assoc,he] at h
  exact h

/-- The actual new probe after its conservative transport to a later cut. -/
def probe (j : J) (hj : ¬IsMax j) (d : ProbeData M)
    (hd : schedule j = .inl d) (k : J) (hjk : Order.succ j ≤ k) :
    (functor M schedule).obj k :=
  afterRequestMap M schedule j hj (.inl d) hd k hjk (d.map (fromBase M schedule j)).probe

@[simp] theorem probe_transition (j : J) (hj : ¬IsMax j) (d : ProbeData M)
    (hd : schedule j = .inl d) (k l : J) (hjk : Order.succ j ≤ k) (hkl : k ≤ l) :
    (functor M schedule).map (homOfLE hkl) (probe M schedule j hj d hd k hjk) =
      probe M schedule j hj d hd l (hjk.trans hkl) := by
  change ((requestIso M schedule j hj (.inl d) hd).inv ≫
    (functor M schedule).map (homOfLE hjk) ≫ (functor M schedule).map (homOfLE hkl)) _ = _
  rw [← Functor.map_comp,homOfLE_comp]
  rfl

theorem probe_profile (j : J) (hj : ¬IsMax j) (d : ProbeData M)
    (hd : schedule j = .inl d) (k : J) (hjk : Order.succ j ≤ k) :
    ProbeProfile (fromBase M schedule k d.a) (fromBase M schedule k d.b)
      ((functor M schedule).obj k).e (probe M schedule j hj d hd k hjk)
      (fun i => fromBase M schedule k (d.path.node i)) := by
  let f := afterRequestMap M schedule j hj (.inl d) hd k hjk
  have hp := afterRequestMap_preservesProfiles M schedule j hj (.inl d) hd k hjk
    _ _ _ _ _ (d.map (fromBase M schedule j)).profile
  change ProbeProfile (f ((d.map (fromBase M schedule j)).inclusion (fromBase M schedule j d.a)))
    (f ((d.map (fromBase M schedule j)).inclusion (fromBase M schedule j d.b)))
    (f ((d.map (fromBase M schedule j)).extension.e)) (probe M schedule j hj d hd k hjk)
    (fun i => f ((d.map (fromBase M schedule j)).inclusion (fromBase M schedule j (d.path.node i)))) at hp
  have he (x : M) : f ((d.map (fromBase M schedule j)).inclusion (fromBase M schedule j x)) =
      fromBase M schedule k x := fromBase_afterRequestMap M schedule j hj (.inl d) hd k hjk x
  have hee : f (d.map (fromBase M schedule j)).extension.e = ((functor M schedule).obj k).e := f.map_e
  simpa only [he,hee] using hp

theorem probe_new (j : J) (hj : ¬IsMax j) (d : ProbeData M)
    (hd : schedule j = .inl d) (k : J) (hjk : Order.succ j ≤ k) :
    ¬ ∃ x : (functor M schedule).obj j,
      (functor M schedule).map (homOfLE ((Order.le_succ j).trans hjk)) x =
        probe M schedule j hj d hd k hjk := by
  rintro ⟨x,hx⟩
  rw [← inclusion_afterRequestMap M schedule j hj (.inl d) hd k hjk] at hx
  exact (d.map (fromBase M schedule j)).probe_new
    ⟨x,(afterRequestMap M schedule j hj (.inl d) hd k hjk).injective hx⟩

/-- Independence is with respect to the whole previous stage, not merely the
round's starting monoid. -/
theorem probe_independent (j : J) (hj : ¬IsMax j) (d : ProbeData M)
    (hd : schedule j = .inl d) (k : J) (hjk : Order.succ j ≤ k)
    (x : (functor M schedule).obj j)
    (hx : x ∣ (fromBase M schedule j d.a) * ((functor M schedule).obj j).e)
    (hxa : ¬ x ∣ fromBase M schedule j d.a) (z : (functor M schedule).obj k) :
    (functor M schedule).map (homOfLE ((Order.le_succ j).trans hjk)) x ∣ z ∧
      probe M schedule j hj d hd k hjk ∣ z ↔ fromBase M schedule k d.a * ((functor M schedule).obj k).e ∣ z := by
  let d' := d.map (fromBase M schedule j)
  let f : d'.extension ⟶ (functor M schedule).obj k :=
    afterRequestMap M schedule j hj (.inl d) hd k hjk
  have h := f.conservative.intersections _ _ _ (d'.independent x hx hxa) z
  have he := fromBase_afterRequestMap M schedule j hj (.inl d) hd k hjk d.a
  have htrans := inclusion_afterRequestMap M schedule j hj (.inl d) hd k hjk
  change d'.inclusion ≫ f = _ at htrans
  change f (d'.inclusion d'.a) = _ at he
  change ((d'.inclusion ≫ f) x ∣ z ∧ probe M schedule j hj d hd k hjk ∣ z) ↔
    f (d'.inclusion (d'.a * ((functor M schedule).obj j).e)) ∣ z at h
  simpa only [htrans,d'.inclusion.toMonoidHom.map_mul,f.toMonoidHom.map_mul,d'.inclusion.map_e,
    f.map_e,he] using h
end MonoidConstruction.Round
end
end PartitionConsistency


/-! ## CompleteRound -/
namespace PartitionConsistency.MonoidConstruction
universe u
open CategoryTheory CategoryTheory.Limits DiagramOrder
noncomputable section
open scoped Classical
namespace Round
variable {J : Type u} [CompleteLinearOrder J] [SuccOrder J] [WellFoundedLT J]
  (M : Object.{u}) (schedule : J → Request M)

theorem probes_ne_of_lt (i j : J) (hi : ¬IsMax i) (hj : ¬IsMax j)
    (di dj : ProbeData M) (hdi : schedule i = .inl di) (hdj : schedule j = .inl dj)
    (hij : i < j) (k : J) (hjk : Order.succ j ≤ k) :
    probe M schedule i hi di hdi k ((Order.succ_le_iff_of_not_isMax hi).2 hij |>.trans
      ((Order.le_succ j).trans hjk)) ≠ probe M schedule j hj dj hdj k hjk := by
  intro he
  let hle := (Order.succ_le_iff_of_not_isMax hi).2 hij
  apply probe_new M schedule j hj dj hdj k hjk
  refine ⟨probe M schedule i hi di hdi j hle,?_⟩
  rw [probe_transition]
  exact he

/-- Any two distinct executions of one datum have exactly the common exit cone. -/
theorem probes_independent_of_lt (i j : J) (hi : ¬IsMax i) (hj : ¬IsMax j)
    (d : ProbeData M) (hdi : schedule i = .inl d) (hdj : schedule j = .inl d)
    (hij : i < j) (k : J) (hjk : Order.succ j ≤ k) (z : (functor M schedule).obj k) :
    probe M schedule i hi d hdi k ((Order.succ_le_iff_of_not_isMax hi).2 hij |>.trans
      ((Order.le_succ j).trans hjk)) ∣ z ∧ probe M schedule j hj d hdj k hjk ∣ z ↔
      fromBase M schedule k d.a * ((functor M schedule).obj k).e ∣ z := by
  let hle := (Order.succ_le_iff_of_not_isMax hi).2 hij
  have hp := probe_profile M schedule i hi d hdi j hle
  have h : probe M schedule i hi d hdi j hle ∣
      fromBase M schedule j d.a * ((functor M schedule).obj j).e :=
    ⟨fromBase M schedule j d.b,hp.exit.symm⟩
  simpa only [probe_transition] using
    probe_independent M schedule j hj d hdj k hjk _ h hp.not_divides z
end Round

/- An entire round schedules every available datum, once for every repetition
index. Its chosen well-order is immaterial to conservation and independence. -/
namespace CompleteRound
variable (M : Object.{u}) (K : Type u) [Nonempty K]
abbrev Index := ScheduleIndex (Request M × K)

def schedule : Index M K → Request M
  | none => .inl (Request.defaultProbe M)
  | some d => d.1

def place (d : Request M) (i : K) : Index M K := some (d,i)
omit [Nonempty K] in
@[simp] theorem at_place (d : Request M) (i : K) : schedule M K (place M K d i) = d := rfl

theorem place_not_isMax (d : Request M) (i : K) : ¬IsMax (place M K d i) := by
  apply not_isMax_iff_ne_top.mpr
  exact WithTop.coe_ne_top

omit [Nonempty K] in
theorem place_injective (d : Request M) : Function.Injective (place M K d) := by
  intro i j h
  exact (Prod.mk.inj (Option.some.inj h)).2

abbrev tower : Index M K ⥤ Object.{u} := Round.functor M (schedule M K)
def target : Object.{u} := (tower M K).obj ⊤
def inclusion : M ⟶ target M K := Round.fromBase M (schedule M K) ⊤

theorem preservesProfiles : PreservesProfiles (inclusion M K) :=
  Round.fromBase_preservesProfiles M (schedule M K) ⊤

theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hpow : μ ^ Cardinal.aleph0 = μ) (hM : Cardinal.mk M ≤ μ) (hK : Cardinal.mk K ≤ μ) :
    Cardinal.mk (target M K) ≤ μ := by
  apply Round.cardinal_le M (schedule M K) hω _ hM
  change Cardinal.mk (Option (Request M × K)) ≤ μ
  simp only [Cardinal.mk_option,Cardinal.mk_prod,Cardinal.lift_id]
  exact (add_le_add ((mul_le_mul' (Request.data_cardinal_le hω hpow hM) hK).trans_eq
    (Cardinal.mul_eq_self hω)) (Cardinal.one_le_aleph0.trans hω)).trans_eq (Cardinal.add_eq_self hω)

def probe (d : ProbeData M) (i : K) : target M K :=
  Round.probe M (schedule M K) (place M K (.inl d) i) (place_not_isMax M K _ _) d rfl ⊤ le_top

theorem probe_profile (d : ProbeData M) (i : K) :
    ProbeProfile (inclusion M K d.a) (inclusion M K d.b) (target M K).e
      (probe M K d i) (fun j => inclusion M K (d.path.node j)) :=
  Round.probe_profile M (schedule M K) (place M K (.inl d) i) (place_not_isMax M K _ _) d rfl ⊤ le_top

theorem probe_injective (d : ProbeData M) : Function.Injective (probe M K d) := by
  intro i j he
  by_contra hij
  have hne := (place_injective M K (.inl d)).ne hij
  rcases lt_or_gt_of_ne hne with h | h
  · exact Round.probes_ne_of_lt M (schedule M K) _ _ (place_not_isMax M K _ _)
      (place_not_isMax M K _ _) d d rfl rfl h ⊤ le_top he
  · exact Round.probes_ne_of_lt M (schedule M K) _ _ (place_not_isMax M K _ _)
      (place_not_isMax M K _ _) d d rfl rfl h ⊤ le_top he.symm

theorem probes_independent (d : ProbeData M) (i j : K) (hij : i ≠ j) (z : target M K) :
    probe M K d i ∣ z ∧ probe M K d j ∣ z ↔ inclusion M K d.a * (target M K).e ∣ z := by
  have hne := (place_injective M K (.inl d)).ne hij
  rcases lt_or_gt_of_ne hne with h | h
  · exact Round.probes_independent_of_lt M (schedule M K) _ _ (place_not_isMax M K _ _)
      (place_not_isMax M K _ _) d rfl rfl h ⊤ le_top z
  · have h := Round.probes_independent_of_lt M (schedule M K) _ _ (place_not_isMax M K _ _)
      (place_not_isMax M K _ _) d rfl rfl h ⊤ le_top z
    exact and_comm.trans h

theorem realizes_merger (d : MergerData M) :
    ∃ l : Fin d.n → target M K, (d.prescription.map (inclusion M K).toMonoidHom).RootSystem l :=
  Round.creates_merger M (schedule M K) (place M K (.inr d) (Classical.choice ‹Nonempty K›))
    (place_not_isMax M K _ _) d rfl ⊤ le_top
end CompleteRound
end
end PartitionConsistency.MonoidConstruction


/-! ## OuterIteration -/

namespace PartitionConsistency.MonoidConstruction
universe u v
open CategoryTheory CategoryTheory.Limits DiagramOrder
noncomputable section
open scoped Classical

/-- The first uncountable ordinal, as a small indexing type. There is no
inaccessible-cardinal or chain-length closure assumption in this index. -/
abbrev RoundOrdinal : Type u := (Cardinal.aleph.{u} 1).ord.ToType
namespace RoundOrdinal
instance instNonempty : Nonempty RoundOrdinal.{u} := Ordinal.nonempty_toType_iff.mpr
  Cardinal.isRegular_aleph_one.ord_pos.ne'
instance instOrderBot : OrderBot RoundOrdinal.{u} := WellFoundedLT.toOrderBot _
instance instConditionallyCompleteLinearOrderBot : ConditionallyCompleteLinearOrderBot RoundOrdinal.{u} :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _
instance instNoMaxOrder : NoMaxOrder RoundOrdinal.{u} := Cardinal.noMaxOrder Cardinal.aleph0_lt_aleph_one.le

/-- Countably many round indices are bounded before the last union. -/
theorem countable_bounded {A : Type v} [Countable A] (f : A → RoundOrdinal.{u}) :
    ∃ j : RoundOrdinal.{u}, ∀ i, f i ≤ j := by
  let g : A → Ordinal.{u} := fun i => (f i).toOrd.val
  have hg : ∀ i, g i < (Cardinal.aleph.{u} 1).ord := fun i => (f i).toOrd.property
  have hc : Cardinal.lift.{u,v} (Cardinal.mk A) <
      (Ordinal.lift.{v,u} (Cardinal.aleph.{u} 1).ord).cof := by
    rw [← Ordinal.lift_cof, Cardinal.isRegular_aleph_one.cof_ord]
    have h : Cardinal.lift.{u,v} (Cardinal.mk A) ≤ Cardinal.aleph0 := by
      simpa only [Cardinal.lift_aleph0] using
        Cardinal.lift_le.mpr (Cardinal.mk_le_aleph0 (α := A))
    exact h.trans_lt (by simp)
  have hb := Ordinal.lift_iSup_lt_of_lt_cof hc hg
  let j : RoundOrdinal.{u} := Ordinal.ToType.mk ⟨iSup g,hb⟩
  refine ⟨j,fun i => ?_⟩
  apply Ordinal.ToType.mk.symm.le_iff_le.mp
  change (Ordinal.ToType.mk.symm (f i)).val ≤ (Ordinal.ToType.mk.symm j).val
  change g i ≤ (Ordinal.ToType.mk.symm (Ordinal.ToType.mk ⟨iSup g,hb⟩)).val
  simpa only [OrderIso.symm_apply_apply] using
    le_ciSup (show BddAbove (Set.range g) from ⟨_,fun _ ⟨i,hi⟩ => hi ▸ (hg i).le⟩) i

@[simp] theorem cardinal : Cardinal.mk RoundOrdinal.{u} = Cardinal.aleph 1 := by
  rw [RoundOrdinal,Cardinal.mk_toType,Cardinal.card_ord]
end RoundOrdinal

abbrev OuterIndex : Type u := WithTop RoundOrdinal.{u}
instance instSuccOrderOuterIndex : SuccOrder OuterIndex.{u} := SuccOrder.ofLinearWellFoundedLT _

theorem outer_top_limit : Order.IsSuccLimit (⊤ : OuterIndex.{u}) := WithTop.isSuccLimit_top

theorem outer_countable_bound {A : Type v} [Countable A] (f : A → OuterIndex.{u})
    (hf : ∀ i, f i < ⊤) : ∃ j : OuterIndex.{u}, j < ⊤ ∧ ∀ i, f i ≤ j := by
  let g : A → RoundOrdinal.{u} := fun i => (f i).untop (ne_of_lt (hf i))
  obtain ⟨j,hj⟩ := RoundOrdinal.countable_bounded g
  refine ⟨j,WithTop.coe_lt_top j,fun i => ?_⟩
  rw [← WithTop.coe_untop (f i) (ne_of_lt (hf i))]
  exact WithTop.coe_le_coe.mpr (hj i)

namespace Saturation
variable (M : Object.{u}) (K : Type u) [Nonempty K]

def step (_ : OuterIndex.{u}) (X : Object.{u}) : ConstructionIteration.Step X :=
  ⟨CompleteRound.target X K, CompleteRound.inclusion X K⟩
abbrev tower : OuterIndex.{u} ⥤ Object.{u} := ConstructionIteration.functor M (step K)

def botIso : (tower M K).obj ⊥ ≅ M := ConstructionIteration.botIso M (step K)
def succIso (j : OuterIndex.{u}) (hj : j < ⊤) :
    (tower M K).obj (Order.succ j) ≅ CompleteRound.target ((tower M K).obj j) K :=
  ConstructionIteration.succIso M (step K) j (not_isMax_iff_ne_top.mpr hj.ne)

theorem map_succ (j : OuterIndex.{u}) (hj : j < ⊤) :
    (tower M K).map (homOfLE (Order.le_succ j)) =
      CompleteRound.inclusion ((tower M K).obj j) K ≫ (succIso M K j hj).inv :=
  ConstructionIteration.map_succ M (step K) j (not_isMax_iff_ne_top.mpr hj.ne)

def target : Object.{u} := (tower M K).obj ⊤
def fromStage (j : OuterIndex.{u}) : (tower M K).obj j ⟶ target M K :=
  (tower M K).map (homOfLE le_top)

theorem preservesProfiles (i j : OuterIndex.{u}) (hij : i ≤ j) :
    PreservesProfiles ((tower M K).map (homOfLE hij)) := by
  apply ContinuousTower.preservesProfiles
  intro k hk
  have hkt : k < ⊤ := lt_top_iff_ne_top.mpr (not_isMax_iff_ne_top.mp hk)
  rw [map_succ M K k hkt]
  exact (CompleteRound.preservesProfiles _ K).comp
    (PreservesProfiles.of_iso (succIso M K k hkt).symm)

theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph 1 ≤ μ)
    (hpow : μ ^ Cardinal.aleph0 = μ) (hM : Cardinal.mk M ≤ μ) (hK : Cardinal.mk K ≤ μ)
    (j : OuterIndex.{u}) : Cardinal.mk ((tower M K).obj j) ≤ μ := by
  have hω₀ := Cardinal.aleph0_lt_aleph_one.le.trans hω
  apply ContinuousTower.cardinal_le _ hω₀
  · change Cardinal.mk (Option RoundOrdinal.{u}) ≤ μ
    rw [Cardinal.mk_option, RoundOrdinal.cardinal]
    exact (add_le_add hω (Cardinal.one_le_aleph0.trans hω₀)).trans_eq (Cardinal.add_eq_self hω₀)
  · rw [Cardinal.mk_congr (isoEquiv (botIso M K))]
    exact hM
  · intro k hk h
    have hkt : k < ⊤ := lt_top_iff_ne_top.mpr (not_isMax_iff_ne_top.mp hk)
    rw [Cardinal.mk_congr (isoEquiv (succIso M K k hkt))]
    exact CompleteRound.cardinal_le _ K hω₀ hpow h hK

/-- Every countable set of final elements, with no restriction on their
birth rounds, lies in one proper stage, before a following complete round. -/
theorem countable_stage {A : Type v} [Countable A] (f : A → target M K) :
    ∃ j : OuterIndex.{u}, j < ⊤ ∧ ∃ g : A → (tower M K).obj j,
      ∀ a, fromStage M K j (g a) = f a := by
  have h (a : A) := ContinuousTower.exists_rep (tower M K) outer_top_limit (f a)
  choose i hi x hx using h
  obtain ⟨j,hj,hij⟩ := outer_countable_bound i hi
  refine ⟨j,hj,fun a => (tower M K).map (homOfLE (hij a)) (x a),fun a => ?_⟩
  change (((tower M K).map (homOfLE (hij a))) ≫ fromStage M K j) (x a) = _
  unfold fromStage
  erw [← Functor.map_comp, homOfLE_comp]
  exact hx a

end Saturation
end
end PartitionConsistency.MonoidConstruction

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_SaturatedMonoids
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## SaturationData -/

namespace PartitionConsistency.MonoidConstruction
universe u
open CategoryTheory CategoryTheory.Limits DiagramOrder DiagramForcing
noncomputable section
open scoped Classical

@[ext] theorem _root_.OAI.PartitionConsistency.DiagramForcing.OverlapPrescription.ext
    {A : Type u} {n : ℕ} {P Q : OverlapPrescription A n}
    (h : ∀ i j, P.start i j = Q.start i j) : P = Q := by
  cases P; cases Q; congr 1; exact funext (fun i => funext (h i))

namespace Saturation
variable (M : Object.{u}) (K : Type u) [Nonempty K]

/-- All the parameters of a final probe occur before one complete round.
Its comparisons reflect to that stage; they are not separately postulated. -/
theorem probe_stage (d : ProbeData (target M K)) :
    ∃ j : OuterIndex.{u}, j < ⊤ ∧ ∃ d₀ : ProbeData ((tower M K).obj j),
      fromStage M K j d₀.a = d.a ∧ fromStage M K j d₀.b = d.b ∧
        ∀ i, fromStage M K j (d₀.path.node i) = d.path.node i := by
  let f : Option (Option ℕ) → target M K
    | none => d.b
    | some none => d.a
    | some (some n) => d.path.node n
  obtain ⟨j,hj,g,hg⟩ := countable_stage M K f
  let f₀ := fromStage M K j
  let P : ProbeAlgebra.Path ((tower M K).obj j) (g (some none)) := {
    node := fun i => g (some (some i))
    zero := by
      apply f₀.injective
      exact (hg (some (some 0))).trans (d.path.zero.trans f₀.map_one.symm)
    increasing := by
      intro i k hik
      apply (f₀.conservative.dvd_iff _ _).1
      simpa only [f₀,hg,f] using d.path.increasing hik
    bounded := by
      intro i
      apply (f₀.conservative.dvd_iff _ _).1
      simpa only [f₀,hg,f] using d.path.bounded i }
  refine ⟨j,hj,⟨g (some none),g none,?_,P⟩,hg (some none),hg none,fun i => hg (some (some i))⟩
  intro he
  apply d.b_ne_one
  exact (hg none).symm.trans ((congrArg f₀ he).trans f₀.map_one)

/-- Inclusion of the completed successor round into the final union. -/
def afterRound (j : OuterIndex.{u}) (hj : j < ⊤) :
    CompleteRound.target ((tower M K).obj j) K ⟶ target M K :=
  (succIso M K j hj).inv ≫ fromStage M K (Order.succ j)

theorem inclusion_afterRound (j : OuterIndex.{u}) (hj : j < ⊤) :
    CompleteRound.inclusion ((tower M K).obj j) K ≫ afterRound M K j hj =
      fromStage M K j := by
  unfold afterRound
  rw [← Category.assoc,← map_succ]
  unfold fromStage
  erw [← Functor.map_comp,homOfLE_comp]

theorem afterRound_preservesProfiles (j : OuterIndex.{u}) (hj : j < ⊤) :
    PreservesProfiles (afterRound M K j hj) :=
  (PreservesProfiles.of_iso (succIso M K j hj).symm).comp
    (preservesProfiles M K _ _ _)

/-- Saturation for countable paths, including the complete final divisor
profile and pairwise exact intersections in the final monoid. -/
theorem probes (d : ProbeData (target M K)) :
    ∃ m : K → target M K, Function.Injective m ∧
      (∀ i, ProbeProfile d.a d.b (target M K).e (m i) d.path.node) ∧
      ∀ i j, i ≠ j → ∀ z : target M K,
        m i ∣ z ∧ m j ∣ z ↔ d.a * (target M K).e ∣ z := by
  obtain ⟨j,hj,d₀,ha,hb,hn⟩ := probe_stage M K d
  let f := afterRound M K j hj
  let C := CompleteRound.target ((tower M K).obj j) K
  let inc := CompleteRound.inclusion ((tower M K).obj j) K
  have hi (x : (tower M K).obj j) : f (inc x) = fromStage M K j x :=
    congrArg (fun h : (tower M K).obj j ⟶ target M K => h x) (inclusion_afterRound M K j hj)
  have he : f C.e = (target M K).e := f.map_e
  let m : K → C := CompleteRound.probe ((tower M K).obj j) K d₀
  refine ⟨fun i => f (m i),f.injective.comp (CompleteRound.probe_injective _ K d₀),?_,?_⟩
  · intro i
    have ht := afterRound_preservesProfiles M K j hj _ _ _ _ _
      (CompleteRound.probe_profile _ K d₀ i)
    change ProbeProfile (f (inc d₀.a)) (f (inc d₀.b)) (f C.e)
      (f (m i)) (fun k => f (inc (d₀.path.node k))) at ht
    simpa only [hi,ha,hb,he,hn] using ht
  · intro i k hik z
    have hh := f.conservative.intersections (m i) (m k) (inc d₀.a * C.e)
      (CompleteRound.probes_independent _ K d₀ i k hik) z
    simpa only [f.map_mul,hi,ha,he] using hh

/-- Every finite prescription, without a validity restriction, is the image
of its actual parameters in a proper stage. -/
theorem prescription_stage {n : ℕ} (P : OverlapPrescription (target M K) n) :
    ∃ j : OuterIndex.{u}, j < ⊤ ∧ ∃ P₀ : OverlapPrescription ((tower M K).obj j) n,
      P₀.map (fromStage M K j).toMonoidHom = P := by
  let f : Fin n × Fin n × Bool → target M K := fun (i,k,b) =>
    if b then ((P.start i k).getD (1,1)).2 else ((P.start i k).getD (1,1)).1
  obtain ⟨j,hj,g,hg⟩ := countable_stage M K f
  let P₀ : OverlapPrescription ((tower M K).obj j) n :=
    ⟨fun i k => (P.start i k).map (fun _ => (g (i,k,false),g (i,k,true)))⟩
  refine ⟨j,hj,P₀,?_⟩
  apply OverlapPrescription.ext
  intro i k
  cases hp : P.start i k with
  | none => simp [P₀,OverlapPrescription.map,hp]
  | some ab =>
    have ha := hg (i,k,false)
    have hb := hg (i,k,true)
    simp only [f,hp,Option.getD_some,Bool.false_eq_true,↓reduceIte] at ha
    simp only [f,hp,Option.getD_some,↓reduceIte] at hb
    simp only [OverlapPrescription.map_start,P₀,hp,Option.map_some,ha,hb,Prod.eta]

/-- Exact cone realizations persist after all the later rounds, including
for right factors which did not exist when the merger was executed. -/
theorem realizes_prescription {n : ℕ} (P : OverlapPrescription (target M K) n)
    (hP : P.Valid) : ∃ l : Fin n → target M K, P.RootSystem l := by
  by_cases hn : 0 < n
  · obtain ⟨j,hj,P₀,hmap⟩ := prescription_stage M K P
    have hv : P₀.Valid := P₀.valid_of_map (fromStage M K j).conservative (hmap ▸ hP)
    let d : MergerData ((tower M K).obj j) := ⟨n,hn,P₀,hv⟩
    obtain ⟨l,hl⟩ := CompleteRound.realizes_merger ((tower M K).obj j) K d
    let f := afterRound M K j hj
    have ht := hl.map f.conservative
    have hp : (d.prescription.map (CompleteRound.inclusion ((tower M K).obj j) K).toMonoidHom).map
        f.toMonoidHom = P := by
      rw [← hmap]
      apply OverlapPrescription.ext
      intro i k
      change ((P₀.start i k).map _).map _ = (P₀.start i k).map _
      rw [Option.map_map]
      apply congrArg (fun g => (P₀.start i k).map g)
      funext ab
      have h := inclusion_afterRound M K j hj
      exact congrArg (fun t : (tower M K).obj j ⟶ target M K => (t ab.1,t ab.2)) h
    exact ⟨fun i => f (l i),hp ▸ ht⟩
  · have hn : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    exact ⟨Fin.elim0,fun i => Fin.elim0 i⟩

theorem finiteMergers : HasFiniteMergers (target M K) := by
  intro n P hP
  obtain ⟨l,hl⟩ := realizes_prescription M K P hP
  exact ⟨l,hl.realization⟩

/-- The executed probes at `a = 1, b = e` lie outside the full cone `eT`. -/
theorem complement_probes : ∃ m : K → target M K,
    Function.Injective m ∧ ∀ i, ¬ (target M K).e ∣ m i := by
  let d : ProbeData (target M K) := {
    a := 1
    b := (target M K).e
    b_ne_one := (target M K).e_ne_one
    path := ⟨fun _ => 1,rfl,fun _ => dvd_refl _,fun _ => dvd_refl _⟩ }
  obtain ⟨m,hinj,hm,hind⟩ := probes M K d
  refine ⟨m,hinj,?_⟩
  intro i he
  obtain ⟨x,hx⟩ := he
  have hex : (target M K).e * x * (target M K).e = 1 * (target M K).e := by
    rw [← hx]; exact (hm i).exit
  have hxe : x * (target M K).e = 1 := by
    apply mul_left_cancel (a := (target M K).e)
    simpa only [mul_assoc,mul_one,one_mul] using hex
  exact (target M K).e_ne_one (IsConical.eq_one_of_mul_eq_one hxe).2

theorem target_cardinal {μ : Cardinal.{u}} (hω : Cardinal.aleph 1 ≤ μ)
    (hpow : μ ^ Cardinal.aleph0 = μ) (hM : Cardinal.mk M ≤ μ) (hK : Cardinal.mk K = μ) :
    Cardinal.mk (target M K) = μ := by
  apply le_antisymm (cardinal_le M K hω hpow hM hK.le ⊤)
  obtain ⟨m,hinj,_⟩ := complement_probes M K
  rw [← hK]
  exact Cardinal.mk_le_of_injective hinj

end Saturation
end
end PartitionConsistency.MonoidConstruction

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_MergerPushouts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## MergerPresentation -/

namespace PartitionConsistency.MergerAlgebra.Word
universe u v w
noncomputable section
variable {M : Type u} {D : Type v} {N : Type w}
  [Monoid M] [RightFreeAction M D] [Monoid N]

/-- Interpretation of an actual merger normal form. New letters are evaluated
in their displayed order; the target is an arbitrary monoid. -/
def evaluate (f : M →* N) (g : D → N) : Word M D → N
  | old x => f x
  | snoc x d => evaluate f g x * g d

variable (f : M →* N) (g : D → N)
  (hg : ∀ d x, g (RightFreeAction.act d x) = g d * f x)

include hg in
theorem evaluate_act (w : Word M D) (x : M) :
    evaluate f g (act w x) = evaluate f g w * f x := by
  cases w with
  | old y => exact f.map_mul y x
  | snoc w d =>
    change evaluate f g w * g (RightFreeAction.act d x) = (evaluate f g w * g d) * f x
    rw [hg,mul_assoc]

include hg in
theorem evaluate_mul (x y : Word M D) :
    evaluate f g (x*y) = evaluate f g x * evaluate f g y := by
  induction y with
  | old y => exact evaluate_act f g hg x y
  | snoc y d ih =>
    change evaluate f g (x*y) * g d = evaluate f g x * (evaluate f g y * g d)
    rw [ih,mul_assoc]

/-- Universal evaluation of merger words for an equivariant interpretation
of the quotient of copies. -/
def liftHom : Word M D →* N where
  toFun := evaluate f g
  map_one' := f.map_one
  map_mul' := evaluate_mul f g hg

@[simp] theorem liftHom_old (x : M) : liftHom f g hg (old x) = f x := rfl

@[simp] theorem liftHom_letter (d : D) :
    liftHom f g hg (snoc (old 1) d) = g d := by
  change f 1 * g d = g d
  rw [f.map_one,one_mul]

/-- Old coefficients and the single-letter words generate the extension.
This asserts uniqueness in arbitrary target monoids, not just conservative
ones. -/
theorem hom_ext (F G : Word M D →* N)
    (ho : ∀ x, F (old x) = G (old x))
    (hn : ∀ d, F (snoc (old 1) d) = G (snoc (old 1) d)) : F = G := by
  apply MonoidHom.ext
  intro w
  induction w with
  | old x => exact ho x
  | snoc w d ih =>
    have he : snoc w d = w * snoc (old 1) d := by
      change snoc w d = snoc (w * 1) d
      rw [mul_one]
    rw [he,F.map_mul,G.map_mul,ih,hn]

end
end PartitionConsistency.MergerAlgebra.Word

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u v
noncomputable section
variable {M : Type u} [LeftCancelMonoid M] {n : ℕ}
  (P : OverlapPrescription M n) (hP : P.Valid)
  {N : Type v} [Monoid N] (f : M →* N) (p : Fin n → N)

/-- Precisely the finite list of merger relations, interpreted in `N`.
Diagonal entries of `start` are ignored, as in the definition of `Rel`.
Reflected joins, nonjoins or injectivity are not required in the target. -/
def Satisfies : Prop :=
  ∀ i j a b, i ≠ j → P.start i j = some (a,b) → p i * f a = p j * f b

variable (hp : P.Satisfies f p)

include hp in
theorem satisfies_rel {z w : Fin n × M} (h : P.Rel z w) :
    p z.1 * f z.2 = p w.1 * f w.2 := by
  obtain ⟨i,x⟩ := z
  obtain ⟨j,y⟩ := w
  by_cases hij : i = j
  · subst j
    exact congrArg (fun t => p i * f t) ((P.rel_same_copy i x y).mp h)
  · simp only [Rel,hij,↓reduceIte] at h
    cases hs : P.start i j with
    | none => simp only [hs] at h
    | some ab =>
      obtain ⟨a,b⟩ := ab
      rw [hs] at h
      obtain ⟨t,rfl,rfl⟩ := h
      change p i * f (a*t) = p j * f (b*t)
      rw [f.map_mul,f.map_mul,← mul_assoc,← mul_assoc,hp i j a b hij hs]

/-- Interpretation of the actual prescribed quotient, not of a free
collection of formal copies. -/
def interpretedCopy : P.Copies hP → N :=
  Quotient.lift (fun z : Fin n × M => p z.1 * f z.2)
    (fun _ _ h => P.satisfies_rel f p hp h)

@[simp] theorem interpretedCopy_copy (i : Fin n) (x : M) :
    P.interpretedCopy hP f p hp (P.copy hP i x) = p i * f x := rfl

@[simp] theorem interpretedCopy_act (d : P.Copies hP) (x : M) :
    P.interpretedCopy hP f p hp (MergerAlgebra.RightFreeAction.act d x) =
      P.interpretedCopy hP f p hp d * f x := by
  induction d using Quotient.inductionOn with
  | h z =>
    change p z.1 * f (z.2*x) = (p z.1*f z.2)*f x
    rw [f.map_mul,mul_assoc]

/-- The merger normal forms have the universal property of the finite
relative monoid presentation used in the countable-base rearrangement. -/
def presentedLift : P.Merger hP →* N :=
  MergerAlgebra.Word.liftHom f (P.interpretedCopy hP f p hp)
    (P.interpretedCopy_act hP f p hp)

@[simp] theorem presentedLift_old (x : M) :
    P.presentedLift hP f p hp (.old x) = f x := rfl

@[simp] theorem presentedLift_root (i : Fin n) :
    P.presentedLift hP f p hp (P.root hP i) = p i := by
  change f 1 * (p i * f 1) = p i
  rw [f.map_one,one_mul,mul_one]

/-- All normal forms are determined by the old elements and the finitely
many roots. This is the uniqueness part needed when comparing reordered
presentations. -/
theorem presentedHom_ext (F G : P.Merger hP →* N)
    (ho : ∀ x, F (.old x) = G (.old x))
    (hn : ∀ i, F (P.root hP i) = G (P.root hP i)) : F = G := by
  apply MergerAlgebra.Word.hom_ext F G ho
  intro d
  induction d using Quotient.inductionOn with
  | h z =>
    change F (.snoc (.old 1) (P.copy hP z.1 z.2)) =
      G (.snoc (.old 1) (P.copy hP z.1 z.2))
    rw [← P.root_mul_old hP z.1 z.2,F.map_mul,G.map_mul,hn,ho]

/-- The literal roots satisfy every relation of their relative presentation. -/
theorem roots_satisfy : P.Satisfies MergerAlgebra.Word.oldHom (P.root hP) := by
  intro i j a b hij hab
  apply (P.root_mul_eq_iff hP (i,a) (j,b)).mpr
  simp only [Rel,hij,↓reduceIte,hab]
  exact ⟨1,(mul_one a).symm,(mul_one b).symm⟩

/-- Every homomorphism from a merger, with no conservation assumption,
necessarily satisfies those relations. -/
theorem map_roots_satisfy (F : P.Merger hP →* N) :
    P.Satisfies (F.comp MergerAlgebra.Word.oldHom) (fun i => F (P.root hP i)) := by
  intro i j a b hij hab
  simpa only [MonoidHom.comp_apply,F.map_mul] using
    congrArg F (P.roots_satisfy hP i j a b hij hab)

end
end PartitionConsistency.DiagramForcing.OverlapPrescription


/-! ## SimulationPushout -/

/-! The conservative simulations are also categorical pushouts among *all*
monoids. This supplies the presentation comparison, which alone is not yet
a countable-base rearrangement. -/
namespace PartitionConsistency.MonoidPushout
universe u
noncomputable section
variable {A B C D : Type u} [Monoid A] [Monoid B] [Monoid C] [Monoid D]

structure IsPushout (f : A →* B) (g : A →* C) (i : B →* D) (j : C →* D) : Prop where
  comm : i.comp f = j.comp g
  universal : ∀ {N : Type u} [Monoid N] (b : B →* N) (c : C →* N),
    b.comp f = c.comp g → ∃! t : D →* N, t.comp i = b ∧ t.comp j = c

namespace IsPushout
variable {f : A →* B} {g : A →* C} {i : B →* D} {j : C →* D}
variable (h : IsPushout f g i j)

def lift {N : Type u} [Monoid N] (b : B →* N) (c : C →* N)
    (hc : b.comp f = c.comp g) : D →* N := (h.universal b c hc).choose

@[simp] theorem lift_comp_left {N : Type u} [Monoid N] (b : B →* N) (c : C →* N)
    (hc : b.comp f = c.comp g) : (h.lift b c hc).comp i = b :=
  (h.universal b c hc).choose_spec.1.1

@[simp] theorem lift_comp_right {N : Type u} [Monoid N] (b : B →* N) (c : C →* N)
    (hc : b.comp f = c.comp g) : (h.lift b c hc).comp j = c :=
  (h.universal b c hc).choose_spec.1.2

include h in
theorem hom_ext {N : Type u} [Monoid N] (s t : D →* N)
    (hb : s.comp i = t.comp i) (hc : s.comp j = t.comp j) : s = t := by
  have hsq : (t.comp i).comp f = (t.comp j).comp g := by
    rw [MonoidHom.comp_assoc,MonoidHom.comp_assoc,h.comm]
  obtain ⟨l,hl,hu⟩ := h.universal (t.comp i) (t.comp j) hsq
  exact (hu s ⟨hb,hc⟩).trans (hu t ⟨rfl,rfl⟩).symm

/-- Apexes of two actual pushout squares are isomorphic over both bases. -/
def equiv {E : Type u} [Monoid E] {i' : B →* E} {j' : C →* E}
    (h' : IsPushout f g i' j') : D ≃* E := by
  let F := h.lift i' j' h'.comm
  let G := h'.lift i j h.comm
  have hFG : F.comp G = MonoidHom.id E := by
    apply h'.hom_ext
    · rw [MonoidHom.comp_assoc,h'.lift_comp_left,h.lift_comp_left,MonoidHom.id_comp]
    · rw [MonoidHom.comp_assoc,h'.lift_comp_right,h.lift_comp_right,MonoidHom.id_comp]
  have hGF : G.comp F = MonoidHom.id D := by
    apply h.hom_ext
    · rw [MonoidHom.comp_assoc,h.lift_comp_left,h'.lift_comp_left,MonoidHom.id_comp]
    · rw [MonoidHom.comp_assoc,h.lift_comp_right,h'.lift_comp_right,MonoidHom.id_comp]
  exact
    { F with
      invFun := G
      left_inv := fun x => DFunLike.congr_fun hGF x
      right_inv := fun x => DFunLike.congr_fun hFG x }

@[simp] theorem equiv_comp_left {E : Type u} [Monoid E] {i' : B →* E} {j' : C →* E}
    (h' : IsPushout f g i' j') : (h.equiv h').toMonoidHom.comp i = i' :=
  h.lift_comp_left i' j' h'.comm

@[simp] theorem equiv_comp_right {E : Type u} [Monoid E] {i' : B →* E} {j' : C →* E}
    (h' : IsPushout f g i' j') : (h.equiv h').toMonoidHom.comp j = j' :=
  h.lift_comp_right i' j' h'.comm

end IsPushout
end
end PartitionConsistency.MonoidPushout

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u
noncomputable section
open DiagramOrder MonoidPushout MergerAlgebra
variable {A B : Type u} [LeftCancelMonoid A] [IsConical A] [LeftCancelMonoid B]
  {n : ℕ} (P : OverlapPrescription A n) (hP : P.Valid)
  (hA : HasConditionalJoins (LeftDivOrder A)) {f : A →* B} (hf : Conservative f)

@[simp] theorem mergerSimulation_root (i : Fin n) :
    P.mergerSimulation hP hA hf (P.root hP i) =
      (P.map f).root (P.valid_map hP hA hf) i := by
  change Word.snoc (Word.old (f 1))
    ((P.map f).copy (P.valid_map hP hA hf) i (f 1)) = _
  rw [f.map_one]
  rfl

omit [IsConical A] in
theorem satisfies_map_iff {N : Type u} [Monoid N] (g : B →* N) (p : Fin n → N) :
    (P.map f).Satisfies g p ↔ P.Satisfies (g.comp f) p := by
  constructor
  · intro h i j a b hij hab
    exact h i j (f a) (f b) hij (by simp only [map_start,hab,Option.map_some])
  · intro h i j a b hij hab
    change (P.start i j).map _ = some (a,b) at hab
    cases hs : P.start i j with
    | none => simp only [hs,Option.map_none] at hab; cases hab
    | some ab =>
      simp only [hs,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hab
      rcases hab with ⟨ha,hb⟩
      subst a; subst b
      exact h i j ab.1 ab.2 hij hs

/-- Simulating a finite merger is extension of scalars for its literal
relative presentation. -/
theorem mergerSimulation_pushout :
    IsPushout (Word.oldHom : A →* P.Merger hP) f
      (P.mergerSimulation hP hA hf)
      (Word.oldHom : B →* (P.map f).Merger (P.valid_map hP hA hf)) where
  comm := by ext x; rfl
  universal s t hc := by
    let p (i : Fin n) := s (P.root hP i)
    have hp : (P.map f).Satisfies t p := by
      apply (P.satisfies_map_iff t p).mpr
      rw [← hc]
      exact P.map_roots_satisfy hP s
    let l := (P.map f).presentedLift (P.valid_map hP hA hf) t p hp
    have hlold : l.comp Word.oldHom = t := by ext x; rfl
    have hlnew : l.comp (P.mergerSimulation hP hA hf) = s := by
      apply P.presentedHom_ext hP
      · intro x
        change t (f x) = s (Word.old x)
        exact (DFunLike.congr_fun hc x).symm
      · intro i
        simp only [MonoidHom.comp_apply,mergerSimulation_root,
          l,presentedLift_root,p]
    refine ⟨l,⟨hlnew,hlold⟩,?_⟩
    intro k hk
    apply (P.map f).presentedHom_ext (P.valid_map hP hA hf)
    · intro x
      exact (DFunLike.congr_fun hk.2 x).trans (DFunLike.congr_fun hlold x).symm
    · intro i
      have hki := DFunLike.congr_fun hk.1 (P.root hP i)
      simpa only [MonoidHom.comp_apply,mergerSimulation_root,
        l,presentedLift_root,p] using hki

end
end PartitionConsistency.DiagramForcing.OverlapPrescription

namespace PartitionConsistency.ProbeAlgebra.Path
universe u
noncomputable section
open DiagramOrder MonoidPushout
variable {A B : Type u} [LeftCancelMonoid A] [IsConical A]
  [LeftCancelMonoid B] [IsConical B] {a e : A} (P : Path A a)
  (he : e ≠ 1) {f : A →* B} (hf : Conservative f) (b : A) (hb : b ≠ 1)

include hb in
/-- Simulating an indexed probe is a pushout for exactly its countable
transition and exit presentation. No universal property is assumed. -/
theorem simulation_pushout :
    IsPushout (Word.oldHom (P.alphabet he) b) f (P.simulation he hf b)
      (Word.oldHom ((P.map f).alphabet
        (fun h => he (hf.injective (h.trans f.map_one.symm)))) (f b)) where
  comm := by ext x; rfl
  universal s t hc := by
    let he' : f e ≠ 1 := fun h => he (hf.injective (h.trans f.map_one.symm))
    let hb' : f b ≠ 1 := fun h => hb (hf.injective (h.trans f.map_one.symm))
    let p (i : ℕ) := s (P.probe he b hb i)
    have hco (x : A) : s (Word.old (P.alphabet he) b x) = t (f x) :=
      DFunLike.congr_fun hc x
    have hp : ∀ i, t ((P.map f).factor i (i+1) (Nat.le_succ i)) * p (i+1) = p i := by
      intro i
      rw [map_factor]
      change t (f (P.factor i (i+1) (Nat.le_succ i))) * s (P.probe he b hb (i+1)) =
        s (P.probe he b hb i)
      rw [← hco,← s.map_mul,P.probe_transition he b hb]
    have hpexit : ∀ i, p i * t (f b) = t ((P.map f).terminal i * f e) := by
      intro i
      rw [map_terminal,← f.map_mul,← hco,← hco,← s.map_mul]
      exact congrArg s (P.probe_mul_b he b hb i)
    let l := (P.map f).presentedLift he' (f b) t p (fun i => (hp i).symm) hpexit
    have hlold : l.comp (Word.oldHom ((P.map f).alphabet he') (f b)) = t := by
      ext x; rfl
    have hlnew : l.comp (P.simulation he hf b) = s := by
      apply P.presentedHom_ext he b hb
      · intro x
        exact (hco x).symm
      · intro i
        simp only [MonoidHom.comp_apply,simulation_probe,l,presentedLift_probe,p]
    refine ⟨l,⟨hlnew,hlold⟩,?_⟩
    intro k hk
    apply (P.map f).presentedHom_ext he' (f b) hb'
    · intro x
      exact (DFunLike.congr_fun hk.2 x).trans (DFunLike.congr_fun hlold x).symm
    · intro i
      have hki := DFunLike.congr_fun hk.1 (P.probe he b hb i)
      simpa only [MonoidHom.comp_apply,simulation_probe,l,presentedLift_probe,p] using hki

end
end PartitionConsistency.ProbeAlgebra.Path


/-! ## PushoutPasting -/

/-! Universal-property bookkeeping for moving already selected cells before
omitted cells. These lemmas are about literal monoid pushouts; they do not
assert the existence of a selected subconstruction. -/
namespace PartitionConsistency.MonoidPushout
universe u
noncomputable section
variable {A B C D E F : Type u} [Monoid A] [Monoid B] [Monoid C]
  [Monoid D] [Monoid E] [Monoid F]

namespace IsPushout

/-- Two adjoining pushout squares give the outer pushout. In the diagram
`A → B → E`, `C → D → F`, the two vertical composites are unchanged. -/
theorem paste {f : A →* B} {g : A →* C} {i : B →* D} {j : C →* D}
    {k : B →* E} {l : D →* F} {m : E →* F}
    (h : IsPushout f g i j) (h' : IsPushout k i m l) :
    IsPushout (k.comp f) g m (l.comp j) where
  comm := by
    rw [← MonoidHom.comp_assoc,h'.comm,MonoidHom.comp_assoc,h.comm,
      MonoidHom.comp_assoc]
  universal b c hc := by
    let d := h.lift (b.comp k) c (by simpa only [MonoidHom.comp_assoc] using hc)
    have hd₁ : d.comp i = b.comp k := h.lift_comp_left _ _ _
    have hd₂ : d.comp j = c := h.lift_comp_right _ _ _
    let t := h'.lift b d hd₁.symm
    have ht₁ : t.comp m = b := h'.lift_comp_left _ _ _
    have ht₂ : t.comp l = d := h'.lift_comp_right _ _ _
    refine ⟨t,⟨ht₁,by rw [← MonoidHom.comp_assoc,ht₂,hd₂]⟩,?_⟩
    intro s hs
    apply h'.hom_ext
    · exact hs.1.trans ht₁.symm
    · rw [ht₂]
      apply h.hom_ext
      · rw [MonoidHom.comp_assoc,← h'.comm,← MonoidHom.comp_assoc,hs.1,hd₁]
      · rw [MonoidHom.comp_assoc,hs.2,hd₂]

/-- Conversely, if the left square and the outer rectangle are pushouts,
then the right square is a pushout. This is the cancellation used after the
selected future cells have been moved in front of one omitted cell. -/
theorem cancel_left {f : A →* B} {g : A →* C} {i : B →* D} {j : C →* D}
    {k : B →* E} {l : D →* F} {m : E →* F}
    (h : IsPushout f g i j) (hc : m.comp k = l.comp i)
    (ho : IsPushout (k.comp f) g m (l.comp j)) : IsPushout k i m l where
  comm := hc
  universal b d hd := by
    have he : b.comp (k.comp f) = (d.comp j).comp g := by
      rw [← MonoidHom.comp_assoc,hd,MonoidHom.comp_assoc,h.comm,
        MonoidHom.comp_assoc]
    let t := ho.lift b (d.comp j) he
    have ht₁ : t.comp m = b := ho.lift_comp_left _ _ _
    have ht₂ : t.comp (l.comp j) = d.comp j := ho.lift_comp_right _ _ _
    have ht : t.comp l = d := by
      apply h.hom_ext
      · rw [MonoidHom.comp_assoc,← hc,← MonoidHom.comp_assoc,ht₁,hd]
      · rw [MonoidHom.comp_assoc,ht₂]
    refine ⟨t,⟨ht₁,ht⟩,?_⟩
    intro s hs
    apply ho.hom_ext
    · exact hs.1.trans ht₁.symm
    · rw [← MonoidHom.comp_assoc,hs.2,← MonoidHom.comp_assoc,ht]

/-- The degenerate cell is also a pushout; no generator is added. -/
theorem of_id (f : A →* B) :
    IsPushout (MonoidHom.id A) f f (MonoidHom.id B) where
  comm := by simp only [MonoidHom.comp_id,MonoidHom.id_comp]
  universal a b h := by
    simp only [MonoidHom.comp_id] at h
    refine ⟨b,⟨h.symm,MonoidHom.comp_id b⟩,?_⟩
    intro t ht
    simpa only [MonoidHom.comp_id] using ht.2

/-- Postcomposing a pushout apex with a fixed monoid isomorphism preserves
its full universal property, not just its conservative embeddings. -/
theorem map_apex {f : A →* B} {g : A →* C} {i : B →* D} {j : C →* D}
    (h : IsPushout f g i j) (e : D ≃* E) :
    IsPushout f g (e.toMonoidHom.comp i) (e.toMonoidHom.comp j) where
  comm := by rw [MonoidHom.comp_assoc,h.comm,MonoidHom.comp_assoc]
  universal b c hc := by
    let t := (h.lift b c hc).comp e.symm.toMonoidHom
    have he (x : D) : t (e x) = h.lift b c hc x :=
      congrArg (h.lift b c hc) (e.symm_apply_apply x)
    have ht₁ : t.comp (e.toMonoidHom.comp i) = b := by
      ext x
      exact (he (i x)).trans (DFunLike.congr_fun (h.lift_comp_left b c hc) x)
    have ht₂ : t.comp (e.toMonoidHom.comp j) = c := by
      ext x
      exact (he (j x)).trans (DFunLike.congr_fun (h.lift_comp_right b c hc) x)
    refine ⟨t,⟨ht₁,ht₂⟩,?_⟩
    intro s hs
    have hh : s.comp e.toMonoidHom = t.comp e.toMonoidHom := by
      apply h.hom_ext
      · simpa only [MonoidHom.comp_assoc] using hs.1.trans ht₁.symm
      · simpa only [MonoidHom.comp_assoc] using hs.2.trans ht₂.symm
    ext x
    obtain ⟨y,rfl⟩ := e.surjective x
    exact DFunLike.congr_fun hh y

end IsPushout
end
end PartitionConsistency.MonoidPushout

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_ConservativeHulls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## MonoidColimit -/

/-! The directed unions used by the monoid construction retain their
universal property against arbitrary monoid homomorphisms. The stronger
category of conservative height/cost embeddings is not a restriction on
the presentation universal property. -/


/-! ## DirectedPushout -/


/-! ## ConservativeHull -/

/-! Countable conservative submonoids.  This closes an arbitrary countable
set under specified countable dependencies, right factors and joins.  It is
only the hull part of the countable-base rearrangement; it does not identify
the complement presentation with an iterated gate tower. -/

namespace PartitionConsistency.DiagramOrder
universe u
noncomputable section
open scoped Classical
variable {M : Type u} [LeftCancelMonoid M] [IsConical M]

instance instIsConicalSubtypeMemSubmonoid (S : Submonoid M) : IsConical S where
  eq_one_of_mul_eq_one {x y} h := by
    have h' : x.val * y.val = 1 := congrArg Subtype.val h
    obtain ⟨hx,hy⟩ := IsConical.eq_one_of_mul_eq_one h'
    exact ⟨Subtype.ext hx,Subtype.ext hy⟩

namespace ConservativeHull

/-- The unique right factor when it exists, and `1` otherwise. -/
def factor (x y : M) : M := if h : x ∣ y then h.choose else 1

omit [IsConical M] in
theorem factor_eq (x y z : M) (h : x*z = y) : factor x y = z := by
  have hxy : x ∣ y := ⟨z,h.symm⟩
  rw [factor,dite_eq_left hxy]
  exact mul_left_cancel (hxy.choose_spec.symm.trans h.symm)

/-- The conditional join when it exists, and `1` for a pair with disjoint
right cones. There is no completion added to the monoid. -/
def join (x y : M) : M :=
  if h : ∃ j : M, ∀ z : M, x ∣ z ∧ y ∣ z ↔ j ∣ z then h.choose else 1

theorem join_spec (hj : HasConditionalJoins (LeftDivOrder M)) (x y : M)
    (h : ∃ z : M, x ∣ z ∧ y ∣ z) :
    ∀ z : M, x ∣ z ∧ y ∣ z ↔ join x y ∣ z := by
  have hex : ∃ j : M, ∀ z : M, x ∣ z ∧ y ∣ z ↔ j ∣ z := by
    obtain ⟨z,hx,hy⟩ := h
    exact exists_cone_join hj x y z hx hy
  rw [join,dite_eq_left hex]
  exact hex.choose_spec

/-- Closing under right factors and the actual ambient conditional joins is
sufficient for all four conservation clauses. -/
theorem conservative (hj : HasConditionalJoins (LeftDivOrder M)) (S : Submonoid M)
    (hf : ∀ x ∈ S, ∀ y ∈ S, factor x y ∈ S)
    (hjS : ∀ x ∈ S, ∀ y ∈ S, join x y ∈ S) : Conservative S.subtype where
  injective := Subtype.val_injective
  factors x y z he := by
    exact ⟨⟨z, factor_eq x.val y.val z he ▸ hf x.val x.property y.val y.property⟩,rfl⟩
  intersections x y j h z := by
    have div_iff (a b : S) : a.val ∣ b.val ↔ a ∣ b := by
      constructor
      · rintro ⟨c,hc⟩
        exact ⟨⟨c,factor_eq a.val b.val c hc.symm ▸ hf _ a.property _ b.property⟩,
          Subtype.ext hc⟩
      · rintro ⟨c,hc⟩
        exact ⟨c.val,congrArg Subtype.val hc⟩
    have hxy : x.val ∣ j.val ∧ y.val ∣ j.val := by
      have hh := (h j).mpr (dvd_refl _)
      exact ⟨(div_iff x j).mpr hh.1,(div_iff y j).mpr hh.2⟩
    let l : S := ⟨join x.val y.val,hjS _ x.property _ y.property⟩
    have hl := join_spec hj x.val y.val ⟨j.val,hxy⟩
    have hlj : l.val ∣ j.val := (hl _).mp hxy
    have hjl : j.val ∣ l.val := by
      have hc := (hl l.val).mpr (dvd_refl _)
      exact (div_iff j l).mpr ((h l).mp
        ⟨(div_iff x l).mp hc.1,(div_iff y l).mp hc.2⟩)
    have heq : l.val = j.val := @le_antisymm (LeftDivOrder M) _ l.val j.val
      ((LeftDivOrder.le_iff_dvd (M := M) _ _).mpr hlj)
      ((LeftDivOrder.le_iff_dvd (M := M) _ _).mpr hjl)
    change x.val ∣ z ∧ y.val ∣ z ↔ j.val ∣ z
    rw [← heq]
    exact hl z
  common x y h := by
    let l : S := ⟨join x.val y.val,hjS _ x.property _ y.property⟩
    have hl := (join_spec hj x.val y.val h l.val).mpr (dvd_refl _)
    refine ⟨l,?_,?_⟩
    · obtain ⟨c,hc⟩ := hl.1
      exact ⟨⟨c,factor_eq x.val l.val c hc.symm ▸ hf _ x.property _ l.property⟩,
        Subtype.ext hc⟩
    · obtain ⟨c,hc⟩ := hl.2
      exact ⟨⟨c,factor_eq y.val l.val c hc.symm ▸ hf _ y.property _ l.property⟩,
        Subtype.ext hc⟩

variable (hj : HasConditionalJoins (LeftDivOrder M))
variable (s : Set M) (deps : M → Set M)

def operations (x y : M) : Set M := {x*y,factor x y,join x y} ∪ deps x

end ConservativeHull
end
end PartitionConsistency.DiagramOrder


/-! ## ConservativeCategory -/

/-! Conservative monoids without height/cost bookkeeping. The original
saturated tower forgets to this category. It is used for rearrangements:
heights are needed for scheduling ideals, but not for old-gate descent. -/
namespace PartitionConsistency.DiagramOrder
universe u
instance instLeftCancelMonoidSubtypeMemSubmonoid_solutions {M : Type u} [LeftCancelMonoid M] (S : Submonoid M) : LeftCancelMonoid S where
  toMonoid := inferInstance
  toIsLeftCancelMul := inferInstance
end PartitionConsistency.DiagramOrder

namespace PartitionConsistency.ConservativeMonoids
universe u v w
open DiagramOrder CategoryTheory CategoryTheory.Limits
noncomputable section

structure Object where
  Carrier : Type u
  [monoid : LeftCancelMonoid Carrier]
  [conical : IsConical Carrier]
  joins : HasConditionalJoins (LeftDivOrder Carrier)

instance instCoeSortObjectType : CoeSort Object.{u} (Type u) := ⟨Object.Carrier⟩
attribute [instance] Object.monoid Object.conical

structure Hom (M : Object.{u}) (N : Object.{v}) extends M →* N where
  conservative : Conservative toMonoidHom

instance instCoeFunHomForallCarrier {M : Object.{u}} {N : Object.{v}} : CoeFun (Hom M N) (fun _ => M → N) :=
  ⟨fun f => f.toMonoidHom⟩
namespace Hom
variable {M : Object.{u}} {N : Object.{v}} {R : Object.{w}}

@[ext] theorem ext {f g : Hom M N} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g
  congr 1
  exact MonoidHom.ext h

def id (M : Object.{u}) : Hom M M := ⟨MonoidHom.id M,Conservative.id M⟩
def comp (g : Hom N R) (f : Hom M N) : Hom M R :=
  ⟨g.toMonoidHom.comp f.toMonoidHom,f.conservative.comp g.conservative⟩

@[simp] theorem id_apply (x : M) : (id M) x = x := rfl
@[simp] theorem comp_apply (g : Hom N R) (f : Hom M N) (x : M) :
    (g.comp f) x = g (f x) := rfl
@[simp] theorem id_comp (f : Hom M N) : (id N).comp f = f := by ext; rfl
@[simp] theorem comp_id (f : Hom M N) : f.comp (id M) = f := by ext; rfl

theorem injective (f : Hom M N) : Function.Injective f := f.conservative.injective
end Hom

instance instCategoryObject : Category Object.{u} where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f
  id_comp := by intros; apply Hom.ext; intro; rfl
  comp_id := by intros; apply Hom.ext; intro; rfl
  assoc := by intros; apply Hom.ext; intro; rfl

instance instCoeFunHomObjectForallCarrier (M N : Object.{u}) : CoeFun (M ⟶ N) (fun _ => M → N) := ⟨fun f => f.toMonoidHom⟩

end
end PartitionConsistency.ConservativeMonoids

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_ConservativeCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## ConservativeIntersections -/

/-! The intersections used when a presentation is restricted to a countable
hull. This establishes conservation at arbitrary cuts, not just selected cuts. -/
namespace PartitionConsistency.DiagramOrder.Conservative
universe u v w
open ConservativeHull
noncomputable section
variable {A : Type u} {B : Type v} {C : Type w}
variable [LeftCancelMonoid A] [IsConical A] [LeftCancelMonoid B] [IsConical B]
  [LeftCancelMonoid C] [IsConical C]
variable {f : A →* B} (hf : Conservative f)

omit [IsConical A] [IsConical B] in
include hf in
theorem map_factor (x y : A) : f (factor x y) = factor (f x) (f y) := by
  by_cases h : x ∣ y
  · exact (ConservativeHull.factor_eq (f x) (f y) (f (factor x y)) (by
      rw [← map_mul, factor, dite_eq_left h]; exact congrArg f h.choose_spec.symm)).symm
  · have h' := mt (hf.dvd_iff x y).mp h
    simp only [factor,dite_eq_right h,dite_eq_right h',f.map_one]

include hf in
/-- The selected conditional join (or the identity for disjoint cones) is
preserved literally by every conservative map of conditional-join monoids. -/
theorem map_join (hA : HasConditionalJoins (LeftDivOrder A))
    (hB : HasConditionalJoins (LeftDivOrder B)) (x y : A) :
    f (join x y) = join (f x) (f y) := by
  by_cases h : ∃ z : A, x ∣ z ∧ y ∣ z
  · have h' : ∃ z : B, f x ∣ z ∧ f y ∣ z := (hf.common_iff x y).mpr h
    have hl := hf.intersections x y (join x y) (join_spec hA x y h)
    have hr := join_spec hB (f x) (f y) h'
    apply @le_antisymm (LeftDivOrder B) _
    · exact (LeftDivOrder.le_iff_dvd _ _).mpr ((hl _).mp ((hr _).mpr (dvd_refl _)))
    · exact (LeftDivOrder.le_iff_dvd _ _).mpr ((hr _).mp ((hl _).mpr (dvd_refl _)))
  · have h₀ : ¬ ∃ j : A, ∀ z : A, x ∣ z ∧ y ∣ z ↔ j ∣ z := by
      rintro ⟨j,hj⟩; exact h ⟨j,(hj j).mpr (dvd_refl j)⟩
    have h₁ : ¬ ∃ j : B, ∀ z : B, f x ∣ z ∧ f y ∣ z ↔ j ∣ z := by
      rintro ⟨j,hj⟩; exact h (hf.common x y ⟨j,(hj j).mpr (dvd_refl j)⟩)
    simp only [join,dite_eq_right h₀,dite_eq_right h₁,f.map_one]

omit [IsConical A] [IsConical B] [IsConical C] in
/-- Conservation reflects through a conservative final embedding. -/
theorem of_comp {g : B →* C} (hg : Conservative g) (hgf : Conservative (g.comp f)) :
    Conservative f where
  injective := by intro x y h; exact hgf.injective (congrArg g h)
  factors x y z h := by
    obtain ⟨t,ht⟩ := hgf.factors x y (g z) (by
      change g (f x) * g z = g (f y); rw [← g.map_mul,h])
    exact ⟨t,hg.injective ht⟩
  intersections x y j hj z := by
    have h := hgf.intersections x y j hj (g z)
    change g (f x) ∣ g z ∧ g (f y) ∣ g z ↔ g (f j) ∣ g z at h
    simpa only [hg.dvd_iff] using h
  common x y h := by
    obtain ⟨z,hx,hy⟩ := h
    exact hgf.common x y ⟨g z,g.map_dvd hx,g.map_dvd hy⟩

end
end PartitionConsistency.DiagramOrder.Conservative

namespace PartitionConsistency.DiagramOrder.ConservativeHull
universe u
noncomputable section
variable {M : Type u} [LeftCancelMonoid M] [IsConical M]
variable (hj : HasConditionalJoins (LeftDivOrder M)) (S : Submonoid M)
variable (hf : ∀ x ∈ S, ∀ y ∈ S, factor x y ∈ S)
  (hc : ∀ x ∈ S, ∀ y ∈ S, join x y ∈ S)

include hj hf hc
/-- A submonoid closed under the uniquely determined factors and joins has
conditional joins of its own. -/
theorem conditionalJoins : HasConditionalJoins (LeftDivOrder S) := by
  intro x y z hx hy
  let l : S := ⟨join x.val y.val,hc _ x.property _ y.property⟩
  have hco := conservative hj S hf hc
  have h := join_spec hj x.val y.val
    ⟨z.val,S.subtype.map_dvd ((LeftDivOrder.le_iff_dvd _ _).mp hx),
      S.subtype.map_dvd ((LeftDivOrder.le_iff_dvd _ _).mp hy)⟩
  refine ⟨l,(pair_lub_iff (α := LeftDivOrder S) x y l).mpr ?_⟩
  intro w
  rw [LeftDivOrder.le_iff_dvd (M := S) x w,
    LeftDivOrder.le_iff_dvd (M := S) y w, LeftDivOrder.le_iff_dvd (M := S) l w]
  change ((x : S) ∣ (w : S)) ∧ ((y : S) ∣ (w : S)) ↔ l ∣ (w : S)
  exact ((hco.dvd_iff x w).symm.and (hco.dvd_iff y w).symm).trans
    ((h w.val).trans (hco.dvd_iff l w))

end
end PartitionConsistency.DiagramOrder.ConservativeHull

namespace PartitionConsistency.ConservativeMonoids
universe u
open DiagramOrder DiagramOrder.ConservativeHull
noncomputable section
variable {M : Object.{u}}

/-- Closure under factors and ambient joins supplies a genuine object. -/
def closedObject (S : Submonoid M)
    (hf : ∀ x ∈ S, ∀ y ∈ S, factor x y ∈ S)
    (hc : ∀ x ∈ S, ∀ y ∈ S, join x y ∈ S) : Object.{u} :=
  ⟨S,conditionalJoins M.joins S hf hc⟩

def closedInclusion (S : Submonoid M)
    (hf : ∀ x ∈ S, ∀ y ∈ S, factor x y ∈ S)
    (hc : ∀ x ∈ S, ∀ y ∈ S, join x y ∈ S) :
    closedObject S hf hc ⟶ M := ⟨S.subtype,conservative M.joins S hf hc⟩

/-- A conservative subobject can equivalently be specified by its carrier
submonoid and its two countably-ary closure requirements. -/
structure Subobject (M : Object.{u}) where
  submonoid : Submonoid M
  factors : ∀ x ∈ submonoid, ∀ y ∈ submonoid, factor x y ∈ submonoid
  joins : ∀ x ∈ submonoid, ∀ y ∈ submonoid, join x y ∈ submonoid

namespace Subobject

def object (S : Subobject M) : Object.{u} := closedObject S.submonoid S.factors S.joins

def inclusion (S : Subobject M) : S.object ⟶ M :=
  closedInclusion S.submonoid S.factors S.joins

/-- Conservative intersections exist at every original tower cut. -/
def inf (S R : Subobject M) : Subobject M where
  submonoid := S.submonoid ⊓ R.submonoid
  factors _ hx _ hy := ⟨S.factors _ hx.1 _ hy.1,R.factors _ hx.2 _ hy.2⟩
  joins _ hx _ hy := ⟨S.joins _ hx.1 _ hy.1,R.joins _ hx.2 _ hy.2⟩

/-- Images of actual conservative maps are conservative subobjects. -/
def range {N : Object.{u}} (f : M ⟶ N) : Subobject N where
  submonoid := MonoidHom.mrange f.toMonoidHom
  factors := by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
    exact ⟨factor x y,f.conservative.map_factor x y⟩
  joins := by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
    exact ⟨join x y,f.conservative.map_join M.joins N.joins x y⟩

end Subobject
end
end PartitionConsistency.ConservativeMonoids


/-! ## Cell -/

/-! The actual countably presented operations, with their conservative
simulations and finite coefficient supports. These are the cells in the
original schedule, forgetting only the height/cost bookkeeping. -/
namespace PartitionConsistency.ConservativeMonoids
universe u
open DiagramOrder DiagramForcing MonoidPushout
noncomputable section

structure Probe (M : Object.{u}) where
  a : M
  b : M
  e : M
  b_ne_one : b ≠ 1
  e_ne_one : e ≠ 1
  path : ProbeAlgebra.Path M a

namespace Probe
variable {M N : Object.{u}} (d : Probe M)

def extension : Object.{u} where
  Carrier := d.path.Extension d.e_ne_one d.b
  monoid := inferInstance
  conical := inferInstance
  joins := d.path.extension_hasConditionalJoins d.e_ne_one d.b M.joins d.b_ne_one

def inclusion : M ⟶ d.extension :=
  ⟨ProbeAlgebra.Word.oldHom (d.path.alphabet d.e_ne_one) d.b,
    d.path.oldHom_conservative d.e_ne_one d.b⟩

def generator (i : ℕ) : d.extension := d.path.probe d.e_ne_one d.b d.b_ne_one i

def map (f : M ⟶ N) : Probe N :=
  ⟨f d.a,f d.b,f d.e,(fun h => d.b_ne_one (f.injective (h.trans f.map_one.symm))),
    (fun h => d.e_ne_one (f.injective (h.trans f.map_one.symm))),d.path.map f.toMonoidHom⟩

def simulation (f : M ⟶ N) : d.extension ⟶ (d.map f).extension :=
  ⟨d.path.simulation d.e_ne_one f.conservative d.b,
    d.path.simulation_conservative d.e_ne_one f.conservative d.b M.joins d.b_ne_one⟩

@[simp] theorem simulation_inclusion (f : M ⟶ N) (x : M) :
    d.simulation f (d.inclusion x) = (d.map f).inclusion (f x) := rfl

@[simp] theorem simulation_generator (f : M ⟶ N) (i : ℕ) :
    d.simulation f (d.generator i) = (d.map f).generator i :=
  d.path.simulation_probe d.e_ne_one f.conservative d.b d.b_ne_one i

theorem pushout (f : M ⟶ N) :
    IsPushout d.inclusion.toMonoidHom f.toMonoidHom (d.simulation f).toMonoidHom
      (d.map f).inclusion.toMonoidHom :=
  d.path.simulation_pushout d.e_ne_one f.conservative d.b d.b_ne_one

/-- An extension is generated by the whole old monoid and its countably
many displayed generators. This is proved from the literal presentation. -/
theorem generated (S : Submonoid d.extension)
    (ho : ∀ x : M, d.inclusion x ∈ S) (hn : ∀ i, d.generator i ∈ S) : S = ⊤ := by
  let f : M →* S :=
    { toFun := fun x => ⟨d.inclusion x,ho x⟩
      map_one' := Subtype.ext d.inclusion.map_one
      map_mul' x y := Subtype.ext (d.inclusion.map_mul x y) }
  let p : ℕ → S := fun i => ⟨d.generator i,hn i⟩
  have hp : ∀ i, p i = f (d.path.factor i (i+1) (Nat.le_succ i)) * p (i+1) := by
    intro i
    apply Subtype.ext
    exact (d.path.probe_transition d.e_ne_one d.b d.b_ne_one (Nat.le_succ i)).symm
  have hx : ∀ i, p i * f d.b = f (d.path.terminal i * d.e) := by
    intro i
    apply Subtype.ext
    exact d.path.probe_mul_b d.e_ne_one d.b d.b_ne_one i
  let l := d.path.presentedLift d.e_ne_one d.b f p hp hx
  have h : S.subtype.comp l = MonoidHom.id d.extension := by
    apply d.path.presentedHom_ext d.e_ne_one d.b d.b_ne_one
    · intro x; rfl
    · intro i
      change (l (d.generator i)).val = d.generator i
      rw [show l (d.generator i) = p i from
        d.path.presentedLift_probe d.e_ne_one d.b f p hp hx d.b_ne_one i]
  apply top_unique
  intro x _
  have hh := (l x).property
  rwa [show (l x).val = x from DFunLike.congr_fun h x] at hh

/-- Only these countably many old elements are needed to specify a probe
cell; factors along the path belong to every conservative subobject that
contains the displayed endpoints. -/
def parameters : Set M := {d.a,d.b,d.e} ∪ Set.range d.path.node

end Probe

structure Merger (M : Object.{u}) where
  n : ℕ
  prescription : OverlapPrescription M n
  valid : prescription.Valid

namespace Merger
variable {M N : Object.{u}} (d : Merger M)

def extension : Object.{u} where
  Carrier := d.prescription.Merger d.valid
  monoid := inferInstance
  conical := inferInstance
  joins := d.prescription.merger_hasConditionalJoins d.valid M.joins

def inclusion : M ⟶ d.extension :=
  ⟨MergerAlgebra.Word.oldHom,MergerAlgebra.Word.oldHom_conservative⟩

def generator (i : Fin d.n) : d.extension := d.prescription.root d.valid i

def map (f : M ⟶ N) : Merger N :=
  ⟨d.n,d.prescription.map f.toMonoidHom,d.prescription.valid_map d.valid M.joins f.conservative⟩

def simulation (f : M ⟶ N) : d.extension ⟶ (d.map f).extension :=
  ⟨d.prescription.mergerSimulation d.valid M.joins f.conservative,
    d.prescription.mergerSimulation_conservative d.valid M.joins f.conservative⟩

@[simp] theorem simulation_inclusion (f : M ⟶ N) (x : M) :
    d.simulation f (d.inclusion x) = (d.map f).inclusion (f x) := rfl

@[simp] theorem simulation_generator (f : M ⟶ N) (i : Fin d.n) :
    d.simulation f (d.generator i) = (d.map f).generator i :=
  d.prescription.mergerSimulation_root d.valid M.joins f.conservative i

theorem pushout (f : M ⟶ N) :
    IsPushout d.inclusion.toMonoidHom f.toMonoidHom (d.simulation f).toMonoidHom
      (d.map f).inclusion.toMonoidHom :=
  d.prescription.mergerSimulation_pushout d.valid M.joins f.conservative

theorem generated (S : Submonoid d.extension)
    (ho : ∀ x : M, d.inclusion x ∈ S) (hn : ∀ i, d.generator i ∈ S) : S = ⊤ := by
  let f : M →* S :=
    { toFun := fun x => ⟨d.inclusion x,ho x⟩
      map_one' := Subtype.ext d.inclusion.map_one
      map_mul' x y := Subtype.ext (d.inclusion.map_mul x y) }
  let p : Fin d.n → S := fun i => ⟨d.generator i,hn i⟩
  have hp : d.prescription.Satisfies f p := by
    intro i j a b hij hab
    apply Subtype.ext
    exact d.prescription.roots_satisfy d.valid i j a b hij hab
  let l := d.prescription.presentedLift d.valid f p hp
  have h : S.subtype.comp l = MonoidHom.id d.extension := by
    apply d.prescription.presentedHom_ext d.valid
    · intro x; rfl
    · intro i
      change (l (d.generator i)).val = d.generator i
      rw [show l (d.generator i) = p i from
        d.prescription.presentedLift_root d.valid f p hp i]
  apply top_unique
  intro x _
  have hh := (l x).property
  rwa [show (l x).val = x from DFunLike.congr_fun h x] at hh

def parameters : Set M :=
  {x | ∃ i j a b, d.prescription.start i j = some (a,b) ∧ (x = a ∨ x = b)}

end Merger

abbrev Cell (M : Object.{u}) := Probe M ⊕ Merger M

namespace Cell
variable {M N : Object.{u}}

def extension : Cell M → Object.{u}
  | .inl d => d.extension
  | .inr d => d.extension

def inclusion : (d : Cell M) → M ⟶ d.extension
  | .inl d => d.inclusion
  | .inr d => d.inclusion

def Generators : Cell M → Type
  | .inl _ => ℕ
  | .inr d => Fin d.n

instance instCountableGenerators (d : Cell M) : Countable d.Generators := by cases d <;> dsimp [Generators] <;> infer_instance

def generator : (d : Cell M) → d.Generators → d.extension
  | .inl d => d.generator
  | .inr d => d.generator

def parameters : Cell M → Set M
  | .inl d => d.parameters
  | .inr d => d.parameters

def map : Cell M → (M ⟶ N) → Cell N
  | .inl d,f => .inl (d.map f)
  | .inr d,f => .inr (d.map f)

def simulation : (d : Cell M) → (f : M ⟶ N) → d.extension ⟶ (d.map f).extension
  | .inl d,f => d.simulation f
  | .inr d,f => d.simulation f

theorem pushout (d : Cell M) (f : M ⟶ N) :
    IsPushout d.inclusion.toMonoidHom f.toMonoidHom (d.simulation f).toMonoidHom
      (d.map f).inclusion.toMonoidHom := by
  cases d with
  | inl d => exact d.pushout f
  | inr d => exact d.pushout f

theorem generated (d : Cell M) (S : Submonoid d.extension)
    (ho : ∀ x : M, d.inclusion x ∈ S) (hn : ∀ i, d.generator i ∈ S) : S = ⊤ := by
  cases d with
  | inl d => exact d.generated S ho hn
  | inr d => exact d.generated S ho hn

theorem mem_closure (d : Cell M) (x : d.extension) :
    x ∈ Submonoid.closure (Set.range d.inclusion ∪ Set.range d.generator) := by
  rw [d.generated _ (fun x => Submonoid.subset_closure (Or.inl ⟨x,rfl⟩))
    (fun i => Submonoid.subset_closure (Or.inr ⟨i,rfl⟩))]
  trivial

/-- The countable list of new generators remains whole, but each particular
word uses just finitely many old coefficients. No finite support is claimed
for the countable path which specifies the cell. -/
theorem finite_coefficients (d : Cell M) (x : d.extension) :
    ∃ s : Finset M, x ∈ Submonoid.closure (d.inclusion '' (s : Set M) ∪ Set.range d.generator) := by
  classical
  apply Submonoid.closure_induction (s := Set.range d.inclusion ∪ Set.range d.generator)
    (motive := fun x _ => ∃ s : Finset M,
      x ∈ Submonoid.closure (d.inclusion '' (s : Set M) ∪ Set.range d.generator))
    ?_ ?_ ?_ (d.mem_closure x)
  · intro y hy
    rcases hy with ⟨a,rfl⟩ | ⟨i,rfl⟩
    · exact ⟨{a},Submonoid.subset_closure (Or.inl ⟨a,by simp,rfl⟩)⟩
    · exact ⟨∅,Submonoid.subset_closure (Or.inr ⟨i,rfl⟩)⟩
  · exact ⟨∅,Submonoid.one_mem _⟩
  · rintro y z _ _ ⟨s,hs⟩ ⟨t,ht⟩
    refine ⟨s ∪ t,Submonoid.mul_mem _ ?_ ?_⟩
    · apply (Submonoid.closure_mono (Set.union_subset_union ?_ Set.Subset.rfl)) hs
      exact Set.image_mono (by intro a ha; exact Finset.mem_union.mpr (Or.inl ha))
    · apply (Submonoid.closure_mono (Set.union_subset_union ?_ Set.Subset.rfl)) ht
      exact Set.image_mono (by intro a ha; exact Finset.mem_union.mpr (Or.inr ha))

end Cell

end
end PartitionConsistency.ConservativeMonoids

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_CellTowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CellRestriction -/

/-! Reflecting a scheduled operation to a conservative subobject that
contains its literal countable parameter set. -/
namespace PartitionConsistency.ConservativeMonoids
universe u
open DiagramOrder DiagramForcing
noncomputable section

namespace Probe
variable {M N : Object.{u}}

@[ext] theorem ext {d c : Probe M} (ha : d.a = c.a) (hb : d.b = c.b)
    (he : d.e = c.e) (hn : d.path.node = c.path.node) : d = c := by
  cases d with | mk a b e hb' he' p =>
    cases c with | mk a' b' e' hb'' he'' q =>
      dsimp only at ha hb he hn
      subst a'; subst b'; subst e'
      cases p; cases q
      congr

/-- No closure-of-path assertion is presumed: divisibility is reflected by
conservation, and the actual countably many nodes are pulled back. -/
theorem exists_preimage (d : Probe N) (f : M ⟶ N)
    (h : d.parameters ⊆ Set.range f) : ∃ c : Probe M, c.map f = d := by
  classical
  obtain ⟨a,ha⟩ := h (show d.a ∈ d.parameters from Or.inl (by simp))
  obtain ⟨b,hb⟩ := h (show d.b ∈ d.parameters from Or.inl (by simp))
  obtain ⟨e,he⟩ := h (show d.e ∈ d.parameters from Or.inl (by simp))
  have hn : ∀ i, ∃ n, f n = d.path.node i :=
    fun i => h (Or.inr ⟨i,rfl⟩)
  choose n hn using hn
  have hzero : n 0 = 1 := f.injective (by rw [hn,d.path.zero,f.map_one])
  have hinc {i j : ℕ} (hij : i ≤ j) : n i ∣ n j :=
    (f.conservative.dvd_iff _ _).mp (by rw [hn,hn]; exact d.path.increasing hij)
  have hbound (i : ℕ) : n i ∣ a :=
    (f.conservative.dvd_iff _ _).mp (by rw [hn,ha]; exact d.path.bounded i)
  have hb' : b ≠ 1 := by intro hh; apply d.b_ne_one; rw [← hb,hh,f.map_one]
  have he' : e ≠ 1 := by intro hh; apply d.e_ne_one; rw [← he,hh,f.map_one]
  let c : Probe M := ⟨a,b,e,hb',he',⟨n,hzero,hinc,hbound⟩⟩
  exact ⟨c,ext ha hb he (funext hn)⟩

end Probe

namespace Merger
variable {M N : Object.{u}}

/-- The finite presentation uses only the displayed starts. Every validity
clause is reflected along the conservative inclusion, not added as a new
hypothesis on the selected prescription. -/
theorem exists_preimage (d : Merger N) (f : M ⟶ N)
    (h : d.parameters ⊆ Set.range f) : ∃ c : Merger M, c.map f = d := by
  classical
  have hs : ∀ i j a b, d.prescription.start i j = some (a,b) →
      ∃ x y, f x = a ∧ f y = b := by
    intro i j a b hab
    obtain ⟨x,hx⟩ := h ⟨i,j,a,b,hab,Or.inl rfl⟩
    obtain ⟨y,hy⟩ := h ⟨i,j,a,b,hab,Or.inr rfl⟩
    exact ⟨x,y,hx,hy⟩
  let start (i j : Fin d.n) : Option (M × M) :=
    match he : d.prescription.start i j with
    | none => none
    | some (a,b) => some ((hs i j a b he).choose,(hs i j a b he).choose_spec.choose)
  let P : OverlapPrescription M d.n := ⟨start⟩
  have hm : P.map f.toMonoidHom = d.prescription := by
    have heq : (P.map f.toMonoidHom).start = d.prescription.start := by
      funext i j
      change (start i j).map _ = d.prescription.start i j
      dsimp only [start]
      split
      · rename_i he
        simp only [Option.map_none,he]
      · rename_i a b he
        simp only [he,Option.map_some,Option.some.injEq]
        exact Prod.ext (hs i j a b he).choose_spec.choose_spec.1
          (hs i j a b he).choose_spec.choose_spec.2
    exact congrArg OverlapPrescription.mk heq
  have hp : P.Valid := P.valid_of_map f.conservative (hm ▸ d.valid)
  let c : Merger M := ⟨d.n,P,hp⟩
  refine ⟨c,?_⟩
  have heq : Merger.mk d.n (P.map f.toMonoidHom)
      (P.valid_map hp M.joins f.conservative) = Merger.mk d.n d.prescription d.valid := by
    congr 1
  exact heq.trans (by cases d; rfl)

end Merger

namespace Cell
variable {M N : Object.{u}}

theorem exists_preimage (d : Cell N) (f : M ⟶ N)
    (h : d.parameters ⊆ Set.range f) : ∃ c : Cell M, c.map f = d := by
  cases d with
  | inl d =>
    obtain ⟨c,hc⟩ := d.exists_preimage f h
    exact ⟨.inl c,congrArg Sum.inl hc⟩
  | inr d =>
    obtain ⟨c,hc⟩ := d.exists_preimage f h
    exact ⟨.inr c,congrArg Sum.inr hc⟩

end Cell
end
end PartitionConsistency.ConservativeMonoids


/-! ## CellularTower -/

/-! Cellular towers inside their actual terminal monoid. The countable hull
retains literal generators and finite old coefficients. -/
namespace PartitionConsistency.DiagramOrder.Conservative
universe u v
variable {M : Type u} {N : Type v} [LeftCancelMonoid M] [IsConical M]
  [LeftCancelMonoid N] [IsConical N]

omit [IsConical M] [IsConical N] in
/-- A monoid isomorphism preserves all four conservation conditions. -/
theorem of_mulEquiv (e : M ≃* N) : Conservative e.toMonoidHom where
  injective := e.injective
  factors x y z _ := ⟨e.symm z,e.apply_symm_apply z⟩
  intersections x y j h z := by
    obtain ⟨w,rfl⟩ := e.surjective z
    change (e x ∣ e w ∧ e y ∣ e w ↔ e j ∣ e w)
    simpa only [map_dvd_iff] using h w
  common x y h := by
    obtain ⟨z,hx,hy⟩ := h
    obtain ⟨w,rfl⟩ := e.surjective z
    exact ⟨w, (map_dvd_iff e).mp hx, (map_dvd_iff e).mp hy⟩
end PartitionConsistency.DiagramOrder.Conservative

namespace PartitionConsistency.ConservativeMonoids
universe u
open DiagramOrder DiagramOrder.ConservativeHull CategoryTheory MonoidPushout
noncomputable section
open scoped Classical

def ofMulEquiv {M N : Object.{u}} (e : M ≃* N) : M ⟶ N :=
  ⟨e.toMonoidHom,Conservative.of_mulEquiv e⟩

namespace Subobject
variable {T : Object.{u}}

@[ext] theorem ext {S R : Subobject T} (h : S.submonoid = R.submonoid) : S = R := by
  cases S; cases R; cases h; rfl

def top : Subobject T where
  submonoid := ⊤
  factors := by intros; trivial
  joins := by intros; trivial

def hom {S R : Subobject T} (h : S.submonoid ≤ R.submonoid) : S.object ⟶ R.object :=
  ⟨Submonoid.inclusion h,Conservative.of_comp R.inclusion.conservative
    (show Conservative (R.inclusion.toMonoidHom.comp (Submonoid.inclusion h)) from
      S.inclusion.conservative)⟩

@[simp] theorem hom_apply {S R : Subobject T} (h : S.submonoid ≤ R.submonoid)
    (x : S.object) : (hom h x).val = x.val := rfl

end Subobject
/-- An actual presentation cell, identified with a subobject of the very
same terminal monoid. The identification fixes every old element. -/
structure Attachment {T : Object.{u}} (S R : Subobject T) where
  cell : Cell S.object
  equiv : cell.extension ≃* R.object
  old : ∀ x : S.object, (equiv (cell.inclusion x)).val = x.val

namespace Attachment
variable {T : Object.{u}} {S R : Subobject T} (d : Attachment S R)

def embedding : d.cell.extension ⟶ T := R.inclusion.comp (ofMulEquiv d.equiv)

def generator (i : d.cell.Generators) : T := d.embedding (d.cell.generator i)

def parameters : Set T := S.inclusion '' d.cell.parameters

@[simp] theorem embedding_old (x : S.object) : d.embedding (d.cell.inclusion x) = x.val :=
  d.old x

/-- A retained word has a finite list of old coefficients, even in a
countably presented cell. -/
theorem finite_coefficients (x : R.object) :
    ∃ s : Finset S.object, x.val ∈ Submonoid.closure
      (S.inclusion '' (s : Set S.object) ∪ Set.range d.generator) := by
  obtain ⟨s,hs⟩ := d.cell.finite_coefficients (d.equiv.symm x)
  refine ⟨s,?_⟩
  let Q := Submonoid.closure (S.inclusion '' (s : Set S.object) ∪ Set.range d.generator)
  have h : Submonoid.closure (d.cell.inclusion '' (s : Set S.object) ∪
      Set.range d.cell.generator) ≤ Q.comap d.embedding.toMonoidHom := by
    apply Submonoid.closure_le.mpr
    rintro z (⟨y,hy,rfl⟩ | ⟨i,rfl⟩)
    · change d.embedding (d.cell.inclusion y) ∈ Q
      rw [d.embedding_old]
      exact Submonoid.subset_closure (Or.inl ⟨y,hy,rfl⟩)
    · exact Submonoid.subset_closure (Or.inr ⟨i,rfl⟩)
  have hh := h hs
  change (d.equiv (d.equiv.symm x)).val ∈ Q at hh
  simpa only [d.equiv.apply_symm_apply] using hh

end Attachment

variable (T : Object.{u}) (J : Type u) [LinearOrder J] [OrderBot J] [OrderTop J]
  [SuccOrder J] [WellFoundedLT J]

/-- The original construction as a continuous tower of literal cells.
Identity steps are allowed, so a selected or an omitted subconstruction can
keep the same index order without compressing its limit cuts. -/
structure CellTower where
  stage : J → Subobject T
  mono : Monotone (fun i => (stage i).submonoid)
  terminal : (stage ⊤).submonoid = ⊤
  continuous : ∀ i, Order.IsSuccLimit i → ∀ x, x ∈ (stage i).submonoid →
    ∃ j < i, x ∈ (stage j).submonoid
  step : ∀ i, (stage i).submonoid = (stage (Order.succ i)).submonoid ∨
    Nonempty (Attachment (stage i) (stage (Order.succ i)))

namespace CellTower
variable {T J} (D : CellTower T J)

/-- The unique original successor where an element first appears. -/
def NewAt (i : J) (x : T) : Prop :=
  x ∈ (D.stage (Order.succ i)).submonoid ∧ x ∉ (D.stage i).submonoid

omit [OrderBot J] [WellFoundedLT J] in
theorem NewAt.not_isMax {i : J} {x : T} (h : D.NewAt i x) : ¬ IsMax i := by
  intro hi
  exact h.2 ((show Order.succ i = i from Order.succ_eq_iff_isMax.mpr hi) ▸ h.1)

omit [OrderBot J] [WellFoundedLT J] in
theorem NewAt.neq {i : J} {x : T} (h : D.NewAt i x) :
    (D.stage i).submonoid ≠ (D.stage (Order.succ i)).submonoid := by
  intro he
  exact h.2 (he ▸ h.1)

omit [OrderBot J] [WellFoundedLT J] in
theorem NewAt.unique {i j : J} {x : T} (hi : D.NewAt i x) (hj : D.NewAt j x) : i = j := by
  apply le_antisymm
  · by_contra h
    have hd := (Order.succ_le_iff_of_not_isMax (hj.not_isMax D)).mpr (lt_of_not_ge h)
    exact hi.2 (D.mono hd hj.1)
  · by_contra h
    have hd := (Order.succ_le_iff_of_not_isMax (hi.not_isMax D)).mpr (lt_of_not_ge h)
    exact hj.2 (D.mono hd hi.1)

omit [WellFoundedLT J]

def newIndex (x : T) : J := if h : ∃ i, D.NewAt i x then h.choose else ⊥

theorem newIndex_eq {x : T} {i : J} (h : D.NewAt i x) : D.newIndex x = i := by
  have he : ∃ j, D.NewAt j x := ⟨i,h⟩
  rw [newIndex,dite_eq_left he]
  exact NewAt.unique D he.choose_spec h

/-- The chosen cell at an active stage is independent of the queried word. -/
def stepCell (i : J) (h : (D.stage i).submonoid ≠ (D.stage (Order.succ i)).submonoid) :
    Attachment (D.stage i) (D.stage (Order.succ i)) := ((D.step i).resolve_left h).some

def coefficients (i : J) (h : (D.stage i).submonoid ≠ (D.stage (Order.succ i)).submonoid)
    (x : (D.stage (Order.succ i)).object) : Finset (D.stage i).object :=
  ((D.stepCell i h).finite_coefficients x).choose

def dependencies (x : T) : Set T :=
  if h : D.NewAt (D.newIndex x) x then
    (D.stepCell (D.newIndex x) (h.neq D)).parameters ∪
      Set.range (D.stepCell (D.newIndex x) (h.neq D)).generator ∪
      (D.stage (D.newIndex x)).inclusion ''
        (D.coefficients (D.newIndex x) (h.neq D) ⟨x,h.1⟩ : Set (D.stage (D.newIndex x)).object)
  else ∅

theorem dependencies_at {i : J} {x : T} (h : D.NewAt i x) :
    D.dependencies x = (D.stepCell i (h.neq D)).parameters ∪
      Set.range (D.stepCell i (h.neq D)).generator ∪
      (D.stage i).inclusion '' (D.coefficients i (h.neq D) ⟨x,h.1⟩ :
        Set (D.stage i).object) := by
  have hi := D.newIndex_eq h
  subst i
  rw [dependencies,dite_eq_left h]

end CellTower
end
end PartitionConsistency.ConservativeMonoids

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_CellCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CellCut -/

/-! The selected subconstruction at every original cut. Closing the retained
words under their dependencies supplies actual restricted cells. -/
namespace PartitionConsistency.MonoidPushout.IsPushout
universe u
noncomputable section
variable {A B C D E : Type u} [Monoid A] [Monoid B] [Monoid C] [Monoid D] [Monoid E]

/-- Replacing the upper-right corner by an isomorphic monoid does not
change a presentation pushout. -/
theorem change_left {f : A →* B} {g : A →* C} {i : B →* D} {j : C →* D}
    (h : IsPushout f g i j) (e : B ≃* E) :
    IsPushout (e.toMonoidHom.comp f) g (i.comp e.symm.toMonoidHom) j where
  comm := by ext x; simpa using DFunLike.congr_fun h.comm x
  universal b c hc := by
    let b' := b.comp e.toMonoidHom
    have hc' : b'.comp f = c.comp g := by simpa only [b',MonoidHom.comp_assoc] using hc
    let t := h.lift b' c hc'
    have ht : t.comp i = b' := h.lift_comp_left _ _ _
    have ht' : t.comp j = c := h.lift_comp_right _ _ _
    have he : t.comp (i.comp e.symm.toMonoidHom) = b := by
      ext x
      have hh := DFunLike.congr_fun ht (e.symm x)
      simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.apply_symm_apply,b'] using hh
    refine ⟨t,⟨he,ht'⟩,?_⟩
    intro s hs
    apply h.hom_ext
    · ext x
      have hh := DFunLike.congr_fun hs.1 (e x)
      have hh' := DFunLike.congr_fun he (e x)
      simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply]
        using hh.trans hh'.symm
    · exact hs.2.trans ht'.symm
end
end PartitionConsistency.MonoidPushout.IsPushout

namespace PartitionConsistency.ConservativeMonoids
universe u
open CategoryTheory DiagramOrder MonoidPushout
noncomputable section
open scoped Classical

namespace Cell
variable {M N : Object.{u}}

@[simp] theorem simulation_old (d : Cell M) (f : M ⟶ N) (x : M) :
    d.simulation f (d.inclusion x) = (d.map f).inclusion (f x) := by cases d <;> rfl

theorem simulation_generator_range (d : Cell M) (f : M ⟶ N) :
    Set.range (fun i => d.simulation f (d.generator i)) = Set.range (d.map f).generator := by
  cases d with
  | inl d => exact congrArg Set.range (funext (d.simulation_generator f))
  | inr d => exact congrArg Set.range (funext (d.simulation_generator f))
end Cell

namespace CellTower
variable {T : Object.{u}} {J : Type u} [LinearOrder J] [OrderBot J] [OrderTop J]
  [SuccOrder J] (D : CellTower T J) (S : Subobject T)

def Closed : Prop := ∀ x ∈ S.submonoid, D.dependencies x ⊆ S.submonoid

def selected (i : J) : Prop := ∃ x ∈ S.submonoid, D.NewAt i x

def restrict (i : J) : Subobject T := S.inf (D.stage i)

omit [OrderBot J] in
theorem restrict_le (i : J) : (D.restrict S i).submonoid ≤ (D.stage i).submonoid := fun _ h => h.2

omit [OrderBot J] in
theorem restrict_mono : Monotone (fun i => (D.restrict S i).submonoid) :=
  fun _ _ h _ hx => ⟨hx.1,D.mono h hx.2⟩

omit [OrderBot J] in
theorem restrict_omitted {i : J} (h : ¬ D.selected S i) :
    (D.restrict S i).submonoid = (D.restrict S (Order.succ i)).submonoid := by
  apply le_antisymm (D.restrict_mono S (Order.le_succ i))
  intro x hx
  exact ⟨hx.1,by by_contra hh; exact h ⟨x,hx.1,hx.2,hh⟩⟩

/-- All the parameters and all the countably many generators are retained
as soon as one new word of this cell is retained. -/
theorem selected_dependencies (hS : D.Closed S) {i : J} (hi : D.selected S i) :
    ∃ h : (D.stage i).submonoid ≠ (D.stage (Order.succ i)).submonoid,
      (D.stepCell i h).parameters ⊆ S.submonoid ∧
        Set.range (D.stepCell i h).generator ⊆ S.submonoid := by
  obtain ⟨x,hx,hin⟩ := hi
  refine ⟨hin.neq D,?_,?_⟩
  all_goals
    have hh := hS x hx
    rw [D.dependencies_at hin] at hh
  · exact fun _ hm => hh (Or.inl (Or.inl hm))
  · exact fun _ hm => hh (Or.inl (Or.inr hm))

/-- Every retained new word is still generated by retained old coefficients
and the generators of this very same cell. -/
theorem selected_word (hS : D.Closed S) {i : J}
    (h : (D.stage i).submonoid ≠ (D.stage (Order.succ i)).submonoid)
    {x : T} (hx : x ∈ S.submonoid) (hi : D.NewAt i x) :
    x ∈ Submonoid.closure ((D.restrict S i).submonoid ∪
      Set.range (D.stepCell i h).generator) := by
  let c := D.coefficients i h ⟨x,hi.1⟩
  have hc : (D.stage i).inclusion '' (c : Set (D.stage i).object) ⊆ S.submonoid := by
    have hh := hS x hx
    rw [D.dependencies_at hi] at hh
    exact fun _ hm => hh (Or.inr hm)
  have hc' : (D.stage i).inclusion '' (c : Set (D.stage i).object) ⊆
      (D.restrict S i).submonoid := by
    rintro z ⟨y,hy,rfl⟩
    exact ⟨hc ⟨y,hy,rfl⟩,y.property⟩
  exact (Submonoid.closure_mono (Set.union_subset_union hc' Set.Subset.rfl))
    ((D.stepCell i h).finite_coefficients ⟨x,hi.1⟩).choose_spec

/-- A selected successor really is the operation restricted to the retained
base. Its inclusion into the original successor is the conservative cell
simulation. This theorem includes the full presentation pushout. -/
theorem restrict_selected (hS : D.Closed S) {i : J} (hi : D.selected S i) :
    Nonempty (Attachment (D.restrict S i) (D.restrict S (Order.succ i))) ∧
    IsPushout (Subobject.hom (D.restrict_mono S (Order.le_succ i))).toMonoidHom
      (Subobject.hom (D.restrict_le S i)).toMonoidHom
      (Subobject.hom (D.restrict_le S (Order.succ i))).toMonoidHom
      (Subobject.hom (D.mono (Order.le_succ i))).toMonoidHom := by
  obtain ⟨h,hp,hg⟩ := D.selected_dependencies S hS hi
  let d := D.stepCell i h
  let f := Subobject.hom (D.restrict_le S i)
  have hp' : d.cell.parameters ⊆ Set.range f := by
    intro x hx
    exact ⟨⟨x.val,hp ⟨x,hx,rfl⟩,x.property⟩,Subtype.ext rfl⟩
  obtain ⟨c,hc⟩ := d.cell.exists_preimage f hp'
  have work (c : Cell (D.restrict S i).object)
      (cell : Cell (D.stage i).object) (hc : c.map f = cell)
      (e : cell.extension ≃* (D.stage (Order.succ i)).object)
      (he : ∀ x : (D.stage i).object, (e (cell.inclusion x)).val = x.val)
      (hgen : Set.range (fun k => (e (cell.generator k)).val) ⊆ S.submonoid)
      (hwords : ∀ x ∈ S.submonoid, D.NewAt i x →
        x ∈ Submonoid.closure ((D.restrict S i).submonoid ∪
          Set.range (fun k => (e (cell.generator k)).val))) :
      Nonempty (Attachment (D.restrict S i) (D.restrict S (Order.succ i))) ∧
      IsPushout (Subobject.hom (D.restrict_mono S (Order.le_succ i))).toMonoidHom
        f.toMonoidHom (Subobject.hom (D.restrict_le S (Order.succ i))).toMonoidHom
        (Subobject.hom (D.mono (Order.le_succ i))).toMonoidHom := by
    subst cell
    let m := (D.stage (Order.succ i)).inclusion.comp
      ((ofMulEquiv e).comp (c.simulation f))
    have mo (x : (D.restrict S i).object) : m (c.inclusion x) = x.val := by
      change (e (c.simulation f (c.inclusion x))).val = x.val
      rw [c.simulation_old]
      exact he (f x)
    have mg : Set.range (fun k => m (c.generator k)) =
        Set.range (fun k => (e ((c.map f).generator k)).val) := by
      have hh := congrArg (fun s => (fun y => (e y).val) '' s)
        (c.simulation_generator_range f)
      rw [← Set.range_comp,← Set.range_comp] at hh
      exact hh
    have sm : ∀ x : c.extension, m x ∈ S.submonoid := by
      let Q := S.submonoid.comap m.toMonoidHom
      have hQ : Q = ⊤ := c.generated Q
        (fun x => by change m (c.inclusion x) ∈ S.submonoid; rw [mo]; exact x.property.1)
        (fun k => hgen (mg ▸ Set.mem_range_self k))
      intro x
      exact (show x ∈ Q from hQ ▸ Submonoid.mem_top x)
    have rm : ∀ x : c.extension, m x ∈ (D.restrict S (Order.succ i)).submonoid :=
      fun x => ⟨sm x,(e (c.simulation f x)).property⟩
    let m' : c.extension →* (D.restrict S (Order.succ i)).object :=
      { toFun := fun x => ⟨m x,rm x⟩
        map_one' := Subtype.ext m.map_one
        map_mul' x y := Subtype.ext (m.map_mul x y) }
    have hm : Function.Bijective m' := by
      refine ⟨?_,?_⟩
      · intro x y hh
        apply m.injective
        exact congrArg (fun z : (D.restrict S (Order.succ i)).object => z.val) hh
      · intro x
        have hl : (D.restrict S i).submonoid ≤ MonoidHom.mrange m.toMonoidHom := by
          intro y hy
          exact ⟨c.inclusion ⟨y,hy⟩,mo ⟨y,hy⟩⟩
        have hn : Set.range (fun k => (e ((c.map f).generator k)).val) ⊆
            MonoidHom.mrange m.toMonoidHom := by
          rw [← mg]
          rintro _ ⟨k,rfl⟩
          exact ⟨c.generator k,rfl⟩
        have hh : x.val ∈ MonoidHom.mrange m.toMonoidHom := by
          by_cases ho : x.val ∈ (D.stage i).submonoid
          · exact hl ⟨x.property.1,ho⟩
          · exact (Submonoid.closure_le.mpr (Set.union_subset hl hn))
              (hwords x.val x.property.1 ⟨x.property.2,ho⟩)
        obtain ⟨z,hz⟩ := hh
        exact ⟨z,Subtype.ext hz⟩
    let e' := MulEquiv.ofBijective m' hm
    have hpo := ((c.pushout f).map_apex e).change_left e'
    have h₁ : e'.toMonoidHom.comp c.inclusion.toMonoidHom =
        (Subobject.hom (D.restrict_mono S (Order.le_succ i))).toMonoidHom := by
      ext x; apply Subtype.ext; exact mo x
    have h₂ : (e.toMonoidHom.comp (c.simulation f).toMonoidHom).comp e'.symm.toMonoidHom =
        (Subobject.hom (D.restrict_le S (Order.succ i))).toMonoidHom := by
      ext x
      apply Subtype.ext
      exact congrArg (fun z : (D.restrict S (Order.succ i)).object => z.val) (e'.apply_symm_apply x)
    have h₃ : e.toMonoidHom.comp (c.map f).inclusion.toMonoidHom =
        (Subobject.hom (D.mono (Order.le_succ i))).toMonoidHom := by
      ext x; apply Subtype.ext; exact he x
    rw [h₁,h₂,h₃] at hpo
    exact ⟨⟨⟨c,e',mo⟩⟩,hpo⟩
  have hh : ∀ x ∈ S.submonoid, D.NewAt i x →
      x ∈ Submonoid.closure ((D.restrict S i).submonoid ∪ Set.range d.generator) :=
    fun _ hx hin => D.selected_word S hS h hx hin
  exact work c d.cell hc d.equiv d.old hg hh

end CellTower
end
end PartitionConsistency.ConservativeMonoids


/-! ## CellFunctor -/

/-! Functoriality of the actual presentations. A redundant natural-number
list of generators avoids changing index types during base change. -/
namespace PartitionConsistency.ConservativeMonoids.Cell
universe u
open CategoryTheory DiagramOrder DiagramForcing
noncomputable section
open scoped Classical
variable {M N P : Object.{u}}

def naturalGenerator : (d : Cell M) → ℕ → d.extension
  | .inl d,i => d.generator i
  | .inr d,i => if h : i < d.n then d.generator ⟨i,h⟩ else 1

theorem hom_ext {R : Type u} [Monoid R] (d : Cell M) {f g : d.extension →* R}
    (ho : ∀ x, f (d.inclusion x) = g (d.inclusion x))
    (hn : ∀ i, f (d.naturalGenerator i) = g (d.naturalGenerator i)) : f = g := by
  cases d with
  | inl d => exact d.path.presentedHom_ext d.e_ne_one d.b d.b_ne_one f g ho hn
  | inr d =>
    apply d.prescription.presentedHom_ext d.valid f g ho
    rintro ⟨i,hi⟩
    have hh := hn i
    dsimp only [naturalGenerator] at hh
    erw [dite_eq_left hi] at hh
    exact hh

@[simp] theorem simulation_naturalGenerator (d : Cell M) (f : M ⟶ N) (i : ℕ) :
    d.simulation f (d.naturalGenerator i) = (d.map f).naturalGenerator i := by
  cases d with
  | inl d => exact d.simulation_generator f i
  | inr d =>
    dsimp only [map,naturalGenerator,simulation,Merger.map]
    by_cases hi : i < d.n
    · erw [dite_eq_left hi, dite_eq_left hi]
      exact d.simulation_generator f _
    · erw [dite_eq_right hi, dite_eq_right hi]
      exact (d.simulation f).map_one

def cast {c d : Cell M} (h : c = d) : c.extension ≃* d.extension := h ▸ MulEquiv.refl _

@[simp] theorem cast_old {c d : Cell M} (h : c = d) (x : M) :
    cast h (c.inclusion x) = d.inclusion x := by subst d; rfl

@[simp] theorem cast_naturalGenerator {c d : Cell M} (h : c = d) (i : ℕ) :
    cast h (c.naturalGenerator i) = d.naturalGenerator i := by subst d; rfl

theorem map_comp (d : Cell M) (f : M ⟶ N) (g : N ⟶ P) :
    (d.map f).map g = d.map (g.comp f) := by
  cases d with
  | inl d =>
    apply congrArg Sum.inl
    exact Probe.ext rfl rfl rfl rfl
  | inr d =>
    apply congrArg Sum.inr
    have hh : (d.prescription.map f.toMonoidHom).map g.toMonoidHom =
        d.prescription.map (g.comp f).toMonoidHom := by
      have hst : ((d.prescription.map f.toMonoidHom).map g.toMonoidHom).start =
          (d.prescription.map (g.comp f).toMonoidHom).start := by
        funext i j
        dsimp only [OverlapPrescription.map]
        cases d.prescription.start i j <;> rfl
      exact congrArg OverlapPrescription.mk hst
    change Merger.mk _ _ _ = Merger.mk _ _ _
    congr 1

/-- Simulating along two conservative maps is the literal simulation along
the composite, after the presentation-theoretic identification. -/
theorem simulation_comp (d : Cell M) (f : M ⟶ N) (g : N ⟶ P) :
    (cast (d.map_comp f g)).toMonoidHom.comp
      (((d.map f).simulation g).toMonoidHom.comp (d.simulation f).toMonoidHom) =
      (d.simulation (g.comp f)).toMonoidHom := by
  apply d.hom_ext
  · intro x
    change cast _ ((d.map f).simulation g (d.simulation f (d.inclusion x))) =
      d.simulation (g.comp f) (d.inclusion x)
    simp only [simulation_old,cast_old,Hom.comp_apply]
  · intro i
    change cast _ ((d.map f).simulation g (d.simulation f (d.naturalGenerator i))) =
      d.simulation (g.comp f) (d.naturalGenerator i)
    simp only [simulation_naturalGenerator,cast_naturalGenerator]

end
end PartitionConsistency.ConservativeMonoids.Cell


/-! ## CellBaseChange -/

/-! A selected cell can be simulated over any conservative intermediate
base. Full monoid pushouts identify the presentations, while explicit cell
simulations prove that the intermediate presentation embeds conservatively. -/
namespace PartitionConsistency.MonoidPushout.IsPushout
universe u
noncomputable section
variable {A B C D : Type u} [Monoid A] [Monoid B] [Monoid C] [Monoid D]
variable {f : A →* B} {g : A →* C} {i : B →* D} {j : C →* D}

theorem generated (h : IsPushout f g i j) (S : Submonoid D)
    (hb : ∀ x, i x ∈ S) (hc : ∀ x, j x ∈ S) : S = ⊤ := by
  let b : B →* S :=
    { toFun := fun x => ⟨i x,hb x⟩
      map_one' := Subtype.ext i.map_one
      map_mul' x y := Subtype.ext (i.map_mul x y) }
  let c : C →* S :=
    { toFun := fun x => ⟨j x,hc x⟩
      map_one' := Subtype.ext j.map_one
      map_mul' x y := Subtype.ext (j.map_mul x y) }
  have hbc : b.comp f = c.comp g := by
    ext x
    exact congrArg (fun m : A →* D => m x) h.comm
  let l := h.lift b c hbc
  have hl : S.subtype.comp l = MonoidHom.id D := by
    apply h.hom_ext
    · rw [MonoidHom.comp_assoc,h.lift_comp_left,MonoidHom.id_comp]; rfl
    · rw [MonoidHom.comp_assoc,h.lift_comp_right,MonoidHom.id_comp]; rfl
  apply top_unique
  intro x _
  have hh := (l x).property
  rwa [show (l x).val = x from DFunLike.congr_fun hl x] at hh
end
end PartitionConsistency.MonoidPushout.IsPushout

namespace PartitionConsistency.ConservativeMonoids
universe u
open CategoryTheory DiagramOrder MonoidPushout
noncomputable section
open scoped Classical

namespace Subobject
variable {T : Object.{u}}

/-- A commutative square of actual inclusions which is a pushout among all
monoids, not merely among conservative maps. -/
structure Square (A B C D : Subobject T) : Prop where
  ab : A.submonoid ≤ B.submonoid
  ac : A.submonoid ≤ C.submonoid
  bd : B.submonoid ≤ D.submonoid
  cd : C.submonoid ≤ D.submonoid
  pushout : IsPushout (hom ab).toMonoidHom (hom ac).toMonoidHom
    (hom bd).toMonoidHom (hom cd).toMonoidHom

namespace Square
variable {A B C D : Subobject T} (h : Square A B C D)

include h in
theorem apex_eq_sup : D.submonoid = B.submonoid ⊔ C.submonoid := by
  apply le_antisymm ?_ (sup_le h.bd h.cd)
  let Q := (B.submonoid ⊔ C.submonoid).comap D.inclusion.toMonoidHom
  have hQ := h.pushout.generated Q
    (fun x => (show B.submonoid ≤ B.submonoid ⊔ C.submonoid from le_sup_left) x.property)
    (fun x => (show C.submonoid ≤ B.submonoid ⊔ C.submonoid from le_sup_right) x.property)
  intro x hx
  exact (show (⟨x,hx⟩ : D.object) ∈ Q from hQ ▸ Submonoid.mem_top _)

theorem presentationPushout (d : Attachment A B) :
    IsPushout d.cell.inclusion.toMonoidHom (hom h.ac).toMonoidHom
      ((hom h.bd).toMonoidHom.comp d.equiv.toMonoidHom) (hom h.cd).toMonoidHom := by
  have hp := h.pushout.change_left d.equiv.symm
  have h₁ : d.equiv.symm.toMonoidHom.comp (hom h.ab).toMonoidHom =
      d.cell.inclusion.toMonoidHom := by
    ext x
    apply d.equiv.injective
    simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,d.equiv.apply_symm_apply]
      using! (Subtype.ext (d.old x)).symm
  rw [h₁] at hp
  exact hp

/-- The canonical cell base-change is identified with the given apex by
its universal property. -/
def realization (d : Attachment A B) :
    (d.cell.map (hom h.ac)).extension ≃* D.object :=
  (d.cell.pushout (hom h.ac)).equiv (h.presentationPushout d)

@[simp] theorem realization_old (d : Attachment A B) (x : C.object) :
    (h.realization d ((d.cell.map (hom h.ac)).inclusion x)).val = x.val :=
  congrArg (fun z : D.object => z.val)
    (DFunLike.congr_fun ((d.cell.pushout (hom h.ac)).equiv_comp_right (h.presentationPushout d)) x)

@[simp] theorem realization_new (d : Attachment A B) (x : d.cell.extension) :
    (h.realization d (d.cell.simulation (hom h.ac) x)).val = (d.equiv x).val :=
  congrArg (fun z : D.object => z.val)
    (DFunLike.congr_fun ((d.cell.pushout (hom h.ac)).equiv_comp_left (h.presentationPushout d)) x)

end Square
end Subobject

namespace Hom
variable {M N : Object.{u}} (f : M ⟶ N)

/-- A conservative embedding identifies its domain with its actual range. -/
def rangeEquiv : M ≃* (Subobject.range f).object := by
  let m : M →* (Subobject.range f).object :=
    { toFun := fun x => ⟨f x,⟨x,rfl⟩⟩
      map_one' := Subtype.ext f.map_one
      map_mul' x y := Subtype.ext (f.map_mul x y) }
  exact MulEquiv.ofBijective m
    ⟨fun _ _ h => f.injective (congrArg Subtype.val h),by
      rintro ⟨x,y,hy⟩
      exact ⟨y,Subtype.ext hy⟩⟩

@[simp] theorem rangeEquiv_val (x : M) : (f.rangeEquiv x).val = f x := rfl
end Hom

namespace Subobject.Square
variable {T : Object.{u}} {A B C D E : Subobject T}

/-- Intermediate base change stays inside the original successor. Its
carrier is exactly the submonoid generated by the intermediate base and
the retained successor, not an enlarged conservative hull. -/
theorem intermediate (h : Square A B C D) (d : Attachment A B)
    (ha : A.submonoid ≤ E.submonoid) (hc : E.submonoid ≤ C.submonoid) :
    ∃ F : Subobject T, F.submonoid = B.submonoid ⊔ E.submonoid ∧
      F.submonoid ≤ D.submonoid ∧ Nonempty (Attachment E F) ∧ Square A B E F := by
  let f := hom ha
  let g := hom hc
  have hcomp : g.comp f = hom h.ac := by ext x; rfl
  have heq : (d.cell.map f).map g = d.cell.map (hom h.ac) :=
    (d.cell.map_comp f g).trans (congrArg d.cell.map hcomp)
  let e := h.realization d
  let m := D.inclusion.comp ((ofMulEquiv e).comp
    ((ofMulEquiv (Cell.cast heq)).comp ((d.cell.map f).simulation g)))
  have mo (x : E.object) : m ((d.cell.map f).inclusion x) = x.val := by
    change (e (Cell.cast heq ((d.cell.map f).simulation g ((d.cell.map f).inclusion x)))).val = x.val
    rw [Cell.simulation_old,Cell.cast_old]
    exact h.realization_old d (g x)
  have mn (x : d.cell.extension) : m (d.cell.simulation f x) = (d.equiv x).val := by
    have hn : Cell.cast heq ((d.cell.map f).simulation g (d.cell.simulation f x)) =
        d.cell.simulation (hom h.ac) x := by
      have hh := DFunLike.congr_fun (d.cell.simulation_comp f g) x
      cases hcomp
      exact hh
    change (e (Cell.cast heq ((d.cell.map f).simulation g (d.cell.simulation f x)))).val = _
    rw [hn]
    exact h.realization_new d x
  let F := Subobject.range m
  have hEF : E.submonoid ≤ F.submonoid := by
    intro x hx
    exact ⟨(d.cell.map f).inclusion ⟨x,hx⟩,mo ⟨x,hx⟩⟩
  have hBF : B.submonoid ≤ F.submonoid := by
    intro x hx
    refine ⟨d.cell.simulation f (d.equiv.symm ⟨x,hx⟩),?_⟩
    erw [mn,d.equiv.apply_symm_apply]
  let e' := m.rangeEquiv
  have hp := ((d.cell.pushout f).map_apex e').change_left d.equiv
  have h₁ : d.equiv.toMonoidHom.comp d.cell.inclusion.toMonoidHom =
      (hom h.ab).toMonoidHom := by ext x; apply Subtype.ext; exact d.old x
  have h₂ : (e'.toMonoidHom.comp (d.cell.simulation f).toMonoidHom).comp
      d.equiv.symm.toMonoidHom = (hom hBF).toMonoidHom := by
    ext x
    apply Subtype.ext
    exact (mn (d.equiv.symm x)).trans (congrArg (fun z : B.object => z.val) (d.equiv.apply_symm_apply x))
  have h₃ : e'.toMonoidHom.comp (d.cell.map f).inclusion.toMonoidHom =
      (hom hEF).toMonoidHom := by ext x; apply Subtype.ext; exact mo x
  rw [h₁,h₂,h₃] at hp
  let hs : Square A B E F := ⟨h.ab,ha,hBF,hEF,hp⟩
  refine ⟨F,hs.apex_eq_sup,?_,⟨⟨d.cell.map f,e',mo⟩⟩,hs⟩
  rintro x ⟨y,rfl⟩
  exact (e (Cell.cast heq ((d.cell.map f).simulation g y))).property

end Subobject.Square
end
end PartitionConsistency.ConservativeMonoids

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_CellReorder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CellUnion -/

/-! Directed unions of conservative submonoids and of their presentation
pushouts. Every union here is inside the original terminal monoid. -/
namespace PartitionConsistency.ConservativeMonoids.Subobject
universe u v
open CategoryTheory DiagramOrder MonoidPushout
noncomputable section
open scoped Classical
variable {T : Object.{u}}

/-- Directed unions do not add factors or conditional joins. -/
def directedSup {K : Type u} [Nonempty K] (F : K → Subobject T)
    (hF : Directed (· ≤ ·) (fun k => (F k).submonoid)) : Subobject T where
  submonoid := ⨆ k, (F k).submonoid
  factors := by
    intro x hx y hy
    obtain ⟨i,hi⟩ := (Submonoid.mem_iSup_of_directed hF).mp hx
    obtain ⟨j,hj⟩ := (Submonoid.mem_iSup_of_directed hF).mp hy
    obtain ⟨k,hik,hjk⟩ := hF i j
    exact (le_iSup (fun k => (F k).submonoid) k) ((F k).factors x (hik hi) y (hjk hj))
  joins := by
    intro x hx y hy
    obtain ⟨i,hi⟩ := (Submonoid.mem_iSup_of_directed hF).mp hx
    obtain ⟨j,hj⟩ := (Submonoid.mem_iSup_of_directed hF).mp hy
    obtain ⟨k,hik,hjk⟩ := hF i j
    exact (le_iSup (fun k => (F k).submonoid) k) ((F k).joins x (hik hi) y (hjk hj))

section UnionLift
variable {K : Type u} [Preorder K] [IsDirectedOrder K] [Nonempty K]
  (F : K → Subobject T) (hF : Monotone (fun k => (F k).submonoid))
  (U : Subobject T) (hle : ∀ k, (F k).submonoid ≤ U.submonoid)
  (hcovers : ∀ x ∈ U.submonoid, ∃ k, x ∈ (F k).submonoid)
  {N : Type v} [Monoid N] (f : ∀ k, (F k).object →* N)
  (hf : ∀ i j (h : i ≤ j), (f j).comp (hom (hF h)).toMonoidHom = f i)

def unionValue (x : U.object) : N :=
  f (hcovers x.val x.property).choose
    ⟨x.val,(hcovers x.val x.property).choose_spec⟩

include hf in
omit [Nonempty K] in
theorem unionValue_at (k : K) (x : (F k).object) :
    unionValue F U hcovers f (hom (hle k) x) = f k x := by
  let i := (hcovers x.val ((hle k) x.property)).choose
  have hi := (hcovers x.val ((hle k) x.property)).choose_spec
  obtain ⟨j,hij,hkj⟩ := exists_ge_ge i k
  have e₁ := DFunLike.congr_fun (hf i j hij) ⟨x.val,hi⟩
  have e₂ := DFunLike.congr_fun (hf k j hkj) x
  exact e₁.symm.trans e₂

/-- A compatible family of arbitrary monoid homomorphisms glues over an
actual directed union. -/
def unionLift : U.object →* N where
  toFun := unionValue F U hcovers f
  map_one' := by
    let k : K := Classical.arbitrary K
    exact (unionValue_at F hF U hle hcovers f hf k 1).trans (f k).map_one
  map_mul' x y := by
    obtain ⟨i,hi⟩ := hcovers x.val x.property
    obtain ⟨j,hj⟩ := hcovers y.val y.property
    obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
    let a : (F k).object := ⟨x.val,hF hik hi⟩
    let b : (F k).object := ⟨y.val,hF hjk hj⟩
    have ha : hom (hle k) a = x := Subtype.ext rfl
    have hb : hom (hle k) b = y := Subtype.ext rfl
    rw [← ha,← hb,← (hom (hle k)).map_mul]
    rw [unionValue_at F hF U hle hcovers f hf k,
      unionValue_at F hF U hle hcovers f hf k,
      unionValue_at F hF U hle hcovers f hf k]
    exact (f k).map_mul a b

@[simp] theorem unionLift_comp (k : K) :
    (unionLift F hF U hle hcovers f hf).comp (hom (hle k)).toMonoidHom = f k := by
  ext x
  exact unionValue_at F hF U hle hcovers f hf k x

end UnionLift

namespace Square
variable {A B C D E F : Subobject T}

theorem identity (h : A.submonoid ≤ B.submonoid) : Square A A B B :=
  ⟨le_refl _,h,h,le_refl _,IsPushout.of_id (hom h).toMonoidHom⟩

theorem paste (h : Square A B C D) (h' : Square B E D F) : Square A E C F :=
  ⟨h.ab.trans h'.ab,h.ac,h'.bd,h.cd.trans h'.cd,h.pushout.paste h'.pushout⟩

theorem cancel_left (h : Square A B C D) (ho : Square A E C F)
    (hBE : B.submonoid ≤ E.submonoid) (hDF : D.submonoid ≤ F.submonoid) :
    Square B E D F :=
  ⟨hBE,h.bd,ho.bd,hDF,h.pushout.cancel_left (by ext x; rfl) ho.pushout⟩

end Square
end
end PartitionConsistency.ConservativeMonoids.Subobject


/-! ## CellReorder -/

/-! Rearranging the actual tower: a countable dependency-closed submonoid
can be performed first, and every omitted cell can then be appended in its
original order. The construction uses full monoid pushouts at all cuts. -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_BlockTowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## BlockIndex -/

/-! Lexicographic concatenation of the actual rounds. The extra cut at the
end of each round is retained, making passage to the next initial cut an
identity step. -/
namespace PartitionConsistency.ConservativeMonoids
universe u
noncomputable section
open scoped Classical
namespace BlockIndex
variable {I : Type u} {J : I → Type u}
variable [LinearOrder I] [WellFoundedLT I] [OrderBot I] [NoMaxOrder I] [SuccOrder I]
variable [∀ i, LinearOrder (J i)] [∀ i, WellFoundedLT (J i)]
variable [∀ i, OrderBot (J i)] [∀ i, OrderTop (J i)] [∀ i, SuccOrder (J i)]

abbrev Interior (I : Type u) (J : I → Type u) := Lex (Sigma J)
abbrev Index (I : Type u) (J : I → Type u) := WithTop (Interior I J)

instance instWellFoundedLTInterior : WellFoundedLT (Interior I J) := by
  constructor
  constructor
  rintro ⟨i,j⟩
  induction i using (wellFounded_lt (α := I)).induction with
  | h i ih =>
    induction j using (wellFounded_lt (α := J i)).induction with
    | h j jh =>
      constructor
      rintro ⟨k,l⟩ hl
      cases hl with
      | left _ _ hk => exact ih k hk l
      | right _ _ hl => exact jh l hl

instance instSuccOrderIndex : SuccOrder (Index I J) := SuccOrder.ofLinearWellFoundedLT _

def cut (i : I) (j : J i) : Index I J := WithTop.some (toLex ⟨i,j⟩)

section
omit [WellFoundedLT I] [OrderBot I] [NoMaxOrder I] [SuccOrder I]
  [∀ i, WellFoundedLT (J i)] [∀ i, OrderBot (J i)] [∀ i, OrderTop (J i)]
  [∀ i, SuccOrder (J i)]

@[simp] theorem cut_le_cut (i : I) (j k : J i) : cut i j ≤ cut i k ↔ j ≤ k := by
  simp [cut, Sigma.Lex.le_def]
  change (i < i ∨ i = i ∧ j ≤ k) ↔ j ≤ k
  simp
@[simp] theorem cut_lt_cut (i : I) (j k : J i) : cut i j < cut i k ↔ j < k := by
  simp [cut, Sigma.Lex.lt_def]
  change (i < i ∨ i = i ∧ j < k) ↔ j < k
  simp
theorem cut_lt_of_lt {i k : I} (h : i < k) (j : J i) (l : J k) : cut i j < cut k l :=
  WithTop.coe_lt_coe.mpr (Sigma.Lex.left _ _ h)
@[simp] theorem cut_lt_top (i : I) (j : J i) : cut i j < ⊤ := WithTop.coe_lt_top _
end

omit [WellFoundedLT I] [NoMaxOrder I] [SuccOrder I]
  [∀ i, WellFoundedLT (J i)] [∀ i, OrderTop (J i)] [∀ i, SuccOrder (J i)] in
@[simp] theorem cut_bot : cut (⊥ : I) (⊥ : J ⊥) = (⊥ : Index I J) := rfl

omit [OrderBot I] [NoMaxOrder I] [SuccOrder I] [∀ i, OrderBot (J i)] in
/-- Successors within a block. -/
theorem succ_inner (i : I) (j : J i) (hj : j < ⊤) :
    Order.succ (cut i j) = cut i (Order.succ j) := by
  apply CovBy.succ_eq
  apply WithTop.coe_covBy_coe.mpr
  have H := Order.covBy_succ_of_not_isMax (not_isMax_iff_ne_top.mpr hj.ne)
  refine ⟨Sigma.Lex.right _ _ H.lt,?_⟩
  rintro ⟨k,l⟩ h₁ h₂
  cases h₁ with
  | left _ _ h₁ =>
    cases h₂ with
    | left _ _ h₂ => exact h₁.not_gt h₂
    | right _ _ _ => exact lt_irrefl _ h₁
  | right _ _ h₁ =>
    cases h₂ with
    | left _ _ h₂ => exact lt_irrefl _ h₂
    | right _ _ h₂ => exact H.2 h₁ h₂

omit [OrderBot I] [∀ i, SuccOrder (J i)] in
/-- The final cut of one block is followed by the initial cut of the next. -/
theorem succ_boundary (i : I) :
    Order.succ (cut i (⊤ : J i)) = cut (Order.succ i) (⊥ : J (Order.succ i)) := by
  apply CovBy.succ_eq
  apply WithTop.coe_covBy_coe.mpr
  refine ⟨Sigma.Lex.left _ _ (Order.lt_succ i),?_⟩
  rintro ⟨k,l⟩ h₁ h₂
  cases h₁ with
  | left _ _ h₁ =>
    cases h₂ with
    | left _ _ h₂ => exact (Order.covBy_succ i).2 h₁ h₂
    | right _ _ h₂ => exact not_lt_bot h₂
  | right _ _ h₁ => exact not_top_lt h₁

omit [OrderBot I] [NoMaxOrder I] [SuccOrder I] in
/-- A noninitial limit inside a block must be a limit of that block. -/
theorem inner_limit {i : I} {j : J i} (h : Order.IsSuccLimit (cut i j)) (hj : j ≠ ⊥) :
    Order.IsSuccLimit j := by
  refine ⟨not_isMin_iff_ne_bot.mpr hj,?_⟩
  intro k hk
  have hkt : k < ⊤ := hk.lt.trans_le le_top
  have he := succ_inner i k hkt
  rw [hk.succ_eq] at he
  exact (not_isMax_iff_ne_top.mpr (cut_lt_top i k).ne) ((he ▸ h).isMax)

omit [∀ i, SuccOrder (J i)] in
/-- A limit at an initial cut must be an outer limit (not a successor or
zero). This includes the identity boundary cuts in the argument. -/
theorem outer_limit {i : I} (h : Order.IsSuccLimit (cut i (⊥ : J i))) :
    Order.IsSuccLimit i := by
  refine ⟨?_,?_⟩
  · intro hi
    have hi' := hi.eq_bot
    subst i
    exact h.ne_bot cut_bot
  · intro k hk
    have he := succ_boundary (J := J) k
    rw [hk.succ_eq] at he
    exact (not_isMax_iff_ne_top.mpr (cut_lt_top k (⊤ : J k)).ne) ((he ▸ h).isMax)

end BlockIndex
end
end PartitionConsistency.ConservativeMonoids


/-! ## BlockTower -/

namespace PartitionConsistency.ConservativeMonoids
universe u
noncomputable section
open scoped Classical
open BlockIndex
variable {I : Type u} {J : I → Type u}
variable [LinearOrder I] [WellFoundedLT I] [OrderBot I] [NoMaxOrder I] [SuccOrder I]
variable [∀ i, LinearOrder (J i)] [∀ i, WellFoundedLT (J i)]
variable [∀ i, OrderBot (J i)] [∀ i, OrderTop (J i)] [∀ i, SuccOrder (J i)]
variable (T : Object.{u})

/-- An iterated cellular construction before flattening. All stages are
literal submonoids of the same final monoid. -/
structure BlockTower where
  stage : ∀ i, J i → Subobject T
  inner_mono : ∀ i, Monotone (fun j => (stage i j).submonoid)
  outer_mono : Monotone (fun i => (stage i ⊥).submonoid)
  boundary : ∀ i, (stage i ⊤).submonoid = (stage (Order.succ i) ⊥).submonoid
  inner_limit : ∀ i j, Order.IsSuccLimit j → ∀ x, x ∈ (stage i j).submonoid →
    ∃ k < j, x ∈ (stage i k).submonoid
  outer_limit : ∀ i, Order.IsSuccLimit i → ∀ x, x ∈ (stage i ⊥).submonoid →
    ∃ k < i, x ∈ (stage k ⊥).submonoid
  covers : ∀ x : T, ∃ i, x ∈ (stage i ⊥).submonoid
  step : ∀ i j, j < ⊤ → Nonempty (Attachment (stage i j) (stage i (Order.succ j)))

namespace BlockTower
variable {T} (B : BlockTower (I := I) (J := J) T)

def flatStage : Index I J → Subobject T
  | none => Subobject.top
  | some z => B.stage z.1 z.2

omit [WellFoundedLT I] [OrderBot I] [NoMaxOrder I] [∀ i, WellFoundedLT (J i)] in
@[simp] theorem flatStage_cut (i : I) (j : J i) : B.flatStage (cut i j) = B.stage i j := rfl

/-- Flattening retains every original cell and does not change the terminal
monoid or any of the limit unions. -/
def flatten : CellTower T (Index I J) where
  stage := B.flatStage
  terminal := rfl
  mono := by
    intro a b hab
    cases b with
    | none => exact le_top
    | some b =>
      cases a with
      | none => exact (WithTop.not_top_le_coe _ hab).elim
      | some a =>
        rcases a with ⟨i,j⟩
        rcases b with ⟨k,l⟩
        have h := WithTop.coe_le_coe.mp hab
        cases h with
        | left _ _ hik =>
          change (B.stage i j).submonoid ≤ (B.stage k l).submonoid
          calc
            (B.stage i j).submonoid ≤ (B.stage i ⊤).submonoid := B.inner_mono i le_top
            _ = (B.stage (Order.succ i) ⊥).submonoid := B.boundary i
            _ ≤ (B.stage k ⊥).submonoid := B.outer_mono (Order.succ_le_of_lt hik)
            _ ≤ (B.stage k l).submonoid := B.inner_mono k bot_le
        | right _ _ hjl => exact B.inner_mono i hjl
  continuous := by
    intro a ha x hx
    cases a with
    | none =>
      obtain ⟨i,hi⟩ := B.covers x
      exact ⟨cut i ⊥,cut_lt_top _ _,hi⟩
    | some a =>
      rcases a with ⟨i,j⟩
      change Order.IsSuccLimit (cut i j) at ha
      by_cases hj : j = ⊥
      · subst j
        obtain ⟨k,hki,hkx⟩ := B.outer_limit i (BlockIndex.outer_limit ha) x hx
        exact ⟨cut k ⊥,cut_lt_of_lt hki _ _,hkx⟩
      · obtain ⟨k,hkj,hkx⟩ := B.inner_limit i j (BlockIndex.inner_limit ha hj) x hx
        exact ⟨cut i k,(cut_lt_cut i k j).mpr hkj,hkx⟩
  step := by
    intro a
    cases a with
    | none =>
      left
      change (B.flatStage (⊤ : Index I J)).submonoid =
        (B.flatStage (Order.succ (⊤ : Index I J))).submonoid
      rw [Order.succ_top]
    | some a =>
      rcases a with ⟨i,j⟩
      change (B.flatStage (cut i j)).submonoid =
        (B.flatStage (Order.succ (cut i j))).submonoid ∨
        Nonempty (Attachment (B.flatStage (cut i j)) (B.flatStage (Order.succ (cut i j))))
      by_cases hj : j = ⊤
      · subst j
        left
        rw [succ_boundary, flatStage_cut,flatStage_cut]
        exact B.boundary i
      · right
        rw [succ_inner i j (lt_top_iff_ne_top.mpr hj),flatStage_cut,flatStage_cut]
        exact B.step i j (lt_top_iff_ne_top.mpr hj)

@[simp] theorem flatten_bottom : (B.flatten.stage ⊥) = B.stage ⊥ ⊥ := rfl

end BlockTower
end
end PartitionConsistency.ConservativeMonoids


/-! ## RangeAttachment -/

namespace PartitionConsistency.ConservativeMonoids
universe u
open CategoryTheory DiagramOrder
noncomputable section

namespace Cell
variable {M N : Object.{u}} (d : Cell M)

theorem simulation_surjective (f : M ⟶ N) (hf : Function.Surjective f) :
    Function.Surjective (d.simulation f) := by
  apply (MonoidHom.mrange_eq_top (f := (d.simulation f).toMonoidHom)).mp
  apply (d.map f).generated
  · intro y
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨d.inclusion x,Cell.simulation_old d f x⟩
  · intro i
    have hi : (d.map f).generator i ∈ Set.range (d.map f).generator := ⟨i,rfl⟩
    rw [← d.simulation_generator_range f] at hi
    obtain ⟨j,hj⟩ := hi
    exact ⟨d.generator j,hj⟩

def simulationEquiv (f : M ⟶ N) (hf : Function.Surjective f) :
    d.extension ≃* (d.map f).extension :=
  MulEquiv.ofBijective (d.simulation f).toMonoidHom
    ⟨(d.simulation f).injective,d.simulation_surjective f hf⟩

@[simp] theorem simulationEquiv_old (f : M ⟶ N) (hf : Function.Surjective f) (x : M) :
    d.simulationEquiv f hf (d.inclusion x) = (d.map f).inclusion (f x) :=
  Cell.simulation_old d f x

/-- Identify an original executed cell with the literal ranges inside its
terminal monoid. Surjectivity here is proved from the presentation. -/
def rangeAttachment {T : Object.{u}} (f : M ⟶ T) (g : d.extension ⟶ T)
    (h : ∀ x, g (d.inclusion x) = f x) :
    Attachment (Subobject.range f) (Subobject.range g) := by
  let e := ofMulEquiv f.rangeEquiv
  let s := d.simulationEquiv e f.rangeEquiv.surjective
  refine ⟨d.map e,s.symm.trans g.rangeEquiv,?_⟩
  intro y
  obtain ⟨x,rfl⟩ := f.rangeEquiv.surjective y
  change g (s.symm ((d.map e).inclusion (e x))) = f x
  rw [← d.simulationEquiv_old e f.rangeEquiv.surjective x,s.symm_apply_apply]
  exact h x

end Cell

end
end PartitionConsistency.ConservativeMonoids


/-! ## SaturationBlock -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_SupportFilter
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency
namespace SupportFilter
universe u
variable {I : Type u}

/-- Ground pointwise stabilizer of a set of labels. -/
abbrev Fix (J : Set I) : Subgroup (Equiv.Perm I) := fixingSubgroup (Equiv.Perm I) J

@[simp] theorem mem_Fix (J : Set I) (π : Equiv.Perm I) :
    π ∈ Fix J ↔ ∀ j ∈ J, π j = j := mem_fixingSubgroup_iff (Equiv.Perm I)

/-- The actual small-support subgroup filter, rather than a condition asserting
that some symmetric interpretation already has the target properties. -/
def subgroupFilter (μ : Cardinal.{u}) : Set (Subgroup (Equiv.Perm I)) :=
  {K | ∃ J : Set I, Cardinal.mk J ≤ μ ∧ Fix J ≤ K}

theorem top_mem (μ : Cardinal.{u}) : (⊤ : Subgroup (Equiv.Perm I)) ∈ subgroupFilter μ :=
  ⟨∅, by simp, le_top⟩

theorem upward_closed {μ : Cardinal.{u}} {K L : Subgroup (Equiv.Perm I)}
    (hK : K ∈ subgroupFilter μ) (hKL : K ≤ L) : L ∈ subgroupFilter μ := by
  obtain ⟨J, hJ, hf⟩ := hK
  exact ⟨J, hJ, hf.trans hKL⟩

theorem inf_mem {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
    {K L : Subgroup (Equiv.Perm I)} (hK : K ∈ subgroupFilter μ)
    (hL : L ∈ subgroupFilter μ) : K ⊓ L ∈ subgroupFilter μ := by
  obtain ⟨J, hJ, hK⟩ := hK
  obtain ⟨J', hJ', hL⟩ := hL
  refine ⟨J ∪ J', ?_, ?_⟩
  · exact (Cardinal.mk_union_le J J').trans
      ((add_le_add hJ hJ').trans_eq (Cardinal.add_eq_self hμ))
  · simp only [Fix, fixingSubgroup_union]
    exact inf_le_inf hK hL

/-- Conjugating a pointwise stabilizer transports precisely its fixed labels. -/
theorem conjugate_fix (π : Equiv.Perm I) (J : Set I) :
    (Fix J).map (MulAut.conj π).toMonoidHom = Fix (π '' J) := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    have hτ' := (mem_Fix J τ).1 hτ
    apply (mem_Fix _ _).2
    rintro _ ⟨j, hj, rfl⟩
    change π (τ (π⁻¹ (π j))) = π j
    simp [hτ' j hj]
  · intro hσ
    rw [mem_Fix] at hσ
    refine Subgroup.mem_map.2 ⟨π⁻¹ * σ * π, ?_, ?_⟩
    · rw [mem_Fix]
      intro j hj
      change π⁻¹ (σ (π j)) = j
      rw [hσ _ ⟨j, hj, rfl⟩]
      simp
    · change π * (π⁻¹ * σ * π) * π⁻¹ = σ
      group

theorem conjugate_mem {μ : Cardinal.{u}} {K : Subgroup (Equiv.Perm I)}
    (hK : K ∈ subgroupFilter μ) (π : Equiv.Perm I) :
    K.map (MulAut.conj π).toMonoidHom ∈ subgroupFilter μ := by
  obtain ⟨J, hJ, hfix⟩ := hK
  refine ⟨π '' J, Cardinal.mk_image_le.trans hJ, ?_⟩
  rw [← conjugate_fix]
  exact Subgroup.map_mono hfix

/-- The normal-filter properties required by the set symmetric-system theorem. -/
def IsNormalFilter {G : Type*} [Group G] (F : Set (Subgroup G)) : Prop :=
  ⊤ ∈ F ∧
  (∀ K L, K ∈ F → K ≤ L → L ∈ F) ∧
  (∀ K L, K ∈ F → L ∈ F → K ⊓ L ∈ F) ∧
  (∀ g K, K ∈ F → K.map (MulAut.conj g).toMonoidHom ∈ F)

theorem isNormalFilter {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) :
    IsNormalFilter (subgroupFilter (I := I) μ) :=
  ⟨top_mem μ, fun _ _ => upward_closed, fun _ _ => inf_mem hμ,
    fun _ _ h => conjugate_mem h _⟩

/-- Small support translates to a small support, since permutations preserve
cardinality. This concerns literal actions, not automorphisms of an extension. -/
theorem transport_support {X : Type*} [MulAction (Equiv.Perm I) X]
    {J : Set I} {x : X} (h : ∀ π ∈ Fix J, π • x = x) (σ : Equiv.Perm I) :
    ∀ π ∈ Fix (σ '' J), π • (σ • x) = σ • x := by
  intro π hπ
  rw [← conjugate_fix] at hπ
  obtain ⟨τ, hτ, rfl⟩ := hπ
  change (σ * τ * σ⁻¹) • (σ • x) = σ • x
  simp [mul_smul, h τ hτ]

end SupportFilter
end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Logic_Completeness
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency
/-! Countable Henkin completeness for the target proof calculus. -/

deriving instance Countable for Formula

namespace Formula

@[simp] theorem liftRen_id (n : ℕ) : liftRen (id : Fin n → Fin n) = id := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftRen]

@[simp] theorem liftRen_comp {n m k : ℕ} (r : Fin n → Fin m) (s : Fin m → Fin k) :
    liftRen (s ∘ r) = liftRen s ∘ liftRen r := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftRen]

@[simp] theorem rename_id {n} (φ : Formula n) : φ.rename id = φ := by
  induction φ with
  | bot => rfl
  | mem => rfl
  | equal => rfl
  | imp φ ψ hφ hψ => simp [rename, hφ, hψ]
  | conj φ ψ hφ hψ => simp [rename, hφ, hψ]
  | disj φ ψ hφ hψ => simp [rename, hφ, hψ]
  | all φ hφ => simp [rename, hφ]
  | ex φ hφ => simp [rename, hφ]

@[simp] theorem rename_comp {n m k} (φ : Formula n)
    (r : Fin n → Fin m) (s : Fin m → Fin k) :
    (φ.rename r).rename s = φ.rename (s ∘ r) := by
  induction φ generalizing m k with
  | bot => rfl
  | mem => rfl
  | equal => rfl
  | imp φ ψ hφ hψ => simp [rename, hφ, hψ]
  | conj φ ψ hφ hψ => simp [rename, hφ, hψ]
  | disj φ ψ hφ hψ => simp [rename, hφ, hψ]
  | all φ hφ => simp [rename, hφ, liftRen_comp]
  | ex φ hφ => simp [rename, hφ, liftRen_comp]

/-- Instantiation after renaming the free variables extends that renaming by
one chosen variable; this is the capture-avoidance identity for witnesses. -/
@[simp] theorem instantiate_rename {n m} (φ : Formula (n + 1))
    (r : Fin n → Fin m) (t : Fin m) :
    (φ.rename (liftRen r)).instantiate t = φ.rename (Fin.snoc r t) := by
  rw [instantiate, rename_comp]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftRen]

@[simp] theorem rename_snoc_castSucc_last {n} (φ : Formula (n + 1)) :
    φ.rename (Fin.snoc Fin.castSucc (Fin.last n)) = φ := by
  have h : Fin.snoc Fin.castSucc (Fin.last n) = (id : Fin (n+1) → Fin (n+1)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [h, rename_id]

@[simp] theorem rename_instantiate {n m} (φ : Formula (n+1))
    (r : Fin n → Fin m) (t : Fin n) :
    (φ.instantiate t).rename r = (φ.rename (liftRen r)).instantiate (r t) := by
  rw [instantiate_rename, instantiate, rename_comp]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

end Formula

namespace Completeness

/-- Extending the variable map by a new last variable is the binder lift. -/
@[simp] theorem snoc_castSucc {n m} (w : Fin n → Fin m) :
    Fin.snoc (Fin.castSucc ∘ w) (Fin.last m) = Formula.liftRen w := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Formula.liftRen]

end Completeness
end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_ForcingNames
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency.SetForcingNames
universe u v

/-- The subname relation on literal set codes. The second component of an edge
is a forcing condition; the first component is a name for a potential member. -/
def Child (τ σ : ZFSet.{u}) : Prop := ∃ p, ZFSet.pair τ p ∈ σ

theorem child_wf : WellFounded Child.{u} := by
  apply (ZFSet.mem_wf.transGen).mono
  rintro τ σ ⟨p, hp⟩
  have h₁ : Relation.TransGen (fun x y : ZFSet.{u} => x ∈ y) τ {τ} :=
    .single (by simp)
  have h₂ : Relation.TransGen (fun x y : ZFSet.{u} => x ∈ y) τ (ZFSet.pair τ p) :=
    h₁.tail (by simp [ZFSet.pair])
  exact h₂.tail hp

/-- Edges of a set name, with no choice of a presentation of that set. -/
def Edges (σ : ZFSet.{u}) := {e : ZFSet.{u} × ZFSet.{u} // ZFSet.pair e.1 e.2 ∈ σ}

instance instSmallEdges (σ : ZFSet.{u}) : Small.{u} (Edges σ) := by
  apply small_of_injective (f := fun e : Edges σ =>
    (⟨ZFSet.pair e.val.1 e.val.2, e.property⟩ : σ))
  intro a b hab
  apply Subtype.ext
  exact Prod.ext ((ZFSet.pair_inj.mp (Subtype.ext_iff.mp hab)).1)
    ((ZFSet.pair_inj.mp (Subtype.ext_iff.mp hab)).2)

/-- Well-formed set-forcing names. This is the usual hereditary recursive
condition on sets of pairs, not a predicate on their interpreted values. -/
def IsName (P : Set ZFSet.{u}) : ZFSet.{u} → Prop :=
  child_wf.fix fun σ rec =>
    (∀ z ∈ σ, ∃ τ p, z = ZFSet.pair τ p) ∧
    ∀ τ p (he : ZFSet.pair τ p ∈ σ), p ∈ P ∧ rec τ ⟨p, he⟩

theorem isName_iff {P : Set ZFSet.{u}} {σ : ZFSet.{u}} : IsName P σ ↔
    (∀ z ∈ σ, ∃ τ p, z = ZFSet.pair τ p) ∧
    ∀ τ p, ZFSet.pair τ p ∈ σ → p ∈ P ∧ IsName P τ := by
  unfold IsName
  rw [WellFounded.fix_eq]

theorem IsName.intro {P : Set ZFSet.{u}} (σ : ZFSet.{u})
    (h : ∀ z ∈ σ, ∃ τ p, z = ZFSet.pair τ p ∧ p ∈ P ∧ IsName P τ) : IsName P σ := by
  apply isName_iff.mpr
  refine ⟨fun z hz => ?_, fun τ p he => ?_⟩
  · obtain ⟨τ, p, hpair, _, _⟩ := h z hz
    exact ⟨τ, p, hpair⟩
  · obtain ⟨τ', p', hpair, hp', hn⟩ := h _ he
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp hpair
    exact ⟨hp', hn⟩

theorem IsName.edges {P : Set ZFSet.{u}} {σ : ZFSet.{u}} (h : IsName P σ) :
    ∀ z ∈ σ, ∃ τ p, z = ZFSet.pair τ p ∧ p ∈ P ∧ IsName P τ := by
  intro z hz
  obtain ⟨τ, p, rfl⟩ := (isName_iff.mp h).1 z hz
  exact ⟨τ, p, rfl, (isName_iff.mp h).2 τ p hz⟩

theorem IsName.child {P : Set ZFSet.{u}} {σ τ p : ZFSet.{u}}
    (h : IsName P σ) (he : ZFSet.pair τ p ∈ σ) : IsName P τ :=
  ((isName_iff.mp h).2 τ p he).2

theorem IsName.condition {P : Set ZFSet.{u}} {σ τ p : ZFSet.{u}}
    (h : IsName P σ) (he : ZFSet.pair τ p ∈ σ) : p ∈ P :=
  ((isName_iff.mp h).2 τ p he).1

theorem isName_empty (P : Set ZFSet.{u}) : IsName P ∅ :=
  .intro _ (by simp)

/-- Recursive transport of names by a map on condition codes. -/
noncomputable def mapConditions (f : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} → ZFSet.{u} :=
  child_wf.fix fun σ rec => ZFSet.range fun e : Edges σ =>
    ZFSet.pair (rec e.val.1 ⟨e.val.2, e.property⟩) (f e.val.2)

theorem mapConditions_eq (f : ZFSet.{u} → ZFSet.{u}) (σ : ZFSet.{u}) :
    mapConditions f σ = ZFSet.range (fun e : Edges σ =>
      ZFSet.pair (mapConditions f e.val.1) (f e.val.2)) := by
  unfold mapConditions
  rw [WellFounded.fix_eq]

theorem mem_mapConditions_iff {f : ZFSet.{u} → ZFSet.{u}} {σ z : ZFSet.{u}} :
    z ∈ mapConditions f σ ↔ ∃ τ p, ZFSet.pair τ p ∈ σ ∧
      ZFSet.pair (mapConditions f τ) (f p) = z := by
  rw [mapConditions_eq, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨τ, p⟩, he⟩, hz⟩
    exact ⟨τ, p, he, hz⟩
  · rintro ⟨τ, p, he, hz⟩
    exact ⟨⟨(τ, p), he⟩, hz⟩

theorem edge_mapConditions_iff {f : ZFSet.{u} → ZFSet.{u}} {σ τ p : ZFSet.{u}} :
    ZFSet.pair τ p ∈ mapConditions f σ ↔ ∃ τ' p',
      ZFSet.pair τ' p' ∈ σ ∧ mapConditions f τ' = τ ∧ f p' = p := by
  simp only [mem_mapConditions_iff, ZFSet.pair_inj]

@[simp] theorem mapConditions_empty (f : ZFSet.{u} → ZFSet.{u}) :
    mapConditions f ∅ = ∅ := by
  apply ZFSet.ext
  simp [mem_mapConditions_iff]

theorem mapConditions_id {P : Set ZFSet.{u}} {σ : ZFSet.{u}} (h : IsName P σ) :
    mapConditions id σ = σ := by
  induction σ using child_wf.induction with | h σ ih =>
  apply ZFSet.ext
  intro z
  rw [mem_mapConditions_iff]
  constructor
  · rintro ⟨τ, p, he, rfl⟩
    simpa only [ih τ ⟨p, he⟩ (h.child he), id_eq] using he
  · intro hz
    obtain ⟨τ, p, rfl, _, _⟩ := h.edges z hz
    exact ⟨τ, p, hz, by rw [ih τ ⟨p, hz⟩ (h.child hz)]; rfl⟩

theorem mapConditions_comp (f g : ZFSet.{u} → ZFSet.{u}) (σ : ZFSet.{u}) :
    mapConditions f (mapConditions g σ) = mapConditions (f ∘ g) σ := by
  induction σ using child_wf.induction with | h σ ih =>
  apply ZFSet.ext
  intro z
  rw [mem_mapConditions_iff, mem_mapConditions_iff]
  constructor
  · rintro ⟨τ, p, he, hz⟩
    obtain ⟨τ', p', he', rfl, rfl⟩ := edge_mapConditions_iff.mp he
    refine ⟨τ', p', he', ?_⟩
    simpa only [ih τ' ⟨p', he'⟩, Function.comp_apply] using hz
  · rintro ⟨τ, p, he, hz⟩
    refine ⟨mapConditions g τ, g p, edge_mapConditions_iff.mpr ⟨τ, p, he, rfl, rfl⟩, ?_⟩
    simpa only [ih τ ⟨p, he⟩, Function.comp_apply] using hz

theorem IsName.mapConditions {P Q : Set ZFSet.{u}} {f : ZFSet.{u} → ZFSet.{u}}
    (hf : ∀ p ∈ P, f p ∈ Q) {σ : ZFSet.{u}} (h : IsName P σ) :
    IsName Q (mapConditions f σ) := by
  induction σ using child_wf.induction with | h σ ih =>
  apply IsName.intro
  intro z hz
  obtain ⟨τ, p, he, rfl⟩ := mem_mapConditions_iff.mp hz
  exact ⟨_, _, rfl, hf p (h.condition he), ih τ ⟨p, he⟩ (h.child he)⟩


/-- The canonical name for a ground set, using the condition `t`. In applications
`t` is the largest condition. -/
noncomputable def checkName (t : ZFSet.{u}) : ZFSet.{u} → ZFSet.{u} :=
  ZFSet.mem_wf.fix fun x rec => ZFSet.range fun y : x => ZFSet.pair (rec y.val y.property) t

theorem checkName_eq (t x : ZFSet.{u}) :
    checkName t x = ZFSet.range (fun y : x => ZFSet.pair (checkName t y.val) t) := by
  unfold checkName
  rw [WellFounded.fix_eq]

theorem mem_checkName_iff {t x z : ZFSet.{u}} :
    z ∈ checkName t x ↔ ∃ y ∈ x, ZFSet.pair (checkName t y) t = z := by
  rw [checkName_eq, ZFSet.mem_range]
  exact ⟨fun ⟨y, hy⟩ => ⟨y.val, y.property, hy⟩, fun ⟨y, hy, hz⟩ => ⟨⟨y, hy⟩, hz⟩⟩

theorem edge_checkName_iff {t x τ p : ZFSet.{u}} :
    ZFSet.pair τ p ∈ checkName t x ↔ ∃ y ∈ x, checkName t y = τ ∧ t = p := by
  simp only [mem_checkName_iff, ZFSet.pair_inj]

theorem checkName_isName {P : Set ZFSet.{u}} {t : ZFSet.{u}} (ht : t ∈ P) (x : ZFSet.{u}) :
    IsName P (checkName t x) := by
  induction x using ZFSet.inductionOn with | h x ih =>
  apply IsName.intro
  intro z hz
  obtain ⟨y, hy, rfl⟩ := mem_checkName_iff.mp hz
  exact ⟨_, _, rfl, ht, ih y hy⟩

theorem mapConditions_checkName (f : ZFSet.{u} → ZFSet.{u}) (t x : ZFSet.{u}) :
    mapConditions f (checkName t x) = checkName (f t) x := by
  induction x using ZFSet.inductionOn with | h x ih =>
  apply ZFSet.ext
  intro z
  rw [mem_mapConditions_iff, mem_checkName_iff]
  constructor
  · rintro ⟨τ, p, he, hz⟩
    obtain ⟨y, hy, rfl, rfl⟩ := edge_checkName_iff.mp he
    exact ⟨y, hy, by simpa only [ih y hy] using hz⟩
  · rintro ⟨y, hy, hz⟩
    exact ⟨checkName t y, t, edge_checkName_iff.mpr ⟨y, hy, rfl, rfl⟩,
      by simpa only [ih y hy] using hz⟩

/-- A literal pairing name. -/
def pairName (t σ τ : ZFSet.{u}) : ZFSet.{u} := {ZFSet.pair σ t, ZFSet.pair τ t}

theorem pairName_isName {P : Set ZFSet.{u}} {t σ τ : ZFSet.{u}}
    (ht : t ∈ P) (hσ : IsName P σ) (hτ : IsName P τ) : IsName P (pairName t σ τ) := by
  apply IsName.intro
  intro z hz
  rcases ZFSet.mem_pair.mp hz with rfl | rfl
  · exact ⟨σ, t, rfl, ht, hσ⟩
  · exact ⟨τ, t, rfl, ht, hτ⟩

theorem edge_pairName_iff {t σ τ ν p : ZFSet.{u}} :
    ZFSet.pair ν p ∈ pairName t σ τ ↔ (ν = σ ∨ ν = τ) ∧ p = t := by
  simp only [pairName, ZFSet.mem_pair, ZFSet.pair_inj, or_and_right]

theorem mapConditions_pairName (f : ZFSet.{u} → ZFSet.{u}) (t σ τ : ZFSet.{u}) :
    mapConditions f (pairName t σ τ) = pairName (f t) (mapConditions f σ) (mapConditions f τ) := by
  apply ZFSet.ext
  intro z
  simp only [mem_mapConditions_iff, edge_pairName_iff]
  rw [pairName, ZFSet.mem_pair]
  constructor
  · rintro ⟨ν, p, ⟨(rfl | rfl), rfl⟩, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨σ, t, ⟨Or.inl rfl, rfl⟩, rfl⟩
    · exact ⟨τ, t, ⟨Or.inr rfl, rfl⟩, rfl⟩

/-- A small type indexing the three conditions used by the union-name
construction: the two existing edge conditions and their common strengthening. -/
def UnionEdges (P : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop) (σ : ZFSet.{u}) :=
  {e : (Σ a : Edges σ, Edges a.val.1 × P) //
    R e.2.2.val e.1.val.2 ∧ R e.2.2.val e.2.1.val.2}

instance instSmallUnionEdges (P : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop) (σ : ZFSet.{u}) :
    Small.{u} (UnionEdges P R σ) := by
  unfold UnionEdges
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The union name for an arbitrary set forcing, not necessarily one with binary
meets. Every common strengthening is included. -/
noncomputable def unionName (P : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (σ : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun e : UnionEdges P R σ => ZFSet.pair e.val.2.1.val.1 e.val.2.2.val)

theorem mem_unionName_iff {P : ZFSet.{u}} {R : ZFSet.{u} → ZFSet.{u} → Prop}
    {σ z : ZFSet.{u}} : z ∈ unionName P R σ ↔ ∃ χ p τ r q,
      ZFSet.pair χ p ∈ σ ∧ ZFSet.pair τ r ∈ χ ∧ q ∈ P ∧
      R q p ∧ R q r ∧ ZFSet.pair τ q = z := by
  rw [unionName, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨⟨⟨χ, p⟩, hp⟩, ⟨⟨⟨τ, r⟩, hr⟩, ⟨q, hq⟩⟩⟩, hqp, hqr⟩, hz⟩
    exact ⟨χ, p, τ, r, q, hp, hr, hq, hqp, hqr, hz⟩
  · rintro ⟨χ, p, τ, r, q, hp, hr, hq, hqp, hqr, hz⟩
    exact ⟨⟨⟨⟨(χ, p), hp⟩, ⟨⟨(τ, r), hr⟩, ⟨q, hq⟩⟩⟩, hqp, hqr⟩, hz⟩

theorem edge_unionName_iff {P : ZFSet.{u}} {R : ZFSet.{u} → ZFSet.{u} → Prop}
    {σ τ q : ZFSet.{u}} : ZFSet.pair τ q ∈ unionName P R σ ↔
      ∃ χ p r, ZFSet.pair χ p ∈ σ ∧ ZFSet.pair τ r ∈ χ ∧ q ∈ P ∧ R q p ∧ R q r := by
  simp only [mem_unionName_iff, ZFSet.pair_inj]
  constructor
  · rintro ⟨χ, p, τ', r, q', hp, hr, hq, hqp, hqr, rfl, rfl⟩
    exact ⟨χ, p, r, hp, hr, hq, hqp, hqr⟩
  · rintro ⟨χ, p, r, hp, hr, hq, hqp, hqr⟩
    exact ⟨χ, p, τ, r, q, hp, hr, hq, hqp, hqr, rfl, rfl⟩

theorem unionName_isName {P : ZFSet.{u}} (R : ZFSet.{u} → ZFSet.{u} → Prop)
    {σ : ZFSet.{u}} (hσ : IsName P σ) : IsName P (unionName P R σ) := by
  apply IsName.intro
  intro z hz
  obtain ⟨χ, p, τ, r, q, hp, hr, hq, _, _, rfl⟩ := mem_unionName_iff.mp hz
  exact ⟨τ, q, rfl, hq, (hσ.child hp).child hr⟩


/-- The condition part of a symmetric system. A homomorphism into permutations
of the actual set of conditions is enough to lift the action to set names.
Preservation of the forcing order is used separately for the union constructor. -/
structure ConditionAction (Γ : Type v) [Group Γ] where
  conditions : ZFSet.{u}
  perm : Γ →* Equiv.Perm conditions

namespace ConditionAction
variable {Γ : Type v} [Group Γ] (S : ConditionAction.{u} Γ)

/-- Extend a permutation of the conditions by the identity on all other codes. -/
noncomputable def actCode (g : Γ) (p : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if h : p ∈ S.conditions then (S.perm g ⟨p, h⟩).val else p

@[simp] theorem actCode_of_mem (g : Γ) {p : ZFSet.{u}} (hp : p ∈ S.conditions) :
    S.actCode g p = (S.perm g ⟨p, hp⟩).val := by
  classical
  simp only [actCode, dite_eq_left hp]

@[simp] theorem actCode_of_not_mem (g : Γ) {p : ZFSet.{u}} (hp : p ∉ S.conditions) :
    S.actCode g p = p := by
  classical
  simp only [actCode, dite_eq_right hp]

theorem actCode_mem (g : Γ) {p : ZFSet.{u}} (hp : p ∈ S.conditions) :
    S.actCode g p ∈ S.conditions := by
  rw [S.actCode_of_mem g hp]
  exact (S.perm g ⟨p, hp⟩).property

@[simp] theorem actCode_one (p : ZFSet.{u}) : S.actCode 1 p = p := by
  classical
  by_cases hp : p ∈ S.conditions
  · simp [actCode, hp]
  · exact S.actCode_of_not_mem 1 hp

@[simp] theorem actCode_mul (g h : Γ) (p : ZFSet.{u}) :
    S.actCode (g * h) p = S.actCode g (S.actCode h p) := by
  classical
  by_cases hp : p ∈ S.conditions
  · rw [S.actCode_of_mem (g * h) hp, S.actCode_of_mem g (S.actCode_mem h hp)]
    simp only [S.actCode_of_mem h hp, map_mul, Equiv.Perm.coe_mul, Function.comp_apply]
  · rw [S.actCode_of_not_mem _ hp, S.actCode_of_not_mem _ hp, S.actCode_of_not_mem _ hp]

@[simp] theorem actCode_inv_actCode (g : Γ) (p : ZFSet.{u}) :
    S.actCode g⁻¹ (S.actCode g p) = p := by
  rw [← S.actCode_mul, inv_mul_cancel, S.actCode_one]

@[simp] theorem actCode_actCode_inv (g : Γ) (p : ZFSet.{u}) :
    S.actCode g (S.actCode g⁻¹ p) = p := by
  rw [← S.actCode_mul, mul_inv_cancel, S.actCode_one]

theorem actCode_injective (g : Γ) : Function.Injective (S.actCode g) :=
  Function.LeftInverse.injective (S.actCode_inv_actCode g)

/-- Literal names for this condition set. Equality is equality of the underlying
ZF sets, not equality of tree presentations. -/
structure Name where
  val : ZFSet.{u}
  property : IsName S.conditions val

namespace Name
variable {S}

@[ext] theorem ext {σ τ : S.Name} (h : σ.val = τ.val) : σ = τ := by
  cases σ
  cases τ
  cases h
  rfl

noncomputable def act (g : Γ) (σ : S.Name) : S.Name :=
  ⟨mapConditions (S.actCode g) σ.val,
    σ.property.mapConditions (fun _ => S.actCode_mem g)⟩

noncomputable instance instMulAction : MulAction Γ S.Name where
  smul := act
  one_smul σ := by
    apply ext
    change mapConditions (S.actCode 1) σ.val = σ.val
    have he : S.actCode 1 = id := funext S.actCode_one
    rw [he]
    exact mapConditions_id σ.property
  mul_smul g h σ := by
    apply ext
    change mapConditions (S.actCode (g * h)) σ.val =
      mapConditions (S.actCode g) (mapConditions (S.actCode h) σ.val)
    rw [mapConditions_comp]
    congr 1
    exact funext (S.actCode_mul g h)

@[simp] theorem smul_val (g : Γ) (σ : S.Name) :
    (g • σ).val = mapConditions (S.actCode g) σ.val := rfl

/-- An edge recovers a name, with hereditary well-formedness proved from its
parent rather than imposed as an additional hypothesis. -/
def child (σ : S.Name) {τ p : ZFSet.{u}} (he : ZFSet.pair τ p ∈ σ.val) : S.Name :=
  ⟨τ, σ.property.child he⟩

@[simp] theorem child_val (σ : S.Name) {τ p : ZFSet.{u}} (he : ZFSet.pair τ p ∈ σ.val) :
    (σ.child he).val = τ := rfl

theorem child_wellFounded : WellFounded (fun τ σ : S.Name => Child τ.val σ.val) :=
  child_wf.onFun

/-- Canonical names in the actual condition system. -/
noncomputable def check {t : ZFSet.{u}} (ht : t ∈ S.conditions) (x : ZFSet.{u}) : S.Name :=
  ⟨checkName t x, checkName_isName ht x⟩

/-- Pairing of names in the actual condition system. -/
def pair {t : ZFSet.{u}} (ht : t ∈ S.conditions) (σ τ : S.Name) : S.Name :=
  ⟨pairName t σ.val τ.val, pairName_isName ht σ.property τ.property⟩

/-- Union of names for the chosen forcing order. -/
noncomputable def union (R : ZFSet.{u} → ZFSet.{u} → Prop) (σ : S.Name) : S.Name :=
  ⟨unionName S.conditions R σ.val, unionName_isName R σ.property⟩

@[simp] theorem smul_check {t : ZFSet.{u}} (ht : t ∈ S.conditions) (g : Γ)
    (hx : S.actCode g t = t) (x : ZFSet.{u}) :
    g • check ht x = check ht x := by
  apply ext
  change mapConditions (S.actCode g) (checkName t x) = checkName t x
  rw [mapConditions_checkName, hx]

@[simp] theorem smul_pair {t : ZFSet.{u}} (ht : t ∈ S.conditions) (g : Γ)
    (hx : S.actCode g t = t) (σ τ : S.Name) :
    g • pair ht σ τ = pair ht (g • σ) (g • τ) := by
  apply ext
  change mapConditions (S.actCode g) (pairName t σ.val τ.val) =
    pairName t (mapConditions (S.actCode g) σ.val) (mapConditions (S.actCode g) τ.val)
  rw [mapConditions_pairName, hx]

end Name
end ConditionAction


namespace ConditionAction
variable {Γ : Type v} [Group Γ] (S : ConditionAction.{u} Γ)

/-- If condition permutations preserve the order, they commute exactly with
the set-valued union-name constructor. -/
theorem mapConditions_unionName (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (hR : ∀ g p q, R (S.actCode g p) (S.actCode g q) ↔ R p q)
    (g : Γ) (σ : ZFSet.{u}) :
    mapConditions (S.actCode g) (unionName S.conditions R σ) =
      unionName S.conditions R (mapConditions (S.actCode g) σ) := by
  apply ZFSet.ext
  intro z
  rw [mem_mapConditions_iff, mem_unionName_iff]
  constructor
  · rintro ⟨τ, q, he, hz⟩
    obtain ⟨χ, p, r, hp, hr, hq, hqp, hqr⟩ := edge_unionName_iff.mp he
    exact ⟨mapConditions (S.actCode g) χ, S.actCode g p,
      mapConditions (S.actCode g) τ, S.actCode g r, S.actCode g q,
      edge_mapConditions_iff.mpr ⟨χ, p, hp, rfl, rfl⟩,
      edge_mapConditions_iff.mpr ⟨τ, r, hr, rfl, rfl⟩,
      S.actCode_mem g hq, (hR g q p).mpr hqp, (hR g q r).mpr hqr, hz⟩
  · rintro ⟨χ, p, τ, r, q, hp, hr, hq, hqp, hqr, hz⟩
    obtain ⟨χ', p', hp', rfl, rfl⟩ := edge_mapConditions_iff.mp hp
    obtain ⟨τ', r', hr', rfl, rfl⟩ := edge_mapConditions_iff.mp hr
    have hqp' : R (S.actCode g⁻¹ q) p' := by
      apply (hR g _ _).mp
      simpa only [S.actCode_actCode_inv] using hqp
    have hqr' : R (S.actCode g⁻¹ q) r' := by
      apply (hR g _ _).mp
      simpa only [S.actCode_actCode_inv] using hqr
    refine ⟨τ', S.actCode g⁻¹ q, ?_, ?_⟩
    · exact edge_unionName_iff.mpr ⟨χ', p', r', hp', hr', S.actCode_mem _ hq, hqp', hqr'⟩
    · simpa only [S.actCode_actCode_inv] using hz

namespace Name
variable {S}

@[simp] theorem smul_union (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (hR : ∀ g p q, R (S.actCode g p) (S.actCode g q) ↔ R p q) (g : Γ) (σ : S.Name) :
    g • union R σ = union R (g • σ) := by
  apply ext
  exact S.mapConditions_unionName R hR g σ.val

/-- A name is symmetric when its literal set-name stabilizer belongs to the
specified subgroup filter. This does not mention its interpretation. -/
def Symmetric (F : Set (Subgroup Γ)) (σ : S.Name) : Prop :=
  MulAction.stabilizer Γ σ ∈ F

/-- Hereditary symmetry follows the subname relation, not membership of the
interpreted sets. -/
def HS (F : Set (Subgroup Γ)) : S.Name → Prop :=
  child_wellFounded.fix fun σ rec => Symmetric F σ ∧
    ∀ τ (he : Child τ.val σ.val), rec τ he

theorem hs_iff {F : Set (Subgroup Γ)} {σ : S.Name} : HS F σ ↔
    Symmetric F σ ∧ ∀ τ : S.Name, Child τ.val σ.val → HS F τ := by
  unfold HS
  rw [WellFounded.fix_eq]

theorem HS.symmetric {F : Set (Subgroup Γ)} {σ : S.Name} (h : HS F σ) :
    Symmetric F σ := (hs_iff.mp h).1

theorem HS.subname {F : Set (Subgroup Γ)} {σ τ : S.Name} (h : HS F σ)
    (he : Child τ.val σ.val) : HS F τ := (hs_iff.mp h).2 τ he

theorem HS.child {F : Set (Subgroup Γ)} {σ : S.Name} (h : HS F σ)
    {τ p : ZFSet.{u}} (he : ZFSet.pair τ p ∈ σ.val) : HS F (σ.child he) :=
  h.subname ⟨p, he⟩

/-- Normality of the subgroup filter is exactly what is needed to transport
hereditarily symmetric names. -/
theorem HS.smul {F : Set (Subgroup Γ)} (hF : SupportFilter.IsNormalFilter F) (g : Γ)
    {σ : S.Name} (hσ : HS F σ) : HS F (g • σ) := by
  induction σ using child_wellFounded.induction with | h σ ih =>
  apply hs_iff.mpr
  constructor
  · change MulAction.stabilizer Γ (g • σ) ∈ F
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    exact hF.2.2.2 g _ hσ.symmetric
  · rintro τ ⟨p, hp⟩
    obtain ⟨τ', p', he, hτ', _⟩ := edge_mapConditions_iff.mp hp
    let ν : S.Name := σ.child he
    have hν : Child ν.val σ.val := ⟨p', he⟩
    have heq : g • ν = τ := ext hτ'
    rw [← heq]
    exact ih ν hν (hσ.subname hν)

def empty : S.Name := ⟨∅, isName_empty _⟩

@[simp] theorem smul_empty (g : Γ) : g • (empty : S.Name) = empty := by
  apply ext
  exact mapConditions_empty _

theorem empty_HS {F : Set (Subgroup Γ)} (htop : (⊤ : Subgroup Γ) ∈ F) :
    HS F (empty : S.Name) := by
  apply hs_iff.mpr
  constructor
  · have hs : MulAction.stabilizer Γ (empty : S.Name) = ⊤ := by
      apply top_unique
      intro g _
      exact smul_empty g
    simpa only [Symmetric, hs] using htop
  · rintro τ ⟨p, hp⟩
    exact False.elim (ZFSet.notMem_empty _ hp)

theorem check_HS {F : Set (Subgroup Γ)} (htop : (⊤ : Subgroup Γ) ∈ F)
    {t : ZFSet.{u}} (ht : t ∈ S.conditions) (hfixed : ∀ g : Γ, S.actCode g t = t)
    (x : ZFSet.{u}) : HS F (check ht x) := by
  induction x using ZFSet.inductionOn with | h x ih =>
  apply hs_iff.mpr
  constructor
  · have hs : MulAction.stabilizer Γ (check ht x) = ⊤ := by
      apply top_unique
      intro g _
      exact smul_check ht g (hfixed g) x
    simpa only [Symmetric, hs] using htop
  · rintro τ ⟨p, hp⟩
    obtain ⟨y, hy, hτ, _⟩ := edge_checkName_iff.mp hp
    have heq : check ht y = τ := ext hτ
    rw [← heq]
    exact ih y hy

theorem pair_HS {F : Set (Subgroup Γ)} (hF : SupportFilter.IsNormalFilter F)
    {t : ZFSet.{u}} (ht : t ∈ S.conditions) (hfixed : ∀ g : Γ, S.actCode g t = t)
    {σ τ : S.Name} (hσ : HS F σ) (hτ : HS F τ) : HS F (pair ht σ τ) := by
  apply hs_iff.mpr
  constructor
  · apply hF.2.1 (MulAction.stabilizer Γ σ ⊓ MulAction.stabilizer Γ τ)
      _ (hF.2.2.1 _ _ hσ.symmetric hτ.symmetric)
    intro g hg
    change g • pair ht σ τ = pair ht σ τ
    rw [smul_pair ht g (hfixed g), hg.1, hg.2]
  · rintro ν ⟨p, hp⟩
    obtain ⟨heq | heq, _⟩ := edge_pairName_iff.mp hp
    · exact (ext heq).symm ▸ hσ
    · exact (ext heq).symm ▸ hτ

end Name
end ConditionAction

end PartitionConsistency.SetForcingNames

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_AtomicForcing
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency.SetForcingNames
universe u v

/-- An edge of a literal name decreases the rank of its name component. -/
theorem Child.rank_lt {τ σ : ZFSet.{u}} (h : Child τ σ) : τ.rank < σ.rank := by
  obtain ⟨p, hp⟩ := h
  exact (ZFSet.rank_lt_of_mem (by simp : τ ∈ ({τ} : ZFSet))).trans
    ((ZFSet.rank_lt_of_mem (by simp [ZFSet.pair] : ({τ} : ZFSet) ∈ ZFSet.pair τ p)).trans
      (ZFSet.rank_lt_of_mem hp))

namespace AtomicForcing

/-- The rank multiset, rather than a lexicographic ordering, permits the swaps
in the recursive clauses of atomic forcing. -/
noncomputable def pairRanks (σ τ : ZFSet.{u}) : Multiset Ordinal.{u} := {σ.rank} + {τ.rank}

def PairLower (st uv : ZFSet.{u} × ZFSet.{u}) : Prop :=
  Multiset.IsDershowitzMannaLT (pairRanks st.1 st.2) (pairRanks uv.1 uv.2)

theorem pairLower_wf : WellFounded PairLower.{u} :=
  InvImage.wf (fun st : ZFSet.{u} × ZFSet.{u} => pairRanks st.1 st.2) Multiset.wellFounded_isDershowitzMannaLT

theorem rank_replace (R : Multiset Ordinal.{u}) {τ σ : ZFSet.{u}} (h : Child τ σ) :
    Multiset.IsDershowitzMannaLT (R + {τ.rank}) (R + {σ.rank}) := by
  refine ⟨R, {τ.rank}, {σ.rank}, by simp, rfl, rfl, ?_⟩
  simpa using h.rank_lt

theorem pairLower_right {σ τ ν : ZFSet.{u}} (h : Child ν τ) :
    PairLower (σ, ν) (σ, τ) := rank_replace _ h

theorem pairLower_left {σ τ ν : ZFSet.{u}} (h : Child ν σ) :
    PairLower (ν, τ) (σ, τ) := by
  simpa [PairLower, pairRanks, add_comm] using rank_replace {τ.rank} h

theorem pairLower_swap {σ τ ν : ZFSet.{u}} (h : Child ν τ) :
    PairLower (ν, σ) (σ, τ) := by
  simpa [PairLower, pairRanks, add_comm] using rank_replace {σ.rank} h

variable {P : Type v} [Preorder P] (code : P → ZFSet.{u})

/-- Ordinary atomic set forcing, on actual sets of Kuratowski pairs. The first
component is membership and the second is equality. No truth values or atomic
laws are supplied as parameters. -/
noncomputable def relations : ZFSet.{u} × ZFSet.{u} → (P → Prop) × (P → Prop) :=
  pairLower_wf.fix fun st rec =>
  ( (fun p => ∀ q, q ≤ p → ∃ s, s ≤ q ∧ ∃ (ν : ZFSet.{u}) (r : P),
      ∃ he : ZFSet.pair ν (code r) ∈ st.2,
        s ≤ r ∧ (rec (st.1, ν) (pairLower_right ⟨(code r), he⟩)).2 s),
    (fun p =>
      (∀ ν (r : P) (he : ZFSet.pair ν (code r) ∈ st.1), ∀ q, q ≤ p → q ≤ r →
        (rec (ν, st.2) (pairLower_left ⟨(code r), he⟩)).1 q) ∧
      (∀ ν (r : P) (he : ZFSet.pair ν (code r) ∈ st.2), ∀ q, q ≤ p → q ≤ r →
        (rec (ν, st.1) (pairLower_swap ⟨(code r), he⟩)).1 q)) )

noncomputable def MemAt (p : P) (σ τ : ZFSet.{u}) : Prop := (relations code (σ, τ)).1 p
noncomputable def EqAt (p : P) (σ τ : ZFSet.{u}) : Prop := (relations code (σ, τ)).2 p

variable {code}

theorem mem_iff {p : P} {σ τ : ZFSet.{u}} : MemAt code p σ τ ↔
    ∀ q, q ≤ p → ∃ s, s ≤ q ∧ ∃ (ν : ZFSet.{u}) (r : P),
      ZFSet.pair ν (code r) ∈ τ ∧ s ≤ r ∧ EqAt code s σ ν := by
  unfold MemAt relations
  rw [WellFounded.fix_eq]
  change (∀ q, q ≤ p → ∃ s, s ≤ q ∧ ∃ (ν : ZFSet.{u}) (r : P),
    ∃ _he : ZFSet.pair ν (code r) ∈ τ, s ≤ r ∧ EqAt code s σ ν) ↔ _
  simp only [exists_prop]

theorem eq_iff {p : P} {σ τ : ZFSet.{u}} : EqAt code p σ τ ↔
    (∀ ν (r : P), ZFSet.pair ν (code r) ∈ σ → ∀ q, q ≤ p → q ≤ r → MemAt code q ν τ) ∧
    (∀ ν (r : P), ZFSet.pair ν (code r) ∈ τ → ∀ q, q ≤ p → q ≤ r → MemAt code q ν σ) := by
  unfold EqAt relations
  rw [WellFounded.fix_eq]
  rfl

theorem mem_mono {p q : P} {σ τ : ZFSet.{u}} (hqp : q ≤ p)
    (h : MemAt code p σ τ) : MemAt code q σ τ := by
  exact mem_iff.mpr fun r hr => mem_iff.mp h r (hr.trans hqp)

theorem eq_mono {p q : P} {σ τ : ZFSet.{u}} (hqp : q ≤ p)
    (h : EqAt code p σ τ) : EqAt code q σ τ := by
  obtain ⟨h₁, h₂⟩ := eq_iff.mp h
  exact eq_iff.mpr ⟨fun ν r he s hs hsr => h₁ ν r he s (hs.trans hqp) hsr,
    fun ν r he s hs hsr => h₂ ν r he s (hs.trans hqp) hsr⟩

theorem eq_symm {p : P} {σ τ : ZFSet.{u}} (h : EqAt code p σ τ) : EqAt code p τ σ :=
  eq_iff.mpr (eq_iff.mp h).symm

/-- Atomic membership is unchanged by closing densely below a condition. -/
theorem mem_of_dense {p : P} {σ τ : ZFSet.{u}}
    (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ MemAt code r σ τ) : MemAt code p σ τ := by
  apply mem_iff.mpr
  intro q hq
  obtain ⟨r, hrq, hr⟩ := h q hq
  obtain ⟨s, hsr, w⟩ := mem_iff.mp hr r le_rfl
  exact ⟨s, hsr.trans hrq, w⟩

/-- Atomic equality also has the dense-closure property. -/
theorem eq_of_dense {p : P} {σ τ : ZFSet.{u}}
    (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ EqAt code r σ τ) : EqAt code p σ τ := by
  have step : ∀ a b, (∀ q, q ≤ p → ∃ r, r ≤ q ∧ EqAt code r a b) →
      ∀ ν (s : P), ZFSet.pair ν (code s) ∈ a → ∀ q, q ≤ p → q ≤ s → MemAt code q ν b := by
    intro a b hab ν s he q hqp hqs
    apply mem_of_dense
    intro t htq
    obtain ⟨r, hrt, hr⟩ := hab t (htq.trans hqp)
    exact ⟨r, hrt, (eq_iff.mp hr).1 ν s he r le_rfl ((hrt.trans htq).trans hqs)⟩
  exact eq_iff.mpr ⟨step σ τ h, step τ σ (fun q hq => by
    obtain ⟨r, hrq, hr⟩ := h q hq
    exact ⟨r, hrq, eq_symm hr⟩)⟩

theorem mem_of_edge_eq {p r : P} {σ τ ν : ZFSet.{u}}
    (hr : p ≤ r) (he : ZFSet.pair ν (code r) ∈ τ) (h : EqAt code p σ ν) :
    MemAt code p σ τ := by
  apply mem_iff.mpr
  intro q hq
  exact ⟨q, le_rfl, ν, r, he, hq.trans hr, eq_mono hq h⟩

theorem eq_refl (p : P) (σ : ZFSet.{u}) : EqAt code p σ σ := by
  induction σ using child_wf.induction generalizing p with
  | h σ ih =>
    apply eq_iff.mpr
    have step : ∀ ν (r : P), ZFSet.pair ν (code r) ∈ σ →
        ∀ q, q ≤ p → q ≤ r → MemAt code q ν σ := by
      intro ν r he q _ hqr
      exact mem_of_edge_eq hqr he (ih ν ⟨(code r), he⟩ q)
    exact ⟨step, step⟩

noncomputable def tripleRanks (a b c : ZFSet.{u}) : Multiset Ordinal.{u} :=
  {a.rank} + {b.rank} + {c.rank}

def TripleLower (s t : ZFSet.{u} × ZFSet.{u} × ZFSet.{u}) : Prop :=
  Multiset.IsDershowitzMannaLT (tripleRanks s.1 s.2.1 s.2.2)
    (tripleRanks t.1 t.2.1 t.2.2)

theorem tripleLower_wf : WellFounded TripleLower.{u} :=
  InvImage.wf (fun s : ZFSet.{u} × ZFSet.{u} × ZFSet.{u} => tripleRanks s.1 s.2.1 s.2.2)
    Multiset.wellFounded_isDershowitzMannaLT

/-- All three substitution rules are proved together. The induction measure
is invariant under permutations, while replacing a name by a child decreases
it. In particular transitivity is a consequence, not an assumed atomic law. -/
theorem atomic_laws (a b c : ZFSet.{u}) :
    (∀ p : P, EqAt code p a b → EqAt code p b c → EqAt code p a c) ∧
    (∀ p : P, EqAt code p a b → MemAt code p a c → MemAt code p b c) ∧
    (∀ p : P, EqAt code p b c → MemAt code p a b → MemAt code p a c) := by
  let T (s : ZFSet.{u} × ZFSet.{u} × ZFSet.{u}) :=
    (∀ p : P, EqAt code p s.1 s.2.1 → EqAt code p s.2.1 s.2.2 → EqAt code p s.1 s.2.2) ∧
    (∀ p : P, EqAt code p s.1 s.2.1 → MemAt code p s.1 s.2.2 → MemAt code p s.2.1 s.2.2) ∧
    (∀ p : P, EqAt code p s.2.1 s.2.2 → MemAt code p s.1 s.2.1 → MemAt code p s.1 s.2.2)
  change T (a, b, c)
  apply tripleLower_wf.induction (C := T)
  rintro ⟨a,b,c⟩ ih
  refine ⟨?_, ?_, ?_⟩
  · intro p hab hbc
    apply eq_iff.mpr
    constructor
    · intro ν r he q hqp hqr
      have hl : TripleLower (ν,b,c) (a,b,c) := by
        simpa only [TripleLower, tripleRanks, add_comm, add_left_comm, add_assoc] using
          rank_replace ({b.rank} + {c.rank}) (show Child ν a from ⟨(code r), he⟩)
      exact (ih (ν,b,c) hl).2.2 q (eq_mono hqp hbc)
        ((eq_iff.mp hab).1 ν r he q hqp hqr)
    · intro ν r he q hqp hqr
      have hl : TripleLower (ν,b,a) (a,b,c) := by
        simpa only [TripleLower, tripleRanks, add_comm, add_left_comm, add_assoc] using
          rank_replace ({a.rank} + {b.rank}) (show Child ν c from ⟨(code r), he⟩)
      exact (ih (ν,b,a) hl).2.2 q (eq_symm (eq_mono hqp hab))
        ((eq_iff.mp hbc).2 ν r he q hqp hqr)
  · intro p hab hac
    apply mem_iff.mpr
    intro q hqp
    obtain ⟨s, hsq, ν, r, he, hsr, heq⟩ := mem_iff.mp hac q hqp
    have hl : TripleLower (b,a,ν) (a,b,c) := by
      simpa only [TripleLower, tripleRanks, add_comm, add_left_comm, add_assoc] using
        rank_replace ({a.rank} + {b.rank}) (show Child ν c from ⟨(code r), he⟩)
    exact ⟨s, hsq, ν, r, he, hsr,
      (ih (b,a,ν) hl).1 s (eq_symm (eq_mono (hsq.trans hqp) hab)) heq⟩
  · intro p hbc hab
    apply mem_of_dense
    intro q hqp
    obtain ⟨s, hsq, ν, r, he, hsr, heq⟩ := mem_iff.mp hab q hqp
    have hl : TripleLower (ν,a,c) (a,b,c) := by
      simpa only [TripleLower, tripleRanks, add_comm, add_left_comm, add_assoc] using
        rank_replace ({a.rank} + {c.rank}) (show Child ν b from ⟨(code r), he⟩)
    exact ⟨s, hsq, (ih (ν,a,c) hl).2.1 s (eq_symm heq)
      ((eq_iff.mp hbc).1 ν r he s (hsq.trans hqp) hsr)⟩

theorem eq_trans {p : P} {a b c : ZFSet.{u}} (hab : EqAt code p a b)
    (hbc : EqAt code p b c) : EqAt code p a c := (atomic_laws a b c).1 p hab hbc

theorem mem_congr_left {p : P} {a b c : ZFSet.{u}} (hab : EqAt code p a b) :
    MemAt code p a c ↔ MemAt code p b c :=
  ⟨(atomic_laws a b c).2.1 p hab, (atomic_laws b a c).2.1 p (eq_symm hab)⟩

theorem mem_congr_right {p : P} {a b c : ZFSet.{u}} (hbc : EqAt code p b c) :
    MemAt code p a b ↔ MemAt code p a c :=
  ⟨(atomic_laws a b c).2.2 p hbc, (atomic_laws a c b).2.2 p (eq_symm hbc)⟩

end AtomicForcing
end PartitionConsistency.SetForcingNames



namespace PartitionConsistency.SetForcingNames.AtomicForcing
universe u v
variable {P : Type v} [Preorder P] {code : P → ZFSet.{u}}

/-- The literal action transforms exactly the edges, including their condition
codes. Injectivity prevents an edge using a different code from entering this
fiber. -/
theorem edge_map_orderIso {f : ZFSet.{u} → ZFSet.{u}} (hf : Function.Injective f)
    (e : P ≃o P) (hcode : ∀ p, f (code p) = code (e p))
    {σ ν : ZFSet.{u}} {r : P} :
    ZFSet.pair ν (code (e r)) ∈ mapConditions f σ ↔
      ∃ ρ, ZFSet.pair ρ (code r) ∈ σ ∧ mapConditions f ρ = ν := by
  rw [← hcode r, edge_mapConditions_iff]
  constructor
  · rintro ⟨ρ, s, he, hn, hc⟩
    have hs := hf hc
    subst s
    exact ⟨ρ, he, hn⟩
  · rintro ⟨ρ, he, rfl⟩
    exact ⟨ρ, code r, he, rfl, rfl⟩

/-- Atomic symmetry on literal names. Conditions are moved together with the
names; this makes no assertion that a generic filter is fixed by the action. -/
theorem atomic_symmetry {f : ZFSet.{u} → ZFSet.{u}} (hf : Function.Injective f)
    (e : P ≃o P) (hcode : ∀ p, f (code p) = code (e p)) (σ τ : ZFSet.{u}) :
    (∀ p, MemAt code p σ τ ↔
      MemAt code (e p) (mapConditions f σ) (mapConditions f τ)) ∧
    (∀ p, EqAt code p σ τ ↔
      EqAt code (e p) (mapConditions f σ) (mapConditions f τ)) := by
  let T (st : ZFSet.{u} × ZFSet.{u}) :=
    (∀ p, MemAt code p st.1 st.2 ↔
      MemAt code (e p) (mapConditions f st.1) (mapConditions f st.2)) ∧
    (∀ p, EqAt code p st.1 st.2 ↔
      EqAt code (e p) (mapConditions f st.1) (mapConditions f st.2))
  change T (σ,τ)
  apply pairLower_wf.induction (C := T)
  rintro ⟨a,b⟩ ih
  refine ⟨fun p => ⟨?_, ?_⟩, fun p => ⟨?_, ?_⟩⟩
  · intro hm
    apply mem_iff.mpr
    intro q hqp
    obtain ⟨q, rfl⟩ := e.surjective q
    obtain ⟨s, hsq, ν, r, he, hsr, heq⟩ := mem_iff.mp hm q (e.le_iff_le.mp hqp)
    refine ⟨e s, e.monotone hsq, mapConditions f ν, e r, ?_, e.monotone hsr, ?_⟩
    · exact (edge_map_orderIso hf e hcode).mpr ⟨ν, he, rfl⟩
    · exact ((ih (a,ν) (pairLower_right ⟨code r, he⟩)).2 s).mp heq
  · intro hm
    apply mem_iff.mpr
    intro q hqp
    obtain ⟨s, hsq, ν, r, he, hsr, heq⟩ := mem_iff.mp hm (e q) (e.monotone hqp)
    obtain ⟨s, rfl⟩ := e.surjective s
    obtain ⟨r, rfl⟩ := e.surjective r
    obtain ⟨ρ, hρ, hν⟩ := (edge_map_orderIso hf e hcode).mp he
    subst ν
    refine ⟨s, e.le_iff_le.mp hsq, ρ, r, hρ, e.le_iff_le.mp hsr, ?_⟩
    exact ((ih (a,ρ) (pairLower_right ⟨code r, hρ⟩)).2 s).mpr heq
  · intro heq
    apply eq_iff.mpr
    constructor
    · intro ν r he q hqp hqr
      obtain ⟨r, rfl⟩ := e.surjective r
      obtain ⟨q, rfl⟩ := e.surjective q
      obtain ⟨ρ, hρ, hν⟩ := (edge_map_orderIso hf e hcode).mp he
      subst ν
      exact ((ih (ρ,b) (pairLower_left ⟨code r, hρ⟩)).1 q).mp
        ((eq_iff.mp heq).1 ρ r hρ q (e.le_iff_le.mp hqp) (e.le_iff_le.mp hqr))
    · intro ν r he q hqp hqr
      obtain ⟨r, rfl⟩ := e.surjective r
      obtain ⟨q, rfl⟩ := e.surjective q
      obtain ⟨ρ, hρ, hν⟩ := (edge_map_orderIso hf e hcode).mp he
      subst ν
      exact ((ih (ρ,a) (pairLower_swap ⟨code r, hρ⟩)).1 q).mp
        ((eq_iff.mp heq).2 ρ r hρ q (e.le_iff_le.mp hqp) (e.le_iff_le.mp hqr))
  · intro heq
    apply eq_iff.mpr
    constructor
    · intro ν r he q hqp hqr
      have he' : ZFSet.pair (mapConditions f ν) (code (e r)) ∈ mapConditions f a :=
        (edge_map_orderIso hf e hcode).mpr ⟨ν, he, rfl⟩
      exact ((ih (ν,b) (pairLower_left ⟨code r, he⟩)).1 q).mpr
        ((eq_iff.mp heq).1 _ _ he' (e q) (e.monotone hqp) (e.monotone hqr))
    · intro ν r he q hqp hqr
      have he' : ZFSet.pair (mapConditions f ν) (code (e r)) ∈ mapConditions f b :=
        (edge_map_orderIso hf e hcode).mpr ⟨ν, he, rfl⟩
      exact ((ih (ν,a) (pairLower_swap ⟨code r, he⟩)).1 q).mpr
        ((eq_iff.mp heq).2 _ _ he' (e q) (e.monotone hqp) (e.monotone hqr))

end PartitionConsistency.SetForcingNames.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_ForcingTruth
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency.ForcingQuotient.AtomicData

variable {P N : Type*} [Preorder P] (A : AtomicData P N)

/-- Induction through the defined logical forcing relation propagates a
condition/name automorphism from the atomic cases to each fixed formula.
The existential clause remains density of local witnesses. -/
theorem force_symmetry (e : P ≃o P) (f : N ≃ N)
    (heq : ∀ p a b, A.EqF p a b ↔ A.EqF (e p) (f a) (f b))
    (hmem : ∀ p a b, A.MemF p a b ↔ A.MemF (e p) (f a) (f b))
    {n} (φ : BasicFormula n) (v : Fin n → N) (p : P) :
    A.Force v p φ ↔ A.Force (f ∘ v) (e p) φ := by
  induction φ generalizing p with
  | bot => rfl
  | mem a b => exact hmem p (v a) (v b)
  | equal a b => exact heq p (v a) (v b)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ v p) (ihψ v p)
  | neg φ ih =>
    constructor
    · intro h q hqp hq
      obtain ⟨q, rfl⟩ := e.surjective q
      exact h q (e.le_iff_le.mp hqp) ((ih v q).mpr hq)
    · intro h q hqp hq
      exact h (e q) (e.monotone hqp) ((ih v q).mp hq)
  | ex φ ih =>
    constructor
    · intro h q hqp
      obtain ⟨q, rfl⟩ := e.surjective q
      obtain ⟨r, hrq, x, hx⟩ := h q (e.le_iff_le.mp hqp)
      refine ⟨e r, e.monotone hrq, f x, ?_⟩
      simpa only [Fin.comp_snoc] using (ih (Fin.snoc v x) r).mp hx
    · intro h q hqp
      obtain ⟨r, hrq, x, hx⟩ := h (e q) (e.monotone hqp)
      obtain ⟨r, rfl⟩ := e.surjective r
      obtain ⟨x, rfl⟩ := f.surjective x
      refine ⟨r, e.le_iff_le.mp hrq, x, (ih (Fin.snoc v x) r).mpr ?_⟩
      simpa only [Fin.comp_snoc] using hx

end PartitionConsistency.ForcingQuotient.AtomicData



namespace PartitionConsistency.ForcingQuotient.AtomicData
variable {P N : Type*} [Preorder P] (A : AtomicData P N)

/-- The ordinary forcing relation is regular: density of atomic forcing below
`p` already implies forcing at `p`. This property is separately verified by the
actual name recursion, not assumed for any target axiom. -/
def Regular : Prop :=
  (∀ p a b, (∀ q, q ≤ p → ∃ r, r ≤ q ∧ A.EqF r a b) → A.EqF p a b) ∧
  (∀ p a b, (∀ q, q ≤ p → ∃ r, r ≤ q ∧ A.MemF r a b) → A.MemF p a b)

/-- Dense closure extends from the atomic relations to every fixed formula. -/
theorem force_of_dense (hA : A.Regular) {n} (φ : BasicFormula n) (v : Fin n → N)
    (p : P) (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ A.Force v r φ) : A.Force v p φ := by
  induction φ generalizing p with
  | bot => obtain ⟨r, _, hr⟩ := h p le_rfl; exact hr
  | mem x y => exact hA.2 p (v x) (v y) h
  | equal x y => exact hA.1 p (v x) (v y) h
  | conj φ ψ ihφ ihψ =>
    refine ⟨ihφ v p ?_, ihψ v p ?_⟩
    · intro q hq
      obtain ⟨r, hrq, hr⟩ := h q hq
      exact ⟨r, hrq, hr.1⟩
    · intro q hq
      obtain ⟨r, hrq, hr⟩ := h q hq
      exact ⟨r, hrq, hr.2⟩
  | neg φ _ =>
    intro q hqp hq
    obtain ⟨r, hrq, hr⟩ := h q hqp
    exact hr r le_rfl (A.force_mono φ v hrq hq)
  | ex φ _ =>
    intro q hqp
    obtain ⟨r, hrq, hr⟩ := h q hqp
    obtain ⟨s, hsr, hs⟩ := hr r le_rfl
    exact ⟨s, hsr.trans hrq, hs⟩

theorem exists_force_neg (hA : A.Regular) {n} (φ : BasicFormula n) (v : Fin n → N)
    {p : P} (h : ¬ A.Force v p φ) : ∃ q, q ≤ p ∧ A.Force v q (.neg φ) := by
  classical
  by_contra! hn
  apply h
  apply A.force_of_dense hA φ v
  intro q hqp
  have hnot := hn q hqp
  change ¬ (∀ r, r ≤ q → ¬ A.Force v r φ) at hnot
  push Not at hnot
  exact hnot

/-- Forcing in the full syntax of the statement is the previously defined
Boolean/existential-basis forcing, with no change of quantifier domain. -/
def ForceFormula {n} (v : Fin n → N) (p : P) (φ : Formula n) : Prop :=
  A.Force v p φ.toBasic

theorem forceFormula_mono {n} {v : Fin n → N} {p q : P} {φ : Formula n}
    (hqp : q ≤ p) (h : A.ForceFormula v p φ) : A.ForceFormula v q φ :=
  A.force_mono φ.toBasic v hqp h

@[simp] theorem forceFormula_bot {n} (v : Fin n → N) (p : P) :
    A.ForceFormula v p .bot ↔ False := Iff.rfl

@[simp] theorem forceFormula_mem {n} (v : Fin n → N) (p : P) (x y : Fin n) :
    A.ForceFormula v p (.mem x y) ↔ A.MemF p (v x) (v y) := Iff.rfl

@[simp] theorem forceFormula_equal {n} (v : Fin n → N) (p : P) (x y : Fin n) :
    A.ForceFormula v p (.equal x y) ↔ A.EqF p (v x) (v y) := Iff.rfl

@[simp] theorem forceFormula_conj {n} (v : Fin n → N) (p : P) (φ ψ : Formula n) :
    A.ForceFormula v p (.conj φ ψ) ↔ A.ForceFormula v p φ ∧ A.ForceFormula v p ψ := Iff.rfl

theorem forceFormula_imp (hA : A.Regular) {n} (v : Fin n → N) (p : P) (φ ψ : Formula n) :
    A.ForceFormula v p (.imp φ ψ) ↔
      ∀ q, q ≤ p → A.ForceFormula v q φ → A.ForceFormula v q ψ := by
  constructor
  · intro h q hqp hq
    by_contra! hn
    obtain ⟨r, hrq, hr⟩ := A.exists_force_neg hA ψ.toBasic v hn
    exact h r (hrq.trans hqp) ⟨A.forceFormula_mono hrq hq, hr⟩
  · intro h q hqp hq
    exact hq.2 q le_rfl (h q hqp hq.1)

theorem forceFormula_disj {n} (v : Fin n → N) (p : P) (φ ψ : Formula n) :
    A.ForceFormula v p (.disj φ ψ) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ (A.ForceFormula v r φ ∨ A.ForceFormula v r ψ) := by
  classical
  constructor
  · intro h q hqp
    by_contra! hn
    apply h q hqp
    exact ⟨fun r hrq hr => (hn r hrq).1 hr, fun r hrq hr => (hn r hrq).2 hr⟩
  · intro h q hqp hq
    obtain ⟨r, hrq, hr | hr⟩ := h q hqp
    · exact hq.1 r hrq hr
    · exact hq.2 r hrq hr

@[simp] theorem forceFormula_ex {n} (v : Fin n → N) (p : P) (φ : Formula (n+1)) :
    A.ForceFormula v p (.ex φ) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x, A.ForceFormula (Fin.snoc v x) r φ := Iff.rfl

theorem forceFormula_all (hA : A.Regular) {n} (v : Fin n → N) (p : P)
    (φ : Formula (n+1)) : A.ForceFormula v p (.all φ) ↔
      ∀ x, A.ForceFormula (Fin.snoc v x) p φ := by
  constructor
  · intro h x
    by_contra! hn
    obtain ⟨q, hqp, hq⟩ := A.exists_force_neg hA φ.toBasic (Fin.snoc v x) hn
    apply h q hqp
    intro r hrq
    exact ⟨r, le_rfl, x, A.force_mono (.neg φ.toBasic) (Fin.snoc v x) hrq hq⟩
  · intro h q hqp hq
    obtain ⟨r, hrq, x, hr⟩ := hq q le_rfl
    exact hr r le_rfl (A.forceFormula_mono (hrq.trans hqp) (h x))

theorem forceFormula_rename (hA : A.Regular) {n m} (φ : Formula n) (r : Fin n → Fin m)
    (v : Fin m → N) (p : P) :
    A.ForceFormula v p (φ.rename r) ↔ A.ForceFormula (v ∘ r) p φ := by
  induction φ generalizing m p with
  | bot => rfl
  | mem => rfl
  | equal => rfl
  | imp φ ψ ihφ ihψ =>
    simp only [Formula.rename, A.forceFormula_imp hA, ihφ, ihψ]
  | conj φ ψ ihφ ihψ =>
    simp only [Formula.rename, forceFormula_conj, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
    simp only [Formula.rename, forceFormula_disj, ihφ, ihψ]
  | all φ ih =>
    simp only [Formula.rename, A.forceFormula_all hA, ih, Formula.snoc_comp_liftRen]
  | ex φ ih =>
    simp only [Formula.rename, forceFormula_ex, ih, Formula.snoc_comp_liftRen]

/-- Equality substitution for all formulas follows from the atomic laws. -/
theorem force_tuple_congr {n} (φ : BasicFormula n) (v w : Fin n → N) (p : P)
    (hvw : ∀ i, A.EqF p (v i) (w i)) : A.Force v p φ ↔ A.Force w p φ := by
  induction φ generalizing p with
  | bot => rfl
  | mem x y => exact A.mem_congr (hvw x) (hvw y)
  | equal x y =>
    constructor
    · intro h
      exact A.eq_trans (A.eq_symm (hvw x)) (A.eq_trans h (hvw y))
    · intro h
      exact A.eq_trans (hvw x) (A.eq_trans h (A.eq_symm (hvw y)))
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ v w p hvw) (ihψ v w p hvw)
  | neg φ ih =>
    constructor
    · intro h q hqp hq
      exact h q hqp ((ih v w q (fun i => A.eq_mono hqp (hvw i))).mpr hq)
    · intro h q hqp hq
      exact h q hqp ((ih v w q (fun i => A.eq_mono hqp (hvw i))).mp hq)
  | @ex n φ ih =>
    have step : ∀ v w : Fin n → N, (∀ i, A.EqF p (v i) (w i)) →
        A.Force v p (.ex φ) → A.Force w p (.ex φ) := by
      intro v w he h q hqp
      obtain ⟨r, hrq, x, hr⟩ := h q hqp
      refine ⟨r, hrq, x, (ih (Fin.snoc v x) (Fin.snoc w x) r ?_).mp hr⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using A.eq_refl r x
      · simpa using A.eq_mono (hrq.trans hqp) (he j)
    exact ⟨step v w hvw, step w v (fun i => A.eq_symm (hvw i))⟩

theorem forceFormula_tuple_congr {n} (φ : Formula n) (v w : Fin n → N) (p : P)
    (hvw : ∀ i, A.EqF p (v i) (w i)) :
    A.ForceFormula v p φ ↔ A.ForceFormula w p φ := A.force_tuple_congr φ.toBasic v w p hvw

end PartitionConsistency.ForcingQuotient.AtomicData

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_SymmetricNames
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency.SetForcingNames
universe u v w

/-- A set symmetric system with a named presentation of the conditions.
Every piece of data is algebraic: no forcing axiom or satisfaction assertion
is included in this structure. The equivalence also ensures that the poset is
a set in the same universe as the literal name codes. -/
structure SymmetricSystem (P : Type w) [Preorder P] (Γ : Type v) [Group Γ] where
  action : ConditionAction.{u} Γ
  codeEquiv : P ≃ action.conditions
  order : ∀ g p q,
    codeEquiv.symm (action.perm g (codeEquiv p)) ≤
      codeEquiv.symm (action.perm g (codeEquiv q)) ↔ p ≤ q
  filter : Set (Subgroup Γ)
  normal : SupportFilter.IsNormalFilter filter

namespace SymmetricSystem
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

theorem small_conditions (S : SymmetricSystem.{u} P Γ) : Small.{u} P := small_of_injective S.codeEquiv.injective

/-- The actual set code, not a semantic truth value. -/
def code (p : P) : ZFSet.{u} := (S.codeEquiv p).val

theorem code_mem (p : P) : S.code p ∈ S.action.conditions := (S.codeEquiv p).property

theorem code_injective : Function.Injective S.code := fun _ _ h =>
  S.codeEquiv.injective (Subtype.ext h)

/-- Automorphisms of the poset obtained from its coded action. -/
noncomputable def move (g : Γ) : P ≃o P where
  toEquiv := (S.codeEquiv.trans (S.action.perm g)).trans S.codeEquiv.symm
  map_rel_iff' := fun {p q} => S.order g p q

@[simp] theorem actCode_code (g : Γ) (p : P) :
    S.action.actCode g (S.code p) = S.code (S.move g p) := by
  rw [S.action.actCode_of_mem g (S.code_mem p)]
  change (S.action.perm g (S.codeEquiv p)).val =
    (S.codeEquiv (S.codeEquiv.symm (S.action.perm g (S.codeEquiv p)))).val
  rw [Equiv.apply_symm_apply]

/-- All hereditarily symmetric names, without any fixed bound on ranks. -/
def Name := {σ : S.action.Name // ConditionAction.Name.HS S.filter σ}

namespace Name
variable {S}

def raw (σ : S.Name) : ZFSet.{u} := σ.1.val

@[ext] theorem ext {σ τ : S.Name} (h : σ.raw = τ.raw) : σ = τ :=
  Subtype.ext (ConditionAction.Name.ext h)

theorem isName (σ : S.Name) : IsName S.action.conditions σ.raw := σ.1.property

theorem hs (σ : S.Name) : ConditionAction.Name.HS S.filter σ.1 := σ.property

/-- An active entry is automatically HS by hereditary symmetry. -/
def child (σ : S.Name) {ρ c : ZFSet.{u}} (he : ZFSet.pair ρ c ∈ σ.raw) : S.Name :=
  ⟨σ.1.child he, σ.property.child he⟩

@[simp] theorem child_val (σ : S.Name) {ρ c : ZFSet.{u}} (he : ZFSet.pair ρ c ∈ σ.raw) :
    (σ.child he).raw = ρ := rfl

noncomputable instance instMulAction : MulAction Γ S.Name where
  smul g σ := ⟨g • σ.1, σ.property.smul S.normal g⟩
  one_smul σ := Subtype.ext (one_smul Γ σ.1)
  mul_smul g h σ := Subtype.ext (mul_smul g h σ.1)

@[simp] theorem smul_val (g : Γ) (σ : S.Name) :
    (g • σ).raw = mapConditions (S.action.actCode g) σ.raw := rfl

noncomputable def empty : S.Name :=
  ⟨ConditionAction.Name.empty, ConditionAction.Name.empty_HS S.normal.1⟩

@[simp] theorem empty_val : (empty : S.Name).raw = ∅ := rfl

end Name

/-- The previously constructed recursive atomic relations, restricted to the
actual HS class of this set symmetric system. -/
noncomputable def atomic : ForcingQuotient.AtomicData P S.Name where
  EqF p a b := AtomicForcing.EqAt S.code p a.raw b.raw
  MemF p a b := AtomicForcing.MemAt S.code p a.raw b.raw
  eq_mono := AtomicForcing.eq_mono
  mem_mono := AtomicForcing.mem_mono
  eq_refl p a := AtomicForcing.eq_refl p a.raw
  eq_symm := AtomicForcing.eq_symm
  eq_trans := AtomicForcing.eq_trans
  mem_congr ha hb := (AtomicForcing.mem_congr_left ha).trans (AtomicForcing.mem_congr_right hb)

theorem atomic_regular : S.atomic.Regular :=
  ⟨fun _ _ _ => AtomicForcing.eq_of_dense, fun _ _ _ => AtomicForcing.mem_of_dense⟩

/-- Named formula forcing in this symmetric system. Quantifiers range over all
HS names; the existential clause remains density of local witnesses. -/
abbrev Forces {n} (v : Fin n → S.Name) (p : P) (φ : Formula n) : Prop :=
  S.atomic.ForceFormula v p φ

/-- Full formula symmetry for the concrete HS class. -/
theorem forces_symmetry (g : Γ) {n} (φ : Formula n) (v : Fin n → S.Name) (p : P) :
    S.Forces v p φ ↔ S.Forces (fun i => g • v i) (S.move g p) φ := by
  apply S.atomic.force_symmetry (S.move g) (MulAction.toPerm g)
  · intro p a b
    exact (AtomicForcing.atomic_symmetry (S.action.actCode_injective g)
      (S.move g) (S.actCode_code g) a.raw b.raw).2 p
  · intro p a b
    exact (AtomicForcing.atomic_symmetry (S.action.actCode_injective g)
      (S.move g) (S.actCode_code g) a.raw b.raw).1 p

end SymmetricSystem
end PartitionConsistency.SetForcingNames



namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Active members of an HS name are in the same quantifier domain. -/
theorem mem_iff {p : P} {ν σ : S.Name} : S.atomic.MemF p ν σ ↔
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ (τ : S.Name) (c : P),
      ZFSet.pair τ.raw (S.code c) ∈ σ.raw ∧ r ≤ c ∧ S.atomic.EqF r ν τ := by
  constructor
  · intro h q hqp
    obtain ⟨r, hrq, τ, c, he, hrc, heq⟩ := AtomicForcing.mem_iff.mp h q hqp
    exact ⟨r, hrq, σ.child he, c, he, hrc, heq⟩
  · intro h
    apply AtomicForcing.mem_iff.mpr
    intro q hqp
    obtain ⟨r, hrq, τ, c, he, hrc, heq⟩ := h q hqp
    exact ⟨r, hrq, τ.raw, c, he, hrc, heq⟩

theorem mem_of_edge {p c : P} {σ τ : S.Name}
    (he : ZFSet.pair τ.raw (S.code c) ∈ σ.raw) (hpc : p ≤ c) :
    S.atomic.MemF p τ σ := AtomicForcing.mem_of_edge_eq hpc he (S.atomic.eq_refl p τ)

/-- Extensionality is proved from the recursive definition of equality, not
assumed as another law of a forcing algebra. -/
theorem eq_of_same_members {p : P} {σ τ : S.Name}
    (h : ∀ ν : S.Name, ∀ q, q ≤ p → (S.atomic.MemF q ν σ ↔ S.atomic.MemF q ν τ)) :
    S.atomic.EqF p σ τ := by
  apply AtomicForcing.eq_iff.mpr
  constructor
  · intro ν c he q hqp hqc
    exact (h (σ.child he) q hqp).mp (S.mem_of_edge he hqc)
  · intro ν c he q hqp hqc
    exact (h (τ.child he) q hqp).mpr (S.mem_of_edge he hqc)

end PartitionConsistency.SetForcingNames.SymmetricSystem



namespace PartitionConsistency.SetForcingNames
universe u v w t

/-- Transport of the immediate membership graph preserves inclusions. -/
theorem mapConditions_mono (f : ZFSet.{u} → ZFSet.{u}) {σ τ : ZFSet.{u}} (h : σ ⊆ τ) :
    mapConditions f σ ⊆ mapConditions f τ := by
  intro z hz
  obtain ⟨ν, p, he, hz⟩ := mem_mapConditions_iff.mp hz
  exact mem_mapConditions_iff.mpr ⟨ν, p, h he, hz⟩

namespace SymmetricSystem
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- A small family of HS names with any predicate on its entry conditions. -/
noncomputable def collectRaw {ι : Type t} [Small.{u} ι] (f : ι → S.Name)
    (R : ι → P → Prop) : ZFSet.{u} := by
  letI := S.small_conditions
  exact ZFSet.range (fun z : {z : ι × P // R z.1 z.2} =>
    ZFSet.pair (f z.val.1).raw (S.code z.val.2))

theorem mem_collectRaw {ι : Type t} [Small.{u} ι] (f : ι → S.Name)
    (R : ι → P → Prop) (z : ZFSet.{u}) :
    z ∈ S.collectRaw f R ↔ ∃ i p, R i p ∧ ZFSet.pair (f i).raw (S.code p) = z := by
  let := S.small_conditions
  rw [collectRaw, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨i,p⟩,hR⟩,hz⟩
    exact ⟨i,p,hR,hz⟩
  · rintro ⟨i,p,hR,hz⟩
    exact ⟨⟨(i,p),hR⟩,hz⟩

theorem edge_collectRaw {ι : Type t} [Small.{u} ι] (f : ι → S.Name)
    (R : ι → P → Prop) (ν c : ZFSet.{u}) :
    ZFSet.pair ν c ∈ S.collectRaw f R ↔
      ∃ i p, R i p ∧ (f i).raw = ν ∧ S.code p = c := by
  simp only [mem_collectRaw, ZFSet.pair_inj]

theorem isName_collectRaw {ι : Type t} [Small.{u} ι] (f : ι → S.Name)
    (R : ι → P → Prop) : IsName S.action.conditions (S.collectRaw f R) := by
  apply IsName.intro
  intro z hz
  obtain ⟨i,p,_,rfl⟩ := (S.mem_collectRaw f R z).mp hz
  exact ⟨(f i).raw, S.code p, rfl, S.code_mem p, (f i).isName⟩

noncomputable def collectName {ι : Type t} [Small.{u} ι] (f : ι → S.Name)
    (R : ι → P → Prop) : S.action.Name := ⟨S.collectRaw f R, S.isName_collectRaw f R⟩

/-- Permuting the entry family fixes its literal set of pairs. This lemma
contains no coherence or forcing premise. -/
theorem collect_HS {ι : Type t} [Small.{u} ι] (f : ι → S.Name) (R : ι → P → Prop)
    (H : Subgroup Γ) (hH : H ∈ S.filter)
    (permutes : ∀ g ∈ H, ∀ i p, R i p → ∃ j,
      f j = g • f i ∧ R j (S.move g p)) :
    ConditionAction.Name.HS S.filter (S.collectName f R) := by
  have hsub (g : Γ) (hg : g ∈ H) :
      (g • S.collectName f R).val ⊆ (S.collectName f R).val := by
    intro z hz
    obtain ⟨ν,c,he,rfl⟩ := mem_mapConditions_iff.mp hz
    obtain ⟨i,p,hR,rfl,rfl⟩ := (S.edge_collectRaw f R ν c).mp he
    obtain ⟨j,hj,hRj⟩ := permutes g hg i p hR
    apply (S.mem_collectRaw f R _).mpr
    refine ⟨j, S.move g p, hRj, ?_⟩
    rw [hj, Name.smul_val, S.actCode_code]
  apply ConditionAction.Name.hs_iff.mpr
  constructor
  · apply S.normal.2.1 H _ hH
    intro g hg
    apply ConditionAction.Name.ext
    apply le_antisymm (hsub g hg)
    have hi := mapConditions_mono (S.action.actCode g) (hsub g⁻¹ (H.inv_mem hg))
    change (g • (g⁻¹ • S.collectName f R)).val ⊆ (g • S.collectName f R).val at hi
    simpa only [smul_inv_smul] using hi
  · rintro τ ⟨c,hc⟩
    obtain ⟨i,p,_,hi,_⟩ := (S.edge_collectRaw f R τ.val c).mp hc
    have heq : (f i).val = τ := ConditionAction.Name.ext hi
    exact heq ▸ (f i).hs

/-- The collected name is packaged with the proved hereditary symmetry. -/
noncomputable def collect {ι : Type t} [Small.{u} ι] (f : ι → S.Name) (R : ι → P → Prop)
    (H : Subgroup Γ) (hH : H ∈ S.filter)
    (permutes : ∀ g ∈ H, ∀ i p, R i p → ∃ j,
      f j = g • f i ∧ R j (S.move g p)) : S.Name :=
  ⟨S.collectName f R, S.collect_HS f R H hH permutes⟩

/-- Finite tuples have a common subgroup in the given normal filter. -/
noncomputable def tupleStabilizer : {n : ℕ} → (Fin n → S.Name) → Subgroup Γ
  | 0, _ => ⊤
  | n+1, v => tupleStabilizer (fun i => v i.castSucc) ⊓ MulAction.stabilizer Γ (v (Fin.last n)).val

theorem tupleStabilizer_mem {n} (v : Fin n → S.Name) : S.tupleStabilizer v ∈ S.filter := by
  induction n with
  | zero => exact S.normal.1
  | succ n ih => exact S.normal.2.2.1 _ _ (ih _) (v (Fin.last n)).hs.symmetric

theorem mem_tupleStabilizer {n} (v : Fin n → S.Name) (g : Γ) :
    g ∈ S.tupleStabilizer v ↔ ∀ i, g • v i = v i := by
  induction n with
  | zero => simp [tupleStabilizer]
  | succ n ih =>
    simp only [tupleStabilizer, Subgroup.mem_inf, ih, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨h,hl⟩ i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact Subtype.ext hl
      · exact h j
    · intro h
      exact ⟨fun i => h i.castSucc, congrArg Subtype.val (h (Fin.last n))⟩

/-- Atomic symmetry, explicitly in the HS-name domain used by all quantifiers. -/
theorem mem_symmetry (g : Γ) (p : P) (σ τ : S.Name) :
    S.atomic.MemF p σ τ ↔ S.atomic.MemF (S.move g p) (g • σ) (g • τ) :=
  (AtomicForcing.atomic_symmetry (S.action.actCode_injective g)
    (S.move g) (S.actCode_code g) σ.raw τ.raw).1 p

theorem eq_symmetry (g : Γ) (p : P) (σ τ : S.Name) :
    S.atomic.EqF p σ τ ↔ S.atomic.EqF (S.move g p) (g • σ) (g • τ) :=
  (AtomicForcing.atomic_symmetry (S.action.actCode_injective g)
    (S.move g) (S.actCode_code g) σ.raw τ.raw).2 p

end SymmetricSystem
end PartitionConsistency.SetForcingNames



namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Literal entry families are carried to literal entry families by the group. -/
theorem entry_permute (g : Γ) (σ : S.Name) (i : Edges σ.raw) :
    ∃ j : Edges (g • σ).raw, (g • σ).child j.property = g • σ.child i.property := by
  have he : ZFSet.pair (mapConditions (S.action.actCode g) i.val.1)
      (S.action.actCode g i.val.2) ∈ (g • σ).raw :=
    edge_mapConditions_iff.mpr ⟨i.val.1, i.val.2, i.property, rfl, rfl⟩
  refine ⟨⟨(mapConditions (S.action.actCode g) i.val.1, S.action.actCode g i.val.2),he⟩, ?_⟩
  apply Name.ext
  rfl

noncomputable def separationTest {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+1)) (i : Edges σ.raw) (p : P) : Prop :=
  S.atomic.MemF p (σ.child i.property) σ ∧ S.Forces (Fin.snoc v (σ.child i.property)) p φ

theorem separationTest_permute {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+1)) :
    ∀ g ∈ MulAction.stabilizer Γ σ.val ⊓ S.tupleStabilizer v,
      ∀ i p, S.separationTest σ v φ i p → ∃ j,
      σ.child j.property = g • σ.child i.property ∧ S.separationTest σ v φ j (S.move g p) := by
  intro g hg i p hi
  have hσ : g • σ = σ := Subtype.ext hg.1
  have hv := (S.mem_tupleStabilizer v g).mp hg.2
  have he := S.entry_permute g σ i
  rw [hσ] at he
  obtain ⟨j,hj⟩ := he
  refine ⟨j,hj,?_,?_⟩
  · change S.atomic.MemF (S.move g p) (σ.child j.property) σ
    rw [hj]
    simpa only [hσ] using (S.mem_symmetry g p (σ.child i.property) σ).mp hi.1
  · change S.Forces (Fin.snoc v (σ.child j.property)) (S.move g p) φ
    rw [hj]
    have hvec : (fun k => g • Fin.snoc v (σ.child i.property) k) =
        Fin.snoc v (g • σ.child i.property) := by
      funext k
      refine Fin.lastCases ?_ (fun l => ?_) k <;> simp [hv]
    simpa only [hvec] using (S.forces_symmetry g φ (Fin.snoc v (σ.child i.property)) p).mp hi.2

/-- The Separation name for an arbitrary formula with an arbitrary finite
parameter tuple. Its entries are taken only from the original name's domain. -/
noncomputable def separate {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+1)) : S.Name :=
  S.collect (fun i : Edges σ.raw => σ.child i.property) (S.separationTest σ v φ)
    (MulAction.stabilizer Γ σ.val ⊓ S.tupleStabilizer v)
    (S.normal.2.2.1 _ _ σ.hs.symmetric (S.tupleStabilizer_mem v))
    (S.separationTest_permute σ v φ)

end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_SymmetricSets
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

@[simp] theorem code_top_fixed (g : Γ) : S.action.actCode g (S.code ⊤) = S.code ⊤ := by
  rw [S.actCode_code, (S.move g).map_top]

namespace Name
variable {S}

noncomputable def pair (σ τ : S.Name) : S.Name :=
  ⟨ConditionAction.Name.pair (S.code_mem ⊤) σ.val τ.val,
    ConditionAction.Name.pair_HS S.normal (S.code_mem ⊤) S.code_top_fixed σ.hs τ.hs⟩

noncomputable def check (x : ZFSet.{u}) : S.Name :=
  ⟨ConditionAction.Name.check (S.code_mem ⊤) x,
    ConditionAction.Name.check_HS S.normal.1 (S.code_mem ⊤) S.code_top_fixed x⟩

@[simp] theorem check_raw (x : ZFSet.{u}) : (check (S := S) x).raw = checkName (S.code ⊤) x := rfl

@[simp] theorem check_empty : check (S := S) ∅ = empty := by
  apply ext
  apply ZFSet.ext
  intro z
  simp [check_raw, mem_checkName_iff, empty_val]

end Name

theorem edge_pair (σ τ ν : S.Name) (c : P) :
    ZFSet.pair ν.raw (S.code c) ∈ (σ.pair τ).raw ↔ (ν = σ ∨ ν = τ) ∧ c = ⊤ := by
  change ZFSet.pair ν.raw (S.code c) ∈ pairName (S.code ⊤) σ.raw τ.raw ↔ _
  rw [edge_pairName_iff]
  have hinj : Function.Injective (Name.raw : S.Name → ZFSet.{u}) := fun _ _ => Name.ext
  simp only [hinj.eq_iff, S.code_injective.eq_iff]

theorem mem_pair (σ τ ν : S.Name) (p : P) : S.atomic.MemF p ν (σ.pair τ) ↔
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ (S.atomic.EqF r ν σ ∨ S.atomic.EqF r ν τ) := by
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,η,c,he,_,heq⟩ := (S.mem_iff.mp h) q hqp
    obtain ⟨hη | hη,_⟩ := (S.edge_pair σ τ η c).mp he
    · exact ⟨r,hrq,Or.inl (hη ▸ heq)⟩
    · exact ⟨r,hrq,Or.inr (hη ▸ heq)⟩
  · intro h
    apply S.mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,heq | heq⟩ := h q hqp
    · exact ⟨r,hrq,σ,⊤,(S.edge_pair σ τ σ ⊤).mpr ⟨Or.inl rfl,rfl⟩,le_top,heq⟩
    · exact ⟨r,hrq,τ,⊤,(S.edge_pair σ τ τ ⊤).mpr ⟨Or.inr rfl,rfl⟩,le_top,heq⟩

end PartitionConsistency.SetForcingNames.SymmetricSystem



namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w t
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- The same entry-permutation argument records the particular fixing subgroup,
not merely that some subgroup in the filter fixes the collected name. -/
theorem collectName_fixed {ι : Type t} [Small.{u} ι] (f : ι → S.Name) (R : ι → P → Prop)
    (H : Subgroup Γ)
    (permutes : ∀ g ∈ H, ∀ i p, R i p → ∃ j,
      f j = g • f i ∧ R j (S.move g p)) (g : Γ) (hg : g ∈ H) :
    g • S.collectName f R = S.collectName f R := by
  have hsub (g : Γ) (hg : g ∈ H) :
      (g • S.collectName f R).val ⊆ (S.collectName f R).val := by
    intro z hz
    obtain ⟨ν,c,he,rfl⟩ := mem_mapConditions_iff.mp hz
    obtain ⟨i,p,hR,rfl,rfl⟩ := (S.edge_collectRaw f R ν c).mp he
    obtain ⟨j,hj,hRj⟩ := permutes g hg i p hR
    apply (S.mem_collectRaw f R _).mpr
    refine ⟨j, S.move g p, hRj, ?_⟩
    rw [hj, Name.smul_val, S.actCode_code]
  apply ConditionAction.Name.ext
  apply le_antisymm (hsub g hg)
  have hi := mapConditions_mono (S.action.actCode g) (hsub g⁻¹ (H.inv_mem hg))
  change (g • (g⁻¹ • S.collectName f R)).val ⊆ (g • S.collectName f R).val at hi
  simpa only [smul_inv_smul] using hi

/-- All possible immediate pairs over the domain of a particular name form a
set. This is a bound on normalizations of subsets, not on all HS names. -/
noncomputable def subsetBound (σ : S.Name) : ZFSet.{u} :=
  S.collectRaw (fun i : Edges σ.raw => σ.child i.property) (fun _ _ => True)

theorem subsetBound_fixed (σ : S.Name) (g : Γ) (hg : g • σ = σ) :
    mapConditions (S.action.actCode g) (S.subsetBound σ) = S.subsetBound σ := by
  have hp : ∀ h ∈ MulAction.stabilizer Γ σ.val, ∀ (i : Edges σ.raw) (p : P),
      True → ∃ j : Edges σ.raw, σ.child j.property = h • σ.child i.property ∧ True := by
    intro h hh i p _
    have ht : h • σ = σ := Subtype.ext hh
    have he := S.entry_permute h σ i
    rw [ht] at he
    obtain ⟨j,hj⟩ := he
    exact ⟨j,hj,True.intro⟩
  exact congrArg (fun ν : S.action.Name => ν.val)
    (S.collectName_fixed (fun i : Edges σ.raw => σ.child i.property) (fun _ _ => True)
      (MulAction.stabilizer Γ σ.val) hp g (congrArg Subtype.val hg))

/-- The actual HS candidates inside the small set of normalization codes. -/
def PowerCandidate (σ : S.Name) := {ν : S.Name // ν.raw ⊆ S.subsetBound σ}

end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_ProductForcing
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instIsConicalDirectLimitMonoidHom _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.MergerAlgebra.RightDivOrder.instPartialOrder _root_.OAI.PartitionConsistency.MergerAlgebra.Word.instIsConical _root_.OAI.PartitionConsistency.MonoidConstruction.Base.instIsConicalM _root_.OAI.PartitionConsistency.ProbeAlgebra.Word.instIsConical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency

namespace DiagramForcing.Diagram
universe u
variable {M I : Type u}

@[simp] theorem range_permute (π : Equiv.Perm I) (s : Diagram M I) :
    (s.permute π).range = π '' s.range := by
  change Set.range (π ∘ s) = π '' Set.range s
  exact Set.range_comp π s

/-- Diagram ranges have exactly the cardinality of the monoid. -/
@[simp] theorem cardinal_range (s : Diagram M I) : Cardinal.mk s.range = Cardinal.mk M :=
  (Cardinal.mk_congr (Equiv.ofInjective s s.injective)).symm

theorem permute_eq_of_fixes_range (π : Equiv.Perm I) (s : Diagram M I)
    (hfix : ∀ j ∈ s.range, π j = j) : s.permute π = s := by
  ext x
  exact hfix _ ⟨x, rfl⟩

end DiagramForcing.Diagram

namespace CohenForcing.Condition
universe u v
variable {I : Type u} {κ : Type v}

@[simp] theorem support_permute (π : Equiv.Perm I) (p : Condition I κ) :
    (p.permute π).support = π '' p.support := by
  ext j
  constructor
  · intro hj
    obtain ⟨a, b, hab⟩ := (mem_support _ _).1 hj
    exact ⟨π.symm j, (mem_support p _).2 ⟨a, b, (mem_permute _ _ _).1 hab⟩,
      π.apply_symm_apply j⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨a, b, hab⟩ := (mem_support _ _).1 hj
    exact (mem_support _ _).2 ⟨a, b, (mem_permute _ _ _).2 (by simpa using hab)⟩

theorem cardinal_support (p : Condition I κ) : Cardinal.mk p.support ≤ Cardinal.aleph0 :=
  Cardinal.le_aleph0_iff_set_countable.2 p.countable_support

/-- Fixing the root preserves the Cohen restriction literally. -/
theorem restrict_permute_of_fixes (π : Equiv.Perm I) (p : Condition I κ)
    {J : Set I} (hfix : ∀ j ∈ J, π j = j) :
    restrict (permute π p) J = restrict p J := by
  apply ext
  ext z
  simp only [mem_restrict, mem_permute]
  constructor <;> rintro ⟨hz, hJ⟩
  · have hx : π.symm z.1.1 = z.1.1 := by
      apply π.injective
      simpa using (hfix _ hJ).symm
    exact ⟨by simpa [hx] using hz, hJ⟩
  · have hx : π.symm z.1.1 = z.1.1 := by
      apply π.injective
      simpa using (hfix _ hJ).symm
    exact ⟨by simpa [hx] using hz, hJ⟩

end CohenForcing.Condition

namespace ProductForcing
universe u v
variable {M I : Type u} {κ : Type v}
open DiagramForcing

/-- The actual product of the Cohen and ground diagram posets. -/
abbrev Condition (M I : Type u) (κ : Type v) :=
  CohenForcing.Condition I κ × Diagram M I

/-- Simultaneous transport of labels in both coordinates, as in the paper. -/
def permute (π : Equiv.Perm I) (p : Condition M I κ) : Condition M I κ :=
  (p.1.permute π, p.2.permute π)

@[simp] theorem permute_one (p : Condition M I κ) : permute 1 p = p := by
  simp [permute]

@[simp] theorem permute_mul (π σ : Equiv.Perm I) (p : Condition M I κ) :
    permute (π * σ) p = permute π (permute σ p) := by
  simp [permute]

variable [LeftCancelMonoid M] [DiagramOrder.IsConical M]

def permuteOrderIso (π : Equiv.Perm I) : Condition M I κ ≃o Condition M I κ where
  toFun := permute π
  invFun := permute π⁻¹
  left_inv p := by simp [permute]
  right_inv p := by simp [permute]
  map_rel_iff' := by
    intro p q
    change (p.1.permute π ≤ q.1.permute π ∧ p.2.permute π ≤ q.2.permute π) ↔ _
    exact and_congr (CohenForcing.Condition.permuteOrderIso π).map_rel_iff
      (Diagram.permuteOrderIso π).map_rel_iff

end ProductForcing

end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_ProductNames
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instIsConicalDirectLimitMonoidHom _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.MergerAlgebra.RightDivOrder.instPartialOrder _root_.OAI.PartitionConsistency.MergerAlgebra.Word.instIsConical _root_.OAI.PartitionConsistency.MonoidConstruction.Base.instIsConicalM _root_.OAI.PartitionConsistency.ProbeAlgebra.Word.instIsConical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## ProductSystem -/

namespace PartitionConsistency.SetForcingNames
universe u v
noncomputable section

/-- A genuine small set of condition codes, obtained by wellordering the
condition type. The codes carry no forcing or satisfaction information. -/
def posetCode (P : Type u) (p : P) : ZFSet.{u} :=
  (Ordinal.typein (@WellOrderingRel P) p).toZFSet

theorem posetCode_injective (P : Type u) : Function.Injective (posetCode P) :=
  Ordinal.toZFSet_injective.comp (Ordinal.typein_injective _)

def conditionSet (P : Type u) : ZFSet.{u} := ZFSet.range (posetCode P)

def conditionEquiv (P : Type u) : P ≃ conditionSet P := Equiv.ofBijective
  (fun p => ⟨posetCode P p, ZFSet.mem_range.mpr ⟨p,rfl⟩⟩)
  ⟨fun _ _ h => posetCode_injective P (congrArg Subtype.val h),
    fun p => by
      obtain ⟨q,hq⟩ := ZFSet.mem_range.mp p.property
      exact ⟨q,Subtype.ext hq⟩⟩

namespace SymmetricSystem
variable {P : Type u} [PartialOrder P] {Γ : Type v} [Group Γ]
  (r : Γ →* (P ≃o P))

/-- Conjugating an honest order action by the coding equivalence. -/
def codedAction : ConditionAction.{u} Γ where
  conditions := conditionSet P
  perm := {
    toFun g := ((conditionEquiv P).symm.trans (r g).toEquiv).trans (conditionEquiv P)
    map_one' := by ext p; simp
    map_mul' := by intro g h; ext p; simp }

def ofOrderAction (F : Set (Subgroup Γ)) (hF : SupportFilter.IsNormalFilter F) :
    SymmetricSystem.{u} P Γ where
  action := codedAction r
  codeEquiv := conditionEquiv P
  order g p q := by
    change (conditionEquiv P).symm ((conditionEquiv P) ((r g) ((conditionEquiv P).symm ((conditionEquiv P) p)))) ≤
      (conditionEquiv P).symm ((conditionEquiv P) ((r g) ((conditionEquiv P).symm ((conditionEquiv P) q)))) ↔ _
    simp
  filter := F
  normal := hF

@[simp] theorem move_ofOrderAction (F : Set (Subgroup Γ)) (hF : SupportFilter.IsNormalFilter F)
    (g : Γ) (p : P) : (ofOrderAction r F hF).move g p = r g p := by
  change (conditionEquiv P).symm ((conditionEquiv P) ((r g) ((conditionEquiv P).symm ((conditionEquiv P) p)))) = _
  simp

@[simp] theorem code_ofOrderAction (F : Set (Subgroup Γ)) (hF : SupportFilter.IsNormalFilter F)
    (p : P) : (ofOrderAction r F hF).code p = posetCode P p := rfl

end SymmetricSystem
end
end PartitionConsistency.SetForcingNames

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]

/-- The paper explicitly allows adjoining a fixed largest condition. -/
abbrev Poset (M I κ : Type u) := WithTop (Condition M I κ)

def actionHom : Equiv.Perm I →* (Poset M I κ ≃o Poset M I κ) where
  toFun π := (permuteOrderIso π).withTopCongr
  map_one' := by
    ext p
    induction p using WithTop.recTopCoe with
    | top => rfl
    | coe p => exact congrArg WithTop.some (permute_one p)
  map_mul' π σ := by
    ext p
    induction p using WithTop.recTopCoe with
    | top => rfl
    | coe p => exact congrArg WithTop.some (permute_mul π σ p)

/-- The literal Cohen/diagram symmetric system, with exactly the small-support
subgroup filter. Neither ZF nor any target axiom is a structure field. -/
def system {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) :
    SymmetricSystem.{u} (Poset M I κ) (Equiv.Perm I) :=
  SymmetricSystem.ofOrderAction actionHom (SupportFilter.subgroupFilter μ)
    (SupportFilter.isNormalFilter hμ)

variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

@[simp] theorem move_coe (π : Equiv.Perm I) (p : Condition M I κ) :
    (system (M := M) (κ := κ) hμ).move π (p : Poset M I κ) =
      (permute π p : Poset M I κ) := by
  rw [system,SymmetricSystem.move_ofOrderAction]; rfl

@[simp] theorem move_top (π : Equiv.Perm I) :
    (system (M := M) (I := I) (κ := κ) hμ).move π ⊤ = ⊤ := by
  rw [system,SymmetricSystem.move_ofOrderAction]; rfl

end
end PartitionConsistency.ProductForcing


/-! ## Label -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w t
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

@[simp] theorem Name.smul_check (g : Γ) (x : ZFSet.{u}) :
    g • (Name.check (S := S) x) = Name.check x := by
  apply Subtype.ext
  exact ConditionAction.Name.smul_check (S.code_mem ⊤) g (S.code_top_fixed g) x

omit [OrderTop P] in
/-- Exact transport of a set-sized collected entry family. -/
theorem collectRaw_move {ι : Type t} [Small.{u} ι]
    (f f' : ι → S.Name) (R R' : ι → P → Prop) (g : Γ) (e : Equiv.Perm ι)
    (hf : ∀ i, g • f i = f' (e i))
    (hR : ∀ i p, R i p ↔ R' (e i) (S.move g p)) :
    mapConditions (S.action.actCode g) (S.collectRaw f R) = S.collectRaw f' R' := by
  apply ZFSet.ext
  intro z
  constructor
  · intro h
    obtain ⟨ν,c,he,rfl⟩ := mem_mapConditions_iff.mp h
    obtain ⟨i,p,hi,rfl,rfl⟩ := (S.edge_collectRaw f R ν c).mp he
    refine (S.mem_collectRaw f' R' _).mpr ⟨e i,S.move g p,(hR i p).mp hi,?_⟩
    rw [← hf,Name.smul_val,S.actCode_code]
  · intro h
    obtain ⟨i,p,hi,rfl⟩ := (S.mem_collectRaw f' R' _).mp h
    apply mem_mapConditions_iff.mpr
    refine ⟨(f (e.symm i)).raw,S.code ((S.move g).symm p),?_,?_⟩
    · apply (S.edge_collectRaw f R _ _).mpr
      exact ⟨e.symm i,(S.move g).symm p,(hR _ _).mpr (by simpa using hi),rfl,rfl⟩
    · rw [S.actCode_code,OrderIso.apply_symm_apply]
      have hh := congrArg Name.raw (hf (e.symm i))
      simpa only [Name.smul_val,Equiv.apply_symm_apply] using congrArg (fun a => ZFSet.pair a (S.code p)) hh

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- The Boolean assignment actually contained in a product condition. The
adjoined top condition supplies no assignment. -/
def Bit (p : Poset M I κ) (j : I) (α : κ) (b : Bool) : Prop :=
  ∃ q : Condition M I κ, p = q ∧ ((j,α),b) ∈ q.1.graph

omit [LeftCancelMonoid M] [DiagramOrder.IsConical M] in
@[simp] theorem bit_coe (p : Condition M I κ) (j : I) (α : κ) (b : Bool) :
    Bit (p : Poset M I κ) j α b ↔ ((j,α),b) ∈ p.1.graph := by
  simp only [Bit,WithTop.coe_inj]
  exact ⟨fun ⟨q,hq,h⟩ => hq ▸ h,fun h => ⟨p,rfl,h⟩⟩

omit [LeftCancelMonoid M] [DiagramOrder.IsConical M] in
@[simp] theorem not_bit_top (j : I) (α : κ) (b : Bool) :
    ¬ Bit (⊤ : Poset M I κ) j α b := by simp [Bit]

@[simp] theorem bit_move (π : Equiv.Perm I) (p : Poset M I κ)
    (j : I) (α : κ) (b : Bool) :
    Bit ((system (M := M) (I := I) (κ := κ) hμ).move π p) (π j) α b ↔ Bit p j α b := by
  induction p using WithTop.recTopCoe with
  | top => simp
  | coe p => simp [permute,CohenForcing.Condition.mem_permute]

/-- An index is coded by an actual ground set (eventually a ground ordinal).
At coordinate j the name has precisely the positively assigned indices. -/
def label (c : κ → ZFSet.{u}) (j : I) : (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system (M := M) (I := I) (κ := κ) hμ).collect (fun α : κ => Name.check (c α))
    (fun α p => Bit p j α true) (SupportFilter.Fix {j})
    ⟨{j},by simpa using (Cardinal.one_le_aleph0.trans hμ),le_rfl⟩ (by
      intro π hπ α p hp
      refine ⟨α,by simp,?_⟩
      have hj : π j = j := (SupportFilter.mem_Fix {j} π).mp hπ j (Set.mem_singleton j)
      simpa only [hj] using (bit_move hμ π p j α true).mpr hp)

@[simp] theorem label_raw (c : κ → ZFSet.{u}) (j : I) :
    (label (M := M) hμ c j).raw = (system (M := M) (I := I) (κ := κ) hμ).collectRaw
      (fun α : κ => Name.check (c α)) (fun α p => Bit p j α true) := rfl

@[simp] theorem smul_label (c : κ → ZFSet.{u}) (π : Equiv.Perm I) (j : I) :
    π • label (M := M) hμ c j = label (M := M) hμ c (π j) := by
  apply Name.ext
  rw [Name.smul_val,label_raw,label_raw]
  apply (system (M := M) (I := I) (κ := κ) hμ).collectRaw_move _ _ _ _ π (Equiv.refl κ)
  · intro α; simp
  · intro α p; exact (bit_move hμ π p j α true).symm

/-- The invariant set of all canonical generic labels. -/
def labelSet (c : κ → ZFSet.{u}) : (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system (M := M) (I := I) (κ := κ) hμ).collect (label (M := M) hμ c) (fun _ p => p = ⊤) ⊤ (system (M := M) (I := I) (κ := κ) hμ).normal.1 (by
    intro π _ j p hp
    refine ⟨π j,(smul_label (M := M) hμ c π j).symm,?_⟩
    simp only [hp,move_top])

@[simp] theorem labelSet_raw (c : κ → ZFSet.{u}) :
    (labelSet (M := M) (I := I) hμ c).raw =
      (system (M := M) (I := I) (κ := κ) hμ).collectRaw (label (M := M) hμ c) (fun _ p => p = ⊤) := rfl

@[simp] theorem smul_labelSet (c : κ → ZFSet.{u}) (π : Equiv.Perm I) :
    π • labelSet (M := M) (I := I) hμ c = labelSet (M := M) (I := I) hμ c := by
  apply Name.ext
  rw [Name.smul_val,labelSet_raw]
  apply (system (M := M) (I := I) (κ := κ) hμ).collectRaw_move _ _ _ _ π π
  · exact smul_label (M := M) hμ c π
  · intro i p
    constructor
    · rintro rfl; exact move_top hμ π
    · intro hp
      apply ((system (M := M) (I := I) (κ := κ) hμ).move π).injective
      rw [hp,move_top]

end
end PartitionConsistency.ProductForcing


/-! ## FunctionName -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Application is the forcing of the literal internal ordered-pair graph
formula. It does not replace a set function by an external function. -/
def App (p : P) (f x y : S.Name) : Prop :=
  S.Forces ![f,x,y] p (SetLanguage.edge 0 1 2)

theorem forces_edge {n} (v : Fin n → S.Name) (p : P) (f x y : Fin n) :
    S.Forces v p (SetLanguage.edge f x y) ↔ S.App p (v f) (v x) (v y) := by
  simp only [App, Forces, SetLanguage.edge, S.atomic.forceFormula_rename S.atomic_regular]
  have hv : v ∘ ![f,x,y] = ![v f,v x,v y] ∘ ![0,1,2] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]

theorem app_mono {p q : P} {f x y : S.Name} (h : q ≤ p) (ha : S.App p f x y) :
    S.App q f x y := S.atomic.forceFormula_mono h ha

theorem app_congr {p : P} {f f' x x' y y' : S.Name}
    (hf : S.atomic.EqF p f f') (hx : S.atomic.EqF p x x') (hy : S.atomic.EqF p y y') :
    S.App p f x y ↔ S.App p f' x' y' := by
  apply S.atomic.forceFormula_tuple_congr
  intro i
  fin_cases i <;> assumption

theorem app_symmetry (g : Γ) (p : P) (f x y : S.Name) :
    S.App p f x y ↔ S.App (S.move g p) (g • f) (g • x) (g • y) := by
  have h := S.forces_symmetry g (SetLanguage.edge 0 1 2) ![f,x,y] p
  simpa only [S.forces_edge,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using h

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_ChoiceFailure
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instIsConicalDirectLimitMonoidHom _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.MergerAlgebra.RightDivOrder.instPartialOrder _root_.OAI.PartitionConsistency.MergerAlgebra.Word.instIsConical _root_.OAI.PartitionConsistency.MonoidConstruction.Base.instIsConicalM _root_.OAI.PartitionConsistency.ProbeAlgebra.Word.instIsConical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## OutsideLabel -/

namespace PartitionConsistency.SupportFilter
universe u
variable {I : Type u} {J : Set I} {π : Equiv.Perm I}

theorem perm_mem_iff (hπ : π ∈ Fix J) (j : I) : π j ∈ J ↔ j ∈ J := by
  have hf := (mem_Fix J π).mp hπ
  constructor
  · intro hj
    have he : π j = j := π.injective (hf (π j) hj)
    rwa [he] at hj
  · intro hj
    rwa [hf j hj]

end PartitionConsistency.SupportFilter

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- The set of labels outside a specified small set. Every entry remains a
literal Cohen label, and its support is the specified small set. -/
def labelOutside (c : κ → ZFSet.{u}) (J : Set I) (hJ : Cardinal.mk J ≤ μ) :
    (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system (M := M) (I := I) (κ := κ) hμ).collect (label (M := M) hμ c)
    (fun j p => j ∉ J ∧ p = ⊤) (SupportFilter.Fix J) ⟨J,hJ,le_rfl⟩ (by
      intro π hπ j p hp
      refine ⟨π j,(smul_label (M := M) hμ c π j).symm,?_,?_⟩
      · exact fun h => hp.1 ((SupportFilter.perm_mem_iff hπ j).mp h)
      · simpa only [hp.2] using (move_top (M := M) (I := I) (κ := κ) hμ π))

@[simp] theorem labelOutside_raw (c : κ → ZFSet.{u}) (J : Set I) (hJ : Cardinal.mk J ≤ μ) :
    (labelOutside (M := M) hμ c J hJ).raw =
      (system (M := M) (I := I) (κ := κ) hμ).collectRaw (label (M := M) hμ c)
        (fun j p => j ∉ J ∧ p = ⊤) := rfl

end
end PartitionConsistency.ProductForcing


/-! ## Failure -/


/-! ## LocalDecision -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_DiagramPlacements
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## ProbePlacement -/

namespace PartitionConsistency.DiagramForcing.Diagram
universe u
noncomputable section
variable {M I : Type u} [LeftCancelMonoid M]

/-- Exact intersections of right cones are exactly the corresponding
intersections of ranges inside any fixed injective diagram. -/
theorem range_inter_sub (r : Diagram M I) (a b c : M)
    (h : ∀ z, a ∣ z ∧ b ∣ z ↔ c ∣ z) :
    (r.sub a).range ∩ (r.sub b).range = (r.sub c).range := by
  ext j
  constructor
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    have hxy : a * x = b * y := r.injective (hx.trans hy.symm)
    obtain ⟨z,hz⟩ := (h (a*x)).mp ⟨dvd_mul_right _ _,⟨y,hxy⟩⟩
    exact ⟨z,by simpa only [sub_apply,← hz] using hx⟩
  · rintro ⟨z,rfl⟩
    obtain ⟨⟨x,hx⟩,⟨y,hy⟩⟩ := (h (c*z)).mpr (dvd_mul_right _ _)
    exact ⟨⟨x,congrArg r hx.symm⟩,⟨y,congrArg r hy.symm⟩⟩

end
end PartitionConsistency.DiagramForcing.Diagram

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]

variable {μ : Cardinal.{u}} {K : Type u} (hμ : Cardinal.aleph0 ≤ μ)

/-- A supporting diagram also supports all names obtained by a pointwise
change of coordinates onto that diagram. -/
theorem transported_name_supported
    (s t : Diagram M I) (π : Equiv.Perm I) (hπ : s.permute π = t)
    (τ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hτ : ∀ g ∈ SupportFilter.Fix s.range, g • τ = τ) :
    ∀ g ∈ SupportFilter.Fix t.range, g • (π • τ) = π • τ := by
  have hh := SupportFilter.transport_support hτ π
  rw [← Diagram.range_permute, hπ] at hh
  exact hh

end
end PartitionConsistency.ProductForcing


/-! ## TriplePlacement -/

namespace PartitionConsistency.CohenForcing.Condition
universe u v
variable {I : Type u} {κ : Type v}

/-- Moving a condition only depends on the permutation on its support. -/
theorem permute_eq_of_agree (d : Condition I κ) (α β : Equiv.Perm I)
    (h : ∀ j ∈ d.support, α j = β j) : d.permute α = d.permute β := by
  apply ext
  apply Set.image_congr
  intro z hz
  change ((α z.1.1,z.1.2),z.2) = ((β z.1.1,z.1.2),z.2)
  rw [h _ ((mem_support d _).mpr ⟨z.1.2,z.2,hz⟩)]

/-- Compatibility with a moved condition only uses its already prescribed
part when all shared coordinates are in that part. -/
theorem compatible_permute_of_trigger (d c : Condition I κ) (π : Equiv.Perm I)
    {s v : Set I} (hd : d.support ⊆ v)
    (hov : (π '' v) ∩ c.support ⊆ π '' s) (hc : c ≤ (d.restrict s).permute π) :
    Compatible c (d.permute π) := by
  intro a b e hb he
  have hde := (mem_permute π d _).mp he
  have hv : π.symm a.1 ∈ v := hd ((mem_support d _).mpr ⟨a.2,e,hde⟩)
  have hs : a.1 ∈ π '' s := hov
    ⟨⟨π.symm a.1,hv,π.apply_symm_apply _⟩,(mem_support c _).mpr ⟨a.2,b,hb⟩⟩
  have hδ : (a,e) ∈ ((d.restrict s).permute π).graph := by
    apply (mem_permute π _ _).mpr
    exact ⟨hde,Set.mem_image_equiv.mp hs⟩
  exact c.functional a b e hb (hc hδ)

/-- Two moved copies agree on their overlap when their placements agree
pointwise there, even if their supports outside it are arbitrary. -/
theorem compatible_permutes_of_overlap (d : Condition I κ) (π ρ : Equiv.Perm I)
    {s v : Set I} (hd : d.support ⊆ v)
    (hov : (π '' v) ∩ (ρ '' v) ⊆ π '' s) (hs : ∀ j ∈ s, π j = ρ j) :
    Compatible (d.permute π) (d.permute ρ) := by
  intro a b e hb he
  have hdb := (mem_permute π d _).mp hb
  have hde := (mem_permute ρ d _).mp he
  have hvπ : π.symm a.1 ∈ v := hd ((mem_support d _).mpr ⟨a.2,b,hdb⟩)
  have hvρ : ρ.symm a.1 ∈ v := hd ((mem_support d _).mpr ⟨a.2,e,hde⟩)
  have hroot : π.symm a.1 ∈ s := Set.mem_image_equiv.mp (hov
    ⟨⟨π.symm a.1,hvπ,π.apply_symm_apply _⟩,⟨ρ.symm a.1,hvρ,ρ.apply_symm_apply _⟩⟩)
  have hi : ρ.symm a.1 = π.symm a.1 := by
    apply ρ.injective
    rw [ρ.apply_symm_apply,← hs _ hroot,π.apply_symm_apply]
  rw [hi] at hde
  exact d.functional _ b e hdb hde

theorem Compatible.union_left {c d e : Condition I κ} (hd : Compatible c d)
    (hce : Compatible c e) (hde : Compatible d e) : Compatible (c.union d hd) e := by
  intro a b k hb hk
  rcases hb with hb | hb
  · exact hce a b k hb hk
  · exact hde a b k hb hk

end PartitionConsistency.CohenForcing.Condition

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_OrbitNames
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## OrderedPair -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

@[simp] theorem Name.smul_pair (g : Γ) (σ τ : S.Name) :
    g • σ.pair τ = (g • σ).pair (g • τ) := by
  apply Subtype.ext
  exact ConditionAction.Name.smul_pair (S.code_mem ⊤) g (S.code_top_fixed g) σ.val τ.val

/-- The equivariant name for the actual Kuratowski pair. -/
def Name.opair {S : SymmetricSystem.{u} P Γ} (σ τ : S.Name) : S.Name := (σ.pair σ).pair (σ.pair τ)

@[simp] theorem Name.smul_opair (g : Γ) (σ τ : S.Name) :
    g • σ.opair τ = (g • σ).opair (g • τ) := by simp [Name.opair]

theorem eq_pair_congr {p : P} {σ σ' τ τ' : S.Name}
    (hσ : S.atomic.EqF p σ σ') (hτ : S.atomic.EqF p τ τ') :
    S.atomic.EqF p (σ.pair τ) (σ'.pair τ') := by
  apply S.eq_of_same_members
  intro ν q hqp
  rw [S.mem_pair,S.mem_pair]
  constructor
  · intro h r hrq
    obtain ⟨s,hsr,h | h⟩ := h r hrq
    · exact ⟨s,hsr,Or.inl (S.atomic.eq_trans h (S.atomic.eq_mono (hsr.trans (hrq.trans hqp)) hσ))⟩
    · exact ⟨s,hsr,Or.inr (S.atomic.eq_trans h (S.atomic.eq_mono (hsr.trans (hrq.trans hqp)) hτ))⟩
  · intro h r hrq
    obtain ⟨s,hsr,h | h⟩ := h r hrq
    · exact ⟨s,hsr,Or.inl (S.atomic.eq_trans h
        (S.atomic.eq_symm (S.atomic.eq_mono (hsr.trans (hrq.trans hqp)) hσ)))⟩
    · exact ⟨s,hsr,Or.inr (S.atomic.eq_trans h
        (S.atomic.eq_symm (S.atomic.eq_mono (hsr.trans (hrq.trans hqp)) hτ)))⟩

/-- The pure first-order unordered-pair formula agrees with the canonical name. -/
theorem forces_unorderedPair {n} (v : Fin n → S.Name) (p : P) (a x y : Fin n) :
    S.Forces v p (SetLanguage.unorderedPair a x y) ↔
      S.atomic.EqF p (v a) ((v x).pair (v y)) := by
  simp only [Forces,SetLanguage.unorderedPair,Formula.iff,
    S.atomic.forceFormula_rename S.atomic_regular,S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular,ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem,ForcingQuotient.AtomicData.forceFormula_disj,
    ForcingQuotient.AtomicData.forceFormula_equal]
  constructor
  · intro h
    apply S.eq_of_same_members
    intro ν q hqp
    rw [S.mem_pair]
    exact ⟨(h ν).1 q hqp,(h ν).2 q hqp⟩
  · intro he ν
    constructor
    · intro q hqp hm
      exact (S.mem_pair _ _ ν q).mp
        ((S.atomic.mem_congr (S.atomic.eq_refl q ν) (S.atomic.eq_mono hqp he)).mp hm)
    · intro q hqp hm
      exact (S.atomic.mem_congr (S.atomic.eq_refl q ν) (S.atomic.eq_mono hqp he)).mpr
        ((S.mem_pair _ _ ν q).mpr hm)

/-- The pure first-order Kuratowski-pair formula agrees with the canonical name. -/
theorem forces_orderedPair {n} (v : Fin n → S.Name) (p : P) (a x y : Fin n) :
    S.Forces v p (SetLanguage.orderedPair a x y) ↔
      S.atomic.EqF p (v a) ((v x).opair (v y)) := by
  simp only [Forces,SetLanguage.orderedPair,S.atomic.forceFormula_rename S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_ex,ForcingQuotient.AtomicData.forceFormula_conj,
    S.forces_unorderedPair]
  constructor
  · intro h
    apply S.atomic_regular.1
    intro q hqp
    obtain ⟨r,hrq,A,h⟩ := h q hqp
    obtain ⟨s,hsr,B,hA,hB,hp⟩ := h r le_rfl
    exact ⟨s,hsr.trans hrq,S.atomic.eq_trans hp (S.eq_pair_congr hA hB)⟩
  · intro h q hqp
    refine ⟨q,le_rfl,(v x).pair (v x),?_⟩
    intro r hrq
    exact ⟨r,le_rfl,(v x).pair (v y),S.atomic.eq_refl _ _, S.atomic.eq_refl _ _,
      S.atomic.eq_mono (hrq.trans hqp) h⟩

/-- Internal application is literal membership of the Kuratowski-pair name. -/
theorem app_iff_mem_opair (p : P) (f x y : S.Name) :
    S.App p f x y ↔ S.atomic.MemF p (x.opair y) f := by
  simp only [App,Forces,SetLanguage.edge,S.atomic.forceFormula_rename S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_ex,ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem,S.forces_orderedPair]
  constructor
  · intro h
    apply S.atomic_regular.2
    intro q hqp
    obtain ⟨r,hrq,z,hm,he⟩ := h q hqp
    exact ⟨r,hrq,(S.atomic.mem_congr he (S.atomic.eq_refl r f)).mp hm⟩
  · intro h q hqp
    exact ⟨q,le_rfl,x.opair y,S.atomic.mem_mono hqp h,S.atomic.eq_refl _ _⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## Orbit -/

namespace PartitionConsistency.CohenForcing.Condition
universe u
variable {I κ : Type u}

@[simp] theorem permute_top (π : Equiv.Perm I) :
    (⊤ : Condition I κ).permute π = ⊤ := by
  apply ext
  simp only [permute, graph_top, Set.image_empty]

end PartitionConsistency.CohenForcing.Condition

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- The invariant graph of the partial name-orbit map in
`eq:partial-orbit-map`. Each entry is activated by its actual moved diagram. -/
def orbitGraph (c : κ → ZFSet.{u})
    (σ : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Diagram M I) :
    (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system (M := M) (I := I) (κ := κ) hμ).collect
    (fun π : Equiv.Perm I => (label (M := M) hμ c (π (p 1))).opair (π • σ))
    (fun π t => t = (((⊤ : CohenForcing.Condition I κ),p.permute π) : Poset M I κ))
    ⊤ (system (M := M) (I := I) (κ := κ) hμ).normal.1 (by
      intro ρ _ π t ht
      refine ⟨ρ * π,?_,?_⟩
      · simp only [Name.smul_opair,smul_label,mul_smul]; rfl
      · rw [ht,move_coe]
        change ((CohenForcing.Condition.permute ρ (⊤ : CohenForcing.Condition I κ),(p.permute π).permute ρ) : Poset M I κ) = _
        simp only [CohenForcing.Condition.permute_top,Diagram.permute_mul])

@[simp] theorem smul_orbitGraph (c : κ → ZFSet.{u})
    (σ : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Diagram M I)
    (ρ : Equiv.Perm I) : ρ • orbitGraph hμ c σ p = orbitGraph hμ c σ p := by
  apply Subtype.ext
  apply (system (M := M) (I := I) (κ := κ) hμ).collectName_fixed _ _ ⊤ _ ρ (Subgroup.mem_top _)
  intro γ _ π t ht
  refine ⟨γ * π,?_,?_⟩
  · simp only [Name.smul_opair,smul_label,mul_smul]; rfl
  · rw [ht,move_coe]
    change ((CohenForcing.Condition.permute γ (⊤ : CohenForcing.Condition I κ),
      (p.permute π).permute γ) : Poset M I κ) = _
    simp only [CohenForcing.Condition.permute_top,Diagram.permute_mul]

end
end PartitionConsistency.ProductForcing

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_LocalQuotients
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Descent -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- Literal diagram support is inherited by stronger diagrams. -/
theorem supported_mono {p s : Diagram M I} (hsp : s ≤ p)
    (σ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hσ : ∀ g ∈ SupportFilter.Fix p.range, g • σ = σ) :
    ∀ g ∈ SupportFilter.Fix s.range, g • σ = σ := by
  intro g hg
  apply hσ
  exact (SupportFilter.mem_Fix _ _).mpr
    (fun j hj => (SupportFilter.mem_Fix _ _).mp hg j (Diagram.range_antitone hsp hj))

end
end PartitionConsistency.ProductForcing


/-! ## LocalName -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
variable (c : κ → ZFSet.{u})

/-- The ground collection X(r): all normalized subset names supported
literally by the diagram range. It is a set, rather than an unrestricted
class of HS names. -/
def LocalName (r : Diagram M I) :=
  {ν : (system (M := M) (I := I) (κ := κ) hμ).PowerCandidate (labelSet hμ c) //
    ∀ π ∈ SupportFilter.Fix r.range, π • ν.val = ν.val}

namespace LocalName
variable {hμ c}

def name {r : Diagram M I} (ν : LocalName hμ c r) :
    (system (M := M) (I := I) (κ := κ) hμ).Name := ν.val.val

theorem fixed {r : Diagram M I} (ν : LocalName hμ c r) :
    ∀ π ∈ SupportFilter.Fix r.range, π • ν.name = ν.name := ν.property

@[ext] theorem ext {r : Diagram M I} {ν τ : LocalName hμ c r}
    (h : ν.name = τ.name) : ν = τ := Subtype.ext (Subtype.ext h)

def restrict {r s : Diagram M I} (hsr : s ≤ r) (ν : LocalName hμ c r) :
    LocalName hμ c s :=
  ⟨ν.val,supported_mono hμ hsr ν.name ν.fixed⟩

@[simp] theorem restrict_name {r s : Diagram M I} (hsr : s ≤ r)
    (ν : LocalName hμ c r) : (ν.restrict hsr).name = ν.name := rfl

@[simp] theorem restrict_restrict {r s t : Diagram M I} (hsr : s ≤ r) (hts : t ≤ s)
    (ν : LocalName hμ c r) : (ν.restrict hsr).restrict hts = ν.restrict (hts.trans hsr) := rfl

end LocalName

end
end PartitionConsistency.ProductForcing


/-! ## LocalQuotient -/

namespace PartitionConsistency.ForcingQuotient
universe u
variable {P : Type u} [Preorder P]

/-- Transport of a filter along an order automorphism. It transports the
filter, not the interpretation of all names in a single fixed extension. -/
def GenericFilter.move (F : GenericFilter P) (e : P ≃o P) : GenericFilter P where
  carrier := {p | e.symm p ∈ F}
  lower' := by
    intro p q hpq hq
    exact F.lower (e.symm.monotone hpq) hq
  nonempty' := by
    obtain ⟨p,hp⟩ := F.nonempty
    refine ⟨e p,?_⟩
    change e.symm (e p) ∈ F
    exact (e.symm_apply_apply p).symm ▸ hp
  directed' := by
    intro p hp q hq
    obtain ⟨r,hr,hrp,hrq⟩ := F.directed _ hp _ hq
    refine ⟨e r,?_,?_,?_⟩
    · change e.symm (e r) ∈ F
      exact (e.symm_apply_apply r).symm ▸ hr
    · change e r ≤ p
      exact e.apply_symm_apply p ▸ e.monotone hrp
    · change e r ≤ q
      exact e.apply_symm_apply q ▸ e.monotone hrq

@[simp] theorem GenericFilter.mem_move (F : GenericFilter P) (e : P ≃o P) (p : P) :
    e p ∈ F.move e ↔ p ∈ F := by change e.symm (e p) ∈ F ↔ p ∈ F; simp

end PartitionConsistency.ForcingQuotient

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
variable {c : κ → ZFSet.{u}}

/-- Atomic forcing at a fixed ground diagram, retaining the Cohen coordinate
as the forcing parameter. Its laws follow from actual product forcing. -/
def localAtomic (r : Diagram M I) :
    AtomicData (CohenForcing.Condition I κ) (system (M := M) (I := I) (κ := κ) hμ).Name where
  EqF d σ τ := (system hμ).atomic.EqF ((d,r) : Poset M I κ) σ τ
  MemF d σ τ := (system hμ).atomic.MemF ((d,r) : Poset M I κ) σ τ
  eq_mono h := (system hμ).atomic.eq_mono (WithTop.coe_le_coe.mpr ⟨h,le_rfl⟩)
  mem_mono h := (system hμ).atomic.mem_mono (WithTop.coe_le_coe.mpr ⟨h,le_rfl⟩)
  eq_refl _ σ := (system hμ).atomic.eq_refl _ σ
  eq_symm := (system hμ).atomic.eq_symm
  eq_trans := (system hμ).atomic.eq_trans
  mem_congr := (system hμ).atomic.mem_congr

/-- The local equality relation is witnessed by a Cohen condition in F. -/
def localSetoid (F : GenericFilter (CohenForcing.Condition I κ)) (r : Diagram M I) :
    Setoid (LocalName hμ c r) where
  r σ τ := (localAtomic hμ r).EqG F σ.name τ.name
  iseqv := ⟨fun σ => (localAtomic hμ r).eqG_refl F σ.name,
    fun h => (localAtomic hμ r).eqG_symm F h,
    fun h k => (localAtomic hμ r).eqG_trans F h k⟩

/-- All local normalized subsets modulo local forced equality. The local
E-class sets used subsequently are subcollections of this actual quotient. -/
def LocalQuotient (F : GenericFilter (CohenForcing.Condition I κ)) (r : Diagram M I) :=
  Quotient (localSetoid (c := c) hμ F r)

namespace LocalQuotient
variable {hμ}
variable (F : GenericFilter (CohenForcing.Condition I κ))

def ofName {r : Diagram M I} (σ : LocalName hμ c r) : LocalQuotient (c := c) hμ F r :=
  Quotient.mk _ σ

/-- Retaining the same representative gives the restriction/inclusion map. -/
def restrict {r s : Diagram M I} (hsr : s ≤ r) :
    LocalQuotient (c := c) hμ F r → LocalQuotient (c := c) hμ F s :=
  Quotient.map (LocalName.restrict hsr) (by
    rintro σ τ ⟨d,hd,h⟩
    refine ⟨d,hd,?_⟩
    exact (system hμ).atomic.eq_mono
      (p := ((OrderDual.ofDual d,r) : Poset M I κ))
      (q := ((OrderDual.ofDual d,s) : Poset M I κ))
      (WithTop.coe_le_coe.mpr ⟨le_rfl,hsr⟩) h)

@[simp] theorem restrict_ofName {r s : Diagram M I} (hsr : s ≤ r)
    (σ : LocalName hμ c r) : restrict F hsr (ofName F σ) = ofName F (σ.restrict hsr) := rfl

@[simp] theorem restrict_refl {r : Diagram M I} (x : LocalQuotient (c := c) hμ F r) :
    restrict F le_rfl x = x := by
  induction x using Quotient.inductionOn
  rfl

@[simp] theorem restrict_restrict {r s t : Diagram M I} (hsr : s ≤ r) (hts : t ≤ s)
    (x : LocalQuotient (c := c) hμ F r) :
    restrict F hts (restrict F hsr x) = restrict F (hts.trans hsr) x := by
  induction x using Quotient.inductionOn
  rfl

end LocalQuotient

/-- Literal transport carries the entire local-name collection to the moved
diagram, including normalization and the full supporting fixer. -/
def LocalName.transport {r : Diagram M I} (π : Equiv.Perm I) (σ : LocalName hμ c r) :
    LocalName hμ c (r.permute π) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  refine ⟨⟨π • σ.name,?_⟩,?_⟩
  · have hb := mapConditions_mono (S.action.actCode π) σ.val.property
    change mapConditions (S.action.actCode π) σ.name.raw ⊆
      mapConditions (S.action.actCode π) (S.subsetBound (labelSet hμ c)) at hb
    rw [S.subsetBound_fixed _ π (smul_labelSet hμ c π)] at hb
    exact hb
  · exact transported_name_supported hμ r (r.permute π) π rfl σ.name σ.fixed

@[simp] theorem LocalName.transport_name {r : Diagram M I} (π : Equiv.Perm I)
    (σ : LocalName hμ c r) : (σ.transport hμ π).name = π • σ.name := rfl

/-- Transport of local symbolic names is between F and πF. This is not an
action on some fixed evaluated universe. -/
def LocalQuotient.transport (F : GenericFilter (CohenForcing.Condition I κ))
    (π : Equiv.Perm I) {r : Diagram M I} :
    LocalQuotient (c := c) hμ F r →
      LocalQuotient (c := c) hμ (F.move (CohenForcing.Condition.permuteOrderIso π)) (r.permute π) :=
  Quotient.map (LocalName.transport hμ π) (by
    rintro σ τ ⟨d,hd,heq⟩
    refine ⟨d.permute π,(GenericFilter.mem_move F _ d).mpr hd,?_⟩
    have hh := ((system hμ).eq_symmetry π ((OrderDual.ofDual d,r) : Poset M I κ) σ.name τ.name).mp heq
    change (system hμ).atomic.EqF
      ((CohenForcing.Condition.permute π (OrderDual.ofDual d),r.permute π) : Poset M I κ)
        (π • σ.name) (π • τ.name)
    simpa only [move_coe,permute] using hh)

end
end PartitionConsistency.ProductForcing

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_LocalRecords
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Record -/


/-! The ground record calculation for local quotients. These results count
literal witnesses of local representation by a covariant family of names.
They do not assume that every normalized subset is such a class, or assert
that every local E-class has a witness without the forcing argument. -/
namespace PartitionConsistency.CohenForcing.Condition
universe u
noncomputable section
variable {A I κ : Type u}

/-- Pull back just the coordinates in an injective diagram. -/
def pullback (d : Condition I κ) (r : A ↪ I) : Condition A κ where
  graph := (fun z : (A × κ) × Bool => ((r z.1.1,z.1.2),z.2)) ⁻¹' d.graph
  functional a b c hb hc := d.functional (r a.1,a.2) b c hb hc
  countable_graph := d.countable_graph.preimage (by
    rintro ⟨⟨a,k⟩,b⟩ ⟨⟨a',k'⟩,b'⟩ h
    have ha := r.injective (congrArg (fun z : (I × κ) × Bool => z.1.1) h)
    have hk := congrArg (fun z : (I × κ) × Bool => z.1.2) h
    have hb := congrArg (fun z : (I × κ) × Bool => z.2) h
    simp only at ha hk hb
    subst a'; subst k'; subst b'; rfl)

@[simp] theorem mem_pullback (d : Condition I κ) (r : A ↪ I) (z : (A × κ) × Bool) :
    z ∈ (d.pullback r).graph ↔ ((r z.1.1,z.1.2),z.2) ∈ d.graph := Iff.rfl

end
end PartitionConsistency.CohenForcing.Condition

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
variable {c : κ → ZFSet.{u}}

/-- The actual triple (b,x,t⁻¹d) in the local-quotient proof. -/
abbrev LocalRecord := M × M × CohenForcing.Condition M κ

/-- A local representation by the covariant family, with its literal
stronger diagram and supported Cohen condition. -/
structure LocalWitness (F : GenericFilter (CohenForcing.Condition I κ))
    (r : Diagram M I) (C : I → (system (M := M) hμ).Name) (τ : LocalName hμ c r) where
  diagram : Diagram M I
  rootIndex : M
  root : diagram.sub rootIndex = r
  labelIndex : M
  condition : CohenForcing.Condition I κ
  mem : condition ∈ F
  supported : condition.support ⊆ diagram.range
  represents : (system hμ).atomic.EqF ((condition,diagram) : Poset M I κ)
    τ.name (C (diagram labelIndex))

namespace LocalWitness
variable {hμ} {F : GenericFilter (CohenForcing.Condition I κ)} {r : Diagram M I}
variable {C : I → (system (M := M) hμ).Name}

def record {τ : LocalName hμ c r} (w : LocalWitness hμ F r C τ) :
    LocalRecord (M := M) (κ := κ) :=
  (w.rootIndex,w.labelIndex,w.condition.pullback w.diagram.toEmbedding)

end LocalWitness

end
end PartitionConsistency.ProductForcing


/-! ## Class -/


namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

theorem separate_move_le {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+1)) (g : Γ) :
    (g • S.separate σ v φ).raw ⊆ (S.separate (g • σ) (fun i => g • v i) φ).raw := by
  intro z hz
  obtain ⟨ν,a,he,rfl⟩ := mem_mapConditions_iff.mp hz
  change ZFSet.pair ν a ∈ S.collectRaw (fun i : Edges σ.raw => σ.child i.property)
    (S.separationTest σ v φ) at he
  obtain ⟨i,p,hi,rfl,rfl⟩ := (S.edge_collectRaw _ _ _ _).mp he
  obtain ⟨j,hj⟩ := S.entry_permute g σ i
  change ZFSet.pair (mapConditions (S.action.actCode g) (σ.child i.property).raw)
    (S.action.actCode g (S.code p)) ∈ S.collectRaw
      (fun j : Edges (g • σ).raw => (g • σ).child j.property)
      (S.separationTest (g • σ) (fun i => g • v i) φ)
  apply (S.mem_collectRaw _ _ _).mpr
  refine ⟨j,S.move g p,⟨?_,?_⟩,?_⟩
  · change S.atomic.MemF (S.move g p) ((g • σ).child j.property) (g • σ)
    rw [hj]
    exact (S.mem_symmetry g p _ σ).mp hi.1
  · change S.Forces (Fin.snoc (fun i => g • v i) ((g • σ).child j.property)) (S.move g p) φ
    rw [hj]
    have hv : (fun k => g • Fin.snoc v (σ.child i.property) k) =
        Fin.snoc (fun i => g • v i) (g • σ.child i.property) := by
      ext i
      refine Fin.lastCases ?_ (fun _ => ?_) i <;> simp
    simpa only [hv] using (S.forces_symmetry g φ _ p).mp hi.2
  · rw [hj,Name.smul_val,S.actCode_code]

/-- Literal covariance, not only fixedness, of the canonical Separation
name. The very same formula is used at the moved parameter tuple. -/
theorem separate_move {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+1)) (g : Γ) :
    g • S.separate σ v φ = S.separate (g • σ) (fun i => g • v i) φ := by
  apply Name.ext
  apply le_antisymm (S.separate_move_le σ v φ g)
  have hi := S.separate_move_le (g • σ) (fun i => g • v i) φ g⁻¹
  have hv : (fun i => g⁻¹ • g • v i) = v := by ext; simp
  rw [hv] at hi
  simp only [inv_smul_smul] at hi
  have hh := mapConditions_mono (S.action.actCode g) hi
  change (g • (g⁻¹ • S.separate (g • σ) (fun i => g • v i) φ)).raw ⊆
    (g • S.separate σ v φ).raw at hh
  simpa only [smul_inv_smul] using hh

/-- The canonical name for {y ∈ A | (x,y) ∈ E}.  No equivalence-relation
axiom is needed to construct this set. -/
def relationClass (A E x : S.Name) : S.Name :=
  S.separate A ![E,x] (SetLanguage.edge 0 1 2)

theorem relationClass_move (A E x : S.Name) (g : Γ) :
    g • S.relationClass A E x = S.relationClass (g • A) (g • E) (g • x) := by
  rw [relationClass,S.separate_move,relationClass]
  congr 1
  ext i
  fin_cases i <;> rfl

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.SetLanguage

/-- τ is precisely the E-class of x relative to A, expanded in pure
first-order membership syntax. Slots are τ,A,E,x. -/
def classOfFormula : Formula 4 :=
  .all ((Formula.mem 4 0).iff ((Formula.mem 4 1).conj (edge 2 3 4)))

def classOf {n} (τ A E x : Fin n) : Formula n :=
  Formula.rename ![τ,A,E,x] classOfFormula

/-- τ is the E-class of *some element of A*. Slots are τ,A,E. -/
def isClassFormula : Formula 3 :=
  .ex ((Formula.mem 3 1).conj (classOf 0 1 2 3))

def isClass {n} (τ A E : Fin n) : Formula n :=
  Formula.rename ![τ,A,E] isClassFormula

end PartitionConsistency.SetLanguage

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- The actual canonical class of a label, supported by any diagram
supporting E and containing that label's index. -/
def labelClass (E : (system (M := M) (I := I) (κ := κ) hμ).Name) (j : I) :
    (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system hμ).relationClass (labelSet hμ c) E (label hμ c j)

theorem labelClass_move (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (π : Equiv.Perm I) (j : I) :
    π • labelClass hμ c E j = labelClass hμ c (π • E) (π j) := by
  simp only [labelClass,SymmetricSystem.relationClass_move,smul_labelSet,smul_label]

end
end PartitionConsistency.ProductForcing


/-! ## Availability -/

namespace PartitionConsistency.DiagramOrder.LeftDivOrder
universe u
variable {M : Type u} [LeftCancelMonoid M] [IsConical M]

/-- Left multiplication, unlike right multiplication, preserves and reflects
left divisibility in a left-cancellative monoid. -/
theorem mul_le_mul_left_iff (n x y : LeftDivOrder M) :
    n * x ≤ n * y ↔ x ≤ y := by
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z,mul_left_cancel (by simpa only [mul_assoc] using hz)⟩
  · rintro ⟨z,rfl⟩
    exact ⟨z,mul_assoc n x z⟩

theorem le_mul_right (x y : LeftDivOrder M) : x ≤ x * y := ⟨y,rfl⟩

/-- Conditional joins commute with left multiplication. This uses the
least-upper-bound property, not a global lattice structure. -/
theorem isLUB_mul_left (n : LeftDivOrder M) {x y j : LeftDivOrder M}
    (h : IsLUB {x,y} j) : IsLUB {n*x,n*y} (n*j) := by
  have hx : x ≤ j := h.1 (by simp)
  have hy : y ≤ j := h.1 (by simp)
  constructor
  · intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact (mul_le_mul_left_iff n x j).mpr hx
    · have he : z = n*y := Set.mem_singleton_iff.mp hz
      subst z
      exact (mul_le_mul_left_iff n y j).mpr hy
  · intro z hz
    have hnx : n*x ≤ z := hz (by simp)
    have hny : n*y ≤ z := hz (by simp)
    obtain ⟨w,rfl⟩ := (le_mul_right n x).trans hnx
    exact (mul_le_mul_left_iff n j w).mpr (h.2 (by
      intro z hz
      rcases Set.mem_insert_iff.mp hz with hz | hz
      · rw [hz]
        exact (mul_le_mul_left_iff n x w).mp hnx
      · rw [Set.mem_singleton_iff.mp hz]
        exact (mul_le_mul_left_iff n y w).mp hny))

/-- The right-cone formulation of a conditional join. -/
theorem isLUB_cones {x y j : LeftDivOrder M} (h : IsLUB {x,y} j)
    (z : LeftDivOrder M) : x ≤ z ∧ y ≤ z ↔ j ≤ z := by
  constructor
  · rintro ⟨hx,hy⟩
    apply h.2
    intro w hw
    rcases Set.mem_insert_iff.mp hw with rfl | hw
    · exact hx
    · rwa [Set.mem_singleton_iff.mp hw]
  · intro hz
    exact ⟨(h.1 (by simp)).trans hz,(h.1 (by simp)).trans hz⟩

end PartitionConsistency.DiagramOrder.LeftDivOrder

namespace PartitionConsistency.DiagramForcing.Diagram
universe u
open DiagramOrder
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]

/-- Strengthening reverses containment of ranges but preserves the monoid
left-divisibility order of subdiagram indices. -/
theorem sub_mono (r : Diagram M I) {n m : LeftDivOrder M} (h : n ≤ m) :
    r.sub n ≤ r.sub m := by
  obtain ⟨z,hz⟩ := h
  exact ⟨z,(sub_sub r n z).trans (congrArg r.sub hz)⟩

theorem self_le_sub (r : Diagram M I) (n : M) : r ≤ r.sub n := ⟨n,rfl⟩

theorem range_inter_of_isLUB (r : Diagram M I) {n m k : LeftDivOrder M}
    (h : IsLUB {n,m} k) :
    (r.sub n).range ∩ (r.sub m).range = (r.sub k).range := by
  apply range_inter_sub
  intro z
  constructor
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    obtain ⟨w,hw⟩ := (LeftDivOrder.isLUB_cones h z).mp ⟨⟨x,hx.symm⟩,⟨y,hy.symm⟩⟩
    exact ⟨w,hw.symm⟩
  · rintro ⟨w,hw⟩
    obtain ⟨hx,hy⟩ := (LeftDivOrder.isLUB_cones h z).mpr ⟨w,hw.symm⟩
    obtain ⟨x,hx⟩ := hx
    obtain ⟨y,hy⟩ := hy
    exact ⟨⟨x,hx.symm⟩,⟨y,hy.symm⟩⟩

end PartitionConsistency.DiagramForcing.Diagram

namespace PartitionConsistency.LocalDiagramSystem
universe u v
open DiagramForcing DiagramOrder
variable (M I : Type u) [LeftCancelMonoid M] [IsConical M]

/-- A covariant diagram system with injective restriction and the actual
support-intersection property. This is purely diagrammatic infrastructure;
no counting, choice or partition principle is part of this definition. -/
structure System where
  Obj : Diagram M I → Type v
  restrict {r s : Diagram M I} : s ≤ r → Obj r → Obj s
  restrict_refl {r : Diagram M I} (x : Obj r) : restrict le_rfl x = x
  restrict_comp {r s t : Diagram M I} (hsr : s ≤ r) (hts : t ≤ s) (x : Obj r) :
    restrict hts (restrict hsr x) = restrict (hts.trans hsr) x
  injective {r s : Diagram M I} (hsr : s ≤ r) : Function.Injective (restrict hsr)
  intersection (p s₀ s₁ t : Diagram M I) (hs₀ : s₀ ≤ p) (hs₁ : s₁ ≤ p)
    (hinter : s₀.range ∩ s₁.range = p.range) (ht₀ : t ≤ s₀) (ht₁ : t ≤ s₁)
    (x₀ : Obj s₀) (x₁ : Obj s₁) (heq : restrict ht₀ x₀ = restrict ht₁ x₁) :
    ∃ x : Obj p, restrict hs₀ x = x₀ ∧ restrict hs₁ x = x₁

variable {M I}
namespace System
variable (D : System.{u,v} M I)

/-- Availability is existence of the same symbolic element at the specified
subdiagram. It is not an independently assigned ideal. -/
def Available (r : Diagram M I) (x : D.Obj r) (n : M) : Prop :=
  ∃ y : D.Obj (r.sub n), D.restrict (r.self_le_sub n) y = x

@[simp] theorem available_one (r : Diagram M I) (x : D.Obj r) : D.Available r x 1 := by
  have h : ∀ (s : Diagram M I) (hs : r ≤ s), s = r →
      ∃ y : D.Obj s, D.restrict hs y = x := by
    intro s hs he
    subst s
    exact ⟨x,D.restrict_refl x⟩
  exact h (r.sub 1) (r.self_le_sub 1) (r.sub_one)

/-- Retention of representatives under two successive inclusions. -/
theorem available_lower {r : Diagram M I} {x : D.Obj r}
    {n m : LeftDivOrder M} (hnm : n ≤ m) (hm : D.Available r x m) :
    D.Available r x n := by
  obtain ⟨y,hy⟩ := hm
  refine ⟨D.restrict (r.sub_mono hnm) y,?_⟩
  rw [D.restrict_comp]
  exact hy

/-- Availability at two roots descends to their exact intersection. -/
theorem available_join {r : Diagram M I} {x : D.Obj r}
    {n m k : LeftDivOrder M} (hn : D.Available r x n) (hm : D.Available r x m)
    (hjoin : IsLUB {n,m} k) : D.Available r x k := by
  obtain ⟨y,hy⟩ := hn
  obtain ⟨z,hz⟩ := hm
  have hn : n ≤ k := hjoin.1 (by simp)
  have hm : m ≤ k := hjoin.1 (by simp)
  obtain ⟨w,hw,_⟩ := D.intersection (r.sub k) (r.sub n) (r.sub m) r
    (r.sub_mono hn) (r.sub_mono hm) (r.range_inter_of_isLUB hjoin)
    (r.self_le_sub n) (r.self_le_sub m) y z (hy.trans hz.symm)
  refine ⟨w,?_⟩
  rw [← D.restrict_comp (r.sub_mono hn) (r.self_le_sub n),hw,hy]

/-- Source availability-ideal lemma, common to symbolic elements and labels.
The proof uses the already specified inclusion and intersection maps. -/
def availability (r : Diagram M I) (a : M) (x : D.Obj r) :
    ConeIdeal (show LeftDivOrder M from a) where
  carrier := {n | n ≤ a ∧ D.Available r x n}
  nonempty := ⟨1,bot_le,D.available_one r x⟩
  bounded := fun _ h => h.1
  lower := by
    intro n m hnm hm
    exact ⟨hnm.trans hm.1,D.available_lower hnm hm.2⟩
  join_closed := by
    intro n m k hn hm hk
    exact ⟨(LeftDivOrder.isLUB_cones hk a).mp ⟨hn.1,hm.1⟩,
      D.available_join hn.2 hm.2 hk⟩

@[simp] theorem mem_availability (r : Diagram M I) (a : M) (x : D.Obj r)
    (n : LeftDivOrder M) : n ∈ (D.availability r a x).carrier ↔ n ≤ a ∧ D.Available r x n :=
  Iff.rfl

end System

/-- Label ranges form the literal system underlying the label availability
ideals. Restriction is simply inclusion, not a choice of representatives. -/
def labelSystem : System.{u,u} M I where
  Obj r := r.range
  restrict hsr j := ⟨j.val,Diagram.range_antitone hsr j.property⟩
  restrict_refl _ := rfl
  restrict_comp _ _ _ := rfl
  injective := by
    intro r s hsr x y h
    exact Subtype.ext (congrArg (fun z : s.range => z.val) h)
  intersection p s₀ s₁ t hs₀ hs₁ hinter ht₀ ht₁ x₀ x₁ heq := by
    have hx : x₀.val = x₁.val := congrArg Subtype.val heq
    have hp : x₀.val ∈ p.range := by
      rw [← hinter]
      exact ⟨x₀.property,hx ▸ x₁.property⟩
    exact ⟨⟨x₀.val,hp⟩,rfl,Subtype.ext hx⟩

end PartitionConsistency.LocalDiagramSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_AvailableRecords
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Eligible -/


namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- Actual forcing eligibility, not the existence of a preselected class
representative or a coding witness. -/
def EligibleName (F : GenericFilter (CohenForcing.Condition I κ)) (r : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name) (τ : LocalName hμ c r) : Prop :=
  ∃ d : CohenForcing.Condition I κ, d ∈ F ∧ (system hμ).Forces ![τ.name,labelSet hμ c,E] ((d,r) : Poset M I κ)
    (SetLanguage.isClass 0 1 2)

theorem eligibleName_transport (F : GenericFilter (CohenForcing.Condition I κ))
    (r : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name) (τ σ : LocalName hμ c r)
    (he : (localAtomic hμ r).EqG F τ.name σ.name) :
    EligibleName hμ c F r E τ → EligibleName hμ c F r E σ := by
  rintro ⟨d,hd,hτ⟩
  obtain ⟨a,ha,he⟩ := he
  obtain ⟨b,hb,hbd,hba⟩ := F.directed _ hd _ ha
  refine ⟨b,hb,?_⟩
  have hbt : ((OrderDual.ofDual b,r) : Poset M I κ) ≤ ((OrderDual.ofDual d,r) : Poset M I κ) :=
    WithTop.coe_le_coe.mpr ⟨hbd,le_rfl⟩
  have hbe : ((OrderDual.ofDual b,r) : Poset M I κ) ≤ ((OrderDual.ofDual a,r) : Poset M I κ) :=
    WithTop.coe_le_coe.mpr ⟨hba,le_rfl⟩
  apply ((system hμ).atomic.forceFormula_tuple_congr
    (p := ((OrderDual.ofDual b,r) : Poset M I κ))
    (v := ![τ.name,labelSet hμ c,E]) (w := ![σ.name,labelSet hμ c,E])
    (φ := SetLanguage.isClass 0 1 2) ?_).mp
      ((system hμ).atomic.forceFormula_mono hbt hτ)
  intro i
  fin_cases i
  · exact (system hμ).atomic.eq_mono hbe he
  · exact (system hμ).atomic.eq_refl _ _
  · exact (system hμ).atomic.eq_refl _ _

theorem eligibleName_congr (F : GenericFilter (CohenForcing.Condition I κ))
    (r : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name) (τ σ : LocalName hμ c r)
    (he : (localAtomic hμ r).EqG F τ.name σ.name) :
    EligibleName hμ c F r E τ ↔ EligibleName hμ c F r E σ :=
  ⟨eligibleName_transport hμ c F r E τ σ he,
    eligibleName_transport hμ c F r E σ τ ((localAtomic hμ r).eqG_symm F he)⟩

/-- The class assertion descends to the actual local name quotient. -/
def Eligible (F : GenericFilter (CohenForcing.Condition I κ)) (r : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name) : LocalQuotient (c := c) hμ F r → Prop :=
  Quotient.lift (EligibleName hμ c F r E) (fun τ σ he =>
    propext (eligibleName_congr hμ c F r E τ σ he))

@[simp] theorem eligible_ofName (F : GenericFilter (CohenForcing.Condition I κ))
    (r : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name) (τ : LocalName hμ c r) :
    Eligible hμ c F r E (LocalQuotient.ofName F τ) ↔ EligibleName hμ c F r E τ := Iff.rfl

end
end PartitionConsistency.ProductForcing


/-! ## ActualAvailability -/


/-! ## Contraction -/

namespace PartitionConsistency.DiagramOrder.ConeIdeal
universe u
variable {M : Type u} [LeftCancelMonoid M] [IsConical M]

/-- An ideal can be recovered above any member by taking joins with it. -/
theorem mem_iff_mem_join {a : LeftDivOrder M} (U : ConeIdeal a)
    {n z j : LeftDivOrder M} (hn : n ∈ U.carrier) (hj : IsLUB {z,n} j) :
    z ∈ U.carrier ↔ j ∈ U.carrier :=
  ⟨fun hz => U.join_closed hz hn hj, fun hjU => U.lower (hj.1 (by simp)) hjU⟩

/-- Contraction of an actual bounded ideal, with no new choice of an ideal. -/
def contract {a : LeftDivOrder M} (U : ConeIdeal a)
    {n c : LeftDivOrder M} (hn : n ∈ U.carrier) (hnc : n*c = a) : ConeIdeal c where
  carrier := {x | n*x ∈ U.carrier}
  nonempty := ⟨1,by change n*1 ∈ U.carrier; simpa only [mul_one] using hn⟩
  bounded := by
    intro x hx
    apply (LeftDivOrder.mul_le_mul_left_iff n x c).mp
    rw [hnc]
    exact U.bounded hx
  lower := by
    intro x y hxy hy
    exact U.lower ((LeftDivOrder.mul_le_mul_left_iff n y x).mpr hxy) hy
  join_closed := by
    intro x y j hx hy hj
    exact U.join_closed hx hy (LeftDivOrder.isLUB_mul_left n hj)

@[simp] theorem mem_contract {a : LeftDivOrder M} (U : ConeIdeal a)
    {n c : LeftDivOrder M} (hn : n ∈ U.carrier) (hnc : n*c = a) (x : LeftDivOrder M) :
    x ∈ (U.contract hn hnc).carrier ↔ n*x ∈ U.carrier := Iff.rfl

/-- In a monoid with conditional joins the contraction remembers the full
ideal, provided that its contraction index belongs to that ideal. -/
theorem eq_of_contract_eq (hj : HasConditionalJoins (LeftDivOrder M))
    {a n c : LeftDivOrder M} {U V : ConeIdeal a} (hnU : n ∈ U.carrier)
    (hnV : n ∈ V.carrier) (hnc : n*c = a)
    (h : U.contract hnU hnc = V.contract hnV hnc) : U = V := by
  apply ConeIdeal.ext
  ext z
  by_cases hza : z ≤ a
  · obtain ⟨j,hj⟩ := hj z n a hza (U.bounded hnU)
    obtain ⟨x,hx⟩ := hj.1 (by simp : n ∈ ({z,n} : Set (LeftDivOrder M)))
    rw [U.mem_iff_mem_join hnU hj,V.mem_iff_mem_join hnV hj,← hx]
    exact Set.ext_iff.mp (congrArg ConeIdeal.carrier h) x
  · exact ⟨fun hz => (hza (U.bounded hz)).elim,fun hz => (hza (V.bounded hz)).elim⟩

@[simp] theorem contract_one {a : LeftDivOrder M} (U : ConeIdeal a)
    (h : (1 : LeftDivOrder M) ∈ U.carrier) : U.contract h (one_mul a) = U := by
  apply ConeIdeal.ext
  ext x
  simp only [mem_contract,one_mul]

end PartitionConsistency.DiagramOrder.ConeIdeal

namespace PartitionConsistency.LocalDiagramSystem.System
universe u v
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable (D : System.{u,v} M I)

/-- Inclusion from a fixed earlier level preserves and reflects being in
any later range. -/
theorem restrict_range_iff {r s t : Diagram M I} (hrs : r ≤ s) (hst : s ≤ t)
    (y : D.Obj s) :
    (∃ z : D.Obj t, D.restrict (hrs.trans hst) z = D.restrict hrs y) ↔
      ∃ z : D.Obj t, D.restrict hst z = y := by
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z,D.injective hrs (by rw [D.restrict_comp]; exact hz)⟩
  · rintro ⟨z,hz⟩
    exact ⟨z,by rw [← D.restrict_comp hst hrs,hz]⟩

/-- Equality of target diagrams is sufficient to compare the ranges; all
order proofs are irrelevant. -/
theorem range_congr {r s t : Diagram M I} (x : D.Obj r)
    (hrs : r ≤ s) (hrt : r ≤ t) (h : s = t) :
    (∃ y : D.Obj s, D.restrict hrs y = x) ↔
      ∃ y : D.Obj t, D.restrict hrt y = x := by
  subst t
  rfl

/-- Availability transforms by multiplication of the subdiagram indices. -/
theorem available_sub_iff (r : Diagram M I) (n m : M) (y : D.Obj (r.sub n)) :
    D.Available (r.sub n) y m ↔
      D.Available r (D.restrict (r.self_le_sub n) y) (n*m) := by
  exact (D.restrict_range_iff (r.self_le_sub n) ((r.sub n).self_le_sub m) y).symm.trans
    (D.range_congr _ _ _ (r.sub_sub n m))

/-- An included element is available at its original diagram. -/
theorem available_restrict (r : Diagram M I) (n : M) (y : D.Obj (r.sub n)) :
    D.Available r (D.restrict (r.self_le_sub n) y) n := ⟨y,rfl⟩

/-- The availability ideal at a contracted diagram is exactly the contracted
availability ideal. -/
theorem availability_sub (r : Diagram M I) (a n c : M) (hnc : n*c = a)
    (y : D.Obj (r.sub n)) :
    D.availability (r.sub n) c y =
      (D.availability r a (D.restrict (r.self_le_sub n) y)).contract
        ⟨⟨c,hnc⟩,D.available_restrict r n y⟩ hnc := by
  apply ConeIdeal.ext
  ext x
  change (x ≤ (show LeftDivOrder M from c) ∧ D.Available (r.sub n) y x) ↔
    ((show LeftDivOrder M from n)*x ≤ (show LeftDivOrder M from a) ∧
      D.Available r _ (n*(show M from x)))
  apply and_congr
  · rw [← hnc]
    exact (LeftDivOrder.mul_le_mul_left_iff n x c).symm
  · exact D.available_sub_iff r n x y

/-- Exact fibers, defined using the proved availability ideal rather than
an arbitrarily assigned classification. -/
def Fiber (r : Diagram M I) (a : M) (U : ConeIdeal (show LeftDivOrder M from a)) :=
  {x : D.Obj r // D.availability r a x = U}

end PartitionConsistency.LocalDiagramSystem.System

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_ComponentGluing
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Component -/

namespace PartitionConsistency.LocalDiagramSystem
universe u v
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]

/-- The source vertex system includes its root equation. Thus its bounded
ideal is tied to this actual diagram, not an independently selected poset. -/
structure Vertex (q : Diagram M I) where
  diagram : Diagram M I
  index : M
  root : diagram.sub index = q
  ideal : ConeIdeal (show LeftDivOrder M from index)

namespace Vertex
variable {q : Diagram M I}

/-- A contraction with its uniquely determined monoid index. -/
structure Arrow (v w : Vertex q) where
  index : M
  mem : (show LeftDivOrder M from index) ∈ v.ideal.carrier
  diagram : v.diagram.sub index = w.diagram
  ideal : ∀ x : LeftDivOrder M, x ∈ w.ideal.carrier ↔
    (show LeftDivOrder M from index)*x ∈ v.ideal.carrier

namespace Arrow
variable {v w z : Vertex q}

instance instSubsingleton : Subsingleton (Arrow v w) := ⟨by
  rintro ⟨i,hi,hdi,hUi⟩ ⟨j,hj,hdj,hUj⟩
  have h := Diagram.index_unique (hdi.trans hdj.symm)
  subst j
  rfl⟩

/-- Equality of the right factors follows from equality of the root diagrams. -/
theorem index_mul (f : Arrow v w) : f.index * w.index = v.index := by
  apply Diagram.index_unique (r := v.diagram)
  rw [← Diagram.sub_sub,f.diagram,w.root,v.root]

def id (v : Vertex q) : Arrow v v where
  index := 1
  mem := by
    obtain ⟨n,hn⟩ := v.ideal.nonempty
    exact v.ideal.lower (show (1 : LeftDivOrder M) ≤ n from bot_le) hn
  diagram := v.diagram.sub_one
  ideal := by
    intro x
    exact iff_of_eq (congrArg (fun y : LeftDivOrder M => y ∈ v.ideal.carrier)
      (one_mul x).symm)

def comp (f : Arrow v w) (g : Arrow w z) : Arrow v z where
  index := f.index*g.index
  mem := (f.ideal g.index).mp g.mem
  diagram := by rw [← Diagram.sub_sub,f.diagram,g.diagram]
  ideal := by
    intro x
    rw [g.ideal,f.ideal]
    exact iff_of_eq (congrArg (fun y => y ∈ v.ideal.carrier) (mul_assoc _ _ _).symm)

/-- If two contractions from a vertex have comparable indices, the latter
factors uniquely through the former. -/
theorem between (f : Arrow v w) (g : Arrow v z)
    (hle : (show LeftDivOrder M from f.index) ≤ g.index) : Nonempty (Arrow w z) := by
  obtain ⟨d,hd⟩ := hle
  refine ⟨⟨d,(f.ideal d).mpr ?_,?_,?_⟩⟩
  · rw [hd]
    exact g.mem
  · erw [← f.diagram,Diagram.sub_sub,hd,g.diagram]
  · intro x
    rw [f.ideal,g.ideal,← hd,mul_assoc]

end Arrow

/-- The explicit contraction vertex. The right quotient is specified only
to avoid a hidden choice; left cancellation makes it unique. -/
def contractAt (v : Vertex q) (n c : M)
    (hn : (show LeftDivOrder M from n) ∈ v.ideal.carrier) (hnc : n*c = v.index) : Vertex q where
  diagram := v.diagram.sub n
  index := c
  root := by rw [Diagram.sub_sub,hnc,v.root]
  ideal := v.ideal.contract hn hnc

def toContractAt (v : Vertex q) (n c : M)
    (hn : (show LeftDivOrder M from n) ∈ v.ideal.carrier) (hnc : n*c = v.index) :
    Arrow v (v.contractAt n c hn hnc) where
  index := n
  mem := hn
  diagram := rfl
  ideal _ := Iff.rfl

/-- Every ideal element supplies an actual contraction. -/
theorem exists_contraction (v : Vertex q) (n : M)
    (hn : (show LeftDivOrder M from n) ∈ v.ideal.carrier) :
    ∃ w : Vertex q, ∃ f : Arrow v w, f.index = n := by
  obtain ⟨c,hc⟩ := v.ideal.bounded hn
  exact ⟨v.contractAt n c hn hc,v.toContractAt n c hn hc,rfl⟩

/-- Finite directedness of successors, from conditional joins of indices. -/
theorem successors_directed (hj : HasConditionalJoins (LeftDivOrder M))
    {v w z : Vertex q} (f : Arrow v w) (g : Arrow v z) :
    ∃ t : Vertex q, Nonempty (Arrow w t) ∧ Nonempty (Arrow z t) := by
  obtain ⟨k,hk⟩ := hj f.index g.index v.index (v.ideal.bounded f.mem) (v.ideal.bounded g.mem)
  have hkU := v.ideal.join_closed f.mem g.mem hk
  obtain ⟨t,h,hh⟩ := v.exists_contraction k hkU
  subst k
  exact ⟨t,f.between h (hk.1 (Or.inl rfl)),g.between h (hk.1 (Or.inr rfl))⟩

/-- Two vertices have a common successor. Directedness will identify this
with connectedness in the undirected contraction graph. -/
def Common (v w : Vertex q) : Prop :=
  ∃ t : Vertex q, Nonempty (Arrow v t) ∧ Nonempty (Arrow w t)

namespace Common

theorem refl (v : Vertex q) : Common v v := ⟨v,⟨Arrow.id v⟩,⟨Arrow.id v⟩⟩

theorem symm {v w : Vertex q} : Common v w → Common w v := by
  rintro ⟨t,hv,hw⟩
  exact ⟨t,hw,hv⟩

theorem trans (hj : HasConditionalJoins (LeftDivOrder M))
    {v w z : Vertex q} : Common v w → Common w z → Common v z := by
  rintro ⟨a,⟨f⟩,⟨g⟩⟩ ⟨b,⟨h⟩,⟨k⟩⟩
  obtain ⟨t,⟨l⟩,⟨m⟩⟩ := successors_directed hj g h
  exact ⟨t,⟨f.comp l⟩,⟨k.comp m⟩⟩

end Common

end Vertex
end PartitionConsistency.LocalDiagramSystem


/-! ## FiberMap -/

namespace PartitionConsistency.LocalDiagramSystem.System
universe u v
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable (D : System.{u,v} M I)

/-- Coordinatized form of availability contraction, allowing an equal but
not definitionally identical target diagram. -/
theorem mem_availability_restrict (r s : Diagram M I) (a n c : M)
    (hs : r.sub n = s) (hnc : n*c = a) (y : D.Obj s) (x : LeftDivOrder M) :
    (show LeftDivOrder M from n)*x ∈
      (D.availability r a (D.restrict (show r ≤ s from ⟨n,hs⟩) y)).carrier ↔
      x ∈ (D.availability s c y).carrier := by
  subst s
  have h := Set.ext_iff.mp (congrArg ConeIdeal.carrier (D.availability_sub r a n c hnc y)) x
  exact h.symm

/-- The exact fiber at a vertex of the source's contraction graph. -/
abbrev vertexFiber {q : Diagram M I} (v : Vertex q) :=
  D.Fiber v.diagram v.index v.ideal

/-- Inclusion along an actual contraction, with its proof that exact
availability is preserved. -/
def arrowMap (hj : HasConditionalJoins (LeftDivOrder M))
    {q : Diagram M I} {v w : Vertex q} (f : v.Arrow w)
    (y : D.vertexFiber w) : D.vertexFiber v := by
  let x := D.restrict (show v.diagram ≤ w.diagram from ⟨f.index,f.diagram⟩) y.val
  have hn : (show LeftDivOrder M from f.index) ∈ (D.availability v.diagram v.index x).carrier := by
    have h := (D.mem_availability_restrict v.diagram w.diagram v.index f.index w.index
      f.diagram f.index_mul y.val 1).mpr
        (show (1 : LeftDivOrder M) ∈ (D.availability w.diagram w.index y.val).carrier from
          ⟨bot_le,D.available_one _ _⟩)
    change (show LeftDivOrder M from f.index) * (1 : LeftDivOrder M) ∈
      (D.availability v.diagram v.index
        (D.restrict (show v.diagram ≤ w.diagram from ⟨f.index,f.diagram⟩) y.val)).carrier at h
    simpa only [mul_one (show LeftDivOrder M from f.index)] using h
  refine ⟨x,ConeIdeal.eq_of_contract_eq hj hn f.mem f.index_mul ?_⟩
  apply ConeIdeal.ext
  ext z
  change (show LeftDivOrder M from f.index)*z ∈ (D.availability v.diagram v.index x).carrier ↔ _
  rw [D.mem_availability_restrict _ _ _ _ _ f.diagram f.index_mul y.val z,
    y.property,f.ideal]
  rfl

@[simp] theorem arrowMap_val (hj : HasConditionalJoins (LeftDivOrder M))
    {q : Diagram M I} {v w : Vertex q} (f : v.Arrow w) (y : D.vertexFiber w) :
    (D.arrowMap hj f y).val = D.restrict (show v.diagram ≤ w.diagram from ⟨f.index,f.diagram⟩) y.val := rfl

/-- Every contraction induces a bijection of its actual exact fibers. -/
theorem arrowMap_bijective (hj : HasConditionalJoins (LeftDivOrder M))
    {q : Diagram M I} {v w : Vertex q} (f : v.Arrow w) :
    Function.Bijective (D.arrowMap hj f) := by
  constructor
  · intro x y h
    exact Subtype.ext (D.injective ⟨f.index,f.diagram⟩ (congrArg Subtype.val h))
  · intro x
    have hn : (show LeftDivOrder M from f.index) ∈ (D.availability v.diagram v.index x.val).carrier := by
      rw [x.property]
      exact f.mem
    obtain ⟨y,hy⟩ := (D.range_congr x.val (v.diagram.self_le_sub f.index)
      (show v.diagram ≤ w.diagram from ⟨f.index,f.diagram⟩) f.diagram).mp hn.2
    refine ⟨⟨y,?_⟩,Subtype.ext hy⟩
    apply ConeIdeal.ext
    ext z
    rw [← D.mem_availability_restrict _ _ _ _ _ f.diagram f.index_mul y z,hy,x.property]
    exact (f.ideal z).symm

/-- All composition is the literal composition of inclusions. In particular
parallel chains cannot independently permute a fiber. -/
theorem arrowMap_comp (hj : HasConditionalJoins (LeftDivOrder M))
    {q : Diagram M I} {v w z : Vertex q} (f : v.Arrow w) (g : w.Arrow z)
    (x : D.vertexFiber z) : D.arrowMap hj f (D.arrowMap hj g x) = D.arrowMap hj (f.comp g) x := by
  apply Subtype.ext
  exact D.restrict_comp _ _ _

@[simp] theorem arrowMap_id (hj : HasConditionalJoins (LeftDivOrder M))
    {q : Diagram M I} (v : Vertex q) (x : D.vertexFiber v) :
    D.arrowMap hj (Vertex.Arrow.id v) x = x := by
  apply Subtype.ext
  exact D.restrict_refl _

end PartitionConsistency.LocalDiagramSystem.System


/-! ## Gluing -/

namespace PartitionConsistency.LocalDiagramSystem.System
universe u v
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable (D : System.{u,v} M I) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}

/-- The disjoint union used for gluing; its summands are the actual exact
fibers of the inclusion system. -/
abbrev Point (q : Diagram M I) := Σ w : Vertex q, D.vertexFiber w

/-- Two representatives agree when compared at a common contraction. -/
def Matches (x y : D.Point q) : Prop :=
  ∃ (w : Vertex q) (f : x.1.Arrow w) (g : y.1.Arrow w) (z : D.vertexFiber w),
    D.arrowMap hj f z = x.2 ∧ D.arrowMap hj g z = y.2

namespace Matches

protected theorem refl (x : D.Point q) : D.Matches hj x x :=
  ⟨x.1,Vertex.Arrow.id x.1,Vertex.Arrow.id x.1,x.2,D.arrowMap_id hj _ _,D.arrowMap_id hj _ _⟩

protected theorem symm {x y : D.Point q} (h : D.Matches hj x y) : D.Matches hj y x := by
  obtain ⟨w,f,g,z,hf,hg⟩ := h
  exact ⟨w,g,f,z,hg,hf⟩

/-- Transitivity uses directedness and surjectivity of the restriction maps;
no independent bijections are chosen at vertices. -/
protected theorem trans {x y z : D.Point q}
    (hxy : D.Matches hj x y) (hyz : D.Matches hj y z) : D.Matches hj x z := by
  obtain ⟨a,f,g,b,hf,hg⟩ := hxy
  obtain ⟨c,h,k,d,hh,hk⟩ := hyz
  obtain ⟨t,⟨l⟩,⟨m⟩⟩ := Vertex.successors_directed hj g h
  obtain ⟨e,he⟩ := (D.arrowMap_bijective hj l).2 b
  have hgm : g.comp l = h.comp m := Subsingleton.elim _ _
  have hd : D.arrowMap hj m e = d := by
    apply (D.arrowMap_bijective hj h).1
    rw [D.arrowMap_comp,← hgm,← D.arrowMap_comp,he,hg,hh]
  refine ⟨t,f.comp l,k.comp m,e,?_,?_⟩
  · rw [← D.arrowMap_comp,he,hf]
  · rw [← D.arrowMap_comp,hd,hk]

/-- Gluing does not make any two different members of one fiber equal. -/
theorem same (w : Vertex q) (x y : D.vertexFiber w) :
    D.Matches hj ⟨w,x⟩ ⟨w,y⟩ ↔ x = y := by
  constructor
  · rintro ⟨t,f,g,z,hf,hg⟩
    have he : f = g := Subsingleton.elim _ _
    exact hf.symm.trans (he ▸ hg)
  · rintro rfl
    exact Matches.refl D hj _

end Matches

/-- Representatives in one component, before taking the identification
quotient. The selected vertex determines a component, not an additional
edge relation or a different family of fibers. -/
abbrev ComponentPoint (root : Vertex q) := {x : D.Point q // Vertex.Common root x.1}

def gluingSetoid (root : Vertex q) : Setoid (D.ComponentPoint root) where
  r x y := D.Matches hj x.val y.val
  iseqv := ⟨fun x => Matches.refl D hj x.val,
    fun h => h.symm D hj,fun h k => h.trans D hj k⟩

/-- The source glued component. -/
def Glued (root : Vertex q) := Quotient (D.gluingSetoid hj root)

def toGlued (root w : Vertex q) (hw : Vertex.Common root w)
    (x : D.vertexFiber w) : D.Glued hj root := Quotient.mk _ ⟨⟨w,x⟩,hw⟩

/-- Inclusion of each entire fiber is injective. -/
theorem toGlued_injective (root w : Vertex q) (hw : Vertex.Common root w) :
    Function.Injective (D.toGlued hj root w hw) := by
  intro x y he
  exact (Matches.same D hj w x y).mp (Quotient.exact he)

/-- Every representative of the glued set has a unique representative in
any specified vertex fiber. -/
theorem toGlued_surjective (root w : Vertex q) (hw : Vertex.Common root w) :
    Function.Surjective (D.toGlued hj root w hw) := by
  intro z
  induction z using Quotient.inductionOn with
  | h z =>
    obtain ⟨t,⟨f⟩,⟨g⟩⟩ := hw.symm.trans hj z.property
    obtain ⟨x,hx⟩ := (D.arrowMap_bijective hj g).2 z.val.2
    refine ⟨D.arrowMap hj f x,Quotient.sound ?_⟩
    exact ⟨t,f,g,x,rfl,hx⟩

noncomputable def fiberEquivGlued (root w : Vertex q) (hw : Vertex.Common root w) :
    D.vertexFiber w ≃ D.Glued hj root :=
  Equiv.ofBijective (D.toGlued hj root w hw)
    ⟨D.toGlued_injective hj root w hw,D.toGlued_surjective hj root w hw⟩

end PartitionConsistency.LocalDiagramSystem.System

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_ConcreteSystem
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CardinalParameters -/

namespace PartitionConsistency.CardinalParameters
noncomputable section
open Cardinal

/-- Every countable sequence below a regular uncountable initial ordinal is
strictly bounded. We use the small representative of that ordinal. -/
theorem countable_bound {μ : Cardinal.{0}} (hμ : μ.IsRegular) (hω : aleph0 < μ)
    (f : ℕ → μ.ord.ToType) : ∃ a : μ.ord.ToType, ∀ n, f n < a := by
  let g : ℕ → Ordinal := fun n => (f n).toOrd.val
  have hg : (⨆ n, g n + 1) < μ.ord :=
    Ordinal.iSup_add_one_lt_of_lt_cof
      (by simpa only [Cardinal.mk_nat,hμ.cof_ord] using hω)
      (fun n => (f n).toOrd.property)
  refine ⟨Ordinal.ToType.mk ⟨_,hg⟩,fun n => ?_⟩
  apply Ordinal.ToType.mk.symm.strictMono.lt_iff_lt.mp
  change (f n).toOrd < Ordinal.ToType.mk.symm (Ordinal.ToType.mk ⟨_,hg⟩)
  rw [OrderIso.symm_apply_apply]
  exact Ordinal.lt_iSup_add_one g n

/-- The cardinal arithmetic used in the paper for a successor of a fixed
point of countable exponentiation. This is not an inaccessible assumption. -/
theorem succ_power_aleph0 {c : Cardinal.{0}} (hω : aleph0 ≤ c)
    (hc : c ^ aleph0 = c) : (Order.succ c) ^ aleph0 = Order.succ c := by
  let μ := Order.succ c
  let A := μ.ord.ToType
  have hreg : μ.IsRegular := Cardinal.isRegular_succ hω
  have hωμ : aleph0 < μ := hω.trans_lt (Order.lt_succ c)
  have hbound (f : ℕ → A) : ∃ a : A, ∀ n, f n < a := countable_bound hreg hωμ f
  let bound : (ℕ → A) → A := fun f => (hbound f).choose
  let pack : (ℕ → A) → Σ a : A, (ℕ → Set.Iio a) :=
    fun f => ⟨bound f,fun n => ⟨f n,(hbound f).choose_spec n⟩⟩
  have hpack : Function.Injective pack := by
    intro f g h
    exact congrArg (fun t : Σ a : A, (ℕ → Set.Iio a) => fun n => (t.2 n).val) h
  have hfiber (a : A) : Cardinal.mk (ℕ → Set.Iio a) ≤ c := by
    have ha : Cardinal.mk (Set.Iio a) ≤ c := by
      apply (Order.lt_succ_iff).mp
      simpa [A,μ] using Cardinal.mk_Iio_lt a (by simp [A,μ])
    simpa only [Cardinal.mk_arrow,Cardinal.mk_nat,Cardinal.lift_id,hc] using
      Cardinal.power_le_power_right (c := aleph0) ha
  apply le_antisymm _ (Cardinal.self_le_power μ Cardinal.one_le_aleph0)
  calc
    μ ^ aleph0 = Cardinal.mk (ℕ → A) := by simp [A]
    _ ≤ Cardinal.mk (Σ a : A, ℕ → Set.Iio a) := Cardinal.mk_le_of_injective hpack
    _ = Cardinal.sum (fun a : A => Cardinal.mk (ℕ → Set.Iio a)) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : A => c) := Cardinal.sum_le_sum _ _ hfiber
    _ = μ * c := by simp [A]
    _ ≤ μ * μ := mul_le_mul_right (Order.le_succ c) μ
    _ = μ := Cardinal.mul_eq_self hωμ.le

/-- The parameters of RC262 over the ambient choice ground. -/
def μ : Cardinal.{0} := Order.succ Cardinal.continuum

theorem aleph_one_le_μ : Cardinal.aleph 1 ≤ μ :=
  Cardinal.aleph_one_le_continuum.trans (Order.le_succ _)

theorem aleph0_le_μ : Cardinal.aleph0 ≤ μ :=
  Cardinal.aleph0_le_continuum.trans (Order.le_succ _)

theorem μ_countable_power : μ ^ Cardinal.aleph0 = μ :=
  succ_power_aleph0 Cardinal.aleph0_le_continuum Cardinal.continuum_power_aleph0

theorem μ_regular : μ.IsRegular := Cardinal.isRegular_succ Cardinal.aleph0_le_continuum

end
end PartitionConsistency.CardinalParameters


/-! ## Instance -/

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
noncomputable section

/-- A small type of precisely the source's probe multiplicity. -/
abbrev K : Type := μ.ord.ToType
instance instNonemptyK : Nonempty K := Ordinal.nonempty_toType_iff.mpr μ_regular.ord_pos.ne'

@[simp] theorem cardinal_K : Cardinal.mk K = μ := by
  rw [K,Cardinal.mk_toType,Cardinal.card_ord]

/-- The fully executed, omega-one-length saturation. -/
def T : Object := Saturation.target Base.object K

theorem base_cardinal_le : Cardinal.mk Base.object ≤ μ := by
  change Cardinal.mk (Multiplicative ℕ) ≤ μ
  simpa using aleph0_le_μ

@[simp] theorem cardinal_T : Cardinal.mk T = μ :=
  Saturation.target_cardinal Base.object K aleph_one_le_μ μ_countable_power
    base_cardinal_le cardinal_K

instance instInfiniteCarrierT : Infinite T := Cardinal.aleph0_le_mk_iff.mp (by rw [cardinal_T]; exact aleph0_le_μ)

theorem finiteMergers : HasFiniteMergers T := Saturation.finiteMergers Base.object K

/-- The coordinates and Cohen length specified in the source. -/
abbrev I : Type := (Order.succ μ).ord.ToType
abbrev κ : Type := (Cardinal.aleph 1).ord.ToType

@[simp] theorem cardinal_I : Cardinal.mk I = Order.succ μ := by
  rw [I,Cardinal.mk_toType,Cardinal.card_ord]

@[simp] theorem cardinal_κ : Cardinal.mk κ = Cardinal.aleph 1 := by
  rw [κ,Cardinal.mk_toType,Cardinal.card_ord]

instance instInfiniteI : Infinite I := Cardinal.aleph0_le_mk_iff.mp
  (by rw [cardinal_I]; exact aleph0_le_μ.trans (Order.le_succ μ))
instance instUncountableκ : Uncountable κ := Cardinal.aleph0_lt_mk_iff.mp
  (by rw [cardinal_κ]; exact Cardinal.aleph0_lt_aleph_one)

theorem size_lt : Cardinal.mk T < Cardinal.mk I := by
  rw [cardinal_T,cardinal_I]; exact Order.lt_succ μ

abbrev P := ProductForcing.Poset T I κ

def S : SymmetricSystem.{0} P (Equiv.Perm I) := ProductForcing.system aleph0_le_μ

end
end PartitionConsistency.ConcreteSystem


/-! ## LabelFiber -/

namespace PartitionConsistency.LocalDiagramSystem
universe u
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
noncomputable section

/-- The common ground subset of label indices underlying a component. -/
def labelFiberSet {q : Diagram M I} (w : Vertex q) : Set I :=
  Set.range (fun x : (labelSystem (M := M) (I := I)).vertexFiber w => x.val.val)

theorem labelFiberSet_arrow (hj : HasConditionalJoins (LeftDivOrder M))
    {q : Diagram M I} {w z : Vertex q} (f : w.Arrow z) :
    labelFiberSet w = labelFiberSet z := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy⟩ := ((labelSystem (M := M) (I := I)).arrowMap_bijective hj f).2 x
    exact ⟨y,congrArg (fun t => t.val.val) hy⟩
  · rintro _ ⟨x,rfl⟩
    exact ⟨(labelSystem (M := M) (I := I)).arrowMap hj f x,rfl⟩

/-- The label fibers of a whole connected component are literally the same
subset of the coordinate set, not just equinumerous sets. -/
theorem labelFiberSet_common (hj : HasConditionalJoins (LeftDivOrder M))
    {q : Diagram M I} {w z : Vertex q} (h : Vertex.Common w z) :
    labelFiberSet w = labelFiberSet z := by
  obtain ⟨t,⟨f⟩,⟨g⟩⟩ := h
  exact (labelFiberSet_arrow hj f).trans (labelFiberSet_arrow hj g).symm

end
end PartitionConsistency.LocalDiagramSystem


/-! ## Stabilizer -/

namespace PartitionConsistency.LocalDiagramSystem.Vertex
universe u
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable {q : Diagram M I}
noncomputable section

abbrev RootGroup (q : Diagram M I) := SupportFilter.Fix q.range

/-- The action fixes the chosen root diagram literally, and leaves the
monoid index and ideal unchanged. -/
def permute (π : RootGroup q) (v : Vertex q) : Vertex q where
  diagram := v.diagram.permute π.val
  index := v.index
  root := by
    rw [← Diagram.permute_sub,v.root]
    exact Diagram.permute_eq_of_fixes_range _ q ((SupportFilter.mem_Fix _ _).mp π.property)
  ideal := v.ideal

@[simp] theorem permute_one (v : Vertex q) : permute 1 v = v := by
  cases v
  simp only [permute,Subgroup.coe_one,Diagram.permute_one]

@[simp] theorem permute_mul (π σ : RootGroup q) (v : Vertex q) :
    permute (π * σ) v = permute π (permute σ v) := by
  cases v
  simp only [permute,Subgroup.coe_mul,Diagram.permute_mul]

instance instMulActionSubtypePermMemSubgroupRootGroup : MulAction (RootGroup q) (Vertex q) where
  smul := permute
  one_smul := permute_one
  mul_smul := permute_mul

@[simp] theorem smul_diagram (π : RootGroup q) (v : Vertex q) :
    (π • v).diagram = v.diagram.permute π.val := rfl
@[simp] theorem smul_index (π : RootGroup q) (v : Vertex q) : (π • v).index = v.index := rfl
@[simp] theorem smul_ideal (π : RootGroup q) (v : Vertex q) : (π • v).ideal = v.ideal := rfl

/-- Coordinate transport preserves the entire contraction, not merely a
relation between ranges. -/
def Arrow.move {v w : Vertex q} (π : RootGroup q) (f : Arrow v w) :
    Arrow (π • v) (π • w) where
  index := f.index
  mem := f.mem
  diagram := by rw [smul_diagram,smul_diagram,← Diagram.permute_sub,f.diagram]
  ideal := f.ideal

theorem Common.move {v w : Vertex q} (π : RootGroup q) (h : Common v w) :
    Common (π • v) (π • w) := by
  obtain ⟨t,⟨f⟩,⟨g⟩⟩ := h
  exact ⟨π • t,⟨f.move π⟩,⟨g.move π⟩⟩

/-- Setwise stabilizer of the component of v. `Common` is already proved
to be exactly connectedness under finite contraction zigzags. -/
def componentStabilizer (hj : HasConditionalJoins (LeftDivOrder M)) (v : Vertex q) :
    Subgroup (RootGroup q) where
  carrier := {π | Common v (π • v)}
  one_mem' := by
    change Common v (1 • v)
    simpa only [one_smul] using Common.refl v
  mul_mem' := by
    intro π σ hπ hσ
    change Common v ((π * σ) • v)
    simpa only [mul_smul] using hπ.trans hj (hσ.move π)
  inv_mem' := by
    intro π hπ
    change Common v (π⁻¹ • v)
    simpa only [inv_smul_smul] using (hπ.move π⁻¹).symm

/-- A concrete cofinal chain in a component. Its arrows contain actual
translation indices, and the initial term is the chosen vertex. -/
structure Chain (v : Vertex q) where
  vertex : ℕ → Vertex q
  first : vertex 0 = v
  increasing : ∀ i j, i ≤ j → Nonempty (Arrow (vertex i) (vertex j))
  cofinal : ∀ w, Common v w → ∃ i, Nonempty (Arrow w (vertex i))

end
end PartitionConsistency.LocalDiagramSystem.Vertex

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_QuotientTransport
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Transport -/

namespace PartitionConsistency.ForcingQuotient
universe u
variable {P : Type u} [Preorder P]

@[simp] theorem GenericFilter.move_refl (F : GenericFilter P) :
    F.move (OrderIso.refl P) = F := by
  ext p
  rfl

@[simp] theorem GenericFilter.move_trans (F : GenericFilter P) (e f : P ≃o P) :
    (F.move e).move f = F.move (e.trans f) := by
  ext p
  rfl

@[simp] theorem GenericFilter.move_symm (F : GenericFilter P) (e : P ≃o P) :
    (F.move e).move e.symm = F := by
  ext p
  change OrderDual.toDual (e.symm (e (OrderDual.ofDual p))) ∈ F ↔ p ∈ F
  rw [e.symm_apply_apply]
  rfl

end PartitionConsistency.ForcingQuotient

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- Equal supporting diagrams can be identified without changing any name
code. This explicit version has a definitionally unchanged underlying name. -/
def LocalName.rebase {r s : Diagram M I} (hrs : r = s) (σ : LocalName hμ c r) :
    LocalName hμ c s := ⟨σ.val,by rw [← hrs]; exact σ.property⟩

@[simp] theorem LocalName.rebase_name {r s : Diagram M I} (hrs : r = s)
    (σ : LocalName hμ c r) : (σ.rebase hμ c hrs).name = σ.name := rfl

variable {c hμ}

namespace LocalQuotient
variable (F : GenericFilter (CohenForcing.Condition I κ))

@[simp] theorem transport_ofName (π : Equiv.Perm I) {r : Diagram M I}
    (σ : LocalName hμ c r) :
    transport hμ F π (ofName F σ) =
      ofName (F.move (CohenForcing.Condition.permuteOrderIso π)) (σ.transport hμ π) := rfl

/-- Coordinate transport commutes literally with restriction of symbolic
names. This is the naturality needed for contraction and gluing. -/
@[simp] theorem transport_restrict (π : Equiv.Perm I) {r s : Diagram M I} (hsr : s ≤ r)
    (x : LocalQuotient (c := c) hμ F r) :
    transport hμ F π (restrict F hsr x) =
      restrict (F.move (CohenForcing.Condition.permuteOrderIso π))
        ((Diagram.permuteOrderIso π).monotone hsr) (transport hμ F π x) := by
  induction x using Quotient.inductionOn
  rfl

end LocalQuotient

end
end PartitionConsistency.ProductForcing


/-! ## SystemTransport -/

/-!
Naturality of the exact fibers and the glued component under relabeling.
These are assertions about the genuine local quotient systems, not choices
of fiber bijections. In the application the source and target generics differ.
-/
namespace PartitionConsistency.LocalDiagramSystem
universe u v w
open DiagramForcing DiagramOrder
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]

/-- A reindexing isomorphism of diagram systems. The compatibility square
uses the already-defined literal restriction maps. -/
structure ReindexIso (D : System.{u,v} M I) (E : System.{u,w} M I) (π : Equiv.Perm I) where
  app (r : Diagram M I) : D.Obj r ≃ E.Obj (r.permute π)
  natural {r s : Diagram M I} (hsr : s ≤ r) (x : D.Obj r) :
    app s (D.restrict hsr x) = E.restrict ((Diagram.permuteOrderIso π).monotone hsr) (app r x)

namespace ReindexIso
variable {D : System.{u,v} M I} {E : System.{u,w} M I} {π : Equiv.Perm I}
variable (T : ReindexIso D E π)

/-- An available local element remains available at exactly the same monoid
positions after both its diagram and its name are transported. -/
theorem available_iff (r : Diagram M I) (x : D.Obj r) (n : M) :
    E.Available (r.permute π) (T.app r x) n ↔ D.Available r x n := by
  have hsub := (Diagram.permuteOrderIso π).monotone (r.self_le_sub n)
  have hranges := E.range_congr (T.app r x) hsub ((r.permute π).self_le_sub n)
    (Diagram.permute_sub π r n)
  constructor
  · intro h
    have h' : ∃ y : E.Obj ((r.sub n).permute π), E.restrict hsub y = T.app r x := by
      exact hranges.mpr h
    obtain ⟨y,hy⟩ := h'
    obtain ⟨z,rfl⟩ := (T.app (r.sub n)).surjective y
    refine ⟨z,(T.app r).injective ?_⟩
    rw [T.natural]
    exact hy
  · rintro ⟨y,hy⟩
    have h' : ∃ z : E.Obj ((r.sub n).permute π), E.restrict hsub z = T.app r x :=
      ⟨T.app (r.sub n) y, (T.natural (r.self_le_sub n) y).symm.trans (congrArg (T.app r) hy)⟩
    exact hranges.mp h'

/-- Thus the entire availability ideal, not only an individual cofinal
sequence, is literally unchanged as a subset of the monoid cone. -/
theorem availability (r : Diagram M I) (a : M) (x : D.Obj r) :
    E.availability (r.permute π) a (T.app r x) = D.availability r a x := by
  apply ConeIdeal.ext
  ext n
  exact and_congr Iff.rfl (T.available_iff r x n)

variable {q : Diagram M I} (g : Vertex.RootGroup q)
variable (T : ReindexIso D E g.val)

/-- Isomorphism of the actual exact fibers at moved vertices. -/
def fiberEquiv (a : Vertex q) : D.vertexFiber a ≃ E.vertexFiber (g • a) :=
  (T.app a.diagram).subtypeEquiv (fun x => by
    change D.availability a.diagram a.index x = a.ideal ↔
      E.availability (a.diagram.permute g.val) a.index (T.app a.diagram x) = a.ideal
    rw [T.availability])

@[simp] theorem fiberEquiv_val (a : Vertex q) (x : D.vertexFiber a) :
    (T.fiberEquiv g a x).val = T.app a.diagram x.val := rfl

/-- A component equivalence obtained through a root fiber. The independent
proof below shows that it agrees with transport at every other vertex. -/
noncomputable def gluedEquiv (hj : HasConditionalJoins (LeftDivOrder M)) (a : Vertex q) :
    D.Glued hj a ≃ E.Glued hj (g • a) :=
  (D.fiberEquivGlued hj a a (Vertex.Common.refl a)).symm.trans
    ((T.fiberEquiv g a).trans
      (E.fiberEquivGlued hj (g • a) (g • a) (Vertex.Common.refl (g • a))))

@[simp] theorem gluedEquiv_root (hj : HasConditionalJoins (LeftDivOrder M))
    (a : Vertex q) (x : D.vertexFiber a) :
    T.gluedEquiv g hj a (D.toGlued hj a a (Vertex.Common.refl a) x) =
      E.toGlued hj (g • a) (g • a) (Vertex.Common.refl (g • a)) (T.fiberEquiv g a x) := by
  change E.toGlued hj (g • a) (g • a) (Vertex.Common.refl (g • a))
    (T.fiberEquiv g a ((D.fiberEquivGlued hj a a (Vertex.Common.refl a)).symm
      ((D.fiberEquivGlued hj a a (Vertex.Common.refl a)) x))) = _
  rw [Equiv.symm_apply_apply]

end ReindexIso
end PartitionConsistency.LocalDiagramSystem


/-! ## ComponentRebase -/

/-! Canonical change of the chosen root of a glued component.  These maps
retain each representative literally and have no auxiliary choices. -/
namespace PartitionConsistency.LocalDiagramSystem.System
universe u v
open DiagramForcing DiagramOrder
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable (D : System.{u,v} M I) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}

/-- Changing the root inside its component changes only the proof that a
representative belongs to the component. -/
def rebaseGlued {a b : Vertex q} (hab : Vertex.Common a b) :
    D.Glued hj a ≃ D.Glued hj b where
  toFun := Quotient.map (fun x => ⟨x.val,hab.symm.trans hj x.property⟩)
    (fun _ _ h => h)
  invFun := Quotient.map (fun x => ⟨x.val,hab.trans hj x.property⟩)
    (fun _ _ h => h)
  left_inv := by intro x; induction x using Quotient.inductionOn; rfl
  right_inv := by intro x; induction x using Quotient.inductionOn; rfl

@[simp] theorem rebaseGlued_toGlued {a b : Vertex q} (hab : Vertex.Common a b)
    (w : Vertex q) (hw : Vertex.Common a w) (x : D.vertexFiber w) :
    D.rebaseGlued hj hab (D.toGlued hj a w hw x) =
      D.toGlued hj b w (hab.symm.trans hj hw) x := rfl

@[simp] theorem rebaseGlued_refl (a : Vertex q) (x : D.Glued hj a) :
    D.rebaseGlued hj (Vertex.Common.refl a) x = x := by
  induction x using Quotient.inductionOn
  rfl

@[simp] theorem rebaseGlued_trans {a b c : Vertex q}
    (hab : Vertex.Common a b) (hbc : Vertex.Common b c) (x : D.Glued hj a) :
    D.rebaseGlued hj hbc (D.rebaseGlued hj hab x) =
      D.rebaseGlued hj (hab.trans hj hbc) x := by
  induction x using Quotient.inductionOn
  rfl

end PartitionConsistency.LocalDiagramSystem.System

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_TailGraphs
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## TailCode -/

/-! Codes for actual symbolic classes along a component chain.  The
representing relation ignores a finite prefix and is covariant under each
eventual pointwise fixer, with the *same* code at the moved Cohen filter. -/


/-! ## Graph -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Literal children suffice to name the Cartesian product of two sets, at
arbitrary ranks. The activation test retains both membership values. -/
abbrev ProductEntries (X Y : S.Name) := Edges X.raw × Edges Y.raw

def productEntry (X Y : S.Name) (i : S.ProductEntries X Y) : S.Name :=
  (X.child i.1.property).opair (Y.child i.2.property)

def productTest (X Y : S.Name) (i : S.ProductEntries X Y) (p : P) : Prop :=
  S.atomic.MemF p (X.child i.1.property) X ∧ S.atomic.MemF p (Y.child i.2.property) Y

/-- A regular, equality-respecting binary forcing relation. This auxiliary
structure is used to construct an actual bounded set graph by collection;
it is not an assumed function or an assumed semantic model. -/
structure BinaryRelation where
  holds : P → S.Name → S.Name → Prop
  mono : ∀ {p q x y}, q ≤ p → holds p x y → holds q x y
  regular : ∀ {p x y}, (∀ q, q ≤ p → ∃ r, r ≤ q ∧ holds r x y) → holds p x y
  congr : ∀ {p x x' y y'}, S.atomic.EqF p x x' → S.atomic.EqF p y y' →
    (holds p x y ↔ holds p x' y')

namespace BinaryRelation
variable {S} (R : S.BinaryRelation)
variable (X Y : S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
variable (hX : ∀ g ∈ H, g • X = X) (hY : ∀ g ∈ H, g • Y = Y)
variable (hR : ∀ g ∈ H, ∀ p x y, R.holds p x y → R.holds (S.move g p) (g • x) (g • y))

def test (i : S.ProductEntries X Y) (p : P) : Prop :=
  S.productTest X Y i p ∧ R.holds p (X.child i.1.property) (Y.child i.2.property)

include hX hY hR in
theorem test_permute : ∀ g ∈ H, ∀ i p, R.test X Y i p →
    ∃ j, S.productEntry X Y j = g • S.productEntry X Y i ∧
      R.test X Y j (S.move g p) := by
  intro g hg i p hi
  have hex := S.entry_permute g X i.1
  have hey := S.entry_permute g Y i.2
  rw [hX g hg] at hex
  rw [hY g hg] at hey
  obtain ⟨j,hj⟩ := hex
  obtain ⟨k,hk⟩ := hey
  refine ⟨(j,k),?_,⟨?_,?_⟩,?_⟩
  · simp only [productEntry,Name.smul_opair,hj,hk]
  · change S.atomic.MemF (S.move g p) (X.child j.property) X
    rw [hj]
    simpa only [hX g hg] using (S.mem_symmetry g p _ X).mp hi.1.1
  · change S.atomic.MemF (S.move g p) (Y.child k.property) Y
    rw [hk]
    simpa only [hY g hg] using (S.mem_symmetry g p _ Y).mp hi.1.2
  · change R.holds (S.move g p) (X.child j.property) (Y.child k.property)
    rw [hj,hk]
    exact hR g hg p _ _ hi.2

/-- The actual HS name for the bounded relation on `X × Y`. -/
def graph : S.Name :=
  S.collect (S.productEntry X Y) (R.test X Y) H hH (R.test_permute X Y H hX hY hR)

theorem graph_fixed (g : Γ) (hg : g ∈ H) :
    g • R.graph X Y H hH hX hY hR = R.graph X Y H hH hX hY hR :=
  Subtype.ext (S.collectName_fixed _ _ H (R.test_permute X Y H hX hY hR) g hg)

end BinaryRelation
end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_GraphFusion
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## IndexedGraph -/


/-! ## CheckGraph -/

/-! Literal ground graphs and their check names.  These lemmas keep the
internal set-function formula, including its no-junk-entries conjunct. -/


/-! ## Fusion -/

/-! Countable ground-sequence preservation by fusion at a fixed supporting
root. The diagram forcing is not asserted to be countably closed. -/


/-! ## StableIdeal -/

/-! Dense stabilization of the actual availability ideals. This is a
condition-by-condition form of the countable-closure argument: it involves
no filter asserted to meet an unbounded collection of ambient dense sets. -/

namespace PartitionConsistency.ForcingQuotient
universe u
variable {P : Type u} [Preorder P]

/-- The directed filter generated by one condition; it is NOT called generic
and no meeting property is attributed to it. -/
def principalFilter (p : P) : GenericFilter P where
  carrier := {q | p ≤ q}
  lower' := fun _ _ h hp => hp.trans h
  nonempty' := ⟨p,le_rfl⟩
  directed' := fun _ hq _ hr => ⟨p,le_rfl,hq,hr⟩

@[simp] theorem mem_principalFilter (p q : P) : q ∈ principalFilter p ↔ p ≤ q := Iff.rfl

end PartitionConsistency.ForcingQuotient


/-! ## StableAvailability -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_PersistentCodes
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CodeSelection -/

/-! Least-code selection at the level of forcing conditions. No generic
filter, regular ultrafilter, or selection of values in another universe is
assumed. The equivalence relation has a monotone truth value, and working
codes persist under refinement. -/
namespace PartitionConsistency.ConditionCodeSelection
universe u v
noncomputable section
variable {P : Type u} [Preorder P] {A : Type v}
variable (W : P → A → Prop) (E : P → A → A → Prop)

/-- A working code and the assertion that no smaller code can ever become a
working representative of the same value. -/
def Selected (a : A) (p : P) : Prop :=
  W p a ∧ ∀ q, q ≤ p → ∀ b, WellOrderingRel b a → ¬ (W q b ∧ E q a b)

variable (wmono : ∀ {p q a}, q ≤ p → W p a → W q a)
variable (emono : ∀ {p q a b}, q ≤ p → E p a b → E q a b)
variable (erefl : ∀ p a, E p a a)
variable (esymm : ∀ {p a b}, E p a b → E p b a)
variable (etrans : ∀ {p a b c}, E p a b → E p b c → E p a c)

/-- A coordinate transformation acts on conditions but leaves each ground
code in place (the same-code covariance of the source). It therefore also
preserves the persistent least-code predicate. -/
theorem selected_covariance (e : P ≃o P)
    (hw : ∀ p a, W (e p) a ↔ W p a)
    (he : ∀ p a b, E (e p) a b ↔ E p a b) (a : A) (p : P) :
    Selected W E a (e p) ↔ Selected W E a p := by
  constructor
  · rintro ⟨ha,hb⟩
    refine ⟨(hw p a).mp ha,fun q hqp b hba h => ?_⟩
    exact hb (e q) (e.monotone hqp) b hba
      ⟨(hw q b).mpr h.1,(he q a b).mpr h.2⟩
  · rintro ⟨ha,hb⟩
    refine ⟨(hw p a).mpr ha,fun q hqp b hba h => ?_⟩
    have hqp' : e.symm q ≤ p := by simpa only [e.symm_apply_apply] using e.symm.monotone hqp
    exact hb (e.symm q) hqp' b hba
      ⟨(hw (e.symm q) b).mp (by simpa only [e.apply_symm_apply] using h.1),
       (he (e.symm q) a b).mp (by simpa only [e.apply_symm_apply] using h.2)⟩

end
end PartitionConsistency.ConditionCodeSelection


/-! ## PrincipalCode -/

/-! The least-code construction without an ambient fully generic filter.
The names and glued quotient values are the actual ones from the local
symbolic system. The principal filter at a condition is used only as a
convenient quotient notation for equality forced by that condition. -/
namespace PartitionConsistency.ForcingQuotient
universe u
variable {P : Type u} [Preorder P]

@[simp] theorem principalFilter_move (p : P) (e : P ≃o P) :
    (principalFilter p).move e = principalFilter (e p) := by
  apply Order.Ideal.ext
  ext q
  change (p ≤ e.symm q) ↔ (e p ≤ q)
  exact (e.to_galoisConnection _ _).symm

end PartitionConsistency.ForcingQuotient


/-! ## PersistentCode -/

/-! Stable availability gives actual working ground codes, persistently at
every refinement. This supplies the density input for least-code ranks,
without a countable family of external fully generic filters. -/


/-! ## OrdinalName -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_OrdinalCodes
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## OrdinalSelection -/

/-! A wellordered subset selected by forcing conditions has an actual
ordinal name for its order type and names for the ranks of its elements.
This construction uses ordinary set names, not evaluated ambient generics.
The pointwise invariance of each selection predicate gives literal fixation
of every rank name. -/


/-! ## SelectedRank -/


/-! ## CohenSelection -/

/-! The ordinal coding of a condition-defined wellorder can be carried out
inside the product symmetric system itself. Its rank names have the given
tail support. Reflection to a supporting diagram permits all ordinal
decisions to be made by strengthening just the Cohen coordinate. -/
namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
variable [Infinite M] [Infinite I]
variable (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
include hsize hmerger

omit hsize hmerger

namespace CohenSelection
variable {X : Type u} [LinearOrder X] [IsWellOrder X (· < ·)]
variable (R : X → CohenForcing.Condition I κ → Prop)
variable (H : Subgroup (Equiv.Perm I)) (hH : H ∈ (system (M := M) (I := I) (κ := κ) hμ).filter)
variable (hR : ∀ π ∈ H, ∀ a d, R a d → R a (d.permute π))

/-- Only the Cohen coordinate is examined. No diagram-generic or ambient
fully generic filter occurs in this predicate. -/
def lift (a : X) (p : Poset M I κ) : Prop :=
  ∃ (d : CohenForcing.Condition I κ) (r : Diagram M I), p = ((d,r) : Poset M I κ) ∧ R a d

omit [LeftCancelMonoid M] [DiagramOrder.IsConical M] [Infinite M] [Infinite I]
  [IsWellOrder X (· < ·)] [LinearOrder X] in
@[simp] theorem lift_coe (a : X) (d : CohenForcing.Condition I κ) (r : Diagram M I) :
    lift (M := M) R a ((d,r) : Poset M I κ) ↔ R a d := by
  constructor
  · rintro ⟨e,s,he,ha⟩
    have hh : (d,r) = (e,s) := WithTop.coe_injective he
    have hde : d = e := congrArg Prod.fst hh
    exact hde.symm ▸ ha
  · exact fun h => ⟨d,r,rfl,h⟩

end CohenSelection
end
end PartitionConsistency.ProductForcing


/-! ## CodeRoot -/

/-! Connecting the persistent ground codes to literal root-supported names.
The comparison of two codes is equivalent to forced equality of any of their
root representatives. No generic evaluator is presumed in this step. -/


/-! ## OrderAssignment -/

/-! Enumeration using one fixed, bounded table of bijections with ordinals.
This is the order-theoretic part of the preliminary component assignment.
The table is chosen once and never depends on the wellordered set being
enumerated. -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_RelationCalculus
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## RelationTools -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

namespace BinaryRelation
variable {S} (R : S.BinaryRelation)

/-- Bounds are included in the relation when proving uniqueness, so no
functional behavior outside the specified sets is required. -/
def bounded (X Y : S.Name) : S.BinaryRelation where
  holds p x y := S.atomic.MemF p x X ∧ S.atomic.MemF p y Y ∧ R.holds p x y
  mono h hh := ⟨S.atomic.mem_mono h hh.1,S.atomic.mem_mono h hh.2.1,R.mono h hh.2.2⟩
  regular h := ⟨S.atomic_regular.2 _ _ _ (fun q hq => (h q hq).imp
      (fun _ hr => ⟨hr.1,hr.2.1⟩)),S.atomic_regular.2 _ _ _ (fun q hq => (h q hq).imp
      (fun _ hr => ⟨hr.1,hr.2.2.1⟩)),R.regular (fun q hq => (h q hq).imp
      (fun _ hr => ⟨hr.1,hr.2.2.2⟩))⟩
  congr hx hy := and_congr (S.atomic.mem_congr hx (S.atomic.eq_refl _ _))
    (and_congr (S.atomic.mem_congr hy (S.atomic.eq_refl _ _)) (R.congr hx hy))

def inverse : S.BinaryRelation where
  holds p x y := R.holds p y x
  mono := R.mono
  regular := R.regular
  congr hx hy := R.congr hy hx

/-- Composition is the regular existential relation, not an external
composition of selected evaluations. -/
def comp (Q : S.BinaryRelation) : S.BinaryRelation where
  holds p x z := ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ y : S.Name, R.holds r x y ∧ Q.holds r y z
  mono h hh q hq := hh q (hq.trans h)
  regular h q hq := by
    obtain ⟨r,hrq,hh⟩ := h q hq
    obtain ⟨s,hsr,y,hy⟩ := hh r le_rfl
    exact ⟨s,hsr.trans hrq,y,hy⟩
  congr := by
    intro p x x' z z' hx hz
    have step {x x' z z' : S.Name} (hx : S.atomic.EqF p x x') (hz : S.atomic.EqF p z z')
        (hh : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ y : S.Name, R.holds r x y ∧ Q.holds r y z) :
        ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ y : S.Name, R.holds r x' y ∧ Q.holds r y z' := by
      intro q hq
      obtain ⟨r,hrq,y,hy,hz'⟩ := hh q hq
      exact ⟨r,hrq,y,(R.congr (S.atomic.eq_mono (hrq.trans hq) hx) (S.atomic.eq_refl r y)).mp hy,
        (Q.congr (S.atomic.eq_refl r y) (S.atomic.eq_mono (hrq.trans hq) hz)).mp hz'⟩
    exact ⟨step hx hz,step (S.atomic.eq_symm hx) (S.atomic.eq_symm hz)⟩

end BinaryRelation

/-- The application relation of a particular graph name. -/
def appRelation (f : S.Name) : S.BinaryRelation where
  holds p x y := S.App p f x y
  mono := S.app_mono
  regular := by
    intro p x y h
    rw [S.app_iff_mem_opair]
    exact S.atomic_regular.2 _ _ _ (fun q hq => (h q hq).imp
      (fun r hr => ⟨hr.1,(S.app_iff_mem_opair _ _ _ _).mp hr.2⟩))
  congr hx hy := S.app_congr (S.atomic.eq_refl _ _) hx hy

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## MapCalculus -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

def boundedApp (f X Y : S.Name) : S.BinaryRelation := (S.appRelation f).bounded X Y

theorem boundedApp_move (f X Y : S.Name) (g : Γ)
    (hf : g • f = f) (hX : g • X = X) (hY : g • Y = Y)
    (p : P) (x y : S.Name) (h : (S.boundedApp f X Y).holds p x y) :
    (S.boundedApp f X Y).holds (S.move g p) (g • x) (g • y) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [hX] using (S.mem_symmetry g p x X).mp h.1
  · simpa only [hY] using (S.mem_symmetry g p y Y).mp h.2.1
  · change S.App (S.move g p) f (g • x) (g • y)
    simpa only [hf] using (S.app_symmetry g p f x y).mp h.2.2

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_OrdinalPresentation
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Completion -/


/-! ## Presentation -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- All literal member names of `X` together with all their supporting
diagrams. No rank bound is placed on `X` or on its descendants. -/
def PresentationIndex (X : (system (M := M) (I := I) (κ := κ) hμ).Name) :=
  {ip : Edges X.raw × Diagram M I //
    ∀ g ∈ SupportFilter.Fix ip.2.range, g • X.child ip.1.property = X.child ip.1.property}

/-- The partial function associated to a presentation record is a literal
orbit graph, not a selected representative in an evaluated universe. -/
def presentationPartial (c : κ → ZFSet.{u})
    (X : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (i : PresentationIndex hμ X) : (system (M := M) (I := I) (κ := κ) hμ).Name :=
  orbitGraph hμ c (X.child i.val.1.property) i.val.2

@[simp] theorem smul_presentationPartial (c : κ → ZFSet.{u})
    (X : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (i : PresentationIndex hμ X) (π : Equiv.Perm I) :
    π • presentationPartial hμ c X i = presentationPartial hμ c X i :=
  smul_orbitGraph hμ c _ _ π

end
end PartitionConsistency.ProductForcing

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_ClassFibers
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## LocalList -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- The range of all canonical E-classes of labels. For an equivalence
relation this is A/E, with the actual classes as its members. -/
def quotientName (E : (system (M := M) (I := I) (κ := κ) hμ).Name) :
    (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system hμ).collect (labelClass hμ c E) (fun _ _ => True)
    ((system hμ).tupleStabilizer ![E]) ((system hμ).tupleStabilizer_mem ![E]) (by
      intro π hπ j p hp
      refine ⟨π j,?_,trivial⟩
      have he : π • E = E := ((system hμ).mem_tupleStabilizer ![E] π).mp hπ 0
      rw [labelClass_move,he])

theorem quotientName_fixed (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (π : Equiv.Perm I) (he : π • E = E) :
    π • quotientName hμ c E = quotientName hμ c E := by
  apply Subtype.ext
  refine (system hμ).collectName_fixed _ _ ((system hμ).tupleStabilizer ![E]) ?_ π ?_
  · intro σ hσ j p hp
    refine ⟨σ j,?_,trivial⟩
    have hs : σ • E = E := ((system hμ).mem_tupleStabilizer ![E] σ).mp hσ 0
    rw [labelClass_move,hs]
  · apply ((system hμ).mem_tupleStabilizer ![E] π).mpr
    intro j
    fin_cases j
    exact he

end
end PartitionConsistency.ProductForcing


/-! ## OutsideClass -/


/-! ## ClassFiber -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_OrdinalChoice
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Antichain -/


/-! ## Maximum -/


/-! ## ChoiceFamily -/


/-! ## ACwo -/

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
noncomputable section

instance instUncountableK : Uncountable K := Cardinal.aleph0_lt_mk_iff.mp
  (by rw [cardinal_K]; exact Cardinal.aleph0_lt_aleph_one.trans_le aleph_one_le_μ)

end
end PartitionConsistency.ConcreteSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_QuotientActions
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## SaturatedFibers -/


/-! ## Preliminary -/

/-! A preliminary assignment on the genuine symbolic component with tail
covariance. Exact cardinality at an intermediate filter is an explicit
input here; the issued dense requirements needed to obtain it are in
`SaturatedFibersWork`. No existence of a filter generic over every ambient
set is assumed or asserted. -/


/-! ## ComponentAction -/

/-! The actual symbolic fibers carry transport between moved Cohen filters.
On the total space this is a genuine group action. The individual interpreted
universes are not being treated as if they carried this action internally. -/
namespace PartitionConsistency.ForcingQuotient
universe u
open CohenForcing
variable {I κ : Type u}

instance instMulActionPermGenericFilterCondition : MulAction (Equiv.Perm I) (GenericFilter (Condition I κ)) where
  smul π F := F.move (Condition.permuteOrderIso π)
  one_smul F := by
    ext p
    change (OrderDual.ofDual p).permute ((1 : Equiv.Perm I)⁻¹) ∈ F ↔ p ∈ F
    rw [inv_one,Condition.permute_one]
    rfl
  mul_smul π σ F := by
    ext p
    change (OrderDual.ofDual p).permute ((π*σ)⁻¹) ∈ F ↔
      ((OrderDual.ofDual p).permute π⁻¹).permute σ⁻¹ ∈ F
    rw [mul_inv_rev,Condition.permute_mul]

@[simp] theorem smul_filter (π : Equiv.Perm I) (F : GenericFilter (Condition I κ)) :
    π • F = F.move (Condition.permuteOrderIso π) := rfl

end PartitionConsistency.ForcingQuotient

namespace PartitionConsistency.LocalDiagramSystem
universe u
open DiagramForcing DiagramOrder
noncomputable section
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]

/-- Coordinate transport for literal label fibers. -/
def labelTransport (π : Equiv.Perm I) : ReindexIso (labelSystem (M := M)) labelSystem π where
  app r := π.subtypeEquiv (fun j => by
    constructor
    · rintro ⟨m,hm⟩
      exact ⟨m,congrArg π hm⟩
    · rintro ⟨m,hm⟩
      exact ⟨m,π.injective hm⟩)
  natural _ _ := rfl

@[simp] theorem labelTransport_fiber_val {q : Diagram M I} (g : Vertex.RootGroup q)
    (v : Vertex q) (x : (labelSystem (M := M)).vertexFiber v) :
    ((labelTransport g.val).fiberEquiv g v x).val.val = g.val x.val.val := rfl

theorem labelFiberSet_permute {q : Diagram M I} (g : Vertex.RootGroup q)
    (v : Vertex q) (j : I) : j ∈ labelFiberSet v ↔ g.val j ∈ labelFiberSet (g • v) := by
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨(labelTransport g.val).fiberEquiv g v x,rfl⟩
  · rintro ⟨y,hy⟩
    obtain ⟨x,rfl⟩ := ((labelTransport g.val).fiberEquiv g v).surjective y
    exact ⟨x,g.val.injective hy⟩

namespace Vertex
variable {q : Diagram M I} (hj : HasConditionalJoins (LeftDivOrder M)) (v : Vertex q)

/-- The stabilizer permutes the actual common subset of label indices. -/
instance labelFiberAction : MulAction (componentStabilizer hj v) (labelFiberSet v) where
  smul g j := ⟨g.val.val j.val,by
    exact (labelFiberSet_common hj g.property).symm.subset
      ((labelFiberSet_permute g.val v j.val).mp j.property)⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl

@[simp] theorem smul_labelFiber_val (g : componentStabilizer hj v) (j : labelFiberSet v) :
    (g • j).val = g.val.val j.val := rfl

end Vertex
end
end PartitionConsistency.LocalDiagramSystem


/-! ## CodeCovariance -/

/-! Covariance on actual forcing conditions. The code order is held fixed,
whereas both the Cohen condition and the local supporting vertex move. -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_GermSelectors
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## PreAssignment -/

/-! The preliminary component assignment, as a persistent relation on actual
forcing conditions and actual HS names. The ordinal table is fixed once,
and the names for ranks/order types are computed from the persistent least
codes rather than from arbitrary principal-filter wellorders. -/


/-! ## Germ -/

namespace PartitionConsistency.LocalDiagramSystem.Vertex.Chain
universe u t
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable {q : Diagram M I} {v : Vertex q}
noncomputable section
variable (C : Chain v)

/-- The unique contraction from the initial vertex to a chain vertex. -/
def fromRoot (i : ℕ) : Arrow v (C.vertex i) := by
  simpa only [C.first] using (C.increasing 0 i (Nat.zero_le i)).some

def index (i : ℕ) : M := (C.fromRoot i).index

@[simp] theorem fromRoot_index (i : ℕ) : (C.fromRoot i).index = C.index i := rfl

end
end PartitionConsistency.LocalDiagramSystem.Vertex.Chain


/-! ## Selector -/

/-! A combinatorial coset-selector argument. The existence of a countable-base
tower and symmetric names for its assignments are established separately. -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_StableSelectors
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## ConditionSelector -/

/-! The countable-germ selector as a genuine condition-by-condition recipe.
There is no total family of generic rows in the ambient universe in this
construction.  A countable condition suffices to decide each selection, and
the decisions are both persistent and covariant. -/
namespace PartitionConsistency.CohenForcing.Condition
universe u
noncomputable section
open scoped Classical
variable {I κ : Type u}

/-- A convenient total extension of a partial condition. This is auxiliary
row data, NOT the generic rows; only values in the domain will be used to
make a persistent decision. -/
def rows (p : Condition I κ) (i : I) (a : κ) : Bool :=
  if ((i,a),true) ∈ p.graph then true else false

@[simp] theorem rows_permute (σ : Equiv.Perm I) (p : Condition I κ) (i : I) (a : κ) :
    (p.permute σ).rows i a = p.rows (σ.symm i) a := by
  simp only [rows,mem_permute]

/-- Fill only the as-yet-undefined places in a prescribed countable set. -/
def fill (p : Condition I κ) (A : Set (I × κ)) (hA : A.Countable) : Condition I κ where
  graph := p.graph ∪ {z | z.1 ∈ A ∧ z.1 ∉ p.dom ∧ z.2 = false}
  functional := by
    intro a b c hb hc
    rcases hb with hb | hb <;> rcases hc with hc | hc
    · exact p.functional a b c hb hc
    · exact False.elim (hc.2.1 ((p.mem_dom a).mpr ⟨b,hb⟩))
    · exact False.elim (hb.2.1 ((p.mem_dom a).mpr ⟨c,hc⟩))
    · exact hb.2.2.trans hc.2.2.symm
  countable_graph := p.countable_graph.union ((hA.image (fun a => (a,false))).mono (by
    rintro ⟨a,b⟩ ⟨ha,_,hb⟩
    exact ⟨a,ha,Prod.ext rfl hb.symm⟩))

end
end PartitionConsistency.CohenForcing.Condition


/-! ## CosetPredicate -/

/-! Coset transport for predicates on the total space of computations.
The inverse moves every argument, in particular the actual Cohen condition. -/
namespace PartitionConsistency.CohenForcing.Condition
universe u
variable {I κ : Type u}
instance coordinateAction : MulAction (Equiv.Perm I) (Condition I κ) where
  smul π d := d.permute π
  one_smul := permute_one
  mul_smul := fun π σ d => permute_mul π σ d
@[simp] theorem smul_condition (π : Equiv.Perm I) (d : Condition I κ) :
    π • d = d.permute π := rfl
end PartitionConsistency.CohenForcing.Condition


/-! ## Corrected -/

/-! A component assignment on actual conditions: select a residual coset,
compute at the inverse-moved condition, then transport every argument back.
The quotient operation uses proved tail invariance, not an arbitrary choice
of a bijection. -/


/-! ## StableTransport -/

/-! Coordinate transport for the permanently decided availability ideal.
This is used both for coset correction and for moving between component
orbits. -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_CodeCardinals
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CodeCardinal -/

/-! The upper bound for the actual name for the persistent code order type.
Its possible ordinal values are bounded by literal representation records
and the proved chain condition of the countable Cohen coordinate. -/
namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

namespace LocalWitness
variable {hμ c} {r : Diagram M I} {A : I → (system (M := M) (I := I) (κ := κ) hμ).Name}
variable {τ : LocalName hμ c r} {d e : CohenForcing.Condition I κ}

/-- A stronger principal quotient retains every literal representation
witness. In particular its three ground record entries do not change. -/
def below (w : LocalWitness hμ (principalFilter d) r A τ) (hed : e ≤ d) :
    LocalWitness hμ (principalFilter e) r A τ :=
  { w with mem := (mem_principalFilter _ _).mpr (hed.trans ((mem_principalFilter _ _).mp w.mem)) }

@[simp] theorem record_below (w : LocalWitness hμ (principalFilter d) r A τ) (hed : e ≤ d) :
    (w.below hed).record = w.record := rfl
end LocalWitness

end
end PartitionConsistency.ProductForcing


/-! ## CodeLower -/

/-! The lower bound for the actual persistent-code ordinal. Independent
probe rows give distinct ranks whenever their witnessing conditions are
compatible. The countable Cohen chain bound then gives the cardinal estimate,
without postulating a filter meeting an ambient uncountable family. -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_ConcreteQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CellDescent -/


/-! ## GermActual -/


/-! ## ConcreteSelector -/

/-! The selector for the actual saturated monoid and the prescribed Cohen
length. This supplies all countability/regularity hypotheses from the
construction, rather than leaving them as properties of an abstract action. -/
namespace PartitionConsistency.ConcreteSystem
open CardinalParameters DiagramForcing LocalDiagramSystem
noncomputable section

instance instNonemptyκ : Nonempty κ := Ordinal.nonempty_toType_iff.mpr
  Cardinal.isRegular_aleph_one.ord_pos.ne'

end
end PartitionConsistency.ConcreteSystem


/-! ## ConcreteCode -/

/-! The exact cardinality of the *actual ordinal name* for the persistent
least-code ordering in the executed concrete construction. No assertion of
genericity over an uncountable collection of ambient sets is used. -/


/-! ## ConcretePreAssignment -/


/-! ## ConcreteQuotient -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_UniformImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## KernelImage -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

def kernelRelation (h A B : S.Name) : S.BinaryRelation :=
  (S.boundedApp h A B).comp (S.boundedApp h A B).inverse

theorem kernelRelation_move (h A B : S.Name) (g : Γ)
    (hh : g • h = h) (hA : g • A = A) (hB : g • B = B)
    (p : P) (a b : S.Name) (hab : (S.kernelRelation h A B).holds p a b) :
    (S.kernelRelation h A B).holds (S.move g p) (g • a) (g • b) := by
  intro q hq
  obtain ⟨r,hrq,y,ha,hb⟩ := hab ((S.move g).symm q) ((S.move g).symm_apply_le.mpr hq)
  exact ⟨S.move g r,(S.move g).le_symm_apply.mp hrq,g • y,
    S.boundedApp_move h A B g hh hA hB r a y ha,
    S.boundedApp_move h A B g hh hA hB r b y hb⟩

def kernelGraph (h A B : S.Name) : S.Name :=
  (S.kernelRelation h A B).graph A A (S.tupleStabilizer ![h,A,B])
    (S.tupleStabilizer_mem _) (fun g hg => (S.mem_tupleStabilizer _ g).mp hg 1)
    (fun g hg => (S.mem_tupleStabilizer _ g).mp hg 1)
    (fun g hg => S.kernelRelation_move h A B g ((S.mem_tupleStabilizer _ g).mp hg 0)
      ((S.mem_tupleStabilizer _ g).mp hg 1) ((S.mem_tupleStabilizer _ g).mp hg 2))

theorem kernelGraph_fixed (h A B : S.Name) (g : Γ)
    (hh : g • h = h) (hA : g • A = A) (hB : g • B = B) :
    g • S.kernelGraph h A B = S.kernelGraph h A B := by
  apply BinaryRelation.graph_fixed
  apply (S.mem_tupleStabilizer _ g).mpr
  intro i
  fin_cases i <;> assumption

/-- Graph of the representative-free correspondence `h(a) ↦ [a]`. -/
def imageClassRelation (h A B : S.Name) : S.BinaryRelation where
  holds p y C := ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ a : S.Name,
    S.atomic.MemF r a A ∧ S.App r h a y ∧
      S.atomic.EqF r C (S.relationClass A (S.kernelGraph h A B) a)
  mono h hh q hq := hh q (hq.trans h)
  regular h q hq := by
    obtain ⟨r,hrq,hh⟩ := h q hq
    obtain ⟨s,hsr,a,ha⟩ := hh r le_rfl
    exact ⟨s,hsr.trans hrq,a,ha⟩
  congr := by
    intro p y y' C C' hy hC
    have step {y y' C C' : S.Name} (hy : S.atomic.EqF p y y') (hC : S.atomic.EqF p C C')
        (hh : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ a : S.Name,
          S.atomic.MemF r a A ∧ S.App r h a y ∧ S.atomic.EqF r C
            (S.relationClass A (S.kernelGraph h A B) a)) :
        ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ a : S.Name,
          S.atomic.MemF r a A ∧ S.App r h a y' ∧ S.atomic.EqF r C'
            (S.relationClass A (S.kernelGraph h A B) a) := by
      intro q hq
      obtain ⟨r,hrq,a,ha,hay,he⟩ := hh q hq
      exact ⟨r,hrq,a,ha,(S.app_congr (S.atomic.eq_refl r h) (S.atomic.eq_refl r a)
        (S.atomic.eq_mono (hrq.trans hq) hy)).mp hay,
        S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono (hrq.trans hq) hC)) he⟩
    exact ⟨step hy hC,step (S.atomic.eq_symm hy) (S.atomic.eq_symm hC)⟩

theorem imageClassRelation_move (h A B : S.Name) (g : Γ)
    (hh : g • h = h) (hA : g • A = A) (hB : g • B = B)
    (p : P) (y C : S.Name) (hi : (S.imageClassRelation h A B).holds p y C) :
    (S.imageClassRelation h A B).holds (S.move g p) (g • y) (g • C) := by
  intro q hq
  obtain ⟨r,hrq,a,ha,hay,he⟩ := hi ((S.move g).symm q) ((S.move g).symm_apply_le.mpr hq)
  refine ⟨S.move g r,(S.move g).le_symm_apply.mp hrq,g • a,?_,?_,?_⟩
  · simpa only [hA] using (S.mem_symmetry g r a A).mp ha
  · simpa only [hh] using (S.app_symmetry g r h a y).mp hay
  · simpa only [S.relationClass_move,hA,S.kernelGraph_fixed h A B g hh hA hB] using
      (S.eq_symmetry g r C _).mp he

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
open ProductForcing SetForcingNames.SymmetricSystem
noncomputable section

abbrev A : S.Name := labelSet aleph0_le_μ (posetCode κ)

def imageQuotient (h B : S.Name) : S.Name :=
  quotientName aleph0_le_μ (posetCode κ) (S.kernelGraph h A B)

def imageQuotientGraph (h B : S.Name) : S.Name :=
  (S.imageClassRelation h A B).graph B (imageQuotient h B) (S.tupleStabilizer ![h,B])
    (S.tupleStabilizer_mem _) (fun g hg => (S.mem_tupleStabilizer _ g).mp hg 1)
    (fun g hg => quotientName_fixed _ _ _ g (S.kernelGraph_fixed h A B g
      ((S.mem_tupleStabilizer _ g).mp hg 0) (smul_labelSet _ _ g)
      ((S.mem_tupleStabilizer _ g).mp hg 1)))
    (fun g hg => S.imageClassRelation_move h A B g ((S.mem_tupleStabilizer _ g).mp hg 0)
      (smul_labelSet _ _ g) ((S.mem_tupleStabilizer _ g).mp hg 1))

end
end PartitionConsistency.ConcreteSystem


/-! ## UniformMaximum -/

end OAI
end


