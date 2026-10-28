-- Prove2me | Definitions.Def_BS2_b3ba934b_MinMaxNesting
-- name    : BS2_b3ba934b_MinMaxNesting
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:01:51.786639+00:00
-- url     : https://prove2.me/theorems/ef3f3aba-79c2-4100-97e5-366d72781add
-- title:
--   Sensitivity separation: MinMaxNesting (complete source module)
-- statement:
--   Complete Lean source module `MinMaxNesting` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinMaxNesting.lean; original SHA-256 a818bfe7ba65fe756f4a27ada444c420f86ebb137da4e4441d8b058cd513609f; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_RecursiveLowerBounds
import Definitions.Def_BS2_b3ba934b_ProfileClosures

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace ThreeBoundNesting
open ThreeBoundWitness ThreeBoundProfiles

variable {L I V : Type} [Preorder L] [Fintype V]

/-- Conditions on an actual min/max recipe array that preserve the nesting of
the child predicates. They constrain recipes, not the desired output bound. -/
structure OrderedRecipe (r : MinMaxRecipe L V) : Prop where
  guard : Antitone r.guard
  tolerance : Antitone r.tolerance
  lower_mono : ∀ l, Monotone (r.lower l)
  upper_mono : ∀ l, Monotone (r.upper l)
  lower_order : ∀ i j, i ≤ j → ∀ b, b ≤ r.tolerance j →
    r.lower i b ≤ r.lower j b
  upper_order : ∀ i j, i ≤ j → ∀ b, b ≤ r.tolerance j →
    r.upper i b ≤ r.upper j b

theorem failed_subset (r : MinMaxRecipe L V) (hr : OrderedRecipe r)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (hij : i ≤ j) (x : ((V × Bool) × I) → Bool) (v : V) :
    failed (r.stage F) F i x v ⊆ failed (r.stage F) F j x v := by
  classical
  intro w hw
  change w ∈ Finset.univ.filter (fun z =>
    r.Adj v z ∧ F (r.guard i) (child x z (r.label v z)) = true) at hw
  change w ∈ Finset.univ.filter (fun z =>
    r.Adj v z ∧ F (r.guard j) (child x z (r.label v z)) = true)
  have hh := (Finset.mem_filter.mp hw).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh.1,
    hF _ _ (hr.guard hij) _ hh.2⟩

theorem target_mono (r : MinMaxRecipe L V) (hr : OrderedRecipe r)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (hij : i ≤ j) (a b : ℕ) (hab : a ≤ b)
    (hb : b ≤ r.tolerance j) (x y : I → Bool)
    (h : minmaxTarget F r.lower r.upper j b x y = true) :
    minmaxTarget F r.lower r.upper i a x y = true := by
  have ht : r.lower i a ≤ r.lower j b :=
    (hr.lower_mono i hab).trans (hr.lower_order i j hij b hb)
  have hu : r.upper i a ≤ r.upper j b :=
    (hr.upper_mono i hab).trans (hr.upper_order i j hij b hb)
  simp only [minmaxTarget, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
  refine ⟨⟨hF _ _ ht x h.1.1, hF _ _ ht y h.1.2⟩, ?_⟩
  rcases h.2 with hx | hy
  · exact Or.inl (hF _ _ hu x hx)
  · exact Or.inr (hF _ _ hu y hy)

/-- The concrete parent construction used by the witness recursion preserves
nested families for every ordered min/max recipe. -/
theorem parent_nested (r : MinMaxRecipe L V) (hr : OrderedRecipe r)
    (F : L → (I → Bool) → Bool) (hF : Nested F) :
    Nested (parent (r.stage F) F) := by
  intro i j hij x hj
  obtain ⟨v, hv, ht⟩ := (parent_true_iff (r.stage F) F j x).mp hj
  have hc := Finset.card_le_card (failed_subset r hr F hF i j hij x v)
  apply (parent_true_iff (r.stage F) F i x).mpr
  refine ⟨v, hc.trans (hv.trans (hr.tolerance hij)), ?_⟩
  exact target_mono r hr F hF i j hij _ _ hc hv _ _ ht

/-- Nesting holds at every depth of the actual arbitrary-depth construction. -/
theorem tower_nested (r : ℕ → MinMaxRecipe L V)
    (hr : ∀ n, OrderedRecipe (r n)) (n : ℕ) :
    Nested (towerFamily r n) := by
  induction n with
  | zero => exact fun _ _ _ _ h => h
  | succ n ih => exact parent_nested (r n) (hr n) _ ih

end ThreeBoundNesting

#print axioms ThreeBoundNesting.parent_nested
#print axioms ThreeBoundNesting.tower_nested


