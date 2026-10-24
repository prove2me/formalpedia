-- Prove2me | Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Lemma4
-- name    : PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Lemma4
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T04:45:25.672585+00:00
-- url     : https://prove2.me/theorems/12fe2ce9-6373-47e3-9ef4-fc003613a2b9
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesBounds.Part1.Lemma4
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_8fb65f62dc7f7936c2bf07db
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem sum_map_le_mul {α : Type} (xs : List α) (f : α → Nat)
    (bound : Nat) (hbound : ∀ x ∈ xs, f x ≤ bound) :
    (xs.map f).sum ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := hbound x (by simp)
      have htail : ∀ y ∈ xs, f y ≤ bound := by
        intro y hy
        exact hbound y (by simp [hy])
      have hrest := ih htail
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
end CLRS.Chapter34.Turing.TMClique


