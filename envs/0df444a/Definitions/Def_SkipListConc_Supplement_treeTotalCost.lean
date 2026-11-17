-- Prove2me | Definitions.Def_SkipListConc_Supplement_treeTotalCost
-- name    : SkipListConc_Supplement_treeTotalCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:59:45.131898+00:00
-- url     : https://prove2.me/theorems/baa56eb1-f033-4ebb-a347-db761f192016
-- title:
--   Total tree cost of an operation sequence
-- statement:
--   The total tree cost (search plus restructuring, summed over all charges) of an operation sequence in the self-adjusting treap / zip tree without reseeding.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §8, p.42

import Mathlib
import Definitions.Def_SkipListConc_Supplement_treeCharge

namespace SkipListConc.Supplement

/-- The total tree cost (search plus restructuring) of an operation sequence in the
self-adjusting treap / zip tree without reseeding (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), §8, p.42). -/
noncomputable def treeTotalCost (p : ℝ) {K : ℕ} {α Ω : Type*} [LinearOrder α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (ω : Ω) : ℕ :=
  ∑ t : Fin σ.length, treeCharge p ξ σ t ω

end SkipListConc.Supplement


