-- Prove2me | Definitions.Def_SkipListConc_Supplement_rsAfter
-- name    : SkipListConc_Supplement_rsAfter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:51:51.230726+00:00
-- url     : https://prove2.me/theorems/d1e5d64b-1f51-4246-9d7f-d764b4f5752b
-- title:
--   Height of an item at the end of an operation under reseeding
-- statement:
--   Under epochal reseeding, the height of item $y$ at the end of operation $t$: its height during the search of $t$, advanced by one draw of the epoch's randomness if $y$ is the target of $t$ (its promotion, or its insertion draw).
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Definition 1.6, p.10

import Mathlib
import Definitions.Def_SkipListConc_height
import Definitions.Def_SkipListConc_Supplement_reseedCount

namespace SkipListConc.Supplement

/-- The height of item `y` at the end of operation `t` under epochal reseeding (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c),
Definition 1.6, p.10): as `rsHeight`, with one more draw if `y` is the target `σ[t]` (its
promotion, or its insertion draw). -/
noncomputable def rsAfter (p : ℝ) {K : ℕ} {α Ω : Type*} [DecidableEq α]
    (ξ : (α × ℕ) × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (t : ℕ) (y : α) (ω : Ω) : ℕ :=
  height p ξ (y, (epochState σ t).1) (reseedCount σ t y + if σ[t]? = some y then 1 else 0) ω

end SkipListConc.Supplement


