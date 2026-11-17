-- Prove2me | Definitions.Def_SkipListConc_Supplement_rsHeightChange
-- name    : SkipListConc_Supplement_rsHeightChange
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:53:54.329788+00:00
-- url     : https://prove2.me/theorems/5c853595-b91d-4f5e-a25f-0386c7f79520
-- title:
--   Levels by which heights change at one operation under reseeding
-- statement:
--   In the cost model of [BDL08] each level by which a height changes costs one unit. Under epochal reseeding, at operation $t$:
--
--   1. if $t$ opens an epoch (and $t>0$), every item present is redrawn, changing its height by $|\text{new}-\text{old}|$ levels, where old is its height at the end of operation $t-1$;
--   2. the target changes from its height before the operation to its height after it; an insertion draw counts its whole height (a rise from $0$).
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §5.3, p.35; §5.2, p.32

import Mathlib
import Definitions.Def_SkipListConc_opCount
import Definitions.Def_SkipListConc_Supplement_rsHeight
import Definitions.Def_SkipListConc_Supplement_rsAfter

namespace SkipListConc.Supplement

/-- The levels by which heights change at operation `t` under epochal reseeding, in the cost
model of [BDL08] used by Theorem F(b) (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), §5.3, p.35, and §5.2, p.32):
* if `t` opens an epoch (and `t > 0`), every item `y` present is redrawn, which changes its height
  by `|fresh − old|` levels, `old` its height at the end of operation `t − 1`;
* the target `x = σ[t]` changes from its height before the operation to its height after it; an
  insertion draw counts its whole height (a rise from `0`). -/
noncomputable def rsHeightChange (p : ℝ) {K : ℕ} {α Ω : Type*} [DecidableEq α]
    (ξ : (α × ℕ) × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (t : Fin σ.length) (ω : Ω) : ℕ :=
  Int.natAbs ((rsAfter p ξ σ t (σ.get t) ω : ℤ) -
      (if opCount σ (σ.get t) t = 0 then 0 else (rsHeight p ξ σ t (σ.get t) ω : ℤ))) +
    if (epochState σ t).2.2 = 1 ∧ 0 < (t : ℕ) then
      ∑ y ∈ (σ.take t).toFinset,
        Int.natAbs ((height p ξ (y, (epochState σ t).1) 1 ω : ℤ) - rsAfter p ξ σ ((t : ℕ) - 1) y ω)
    else 0

end SkipListConc.Supplement


