-- Prove2me | Definitions.Def_SkipListConc_levelCplus
-- name    : SkipListConc_levelCplus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:53:30.489769+00:00
-- url     : https://prove2.me/theorems/faf8a2b1-7d65-427c-9685-d56642002a5d
-- title:
--   Level cost above the served level $C^+_\ell$
-- statement:
--   The part of the level cost from the charges found below level $\ell\ge 1$:
--   $$
--   C^+_\ell=\sum_{t:\ s_t\le\ell-1}A_{\ell,t},
--   $$
--   so $C_\ell=C^0_\ell+C^+_\ell$ with $C^0_\ell=\sum_{t:s_t=\ell}A_{\ell,t}$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §4.5.3, p.27

import Mathlib
import Definitions.Def_SkipListConc_servedHeight
import Definitions.Def_SkipListConc_gapA

namespace SkipListConc

/-- The part `C⁺_ℓ = ∑_{t : s_t ≤ ℓ − 1} A_{ℓ,t}` of the level cost from the searches found below
level `ℓ` (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), §4.5.3, p.27).

**Formalization Note** Used for `ℓ ≥ 1`, where `ℓ − 1` is exact. -/
noncomputable def levelCplus (p : ℝ) {K : ℕ} {α Ω : Type*} [LinearOrder α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (ℓ : ℕ) (ω : Ω) : ℕ :=
  ∑ t ∈ Finset.univ.filter (fun t : Fin σ.length => servedHeight p ξ σ t ω ≤ ℓ - 1),
    gapA p ξ σ ℓ t ω

end SkipListConc


