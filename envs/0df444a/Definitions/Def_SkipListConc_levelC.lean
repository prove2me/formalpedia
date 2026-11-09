-- Prove2me | Definitions.Def_SkipListConc_levelC
-- name    : SkipListConc_levelC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:53:32.34421+00:00
-- url     : https://prove2.me/theorems/24ac4b49-fc2f-4d11-8fa5-6cee2666928d
-- title:
--   Level cost $C_\ell=\sum_{t:s_t\le\ell}A_{\ell,t}$
-- statement:
--   The **cost of level $\ell$** is
--   $$
--   C_\ell=\sum_{t:\ s_t\le\ell}A_{\ell,t},
--   $$
--   the left steps on level $\ell$ of all backward walks that visit it.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §4.5.3, p.26

import Mathlib
import Definitions.Def_SkipListConc_servedHeight
import Definitions.Def_SkipListConc_gapA

namespace SkipListConc

/-- The level cost `C_ℓ = ∑_{t : s_t ≤ ℓ} A_{ℓ,t}` (Kapoor–Tanveer, *Counter-Free Self-Adjusting
Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c),
§4.5.3, p.26). -/
noncomputable def levelC (p : ℝ) {K : ℕ} {α Ω : Type*} [LinearOrder α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (ℓ : ℕ) (ω : Ω) : ℕ :=
  ∑ t ∈ Finset.univ.filter (fun t : Fin σ.length => servedHeight p ξ σ t ω ≤ ℓ), gapA p ξ σ ℓ t ω

end SkipListConc


