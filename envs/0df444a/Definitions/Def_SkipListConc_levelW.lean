-- Prove2me | Definitions.Def_SkipListConc_levelW
-- name    : SkipListConc_levelW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:53:25.765712+00:00
-- url     : https://prove2.me/theorems/36343137-c96c-4687-b6d6-501b6d53c24e
-- title:
--   $W_\ell=\#\{t:s_t\le\ell\}$
-- statement:
--   For a level $\ell$, $W_\ell=\#\{t:\ s_t\le\ell\}$ is the number of charges whose served height is at most $\ell$; so $W_\ell\le F$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §4.5.3, p.26

import Mathlib
import Definitions.Def_SkipListConc_servedHeight

namespace SkipListConc

/-- `W_ℓ = #{t : s_t ≤ ℓ}` (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration
Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c), §4.5.3, p.26). -/
noncomputable def levelW (p : ℝ) {K : ℕ} {α Ω : Type*} [DecidableEq α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (ℓ : ℕ) (ω : Ω) : ℕ :=
  (Finset.univ.filter fun t : Fin σ.length => servedHeight p ξ σ t ω ≤ ℓ).card

end SkipListConc


