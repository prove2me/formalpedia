-- Prove2me | Definitions.Def_SkipListConc_levelWplus
-- name    : SkipListConc_levelWplus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:53:15.837424+00:00
-- url     : https://prove2.me/theorems/759fd36e-b138-4957-85fe-c2016833f7a3
-- title:
--   $W^+_\ell=\#\{t:s_t\le\ell-1\}$
-- statement:
--   For a level $\ell\ge1$, $W^+_\ell=\#\{t:\ s_t\le\ell-1\}\le W_\ell$ is the number of charges found below level $\ell$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §4.5.3, p.27

import Mathlib
import Definitions.Def_SkipListConc_servedHeight

namespace SkipListConc

/-- `W⁺_ℓ = #{t : s_t ≤ ℓ − 1}` (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists:
Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c), §4.5.3, p.27).

**Formalization Note** Used for `ℓ ≥ 1`, where `ℓ − 1` is exact. -/
noncomputable def levelWplus (p : ℝ) {K : ℕ} {α Ω : Type*} [DecidableEq α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (ℓ : ℕ) (ω : Ω) : ℕ :=
  (Finset.univ.filter fun t : Fin σ.length => servedHeight p ξ σ t ω ≤ ℓ - 1).card

end SkipListConc


