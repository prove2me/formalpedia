-- Prove2me | Definitions.Def_SkipListConc_scanStart
-- name    : SkipListConc_scanStart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:52:49.884702+00:00
-- url     : https://prove2.me/theorems/2db44b3d-3980-46fd-a424-69e310260478
-- title:
--   Scan start of charge $t$ on level $\ell$
-- statement:
--   For a charge $t$ with $s_t\le\ell-1$, its backward walk arrives on level $\ell$ at the largest key $y\le x_t$ present at time $t$ whose time-$t$ height is at least $\ell$, or at the head if there is none. This is the position at which it starts its scan of level $\ell$.
--
--   **Formalization Note** Valued in the keys extended by a bottom element, the head $-\infty$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §4.5.3, pp.26–27; Lemma 4.10, p.27

import Mathlib
import Definitions.Def_SkipListConc_heightAt
import Definitions.Def_SkipListConc_presentAt

namespace SkipListConc

/-- The position at which charge `t` starts its scan of level `ℓ` (Kapoor–Tanveer, *Counter-Free
Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256
f82c3d35…6dab6c), §4.5.3, pp.26–27, Lemma 4.10): for a charge with `s_t ≤ ℓ − 1`, the backward
walk arrives on level `ℓ` at the largest key `≤ x_t` present at time `t` whose time-`t` height is
`≥ ℓ`, or at the head if there is none.

**Formalization Note** Valued in `WithBot α`, with `⊥` the head `−∞`. -/
noncomputable def scanStart (p : ℝ) {K : ℕ} {α Ω : Type*} [LinearOrder α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (ℓ : ℕ) (t : Fin σ.length) (ω : Ω) :
    WithBot α :=
  ((presentAt σ t).filter fun y => y ≤ σ.get t ∧ ℓ ≤ heightAt p ξ σ t y ω).max

end SkipListConc


