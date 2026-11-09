-- Prove2me | Definitions.Def_SkipListConc_gapA
-- name    : SkipListConc_gapA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:52:23.815994+00:00
-- url     : https://prove2.me/theorems/3d5cf94e-b9ce-44f5-9a1c-b08758db98c2
-- title:
--   Gap $A_{\ell,t}$ of the backward walk of charge $t$
-- statement:
--   Fix a charge $t$. Its **backward walk** traces its search path backwards and continues it upwards, using the heights at time $t$, with the head present on every level: it starts at the target on level $s_t$, and on each level $\ell$ moves left until it reaches the first node, possibly the head, whose height at time $t$ is at least $\ell+1$, then moves up. $A_{\ell,t}\ge 0$ is the number of left steps on level $\ell\ge s_t$. On every level the real search uses, these are exactly its horizontal steps, and above the maximum height $A_{\ell,t}=0$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §4.5.3, pp.26–27

import Mathlib
import Definitions.Def_SkipListConc_heightAt
import Definitions.Def_SkipListConc_presentAt
import Definitions.Def_SkipListConc_levelSteps

namespace SkipListConc

/-- The gap `A_{ℓ,t}` of charge `t` on level `ℓ` (Kapoor–Tanveer, *Counter-Free Self-Adjusting
Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c),
§4.5.3, pp.26–27): the number of left steps on level `ℓ` of the backward walk of charge `t`,
which starts at the target on its served level `s_t`, uses the heights at time `t`, and on each
level moves left to the first node (possibly the head) of height `≥ ℓ + 1`. For `ℓ ≥ s_t` it is
the number of nodes `y ≤ x_t` present at time `t` with height `≥ ℓ` and no node of height
`≥ ℓ + 1` between `y` and `x_t`, which is `levelSteps` of the time-`t` configuration.

**Formalization Note** Used only for `ℓ ≥ s_t`. It is `0` above the maximum height (the walk sits
at the head), and on every level the real search uses it equals the search's steps there. -/
noncomputable def gapA (p : ℝ) {K : ℕ} {α Ω : Type*} [LinearOrder α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (ℓ : ℕ) (t : Fin σ.length) (ω : Ω) : ℕ :=
  levelSteps (presentAt σ t) (fun y => heightAt p ξ σ t y ω) (σ.get t) ℓ

end SkipListConc


