-- Prove2me | Definitions.Def_LeGallBrownianMap_dStar
-- name    : LeGallBrownianMap_dStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:55.419877+00:00
-- url     : https://prove2.me/theorems/1c8c8fd1-db2b-4742-ba4f-0281a9d9f666
-- title:
--   The Brownian map distance $D^*(s,t)$
-- statement:
--   Let $e$ be an excursion path coding the tree $\mathcal T_e=[0,1]/\!\sim_e$, where $s\sim_e t$ iff $d_e(s,t)=e_s+e_t-2\min_{[s\wedge t,s\vee t]}e=0$, and let $Z$ be a label path. For $a,b\in\mathcal T_e$ put $D^\circ(a,b)=\min\{D^\circ(s,t): p_e(s)=a,\ p_e(t)=b\}$ and
--
--   $$
--   D^*(a,b)=\inf\Big\{\sum_{i=1}^k D^\circ(a_{i-1},a_i)\Big\},
--   $$
--
--   the infimum over $k\ge1$ and $a_0=a,a_1,\dots,a_k=b$ in $\mathcal T_e$. Viewed on $[0,1]^2$, $D^*(s,t)=D^*(p_e(s),p_e(t))$. It is the largest pseudometric below $D^\circ$ compatible with $\sim_e$, and is the distance of the Brownian map.
--
--   **Formalization Note** Unfolded on $[0,1]$: the infimum over $k\ge1$ and times $x_1,y_1,\dots,x_k,y_k$ with $x_1\sim_e s$, $y_i\sim_e x_{i+1}$, $y_k\sim_e t$ of $\sum_i D^\circ(x_i,y_i)$. The relation $\sim_e$ uses the published `OAI.FKCRT.excursionDist`. The index set is nonempty and, for continuous $Z$, the terms are nonnegative, so the real infimum is the true one.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.4, p.15; eq. (1), p.4

import Mathlib
import Definitions.Def_FKCRT
import Definitions.Def_LeGallBrownianMap_dCirc

open OAI.FKCRT

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.4, p.15:
"We then set, for every a, b ∈ T_e, D°(a, b) = min{D°(s, t) : s, t ∈ [0, 1], p_e(s) = a,
p_e(t) = b}. […] we can set, for every a, b ∈ T_e, D∗(a, b) = inf { Σ_{i=1}^{k} D°(a_{i−1}, a_i) },
where the infimum is over all choices of the integer k ≥ 1 and of a_0, ..., a_k ∈ T_e such that
a_0 = a and a_k = b. […] It will sometimes be convenient to view D∗ as a function on [0, 1]^2, by
setting D∗(s, t) = D∗(p_e(s), p_e(t))." (Also eq. (1), p.4.)

`dStar e Z s t` is `D∗(s,t)`: the infimum, over `k ≥ 1` and times
`x_1, y_1, …, x_k, y_k ∈ [0,1]` with `x_1 ∼_e s`, `y_i ∼_e x_{i+1}` and `y_k ∼_e t`, of
`Σ_i D°(x_i, y_i)`, where `u ∼_e v` means `d_e(u,v) = 0`.

**Formalization Note.** The tree `T_e = [0,1]/∼_e` is unfolded on `[0,1]`: a point of `T_e` is
a class of times, `D°` on `T_e` is the minimum of `dCirc` over representatives, and the
infimum of a sum of minima is the infimum over all choices of representatives, which is the
infimum written here (chains are indexed by `Fin (k+1)`, i.e. `k + 1 ≥ 1` steps). The relation
`∼_e` is the published `OAI.FKCRT.excursionDist e u v = 0` (`d_e(u,v) = e_u + e_v − 2 min e`).
The index set is never empty (`k = 0`, `x = s`, `y = t`), and for continuous `Z` every term is
`≥ 0`, so the real infimum is the paper's infimum (no junk value). -/
noncomputable def dStar (e Z : unitInterval → ℝ) (s t : unitInterval) : ℝ :=
  ⨅ c : {c : Σ k : ℕ, (Fin (k + 1) → unitInterval) × (Fin (k + 1) → unitInterval) //
      excursionDist e s (c.2.1 0) = 0 ∧
      (∀ i : Fin c.1, excursionDist e (c.2.2 i.castSucc) (c.2.1 i.succ) = 0) ∧
      excursionDist e (c.2.2 (Fin.last c.1)) t = 0},
    ∑ i, dCirc Z (c.1.2.1 i) (c.1.2.2 i)

end LeGallBrownianMap


