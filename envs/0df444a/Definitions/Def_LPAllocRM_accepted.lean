-- Prove2me | Definitions.Def_LPAllocRM_accepted
-- name    : LPAllocRM_accepted
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:06:09.430539+00:00
-- url     : https://prove2.me/theorems/6c858794-8553-4680-9c53-bde981cc2b87
-- title:
--   Number $N^\pi_j$ of accepted class-$j$ customers, eq. (2)
-- statement:
--   Under a policy $\pi$ and an arrival path $d$ on $(0,\tau]$, the number of accepted class-$j$ customers is
--
--   $$N^\pi_j\equiv\int_{(0,\tau]}\pi_j(s)\,D_j(ds),$$
--
--   which "simply counts the number of class $j$ arrivals that occur at times when we are willing to accept class $j$ arrivals". It is computed as the number of indices $i\in\{1,\dots,d_j(\tau)\}$ such that $\pi$, given the history up to the $i$-th class-$j$ arrival time $T_{j,i}$, accepts class $j$ at $T_{j,i}$.
--
--   By construction $0\le N^\pi\le D(\tau)$, the second constraint in (1). Arrivals do not depend on the policy: "we do not allow availability to affect the demand process".
--
--   **Formalization Note** On a simple counting path every class-$j$ jump has size one and occurs at exactly one $T_{j,i}$, so this count is the Stieltjes integral (2).
-- source:
--   Cooper, Asymptotic Behavior of an Allocation Policy for Revenue Management, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855, eq. (2), p.722

import Mathlib
import Definitions.Def_LPAllocRM_Policy
import Definitions.Def_LPAllocRM_arrivalTime

namespace LPAllocRM

/-- The number `N^π_j` of accepted class-`j` customers over `(0, τ]` under policy `π` on the
arrival path `d`: the number of class-`j` arrivals `i = 1, …, D_j(τ)` at whose arrival time
`T_i` the policy, reading the history `d` restricted to `(−∞, T_i]`, accepts class `j`.
Cooper, *Asymptotic Behavior of an Allocation Policy for Revenue Management*, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855,
(2), p.722 (PDF p.3): `N^π_j ≡ ∫_{(0,τ]} π_j(s) D_j(ds)`, which "simply counts the number of class j
arrivals that occur at times when we are willing to accept class j arrivals".

**Formalization Note** This is the integral (2) for counting paths: on a simple path (`IsArrivalPath`)
each class-`j` jump has size one and occurs at exactly one `arrivalTime d j i`, `1 ≤ i ≤ d τ j`, so
the Stieltjes integral is this count. By construction `0 ≤ N^π_j ≤ D_j(τ)`, the constraint
`0 ≤ N^π ≤ D(τ)` of (1). Arrivals do not depend on the policy ("we do not allow availability to
affect the demand process", p.722). -/
noncomputable def accepted {n : ℕ} (τ : ℝ) (π : Policy n) (d : ℝ → Fin n → ℕ) (j : Fin n) : ℕ :=
  ((Finset.Icc 1 (d τ j)).filter
    (fun i => π (arrivalTime d j i) (fun s => d s.1) j = true)).card

end LPAllocRM


