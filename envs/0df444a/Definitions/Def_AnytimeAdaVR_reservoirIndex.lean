-- Prove2me | Definitions.Def_AnytimeAdaVR_reservoirIndex
-- name    : AnytimeAdaVR_reservoirIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:26:47.464351+00:00
-- url     : https://prove2.me/theorems/28814139-529a-4399-8e70-bc5536cec1e5
-- title:
--   Reservoir index after $N$ queries
-- statement:
--   Reservoir sampling with coins $U_1,U_2,\dots\in[0,1]$: at local query $r$ the candidate is replaced by the current label iff $U_r\le 1/r$. After $N\ge1$ queries the retained query is
--   $$
--   R(N)=\max\{r\in\{1,\dots,N\}: U_r\le 1/r\}.
--   $$
--   With independent uniform coins, $R(N)$ is uniform on $\{1,\dots,N\}$ and independent of the labels. Query $1$ always replaces.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), Algorithm 2 (Query), p.8; App. C.7, p.24

import Mathlib

namespace AnytimeAdaVR

/-- **The reservoir's retained query index.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), Algorithm 2 (`Query`), p.8: "With probability
1/q, set R ← ℓ using an independent coin", and p.8: "At local query number r, replace the path's
candidate by its current label with probability 1/r, using an independent coin."

With coins `U : ℕ → [0, 1]`, query `r` replaces the candidate iff `U r ≤ 1/r` (an event of
probability `1/r` when `U r` is uniform). After `N` queries the candidate is the label of the last
replacing query, `reservoirIndex U N = max {r ∈ [1, N] | U r ≤ 1/r}`.

**Formalization Note.** `r = 1` always replaces (`U 1 ≤ 1`), so for `N ≥ 1` the maximum is over a
nonempty set and lies in `[1, N]`; this is Algorithm 2's initial `R = xinit` being overwritten at
query 1 by the first block's label `xinit`. `Finset.sup` returns `0` only for `N = 0`. -/
noncomputable def reservoirIndex (U : ℕ → unitInterval) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun r => (U r : ℝ) ≤ 1 / (r : ℝ))).sup id

end AnytimeAdaVR


