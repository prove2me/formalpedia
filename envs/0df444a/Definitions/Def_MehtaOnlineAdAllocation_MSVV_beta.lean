-- Prove2me | Definitions.Def_MehtaOnlineAdAllocation_MSVV_beta
-- name    : MehtaOnlineAdAllocation_MSVV_beta
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:36:39.393984+00:00
-- url     : https://prove2.me/theorems/d6841945-f95b-48ad-954e-6a34dcbdd324
-- title:
--   Section 5.2 — physical slab volume
-- statement:
--   For unit budgets and actual terminal spends $s_u$, the volume of slab $i$ is
--   $$\beta_i=\sum_u\min\{1/k,\max\{0,s_u-(i-1)/k\}\}.$$
--   This measures the actual money in the physical interval $[(i-1)/k,i/k)$. Partial terminal slabs keep their actual volume. It is not defined by equation (5.2), by a query-sum proxy, or by rounding every spend up to its type endpoint. Relevant uses have $k\ge1$, $1\le i\le k$ and $s_u\in[0,1]$.
-- source:
--   Aranyak Mehta, Online Matching and Ad Allocation, Foundations and Trends in Theoretical Computer Science 8(4), 265–368, 2013, DOI 10.1561/0400000057 (published), §5.2, printed p. 312 (PDF p. 50), Figure 5.2 and preamble to equation (5.2).

import Mathlib

namespace MehtaOnlineAdAllocation.MSVV

noncomputable def beta {N : ℕ} (k : ℕ) (s : Fin N → ℝ) (i : ℕ) : ℝ :=
  ∑ u, min (1 / (k : ℝ)) (max 0 (s u - ((i : ℝ) - 1) / (k : ℝ)))

end MehtaOnlineAdAllocation.MSVV


