-- Prove2me | Definitions.Def_CoCoNet_IsAdmissible
-- name    : CoCoNet_IsAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:17.124612+00:00
-- url     : https://prove2.me/theorems/741fb0f6-c26c-4ac9-b561-a210110e270d
-- title:
--   Admissible conversion network $(m, W)$
-- statement:
--   There are $n$ banks $[n]=\{1,\dots,n\}$. Upon conversion of its contingent convertible debt, bank $i$ issues $m_i$ new stocks (the original number of stocks is normalised to $1$). The entry $w_{ij}$ of the matrix $W$ is the fraction of bank $j$'s convertible debt that is held by bank $i$.
--
--   The pair $(m,W)$ is **admissible** when
--   1. $m_i>0$ for every bank $i$;
--   2. $w_{ij}\in[0,1]$ for all $i,j$;
--   3. $w_{ii}=0$ for every $i$ (no bank holds its own debt);
--   4. $\sum_{i\in[n]} w_{ij}\le 1$ for every issuer $j$.
--
--   These are the standing assumptions of the model; every result of the mission assumes them. The case $\sum_i w_{ij}<1$ means part of bank $j$'s debt is held outside the banking system.
--
--   **Formalization Note** Banks are `Fin n` (0-based) and `W i j` $=w_{ij}$ (holder $i$, issuer $j$), so condition 4 bounds the column sums of $W$.
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, §2 'The Model', p.8

import Mathlib

namespace CoCoNet

/-- **Admissible conversion network** `(m, W)`.
Balter, Schweizer & Vera, *Contingent Capital with Stock Price Triggers in Interbank Networks*,
arXiv:2011.06474v1, §2 "The Model", p.8: banks `[n] = {1, …, n}`; upon conversion bank `i` issues
"mᵢ > 0 new stocks"; "By wᵢⱼ, we denote the fraction of bank j's convertible debt that is due to
bank i. … The wᵢⱼ satisfy wᵢⱼ ∈ [0, 1], wᵢᵢ = 0 and Σ_{i∈[n]} wᵢⱼ ≤ 1."

**Formalization Note.** Banks are `Fin n` (0-based). `W i j = wᵢⱼ` (holder `i`, issuer `j`), so
the condition `Σᵢ wᵢⱼ ≤ 1` bounds the column sums of `W`. -/
structure IsAdmissible {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) : Prop where
  /-- `mᵢ > 0` new stocks are issued upon conversion. -/
  m_pos : ∀ i, 0 < m i
  /-- `wᵢⱼ ∈ [0, 1]`. -/
  W_nonneg : ∀ i j, 0 ≤ W i j
  /-- `wᵢⱼ ∈ [0, 1]`. -/
  W_le_one : ∀ i j, W i j ≤ 1
  /-- `wᵢᵢ = 0`. -/
  W_diag : ∀ i, W i i = 0
  /-- `Σ_{i∈[n]} wᵢⱼ ≤ 1` for every issuer `j`. -/
  colSum_le : ∀ j, ∑ i, W i j ≤ 1

end CoCoNet


