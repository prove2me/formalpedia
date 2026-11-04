-- Prove2me | Definitions.Def_OverbookBL_Instance
-- name    : OverbookBL_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:39.084266+00:00
-- url     : https://prove2.me/theorems/4c9a03ea-8c45-4807-834d-228c882254ce
-- title:
--   Overbooking instance: arrival rates $\lambda_j$, revenues $v_j$, show-up probabilities $p_j$
-- statement:
--   An **overbooking instance** with $k$ customer types consists of, for each type $j\in[k]$,
--
--   1. an arrival probability $\lambda_j>0$, with $\sum_j\lambda_j=1$;
--   2. a revenue $v_j\ge 0$ earned when a type-$j$ customer is accepted;
--   3. a show-up probability $p_j\in(0,1]\cap\mathbb Q$: an accepted type-$j$ customer independently consumes one unit of capacity with probability $p_j$ and is a no-show otherwise.
--
--   The **critical ratio** $q_j=v_j/p_j$ satisfies $q_j<1$ for every type, and the types are ordered by critical ratio,
--
--   $$
--   \frac{v_1}{p_1}\ge\frac{v_2}{p_2}\ge\cdots\ge\frac{v_k}{p_k},
--   $$
--
--   with ties broken in favour of greater value: if $v_i/p_i=v_j/p_j$ for $i<j$, then $v_i>v_j$ and $p_i>p_j$. Overbooked customers are compensated at the normalized cost $1$, so $q_j<1$ means that the expected compensation of an extra type-$j$ customer who surely overflows exceeds his revenue.
--
--   This structure is the data of every statement of the mission.
--
--   **Formalization Note** Types are `Fin k` in the paper's order (type $1$ is index $0$). The paper writes $v_j<1$; it follows from $v_j<p_j\le 1$ and is not a separate field. $v_j\ge0$ and $p_j>0$ are implicit in the paper. The paper states the tie rule for adjacent types; for sorted ratios this is equivalent to the pairwise form used here.
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, §2, pp.9–10

import Mathlib

namespace OverbookBL

/-- An instance of the overbooking model of Freund & Zhao, *Overbooking with bounded loss*,
arXiv:2204.11148v2, §2, pp.9–10: `k` customer types with arrival probabilities `λⱼ`, revenues
`vⱼ` and show-up probabilities `pⱼ`.

* `lam j = λⱼ > 0` with `∑ⱼ λⱼ = 1` (p.9, "Arrivals");
* `v j = vⱼ ≥ 0` is the revenue of an accepted type-`j` customer (p.9);
* `p j = pⱼ ∈ (0, 1] ∩ ℚ` is the probability that an accepted type-`j` customer shows up and
  consumes one unit of capacity (p.9);
* the critical ratio `qⱼ = vⱼ/pⱼ` is `< 1` (p.10, "we focus without loss of generality on types
  `j` with `qⱼ < 1`");
* the types are ordered by non-increasing critical ratio, ties broken in favour of greater value:
  equal ratios force strictly larger `v` and `p` for the earlier type (p.9).

**Formalization Note** Types are `Fin k`, in the paper's order (type 1 is `0`). The paper states
the tie rule for adjacent types (`vⱼ/pⱼ = vⱼ₊₁/pⱼ₊₁ ⇒ vⱼ > vⱼ₊₁ ∧ pⱼ > pⱼ₊₁`); `tie_rule` states it
for every pair `i < j`, which is equivalent given `ratio_antitone` (equal ratios form a contiguous
block). The paper's `vⱼ < 1` (p.9) is not a separate field: it follows from `vⱼ < pⱼ ≤ 1`.
`vⱼ ≥ 0` (a revenue) and `pⱼ > 0` (so that `qⱼ` is defined) are implicit on p.9. -/
structure Instance (k : ℕ) where
  /-- Arrival probability `λⱼ` of type `j`. -/
  lam : Fin k → ℝ
  /-- Revenue `vⱼ` of an accepted type-`j` customer. -/
  v : Fin k → ℝ
  /-- Show-up probability `pⱼ` of an accepted type-`j` customer. -/
  p : Fin k → ℝ
  lam_pos : ∀ j, 0 < lam j
  lam_sum : ∑ j, lam j = 1
  v_nonneg : ∀ j, 0 ≤ v j
  p_pos : ∀ j, 0 < p j
  p_le_one : ∀ j, p j ≤ 1
  p_rat : ∀ j, ∃ r : ℚ, p j = (r : ℝ)
  /-- The critical ratio `qⱼ = vⱼ/pⱼ` is below `1` (p.10). -/
  q_lt_one : ∀ j, v j < p j
  /-- `v₁/p₁ ≥ v₂/p₂ ≥ ⋯ ≥ vₖ/pₖ` (p.9). -/
  ratio_antitone : ∀ i j : Fin k, i ≤ j → v j / p j ≤ v i / p i
  /-- Ties in the critical ratio are broken in favour of greater value (p.9). -/
  tie_rule : ∀ i j : Fin k, i < j → v i / p i = v j / p j → v j < v i ∧ p j < p i

end OverbookBL


