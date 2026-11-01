-- Prove2me | Definitions.Def_SupermodDRO_Assumptions
-- name    : SupermodDRO_Assumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:34:44.054582+00:00
-- url     : https://prove2.me/theorems/56fc174f-4eae-4f14-b90b-ef52f120a1d4
-- title:
--   Standing assumptions of §2
-- statement:
--   The data satisfy:
--
--   1. Problem (2) has a finite optimal value;
--   2. $\mathcal Q\subseteq\{q\in\mathbb R^K_+ : \mathbf 1^\top q=1\}$;
--   3. for every $k\in[K]$ there is $q\in\mathcal Q$ with $q_k>0$;
--   4. every scenario satisfies the assumptions of p.7 (`ScenarioAssumptions`);
--   5. $n\ge1$.
--
--   **Formalization Note** Item 5 is not written in the paper; Algorithm 1 takes $p_1=\min\{q^1_1,\dots,q^1_n\}$, which is undefined for $n=0$. The ordering $\underline z^k\le\mu^k\le\overline z^k$ and $\delta^k\ge0$ inside item 4 is a reading of the paper's implicit assumptions.
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), §2.1, pp.6–7; Algorithm 1, p.10

import Mathlib
import Definitions.Def_SupermodDRO_QSet
import Definitions.Def_SupermodDRO_ScenarioAssumptions
import Definitions.Def_SupermodDRO_problem2Value

namespace SupermodDRO

/-- **The standing assumptions of §2.** Long, Qi & Zhang, *Supermodularity in Two-Stage
Distributionally Robust Optimization*, author manuscript (June 2022), §2.1, pp.6–7, and Algorithm 1,
p.10:
1. (`finite_value`) "We assume that Problem (2) has a finite optimal value" (p.6);
2. (`Q_simplex`) "𝒬 = {q | Rq ≤ ν, q ≥ 0} ⊆ {q ∈ ℜᴷ₊ | 𝟏⊤q = 1}" (p.7);
3. (`Q_pos`) "the polyhedron 𝒬 is such that for all k ∈ [K], there exists q ∈ 𝒬 with q_k > 0" (p.7);
4. (`scenario`) for every scenario `k`, the WLOG assumptions of p.7 and `z̲ᵏ ≤ µᵏ ≤ z̄ᵏ`, `δᵏ ≥ 0`
   (`ScenarioAssumptions`);
5. (`n_pos`) `n ≥ 1`.

**Formalization Note** Item 5 is not written in the paper; Algorithm 1 takes
`p₁ = min{q₁¹, …, qₙ¹}` (p.10), which is undefined for `n = 0`. The last clause of item 4 is a
reading of the paper's implicit assumptions (see `ScenarioAssumptions`). -/
structure Assumptions {l m r n K s : ℕ} (D : Data l m r n K s) : Prop where
  finite_value : problem2Value D ≠ ⊤ ∧ problem2Value D ≠ ⊥
  Q_simplex : ∀ q ∈ QSet D.R D.ν, (∀ k, 0 ≤ q k) ∧ ∑ k, q k = 1
  Q_pos : ∀ k, ∃ q ∈ QSet D.R D.ν, 0 < q k
  scenario : ∀ k, ScenarioAssumptions (D.μ k) (D.δ k) (D.zl k) (D.zu k)
  n_pos : 0 < n

end SupermodDRO


