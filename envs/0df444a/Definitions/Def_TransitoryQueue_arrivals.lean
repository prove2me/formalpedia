-- Prove2me | Definitions.Def_TransitoryQueue_arrivals
-- name    : TransitoryQueue_arrivals
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:20.261072+00:00
-- url     : https://prove2.me/theorems/0d7d278c-6cb3-4c45-91e9-ef0c61d2ea29
-- title:
--   The RS$(G,p)$ arrival process $A_n(t)=\sum_{i=1}^{nG_n(t)}\zeta_i$
-- statement:
--   Let $T_1,\dots,T_n$ be the sampled arrival epochs and $\zeta_1,\dots,\zeta_n\in\{0,1\}$ the turn-up indicators. With the empirical distribution function $G_n(t)=\frac1n\#\{i: T_i\le t\}$ (1), the **arrival process** (2) is
--
--   $$A_n(t)=\sum_{i=1}^{nG_n(t)}\zeta_i,$$
--
--   the number of customers who have turned up by time $t$.
--
--   **Formalization Note** Samples are indexed by $\{0,\dots,n-1\}$, so $\sum_{i=1}^{m}$ is the sum over indices $i<m$. The rank indexing of (2) is kept literally: the indicator $\zeta_i$ goes with the $i$-th epoch in time order, not with customer $i$'s epoch $T_i$.
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, eqs. (1)–(2), p.5

import Mathlib

namespace TransitoryQueue

/-- The RS(G, p) arrival process (2): `A_n(t) = Σ_{i=1}^{n G_n(t)} ζ_i`, where
`n G_n(t) = #{i : T_i ≤ t}` is the number of sampled arrival epochs up to time `t` (1).
The `i`-th turn-up indicator is attached to the `i`-th epoch in time order (rank indexing).
Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, eqs. (1)–(2), p.5.

**Formalization Note** The sample has size `n`: epochs `T : Fin n → ℝ` and indicators
`ζ : Fin n → ℕ` (values in `{0, 1}` in the model). The paper's `Σ_{i=1}^{m}` is the sum over
`i : Fin n` with `i.val < m` (0-based indices). The rank indexing of (2) is kept literally:
`ζ_i` is not attached to customer `i`'s epoch `T_i`. -/
noncomputable def arrivals {n : ℕ} (T : Fin n → ℝ) (ζ : Fin n → ℕ) (t : ℝ) : ℕ :=
  ∑ i : Fin n with i.val < (Finset.univ.filter (fun j : Fin n => T j ≤ t)).card, ζ i

end TransitoryQueue


