-- Prove2me | Definitions.Def_MultiCollQ_deltaN
-- name    : MultiCollQ_deltaN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:33.429042+00:00
-- url     : https://prove2.me/theorems/eaea5ce6-40c8-412d-b2ba-7f9b09780831
-- title:
--   The CPO simulation error $\delta_N(T)$
-- statement:
--   For integers $N,T$ the compressed-permutation-oracle simulation error is
--
--   $$
--   \delta_N(T)=\frac{60T}{\sqrt{N-T+1}}+\frac{T(T+1)}{2(N-2T+1)}.
--   $$
--
--   It bounds the distance between the compressed and the purified joint states after $T$ forward queries when $N\ge3$ and $3T-1\le N$ (Lemma 2.4, the referenced item `CompPermOracle.eq_31`), and enters Lemma 2.5 and Theorem 2.7.
--
--   **Formalization Note** Computed in $\mathbb R$. Every use has $3T-1\le N$, where both denominators are positive.
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; PDF sha256 e20a0870…), (2.6), p.13

import Mathlib

namespace MultiCollQ

/-- The CPO simulation error `δ_N(T) = 60T/√(N − T + 1) + T(T + 1)/(2(N − 2T + 1))` (Peng, Hou,
Dong, manuscript (Oct. 2026), (2.6), p.13).

**Formalization Note.** Computed in `ℝ`. Every use has `3T − 1 ≤ N`, where both denominators are
positive. -/
noncomputable def deltaN (N T : ℕ) : ℝ :=
  60 * (T : ℝ) / Real.sqrt ((N : ℝ) - T + 1) + (T : ℝ) * ((T : ℝ) + 1) / (2 * ((N : ℝ) - 2 * T + 1))

end MultiCollQ


