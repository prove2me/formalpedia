-- Prove2me | Definitions.Def_NestedLogitAssort_General_val10
-- name    : NestedLogitAssort_General_val10
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:48:34.830387+00:00
-- url     : https://prove2.me/theorems/64adecdb-bc09-4b61-97ab-dd8fed7413e5
-- title:
--   Objective of the inner maximization in (10)
-- statement:
--   For a nest $i$, a capacity $\epsilon\ge0$ and a number $x$, this is
--
--   $$
--   (v_{i0}+\epsilon)^{\gamma_i}\left[\frac{K_i(\epsilon)}{v_{i0}+\epsilon}-x\right],
--   $$
--
--   the objective whose maximum over $\epsilon\ge0$ bounds $y_i$ in the knapsack reformulation (10) of problem (3).
--
--   **Formalization Note** Real powers with $0^0=1$ and $a/0=0$; the base vanishes only for $v_{i0}=\epsilon=0$, where $K_i(0)=0$ for nonnegative weights.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, eq. (10), p. 22

import Mathlib
import Definitions.Def_NestedLogitAssort_General_K

namespace NestedLogitAssort.General

/-- **The objective `(v_{i0} + ϵ_i)^{γ_i} [K_i(ϵ_i)/(v_{i0} + ϵ_i) − x]` of the inner maximization in (10).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, eq. (10), p. 22.

**Formalization Note.** `Real.rpow` (`0 ^ 0 = 1`, `0 ^ γ = 0` for `γ ≠ 0`) and `a / 0 = 0`. The base
`v_{i0} + ϵ_i` vanishes only at `v_{i0} = ϵ_i = 0`, where, for nonnegative weights, `K_i(0) = 0`,
so the bracket is `−x`. -/
noncomputable def val10 {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (ε x : ℝ) : ℝ :=
  (I.w0 i + ε) ^ (I.γ i) * (K I i ε / (I.w0 i + ε) - x)

end NestedLogitAssort.General


