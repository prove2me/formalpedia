-- Prove2me | Definitions.Def_NestedLogitAssort_PartialCapture_val10
-- name    : NestedLogitAssort_PartialCapture_val10
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:45:56.795181+00:00
-- url     : https://prove2.me/theorems/fe5b61aa-6391-49b5-aed3-4f391a9290b7
-- title:
--   Objective $(v_{i0}+\epsilon_i)^{\gamma_i}[K_i(\epsilon_i)/(v_{i0}+\epsilon_i)-x]$ of problem (10)
-- statement:
--   For a nest $i$, a capacity $\epsilon$ and a real $x$, this is
--
--   $$
--   (v_{i0}+\epsilon)^{\gamma_i}\Bigl[\frac{K_i(\epsilon)}{v_{i0}+\epsilon}-x\Bigr],
--   $$
--
--   the function maximized over $\epsilon\ge 0$ in the second set of constraints of problem (10).
--
--   **Formalization Note** The power is `Real.rpow` and division by zero returns $0$. The base vanishes only when $v_{i0}=\epsilon=0$; for nonnegative weights $K_i(0)=0$ there, so the bracket is $-x$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, eq. (10), p. 22

import Mathlib
import Definitions.Def_NestedLogitAssort_PartialCapture_K

namespace NestedLogitAssort.PartialCapture

/-- **The objective `(v_{i0} + ϵ_i)^{γ_i} [K_i(ϵ_i)/(v_{i0} + ϵ_i) − x]` of the inner maximization in (10).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, eq. (10), p. 22.

**Formalization Note.** The power is `Real.rpow` (`0 ^ 0 = 1`, `0 ^ γ = 0` for `γ > 0`) and
`a / 0 = 0`. The base `v_{i0} + ϵ_i` vanishes only at `v_{i0} = ϵ_i = 0`, where, for nonnegative weights,
`K_i(0)` is a sum of terms with `v_{ij} = 0`, hence `0`, so the bracket is `−x`. -/
noncomputable def val10 {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (ε x : ℝ) : ℝ :=
  (I.w0 i + ε) ^ (I.γ i) * (K I i ε / (I.w0 i + ε) - x)

end NestedLogitAssort.PartialCapture


