-- Prove2me | Definitions.Def_MultiServerAppt_waitAlpha
-- name    : MultiServerAppt_waitAlpha
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:24.303316+00:00
-- url     : https://prove2.me/theorems/683c4062-67a6-479f-8f57-ed6cb54e294c
-- title:
--   The start vector $\alpha_i^{\mathrm{wait}}$, Eq. (16)
-- statement:
--   The start vector $\alpha_i^{\mathrm{wait}}=p_{\mathrm{wait}}^{(s+i)}(0)$: the restriction of $\alpha_{s+i}$ to the saturated states, the blocks $j=s+i,\dots,s+1$ of Eq. (16).
--
--   **Formalization Note** $\exp(0)=I$ gives $p^{(s+i)}(0)=\alpha_{s+i}$, so restricting $\alpha_{s+i}$ is the same as restricting $p^{(s+i)}(0)$.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (16) and following display, p.14

import Mathlib
import Definitions.Def_MultiServerAppt_alphaSys

namespace MultiServerAppt

/-- The start vector `α_i^wait = p_wait^(s+i)(0)`: the restriction of `α_{s+i}` to the saturated
states, the blocks `j = s + i, …, s + 1` of Eq. (16). Kuiper–Lee, Appointment Scheduling for Multiple
Servers, SSRN 3975471, Eq. (16) and following display, p.14.

**Formalization Note** `exp(0) = 1` gives `p^(s+i)(0) = α_{s+i}`, so this is `p_wait^(s+i)(0)`. -/
noncomputable def waitAlpha {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ)
    (S : Matrix ι ι ℝ) (s : ℕ) (x : ℕ → ℝ) (i : ℕ) : SatState ι s i → ℝ :=
  fun p => alphaSys α S s x i (.inl p)

end MultiServerAppt


