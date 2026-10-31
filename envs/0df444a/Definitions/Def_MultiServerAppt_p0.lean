-- Prove2me | Definitions.Def_MultiServerAppt_p0
-- name    : MultiServerAppt_p0
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:03:03.098988+00:00
-- url     : https://prove2.me/theorems/411d29cb-1419-451d-bdf8-4f52c5a1ec8a
-- title:
--   The empty-state probability $p_0^{(s+i)}(u)$
-- statement:
--   The probability of the empty absorbing state:
--
--   $$p_0^{(s+i)}(u)=1-p^{(s+i)}(u)\mathbf 1.$$
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.1, p.13

import Mathlib
import Definitions.Def_MultiServerAppt_pVec

namespace MultiServerAppt

/-- The probability `p_0^(s+i)(u) = 1 - p^(s+i)(u) 𝟙` of the empty absorbing state. Kuiper–Lee,
Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.1, p.13. -/
noncomputable def p0 {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ) (S : Matrix ι ι ℝ)
    (s : ℕ) (x : ℕ → ℝ) (i : ℕ) (u : ℝ) : ℝ :=
  1 - ∑ a, pVec α S s x i u a

end MultiServerAppt


