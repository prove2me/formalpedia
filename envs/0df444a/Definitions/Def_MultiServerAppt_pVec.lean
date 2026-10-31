-- Prove2me | Definitions.Def_MultiServerAppt_pVec
-- name    : MultiServerAppt_pVec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:32.142623+00:00
-- url     : https://prove2.me/theorems/f8a96eda-08db-47ff-9481-b942ed3d56c8
-- title:
--   The vector $p^{(s+i)}(u)$, Eqs. (11), (12)
-- statement:
--   The row vector on the transient states after client $s+i$:
--
--   $$p^{(s+i)}(u)=\alpha_{s+i}\exp(S_{s+i}\,u).$$
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eqs. (11), (12), p.12, and p.14

import Mathlib
import Definitions.Def_MultiServerAppt_alphaSys

open Matrix

namespace MultiServerAppt

/-- The row vector `p^(s+i)(u) = α_{s+i} exp(S_{s+i} u)` of Eqs. (11), (12) on the transient states.
Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eqs. (11), (12), p.12 and
p.14 ("described by PH(α_{s+i}, S_{s+i})"). -/
noncomputable def pVec {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ) (S : Matrix ι ι ℝ)
    (s : ℕ) (x : ℕ → ℝ) (i : ℕ) (u : ℝ) : State ι s i → ℝ :=
  alphaSys α S s x i ᵥ* NormedSpace.exp (u • sysMat α S s i)

end MultiServerAppt


