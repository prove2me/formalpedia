-- Prove2me | Definitions.Def_MultiServerAppt_Swait
-- name    : MultiServerAppt_Swait
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:56.561901+00:00
-- url     : https://prove2.me/theorems/a3a6672a-a4a1-4886-8c3b-d1dcf2c270e2
-- title:
--   The waiting block $S_i^{\mathrm{wait}}$, Eqs. (13), (14)
-- statement:
--   The block $S_i^{\mathrm{wait}}$ acts on the saturated states. It is $S^{(s)}$ on each of its $i$ diagonal blocks, and $T^{(s)}$ from the block $q+1$ to the block $q$, when a server finishes and the first waiting client starts. Every other block is $0$.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eqs. (13), (14), p.13

import Mathlib
import Definitions.Def_MultiServerAppt_Sblock
import Definitions.Def_MultiServerAppt_Tblock
import Definitions.Def_MultiServerAppt_SatState

namespace MultiServerAppt

/-- The block `S_i^wait` of the saturated states: `S^(s)` on each of the `i` diagonal blocks, and
`T^(s)` from `q + 1` to `q`, when a server finishes and the first waiting client starts. Kuiper–Lee,
Appointment Scheduling for Multiple Servers, SSRN 3975471, Eqs. (13), (14), p.13. -/
def Swait {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ) (S : Matrix ι ι ℝ) (s i : ℕ) :
    Matrix (SatState ι s i) (SatState ι s i) ℝ :=
  Matrix.of fun p q =>
    if (p.1 : ℕ) = q.1 then Sblock S s p.2 q.2
    else if (p.1 : ℕ) = q.1 + 1 then Tblock α S s p.2 q.2
    else 0

end MultiServerAppt


