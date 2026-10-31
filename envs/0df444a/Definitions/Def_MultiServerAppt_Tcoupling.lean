-- Prove2me | Definitions.Def_MultiServerAppt_Tcoupling
-- name    : MultiServerAppt_Tcoupling
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:48.305546+00:00
-- url     : https://prove2.me/theorems/c3abe623-f94a-4528-a756-55eab2609bc6
-- title:
--   The block $T_s^{(s)}$ of Eq. (14)
-- statement:
--   This is the upper right block of Eq. (14), from the saturated to the unsaturated states. Its only nonzero block is $T^{(s)}$, from $j=s+1$ to $j=s$.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eqs. (13), (14), p.13

import Mathlib
import Definitions.Def_MultiServerAppt_Tblock
import Definitions.Def_MultiServerAppt_State

namespace MultiServerAppt

/-- The block `T_s^(s)` of Eq. (14) from the saturated to the unsaturated states: its only nonzero
block is `T^(s)` from `j = s + 1` (`q = 0`) to `j = s` (`ξ + 1 = s`). Kuiper–Lee, Appointment
Scheduling for Multiple Servers, SSRN 3975471, Eqs. (13), (14), p.13.

**Formalization Note** `Fin.cast` renames `Fin s` to `Fin (ξ + 1)` under the proof `ξ + 1 = s`. -/
def Tcoupling {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ) (S : Matrix ι ι ℝ) (s i : ℕ) :
    Matrix (SatState ι s i) (UnsatState ι s) ℝ :=
  Matrix.of fun p q =>
    if h : (p.1 : ℕ) = 0 ∧ (q.1 : ℕ) + 1 = s then
      Tblock α S s p.2 (fun l => q.2 (Fin.cast h.2.symm l))
    else 0

end MultiServerAppt


