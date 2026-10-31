-- Prove2me | Definitions.Def_MultiServerAppt_waitMat
-- name    : MultiServerAppt_waitMat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:00:10.22519+00:00
-- url     : https://prove2.me/theorems/0abb3861-14c0-492a-925b-e0332ea53aae
-- title:
--   The waiting matrix as a block of $S_{s+i}$, Eq. (14)
-- statement:
--   The matrix $S_i^{\mathrm{wait}}$ read off as the upper left block of $S_{s+i}$ in Eq. (14).
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (14), p.13

import Mathlib
import Definitions.Def_MultiServerAppt_sysMat

open Matrix

namespace MultiServerAppt

/-- The waiting block `S_i^wait` as the upper-left block of `S_{s+i}` in Eq. (14). Kuiper–Lee,
Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (14), p.13.

**Formalization Note** It equals `Swait α S s i` by `Matrix.toBlocks_fromBlocks₁₁`. -/
def waitMat {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ) (S : Matrix ι ι ℝ) (s i : ℕ) :
    Matrix (SatState ι s i) (SatState ι s i) ℝ :=
  (sysMat α S s i).toBlocks₁₁

end MultiServerAppt


