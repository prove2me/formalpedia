-- Prove2me | Definitions.Def_MultiServerAppt_sysMat
-- name    : MultiServerAppt_sysMat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:58:53.122363+00:00
-- url     : https://prove2.me/theorems/b5e9d66f-a005-4a8d-87e5-4cfd8412cbd7
-- title:
--   The transition matrix $S_{s+i}$, Eqs. (8), (13), (14)
-- statement:
--   The transition matrix of the system after client $s+i$ is
--
--   $$S_{s+i}=\begin{pmatrix}S_i^{\mathrm{wait}} & T_s^{(s)}\\ 0 & S_s\end{pmatrix}.$$
--
--   For $i=0$ the saturated part is empty and this is $S_s$.
--
--   **Formalization Note** The entries are the page's, with $S^{(1)}=S$ in place of the misprinted $S^{(1)}=1$.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eqs. (8), (13), (14), pp.12-13

import Mathlib
import Definitions.Def_MultiServerAppt_Ss
import Definitions.Def_MultiServerAppt_Swait
import Definitions.Def_MultiServerAppt_Tcoupling

open Matrix

namespace MultiServerAppt

/-- The transition matrix `S_{s+i}` of the system after client `s + i` has arrived, in the block
form of Eq. (14). Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eqs. (8),
(13), (14), pp.12-13.

**Formalization Note** `i = 0` gives `S_s`: the saturated block is then empty. The entries are the
page's; the printed `S^(1) = 1` is corrected to `S^(1) = S` in `Sblock`. -/
def sysMat {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ) (S : Matrix ι ι ℝ) (s i : ℕ) :
    Matrix (State ι s i) (State ι s i) ℝ :=
  Matrix.fromBlocks (Swait α S s i) (Tcoupling α S s i) 0 (Ss S s)

end MultiServerAppt


