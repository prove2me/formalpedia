-- Prove2me | Definitions.Def_CutRankSched_Residual
-- name    : CutRankSched_Residual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:32:45.014227+00:00
-- url     : https://prove2.me/theorems/7be326dd-c9e1-48e0-97d7-61761aa31eb6
-- title:
--   Residual exposure-conflict edges $E(X^\circ)=E_X\setminus E_{\mathrm{anti}}$
-- statement:
--   The **residual exposure-conflict graph** $X^\circ$ has edge set
--   $$
--   E(X^\circ) = E_X \setminus E_{\mathrm{anti}}, \qquad E_{\mathrm{anti}} = \{\, \{i, j\} : A_{ij} = 1 \,\},
--   $$
--   that is, the pairs of distinct events whose exposure regions overlap and which **commute** ($A_{ij} = 0$). It is not the anticommuting pairs.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.2, p.4

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_A
import Definitions.Def_CutRankSched_Overlap

set_option autoImplicit false

namespace CutRankSched

/-- The residual exposure-conflict edges `E(X°) = E_X ∖ E_anti` (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.2, p.4): pairs of
distinct events with overlapping exposure regions that **commute** (`A_ij = 0`). -/
def Residual (I : Instance) (i j : Fin I.n) : Prop :=
  Overlap I i j ∧ A I i j = 0

end CutRankSched


