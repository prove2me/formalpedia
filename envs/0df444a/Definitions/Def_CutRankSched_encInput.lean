-- Prove2me | Definitions.Def_CutRankSched_encInput
-- name    : CutRankSched_encInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:32:22.354177+00:00
-- url     : https://prove2.me/theorems/f7841e0b-269b-4cd0-80d2-203820f51996
-- title:
--   Machine input $\langle I, L\rangle$
-- statement:
--   The machine input for the question "is the instance feasible in $L$ rounds?" is the instance encoding followed by the budget $L$ written in **binary** (least significant bit first), framed as a two-element list.
--
--   Writing $L$ in binary is the standard input size; the time bound is polynomial in $L$, not in $\log L$.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Problem 3.2, p.5

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_encInstance

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT

namespace CutRankSched

/-- The machine input for the decision "is `I` feasible in `L` rounds?" (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Problem 3.2,
p.5): the instance encoding and the budget `L` in **binary** (`countWord`, least significant bit
first), framed by `encodeList`. -/
noncomputable def encInput (I : Instance) (L : ℕ) : List Bool :=
  Encoding.encodeList id [encInstance I, SqrtLogSpace.countWord L]

end CutRankSched


