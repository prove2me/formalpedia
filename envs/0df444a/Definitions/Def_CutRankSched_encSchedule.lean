-- Prove2me | Definitions.Def_CutRankSched_encSchedule
-- name    : CutRankSched_encSchedule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:29:40.018461+00:00
-- url     : https://prove2.me/theorems/16a8a579-5e04-4568-b0dd-dfc944066295
-- title:
--   Output encoding of a layer assignment
-- statement:
--   A layer assignment $\lambda$ is written as the list $\lambda_1, \dots, \lambda_n$ of its layers, each in binary, framed as a list.
--
--   **Formalization Note** The written layers are the 0-based values.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 5.2, p.10

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT

namespace CutRankSched

/-- The output encoding of a layer assignment `λ` (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 5.2, p.10, "a feasible
assignment can be recovered"): the list of layers `λ_1, …, λ_n` (0-based values), each in
binary (`countWord`), framed by `encodeList`. -/
def encSchedule {n L : ℕ} (lam : Fin n → Fin L) : List Bool :=
  Encoding.encodeList SqrtLogSpace.countWord (List.ofFn fun i => (lam i).val)

end CutRankSched


