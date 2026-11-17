-- Prove2me | Definitions.Def_CutRankSched_Supplement_gSpaceBound
-- name    : CutRankSched_Supplement_gSpaceBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:47:48.089004+00:00
-- url     : https://prove2.me/theorems/287188be-cb52-4841-8229-06c16697063f
-- title:
--   The space bound $2^{Cr^2}(L+1)^rL^{w^\circ}\cdot C(n+m+1)^C$
-- statement:
--   For a constant $C$, an instance and a budget $L$, with $r=\mathrm{rank}_{\mathbb F_2}A$,
--   $$
--   2^{Cr^2}(L+1)^r L^{w^\circ}\cdot C(n+m+1)^C ,
--   $$
--   the space bound $2^{O(r^2)}(L+1)^rL^{w^\circ}\,\mathrm{poly}(n,m)$ of Theorem 5.1 with one constant.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 5.1, p.9

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_A
import Definitions.Def_CutRankSched_width

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- The space bound `2^{O(r²)}(L+1)^r L^{w°} poly(n, m)` of Theorem 5.1 (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 5.1, p.9)
with one constant `C`: `2^{Cr²}(L+1)^r L^{w°}·C(n+m+1)^C`, `r = rank_{𝔽₂} A`. -/
noncomputable def gSpaceBound (C : ℕ) (I : Instance) (L : ℕ) : ℕ :=
  2 ^ (C * (A I).rank ^ 2) * (L + 1) ^ (A I).rank * L ^ width I * (C * (I.n + I.m + 1) ^ C)

end Supplement

end CutRankSched


