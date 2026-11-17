-- Prove2me | Definitions.Def_CutRankSched_Supplement_gTimeBound
-- name    : CutRankSched_Supplement_gTimeBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:47:15.447353+00:00
-- url     : https://prove2.me/theorems/9b496e17-3bce-4119-aa10-59e487e2c999
-- title:
--   The time bound $2^{Cr^2}(L+1)^rL^{w^\circ+1}\cdot C(n+m+1)^C$
-- statement:
--   For a constant $C$, an instance and a budget $L$, with $r=\mathrm{rank}_{\mathbb F_2}A$ and $w^\circ$ the vertex-separation width of $X^\circ$ in the given order,
--   $$
--   2^{Cr^2}(L+1)^r L^{w^\circ+1}\cdot C(n+m+1)^C .
--   $$
--   This is the time bound $2^{O(r^2)}(L+1)^rL^{w^\circ+1}\,\mathrm{poly}(n,m)$ of Theorem 5.1 with one constant.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 5.1, p.9

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_A
import Definitions.Def_CutRankSched_width

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- The running-time bound `2^{O(r²)}(L+1)^r L^{w°+1} poly(n, m)` of Theorem 5.1 (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878),
Theorem 5.1, p.9) with one constant `C`: `2^{Cr²}(L+1)^r L^{w°+1}·C(n+m+1)^C`, `r = rank_{𝔽₂} A`. -/
noncomputable def gTimeBound (C : ℕ) (I : Instance) (L : ℕ) : ℕ :=
  2 ^ (C * (A I).rank ^ 2) * (L + 1) ^ (A I).rank * L ^ (width I + 1) *
    (C * (I.n + I.m + 1) ^ C)

end Supplement

end CutRankSched


