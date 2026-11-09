-- Prove2me | Definitions.Def_CutRankSched_spaceBound
-- name    : CutRankSched_spaceBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:36:16.726255+00:00
-- url     : https://prove2.me/theorems/e6855a62-2d9b-446c-aa73-a234cd16a6f0
-- title:
--   Space bound $2^{C\kappa_\pi^2}(L+1)^{\kappa_\pi}L^{w^\circ}\cdot C(n+m+1)^C$
-- statement:
--   For a constant $C$, the **space bound** is
--   $$
--   S_C(I, L) = 2^{C\kappa_\pi^2}\,(L+1)^{\kappa_\pi}\,L^{w^\circ} \cdot C\,(n+m+1)^C ,
--   $$
--   the form $2^{O(\kappa_\pi^2)}(L+1)^{\kappa_\pi}L^{w^\circ}\operatorname{poly}(n, m)$ of Theorem 5.2 with one constant $C$.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 5.2, p.10

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_cutRank
import Definitions.Def_CutRankSched_width

set_option autoImplicit false

namespace CutRankSched

/-- The space bound `S_cut = 2^{O(κ_π²)} (L+1)^{κ_π} L^{w°} poly(n, m)` of Theorem 5.2
(Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 5.2, p.10) with one constant `C`: `2^{Cκ_π²} (L+1)^{κ_π} L^{w°} · C(n+m+1)^C`. -/
noncomputable def spaceBound (C : ℕ) (I : Instance) (L : ℕ) : ℕ :=
  2 ^ (C * cutRank I ^ 2) * (L + 1) ^ cutRank I * L ^ width I * (C * (I.n + I.m + 1) ^ C)

end CutRankSched


