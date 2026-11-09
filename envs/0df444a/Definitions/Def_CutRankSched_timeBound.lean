-- Prove2me | Definitions.Def_CutRankSched_timeBound
-- name    : CutRankSched_timeBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:35:49.639899+00:00
-- url     : https://prove2.me/theorems/54e41dd2-d676-498c-adaf-7297eea204e3
-- title:
--   Time bound $2^{C\kappa_\pi^2}(L+1)^{\kappa_\pi}L^{w^\circ+1}\cdot C(n+m+1)^C$
-- statement:
--   For a constant $C$, the **time bound** is
--   $$
--   T_C(I, L) = 2^{C\kappa_\pi^2}\,(L+1)^{\kappa_\pi}\,L^{w^\circ+1} \cdot C\,(n+m+1)^C ,
--   $$
--   the form $2^{O(\kappa_\pi^2)}(L+1)^{\kappa_\pi}L^{w^\circ+1}\operatorname{poly}(n, m)$ of Theorem 5.2 with one constant $C$ for both the $O(\cdot)$ and the polynomial.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 5.2, p.10

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_cutRank
import Definitions.Def_CutRankSched_width

set_option autoImplicit false

namespace CutRankSched

/-- The running-time bound `T_cut = 2^{O(κ_π²)} (L+1)^{κ_π} L^{w°+1} poly(n, m)` of Theorem 5.2
(Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 5.2, p.10) with one constant `C`: `2^{Cκ_π²} (L+1)^{κ_π} L^{w°+1} · C(n+m+1)^C`. -/
noncomputable def timeBound (C : ℕ) (I : Instance) (L : ℕ) : ℕ :=
  2 ^ (C * cutRank I ^ 2) * (L + 1) ^ cutRank I * L ^ (width I + 1) * (C * (I.n + I.m + 1) ^ C)

end CutRankSched


