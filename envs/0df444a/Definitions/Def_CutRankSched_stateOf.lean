-- Prove2me | Definitions.Def_CutRankSched_stateOf
-- name    : CutRankSched_stateOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:35:29.005635+00:00
-- url     : https://prove2.me/theorems/2c30cba8-52fa-453b-9dbb-c0dc83ccbe39
-- title:
--   State $((U^k_s)_s, \ell_k)$ determined by a partial assignment
-- statement:
--   A partial assignment $\lambda$ of the first $k$ events determines the state
--   $$
--   \bigl( (U^k_s)_{s=1}^L,\ \ell_k \bigr), \qquad \ell_k = \lambda|_{F^\circ_k},
--   $$
--   its descending flag (9) together with the layers of the frontier events $F^\circ_k$.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 5.3, p.9; Section 5.1, p.8

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_State
import Definitions.Def_CutRankSched_flagOf
import Definitions.Def_CutRankSched_frontier

set_option autoImplicit false

namespace CutRankSched

/-- The state `((U^k_s)_{s=1}^L, ℓ_k)` that a partial assignment `λ` determines at cut `k`
(Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §5.3, p.9, and §5.1, p.8): its flag (9) and its labels on the frontier `F°_k`. -/
noncomputable def stateOf (I : Instance) (L k : ℕ) (lam : Fin I.n → Fin L) : State I L :=
  (flagOf I L k lam, fun j => if j ∈ frontier I k then some (lam j) else none)

end CutRankSched


