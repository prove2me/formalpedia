-- Prove2me | Definitions.Def_CutRankSched_next
-- name    : CutRankSched_next
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:35:15.515454+00:00
-- url     : https://prove2.me/theorems/bfd4197c-90d4-447a-a2be-f05d9b0021c5
-- title:
--   Successor state: update (11) and introduce/forget
-- statement:
--   After a legal trial layer $t$ for event $i = k+1$, Algorithm 1 moves to the state
--
--   1. $U'_s = \rho_k(U_s) + \mathbf 1_{\{s \le t\}} \operatorname{span}\{b_i\}$ for every $s$ (update (11), line 14), where $\rho_k$ is applied to the whole subspace also for $s > t$;
--   2. $\ell'$: keep the old labels of events in $F^\circ_{k+1}$, add $(i, t)$ if $i \in F^\circ_{k+1}$, and forget all others (line 15).
--
--   **Formalization Note** In the zero-padded encoding, $b_i$ is the signature of $i$ at cut $k+1$.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Algorithm 1, lines 14–15, p.10; Eq. (11), p.9; Section 5.1, p.8

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_State
import Definitions.Def_CutRankSched_frontier
import Definitions.Def_CutRankSched_signature
import Definitions.Def_CutRankSched_proj

set_option autoImplicit false

namespace CutRankSched

/-- The successor state of Algorithm 1 after placing event `i = k + 1` in layer `t`
(Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Algorithm 1 lines 14–15, p.10; update (11), p.9; introduce/forget rule, p.8):
`U'_s = ρ_k(U_s) + 1_{s ≤ t} span{b_i}` for every `s`, and the labels of the old events that
remain in `F°_{k+1}` are kept, `(i, t)` is added if `i ∈ F°_{k+1}`, all others are forgotten.

**Formalization Note** `ρ_k` is `proj n k` on the zero-padded space, applied to the whole subspace
for every `s` (also `s > t`); `b_i = signature I (k+1) i`. -/
noncomputable def next (I : Instance) (L : ℕ) (i : Fin I.n) (st : State I L) (t : Fin L) :
    State I L :=
  (fun s => (st.1 s).map (proj I.n i.val) ⊔
      (if s ≤ t then Submodule.span (ZMod 2) {signature I (i.val + 1) i} else ⊥),
    fun j => if j ∈ frontier I (i.val + 1) then (if j = i then some t else st.2 j) else none)

end CutRankSched


