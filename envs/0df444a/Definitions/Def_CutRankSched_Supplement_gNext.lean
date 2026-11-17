-- Prove2me | Definitions.Def_CutRankSched_Supplement_gNext
-- name    : CutRankSched_Supplement_gNext
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:44:51.50028+00:00
-- url     : https://prove2.me/theorems/9c93457d-1e8a-417f-8d53-6c3d63ba97e9
-- title:
--   The update (8) of the global-rank DP
-- statement:
--   After event $i=k+1$ passes the tests with layer $t$, the successor state has
--   $$
--   V^{k+1}_s=\begin{cases} V^k_s+\mathrm{span}\{v_i\}, & s\le t,\\ V^k_s, & s>t,\end{cases}\qquad v_i=B_{i,*}^{\mathsf T}\in\mathbb F_2^r ,
--   $$
--   a subspace sum (8), and the frontier labelling keeps the labels of old events that remain in $F^\circ_{k+1}$, inserts $\ell(i)=t$ if $i\in F^\circ_{k+1}$, and forgets all other labels (Section 5.1).
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 5.2, update (8), p.9, and Section 5.1, p.8

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_frontier
import Definitions.Def_CutRankSched_Supplement_GState

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- The successor state of the global-rank DP after placing event `i = k + 1` in layer `t`
(Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §5.2, update (8), p.9, and the frontier rule of §5.1, p.8):
`V^{k+1}_s = V^k_s + span{v_i}` for `s ≤ t` and `V^k_s` for `s > t`, where `v_i = B_{i,*}ᵀ`;
the labels of old events remaining in `F°_{k+1}` are kept, `(i, t)` is added if
`i ∈ F°_{k+1}`, all others are forgotten. -/
noncomputable def gNext (I : Instance) {r : ℕ} (L : ℕ) (B : Matrix (Fin I.n) (Fin r) (ZMod 2))
    (i : Fin I.n) (st : GState I r L) (t : Fin L) : GState I r L :=
  (fun s => if s ≤ t then st.1 s ⊔ Submodule.span (ZMod 2) {B i} else st.1 s,
    fun j => if j ∈ frontier I (i.val + 1) then (if j = i then some t else st.2 j) else none)

end Supplement

end CutRankSched


