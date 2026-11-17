-- Prove2me | Definitions.Def_CutRankSched_Supplement_Dcov
-- name    : CutRankSched_Supplement_Dcov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:48:49.474643+00:00
-- url     : https://prove2.me/theorems/e7080769-025c-4750-85e4-da3b8088737d
-- title:
--   The transitive reduction $D_{\mathrm{cov}}$ of the anticommutation DAG
-- statement:
--   Let $D$ be the DAG on the events with an arc $i\to j$ whenever $i<j$ and $A_{ij}=1$. Its **transitive reduction** $D_{\mathrm{cov}}$ has an arc $i\to j$ exactly when $j$ is reachable from $i$ in $D$ and there is no $k$ with $i\leadsto k\leadsto j$: the cover pairs of the reachability order.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.2, p.4, and Section 3.4, p.5

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_A

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- The transitive reduction `D_cov` of the anticommutation DAG `D` (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.2, p.4, and §3.4,
p.5): `D` has an arc `i → j` iff `i < j` and `A_ij = 1`; `(i, j)` is an arc of `D_cov` iff `j` is
reachable from `i` in `D` and no `k` has `i ⇝ k ⇝ j` (a cover pair of the reachability order). -/
def Dcov (I : Instance) (i j : Fin I.n) : Prop :=
  Relation.TransGen (fun a b : Fin I.n => a < b ∧ A I a b = 1) i j ∧
    ¬ ∃ k, Relation.TransGen (fun a b : Fin I.n => a < b ∧ A I a b = 1) i k ∧
      Relation.TransGen (fun a b : Fin I.n => a < b ∧ A I a b = 1) k j

end Supplement

end CutRankSched


