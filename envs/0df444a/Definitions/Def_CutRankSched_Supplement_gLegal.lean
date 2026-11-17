-- Prove2me | Definitions.Def_CutRankSched_Supplement_gLegal
-- name    : CutRankSched_Supplement_gLegal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:44:17.043217+00:00
-- url     : https://prove2.me/theorems/b59ebcc3-ad44-4488-9ec9-bf2aafb0cae7
-- title:
--   The tests (7) and (5) of the global-rank DP
-- statement:
--   Let $A=BC$ be a rank factorization over $\mathbb F_2$ and $\varphi_i(u)=u^{\mathsf T}C_{*,i}$. When the DP processes event $i=k+1$ with trial layer $t$ from a state $((V_s)_s,\ell)$, it requires
--   $$
--   V_t\subseteq\ker\varphi_i \quad (7)\qquad\text{and}\qquad \ell(j)\neq t\ \text{ for all } j\in F^\circ_k \text{ with } \{j,i\}\in E(X^\circ)\quad(5).
--   $$
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 5.2, tests (7) and (5), pp.8–9

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Residual
import Definitions.Def_CutRankSched_frontier
import Definitions.Def_CutRankSched_Supplement_GState

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- The two tests of the global-rank DP for event `i = k + 1` and trial layer `t`
(Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §5.2, test (7) and test (5), pp.8–9): `V_t ⊆ ker φ_i`, where `φ_i(u) = uᵀ C_{*,i}`, and
`ℓ(j) ≠ t` for every `j ∈ F°_k` with `{j, i} ∈ E(X°)`.

**Formalization Note** The event is 0-based, `i : Fin n` with `k = i.val`. -/
def gLegal (I : Instance) {r : ℕ} (L : ℕ) (C : Matrix (Fin r) (Fin I.n) (ZMod 2)) (i : Fin I.n)
    (st : GState I r L) (t : Fin L) : Prop :=
  (∀ u ∈ st.1 t, dotProduct u (fun a => C a i) = 0) ∧
    ∀ j ∈ frontier I i.val, Residual I j i → st.2 j ≠ some t

end Supplement

end CutRankSched


