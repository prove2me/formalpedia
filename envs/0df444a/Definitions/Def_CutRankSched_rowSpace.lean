-- Prove2me | Definitions.Def_CutRankSched_rowSpace
-- name    : CutRankSched_rowSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:34:06.853532+00:00
-- url     : https://prove2.me/theorems/1409bbfd-1804-4696-bb53-d92e6288920b
-- title:
--   Row space $R_k=\operatorname{rowspan}(A_k)$
-- statement:
--   The **cut row space** at cut $k$ is the row space of the cross matrix,
--   $$
--   R_k = \operatorname{rowspan}(A_k) = \operatorname{span}\{\, a^{(k)}_j : j \le k \,\} \subseteq \mathbb F_2^{\,n-k}, \qquad q_k = \dim R_k \le \kappa_\pi .
--   $$
--
--   **Formalization Note** In the zero-padded encoding of the signatures.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.3, p.5; Section 5.3, p.9

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_signature

set_option autoImplicit false

namespace CutRankSched

/-- The row space `R_k = rowspan(A_k)` at cut `k`, spanned by the signatures `a^{(k)}_j` of the
events `j ≤ k` (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.3, p.5, and §5.3, p.9); `q_k = dim R_k`.

**Formalization Note** In the zero-padded encoding of `signature`. -/
def rowSpace (I : Instance) (k : ℕ) : Submodule (ZMod 2) (Fin I.n → ZMod 2) :=
  Submodule.span (ZMod 2) {v | ∃ j : Fin I.n, j.val < k ∧ v = signature I k j}

end CutRankSched


