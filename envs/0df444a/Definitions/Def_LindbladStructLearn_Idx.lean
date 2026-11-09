-- Prove2me | Definitions.Def_LindbladStructLearn_Idx
-- name    : LindbladStructLearn_Idx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:47:59.703201+00:00
-- url     : https://prove2.me/theorems/4510f06f-8284-4899-95fc-a068de8343de
-- title:
--   Index set of the $k$-local terms
-- statement:
--   The index set of the vectors $x$, $E(x)$, $\mathcal F(x)$ and of the matrices $A_k$, $V_k$: the pairs $\overline P = (P_1,P_2)$ of $n$-qubit Paulis with $P_1 \ne I$ and $s_{\overline P} \le k$. Its size is the paper's $m = O(n^k)$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Notation 3.2, p.19; §3, p.18

import Mathlib
import Definitions.Def_LindbladStructLearn_pairSupport

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The index set of the vectors `x, E(x), F(x)` and of the matrices `A_k, V_k` (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e),
Notation 3.2, p.19, and §3, p.18): the `k`-local pairs `P̄ = (P₁,P₂)` with `P₁ ≠ I`
(`m = |Idx n k|`; "m = O(n^k)", p.42). -/
abbrev Idx (n k : ℕ) : Type :=
  {P : Pauli n × Pauli n // P.1 ≠ 0 ∧ (pairSupport P).card ≤ k}

end LindbladStructLearn


