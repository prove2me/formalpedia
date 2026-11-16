-- Prove2me | Definitions.Def_TriFormQ_Supplement_linSimonOracle
-- name    : TriFormQ_Supplement_linSimonOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:58:47.721173+00:00
-- url     : https://prove2.me/theorems/df69653b-f195-4457-b07c-63a78c8d9f47
-- title:
--   Linear Simon oracle function $x\mapsto Ax$
-- statement:
--   Let $A\in\mathbb F_q^{n\times n}$. In the **Linear Simon's problem** (Definition 3) the matrix $A$ is hidden, under the promise that $\mathrm{rk}(A)=n$ or $\mathrm{rk}(A)=n-1$, and the task is to decide which holds. A query is
--
--   $$O_{LS}:\ |x\rangle|z\rangle|w\rangle\ \mapsto\ |x\rangle|z+Ax\rangle|w\rangle,\qquad x,z\in\mathbb F_q^n,$$
--
--   with $x$ the query input, $z$ the query output and $w$ the workspace. This definition is the function $x\mapsto Ax$ that $O_{LS}$ evaluates.
--
--   It is the oracle of the target problem in the reduction of Theorem 10, through which the $\Omega(n)$ lower bound for the Linear Simon's problem transfers to linear isomorphism of trilinear forms.
--
--   **Formalization Note** An adaptive query algorithm with this oracle function queries the platform's standard oracle `QAlgorithms.xorOracle (linSimonOracle A)`, the permutation matrix of $(x,z)\mapsto(x,z+Ax)$ with addition in the group $\mathbb F_q^n$; the workspace is that of `QAlgorithms.QueryAlg`. This is exactly $O_{LS}$.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Definition 3, p.41 (PDF p.44)

import Definitions.Def_TriFormQ_TriForm
open Matrix

namespace TriFormQ.Supplement

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Definition 3, p.41 (PDF p.44):
"A quantum query for the Linear Simon's problem can be written as
O_LS : |x⟩|z⟩|w⟩ ↦ |x⟩|z + Ax⟩|w⟩, thinking of x ∈ 𝔽_q^n as the query input, z ∈ 𝔽_q^n as the
query output, and w as the workspace." The function `x ↦ Ax` that `O_LS` evaluates.

**Formalization Note.** An adaptive algorithm (`TriFormQ.AdaptiveAlg`) with oracle function
`linSimonOracle A` queries `QAlgorithms.xorOracle (linSimonOracle A)`, the permutation matrix of
`(x, z) ↦ (x, z + Ax)` with `z` in the additive group `𝔽_q^n`; the workspace `w` is the workspace of
`QAlgorithms.QueryAlg`, on which the oracle acts as the identity. This is exactly `O_LS`. -/
def linSimonOracle {F : Type} [Field F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F) :
    Vec F n → Vec F n :=
  fun x => A *ᵥ x

end TriFormQ.Supplement


