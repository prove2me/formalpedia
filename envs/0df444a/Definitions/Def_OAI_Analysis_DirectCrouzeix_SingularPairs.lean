-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
-- name    : OAI_Analysis_DirectCrouzeix_SingularPairs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:27:30.412069+00:00
-- url     : https://prove2.me/theorems/3e43d54e-301c-4b4c-b3a2-36935773db63
-- title:
--   Reshaping a vector of $\mathbb{C}^{n}\otimes\mathbb{C}^{m}$ into an $n\times m$ matrix
-- statement:
--   Let $n,m\in\mathbb{N}$ and let $\ell^{2}(\{1,\dots,n\}\times\{1,\dots,m\})$ be the Euclidean space of complex vectors $x=(x_{(i,j)})$ indexed by pairs $(i,j)$; this is the space $\mathbb{C}^{n}\otimes\mathbb{C}^{m}\cong\mathbb{C}^{nm}$ on which Kronecker products $A\otimes C$ of an $n\times n$ matrix $A$ and an $m\times m$ matrix $C$ act. For such a vector $x$ the module defines the $n\times m$ matrix
--
--   $$
--   \operatorname{mat}(x)_{ij}=x_{(i,j)},\qquad 1\le i\le n,\ 1\le j\le m .
--   $$
--
--   It also records that $\operatorname{mat}$ inverts the entry-vector map: if $\operatorname{vec}(M)$ denotes the vector with coordinates $\operatorname{vec}(M)_{(i,j)}=M_{ij}$, then
--
--   $$
--   \operatorname{vec}\big(\operatorname{mat}(x)\big)=x\qquad\text{for every vector } x .
--   $$
--
--   Consequently $\|\operatorname{mat}(x)\|_{\mathrm{HS}}=\|x\|$, where $\|M\|_{\mathrm{HS}}=\big(\sum_{i,j}|M_{ij}|^{2}\big)^{1/2}$ is the Hilbert–Schmidt norm, so unit vectors correspond to matrices of Hilbert–Schmidt norm one. In the development this is used to convert a pair of unit singular vectors $x,y$ of a matrix $T$ acting on $\mathbb{C}^{n}\otimes\mathbb{C}^{m}$, with $Tx=\|T\|\,y$ and $T^{*}y=\|T\|\,x$, into matrices $X=\operatorname{mat}(x)$ and $Y=\operatorname{mat}(y)$, so that $\|T\|=\langle y,Tx\rangle$ can be computed through matrix compressions $Y^{*}(\cdot)X$.
--
--   **Formalization Note** `matrixify x` is `fun i j => x (i, j)` for `x : EuclideanSpace ℂ (Fin n × Fin m)`, and the simplification lemma `hsVector_matrixify` states `hsVector (matrixify x) = x`, where `hsVector` is the entry-vector map.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/SingularPairs.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/SingularPairs.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DirectCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt

namespace OAI

universe u_37 u_38 u_39 u_40

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

def matrixify {n m : ℕ} (x : EuclideanSpace ℂ (Fin n × Fin m)) :
    Matrix (Fin n) (Fin m) ℂ := fun i j => x (i, j)

@[simp] theorem hsVector_matrixify {n m : ℕ} (x : EuclideanSpace ℂ (Fin n × Fin m)) :
    hsVector (matrixify x) = x := by
  apply WithLp.ofLp_injective
  rfl

end DirectCrouzeix

end

end OAI


