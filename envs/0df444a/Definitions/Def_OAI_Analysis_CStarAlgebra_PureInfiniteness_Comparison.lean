-- Prove2me | Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
-- name    : OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:20:38.101584+00:00
-- url     : https://prove2.me/theorems/3a57e731-9d00-4484-b7e3-899e44369db5
-- title:
--   Cuntz comparison of matrices over a $C^*$-algebra and properly infinite elements
-- statement:
--   Let $A$ be a $C^*$-algebra, not necessarily unital, ordered by its positive cone: $a\le b$ means that $b-a$ is self-adjoint with spectrum in $[0,\infty)$. For natural numbers $m,n$ let $A^{m\times n}$ be the set of $m\times n$ matrices with entries in $A$, let $M_n(A)=A^{n\times n}$ carry its $C^*$-norm, and for $r\in A^{m\times n}$ let $r^*\in A^{n\times m}$ be the conjugate transpose, $(r^*)_{ij}=(r_{ji})^*$.
--
--   1. **Cuntz subequivalence of matrices.** For $d\in M_n(A)$ and $v\in M_m(A)$, write $d\precsim v$ if there is a sequence $(r_j)_{j\in\mathbb{N}}$ in $A^{m\times n}$ with
--
--      $$
--      r_j^*\,v\,r_j\longrightarrow d\qquad(j\to\infty)
--      $$
--
--      in $M_n(A)$. Convergence in the $C^*$-norm of $M_n(A)$ is the same as entrywise convergence.
--
--   2. **Properly infinite elements.** An element $h\in A$ is properly infinite if
--
--      $$
--      \begin{pmatrix} h & 0\\ 0 & h\end{pmatrix}\precsim (h),
--      $$
--
--      that is, there are row vectors $r_j\in A^{1\times 2}$ with $r_j^*\,h\,r_j\to\operatorname{diag}(h,h)$ in $M_2(A)$; here $(h)\in M_1(A)$ is the $1\times1$ matrix with entry $h$.
--
--   3. **Property P.** $A$ has property P if every positive $h\in A$ is properly infinite.
--
--   4. **Block-diagonal matrices.** For $x\in A^{m\times n}$ and $y\in A^{p\times q}$,
--
--      $$
--      x\oplus y=\begin{pmatrix} x & 0\\ 0 & y\end{pmatrix}\in A^{(m+p)\times(n+q)},
--      $$
--
--      with $x$ occupying the first $m$ rows and the first $n$ columns.
--
--   5. **Diagonal amplification.** For $n\in\mathbb{N}$ and $h\in A$, $h^{\oplus n}=\operatorname{diag}(h,\dots,h)\in M_n(A)$ is the diagonal matrix with $n$ copies of $h$.
--
--   These are the finite-matrix forms of Cuntz comparison used throughout the development. A properly infinite $h$ is shown there to dominate any number of copies of itself, $h^{\oplus n}\precsim(h)$ for every $n$, and property P in the form given here is the hypothesis from which the approximate diagonalization property of $A$ (for positive $a,b$, any $c$ and $\varepsilon>0$ there are $s,t$ with $\|s^*as-a\|$, $\|t^*bt-b\|$ and $\|s^*ct\|$ all less than $\varepsilon$) and strong pure infiniteness are derived. A variant of proper infiniteness phrased in the stabilization of $A$ (the completed union of the matrix algebras $M_n(A)$) implies the version given here.
--
--   **Formalization Note** Lean names: `FiniteCuntzLE d v`, for square matrices `d` and `v` of type `CStarMatrix` over `A` indexed by `Fin n` and `Fin m`, with a witness sequence of $m\times n$ matrices and convergence along `atTop`; `ProperlyInfinite h := FiniteCuntzLE (doubleCorner h) (scalarCorner h)`, using the $2\times2$ diagonal and $1\times1$ matrices of the base definitions; `PropertyP`; `matrixBlock x y`, built from `Matrix.fromBlocks` reindexed along `finSumFinEquiv`; and `diagonalCorner n h`. The order is Mathlib's spectral order. These names live in the namespace `MainGap` and are distinct from the stabilization-based `ProperlyInfinite` and `PropertyP` of `MainGap.Manuscript`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Comparison.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Comparison.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the IndividualStrongInfiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

attribute [local instance] OAI.MainGap.positivityOrder
attribute [local instance] OAI.MainGap.positivityStarOrder
def FiniteCuntzLE {m n : ℕ} (d : CStarMatrix (Fin n) (Fin n) A)
    (v : CStarMatrix (Fin m) (Fin m) A) : Prop :=
  ∃ r : ℕ → CStarMatrix (Fin m) (Fin n) A,
    Tendsto (fun j => (r j).conjTranspose * v * r j) atTop (𝓝 d)

def ProperlyInfinite (h : A) : Prop :=
  FiniteCuntzLE (doubleCorner h) (scalarCorner h)

def PropertyP (A : Type*) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ h : A, 0 ≤ h → ProperlyInfinite h

def matrixBlock {m n p q : ℕ} (x : CStarMatrix (Fin m) (Fin n) A)
    (y : CStarMatrix (Fin p) (Fin q) A) : CStarMatrix (Fin (m+p)) (Fin (n+q)) A :=
  CStarMatrix.ofMatrix ((Matrix.fromBlocks (CStarMatrix.ofMatrix.symm x) 0 0 (CStarMatrix.ofMatrix.symm y)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm)

def diagonalCorner (n : ℕ) (h : A) : CStarMatrix (Fin n) (Fin n) A :=
  CStarMatrix.ofMatrix (Matrix.diagonal (fun _ => h))

end MainGap

end

end OAI


