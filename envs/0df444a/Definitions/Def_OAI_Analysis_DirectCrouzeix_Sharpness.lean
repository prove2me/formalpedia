-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
-- name    : OAI_Analysis_DirectCrouzeix_Sharpness
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:28:52.400037+00:00
-- url     : https://prove2.me/theorems/2932e9ca-ad33-4b2f-84c6-dc4ba67e0bf9
-- title:
--   The nilpotent $2\times2$ example showing that the constant $2$ cannot be lowered
-- statement:
--   For $n,m,d\in\mathbb{N}$, a complex $n\times n$ matrix $A$ and complex $m\times m$ matrices $B_0,\dots,B_d$, write
--
--   $$
--   p_B(z)=\sum_{k=0}^{d}z^{k}B_k\quad(z\in\mathbb{C}),\qquad p_B[A]=\sum_{k=0}^{d}A^{k}\otimes B_k ,
--   $$
--
--   where $A\otimes B$ is the Kronecker product, an $nm\times nm$ matrix with entries $(A\otimes B)_{(i,j),(i',j')}=A_{ii'}B_{jj'}$. Let $W(A)=\{\langle u,Au\rangle:u\in\mathbb{C}^{n},\ \|u\|=1\}$ be the numerical range of $A$, and let $\|\cdot\|$ denote the operator norm induced by the Euclidean norms. The module fixes the following data, with $n=2$, $m=1$ and $d=1$:
--
--   1. **Example matrix.**
--   $$
--   S=\begin{pmatrix}0&2\\0&0\end{pmatrix}\in M_2(\mathbb{C}).
--   $$
--
--   2. **Example coefficients.** $B_0=0$ and $B_1=1$, both $1\times1$ matrices, so that the polynomial is $p_B(z)=z$.
--
--   It records the two evaluation rules $p_B(z)=z\,I_1$ for every $z\in\mathbb{C}$ and $p_B[S]=S\otimes I_1$.
--
--   These data form the extremal example for the matrix-coefficient Crouzeix-type bound $\|p_B[A]\|\le c\,\sup_{z\in W(A)}\|p_B(z)\|$. For a unit vector $u=(u_1,u_2)$ one has $\langle u,Su\rangle=2\,\overline{u_1}\,u_2$ and $|2\,\overline{u_1}\,u_2|\le|u_1|^{2}+|u_2|^{2}=1$, so $W(S)$ is contained in (in fact equal to) the closed unit disk and $\sup_{z\in W(S)}\|p_B(z)\|\le1$, whereas $\|S\otimes I_1\|=\|S\|=2$. Hence no constant $c<2$ can satisfy such a bound for all $A$ and $B$.
--
--   **Formalization Note** `sharpnessMatrix` is `!![0, 2; 0, 0]` and `sharpnessCoefficients : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ` is `![0, 1]`. The simplification lemmas `sharpness_polynomialValue` and `sharpness_tensorEvaluation` are stated for the shared definitions `polynomialValue` and `tensorEvaluation` with `d := 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/Sharpness.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/Sharpness.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DirectCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs

namespace OAI

universe u_46

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

def sharpnessMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, 2; 0, 0]

def sharpnessCoefficients : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ := ![0, 1]

@[simp] theorem sharpness_polynomialValue (z : ℂ) :
    polynomialValue (d := 1) sharpnessCoefficients z = z • 1 := by
  simp [polynomialValue, sharpnessCoefficients, Fin.sum_univ_two]

@[simp] theorem sharpness_tensorEvaluation :
    tensorEvaluation (d := 1) sharpnessMatrix sharpnessCoefficients =
      sharpnessMatrix ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  simp [tensorEvaluation, sharpnessCoefficients, Fin.sum_univ_two]

end DirectCrouzeix

end

end OAI


