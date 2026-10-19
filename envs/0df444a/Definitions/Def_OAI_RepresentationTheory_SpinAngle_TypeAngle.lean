-- Prove2me | Definitions.Def_OAI_RepresentationTheory_SpinAngle_TypeAngle
-- name    : OAI_RepresentationTheory_SpinAngle_TypeAngle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T07:11:09.66762+00:00
-- url     : https://prove2.me/theorems/a7c5978b-45bf-4020-8e8b-43aaf5a16206
-- title:
--   Tensor-product square roots, inverse square roots and support projections of column and row densities on a set of cells
-- statement:
--   Fix an integer $q\ge1$ and the *signed spin alphabet* $S_q=\{1,\dots,q\}\times\{0,1\}$, whose second coordinate distinguishes the even sector ($0$) from the odd sector ($1$). An *even density* of order $q$ is a pair $A=(A_0,A_1)$ of positive semidefinite $q\times q$ complex matrices with $\operatorname{tr}A_0+\operatorname{tr}A_1=1$; its matrix is the block-diagonal density matrix
--   $$\rho(A)=A_0\oplus A_1\in\mathbb{C}^{S_q\times S_q},$$
--   with $A_0$ acting on the even sector and $A_1$ on the odd sector. For a nonempty finite set $C$ and a family $A=(A_j)_{j\in C}$ of even densities, the *mean* $\bar A=\frac{1}{|C|}\sum_{j\in C}A_j$ (taken in both components) is again an even density, and $\rho(\bar A)=\frac{1}{|C|}\sum_{j\in C}\rho(A_j)$.
--
--   For a Hermitian matrix $x$ with spectral decomposition $x=\sum_\lambda\lambda P_\lambda$ write
--   $$\sqrt{x}=\sum_{\lambda>0}\sqrt{\lambda}\,P_\lambda,\qquad x^{-1/2}=\sum_{\lambda>0}\lambda^{-1/2}P_\lambda,\qquad \operatorname{supp}x=\sum_{\lambda\ne0}P_\lambda .$$
--   For positive semidefinite $x$ these are the usual square root, the pseudo-inverse of $\sqrt{x}$, and the orthogonal projection onto the range of $x$. For a finite set $W$ and matrices $(x_w)_{w\in W}$ in $\mathbb{C}^{S_q\times S_q}$, the Kronecker product $\bigotimes_{w\in W}x_w$ is the matrix indexed by pairs of colourings $\xi,\eta\in S_q^{W}$ with entries $\prod_{w\in W}x_w(\xi_w,\eta_w)$; it acts on $(\mathbb{C}^{S_q})^{\otimes W}$, and $x^{\otimes W}$ denotes the case of equal factors.
--
--   Let $R$ and $C$ be finite sets of row and column indices and let $W\subseteq R\times C$ be a set of cells; a cell $w=(i,j)$ has row $i(w)=i$ and column $j(w)=j$. The module defines five operators on $(\mathbb{C}^{S_q})^{\otimes W}$.
--
--   1. **Column root.** For a family $A=(A_j)_{j\in C}$ of even densities, $\mathrm{colRoot}_W(A)=\bigotimes_{w\in W}\sqrt{\rho(A_{j(w)})}$: each cell carries the square root of the density of its column.
--   2. **Mean root.** For $C$ nonempty, $\mathrm{meanRoot}_W(A)=\big(\sqrt{\rho(\bar A)}\big)^{\otimes W}$.
--   3. **Mean inverse root.** For $C$ nonempty, $\mathrm{meanInvRoot}_W(A)=\big(\rho(\bar A)^{-1/2}\big)^{\otimes W}$.
--   4. **Mean support.** For $C$ nonempty, $\mathrm{meanSupp}_W(A)=\big(\operatorname{supp}\rho(\bar A)\big)^{\otimes W}$.
--   5. **Row root.** For a family $B=(B_i)_{i\in R}$ of even densities, $\mathrm{rowRoot}_W(B)=\bigotimes_{w\in W}\sqrt{\rho(B_{i(w)})}$: each cell carries the square root of the density of its row.
--
--   These operators are the square-root factors of the product states $\bigotimes_{w}\rho(A_{j(w)})$ and $\bigotimes_w\rho(B_{i(w)})$ that dominate the column and row type projections on a board of cells, together with the normalization by the column average. They enter the estimate of the norm of a product of column, row and global type projections: the product $\mathrm{colRoot}_W(A)\,\mathrm{meanInvRoot}_W(A)\,\mathrm{rowRoot}_W(B)$ is the normalized board operator whose norm is controlled by the missing cells of $W$, while $\mathrm{meanRoot}_W(A)$ carries the global part of the estimate.
--
--   **Formalization Note** `EvenDensity q` is the subtype of pairs `(A.1, A.2)` of matrices satisfying `IsEvenDensity`; `EvenDensity.matrix` is `Matrix.blockDiagonal` over `Bool` with `A.1` in the `false` (even) block, and `EvenDensity.mean` requires `[Nonempty C]`. The maps `root`, `invRoot` and `support` are the continuous functional calculus `cfc` applied to `Real.sqrt`, to `fun x => (Real.sqrt x)⁻¹` and to the indicator of `x ≠ 0`; since `Real.sqrt` vanishes on negative reals and `0⁻¹ = 0` in Lean, this gives the formulas above (and `cfc` returns `0` on non-self-adjoint arguments, which never occur here). `TensorMatrix.tensor` is the Kronecker product indexed by functions `W → Fin q × Bool` on the subtype of cells. The section variable `[Nonempty (Fin q)]` encodes $q\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/SpinAngle/TypeAngle.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/SpinAngle/TypeAngle.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SpinAngle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SpinAngle
import Definitions.Def_OAI_RepresentationTheory_SpinAngle_Core

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open scoped Matrix ComplexOrder
open scoped TensorProduct InnerProductSpace BigOperators
open scoped BigOperators ComplexConjugate
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace ComplexOrder
open scoped BigOperators
open scoped InnerProductSpace ComplexOrder BigOperators
open scoped InnerProductSpace BigOperators ComplexOrder
open scoped BigOperators
open scoped BigOperators
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
open scoped BigOperators
open Set
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators

namespace SpinAngle.TypeAngle
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open MatrixAnalysis TensorMatrix
variable {q : ℕ} [contextInstance30_17 : Nonempty (Fin q)]
variable {R C : Type*} [contextInstance31_23 : Fintype R] [contextInstance31_35 : DecidableEq R] [contextInstance31_51 : Fintype C] [contextInstance31_63 : DecidableEq C]

def columnRoot (W : Finset (R × C)) (A : C → EvenDensity q) :=
  tensor (fun x : W => root (A x.val.2).matrix)
def meanRoot [Nonempty C] (W : Finset (R × C)) (A : C → EvenDensity q) :=
  tensor (fun _ : W => root (EvenDensity.mean A).matrix)
def meanInvRoot [Nonempty C] (W : Finset (R × C)) (A : C → EvenDensity q) :=
  tensor (fun _ : W => invRoot (EvenDensity.mean A).matrix)
def meanSupport [Nonempty C] (W : Finset (R × C)) (A : C → EvenDensity q) :=
  tensor (fun _ : W => support (EvenDensity.mean A).matrix)
def rowRoot (W : Finset (R × C)) (B : R → EvenDensity q) :=
  tensor (fun x : W => root (B x.val.1).matrix)

end SpinAngle.TypeAngle

namespace SpinAngle.TypeBlocks
open scoped BigOperators
variable {q : ℕ}
variable {τ J : Type*} [contextInstance157_23 : Fintype τ] [contextInstance157_35 : DecidableEq τ] [contextInstance157_51 : Fintype J] [contextInstance157_63 : DecidableEq J]

end SpinAngle.TypeBlocks

namespace SpinAngle.TypeAngle
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ} [contextInstance179_17 : Nonempty (Fin q)]
variable {R C : Type*} [contextInstance180_23 : Fintype R] [contextInstance180_35 : DecidableEq R] [contextInstance180_51 : Fintype C] [contextInstance180_63 : DecidableEq C]

end SpinAngle.TypeAngle

end

end OAI


