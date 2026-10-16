-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
-- name    : OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:57:37.066216+00:00
-- url     : https://prove2.me/theorems/aae34ede-e222-45c5-a5a3-386c82779738
-- title:
--   Two-block form of a thermal-noise channel output and the block-swap unitary
-- statement:
--   Let $\mathcal I$ and $\mathcal J$ be finite index sets, $X,Y\in\mathbb{C}^{\mathcal I\times\mathcal J}$ and $a,b,c,d,K\in\mathbb{R}$; $A^*$ denotes the conjugate transpose.
--
--   1. **Two-block output matrix.**
--   $$T(X,Y;a,b,c,d,K)=\begin{pmatrix}a\,XX^{*}+b\,YY^{*}&K\,XY^{*}\\K\,YX^{*}&c\,XX^{*}+d\,YY^{*}\end{pmatrix},$$
--   a complex matrix indexed by $\mathcal I\sqcup\mathcal I$ (two copies of $\mathcal I$).
--   2. **Block swap.** The unitary $W=\begin{pmatrix}0&\mathbf 1\\\mathbf 1&0\end{pmatrix}$ on $\mathbb{C}^{\mathcal I\sqcup\mathcal I}$, which exchanges the two copies of $\mathcal I$; conjugation by it sends $\begin{pmatrix}P&Q\\R&S\end{pmatrix}$ to $\begin{pmatrix}S&R\\Q&P\end{pmatrix}$.
--
--   The matrix $T$ is the shape of the output of the generalized amplitude-damping channel (damping $\gamma$, thermal parameter $\nu$) acting on a pure multi-qubit input, once the first qubit is split off: if $X$ and $Y$ are factor matrices of the outputs of the two branches of the input (first qubit $0$, resp. $1$), the output is, after relabeling, $T(X,Y;1-\gamma\nu,\ \gamma(1-\nu),\ \gamma\nu,\ 1-\gamma(1-\nu),\ \sqrt{1-\gamma})$. The main inequality proved for it is the thermal entropy bound: if $\operatorname{mass}X=\operatorname{mass}Y=1$ (squared Frobenius norms), $a,b,c,d,K\ge0$, $a+b+c+d=1$ and $ad-bc=K^2$, then $T$ is a density matrix, $u=(a+b)(c+d)-K^2\in[0,\tfrac14]$, and
--   $$(a+c)\,S(XX^*)+(b+d)\,S(YY^*)+g(u)\le S\bigl(T(X,Y;a,b,c,d,K)\bigr),$$
--   where $S$ is the von Neumann entropy and $g(u)=h\bigl(\tfrac{1+\sqrt{1-4u}}{2}\bigr)$ with $h$ the binary entropy in nats. The block swap reduces one boundary case of this bound to the other.
--
--   **Formalization Note** The names are `thermal X Y a b c d K`, built with `Matrix.fromBlocks` on the index type `ι ⊕ ι`, and `blockSwap`, a term of `Matrix.unitaryGroup (ι ⊕ ι) ℂ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/ThermalEntropy.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/ThermalEntropy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AmplitudeDamping mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def thermal (X Y : Matrix ι κ ℂ) (a b c d K : ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks (a • gram X+b • gram Y) (K • (X*Yᴴ))
    (K • (Y*Xᴴ)) (c • gram X+d • gram Y)

def blockSwap : Matrix.unitaryGroup (ι ⊕ ι) ℂ :=
  ⟨Matrix.fromBlocks 0 1 1 0, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]⟩

end GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_3} {κ : Type u_4} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

end GAD

end

end OAI


