-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
-- name    : OAI_InformationTheory_AmplitudeDamping_GramMatrices
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:55:24.936704+00:00
-- url     : https://prove2.me/theorems/9323d8ea-2d37-4888-86d4-fba21f843529
-- title:
--   Gram matrices, Frobenius mass and the log-determinant $\log\det(\mathbf{1}+AA^*)$
-- statement:
--   Let $\mathcal I,\mathcal J,\mathcal M,\mathcal N$ be finite index sets; all matrices are complex and $A^*$ denotes the conjugate transpose.
--
--   1. **Zero-corner block matrix.** For $A\in\mathbb{C}^{\mathcal I\times\mathcal J}$, $B\in\mathbb{C}^{\mathcal I\times\mathcal M}$ and $C\in\mathbb{C}^{\mathcal N\times\mathcal J}$,
--   $$\operatorname{zeroBlock}(A,B,C)=\begin{pmatrix}A&B\\C&0\end{pmatrix}\in\mathbb{C}^{(\mathcal I\sqcup\mathcal N)\times(\mathcal J\sqcup\mathcal M)}.$$
--   2. **Gram matrix.** For $A\in\mathbb{C}^{\mathcal I\times\mathcal J}$, $\operatorname{gram}(A)=AA^*$, a positive semidefinite $\mathcal I\times\mathcal I$ matrix.
--   3. **Mass.** $\operatorname{mass}(A)=\operatorname{Re}\operatorname{tr}(AA^*)=\sum_{i,j}|A_{ij}|^2$, the squared Frobenius norm of $A$.
--   4. **Log-Gram determinant.** $\operatorname{logGram}(A)=\log\bigl|\det(\mathbf 1+AA^*)\bigr|$; since $\mathbf 1+AA^*$ is positive definite, this is $\log\det(\mathbf 1+AA^*)$.
--
--   These objects let a positive semidefinite matrix be handled through a factor: if $P=AA^*$ (for example a channel output written through the column matrix of a pure input), then $\operatorname{mass}(A)=\operatorname{tr}P$ and $\operatorname{logGram}(\sqrt r\,A)=\log\det(\mathbf 1+rP)$ for $r\ge0$, the resolvent determinant that controls the von Neumann entropy of $P$. For the zero-corner block matrix one has
--   $$\operatorname{gram}\begin{pmatrix}A&B\\C&0\end{pmatrix}=\begin{pmatrix}AA^*+BB^*&AC^*\\CA^*&CC^*\end{pmatrix},\qquad \operatorname{mass}=\operatorname{mass}A+\operatorname{mass}B+\operatorname{mass}C,$$
--   and $\operatorname{logGram}$ splits as $\operatorname{logGram}B+\operatorname{logGram}C+\log|\det(D+AE^{-1}A^*)|-\log|\det D|$ with $D=\mathbf 1+BB^*$ and $E=\mathbf 1+C^*C$, a block log-determinant deficit.
--
--   **Formalization Note** The names are `zeroBlock`, `gram`, `mass` and `logGram`; `zeroBlock` is `Matrix.fromBlocks A B C 0` on the sum types `ι ⊕ ν` and `κ ⊕ μ` (here `ν` is just an index type).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/GramMatrices.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/GramMatrices.lean by skeleton subtraction
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

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

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

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {κ : Type u_2} {μ : Type u_3} {ν : Type u_4} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

def zeroBlock (A : Matrix ι κ ℂ) (B : Matrix ι μ ℂ) (C : Matrix ν κ ℂ) :
    Matrix (ι ⊕ ν) (κ ⊕ μ) ℂ := Matrix.fromBlocks A B C 0

def gram (A : Matrix ι κ ℂ) : Matrix ι ι ℂ := A * Aᴴ

def mass (A : Matrix ι κ ℂ) : ℝ := (gram A).trace.re

def logGram (A : Matrix ι κ ℂ) : ℝ := Real.log ‖(1+gram A).det‖

end GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_5} [Fintype ι] [DecidableEq ι]

end GAD

end

end OAI


