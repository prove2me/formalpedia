-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
-- name    : OAI_Analysis_HyperbolicCones_BlockReduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:43:59.475664+00:00
-- url     : https://prove2.me/theorems/870f9740-c991-4b09-ac68-207925ea75f3
-- title:
--   Symmetry of the scaled two-block matrices of a block pencil
-- statement:
--   Let $\mathrm{Sym}_n$ be the real symmetric $n\times n$ matrices. Write $M\succeq0$ when $M$ is positive semidefinite and $M\succ0$ when it is positive definite. Let $\mathcal V=\mathrm{Sym}_4\times\mathrm{Sym}_4\times\mathbb{R}^3$, with points $(X,Z,y)$, and fix a set $K\subseteq\mathcal V$. A linear map $\Phi:\mathrm{Sym}_4\to\mathrm{Sym}_k$ is positive if $X\succeq0$ implies $\Phi(X)\succeq0$. A *block pencil* for $K$ consists of integers $a,c\ge1$ and linear maps $D,F:\mathrm{Sym}_4\to\mathrm{Sym}_a$, $E:\mathrm{Sym}_4\to\mathrm{Sym}_c$, $C:\mathrm{Sym}_4\to\mathbb{R}^{a\times c}$, $A:\mathbb{R}^3\to\mathrm{Sym}_a$, $B:\mathbb{R}^3\to\mathbb{R}^{a\times c}$ and $G:\mathbb{R}^3\to\mathrm{Sym}_c$ with the following properties. The maps $D$ and $E$ are positive, $D(I_4)=I_a$, $E(I_4)=I_c$, and $(X,Z,y)\in K$ exactly when $\begin{pmatrix}D(X)+F(Z)+A(y) & C(Z)+B(y)\\ (C(Z)+B(y))^{\mathsf T} & E(Z)+G(y)\end{pmatrix}\succeq0$. For such a pencil, $(X,Z,y)\in\mathcal V$ and $s\in\mathbb{R}$, the scaled matrix is
--
--   $$
--   M_s(X,Z,y)=\begin{pmatrix}D(X)+s\,A(y)+s^2F(Z) & B(y)+s\,C(Z)\\ \bigl(B(y)+s\,C(Z)\bigr)^{\mathsf T} & E(Z)\end{pmatrix}.
--   $$
--
--   The file records that this matrix is symmetric for every block pencil, every $(X,Z,y)\in\mathcal V$ and every $s\in\mathbb{R}$:
--
--   $$
--   M_s(X,Z,y)^{\mathsf T}=M_s(X,Z,y).
--   $$
--
--   The diagonal blocks are symmetric because $D$, $A$, $F$ and $E$ take values in symmetric matrices, and the off-diagonal blocks are transposes of each other. As a result, $M_s(X,Z,y)$ can be regarded as an element of $\mathrm{Sym}_{a+c}$. This is needed to speak of positive semidefiniteness and of convergence within the space of symmetric matrices as $s\to0$.
--
--   **Formalization Note** The statement is `BlockPencil.scaled_isHermitian`; for real matrices Hermitian means symmetric. The scaled matrix is `BlockPencil.scaled`, built with `Matrix.fromBlocks` on the index type `Fin a ⊕ Fin c`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/BlockReduction.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/BlockReduction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HyperbolicCones mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization

namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256.BlockPencil

theorem scaled_isHermitian {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) (s : ℝ) : (P.scaled X Z y s).IsHermitian := by
  apply Matrix.IsHermitian.fromBlocks
  · exact ((P.D X).property.add ((IsSelfAdjoint.all s).smul (P.A y).property)).add
      ((IsSelfAdjoint.all (s ^ 2)).smul (P.F Z).property)
  · simp
  · exact (P.E Z).property

end Paper256.BlockPencil

end

end OAI


