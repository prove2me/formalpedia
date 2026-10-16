-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
-- name    : OAI_Analysis_HyperbolicCones_PencilLimit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:50:58.836434+00:00
-- url     : https://prove2.me/theorems/8e9d565b-41a1-4806-94e7-11a3a5b56d64
-- title:
--   Scaled and limit block matrices as points of the space of symmetric matrices
-- statement:
--   Let $\mathrm{Sym}_n$ be the real symmetric $n\times n$ matrices. Write $M\succeq0$ when $M$ is positive semidefinite and $M\succ0$ when it is positive definite. Let $\mathcal V=\mathrm{Sym}_4\times\mathrm{Sym}_4\times\mathbb{R}^3$, with points $(X,Z,y)$, and fix a set $K\subseteq\mathcal V$. A linear map $\Phi:\mathrm{Sym}_4\to\mathrm{Sym}_k$ is positive if $X\succeq0$ implies $\Phi(X)\succeq0$. A *block pencil* for $K$ consists of integers $a,c\ge1$ and linear maps $D,F:\mathrm{Sym}_4\to\mathrm{Sym}_a$, $E:\mathrm{Sym}_4\to\mathrm{Sym}_c$, $C:\mathrm{Sym}_4\to\mathbb{R}^{a\times c}$, $A:\mathbb{R}^3\to\mathrm{Sym}_a$, $B:\mathbb{R}^3\to\mathbb{R}^{a\times c}$ and $G:\mathbb{R}^3\to\mathrm{Sym}_c$ with the following properties. The maps $D$ and $E$ are positive, $D(I_4)=I_a$, $E(I_4)=I_c$, and $(X,Z,y)\in K$ exactly when $\begin{pmatrix}D(X)+F(Z)+A(y) & C(Z)+B(y)\\ (C(Z)+B(y))^{\mathsf T} & E(Z)+G(y)\end{pmatrix}\succeq0$. For such a pencil, $(X,Z,y)\in\mathcal V$ and $s\in\mathbb{R}$, the scaled and limit matrices are
--
--   $$
--   M_s(X,Z,y)=\begin{pmatrix}D(X)+s\,A(y)+s^2F(Z) & B(y)+s\,C(Z)\\ \bigl(B(y)+s\,C(Z)\bigr)^{\mathsf T} & E(Z)\end{pmatrix},\qquad M_0(X,Z,y)=\begin{pmatrix}D(X)&B(y)\\B(y)^{\mathsf T}&E(Z)\end{pmatrix}.
--   $$
--
--   Both are symmetric $(a+c)\times(a+c)$ matrices. The file packages them as elements of the space $\mathrm{Sym}_{a+c}$ of symmetric matrices indexed by the disjoint union of an $a$-element and a $c$-element index set:
--
--   1. **Scaled family.** For fixed $(X,Z,y)$, the map $\mathbb{R}\to\mathrm{Sym}_{a+c}$, $s\mapsto M_s(X,Z,y)$.
--   2. **Limit point.** The element $M_0(X,Z,y)\in\mathrm{Sym}_{a+c}$.
--
--   Viewed in the finite-dimensional normed space $\mathrm{Sym}_{a+c}$, the family $s\mapsto M_s(X,Z,y)$ is polynomial in $s$, hence continuous, and its value at $s=0$ is the limit matrix. Since the positive semidefinite cone of $\mathrm{Sym}_{a+c}$ is closed, positive semidefiniteness of $M_s(X,Z,y)$ for $s\neq0$ passes to $M_0(X,Z,y)$. This is the step that isolates the blocks $D$, $B$ and $E$.
--
--   **Formalization Note** The definitions are `BlockPencil.scaledSelfAdjoint` and `BlockPencil.limitSelfAdjoint`. They bundle `BlockPencil.scaled` and `BlockPencil.limit` with their symmetry proofs into `selfAdjoint (Matrix (Fin a ⊕ Fin c) (Fin a ⊕ Fin c) ℝ)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/PencilLimit.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/PencilLimit.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology

namespace OAI

noncomputable section

open Matrix Set Filter
open scoped Topology Matrix.Norms.L2Operator

namespace Paper256.BlockPencil

def scaledSelfAdjoint {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) (s : ℝ) :
    selfAdjoint (Matrix (Fin P.a ⊕ Fin P.c) (Fin P.a ⊕ Fin P.c) ℝ) :=
  ⟨P.scaled X Z y s, P.scaled_isHermitian X Z y s⟩

def limitSelfAdjoint {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) :
    selfAdjoint (Matrix (Fin P.a ⊕ Fin P.c) (Fin P.a ⊕ Fin P.c) ℝ) :=
  ⟨P.limit X Z y, P.limit_isHermitian X Z y⟩

end Paper256.BlockPencil

end

end OAI


