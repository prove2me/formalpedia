-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
-- name    : OAI_Analysis_HyperbolicCones_PencilBlocks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:29:55.441574+00:00
-- url     : https://prove2.me/theorems/294dd8cf-e2de-465f-9e45-60e4eed04244
-- title:
--   Two-block normal form of a spectrahedral representation and its scaling limit
-- statement:
--   Let $\mathrm{Sym}_n$ denote the real symmetric $n\times n$ matrices and write $M\succeq0$ when $M$ is positive semidefinite. Let $\mathcal V=\mathrm{Sym}_4\times\mathrm{Sym}_4\times\mathbb{R}^3$, with points $(X,Z,y)$. A linear map $\Phi:\mathrm{Sym}_4\to\mathrm{Sym}_k$ is positive if $X\succeq0$ implies $\Phi(X)\succeq0$. Block matrices below have an upper-left $a\times a$ block and a lower-right $c\times c$ block. Fix a set $K\subseteq\mathcal V$.
--
--   1. **Block pencil for $K$.** A block pencil for $K$ consists of integers $a,c\ge1$ and linear maps
--   $D,F:\mathrm{Sym}_4\to\mathrm{Sym}_a$, $E:\mathrm{Sym}_4\to\mathrm{Sym}_c$, $C:\mathrm{Sym}_4\to\mathbb{R}^{a\times c}$, $A:\mathbb{R}^3\to\mathrm{Sym}_a$, $B:\mathbb{R}^3\to\mathbb{R}^{a\times c}$ and $G:\mathbb{R}^3\to\mathrm{Sym}_c$ with the following properties: $D$ and $E$ are positive, $D(I_4)=I_a$, $E(I_4)=I_c$, and for all $(X,Z,y)\in\mathcal V$
--   $$
--   (X,Z,y)\in K\iff M(X,Z,y)\succeq0,\qquad M(X,Z,y)=\begin{pmatrix}D(X)+F(Z)+A(y) & C(Z)+B(y)\\ \bigl(C(Z)+B(y)\bigr)^{\mathsf T} & E(Z)+G(y)\end{pmatrix}.
--   $$
--   Thus $K$ is the spectrahedron of a linear pencil of size $a+c$ in which $X$ enters only through the upper-left block $D(X)$.
--   2. **The representing matrix.** The $(a+c)\times(a+c)$ symmetric matrix $M(X,Z,y)$ above.
--   3. **The scaled matrix.** For $s\in\mathbb{R}$,
--   $$
--   M_s(X,Z,y)=\begin{pmatrix}D(X)+s\,A(y)+s^2F(Z) & B(y)+s\,C(Z)\\ \bigl(B(y)+s\,C(Z)\bigr)^{\mathsf T} & E(Z)\end{pmatrix}.
--   $$
--   4. **The limit matrix.** $M_0(X,Z,y)=\begin{pmatrix}D(X)&B(y)\\B(y)^{\mathsf T}&E(Z)\end{pmatrix}$, which is the scaled matrix at $s=0$. The file records that it is symmetric.
--
--   The scaled matrix comes from a rescaling. When $G=0$ and $s\neq0$, $M_s(X,Z,y)$ is obtained from $M(X,s^2Z,sy)$ by the congruence with $\operatorname{diag}(I_a,s^{-1}I_c)$. Letting $s\to0$ leaves the limit matrix, which involves only the blocks $D$, $B$ and $E$. When $K$ agrees with the hyperbolicity cone of the surrounding development on the slice where $X$ is positive definite, these three blocks are later shown to form a normalized pencil: $D$ and $E$ are positive and unital, and the Schur complement $E(Z)-B(y)^{\mathsf T}D(X)^{-1}B(y)$ decides membership on that slice.
--
--   **Formalization Note** The structure is `BlockPencil K`, with fields `D_positive`, `E_positive`, `D_unital`, `E_unital` and `represents`. The matrices `matrix`, `scaled` and `limit` are built with `Matrix.fromBlocks` on the index type `Fin a ⊕ Fin c`, and `limit_isHermitian` states the symmetry of the limit matrix. Mathlib's `PosSemidef` includes symmetry. The source describes these blocks as the ones obtained after common-kernel compression and a fixed diagonal congruence.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/PencilBlocks.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/PencilBlocks.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HyperbolicCones mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation

namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

/-- The actual finite blocks after common-kernel compression and fixed diagonal congruence. -/
structure BlockPencil (K : Set Ambient) where
  a : ℕ
  c : ℕ
  a_pos : 0 < a
  c_pos : 0 < c
  D : Sym 4 →ₗ[ℝ] Sym a
  E : Sym 4 →ₗ[ℝ] Sym c
  F : Sym 4 →ₗ[ℝ] Sym a
  C : Sym 4 →ₗ[ℝ] Matrix (Fin a) (Fin c) ℝ
  A : (Fin 3 → ℝ) →ₗ[ℝ] Sym a
  B : (Fin 3 → ℝ) →ₗ[ℝ] Matrix (Fin a) (Fin c) ℝ
  G : (Fin 3 → ℝ) →ₗ[ℝ] Sym c
  D_positive : ∀ X : Sym 4, (X : Mat 4 ℝ).PosSemidef → (D X : Mat a ℝ).PosSemidef
  E_positive : ∀ X : Sym 4, (X : Mat 4 ℝ).PosSemidef → (E X : Mat c ℝ).PosSemidef
  D_unital : D 1 = 1
  E_unital : E 1 = 1
  represents : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), ((X, Z), y) ∈ K ↔
    (Matrix.fromBlocks ((D X : Mat a ℝ) + (F Z : Mat a ℝ) + (A y : Mat a ℝ))
      (C Z + B y) (C Z + B y)ᵀ ((E Z : Mat c ℝ) + (G y : Mat c ℝ))).PosSemidef

namespace BlockPencil

def matrix {K : Set Ambient} (P : BlockPencil K) (X Z : Sym 4) (y : Fin 3 → ℝ) :
    Matrix (Fin P.a ⊕ Fin P.c) (Fin P.a ⊕ Fin P.c) ℝ :=
  Matrix.fromBlocks ((P.D X : Mat P.a ℝ) + (P.F Z : Mat P.a ℝ) + (P.A y : Mat P.a ℝ))
    (P.C Z + P.B y) (P.C Z + P.B y)ᵀ ((P.E Z : Mat P.c ℝ) + (P.G y : Mat P.c ℝ))

def scaled {K : Set Ambient} (P : BlockPencil K) (X Z : Sym 4) (y : Fin 3 → ℝ) (s : ℝ) :
    Matrix (Fin P.a ⊕ Fin P.c) (Fin P.a ⊕ Fin P.c) ℝ :=
  Matrix.fromBlocks ((P.D X : Mat P.a ℝ) + s • (P.A y : Mat P.a ℝ) +
      s ^ 2 • (P.F Z : Mat P.a ℝ))
    (P.B y + s • P.C Z) (P.B y + s • P.C Z)ᵀ (P.E Z : Mat P.c ℝ)

def limit {K : Set Ambient} (P : BlockPencil K) (X Z : Sym 4) (y : Fin 3 → ℝ) :
    Matrix (Fin P.a ⊕ Fin P.c) (Fin P.a ⊕ Fin P.c) ℝ :=
  Matrix.fromBlocks (P.D X : Mat P.a ℝ) (P.B y) (P.B y)ᵀ (P.E Z : Mat P.c ℝ)

theorem limit_isHermitian {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) : (P.limit X Z y).IsHermitian := by
  apply Matrix.IsHermitian.fromBlocks
  · exact (P.D X).property
  · simp
  · exact (P.E Z).property

end BlockPencil

end Paper256

end

end OAI


