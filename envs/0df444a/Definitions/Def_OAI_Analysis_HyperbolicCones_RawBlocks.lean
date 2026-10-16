-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
-- name    : OAI_Analysis_HyperbolicCones_RawBlocks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:31:34.867843+00:00
-- url     : https://prove2.me/theorems/b3f5a120-e069-497b-9fbb-f3a7f1b87281
-- title:
--   Raw two-block representations with positive definite identity blocks
-- statement:
--   Let $\mathrm{Sym}_n$ denote the real symmetric $n\times n$ matrices. Write $M\succeq0$ when $M$ is positive semidefinite and $M\succ0$ when it is positive definite. Let $\mathcal V=\mathrm{Sym}_4\times\mathrm{Sym}_4\times\mathbb{R}^3$, with points $(X,Z,y)$, and fix a set $K\subseteq\mathcal V$. A linear map $\Phi:\mathrm{Sym}_4\to\mathrm{Sym}_k$ is positive if $X\succeq0$ implies $\Phi(X)\succeq0$.
--
--   A **raw block pencil for $K$** consists of integers $a,c\ge1$ and linear maps
--   $D,F:\mathrm{Sym}_4\to\mathrm{Sym}_a$, $E:\mathrm{Sym}_4\to\mathrm{Sym}_c$, $C:\mathrm{Sym}_4\to\mathbb{R}^{a\times c}$, $A:\mathbb{R}^3\to\mathrm{Sym}_a$, $B:\mathbb{R}^3\to\mathbb{R}^{a\times c}$ and $G:\mathbb{R}^3\to\mathrm{Sym}_c$ such that
--
--   - $D$ and $E$ are positive;
--   - $D(I_4)\succ0$ and $E(I_4)\succ0$;
--   - for all $(X,Z,y)\in\mathcal V$,
--   $$
--   (X,Z,y)\in K\iff\begin{pmatrix}D(X)+F(Z)+A(y) & C(Z)+B(y)\\ \bigl(C(Z)+B(y)\bigr)^{\mathsf T} & E(Z)+G(y)\end{pmatrix}\succeq0 .
--   $$
--
--   This is the same data as a block pencil for $K$, except that the diagonal maps are only required to send the identity to positive definite matrices instead of to identity matrices.
--
--   This is the form in which the two blocks first appear. They arise when the support of the positive component $X\mapsto L(X,0,0)$ of a hypothetical spectrahedral representation $L$ is split off from its kernel. The weaker normalization $D(I_4)\succ0$, $E(I_4)\succ0$ is then upgraded to $D(I_4)=I_a$, $E(I_4)=I_c$ by a fixed block-diagonal congruence with $D(I_4)^{-1/2}$ and $E(I_4)^{-1/2}$. This turns a raw block pencil into a block pencil for the same set $K$.
--
--   **Formalization Note** The structure is `RawBlockPencil K`, with fields `D_positive`, `E_positive`, `D_identity_posDef`, `E_identity_posDef` and `represents`. The block matrix is built with `Matrix.fromBlocks` on the index type `Fin a ⊕ Fin c`. Mathlib's `PosSemidef` and `PosDef` include symmetry.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/RawBlocks.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/RawBlocks.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

/-- The finite blocks after splitting the support of the first positive pencil component. -/
structure RawBlockPencil (K : Set Ambient) where
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
  D_identity_posDef : (D 1 : Mat a ℝ).PosDef
  E_identity_posDef : (E 1 : Mat c ℝ).PosDef
  represents : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), ((X, Z), y) ∈ K ↔
    (Matrix.fromBlocks ((D X : Mat a ℝ) + (F Z : Mat a ℝ) + (A y : Mat a ℝ))
      (C Z + B y) (C Z + B y)ᵀ ((E Z : Mat c ℝ) + (G y : Mat c ℝ))).PosSemidef

end Paper256

end

end OAI


