-- Prove2me | Definitions.Def_DualTwoStageRO_Problem
-- name    : DualTwoStageRO_Problem
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:07.557562+00:00
-- url     : https://prove2.me/theorems/dea6b7f2-575f-46ea-ad9f-9c8a67b60f82
-- title:
--   Data of the two-stage robust nonlinear problem (1)–(3)
-- statement:
--   The data of the two-stage robust problem (1) are:
--
--   1. a set $\mathcal X\subseteq\mathbb R^{n_x}$ of here-and-now decisions;
--   2. functions $f_i:\mathbb R^{n_x}\to\mathbb R$ and $g_i:\mathbb R^{n_y}\to\mathbb R$ for $i=0,\dots,m_1$;
--   3. functions $F_{ij}:\mathbb R^{n_x}\to\mathbb R$ for $i=1,\dots,m_1$, $j=1,\dots,n_\zeta$, with rows $F_{i\cdot}(x)=(F_{i1}(x),\dots,F_{in_\zeta}(x))$;
--   4. matrices $A^0,A^l\in\mathbb R^{m_2\times n_\zeta}$ and vectors $b^0,b^l\in\mathbb R^{m_2}$, $l=1,\dots,n_x$, defining the affine maps
--   $$A(x)=A^0+\sum_{l=1}^{n_x}A^lx_l,\qquad b(x)=b^0+\sum_{l=1}^{n_x}b^lx_l;\tag{2}$$
--   5. a fixed recourse matrix $B\in\mathbb R^{m_2\times n_y}$;
--   6. $D\in\mathbb R^{p\times n_\zeta}$ and $d\in\mathbb R^p$, defining the polyhedral uncertainty set
--   $$\mathcal U=\{\zeta\in\mathbb R^{n_\zeta}:\ \zeta\ge0,\ D\zeta=d\}.\tag{3}$$
--
--   The paper assumes the $f_i,g_i$ convex and $\mathcal U$ nonempty; these are hypotheses of the theorems that use the data.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`. The index $i=0,\dots,m_1$ is `Fin (m1+1)`; the rows $F_{i\cdot}$, $i=1,\dots,m_1$, are indexed by `Fin m1`, and row `i` pairs with `f i.succ`, `g i.succ`. The page states the range of $A^l,b^l$ as "$l=0,\dots,n_\zeta$"; (2) sums over $l=1,\dots,n_x$, which is the range used. No dimension is assumed positive.
-- source:
--   de Ruiter, Zhen, den Hertog, Technical Note—Dual Approach for Two-Stage Robust Nonlinear Optimization, Operations Research 71(5):1794–1799, 2023, doi:10.1287/opre.2022.2289 (published version, sha256 75cbce38…fe03ac), §1.1, p.1794, (1)–(3)

import Mathlib

namespace DualTwoStageRO

open Matrix

/-- **Data of the two-stage robust nonlinear problem (1)–(3).**
de Ruiter, Zhen, den Hertog, *Technical Note—Dual Approach for Two-Stage Robust Nonlinear
Optimization*, Operations Research 71(5), 2023, §1.1, p.1794:
"Here, X ⊆ R^{nx}, the functions f_i : R^{nx} → R, g_i : R^{ny} → R are convex for all
i = 0,…,m1, F_i·(x) = (F_i1(x),…,F_inζ(x)), and F_ij : R^{nx} → R are real-valued functions for all
i = 1,…,m1 and j = 1,…,nζ. The matrices A(x) ∈ R^{m2×nζ} and the vector b(x) ∈ R^{m2} depend on
x ∈ R^{nx} in an affine way: A(x) = A⁰ + Σ_{l=1}^{nx} A^l x_l, b(x) = b⁰ + Σ_{l=1}^{nx} b^l x_l (2)
… U = {ζ ≥ 0 : Dζ = d}, (3) where D ∈ R^{p×nζ} and d ∈ R^p."

Fields: `X`; `f i`, `g i` for `i : Fin (m1+1)` (the paper's `i = 0,…,m1`); `F i j` for
`i : Fin m1` (the paper's `i = 1,…,m1`, so `F i` pairs with `f i.succ`, `g i.succ`) and
`j : Fin nζ`; `A0`, `Al l`, `b0`, `bl l` (`l : Fin nx`, the paper's `l = 1,…,nx`); the recourse
matrix `B ∈ ℝ^{m2×ny}`; and `D ∈ ℝ^{p×nζ}`, `d ∈ ℝ^p`.

**Formalization Note.** Vectors are `Fin n → ℝ`. Convexity of `f i`, `g i` and nonemptiness of `U`
are hypotheses of the theorems, not fields. The page writes "for all l = 0,…,nζ" for the range of
`A^l`, `b^l`; (2) sums over `l = 1,…,nx`, and `l` ranges over `0,…,nx` here (`A0`, `b0` and
`Al`, `bl` indexed by `Fin nx`). -/
structure Problem (nx ny nζ m1 m2 p : ℕ) where
  /-- The set `X ⊆ ℝ^{nx}` of here-and-now decisions. -/
  X : Set (Fin nx → ℝ)
  /-- `f_i : ℝ^{nx} → ℝ`, `i = 0,…,m1`. -/
  f : Fin (m1 + 1) → (Fin nx → ℝ) → ℝ
  /-- `g_i : ℝ^{ny} → ℝ`, `i = 0,…,m1`. -/
  g : Fin (m1 + 1) → (Fin ny → ℝ) → ℝ
  /-- `F_ij : ℝ^{nx} → ℝ`; `F i` is the paper's row `F_{i+1,·}`, `i = 1,…,m1`. -/
  F : Fin m1 → Fin nζ → (Fin nx → ℝ) → ℝ
  /-- `A⁰ ∈ ℝ^{m2×nζ}`. -/
  A0 : Matrix (Fin m2) (Fin nζ) ℝ
  /-- `A^l ∈ ℝ^{m2×nζ}`, `l = 1,…,nx`. -/
  Al : Fin nx → Matrix (Fin m2) (Fin nζ) ℝ
  /-- `b⁰ ∈ ℝ^{m2}`. -/
  b0 : Fin m2 → ℝ
  /-- `b^l ∈ ℝ^{m2}`, `l = 1,…,nx`. -/
  bl : Fin nx → Fin m2 → ℝ
  /-- The fixed recourse matrix `B ∈ ℝ^{m2×ny}`. -/
  B : Matrix (Fin m2) (Fin ny) ℝ
  /-- `D ∈ ℝ^{p×nζ}` of the uncertainty set (3). -/
  D : Matrix (Fin p) (Fin nζ) ℝ
  /-- `d ∈ ℝ^p` of the uncertainty set (3). -/
  d : Fin p → ℝ

namespace Problem

variable {nx ny nζ m1 m2 p : ℕ} (P : Problem nx ny nζ m1 m2 p)

/-- `A(x) = A⁰ + Σ_{l=1}^{nx} A^l x_l`, (2), p.1794. -/
def A (x : Fin nx → ℝ) : Matrix (Fin m2) (Fin nζ) ℝ := P.A0 + ∑ l, x l • P.Al l

/-- `b(x) = b⁰ + Σ_{l=1}^{nx} b^l x_l`, (2), p.1794. -/
def b (x : Fin nx → ℝ) : Fin m2 → ℝ := P.b0 + ∑ l, x l • P.bl l

/-- The polyhedral uncertainty set `U = {ζ ≥ 0 : Dζ = d}`, (3), p.1794. -/
def U : Set (Fin nζ → ℝ) := {ζ | 0 ≤ ζ ∧ P.D *ᵥ ζ = P.d}

end Problem

end DualTwoStageRO


