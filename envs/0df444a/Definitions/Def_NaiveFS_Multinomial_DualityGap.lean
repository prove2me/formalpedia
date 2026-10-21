-- Prove2me | Definitions.Def_NaiveFS_Multinomial_DualityGap
-- name    : NaiveFS_Multinomial_DualityGap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:14:12.609817+00:00
-- url     : https://prove2.me/theorems/fad4635a-7095-477e-8d79-147909ed276a
-- title:
--   §3.6, pp. 9–10 — conjugate, biconjugate, lack of convexity ρ (Definition 3.4), Assumption 3.3 and the perturbation function h_P of problem (P)
-- statement:
--   The duality-gap machinery of §3.6, for extended-valued functions $f:\mathbb R^d\to\mathbb R\cup\{\pm\infty\}$.
--
--   1. **Conjugate and biconjugate.** $f^*(y)=\sup_x\{y^\top x-f(x)\}$ and $f^{**}(x)=\sup_y\{x^\top y-f^*(y)\}$; $f^{**}$ is the closed convex envelope of $f$.
--   2. **Lack of convexity** (Definition 3.4, (20)). $\rho(f)=\sup_{x\in\operatorname{dom}f}\{f(x)-f^{**}(x)\}$, where $\operatorname{dom}f=\{x:f(x)<+\infty\}$.
--   3. **Assumption 3.3.** $f$ is proper (never $-\infty$, finite somewhere), 1-coercive ($f(x)/\|x\|\to+\infty$ as $\|x\|\to\infty$), lower semicontinuous, and minorized by an affine function.
--   4. **Problem (P).** Given functions $f_i:\mathbb R^{d_i}\to\mathbb R\cup\{+\infty\}$, $g_i:\mathbb R^{d_i}\to(\mathbb R\cup\{+\infty\})^m$, $i=1,\dots,n$, and $b\in\mathbb R^m$, the perturbation function is
--   $$h_P(u)=\inf_{x_1,\dots,x_n}\Big\{\sum_{i=1}^nf_i(x_i)\ :\ \sum_{i=1}^ng_i(x_i)\le b+u\Big\},\qquad u\in\mathbb R^m,$$
--   with $h_P(u)=+\infty$ when the constraint is infeasible.
--
--   These are the objects of the Aubin–Ekeland / Ekeland–Temam duality-gap bound (Theorem 3.5) used to prove Theorem 3.6.
--
--   **Formalization Note** Values are in `EReal`; $\mathbb R^d$ is `Fin d → ℝ` with the pairing $\sum_iy_ix_i$ (1-coercivity and lower semicontinuity do not depend on the choice of norm). The page prints the conjugate with $\inf$; the supremum is the standard definition that the page's references ([18, Th. 12.1], [11, Th. X.1.3.5]) and its own description of $f^{**}$ use. In `EReal`, $r-(+\infty)=-\infty$, so points outside $\operatorname{dom}f$ do not contribute to $f^*$, and $f\equiv+\infty$ gives $f^*\equiv-\infty$ and $f^{**}\equiv+\infty$. The platform's `fenchelConjugate`/`fenchelBiconjugate` take finite-valued $f$ and cannot express $h_P$ or an indicator extended by $+\infty$, so they are not reused.
-- source:
--   Askari, d'Aspremont & El Ghaoui, Naive Feature Selection, arXiv:1905.09884v4, p. 9 (problem (P), conjugate, Assumption 3.3); p. 10, Definition 3.4 (20)

import Mathlib

namespace NaiveFS.Multinomial

open Finset

/-- The Fenchel conjugate `f*(y) := sup_x {yᵀx − f(x)}` of an extended-valued
`f : ℝᵈ → ℝ ∪ {±∞}` (p. 9). The page prints `inf`; the supremum is the standard definition the
page cites ([18, Th. 12.1], [11, Th. X.1.3.5]) and the one its description of the biconjugate
needs. Points with `f x = +∞` contribute `−∞`, so the supremum is over `dom f`. -/
noncomputable def conj {d : ℕ} (f : (Fin d → ℝ) → EReal) (y : Fin d → ℝ) : EReal :=
  ⨆ x : Fin d → ℝ, ((∑ i, y i * x i : ℝ) : EReal) - f x

/-- The biconjugate `f**(x) := sup_y {xᵀy − f*(y)}` (p. 9), the closed convex envelope of `f`. -/
noncomputable def biconj {d : ℕ} (f : (Fin d → ℝ) → EReal) (x : Fin d → ℝ) : EReal :=
  ⨆ y : Fin d → ℝ, ((∑ i, x i * y i : ℝ) : EReal) - conj f y

/-- The lack of convexity `ρ(f) := sup_{x ∈ dom f} {f(x) − f**(x)}` (Definition 3.4, (20),
p. 10), with `dom f = {x : f x ≠ +∞}`. -/
noncomputable def lackOfConvexity {d : ℕ} (f : (Fin d → ℝ) → EReal) : EReal :=
  ⨆ (x : Fin d → ℝ) (_ : f x ≠ ⊤), f x - biconj f x

/-- Assumption 3.3 (p. 9): `f` is proper, 1-coercive, lower semicontinuous, and minorized by an
affine function. -/
structure Assumption33 {d : ℕ} (f : (Fin d → ℝ) → EReal) : Prop where
  /-- proper: never `−∞` … -/
  ne_bot : ∀ x, f x ≠ ⊥
  /-- … and finite somewhere -/
  dom_nonempty : ∃ x, f x ≠ ⊤
  /-- 1-coercive: `f(x)/‖x‖ → +∞` as `‖x‖ → ∞` -/
  coercive : ∀ M : ℝ, ∃ R : ℝ, ∀ x : Fin d → ℝ, R ≤ ‖x‖ → ((M * ‖x‖ : ℝ) : EReal) ≤ f x
  /-- lower semicontinuous -/
  lsc : LowerSemicontinuous f
  /-- an affine minorant exists -/
  affine_minorant : ∃ (a : Fin d → ℝ) (c : ℝ), ∀ x, ((∑ i, a i * x i + c : ℝ) : EReal) ≤ f x

/-- The perturbation function of problem (P) (p. 9):
`h_P(u) := inf_x Σᵢ fᵢ(xᵢ)` subject to `Σᵢ gᵢ(xᵢ) ≤ b + u` (componentwise), over
`xᵢ ∈ ℝ^{dᵢ}`, `i = 1, …, n`; `gᵢ` takes values in `(ℝ ∪ {+∞})ᵐ`. An infeasible `u` gives `+∞`. -/
noncomputable def hP {n m : ℕ} {d : Fin n → ℕ} (f : ∀ i, (Fin (d i) → ℝ) → EReal)
    (g : ∀ i, (Fin (d i) → ℝ) → Fin m → EReal) (b : Fin m → ℝ) (u : Fin m → ℝ) : EReal :=
  ⨅ (x : ∀ i, Fin (d i) → ℝ) (_ : ∀ j, ∑ i, g i (x i) j ≤ ((b j + u j : ℝ) : EReal)),
    ∑ i, f i (x i)

end NaiveFS.Multinomial


