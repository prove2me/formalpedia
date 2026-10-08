-- Prove2me | Definitions.Def_ConvexOptAlg_Ellipsoid_Defs
-- name    : ConvexOptAlg_Ellipsoid_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:07:27.388137+00:00
-- url     : https://prove2.me/theorems/5ac67cbb-97f5-4b89-b11e-09a7bf66ccae
-- title:
--   Ch. 2 preamble and §2.2, pp. 244, 249–250 — convex body, Euclidean balls, the ellipsoid method as a run predicate, its output, and X_ε
-- statement:
--   This module fixes the objects of Chapter 2 (p. 244) and of the ellipsoid method (§2.2, pp. 249–250) on $\mathbb R^n$.
--
--   1. The **Euclidean ball** of center $z$ and radius $\rho\ge 0$ is $\{x\in\mathbb R^n : (x-z)^\top(x-z)\le\rho^2\}$.
--   2. A **convex body** is a compact convex set $\mathcal X\subset\mathbb R^n$ with non-empty interior.
--   3. A **run of the ellipsoid method** on $\mathcal X$ with objective $f$, started from the Euclidean ball $\mathcal E_0$ of center $c_0$ and radius $R$, is a sequence of centers $c_t$, shape matrices $H_t$ and oracle answers $w_t$ with $H_0=R^2\mathrm I_n$ such that, at every step $t$ reached without a zero answer:
--      - if $c_t\notin\mathcal X$, then $w_t\ne 0$ and $\mathcal X\subset\{x:(x-c_t)^\top w_t\le 0\}$ (separation oracle);
--      - if $c_t\in\mathcal X$, then $w_t$ is a subgradient of $f$ at $c_t$ relative to $\mathcal X$: $f(c_t)+w_t^\top(x-c_t)\le f(x)$ for all $x\in\mathcal X$ (first order oracle);
--      - if $w_t\neq0$, then
--   $$
--   c_{t+1}=c_t-\frac{1}{n+1}\,\frac{H_t w_t}{\sqrt{w_t^\top H_t w_t}},\qquad
--   H_{t+1}=\frac{n^2}{n^2-1}\Big(H_t-\frac{2}{n+1}\,\frac{H_t w_t w_t^\top H_t}{w_t^\top H_t w_t}\Big).
--   $$
--      The current ellipsoid is $\mathcal E_t=\{x:(x-c_t)^\top H_t^{-1}(x-c_t)\le 1\}$.
--   4. An **output after $t$ iterations** is a point $x_t\in\operatorname{argmin}\{f(c): c\in\{c_0,\dots,c_{t-1}\}\cap\mathcal X\}$.
--   5. For a point $x^*$ and $\varepsilon\in[0,1]$, the **scaled copy** is $\mathcal X_\varepsilon=\{(1-\varepsilon)x^*+\varepsilon x : x\in\mathcal X\}$.
--
--   These are the objects in which Theorem 2.4 and its milestones are stated.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`, matching the reused Bertsimas–Tsitsiklis ellipsoid layer; since Mathlib's norm on that type is the sup norm, Euclidean balls are written with the dot product. The update is that layer's `ellipsoidUpdateCenter`/`ellipsoidUpdateMatrix` with $a=-w_t$, which is exactly the page's formula (the page writes $w$ for $w_t$). The page's update divides by $\sqrt{w_t^\top H_t w_t}$; a subgradient may be $0$, in which case $c_t$ minimizes $f$ on $\mathcal X$, and the run predicate then stops constraining later iterates instead of applying a meaningless update. Subgradients are relative to $\mathcal X$ (Definition 1.2) via the published `LinearOptimization.IsSubgradientOn`. The output ranges over the centers queried in the $t$ iterations, $c_0,\dots,c_{t-1}$; the page writes $\{c_1,\dots,c_t\}$ (see Theorem 2.4).
-- source:
--   Bubeck, arXiv:1405.4980v2, Ch. 2 preamble, p. 244; §2.2, p. 247 (ellipsoids) and pp. 249–250 (the method); §2.1, p. 246 (X_ε)

import Mathlib
import Definitions.Def_LinearOptimization_EllipsoidMethod
import Definitions.Def_LinearOptimization_Subgradient

namespace ConvexOptAlg.Ellipsoid

open Matrix

/-- The closed Euclidean ball `{x ∈ ℝⁿ : (x − z)⊤(x − z) ≤ ρ²}` of center `z` and radius `ρ`
(for `ρ ≥ 0`), written with the dot product because the sup norm is Mathlib's default norm on
`Fin n → ℝ`. Bubeck, arXiv:1405.4980v2, Ch. 2 preamble, p. 244 ("an Euclidean ball of radius R"). -/
def euclBall {n : ℕ} (z : Fin n → ℝ) (ρ : ℝ) : Set (Fin n → ℝ) :=
  {x | (x - z) ⬝ᵥ (x - z) ≤ ρ ^ 2}

/-- A convex body: a compact convex set with non-empty interior (Bubeck, Ch. 2 preamble, p. 244). -/
def IsConvexBody {n : ℕ} (X : Set (Fin n → ℝ)) : Prop :=
  IsCompact X ∧ Convex ℝ X ∧ (interior X).Nonempty

/-- A run of the ellipsoid method (Bubeck, §2.2, pp. 249–250) on the constraint set `X` with
objective `f`, started from the Euclidean ball `E₀` of center `c0` and radius `R`
(`H₀ = R² Iₙ`). `c t` is the center, `H t` the matrix, `w t` the oracle answer at step `t`.

At every step `t` reached without a zero oracle answer (`w s ≠ 0` for all `s < t`):
* if `c t ∉ X`, `w t` is a nonzero separating vector: `X ⊆ {x : (x − c_t)⊤w_t ≤ 0}`;
* if `c t ∈ X`, `w t` is a subgradient of `f` at `c t` relative to `X`
  (`f(c_t) + w_t⊤(x − c_t) ≤ f(x)` for all `x ∈ X`, Definition 1.2);
* if `w t ≠ 0`, the next center and matrix are the update of Lemma 2.3 (2.5)–(2.6),
  `c_{t+1} = c_t − (1/(n+1)) H_t w_t / √(w_t⊤H_t w_t)` and
  `H_{t+1} = (n²/(n²−1)) (H_t − (2/(n+1)) H_t w_t w_t⊤H_t / (w_t⊤H_t w_t))`,
  i.e. Bertsimas–Tsitsiklis's `ellipsoidUpdateCenter`/`ellipsoidUpdateMatrix` with `a = −w_t`.

A zero answer can only be a subgradient at a center in `X`, which is then a minimizer of `f` on
`X`; the run stops there and later centers are unconstrained (the page's update would divide
by zero). -/
def IsEllipsoidRun {n : ℕ} (X : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) (R : ℝ)
    (c0 : Fin n → ℝ) (c : ℕ → Fin n → ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (w : ℕ → Fin n → ℝ) : Prop :=
  c 0 = c0 ∧ H 0 = R ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ) ∧
  ∀ t : ℕ, (∀ s < t, w s ≠ 0) →
    (c t ∉ X → w t ≠ 0 ∧ ∀ x ∈ X, (x - c t) ⬝ᵥ w t ≤ 0) ∧
    (c t ∈ X → LinearOptimization.IsSubgradientOn f X (w t) (c t)) ∧
    (w t ≠ 0 →
      c (t + 1) = LinearOptimization.ellipsoidUpdateCenter (c t) (H t) (-(w t)) ∧
      H (t + 1) = LinearOptimization.ellipsoidUpdateMatrix (H t) (-(w t)))

/-- `x` is an output of the ellipsoid method stopped after `t` iterations: a minimizer of `f`
over the centers queried in those iterations that lie in `X`, i.e.
`x ∈ argmin_{c ∈ {c₀, …, c_{t−1}} ∩ X} f(c)` (Bubeck, p. 250; see the indexing note of
Theorem 2.4). -/
def IsEllipsoidOutput {n : ℕ} (X : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (c : ℕ → Fin n → ℝ) (t : ℕ) (x : Fin n → ℝ) : Prop :=
  (∃ s < t, c s = x) ∧ x ∈ X ∧ ∀ s < t, c s ∈ X → f x ≤ f (c s)

/-- The scaled copy `X_ε = {(1 − ε)x∗ + εx : x ∈ X}` of `X` towards `x∗` (Bubeck, §2.1,
p. 246). -/
def scaledCopy {n : ℕ} (X : Set (Fin n → ℝ)) (xstar : Fin n → ℝ) (ε : ℝ) :
    Set (Fin n → ℝ) :=
  (fun x => (1 - ε) • xstar + ε • x) '' X

end ConvexOptAlg.Ellipsoid


