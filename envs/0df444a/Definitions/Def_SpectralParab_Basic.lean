-- Prove2me | Definitions.Def_SpectralParab_Basic
-- name    : SpectralParab_Basic
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:43:55.515611+00:00
-- url     : https://prove2.me/theorems/02782200-f50b-4f6e-9dbf-825abb069c2a
-- title:
--   First-order variational analysis: domain, convexity, local Lipschitz continuity, subderivative, subdifferential, tangent sets, parabolic derivability
-- statement:
--   Let $\mathbf X$ be a real inner-product space and $f:\mathbf X\to\overline{\mathbb R}=[-\infty,\infty]$.
--
--   1. The **domain** is $\operatorname{dom} f=\{x\mid f(x)<\infty\}$; $f$ is **convex** if its epigraph $\{(x,\alpha)\in\mathbf X\times\mathbb R\mid f(x)\le\alpha\}$ is convex; $f$ is **proper** if it never equals $-\infty$ and is not identically $+\infty$.
--   2. $f$ is **locally Lipschitz continuous around $\bar x$ relative to $C\subset\operatorname{dom} f$** if $\bar x\in C$, $f(\bar x)$ is finite, and for some $\ell\ge0$ and some neighbourhood $U$ of $\bar x$, $|f(x)-f(y)|\le\ell\|x-y\|$ for all $x,y\in U\cap C$; it is **locally Lipschitz continuous relative to its domain** if this holds around every $\bar x\in\operatorname{dom} f$ with $C=\operatorname{dom} f$.
--   3. The **subderivative** at $\bar x$ (with $f(\bar x)$ finite) is
--   $$\mathrm df(\bar x)(\bar w)=\liminf_{t\downarrow0,\ w\to\bar w}\frac{f(\bar x+tw)-f(\bar x)}{t}.$$
--   4. The **subdifferential** at $\bar x$ with $f(\bar x)$ finite is $\partial f(\bar x)=\{v\mid f(x)\ge f(\bar x)+\langle v,x-\bar x\rangle\ \forall x\}$; it is empty when $f(\bar x)$ is not finite.
--   5. The **tangent cone** $T_C(\bar x)$ is the set of $w$ for which there are $t_k\downarrow0$, $w_k\to w$ with $\bar x+t_kw_k\in C$; the **second-order tangent set** (2.15) $T^2_C(\bar x,w)$ is the set of $u$ for which there are $t_k\downarrow0$, $u_k\to u$ with $\bar x+t_kw+\tfrac12t_k^2u_k\in C$.
--   6. $C$ is **parabolically derivable at $\bar x$ for $w$** if $T^2_C(\bar x,w)\ne\emptyset$ and for every $u\in T^2_C(\bar x,w)$ there are $\varepsilon>0$ and an arc $\xi:[0,\varepsilon]\to C$ with $\xi(0)=\bar x$, $\xi'_+(0)=w$ and $\xi''_+(0)=u$, where $\xi''_+(0)=\lim_{t\downarrow0}[\xi(t)-\xi(0)-t\xi'_+(0)]/\tfrac12t^2$.
--
--   These are the first-order objects of the paper's §2, written once for a general space so that they apply both to $\mathbb R^n$ and to the symmetric matrices $\mathbf S^n$.
--
--   **Formalization Note** Values are in `EReal`. Where the page assumes $f(\bar x)$ finite, the definitions subtract the real number $f(\bar x)$ (`toReal`), so $+\infty-c=+\infty$. Convexity bundles no properness or lower semicontinuity. The arc of item 6 is a plain function whose values on $[0,\varepsilon]$ lie in $C$, with no continuity requirement, as printed. The Lipschitz inequality is stated on real numbers together with finiteness of $f$ on $U\cap C$, which the printed inequality forces.
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, p.6 (domain, local Lipschitz continuity relative to a set, subderivative, subdifferential, (2.15), parabolic derivability), p.5 (tangent cone), p.9 (proper)

import Mathlib

open Filter Topology
open scoped RealInnerProductSpace

namespace SpectralParab

/-! # First-order variational objects on a real inner-product space

Mohammadi–Sarabi, *Parabolic Regularity of Spectral Functions*, arXiv:2301.04240v3, §2, pp.5–6.
The paper's space `X` is a finite-dimensional Hilbert space; the definitions below need no
finiteness of dimension, the theorems that use it assume `FiniteDimensional ℝ E`.

**Formalization Note.** Functions take values in `EReal` (the paper's `R̄ = [−∞, ∞]`). Every
quotient that the paper writes "with f(x̄) finite" subtracts the real number `(f x̄).toReal`, so
that `+∞ − c = +∞` and `−∞ − c = −∞`; the definitions are used only where `f x̄` is finite. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `dom f = {x | f x < ∞}` (arXiv:2301.04240v3, p.6). -/
def dom (f : E → EReal) : Set E := {x | f x < ⊤}

/-- Convexity of `f : E → R̄`: its epigraph `{(x, α) ∈ E × ℝ | f x ≤ α}` is convex (the convex-analysis
definition the paper uses). **Formalization Note.** No "never `−∞`", properness or lower
semicontinuity is bundled; theorems assume those separately where the paper does. -/
def IsConvexFn (f : E → EReal) : Prop :=
  Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)}

/-- Properness (arXiv:2301.04240v3, Proposition 3.4, p.9): `f` never takes the value `−∞` and is
not identically `+∞`. -/
def IsProperFn (f : E → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ ∃ x, f x ≠ ⊤

/-- Local Lipschitz continuity of `f` around `x̄` relative to `C ⊂ dom f` (arXiv:2301.04240v3, p.6):
`x̄ ∈ C`, `f x̄` finite, and for some `ℓ ≥ 0` and some neighbourhood `U` of `x̄`,
`|f x − f y| ≤ ℓ ‖x − y‖` for all `x, y ∈ U ∩ C`.
**Formalization Note.** The inequality is written on real numbers together with finiteness of
`f` on `U ∩ C`; that finiteness is forced by the printed inequality with `y = x̄`. -/
def LocLipRel (f : E → EReal) (C : Set E) (xbar : E) : Prop :=
  C ⊆ dom f ∧ xbar ∈ C ∧ f xbar ≠ ⊤ ∧ f xbar ≠ ⊥ ∧
    ∃ ℓ : ℝ, 0 ≤ ℓ ∧ ∃ U ∈ 𝓝 xbar, ∀ x ∈ U ∩ C, ∀ y ∈ U ∩ C,
      f x ≠ ⊤ ∧ f x ≠ ⊥ ∧ |(f x).toReal - (f y).toReal| ≤ ℓ * ‖x - y‖

/-- `f` is locally Lipschitz continuous relative to its domain (arXiv:2301.04240v3, p.6): locally
Lipschitz continuous around every `x̄ ∈ dom f` relative to `dom f`. -/
def LocLipOnDom (f : E → EReal) : Prop :=
  ∀ xbar ∈ dom f, LocLipRel f (dom f) xbar

/-- The subderivative (arXiv:2301.04240v3, p.6):
`df(x̄)(w̄) = liminf_{t ↓ 0, w → w̄} (f(x̄ + t w) − f(x̄)) / t`.
**Formalization Note.** `f(x̄)` enters as the real `(f x̄).toReal`; the definition is used only
where `f x̄` is finite. The `liminf` is taken in the complete lattice `EReal`. -/
noncomputable def subderiv (f : E → EReal) (xbar w : E) : EReal :=
  Filter.liminf
    (fun p : ℝ × E => (f (xbar + p.1 • p.2) - (((f xbar).toReal : ℝ) : EReal)) * ((p.1⁻¹ : ℝ) : EReal))
    ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 w)

/-- The convex-analysis subdifferential at a point where `f` is finite (arXiv:2301.04240v3, p.6):
`v ∈ ∂f(x̄)` iff `f x ≥ f x̄ + ⟨v, x − x̄⟩` for all `x`.
**Formalization Note.** `∂f(x̄) = ∅` when `f x̄` is not finite: the paper defines `∂f(x̄)` only at
points where `f(x̄)` is finite. -/
def subdiff (f : E → EReal) (xbar : E) : Set E :=
  {v | f xbar ≠ ⊤ ∧ f xbar ≠ ⊥ ∧
    ∀ x, ((((f xbar).toReal + ⟪v, x - xbar⟫ : ℝ)) : EReal) ≤ f x}

/-- The tangent cone (arXiv:2301.04240v3, p.5): `w ∈ T_C(x̄)` iff there are `t_k ↓ 0` and `w_k → w`
with `x̄ + t_k w_k ∈ C`. -/
def tangentCone (C : Set E) (xbar : E) : Set E :=
  {w | ∃ (t : ℕ → ℝ) (u : ℕ → E), (∀ k, 0 < t k) ∧ Tendsto t atTop (𝓝 0) ∧
    Tendsto u atTop (𝓝 w) ∧ ∀ k, xbar + t k • u k ∈ C}

/-- The second-order tangent set (2.15) (arXiv:2301.04240v3, p.6): `u ∈ T²_C(x̄, w)` iff there are
`t_k ↓ 0` and `u_k → u` with `x̄ + t_k w + ½ t_k² u_k ∈ C`. -/
def secondTangentSet (C : Set E) (xbar w : E) : Set E :=
  {u | ∃ (t : ℕ → ℝ) (v : ℕ → E), (∀ k, 0 < t k) ∧ Tendsto t atTop (𝓝 0) ∧
    Tendsto v atTop (𝓝 u) ∧ ∀ k, xbar + t k • w + (t k ^ 2 / 2) • v k ∈ C}

/-- Parabolic derivability (arXiv:2301.04240v3, p.6): `T²_C(x̄, w)` is nonempty and for every
`u ∈ T²_C(x̄, w)` there are `ε > 0` and an arc `ξ : [0, ε] → C` with `ξ(0) = x̄`, `ξ'_+(0) = w` and
`ξ''_+(0) = u`, where `ξ'_+(0) = lim_{t↓0} (ξ(t) − ξ(0))/t` and
`ξ''_+(0) = lim_{t↓0} (ξ(t) − ξ(0) − t ξ'_+(0)) / (½ t²)`.
**Formalization Note.** The arc is a plain function `ℝ → E` whose values on `[0, ε]` lie in `C`
(values elsewhere are never read); no continuity is required, as on the page. -/
def ParabDerivable (C : Set E) (xbar w : E) : Prop :=
  (secondTangentSet C xbar w).Nonempty ∧
    ∀ u ∈ secondTangentSet C xbar w, ∃ ε : ℝ, 0 < ε ∧ ∃ ξ : ℝ → E,
      (∀ t ∈ Set.Icc (0 : ℝ) ε, ξ t ∈ C) ∧ ξ 0 = xbar ∧
      Tendsto (fun t : ℝ => t⁻¹ • (ξ t - ξ 0)) (𝓝[>] 0) (𝓝 w) ∧
      Tendsto (fun t : ℝ => (2 / t ^ 2) • (ξ t - ξ 0 - t • w)) (𝓝[>] 0) (𝓝 u)

end SpectralParab


