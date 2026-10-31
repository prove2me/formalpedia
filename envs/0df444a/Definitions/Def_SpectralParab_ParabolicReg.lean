-- Prove2me | Definitions.Def_SpectralParab_ParabolicReg
-- name    : SpectralParab_ParabolicReg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:44:51.261007+00:00
-- url     : https://prove2.me/theorems/6b3889a9-bab7-47b1-b3f9-75e029cadb89
-- title:
--   Parabolic subderivative, parabolic epi-differentiability, second subderivative, parabolic regularity (Definition 5.1) and critical cone
-- statement:
--   Let $f:\mathbf X\to\overline{\mathbb R}$, $\bar x$ with $f(\bar x)$ finite.
--
--   1. For $w$ with $\mathrm df(\bar x)(w)$ finite, the **parabolic subderivative** of $f$ at $\bar x$ for $w$ with respect to $z$ is
--   $$\mathrm d^2f(\bar x)(w\,|\,z)=\liminf_{t\downarrow0,\ z'\to z}\frac{f(\bar x+tw+\tfrac12t^2z')-f(\bar x)-t\,\mathrm df(\bar x)(w)}{\tfrac12t^2}.$$
--   2. $f$ is **parabolically epi-differentiable at $\bar x$ for $w$** if $\{z\mid \mathrm d^2f(\bar x)(w|z)<\infty\}\ne\emptyset$ and for every $z$ and every $t_k\downarrow0$ there are $z_k\to z$ along which the quotient of item 1 converges to $\mathrm d^2f(\bar x)(w|z)$ (4.13); it is parabolically epi-differentiable at $\bar x$ if this holds for every $w$ with $\mathrm df(\bar x)(w)$ finite.
--   3. For $\bar v\in\mathbf X$ and $t>0$, $\Delta^2_tf(\bar x,\bar v)(w)=\dfrac{f(\bar x+tw)-f(\bar x)-t\langle\bar v,w\rangle}{\tfrac12t^2}$, and the **second subderivative** is $\mathrm d^2f(\bar x,\bar v)(w)=\liminf_{t\downarrow0,\,w'\to w}\Delta^2_tf(\bar x,\bar v)(w')$.
--   4. (Definition 5.1) $f$ is **parabolically regular at $\bar x$ for $\bar v$** if for every $w$ with $\mathrm d^2f(\bar x,\bar v)(w)<\infty$ there are $t_k\downarrow0$ and $w_k\to w$ with $\Delta^2_{t_k}f(\bar x,\bar v)(w_k)\to\mathrm d^2f(\bar x,\bar v)(w)$ and $\limsup_k\|w_k-w\|/t_k<\infty$; it is parabolically regular at $\bar x$ if this holds for every $\bar v\in\partial f(\bar x)$.
--   5. The **critical cone** is $K_f(\bar x,\bar v)=\{w\mid \mathrm df(\bar x)(w)=\langle\bar v,w\rangle\}$.
--
--   Parabolic regularity is the second-order regularity whose transfer between $\theta$ and $\theta\circ\lambda$ is the subject of the mission.
--
--   **Formalization Note** `EReal` values; $f(\bar x)$ and $\mathrm df(\bar x)(w)$ enter as reals. Parabolic epi-differentiability at $\bar x$ for $w$ includes the page's standing finiteness of $f(\bar x)$ and $\mathrm df(\bar x)(w)$. The limsup condition is written $\exists C,\ \forall k,\ \|w_k-w\|\le Ct_k$, equivalent since $t_k>0$. The page defines parabolic regularity for convex $f$ and $\bar v\in\partial f(\bar x)$; the Lean predicate at $(\bar x,\bar v)$ does not repeat these, and every theorem supplies them.
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, p.17 (parabolic subderivative, (4.13)), p.22 (Δ²_t, second subderivative, Definition 5.1, critical cone)

import Mathlib
import Definitions.Def_SpectralParab_Basic

open Filter Topology
open scoped RealInnerProductSpace

namespace SpectralParab

/-! # Parabolic subderivatives, second subderivatives and parabolic regularity

Mohammadi–Sarabi, arXiv:2301.04240v3, p.17 (parabolic subderivative, (4.13)) and p.22
(second-order difference quotients, second subderivative, Definition 5.1, critical cone).

**Formalization Note.** Values in `EReal`; `f(x̄)` and `df(x̄)(w)` enter as the reals
`(f x̄).toReal` and `(subderiv f x̄ w).toReal`, as the page assumes both finite. Division by
`t > 0` or `½ t²` is multiplication by the real reciprocal. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The parabolic difference quotient
`(f(x̄ + t w + ½ t² z) − f(x̄) − t df(x̄)(w)) / (½ t²)` (arXiv:2301.04240v3, p.17). -/
noncomputable def parabQuot (f : E → EReal) (xbar w z : E) (t : ℝ) : EReal :=
  (f (xbar + t • w + (t ^ 2 / 2) • z) -
      (((f xbar).toReal + t * (subderiv f xbar w).toReal : ℝ) : EReal)) * ((2 / t ^ 2 : ℝ) : EReal)

/-- The parabolic subderivative (arXiv:2301.04240v3, p.17):
`d²f(x̄)(w | z) = liminf_{t↓0, z'→z} (f(x̄ + t w + ½ t² z') − f(x̄) − t df(x̄)(w)) / (½ t²)`,
meaningful when `f(x̄)` and `df(x̄)(w)` are finite. -/
noncomputable def parabSubderiv (f : E → EReal) (xbar w z : E) : EReal :=
  Filter.liminf (fun p : ℝ × E => parabQuot f xbar w p.2 p.1) ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 z)

/-- Parabolic epi-differentiability at `x̄` for `w` (arXiv:2301.04240v3, p.17, [27, Def. 13.59]):
with `f(x̄)` and `df(x̄)(w)` finite, `dom d²f(x̄)(w | ·) ≠ ∅`, and for every `z` and every `t_k ↓ 0`
there are `z_k → z` with the quotients converging to `d²f(x̄)(w | z)` (4.13).
**Formalization Note.** The page's standing finiteness of `f(x̄)` and `df(x̄)(w)` is a conjunct. -/
def ParabEpiDiffAt (f : E → EReal) (xbar w : E) : Prop :=
  f xbar ≠ ⊤ ∧ f xbar ≠ ⊥ ∧ subderiv f xbar w ≠ ⊤ ∧ subderiv f xbar w ≠ ⊥ ∧
    (∃ z, parabSubderiv f xbar w z < ⊤) ∧
    ∀ (z : E) (t : ℕ → ℝ), (∀ k, 0 < t k) → Tendsto t atTop (𝓝 0) →
      ∃ zs : ℕ → E, Tendsto zs atTop (𝓝 z) ∧
        Tendsto (fun k => parabQuot f xbar w (zs k) (t k)) atTop (𝓝 (parabSubderiv f xbar w z))

/-- Parabolic epi-differentiability at `x̄` (arXiv:2301.04240v3, p.17): at every `w` with
`df(x̄)(w)` finite. -/
def ParabEpiDiff (f : E → EReal) (xbar : E) : Prop :=
  ∀ w, subderiv f xbar w ≠ ⊤ → subderiv f xbar w ≠ ⊥ → ParabEpiDiffAt f xbar w

/-- The second-order difference quotient (arXiv:2301.04240v3, p.22):
`Δ²_t f(x̄, v̄)(w) = (f(x̄ + t w) − f(x̄) − t ⟨v̄, w⟩) / (½ t²)`. -/
noncomputable def delta2 (f : E → EReal) (xbar vbar w : E) (t : ℝ) : EReal :=
  (f (xbar + t • w) - (((f xbar).toReal + t * ⟪vbar, w⟫ : ℝ) : EReal)) * ((2 / t ^ 2 : ℝ) : EReal)

/-- The second subderivative (arXiv:2301.04240v3, p.22):
`d²f(x̄, v̄)(w) = liminf_{t↓0, w'→w} Δ²_t f(x̄, v̄)(w')`. -/
noncomputable def secondSubderiv (f : E → EReal) (xbar vbar w : E) : EReal :=
  Filter.liminf (fun p : ℝ × E => delta2 f xbar vbar p.2 p.1) ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 w)

/-- Definition 5.1 (arXiv:2301.04240v3, p.22), parabolic regularity at `x̄` for `v̄`: for every `w`
with `d²f(x̄, v̄)(w) < ∞` there are `t_k ↓ 0` and `w_k → w` with
`Δ²_{t_k} f(x̄, v̄)(w_k) → d²f(x̄, v̄)(w)` and `limsup ‖w_k − w‖ / t_k < ∞`.
**Formalization Note.** `limsup_k ‖w_k − w‖/t_k < ∞` is written `∃ C, ∀ k, ‖w_k − w‖ ≤ C t_k`,
equivalent because `t_k > 0`. The page defines the notion for convex `f` and `v̄ ∈ ∂f(x̄)`; those
are not bundled here, and every use supplies them or they follow from its hypotheses. -/
def ParabRegularAt (f : E → EReal) (xbar vbar : E) : Prop :=
  ∀ w, secondSubderiv f xbar vbar w < ⊤ →
    ∃ (t : ℕ → ℝ) (ws : ℕ → E), (∀ k, 0 < t k) ∧ Tendsto t atTop (𝓝 0) ∧
      Tendsto ws atTop (𝓝 w) ∧
      Tendsto (fun k => delta2 f xbar vbar (ws k) (t k)) atTop (𝓝 (secondSubderiv f xbar vbar w)) ∧
      ∃ C : ℝ, ∀ k, ‖ws k - w‖ ≤ C * t k

/-- Parabolic regularity at `x̄` (Definition 5.1, p.22): at `x̄` for every `v̄ ∈ ∂f(x̄)`. -/
def ParabRegular (f : E → EReal) (xbar : E) : Prop :=
  ∀ vbar ∈ subdiff f xbar, ParabRegularAt f xbar vbar

/-- The critical cone (arXiv:2301.04240v3, p.22): `K_f(x̄, v̄) = {w | df(x̄)(w) = ⟨v̄, w⟩}`. -/
def critCone (f : E → EReal) (xbar vbar : E) : Set E :=
  {w | subderiv f xbar w = ((⟪vbar, w⟫ : ℝ) : EReal)}

end SpectralParab


