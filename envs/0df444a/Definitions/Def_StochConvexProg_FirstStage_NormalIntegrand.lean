-- Prove2me | Definitions.Def_StochConvexProg_FirstStage_NormalIntegrand
-- name    : StochConvexProg_FirstStage_NormalIntegrand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:22.923141+00:00
-- url     : https://prove2.me/theorems/024b2a40-82c4-49ad-b6f9-beea7936a422
-- title:
--   Normal convex integrands (pp. 180–181)
-- statement:
--   Let $(S,\Sigma)$ be a measurable space and $E$ a finite-dimensional real normed space with its Borel $\sigma$-algebra (in the paper, $E=\mathbb R^n$). A function $h:S\times E\to(-\infty,+\infty]$ is a *normal convex integrand* if
--
--   1. for each $s\in S$, $h(s,\cdot)$ is a lower semicontinuous convex function on $E$ with values in $(-\infty,+\infty]$, not identically $+\infty$;
--   2. there is a sequence of measurable functions $z^k:S\to E$, $k=1,2,\dots$, such that $s\mapsto h(s,z^k(s))$ is measurable for each $k$, while for each fixed $s$ the points $z^k(s)$ lying in
--   $$\operatorname{dom}h(s,\cdot)=\{z\in E\mid h(s,z)<+\infty\}$$
--   are dense in that set.
--
--   Normality is the hypothesis under which the integral functional $I_h(z)=\int_S h(s,z(s))\,\sigma(ds)$ is well behaved: $h(s,z(s))$ is measurable for measurable $z$, and the infimum of $I_h$ over $\mathcal L^p$ is the integral of the pointwise infimum (Proposition 1).
--
--   **Formalization Note** Convexity of $h(s,\cdot)$ is convexity of its epigraph $\{(z,t)\in E\times\mathbb R\mid h(s,z)\le t\}$, since $h$ takes the value $+\infty$; values lie in `EReal` and "values in $(-\infty,+\infty]$" is $h(s,z)\ne-\infty$. The page's $k=1,2,\dots$ is indexed by `ℕ`. $E$ is generic so that Proposition 2 can apply the notion on $\mathbb R^{n_1}\times\mathbb R^{n_2}\times\mathbb R^{m_2}$.
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), pp. 180–181, definition of a normal convex integrand

import Mathlib

open MeasureTheory

namespace StochConvexProg.FirstStage

/-- Rockafellar–Wets (1976), pp. 180–181: `h : S × E → (−∞, +∞]` is a *normal convex integrand*
if each `h(s, ·)` is lower semicontinuous, convex (convex epigraph), nowhere `−∞` and not
identically `+∞`, and there is a sequence of measurable `zᵏ : S → E` with `s ↦ h(s, zᵏ(s))`
measurable, such that for each `s` the points `zᵏ(s)` lying in `dom h(s, ·)` are dense in it. -/
def IsNormalConvexIntegrand {S E : Type*} [MeasurableSpace S] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] (h : S → E → EReal) : Prop :=
  (∀ s, LowerSemicontinuous (h s)) ∧
  (∀ s, Convex ℝ {p : E × ℝ | h s p.1 ≤ (p.2 : EReal)}) ∧
  (∀ s z, h s z ≠ ⊥) ∧ (∀ s, ∃ z, h s z ≠ ⊤) ∧
  ∃ zk : ℕ → S → E, (∀ k, Measurable (zk k)) ∧ (∀ k, Measurable (fun s => h s (zk k s))) ∧
    ∀ s, {z | h s z < ⊤} ⊆ closure {z | ∃ k, zk k s = z ∧ h s z < ⊤}

end StochConvexProg.FirstStage


