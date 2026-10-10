-- Prove2me | Definitions.Def_ConvexSDDP_Det_Basic
-- name    : ConvexSDDP_Det_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:06:54.289065+00:00
-- url     : https://prove2.me/theorems/5c81d984-b4ef-4ceb-9f99-c8103ed07117
-- title:
--   Footnote 2, p. 4 and (H1)(3) — proper and convex extended-real functions; convex multifunctions
-- statement:
--   Three elementary notions of convex analysis for functions with values in the extended real line $\overline{\mathbb R}=\mathbb R\cup\{-\infty,+\infty\}$ and for set-valued maps.
--
--   1. A function $g:Z\to\overline{\mathbb R}$ is **proper** when $g(z)>-\infty$ for every $z$ and $g(z)<+\infty$ for at least one $z$.
--   2. A function $g:Z\to\overline{\mathbb R}$ on a real vector space $Z$ is **convex** when its epigraph
--   $$\operatorname{epi} g=\{(z,r)\in Z\times\mathbb R:\ g(z)\le r\}$$
--   is a convex subset of $Z\times\mathbb R$.
--   3. (Footnote 2, p. 4.) A multifunction $\mathcal U:E\rightrightarrows F$ between real vector spaces is **convex** when
--   $$(1-\lambda)\,\mathcal U(x)+\lambda\,\mathcal U(y)\subseteq \mathcal U\big((1-\lambda)x+\lambda y\big)\qquad\text{for all }x,y\in E,\ \lambda\in(0,1),$$
--   i.e. for all $a\in\mathcal U(x)$, $b\in\mathcal U(y)$ the point $(1-\lambda)a+\lambda b$ lies in $\mathcal U((1-\lambda)x+\lambda y)$.
--
--   These notions express assumptions (H₁)(2)–(3) of the paper on the control sets $\mathcal U_t$, the stage costs $C_t$ and the final cost $V_T$, and the conclusions of Lemmas 5.1 and 2.2.
--
--   **Formalization Note** Convexity is epigraph convexity, which is the standard meaning for extended-real-valued functions (Mathlib's `ConvexOn` needs a module structure on the codomain, which `EReal` lacks). Footnote 2 states convexity of $\mathcal U$ on a convex set $\mathcal X$; here $\mathcal U_t$ is defined on all of $\mathbb R^n$ (p. 4), so the condition is imposed for all $x,y$.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, p. 4, (H1)(2)–(3) and footnote 2

import Mathlib

namespace ConvexSDDP.Det

/-- A function into `ℝ ∪ {±∞}` (`EReal`) is *proper* when it never takes the value `-∞`
and is not identically `+∞`. -/
def EProper {Z : Type*} (g : Z → EReal) : Prop :=
  (∀ z, g z ≠ ⊥) ∧ ∃ z, g z ≠ ⊤

/-- A function `g : Z → ℝ ∪ {±∞}` on a real vector space is *convex* when its epigraph
`{(z, r) ∈ Z × ℝ | g z ≤ r}` is a convex set. -/
def EConvex {Z : Type*} [AddCommGroup Z] [Module ℝ Z] (g : Z → EReal) : Prop :=
  Convex ℝ {q : Z × ℝ | g q.1 ≤ (q.2 : EReal)}

/-- Footnote 2, p. 4: a multifunction `U : E ⇒ F` is *convex* when
`(1 - λ) U(x) + λ U(y) ⊆ U((1 - λ) x + λ y)` for all `x, y` and all `λ ∈ (0, 1)`. -/
def ConvexMultifunction {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] (U : E → Set F) : Prop :=
  ∀ x y : E, ∀ a ∈ U x, ∀ b ∈ U y, ∀ l : ℝ, 0 < l → l < 1 →
    (1 - l) • a + l • b ∈ U ((1 - l) • x + l • y)

end ConvexSDDP.Det


