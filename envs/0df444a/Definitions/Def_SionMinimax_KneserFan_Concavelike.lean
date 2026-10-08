-- Prove2me | Definitions.Def_SionMinimax_KneserFan_Concavelike
-- name    : SionMinimax_KneserFan_Concavelike
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:52:21.720979+00:00
-- url     : https://prove2.me/theorems/4dfc2835-5ea1-4a93-b1ae-63b06c2e0b9d
-- title:
--   Definitions 2.1–2.3 and 2.8, p. 172 — concavelike, convexlike, concave-convexlike functions (Fan) and sup inf f, inf sup f
-- statement:
--   Let $M$ and $N$ be arbitrary sets (no linear or topological structure is assumed) and let $f : M\times N\to\mathbb R$ be a real-valued function. Following K. Fan, Sion introduces three notions that generalize concavity and convexity to spaces without linear structure.
--
--   1. **Concavelike in $M$** (Definition 2.1). For every $\mu_1,\mu_2\in M$ and every $0\le t\le 1$ there is a single point $\mu\in M$ such that
--   $$
--   t\,f(\mu_1,\nu)+(1-t)\,f(\mu_2,\nu)\le f(\mu,\nu)\qquad\text{for all }\nu\in N .
--   $$
--   2. **Convexlike in $N$** (Definition 2.2). For every $\nu_1,\nu_2\in N$ and every $0\le t\le 1$ there is a single point $\nu\in N$ such that
--   $$
--   t\,f(\mu,\nu_1)+(1-t)\,f(\mu,\nu_2)\ge f(\mu,\nu)\qquad\text{for all }\mu\in M .
--   $$
--   3. **Concave-convexlike** (Definition 2.3): concavelike in $M$ and convexlike in $N$.
--
--   In each case the witness point is chosen once, depending only on the two given points and on $t$, and must work simultaneously for every point of the other space.
--
--   Definition 2.8 sets
--   $$
--   \sup\inf f=\sup_{\mu\in M}\inf_{\nu\in N} f(\mu,\nu),\qquad \inf\sup f=\inf_{\nu\in N}\sup_{\mu\in M} f(\mu,\nu).
--   $$
--   These values are extended real numbers: they may be $+\infty$ or $-\infty$ when $f$ is unbounded, and the supremum (infimum) over an empty set is $-\infty$ ($+\infty$).
--
--   These are the notions in which Theorems 4.1, 4.1′, 4.2 (Kneser–Fan) and 4.2′ of Sion's paper are stated.
--
--   **Formalization Note** The spaces are arbitrary types `M N` and `f : M → N → ℝ`. The quantities $\sup\inf f$ and $\inf\sup f$ are `supInf f` and `infSup f`, computed in `EReal` from the coercion of $f$, so no junk value of a real supremum enters. The first argument of $f$ is the maximizing variable $\mu$, the second the minimizing variable $\nu$, as in the paper.
-- source:
--   Sion, On general minimax theorems, Pacific J. Math. 8(1) (1958) 171–176, p. 172 (PDF p. 3), Definitions 2.1, 2.2, 2.3 and 2.8

import Mathlib

namespace SionMinimax.KneserFan

/-- Sion 1958, Definition 2.1, p. 172 (after K. Fan): `f` is concavelike in `M` if for every
`μ₁ μ₂ ∈ M` and `0 ≤ t ≤ 1` there is a single `μ ∈ M` with
`t f(μ₁, ν) + (1 - t) f(μ₂, ν) ≤ f(μ, ν)` for all `ν ∈ N`. -/
def Concavelike {M N : Type*} (f : M → N → ℝ) : Prop :=
  ∀ μ₁ μ₂ : M, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    ∃ μ : M, ∀ ν : N, t * f μ₁ ν + (1 - t) * f μ₂ ν ≤ f μ ν

/-- Sion 1958, Definition 2.2, p. 172 (after K. Fan): `f` is convexlike in `N` if for every
`ν₁ ν₂ ∈ N` and `0 ≤ t ≤ 1` there is a single `ν ∈ N` with
`t f(μ, ν₁) + (1 - t) f(μ, ν₂) ≥ f(μ, ν)` for all `μ ∈ M`. -/
def Convexlike {M N : Type*} (f : M → N → ℝ) : Prop :=
  ∀ ν₁ ν₂ : N, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    ∃ ν : N, ∀ μ : M, f μ ν ≤ t * f μ ν₁ + (1 - t) * f μ ν₂

/-- Sion 1958, Definition 2.3, p. 172: `f` is concave-convexlike if it is concavelike in `M`
and convexlike in `N`. -/
def ConcaveConvexlike {M N : Type*} (f : M → N → ℝ) : Prop :=
  Concavelike f ∧ Convexlike f

/-- Sion 1958, Definition 2.8, p. 172: `sup inf f = sup_{μ ∈ M} inf_{ν ∈ N} f(μ, ν)`, computed in
the extended reals (the empty supremum is `⊥`, the empty infimum is `⊤`). -/
noncomputable def supInf {M N : Type*} (f : M → N → ℝ) : EReal :=
  ⨆ μ : M, ⨅ ν : N, ((f μ ν : ℝ) : EReal)

/-- Sion 1958, Definition 2.8, p. 172: `inf sup f = inf_{ν ∈ N} sup_{μ ∈ M} f(μ, ν)`, computed in
the extended reals. -/
noncomputable def infSup {M N : Type*} (f : M → N → ℝ) : EReal :=
  ⨅ ν : N, ⨆ μ : M, ((f μ ν : ℝ) : EReal)

end SionMinimax.KneserFan


