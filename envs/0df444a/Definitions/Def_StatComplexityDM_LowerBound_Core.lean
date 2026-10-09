-- Prove2me | Definitions.Def_StatComplexityDM_LowerBound_Core
-- name    : StatComplexityDM_LowerBound_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:20:05.808628+00:00
-- url     : https://prove2.me/theorems/4c2d524c-c5f6-4ad1-8853-f04dcda6e2cb
-- title:
--   §1.1–§2 and (12), pp. 5–12 — probability vectors, models as kernels, the argmax selector and the L∞-localized class M^∞_ε(M̄)
-- statement:
--   A **probability vector** on a finite set $X$ is a map $\mu:X\to\mathbb R$ with $\mu(x)\ge 0$ for all $x$ and $\sum_x\mu(x)=1$; this is $\Delta(X)$. A **model** $M$ assigns to every decision $\pi\in\Pi$ a probability vector $M(\pi)$ on the finite outcome set $\mathcal Y=\mathcal R\times\mathcal O$ of joint reward–observation pairs. With the reward map $r:\mathcal Y\to\mathbb R$, the mean reward is $f^M(\pi)=\sum_y M(\pi)(y)\,r(y)$, and a **selector** $M\mapsto\pi_M$ is an argmax selector if $f^M(\pi)\le f^M(\pi_M)$ for every model $M$ and decision $\pi$.
--
--   Writing $g^M(\pi):=f^M(\pi_M)-f^M(\pi)$ for the regret of $\pi$ under $M$, the **$L^\infty$-localized class** around a reference model $\bar M$ is
--
--   $$
--   \mathcal M^\infty_\varepsilon(\bar M)=\bigl\{M\in\mathcal M:\ |g^M(\pi)-g^{\bar M}(\pi)|\le\varepsilon\ \text{ for all }\pi\in\Pi\bigr\}.
--   $$
--
--   These objects are the common vocabulary of the lower bound: the localized class is the class over which the decision-estimation coefficient of Theorem 3.2 is taken.
--
--   **Formalization Note** Decisions $\Pi$ and joint reward–observation outcomes $\mathcal R\times\mathcal O$ are finite alphabets (the finite-alphabet case of the paper's measurable setting, §2, p. 9); models and algorithm kernels are probability vectors and expectations are finite sums. The paper's $\arg\max$ is any maximizer; the selector is a parameter, so results hold for every choice.
-- source:
--   arXiv:2112.13487v3, §1.1, p. 5; §2, pp. 9–10; (12), p. 12

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol

namespace StatComplexityDM.LowerBound

open FoundationsRL.GeneralDM

/-- A probability distribution on a finite type: nonnegative weights summing to one
(`Δ(X)`, arXiv:2112.13487v3, §2, p. 10). -/
def IsDist {X : Type*} [Fintype X] (μ : X → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1

/-- A model is a probability kernel from decisions to outcomes, `M : Π → Δ(R × O)`
(§1.1, p. 5; §2, p. 9), on finite alphabets: every `m π` is a probability vector. -/
def IsModel {S Y : Type*} [Fintype Y] (m : S → Y → ℝ) : Prop :=
  ∀ π, IsDist (m π)

/-- `piStar` selects a maximizer of every model's mean reward, `π_M := arg max_{π∈Π} f^M(π)` (p. 5). -/
def IsArgmaxSel {S Y : Type*} [Fintype S] [Fintype Y] (rew : Y → ℝ)
    (piStar : (S → Y → ℝ) → S) : Prop :=
  ∀ m π, fM rew m π ≤ fM rew m (piStar m)

/-- The L∞-localized class (12), p. 12: with `g^M(π) := f^M(π_M) − f^M(π)`,
`M^∞_ε(M̄) = {M ∈ M : |g^M(π) − g^{M̄}(π)| ≤ ε ∀ π ∈ Π}`. -/
def linfLocalized {S Y : Type*} [Fintype S] [Fintype Y] (𝓜 : Set (S → Y → ℝ)) (rew : Y → ℝ)
    (piStar : (S → Y → ℝ) → S) (mbar : S → Y → ℝ) (ε : ℝ) : Set (S → Y → ℝ) :=
  {m ∈ 𝓜 | ∀ π, |(fM rew m (piStar m) - fM rew m π) - (fM rew mbar (piStar mbar) - fM rew mbar π)| ≤ ε}

end StatComplexityDM.LowerBound


