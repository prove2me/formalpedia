-- Prove2me | Definitions.Def_OnlineUBSR_ubsr
-- name    : OnlineUBSR_ubsr
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:52.604686+00:00
-- url     : https://prove2.me/theorems/6b71180f-226a-4a7a-8ebc-6ab85d6337b7
-- title:
--   Utility-based shortfall risk $SR_\lambda(X)=\inf\{t:t+X\in\mathcal A\}$
-- statement:
--   For a random variable $X$, a loss $\ell$ and a risk level $\lambda$, the **utility-based shortfall risk** of $X$ is
--
--   $$
--   SR_\lambda(X)=\inf\{\,t\in\mathbb R:\ t+X\in\mathcal A\,\},
--   $$
--
--   where $\mathcal A$ is the acceptance set. If $X$ is a financial position, $SR_\lambda(X)$ is the minimum amount of cash that must be added to $X$ to make it acceptable. It is a convex risk measure and an elicitable one.
--
--   **Formalization Note** The infimum is the real `sInf`, which is $0$ on an empty or unbounded-below set. Under the mission's hypotheses (Assumption 1, bounded $X$, convex $\ell$) the set is nonempty and bounded below, and `OnlineUBSR.sr_is_root` shows $SR_\lambda(X)\in(t_l,t_u)$, so this junk value does not occur.
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, Online Estimation and Optimization of Utility-Based Shortfall Risk, arXiv:2111.08805v3, §2, eq. (2), p.3

import Mathlib
import Definitions.Def_OnlineUBSR_acceptanceSet

open MeasureTheory

namespace OnlineUBSR

/-- **Utility-based shortfall risk `SR_λ(X)`.**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, §2, (2), p.3: "Using the acceptance
set, the utility-based shortfall risk (UBSR) SRλ(X) is defined by SRλ(X) := inf{t ∈ ℛ : t + X ∈ A}."

`ubsr μ ℓ lam X` is the infimum of the cash amounts `t` for which `t + X` lies in the acceptance
set `A` of (1).

**Formalization Note.** The infimum is the real `sInf`, which returns `0` on an empty or
unbounded-below set. Under the hypotheses of the mission (Assumption 1, a bounded `X`, a convex
`ℓ`) the set is nonempty and bounded below, and the milestone `OnlineUBSR.sr_is_root` shows that
`ubsr` lies strictly between `t_l` and `t_u` and is the root of `g`; so the junk value never
occurs there. -/
noncomputable def ubsr {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ℓ : ℝ → ℝ) (lam : ℝ)
    (X : Ω → ℝ) : ℝ :=
  sInf {t : ℝ | (fun ω => t + X ω) ∈ acceptanceSet μ ℓ lam}

end OnlineUBSR


