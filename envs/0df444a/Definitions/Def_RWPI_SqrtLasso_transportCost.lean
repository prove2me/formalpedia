-- Prove2me | Definitions.Def_RWPI_SqrtLasso_transportCost
-- name    : RWPI_SqrtLasso_transportCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T09:28:06.643885+00:00
-- url     : https://prove2.me/theorems/75a7b3ce-9809-4242-9a9b-5630a38ce98c
-- title:
--   Optimal transport cost $D_c(P,Q)$ for a $[0,\infty]$-valued cost (Eq. (7))
-- statement:
--   Let $Z$ be a measurable space and let $c : Z \times Z \to [0,\infty]$ be a cost function; $c(u,w)$ is the cost of transporting a unit of mass from $u$ to $w$. For two probability measures $P$ and $Q$ on $Z$, the **optimal transport cost** (or discrepancy) between $P$ and $Q$ is
--
--   $$
--   D_c(P,Q) = \inf\Big\{ \mathbb E_\pi\big[c(U,W)\big] \;:\; \pi \in \mathcal P(Z\times Z),\ \pi_U = P,\ \pi_W = Q \Big\},
--   $$
--
--   where $\mathcal P(Z\times Z)$ is the set of probability measures $\pi$ on $Z\times Z$ (the joint laws of a pair $(U,W)$) and $\pi_U$, $\pi_W$ are the two marginals of $\pi$. A probability measure with prescribed marginals $P$ and $Q$ is a **coupling** of $P$ and $Q$.
--
--   In the paper $Z = \mathbb R^m$, the cost is lower semicontinuous and vanishes on the diagonal. Allowing the cost to take the value $+\infty$ is essential: the cost $N_q$ of Eq. (14), which forbids moving the response variable, is infinite off the set $\{y = v\}$. For $c(u,w) = \|u-w\|^\rho$ the quantity $D_c^{1/\rho}$ is the Wasserstein distance of order $\rho$.
--
--   **Formalization Note** The value lies in $[0,\infty]$ (`ENNReal`); the expectation is the lower Lebesgue integral $\int^- c\,d\pi$, so an infinite expected cost is $+\infty$, never a junk real. The infimum runs over probability measures `π` on `Z × Z` with `π.map Prod.fst = P` and `π.map Prod.snd = Q`; both marginals are fixed. If there is no coupling (for instance, if $P$ or $Q$ is not a probability measure) the infimum of the empty family is $+\infty$. The standing assumptions on $c$ (lower semicontinuity, $c(u,u)=0$) are hypotheses of the theorems, not part of the definition.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 8, §2.1, Eq. (7)

import Mathlib

open MeasureTheory

namespace RWPI.SqrtLasso

/-- The optimal transport cost (discrepancy) `D_c(P, Q)` of Blanchet, Kang & Murthy, Eq. (7), p. 8:
`D_c(P, Q) = inf { E_π[c(U, W)] : π ∈ 𝒫(Z × Z), π_U = P, π_W = Q }`.
The infimum ranges over probability measures `π` on `Z × Z` whose first marginal is `P` and whose
second marginal is `Q`. The cost `c` is `[0, ∞]`-valued and the expectation is the lower Lebesgue
integral, so an infinite cost and an infinite expected cost are represented as `⊤`. If no such
coupling exists (e.g. `P` or `Q` is not a probability measure) the value is `⊤`. -/
noncomputable def transportCost {Z : Type*} [MeasurableSpace Z] (c : Z → Z → ENNReal)
    (P Q : Measure Z) : ENNReal :=
  ⨅ (π : Measure (Z × Z)) (_ : IsProbabilityMeasure π ∧ π.map Prod.fst = P ∧ π.map Prod.snd = Q),
    ∫⁻ w, c w.1 w.2 ∂π

end RWPI.SqrtLasso


