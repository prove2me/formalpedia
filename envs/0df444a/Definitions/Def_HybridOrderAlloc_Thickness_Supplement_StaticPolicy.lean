-- Prove2me | Definitions.Def_HybridOrderAlloc_Thickness_Supplement_StaticPolicy
-- name    : HybridOrderAlloc_Thickness_Supplement_StaticPolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:08:11.53137+00:00
-- url     : https://prove2.me/theorems/5335c4e4-d668-4b55-a20d-c9eafd2f846f
-- title:
--   §4.3, (9), pp. 20–21 — the static order-allocation policy y^static(M, D) = (µ0 − µ)₊M ∧ D
-- statement:
--   In §4.3 He and Goh compare their dynamic order-allocation problem (5) with its single-period version, which after removing constants is the problem
--
--   $$\max_{0\le y\le D}\Big\{-\frac{pR}{M}\,y^2+2pR(\mu_0-\mu)\,y\Big\}, \tag{9}$$
--
--   where $M>0$ is the market thickness (number of freelancers on the platform), $D>0$ the firm's demand, $\mu=\mathbb E\beta$ the mean cross-network effect, $p$ the per-order price, $R$ the relative inefficiency of freelancers, and $\mu_0=(p-r)/(2pR)$ as in Definition 1. The **static policy** is
--
--   $$y^{\mathrm{static}}(M,D):=\min\big\{(\mu_0-\mu)_+\,M,\; D\big\},\qquad (x)_+=\max\{x,0\}.$$
--
--   It transfers the unconstrained maximizer $(\mu_0-\mu)M$ of (9), cut off at $0$ and at the capacity $D$. The paper states that it solves (9); that remark is not part of this definition.
--
--   This is the benchmark against which Theorem 2 compares the optimal dynamic policy.
--
--   **Formalization Note** The definition builds on the published model `HybridOrderAlloc.Thickness.Model` (`Sys`, `mu`, `mu0`). The printed $(\mu_0-\mu)_+M\wedge D$ is read as $((\mu_0-\mu)_+M)\wedge D$, as the proof of Theorem 2 (p. 40, $y^U_T=(\mu_0-\mu)_+M$) shows.
-- source:
--   He & Goh, Profit or Growth? Dynamic Order Allocation in a Hybrid Workforce, SSRN 3537700 (preprint, 2020-12-25), pp. 20–21, §4.3, problem (9) and the static policy ystatic

import Mathlib
import Definitions.Def_HybridOrderAlloc_Thickness_Model

namespace HybridOrderAlloc.Thickness.Supplement

/-- The static policy of §4.3, p. 21: `y^static(M, D) := (µ₀ − µ)₊ M ∧ D`, i.e.
`min ((µ₀ − µ)₊ · M) D`, the stated optimal solution of the single-period problem (9), p. 20. -/
noncomputable def yStatic {Ω : Type*} [MeasurableSpace Ω] (S : Sys Ω) (M D : ℝ) : ℝ :=
  min (max (S.mu0 - S.mu) 0 * M) D

end HybridOrderAlloc.Thickness.Supplement


