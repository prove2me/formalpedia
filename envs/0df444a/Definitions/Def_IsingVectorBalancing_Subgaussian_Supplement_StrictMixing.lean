-- Prove2me | Definitions.Def_IsingVectorBalancing_Subgaussian_Supplement_StrictMixing
-- name    : IsingVectorBalancing_Subgaussian_Supplement_StrictMixing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:15:27.807597+00:00
-- url     : https://prove2.me/theorems/3c748aef-e18b-4480-b42c-75886ba2caa3
-- title:
--   Strict worst-start total-variation mixing time
-- statement:
--   For a finite transition matrix $P$ and a mass function $\mu$, use the actual matrix power $P^t$. For each feasible initial state $\sigma$, its first successful time at tolerance $\varepsilon$ is
--
--   $$\inf\{t\in\mathbb N:\tfrac12\sum_\tau|P^t(\sigma,\tau)-\mu(\tau)|<\varepsilon\}.$$
--
--   The worst-start mixing time is the maximum of these times over $\mu(\sigma)>0$. The value is $+\infty$ if a feasible start never succeeds. Thus an upper bound by a finite natural number also asserts convergence. This preserves the source's strict inequality. The reusable finite kernel itself is the published random-scan heat-bath kernel.
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), p. 3 (PDF 4), Section 2, mixing-time definition

import Mathlib
import Definitions.Def_mm_mcmc

open scoped BigOperators
set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian.Supplement

/-- The source's strict total-variation threshold, with actual matrix powers.
Failed convergence gives infinity, not the natural-number empty-infimum default. -/
noncomputable def firstMixingTime {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (μ : S → ℝ) (ε : ℝ) (σ : S) : ℕ∞ :=
  sInf ((fun t : ℕ => (t : ℕ∞)) ''
    {t : ℕ | (1 / 2 : ℝ) * ∑ τ : S, |(P ^ t) σ τ - μ τ| < ε})

/-- Maximum over feasible starts of their first successful time (p.3/PDF4). -/
noncomputable def worstMixingTime {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (μ : S → ℝ) (ε : ℝ) : ℕ∞ :=
  ⨆ σ : {σ : S // 0 < μ σ}, firstMixingTime P μ ε σ.val

end IsingVectorBalancing.Subgaussian.Supplement


