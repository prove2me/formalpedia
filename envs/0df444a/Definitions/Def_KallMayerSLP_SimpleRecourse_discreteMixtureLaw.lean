-- Prove2me | Definitions.Def_KallMayerSLP_SimpleRecourse_discreteMixtureLaw
-- name    : KallMayerSLP_SimpleRecourse_discreteMixtureLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:12:29.642183+00:00
-- url     : https://prove2.me/theorems/7e8c8960-55d2-405b-a083-1e10c4897584
-- title:
--   The finite discrete distribution (2.65)
-- statement:
--   Let $\tilde\xi$ take the values $\xi_\nu$ with probabilities $p_\nu$, $\nu=1,\dots,N$, and let $W=\sum_{k=0}^{K-1}(\alpha_k+\beta_k)$. The distribution (2.65) has the realizations and probabilities
--
--   1. $\xi_\nu$ with $\pi_{\nu0}=(\alpha_0+\beta_0)p_\nu/W$;
--   2. $\xi_\nu-u_\kappa$ with $\pi^-_{\nu\kappa}=\alpha_\kappa p_\nu/W$, $\kappa=1,\dots,K-1$;
--   3. $\xi_\nu+l_\kappa$ with $\pi^+_{\nu\kappa}=\beta_\kappa p_\nu/W$, $\kappa=1,\dots,K-1$.
--
--   That is the measure $\sum_\nu\bigl[\pi_{\nu0}\delta_{\xi_\nu}+\sum_{\kappa\ge1}(\pi^-_{\nu\kappa}\delta_{\xi_\nu-u_\kappa}+\pi^+_{\nu\kappa}\delta_{\xi_\nu+l_\kappa})\bigr]$. For a finite discrete $\tilde\xi$, Theorem 2.8 reduces multiple simple recourse to simple recourse with this finite discrete distribution.
--
--   **Formalization Note** The book writes $\gamma$ for $W$ in (2.65), not the $\gamma$ of Definition 2.4; here $W$ is written out. Index base $0$. Weights enter through `ENNReal.ofReal`; under Definition 2.4 and $p_\nu>0$ they are nonnegative, so nothing is truncated. Coinciding realizations add their weights.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, (2.65), p.243 (PDF 252)

import Mathlib

open MeasureTheory

namespace KallMayerSLP.SimpleRecourse

/-- **The finite discrete distribution (2.65).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, (2.65), p.243 (PDF 252): for a
finite discrete `ξ̃` with realizations `ξ_ν` and probabilities `p_ν` (2.64), the realizations and
probabilities
`ξ_ν`, `π_{ν0} = (α₀ + β₀)p_ν/γ` (`κ = 0`);
`ξ_ν − u_κ`, `π⁻_{νκ} = α_κ p_ν/γ`; `ξ_ν + l_κ`, `π⁺_{νκ} = β_κ p_ν/γ` (`κ = 1, …, K − 1`),
with `γ = Σ_{k=0}^{K−1} (α_k + β_k)`; the measure `Σ_ν [π_{ν0} δ_{ξ_ν} + Σ_{κ≥1} (π⁻_{νκ} δ_{ξ_ν − u_κ} + π⁺_{νκ} δ_{ξ_ν + l_κ})]`.

**Formalization Note.** Index base `0` (`Fin N`, `Fin K`). The book's `γ` here is the total weight
`W = Σ_k (α_k + β_k)` (not the `γ` of Definition 2.4) and is written out. Weights enter through
`ENNReal.ofReal`; under Definition 2.4 (`IsMSRTData`) and `p_ν > 0` they are all nonnegative, so
nothing is truncated. Coinciding realizations add their weights. -/
noncomputable def discreteMixtureLaw {K N : ℕ} (α β u l : Fin K → ℝ) (p ξs : Fin N → ℝ) :
    Measure ℝ :=
  ∑ i, ∑ k : Fin K,
    (if k.val = 0 then
      ENNReal.ofReal ((α k + β k) * p i / ∑ j, (α j + β j)) • Measure.dirac (ξs i)
    else
      ENNReal.ofReal (α k * p i / ∑ j, (α j + β j)) • Measure.dirac (ξs i - u k) +
        ENNReal.ofReal (β k * p i / ∑ j, (α j + β j)) • Measure.dirac (ξs i + l k))

end KallMayerSLP.SimpleRecourse


