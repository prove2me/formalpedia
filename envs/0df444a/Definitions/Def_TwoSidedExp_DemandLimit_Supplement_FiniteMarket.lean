-- Prove2me | Definitions.Def_TwoSidedExp_DemandLimit_Supplement_FiniteMarket
-- name    : TwoSidedExp_DemandLimit_Supplement_FiniteMarket
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:18:27.690506+00:00
-- url     : https://prove2.me/theorems/1a620c92-ac56-4bd8-85db-bba026ee12a8
-- title:
--   Finite-market primitives, independent binomial choice and generator (3)–(5)
-- statement:
--   For N listings let m^(N)(θ) be nonnegative integer counts summing to N, let λ_γ^(N) > 0 be customer arrival rates, and let ϵ_γ^(N) > 0 be outside options. A state σ assigns to each type a count in {0,…,m^(N)(θ)}. The consideration counts D_γ(θ|σ) are independent binomials with σ(θ) trials and success probability α_γ(θ). Define
--
--   $$r_\gamma^{(N)}(\theta\mid\sigma)=\mathbb E\frac{D_\gamma(\theta\mid\sigma)v_\gamma(\theta)}{\epsilon_\gamma^{(N)}+\sum_{\theta'}D_\gamma(\theta'\mid\sigma)v_\gamma(\theta')},$$
--   $$R(\sigma,\sigma+e_\theta)=(m^{(N)}(\theta)-\sigma(\theta))\tau\nu(\theta),\qquad R(\sigma,\sigma-e_\theta)=\sum_\gamma\lambda_\gamma^{(N)}r_\gamma^{(N)}(\theta\mid\sigma).$$
--
--   Only feasible moves occur; the down move requires σ(θ) > 0. The diagonal generator entry is minus the total outgoing rate. The expectation is a finite sum against the product of Mathlib binomial probability masses. It is the finite-system choice law, rather than the mean-field probability.
--
--   **Formalization Note** State coordinates use Fin(m^(N)(θ)+1). Zero is an irrelevant extension of the size index used to write sequences on ℕ. The generic CTMC law is imported from MissionAbort_HasRateChainLaw and is not redefined here.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, pp. 7–10, §3, (3)–(5)

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit.Supplement

variable (Γ Θ : Type) [Fintype Θ]

/-- The N-listing primitives from §3. Zero is an unused extension for sequence indexing. -/
structure FiniteMarket (N : ℕ) where
  m : Θ → ℕ
  listing_sum : ∑ θ, m θ = N
  arrival : Γ → ℝ
  outside : Γ → ℝ
  arrival_pos : ∀ γ, 0 < arrival γ
  outside_pos : ∀ γ, 0 < outside γ

variable {Γ Θ} [Fintype Γ]

/-- S^(N), p. 9: counts of available listings, not continuous masses. -/
abbrev MarketState {N : ℕ} (F : FiniteMarket Γ Θ N) := (θ : Θ) → Fin (F.m θ + 1)

/-- (4), p. 10. The product of Mathlib binomial masses is the law of the independent
consideration counts. Its finite sum is the expectation in (4). -/
noncomputable def finiteChoice (M : Model Γ Θ) (hM : M.Standing) {N : ℕ}
    (F : FiniteMarket Γ Θ N) (γ : Γ) (θ : Θ) (σ : MarketState F) : ℝ := by
  classical
  exact ∑ d : ((θ' : Θ) → Fin ((σ θ' : ℕ) + 1)),
    (∏ θ', (ProbabilityTheory.binomial (σ θ')
      ⟨M.sys.α γ θ', ⟨(hM.alpha_pos γ θ').le, hM.alpha_le_one γ θ'⟩⟩).real {(d θ' : ℕ)}) *
      ((d θ : ℕ) * M.sys.v γ θ /
        (F.outside γ + ∑ θ', (d θ' : ℕ) * M.sys.v γ θ'))

/-- The off-diagonal rates (3),(5), with zero forbidden moves. -/
noncomputable def offRate (M : Model Γ Θ) (hM : M.Standing) {N : ℕ}
    (F : FiniteMarket Γ Θ N) (tau : ℝ) (σ η : MarketState F) : ℝ := by
  classical
  exact ∑ θ,
    if (∀ θ', θ' ≠ θ → η θ' = σ θ') ∧ (η θ : ℕ) = (σ θ : ℕ) + 1 then
      ((F.m θ : ℝ) - (σ θ : ℕ)) * (tau * M.sys.ν θ)
    else if (∀ θ', θ' ≠ θ → η θ' = σ θ') ∧ (σ θ : ℕ) = (η θ : ℕ) + 1 then
      ∑ γ, F.arrival γ * finiteChoice M hM F γ θ σ
    else 0

/-- Conservative generator: the diagonal is minus the total rate of leaving a state. -/
noncomputable def generator (M : Model Γ Θ) (hM : M.Standing) {N : ℕ}
    (F : FiniteMarket Γ Θ N) (tau : ℝ) : Matrix (MarketState F) (MarketState F) ℝ := by
  classical
  exact fun σ η => if σ = η then -(∑ ζ, if ζ = σ then 0 else offRate M hM F tau σ ζ)
    else offRate M hM F tau σ η

end TwoSidedExp.DemandLimit.Supplement


