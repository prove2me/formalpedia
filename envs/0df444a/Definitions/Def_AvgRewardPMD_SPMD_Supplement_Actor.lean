-- Prove2me | Definitions.Def_AvgRewardPMD_SPMD_Supplement_Actor
-- name    : AvgRewardPMD_SPMD_Supplement_Actor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:24:06.049291+00:00
-- url     : https://prove2.me/theorems/f8482fbf-c3b4-4c1e-9b43-7bc89b0828d3
-- title:
--   Assumption 2 (p. 7), the constant Γ of §3.4 (p. 12), π_0 of Algorithm 1 and the variance condition (3.8) of Assumption 3 (p. 8)
-- statement:
--   Objects added to the published vocabulary of the mission (`AvgRewardPMD.SPMD.Setting`) for the strongly convex regularized SPMD results of §3.4 (Li, Wu and Lan, pp. 7–14).
--
--   1. **Ergodicity (Assumption 2, p. 7).** For every feasible (randomized stationary) policy $\pi$, the Markov chain on $\mathcal S$ with transition matrix $P_\pi(s,s')=\sum_a\pi(a\mid s)\mathsf P(s'\mid s,a)$ is irreducible and aperiodic.
--   2. **The constant $\Gamma$ (§3.4, p. 12).** A number $\Gamma\in(0,1)$ is admissible when every stationary distribution $\nu^\pi$ of every feasible policy satisfies
--   $$\min_{s\in\mathcal S}\nu^\pi(s)\ge 1-\Gamma .$$
--   3. **The initial policy** $\pi_0(a\mid s)=1/|\mathcal A|$ of Algorithm 1 (p. 8).
--   4. **Variance condition (3.8) of Assumption 3 (p. 8).** For the first $n$ critic outputs $\bar{\mathcal Q}^{\pi_k,\zeta_k}$, $k<n$, with $\delta_k=\bar{\mathcal Q}^{\pi_k,\zeta_k}-\bar Q^{\pi_k}$,
--   $$\mathbb E_{\zeta_k}\big[\|\delta_k\|_{\mathrm{sp}}^2\big]\le\sigma^2,\qquad \sigma\ge0 .$$
--
--   Assumption 2 is the ergodicity hypothesis of the Markovian noise model and of Theorem 3; $\Gamma$ quantifies how much mass every stationary law puts on each state; (3.8) separates the variance $\sigma^2$ of the critic from its bias $\varsigma$ (3.7) and its second moment $\kappa^2$ (3.9), which the published `CriticAssumption` already encodes.
--
--   **Formalization Note** Irreducibility and aperiodicity are the published `MarkovMixing.Irreducible` and `MarkovMixing.Aperiodic` of $P_\pi$. (3.8) is stated with the conventions of the published `CriticAssumption`: on a probability space with a filtration `ℱ`, `ℱ k` playing $\mathcal F_{k-1}$, the squared span of $\delta_k$ is integrable and its conditional expectation given `ℱ k` is at most $\sigma^2$ almost surely.
-- source:
--   Li, Wu, Lan, Stochastic first-order methods for average-reward Markov decision processes, arXiv:2205.05800v6, p. 7 Assumption 2; p. 8 Algorithm 1 (input) and Assumption 3 (3.8); p. 9 (F_s, δ_k); p. 12 (Γ)

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting

namespace AvgRewardPMD.SPMD.Supplement

open FoundationsML.ReinforcementLearning MeasureTheory

noncomputable section

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- Assumption 2 (Li–Wu–Lan, arXiv:2205.05800v6, p. 7): for every feasible (randomized stationary)
policy `π`, the Markov chain on `S` with transition matrix `P_π` is irreducible and aperiodic. -/
def IsErgodic (P : S → A → S → ℝ) : Prop :=
  ∀ π : S → A → ℝ, IsPolicy π →
    MarkovMixing.Irreducible (stateMatrix P π) ∧ MarkovMixing.Aperiodic (stateMatrix P π)

/-- The constant `Γ` of §3.4 (p. 12): `Γ ∈ (0,1)` and every stationary distribution `ν^π` of every
feasible policy `π` satisfies `min_s ν^π(s) ≥ 1 − Γ`. -/
def IsGammaBound (P : S → A → S → ℝ) (Γ : ℝ) : Prop :=
  0 < Γ ∧ Γ < 1 ∧
    ∀ π : S → A → ℝ, IsPolicy π → ∀ ν : S → ℝ, MarkovMixing.IsStationary (stateMatrix P π) ν →
      ∀ s, 1 - Γ ≤ ν s

/-- The initial policy `π_0(a|s) = 1/|A|` of Algorithm 1 (p. 8). -/
def uniformPolicy : S → A → ℝ := fun _ _ => 1 / (Fintype.card A : ℝ)

/-- Condition (3.8) of Assumption 3 (p. 8) for the first `n` critic outputs:
`E_{ζ_k}[‖Q̂_k − Q̄^{π_k}‖²_sp] ≤ σ²`, with `ℱ k` the paper's `F_{k−1}` (as in the published
`CriticAssumption`) and `‖Q̂_k − Q̄^{π_k}‖²_sp` integrable. `Qbar π'` is the exact basic
differential Q-function of `π'`. -/
def CriticVariance {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) (ℱ : Filtration ℕ m)
    (Qbar : (S → A → ℝ) → S × A → ℝ) (Qhat : ℕ → Ω → S × A → ℝ) (π : ℕ → Ω → S → A → ℝ)
    (σ : ℝ) (n : ℕ) : Prop :=
  0 ≤ σ ∧ ∀ k < n,
    Integrable (fun ξ => span (fun x => Qhat k ξ x - Qbar (π k ξ) x) ^ 2) μ ∧
    ∀ᵐ ξ ∂μ, μ[fun ξ' => span (fun x => Qhat k ξ' x - Qbar (π k ξ') x) ^ 2 | ℱ k] ξ ≤ σ ^ 2

end

end AvgRewardPMD.SPMD.Supplement


