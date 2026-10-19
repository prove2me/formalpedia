-- Prove2me | Definitions.Def_OnlineNRM_TSFixed_EntropyExperiment
-- name    : OnlineNRM_TSFixed_EntropyExperiment
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-17T18:22:31.697421+00:00
-- url     : https://prove2.me/theorems/be751e70-4dc5-49d7-a292-31e164d380f1
-- title:
--   Bounded finite oracle experiments, diagonal covariances, and one-period reward functions
-- statement:
--   Defines the history-centered oracle covariance and an abstract finite experiment with explicit ambient sigma-algebra inclusions, simplex weights, bounded rewards, posterior-matched action probabilities, and conditional reward means. It also defines mean and observed full-demand rewards using the existing demand and price definitions.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Definitions.Def_OnlineNRM_TSFixed_Run
import Definitions.Def_OnlineNRM_TSFixed_OracleEntropy

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- A diagonal covariance of an oracle weight and a latent mean reward,
centered with respect to the observed history. -/
noncomputable def ProbabilityTheory.weightedOracleCovariance
    {Ω α : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : MeasurableSpace Ω)
    (w r : Ω → α → ℝ) (a : α) : ℝ :=
  ∫ ω, (w ω a - (P[fun ω' => w ω' a | H]) ω) * r ω a ∂P

/-- A bounded finite-action experiment. `H` is the old observed history,
`L` also contains the latent oracle weights and mean rewards, and `G` is
 the new observed history. The action law given `L` is the posterior mean
of the oracle weights given `H`. Only a conditional reward mean is needed. -/
structure ProbabilityTheory.IsFiniteOracleExperiment
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : Measure Ω) (H L G : MeasurableSpace Ω)
    (w r : Ω → α → ℝ) (B : Ω → α) (Y : Ω → ℝ) (R : ℝ) : Prop where
  history_le_latent : H ≤ L
  latent_le_ambient : L ≤ mΩ
  history_le_observed : H ≤ G
  observed_le_ambient : G ≤ mΩ
  measurable_weights : @Measurable Ω (α → ℝ) L inferInstance w
  measurable_means : @Measurable Ω (α → ℝ) L inferInstance r
  measurable_action : @Measurable Ω α G inferInstance B
  measurable_reward : @Measurable Ω ℝ G inferInstance Y
  weights_nonneg : ∀ ω a, 0 ≤ w ω a
  weights_sum : ∀ ω, ∑ a : α, w ω a = 1
  scale_nonneg : 0 ≤ R
  means_bounded : ∀ᵐ ω ∂P, ∀ a, r ω a ∈ Set.Icc 0 R
  reward_bounded : ∀ᵐ ω ∂P, Y ω ∈ Set.Icc 0 R
  action_law : ∀ a : α,
    P[(B ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) | L] =ᵐ[P]
      P[fun ω => w ω a | H]
  reward_mean :
    P[Y | L ⊔ MeasurableSpace.comap B inferInstance] =ᵐ[P]
      fun ω => r ω (B ω)

/-- Mean full-demand revenue at one price, including the shut-off action. -/
noncomputable def OnlineNRM.TSFixed.oracleMeanReward
    {N K : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (p : Fin N → Fin K → ℝ)
    (F : Kernel (Θ × Fin K) (Fin N → ℝ)) (ρ : Θ) : Option (Fin K) → ℝ
  | none => 0
  | some k => ∑ i : Fin N, p i k * OnlineNRM.TSFixed.meanDemand F ρ i k

/-- Observed full-demand revenue in one experiment. -/
def OnlineNRM.TSFixed.observedPriceReward
    {N K : ℕ} {Ω : Type*} (p : Fin N → Fin K → ℝ)
    (B : Ω → Option (Fin K)) (Z : Ω → Fin N → ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin N, OnlineNRM.TSFixed.postedPrice p (B ω) i * Z ω i


