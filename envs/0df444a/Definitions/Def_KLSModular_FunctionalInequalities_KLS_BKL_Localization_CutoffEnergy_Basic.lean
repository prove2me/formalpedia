-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Basic
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T19:36:49.517764+00:00
-- url     : https://prove2.me/theorems/ae36e8bc-b0be-4294-a7b1-adcba1129d2b
-- title:
--   Cutoff-weighted cumulant energy claim
-- statement:
--   `weightedEnergyIntegral μ hc P γ p d u T` is the real integral over $\omega$ and $s\in(0,T]$ of $\gamma(p_s(\omega))^2$ times the order-$d+1$ `cumulantEnergy` of the compact posterior at the parameter $p_s(\omega)$. `CutoffEnergyClaim K d` is a universal proposition: for every dimension, compactly supported isotropic log-concave probability measure, unit vector $u$, $\varepsilon>0$, and $T\ge0$, there is a cutoff radius threshold $R_0$ such that every larger radius and every admissible Brownian setup and cutoff Eldan process satisfy $E_{d+1}(0)+\frac12$ times the weighted integral is at most `envelope K (d+1) + ε`. The statement includes the filtration conditions for nonpositive times and completion of $P$-null sets in $\mathcal{F}_0$; it is a named claim rather than a proof of that claim.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
--   import FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic
--   import FunctionalInequalities.KLS.BKL.CumulantEnvelope
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def weightedEnergyIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : Param n → ℝ)
--       (p : ℝ → Ω → Param n) (d : ℕ) (u : EuclideanSpace ℝ (Fin n)) (T : ℝ) : ℝ :=
--     ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, γ (p s ω) ^ 2 *
--       cumulantEnergy (compactPosterior μ hc (p s ω).1 (p s ω).2 : Measure (EuclideanSpace ℝ (Fin n))) d u ∂volume ∂P
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Localization/Process/Basic`](https://prove2.me/theorems/e451f491-3413-45b6-83f9-6d32bb29f918), [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086), [`KLS/BKL/CumulantEnvelope`](https://prove2.me/theorems/dd70df63-9b7a-4c42-ab12-35ef642d8be7).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Basic.lean) · `FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Basic` · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), item E95. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Basic.lean#L21-L44 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Basic`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Basic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnvelope

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
namespace FunctionalInequalities
namespace KLS
namespace BKL
namespace Localization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
/-- The cutoff-weighted energy integral `∫₀ᵀ E[γ(p_s)² E_{d+1}(p_s)(u)] ds` (BKL (95)–(97) along the cutoff process). -/
def weightedEnergyIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : Param n → ℝ)
    (p : ℝ → Ω → Param n) (d : ℕ) (u : EuclideanSpace ℝ (Fin n)) (T : ℝ) : ℝ :=
  ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, γ (p s ω) ^ 2 *
    cumulantEnergy (compactPosterior μ hc (p s ω).1 (p s ω).2 : Measure (EuclideanSpace ℝ (Fin n))) d u ∂volume ∂P
/-- **BKL (95) in cutoff form** at order `m = d + 1 ≥ 2` with envelope `b_m = envelope K m`: for every compactly
supported isotropic log-concave prior, unit vector `u`, tolerance `ε > 0` and horizon `T`, for every large enough cutoff
radius `R` and every ball-cutoff Eldan process on any Brownian setup,
`E_m(0) + ½ ∫₀ᵀ E[γ_R² E_{m+1}(p_s)] ds ≤ b_m + ε`. -/
def CutoffEnergyClaim (K : ℝ) (d : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support),
    KLS.Isotropic μ → KLS.LogConcave μ → ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 →
    ∀ ε : ℝ, 0 < ε → ∀ T : ℝ, 0 ≤ T → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        (W : MultidimBrownianMotion P n) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
        (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ),
        (∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t) →
        (∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) →
        ∀ {p : ℝ → Ω → Param n}, IsEldanCutoff μ hc W ℱ hW (ballCutoff R) p →
          cumulantEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) d u +
              (1 / 2 : ℝ) * weightedEnergyIntegral μ hc P (ballCutoff R) p (d + 1) u T ≤
            envelope K (d + 1) + ε
end Localization
end BKL
end KLS
end FunctionalInequalities


