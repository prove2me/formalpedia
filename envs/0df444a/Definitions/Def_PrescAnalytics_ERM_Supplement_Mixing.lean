-- Prove2me | Definitions.Def_PrescAnalytics_ERM_Supplement_Mixing
-- name    : PrescAnalytics_ERM_Supplement_Mixing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:52:54.318117+00:00
-- url     : https://prove2.me/theorems/b2f71307-5ae3-4b5c-83b6-197ca7cf3867
-- title:
--   The beta coefficient and the exact sampling alternatives
-- statement:
--   Stationarity and the $\alpha$ and $\rho$ coefficients are imported from the published MixingCoefficients interface. Only the missing $\beta$ coefficient is newly defined:
--   $$\beta(k)=\sup_t\operatorname{TV}\!\left(\mathcal L(S_{0:t},S_{t+k:\infty}),\mathcal L(S_{0:t})\otimes\mathcal L(S_{t+k:\infty})\right).$$
--   Here $\operatorname{TV}(\mu,\nu)=\sup_A|\mu(A)-\nu(A)|$, with measurable test sets. The file also packages the exact three kernel regimes, summable-$\rho$ recursive regime and two local-linear regimes; polynomial rates mean an eventual bound with an existential finite constant. All bandwidth thresholds remain strict. No mixing rate is bundled into the general process definition.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, pp. 42–44, Definitions 4–5, Theorems 16–19

import Mathlib
import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace PrescAnalytics.ERM.Supplement

/-- Total-variation distance sup_A |μ(A)-ν(A)| for finite measures.
For the probability laws below, this is half the signed-measure variation norm. -/
noncomputable def totalVariationDistance {E : Type*} [MeasurableSpace E]
    (μ ν : Measure E) : ℝ :=
  sSup {r | ∃ A : Set E, MeasurableSet A ∧ r = |(μ A).toReal - (ν A).toReal|}

/-- Past and future joint law versus their product, Definition 5, p. 42.
The finite past is encoded on Fin(t+1), the future on ℕ, both with product σ-algebras. -/
noncomputable def betaMixingCoef {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (S : ℕ → Ω → E) (k : ℕ) : ℝ :=
  ⨆ t : ℕ,
    totalVariationDistance
      (P.map (fun ω => ((fun i : Fin (t+1) => S i.val ω), (fun n : ℕ => S (t+k+n) ω))))
      ((P.map (fun ω => (fun i : Fin (t+1) => S i.val ω))).prod
        (P.map (fun ω => (fun n : ℕ => S (t+k+n) ω))))

/-- Polynomial O(k^(-γ)): a finite constant and an eventual bound, not a chosen rate. -/
def PolynomialMixingRate (a : ℕ → ℝ) (γ : ℝ) : Prop :=
  ∃ M : ℝ, 0 < M ∧ ∀ᶠ k in atTop, |a k| ≤ M * (k : ℝ) ^ (-γ)

/-- All three sampling alternatives in Theorem 16, with strict exponent thresholds. -/
def KernelRegime {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (S : ℕ → Ω → E) (dx : ℕ) (δ : ℝ) : Prop :=
  (iIndepFun S P ∧ δ < 1 / (dx : ℝ)) ∨
  (MarkovChainCLT.IsStrictlyStationary P S ∧
    ∃ γ : ℝ, 0 < γ ∧ PolynomialMixingRate (MarkovChainCLT.rhoMixingCoef P S) γ ∧
      δ < 2 * γ / ((dx : ℝ) + 2 * dx * γ)) ∨
  (MarkovChainCLT.IsStrictlyStationary P S ∧
    ∃ γ : ℝ, 1 < γ ∧ PolynomialMixingRate (MarkovChainCLT.alphaMixingCoef P S) γ ∧
      δ < 2 * (γ - 1) / (3 * (dx : ℝ) + 2 * dx * γ))

/-- Summability starts at lag 1. No polynomial rate is imposed in Theorem 17. -/
def RecursiveRegime {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (S : ℕ → Ω → E) : Prop :=
  iIndepFun S P ∨
    (MarkovChainCLT.IsStrictlyStationary P S ∧
      Summable (fun k : ℕ => MarkovChainCLT.rhoMixingCoef P S (k+1)))

/-- Both regimes and the full threshold of Theorems 18 and 19. -/
def LocalRegime {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (S : ℕ → Ω → E) (dx : ℕ) (δ : ℝ) : Prop :=
  (iIndepFun S P ∧ δ < 1 / (dx : ℝ)) ∨
  (MarkovChainCLT.IsStrictlyStationary P S ∧
    ∃ γ : ℝ, (dx : ℝ) + 3 < γ ∧
      PolynomialMixingRate (MarkovChainCLT.alphaMixingCoef P S) γ ∧
      δ < (γ - dx - 3) / ((dx : ℝ) * (γ - dx + 3)))

end PrescAnalytics.ERM.Supplement


