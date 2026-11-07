-- Prove2me | Definitions.Def_MixScale_Estimator
-- name    : MixScale_Estimator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:10:38.738053+00:00
-- url     : https://prove2.me/theorems/619e9c31-4691-47e3-a587-6ac04cd8e66a
-- title:
--   Chi-square divergence, randomized estimators and two-point hard pairs
-- statement:
--   The chi-square divergence is $\chi^2(P\|Q)=\int(dP/dQ-1)^2\,dQ$ if $P\ll Q$ and $+\infty$ otherwise; on densities this is $\int(p_+-p_-)^2/p_-$.
--
--   A **randomized estimator** from $N$ samples is a function of the $N$ samples and an independent seed, the seed having an arbitrary probability law. It succeeds with probability at least $p$ under $\Theta$ if some measurable set of (sample, seed) pairs of probability at least $p$ lies in $\{D_{\mathrm{par}}(\mathrm{est},\Theta)\le\varepsilon\}$.
--
--   A **hard pair** for a weight class, with bounds $B,\kappa,w_\star,\gamma$, accuracy $\varepsilon$ and sample threshold $b$, consists of two one-dimensional $k_0$-tuples satisfying (2) with the same list of centers (and, for equal weights, all weights $1/k_0$ and the same multiset of scales), such that every randomized estimator succeeding with probability at least $2/3$ under both uses at least $b$ samples.
--
--   The hard pair expresses the paper's statement that the lower bound holds on a subclass "even when the component centers are supplied".
--
--   **Formalization Note** No measurability of the estimator is required; for a measurable estimator the success condition is the ordinary probability. The supplied centers and scale multisets are the same for both tuples, so they are constant side information on which the estimator may depend.
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), §3, p.10; Lemma H.4, p.51 (PDF p.53); Theorem 1.1, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_MixScale_Profile
import Definitions.Def_MixScale_Model

open MeasureTheory

namespace MixScale

/-!
# Chi-square divergence, randomized estimators, and two-point hard pairs

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*,
STOC 2027 submission manuscript (sha256 5277f95e…7c6c). §3, p.10 (PDF p.12): "small `χ²`
divergence therefore yields a sample lower bound"; Lemma H.4, p.51 (PDF p.53): "Any possibly
randomized estimator that has parameter error at most `ε` with probability at least `2/3` under both
tuples"; Theorem 1.1, p.3 (PDF p.5): "there exists a fixed-size one-dimensional subclass with fixed
valid condition bounds on which every estimator succeeding with probability at least `2/3` requires
`N ≥ c ℓ_q(γ)γ^{−E_W}ε^{−2}` […] These lower bounds hold even when the component centers are
supplied. Under equal weights, the multiset of component scales may also be supplied".

**Formalization Note.**
* `chiSq P Q = ∫ (dP/dQ − 1)² dQ` if `P ≪ Q`, and `∞` otherwise; on densities this is the paper's
  `∫ (p₊ − p₋)²/p₋`.
* `iidLaw N μ` is the law of `N` i.i.d. draws (`Measure.pi`), the zero measure if `μ` is not a
  probability measure.
* A randomized estimator from `N` samples is any function `est : (Fin N → ℝ^d) × S → Params d k`,
  where the seed space `S` (a `Type`) carries an arbitrary probability measure `μS` independent of
  the samples. It succeeds with probability at least `p` under `Θ` if some measurable set of
  (sample, seed) pairs of probability at least `p` lies inside `{D_par(est, Θ) ≤ ε}`. No
  measurability of `est` is required; for a measurable `est` this is the ordinary probability.
* `HardPair χ W k₀ B κ w★ γ ε bound`: two one-dimensional `k₀`-tuples satisfying (2) with these
  bounds and with the same center list (index by index); for `W = eq` both have weights `1/k₀` and
  the same scale multiset. Every estimator that succeeds with probability at least `2/3` under both
  (for any component laws) uses at least `bound` samples. Supplied centers and scale multisets are
  the same for both tuples, so they are constant side information the estimator may depend on.
-/

/-- The chi-square divergence `χ²(P‖Q)`. -/
noncomputable def chiSq {α : Type*} [MeasurableSpace α] (P Q : Measure α) : ENNReal := by
  classical
  exact if P ≪ Q then ∫⁻ x, ENNReal.ofReal (((P.rnDeriv Q x).toReal - 1) ^ 2) ∂Q else ⊤

open Classical in
/-- The law of `N` i.i.d. draws from `μ` (zero if `μ` is not a probability measure). -/
noncomputable def iidLaw {α : Type*} [MeasurableSpace α] (N : ℕ) (μ : Measure α) :
    Measure (Fin N → α) :=
  if h : IsProbabilityMeasure μ then
    haveI := h
    Measure.pi (fun _ : Fin N => μ)
  else 0

/-- The randomized estimator `est` (seed law `μS`), fed samples with law `law`, has
`D_par(est, Θ) ≤ ε` with probability at least `p`. -/
def EstSucceeds {d k N : ℕ} {Sd : Type} [MeasurableSpace Sd] (μS : Measure Sd)
    (est : (Fin N → Vec d) × Sd → Params d k) (law : Measure (Fin N → Vec d))
    (Θ : Params d k) (ε : ℝ) (p : ENNReal) : Prop :=
  ∃ E : Set ((Fin N → Vec d) × Sd), MeasurableSet E ∧
    E ⊆ {x | Dpar (est x) Θ ≤ ε} ∧ p ≤ (law.prod μS) E

/-- A two-point hard pair for weight class `W`: one-dimensional `k₀`-tuples satisfying (2) with
`B, κ, w★, γ`, with equal center lists (and, for `W = eq`, weights `1/k₀` and equal scale
multisets), such that every randomized estimator succeeding with probability at least `2/3` under
both uses at least `bound` samples. -/
def HardPair (χ : ℝ → ℝ) (W : WeightClass) (k₀ : ℕ) (B κ wstar γ ε bound : ℝ) : Prop :=
  ∃ Θp Θm : Params 1 k₀, Valid B κ wstar γ Θp ∧ Valid B κ wstar γ Θm ∧
    (∀ j, center Θp j = center Θm j) ∧
    (W = .eq → EqualWeights Θp ∧ EqualWeights Θm ∧
      ∃ σ : Equiv.Perm (Fin k₀), ∀ j, scale Θm j = scale Θp (σ j)) ∧
    ∀ (Pp Pm : Fin k₀ → Measure (Vec 1)), IsCompFamily χ Θp Pp → IsCompFamily χ Θm Pm →
    ∀ (N : ℕ) (Sd : Type) [MeasurableSpace Sd] (μS : Measure Sd) [IsProbabilityMeasure μS]
      (est : (Fin N → Vec 1) × Sd → Params 1 k₀),
      EstSucceeds μS est (iidLaw N (mixLaw Θp Pp)) Θp ε (2 / 3) →
      EstSucceeds μS est (iidLaw N (mixLaw Θm Pm)) Θm ε (2 / 3) →
      bound ≤ (N : ℝ)

end MixScale


