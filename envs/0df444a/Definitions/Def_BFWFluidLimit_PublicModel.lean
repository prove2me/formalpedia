-- Prove2me | Definitions.Def_BFWFluidLimit_PublicModel
-- name    : BFWFluidLimit_PublicModel
-- status  : Definition
-- author  : @wfe2017
-- created : 2026-11-20T11:14:16.743827+00:00
-- url     : https://prove2.me/theorems/1a3f3724-1c36-4d1e-8431-c05169f85d7a
-- title:
--   Corrected finite-run pricing model and full Theorem 3.1 target
-- statement:
--   Fresh definitions from the public paper, including arbitrary fixed N, the exact clipped OLS policy and mean-field target, IID independent exploration prices, the original conditional second-moment bound, explicitly added conditional independence of shocks and current exploration prices, and a zero-variance OLS completion. CorrectedTheorem31 is a proposition describing the desired ODE existence, uniqueness, and stochastic terminal convergence; defining it does not prove it.
-- source:
--   https://arxiv.org/pdf/2605.16064, Section 2 pp.7–9, Definition3.1 and Theorem3.1 pp.10–11, AppendicesE–F pp.37–61. Explicit authorized corrections: current-price/noise conditional independence; zero-variance fallback.

import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
Fresh public-paper model for the CORRECTED BFW Theorem 3.1.
This file defines the target; it does not prove the fluid limit.
No private pricing development is imported.
-/
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace BFWFluidLimit.Model

abbrev Prices (N : ℕ) := Fin N → ℝ
abbrev PriceMatrix (N : ℕ) := Fin N → Fin N → ℝ
abbrev MomentState (N : ℕ) := Prices N × Prices N × PriceMatrix N × Prices N

structure Data (N : ℕ) where
  a : ℝ
  b : ℝ
  c : ℝ
  pmin : ℝ
  pmax : ℝ

def ValidData {N : ℕ} (d : Data N) : Prop :=
  2 ≤ N ∧ 0 < d.a ∧ 0 < d.c ∧ d.c < d.b ∧
  0 < d.pmin ∧ d.pmin < d.pmax ∧
  d.pmin ≤ d.a / (2 * d.b - d.c) ∧
  d.a / (2 * d.b - d.c) < d.pmax ∧ d.pmax ≤ d.a / d.b

noncomputable def otherMean {N : ℕ} (p : Prices N) (i : Fin N) : ℝ :=
  (∑ j ∈ Finset.univ.erase i, p j) / ((N : ℝ) - 1)

noncomputable def demand {N : ℕ} (d : Data N) (p : Prices N) : Prices N :=
  fun i => d.a - d.b * p i + d.c * otherMean p i

noncomputable def clip {N : ℕ} (d : Data N) (p : ℝ) : ℝ :=
  max d.pmin (min d.pmax p)

noncomputable def observation {N : ℕ} (p q : Prices N) : MomentState N :=
  (p, q, (fun i j => p i * p j), fun i => p i * q i)

noncomputable def empirical {N : ℕ} (P Q : ℕ → Prices N) (t : ℕ) : MomentState N :=
  (t : ℝ)⁻¹ • ∑ s ∈ Finset.Icc 1 t, observation (P s) (Q s)

noncomputable def variance {N : ℕ} (x : MomentState N) (i : Fin N) : ℝ :=
  x.2.2.1 i i - (x.1 i)^2

noncomputable def covariance {N : ℕ} (x : MomentState N) (i : Fin N) : ℝ :=
  x.2.2.2 i - x.1 i * x.2.1 i

/-- Total OLS policy. On zero-variance histories choose slope zero, intercept the
quantity average, and hence post the upper price bound. -/
noncomputable def policy {N : ℕ} (d : Data N) (x : MomentState N) : Prices N :=
  fun i => if 0 < variance x i ∧ covariance x i < 0 then
    clip d ((x.1 i * x.2.2.2 i - x.2.2.1 i i * x.2.1 i) /
      (2 * covariance x i))
  else d.pmax

noncomputable def meanObservation {N : ℕ} (d : Data N) (x : MomentState N) : MomentState N :=
  observation (policy d x) (demand d (policy d x))

noncomputable def drift {N : ℕ} (d : Data N) (x : MomentState N) : MomentState N :=
  meanObservation d x - x

noncomputable def explorationMean {N : ℕ} (ν : Measure (Prices N)) : Prices N :=
  fun i => ∫ p, p i ∂ν

noncomputable def explorationVariance {N : ℕ} (ν : Measure (Prices N)) (i : Fin N) : ℝ :=
  ∫ p, (p i - explorationMean ν i)^2 ∂ν

noncomputable def explorationCovariance {N : ℕ} (ν : Measure (Prices N)) : PriceMatrix N :=
  fun i j => if i = j then explorationVariance ν i else 0

/-- The exploration restrictions in Section 2.2. Independence is of prices,
not of full price-quantity observations. -/
def ExplorationLaw {N : ℕ} (d : Data N) (ν : Measure (Prices N)) : Prop :=
  (∀ᵐ p ∂ν, ∀ i, p i ∈ Set.Icc d.pmin d.pmax) ∧
  iIndepFun (fun i (p : Prices N) => p i) ν ∧
  (∀ i, 0 < explorationVariance ν i)

noncomputable def initialMoments {N : ℕ} (d : Data N) (ν : Measure (Prices N)) : MomentState N :=
  let u := explorationMean ν
  let sig := explorationCovariance ν
  (u, demand d u, (fun i j => u i * u j + sig i j),
    fun i => u i * demand d u i - d.b * sig i i + d.c * otherMean (sig i) i)

noncomputable def policyUV {N : ℕ} (d : Data N) (U : Prices N)
    (V : PriceMatrix N) : Prices N :=
  fun i => if -d.b * V i i + d.c * otherMean (V i) i < 0 then
    clip d (((d.a + d.c * otherMean U i) * V i i -
      d.c * U i * otherMean (V i) i) /
      (2 * (d.b * V i i - d.c * otherMean (V i) i)))
  else d.pmax

/-- Definition 3.1, including its initial data and the clipped pricing rule. -/
def IsPriceMomentsODE {N : ℕ} (d : Data N) (ν : Measure (Prices N))
    (U : ℝ → Prices N) (V : ℝ → PriceMatrix N) : Prop :=
  U 1 = explorationMean ν ∧ V 1 = explorationCovariance ν ∧
  ∀ τ ∈ Set.Ici (1 : ℝ),
    HasDerivWithinAt U (τ⁻¹ • (policyUV d (U τ) (V τ) - U τ)) (Set.Ici 1) τ ∧
    HasDerivWithinAt V
      (fun i j => (policyUV d (U τ) (V τ) i - U τ i) *
        (policyUV d (U τ) (V τ) j - U τ j)) (Set.Ici 1) τ

section Stochastic
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Information after current prices are posted, before the current demand shock. -/
abbrev currentPriceInfo {N : ℕ} (F : Filtration ℕ mΩ) (P : ℕ → Ω → Prices N)
    (t : ℕ) : MeasurableSpace Ω :=
  F t ⊔ MeasurableSpace.comap (P (t + 1)) inferInstance

/-- Added assumption, in the conditional-expectation characterization of
conditional independence. All integrable measurable functions of the entire
shock vector have the same conditional mean with and without current prices.
This imposes no independence of shocks across dates or firms. -/
def NoisePriceConditionalIndependence {N : ℕ} (μ : Measure Ω)
    (F : Filtration ℕ mΩ) (P E : ℕ → Ω → Prices N) (t : ℕ) : Prop :=
  ∀ φ : Prices N → ℝ, Measurable φ → Integrable (fun ω => φ (E (t + 1) ω)) μ →
    μ[fun ω => φ (E (t + 1) ω) | currentPriceInfo F P t] =ᵐ[μ]
      μ[fun ω => φ (E (t + 1) ω) | F t]

/-- A finite stochastic run; observation indices start at one. The second
moment bound is conditioned only on the past, as in the printed paper. -/
def IsRun {N : ℕ} (μ : Measure Ω) (F : Filtration ℕ mΩ) (d : Data N)
    (ν : Measure (Prices N)) (σ : ℝ) (K T : ℕ) (P E : ℕ → Ω → Prices N) : Prop :=
  1 ≤ K ∧ 1 ≤ T ∧ 0 ≤ σ ∧
  (∀ t ∈ Finset.Icc 1 (K + T),
    @Measurable Ω (Prices N) (F t) inferInstance (P t) ∧
    @Measurable Ω (Prices N) (F t) inferInstance (E t) ∧
    (∀ᵐ ω ∂μ, ∀ i, P t ω i ∈ Set.Icc d.pmin d.pmax ∧
      0 < demand d (P t ω) i + E t ω i)) ∧
  (∀ t < K + T, ∀ i,
    MemLp (fun ω => E (t + 1) ω i) 2 μ ∧
    μ[fun ω => E (t + 1) ω i | F t] =ᵐ[μ] 0 ∧
    (∀ᵐ ω ∂μ, μ[fun ω => (E (t + 1) ω i)^2 | F t] ω ≤ σ^2)) ∧
  (∀ t < K, NoisePriceConditionalIndependence μ F P E t) ∧
  iIndepFun (fun t : Fin K => P (t.val + 1)) μ ∧
  (∀ t < K, IdentDistrib (P (t + 1)) (id : Prices N → Prices N) μ ν) ∧
  (∀ t ∈ Finset.Icc K (K + T - 1), ∀ᵐ ω ∂μ,
    P (t + 1) ω = policy d
      (empirical (fun s => P s ω) (fun s => demand d (P s ω) + E s ω) t))

end Stochastic

/-- The full corrected target, recorded as a proposition rather than an unproved
Lean theorem. No fluid-limit proof is asserted by this definition. -/
def CorrectedTheorem31 {N : ℕ} (d : Data N) (ν : Measure (Prices N)) : Prop :=
  ∃ (U : ℝ → Prices N) (V : ℝ → PriceMatrix N), IsPriceMomentsODE d ν U V ∧
  (∀ U' V', IsPriceMomentsODE d ν U' V' →
    Set.EqOn U U' (Set.Ici 1) ∧ Set.EqOn V V' (Set.Ici 1)) ∧
  ∀ (Ω : Type*) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ),
    @IsProbabilityMeasure Ω mΩ μ →
  ∀ (F : ℕ → Filtration ℕ mΩ) (P E : ℕ → ℕ → Ω → Prices N)
      (K T : ℕ → ℕ) (σ τ : ℝ),
    (∀ m, IsRun μ (F m) d ν σ (K m) (T m) (P m) (E m)) →
    Tendsto K atTop atTop → Tendsto T atTop atTop → 1 ≤ τ →
    Tendsto (fun m => ((K m + T m : ℕ) : ℝ) / (K m : ℝ)) atTop (nhds τ) →
    TendstoInMeasure μ (fun m ω => P m (K m + T m) ω) atTop
      (fun _ => policyUV d (U τ) (V τ))

end BFWFluidLimit.Model


