-- Prove2me | Definitions.Def_AppliedSDE_SarkkaSolin_ChapterCertification02to05
-- name    : AppliedSDE_SarkkaSolin_ChapterCertification02to05
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-13T18:03:30.546252+00:00
-- url     : https://prove2.me/theorems/41670582-782f-410a-8555-c4f7da9df126
-- title:
--   Certification propositions for 02to05
-- statement:
--   Named propositions for chapter certification: Chapters 2–5. Each declaration is a Prop-valued abbreviation of the exact published-goal candidate statement from the current textbook Draft. It is not a theorem, axiom, proof or verified result. All quantified mathematical hypotheses are preserved.
--
--   Representative mathematical obligation:
--
--   $$
--   \mathcal{P}_{02to05}
--   $$
-- source:
--   Original derived formal certification definitions from Simo Särkkä and Arno Solin (2019), Applied Stochastic Differential Equations, Chapters 2–5, printed pp. 10–68. https://doi.org/10.1017/9781108186735

import Definitions.Def_AppliedSDE_SarkkaSolin_OUKalmanInterfaces
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoFormula
import Mathlib
open MeasureTheory Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Ito
open scoped NNReal ENNReal Topology BigOperators
open LevyStochCalc
open MeasureTheory
open scoped BigOperators Topology
open scoped BigOperators
open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open Filter
open Matrix
open scoped BigOperators Matrix
set_option autoImplicit false
universe u

def private_sde_cert_ch02 : Prop :=
  ∀ 
    (a x₀ : ℝ) (b x : ℝ → ℝ)
    (hb : Continuous b)
    (hxcont : Continuous x)
    (hxdiff : ∀ t : ℝ, 0 ≤ t → DifferentiableAt ℝ x t)
    (hx0 : x 0 = x₀)
    (hode : ∀ t : ℝ, 0 ≤ t → deriv x t = a * x t + b t),
    ∀ t : ℝ, 0 ≤ t →
      x t = Real.exp (a * t) * x₀ +
        ∫ s in (0 : ℝ)..t, Real.exp (a * (t - s)) * b s

def private_sde_cert_ch03 : Prop :=
  ∀ 
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (rate q x₀ T : ℝ) (hrate : 0 < rate) (hq : 0 ≤ q) (hT : 0 ≤ T)
    (H : Ω → ℝ → ℝ)
    (hH : ∀ (ω : Ω) (s : ℝ),
      H ω s = Real.sqrt q * Real.exp (-rate * (T - s)))
    (hHmeas : Measurable (Function.uncurry H))
    (hHprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHsq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
    let Y : Ω → ℝ := fun ω =>
      Real.exp (-rate * T) * x₀ +
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
          W ℱ hW H hHmeas hHprog hHsq T ω
    (∫ ω, Y ω ∂P) = Real.exp (-rate * T) * x₀ ∧
      (∫ ω, (Y ω - Real.exp (-rate * T) * x₀) ^ 2 ∂P) =
        q / (2 * rate) * (1 - Real.exp (-2 * rate * T))

def private_sde_cert_ch04 : Prop :=
  ∀ 
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ}
    {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {hcoord : ∀ k : Fin d,
      LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ}
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ}
    {bdrift : Fin n → Ω → ℝ → ℝ}
    {X : ℝ → Ω → Fin n → ℝ}
    {C : ℝ} (hC0 : 0 ≤ C)
    (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ),
      |H p k ω s| ≤ C)
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    (hma : ∀ (p q : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : ∀ (p q : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ (p q : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : ℝ → (Fin n → ℝ) → ℝ}
    {ft : ℝ → (Fin n → ℝ) → ℝ}
    {fx : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {fxx : ℝ → (Fin n → ℝ) →
       (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (ht : ∀ s z, HasDerivAt (fun r => f r z) (ft s z) s)
    (hx : ∀ s z, HasFDerivAt (f s) (fx s z) z)
    (hxx : ∀ s z, HasFDerivAt (fx s) (fxx s z) z)
    (hftc : Continuous (Function.uncurry ft))
    (hfxc : Continuous (Function.uncurry fx))
    (hfxxc : Continuous (Function.uncurry fxx))
    (hfxxunif : ∀ (s : ℝ) (ε : ℝ), 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ z w : Fin n → ℝ,
        ‖z - w‖ < δ → ‖fxx s z - fxx s w‖ ≤ ε)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hfbd : ∀ (s : ℝ) (z : Fin n → ℝ),
      |ft s z| ≤ K ∧ ‖fx s z‖ ≤ K ∧ ‖fxx s z‖ ≤ K)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s =>
        coordDeriv (fx s) p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ fun ω s =>
        coordDeriv (fx s) p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv (fx s) p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T),
    (fun ω : Ω => f T (X T ω) - f 0 (X 0 ω)) =ᵐ[P]
      fun ω : Ω =>
        (∫ s in Set.Ioc (0 : ℝ) T, ft s (X s ω) ∂volume)
          + (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv (fx s) p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d,
              stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
                (fun ω s =>
                  coordDeriv (fx s) p (X s ω) * H p k ω s)
                (hmg p k) (hpg p k) (hqg p k) T ω)
          + (1 / 2 : ℝ) * ∑ p : Fin n, ∑ q : Fin n,
              ∫ s in Set.Ioc (0 : ℝ) T,
                coordDeriv₂ (fxx s) p q (X s ω) *
                  (∑ k : Fin d, H p k ω s * H q k ω s) ∂volume

def private_sde_cert_ch05 : Prop :=
  ∀ 
    (n : ℕ) (q : ℝ) (hq : 0 < q)
    (v : (Fin n → ℝ) → ℝ) (hv : ContDiff ℝ 2 v)
    (hInt : Integrable (fun x : Fin n → ℝ =>
      Real.exp (-(v x / q))))
    (hZ : 0 < ∫ x : Fin n → ℝ, Real.exp (-(v x / q))),
    let Z : ℝ := ∫ x : Fin n → ℝ, Real.exp (-(v x / q))
    let p : (Fin n → ℝ) → ℝ := fun x =>
      Z⁻¹ * Real.exp (-(v x / q))
    (∀ x : Fin n → ℝ, 0 ≤ p x) ∧
    (∫ x : Fin n → ℝ, p x = 1) ∧
    (∀ x : Fin n → ℝ,
      (∑ i : Fin n,
        fderiv ℝ (fun y : Fin n → ℝ =>
          (-(1 / 2 : ℝ) *
            fderiv ℝ v y (Pi.single i (1 : ℝ))) * p y) x
          (Pi.single i (1 : ℝ))) =
      q / 2 * ∑ i : Fin n,
        fderiv ℝ (fun y : Fin n → ℝ =>
          fderiv ℝ p y (Pi.single i (1 : ℝ))) x
          (Pi.single i (1 : ℝ)))


