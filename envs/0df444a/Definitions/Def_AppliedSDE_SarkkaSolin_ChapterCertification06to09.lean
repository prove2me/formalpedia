-- Prove2me | Definitions.Def_AppliedSDE_SarkkaSolin_ChapterCertification06to09
-- name    : AppliedSDE_SarkkaSolin_ChapterCertification06to09
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-13T18:03:44.11674+00:00
-- url     : https://prove2.me/theorems/5c014805-599a-4a8c-a463-474ae81ffa6a
-- title:
--   Certification propositions for 06to09
-- statement:
--   Named propositions for chapter certification: Chapters 6–9. Each declaration is a Prop-valued abbreviation of the exact published-goal candidate statement from the current textbook Draft. It is not a theorem, axiom, proof or verified result. All quantified mathematical hypotheses are preserved.
--
--   Representative mathematical obligation:
--
--   $$
--   \mathcal{P}_{06to09}
--   $$
-- source:
--   Original derived formal certification definitions from Simo Särkkä and Arno Solin (2019), Applied Stochastic Differential Equations, Chapters 6–9, printed pp. 80–178. https://doi.org/10.1017/9781108186735

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

def private_sde_cert_ch06 : Prop :=
  ∀ 
    (n : ℕ) (rate V : ℝ) (hrate : 0 < rate) (hV : 0 ≤ V)
    (t : Fin n → ℝ) (a : Fin n → ℝ),
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      a i * a j * (V * Real.exp (-rate * |t i - t j|))

def private_sde_cert_ch07 : Prop :=
  ∀ 
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (T : ℝ) (hT : 0 < T)
    (θ : Ω → ℝ → ℝ)
    (hθmeas : Measurable (Function.uncurry θ))
    (hθprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ θ)
    (hθq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖θ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hθzero : ∀ (ω : Ω) (s : ℝ), T ≤ s → θ ω s = 0)
    (Z : Ω → ℝ)
    (hZ : ∀ ω : Ω,
      Z ω = Real.exp (
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW θ hθmeas hθprog hθq T ω -
        (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..T, θ ω s ^ 2))
    (hZmean : ∫ ω, Z ω ∂P = 1),
    let Q : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal (Z ω))
    let shifted : ℝ≥0 → Ω → ℝ := fun t ω =>
      W.W (t : ℝ) ω - ∫ s in (0 : ℝ)..(t : ℝ), θ ω s
    IsProbabilityMeasure Q ∧ IsBrownianReal shifted Q

def private_sde_cert_ch08 : Prop :=
  ∀ 
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (T x₀ : ℝ) (hT : 0 < T)
    (b σ : ℝ → ℝ)
    (hLip : ∃ L : ℝ, 0 ≤ L ∧
      (∀ x y : ℝ, |b x - b y| ≤ L * |x - y|) ∧
      (∀ x y : ℝ, |σ x - σ y| ≤ L * |x - y|))
    (X : ℝ → Ω → ℝ)
    (hXcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => X t ω))
    (hXmom : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
      Integrable (fun ω : Ω => (X t ω) ^ 2) P)
    (H : Ω → ℝ → ℝ)
    (hH : ∀ (ω : Ω) (s : ℝ), H ω s = σ (X s ω))
    (hHmeas : Measurable (Function.uncurry H))
    (hHprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHsq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXeq : ∀ t : ℝ, 0 ≤ t → t ≤ T →
      (fun ω : Ω => X t ω) =ᵐ[P] fun ω : Ω =>
        x₀ + (∫ s in (0 : ℝ)..t, b (X s ω)) +
          LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
            W ℱ hW H hHmeas hHprog hHsq t ω)
    (E : (n : ℕ) → Fin (n + 1) → Ω → ℝ)
    (hE0 : ∀ (n : ℕ) (ω : Ω), E n 0 ω = x₀)
    (hErec : ∀ (n : ℕ), 0 < n →
      ∀ (k : Fin n) (ω : Ω),
        E n k.succ ω = E n k.castSucc ω +
          b (E n k.castSucc ω) * (T / n) +
          σ (E n k.castSucc ω) *
          (W.W ((((k.val + 1 : ℕ) : ℝ) * T / n)) ω -
            W.W (((k.val : ℝ) * T / n)) ω)),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 0 < n →
      (∫ ω, (X T ω - E n (Fin.last n) ω) ^ 2 ∂P) ≤
        C * (T / n)

def private_sde_cert_ch09 : Prop :=
  ∀ 
    {n m : ℕ}
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (μ : Fin n → ℝ)
    (f : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (t : ℝ)
    (hf : ∀ i : Fin n, ContDiff ℝ 1 (fun x : Fin n → ℝ => f t x i))
    (hfb : ∃ C : ℝ, ∀ (x : Fin n → ℝ) (i : Fin n), |f t x i| ≤ C)
    (hfdb : ∃ D : ℝ, ∀ (x : Fin n → ℝ) (i : Fin n),
      ‖fderiv ℝ (fun y : Fin n → ℝ => f t y i) x‖ ≤ D)
    (i j : Fin n),
    (∫ z : Fin m → ℝ, f t (μ + L z) i * (L z) j
      ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1))) =
      ∑ k : Fin m, (L (Pi.single k (1 : ℝ))) j *
        (∫ z : Fin m → ℝ,
          fderiv ℝ (fun y : Fin n → ℝ => f t y i) (μ + L z)
            (L (Pi.single k (1 : ℝ)))
          ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1)))


