-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.euler_maruyama_strong_half_order
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:24:10.102344+00:00
-- url     : https://prove2.me/submissions/842076a2-d46a-49b6-9ffc-543bb5216d39
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Theorems.Thm_AppliedSDE_SarkkaSolin_euler_maruyama_grid_l2_local_error
import Theorems.Thm_AppliedSDE_SarkkaSolin_euler_grid_mean_square_from_local_error
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology BigOperators

theorem solution
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
            W.W (((k.val : ℝ) * T / n)) ω)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 0 < n →
      (∫ ω, (X T ω - E n (Fin.last n) ω) ^ 2 ∂P) ≤
        C * (T / n) := by
  obtain ⟨c, hc, hgrid⟩ :=
    AppliedSDE.SarkkaSolin.euler_maruyama_grid_l2_local_error
      P W ℱ hW T x₀ hT b σ hLip X hXcont hXmom
      H hH hHmeas hHprog hHsq hXeq E hE0 hErec
  refine ⟨c * T * Real.exp (c * T), ?_, ?_⟩
  · positivity
  intro n hn
  obtain ⟨e, hzero, hstep, hlink⟩ := hgrid n hn
  have hterminal :=
    AppliedSDE.SarkkaSolin.euler_grid_mean_square_from_local_error
      c T hc hT.le e n hn hzero hstep
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have htime : (n : ℝ) * T / n = T := by
    field_simp [hnreal]
  have hlast := hlink (Fin.last n)
  simp only [Fin.val_last, htime] at hlast
  calc
    (∫ ω, (X T ω - E n (Fin.last n) ω) ^ 2 ∂P) =
        e n := hlast.symm
    _ ≤ c * T * (T / n) * Real.exp (c * T) := hterminal
    _ = (c * T * Real.exp (c * T)) * (T / n) := by ring
