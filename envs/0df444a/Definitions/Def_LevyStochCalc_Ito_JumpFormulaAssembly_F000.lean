-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaAssembly_F000
-- name    : LevyStochCalc_Ito_JumpFormulaAssembly_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:39:23.352877+00:00
-- url     : https://prove2.me/theorems/8d6520ff-4fb6-45a1-b141-0e793eb97c6b
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaAssembly
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaAssembly. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaIncrement_F001
import Definitions.Def_LevyStochCalc_Ito_ItoIntegrandAeCongr_F000
import Definitions.Def_LevyStochCalc_Ito_JumpTelescope_F000
import Definitions.Def_SourceProof_c9f8d91666f468ff1aabe966

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula along a chain of stopping times

A path that evolves continuously between the members of a chain of times and is translated by a
vector held fixed on each of the intervals they cut out satisfies, after composition with a
function of the state, a telescoping identity: the increment over the whole window is the sum of
the increments with the translation frozen on each interval plus the sum of the increments of the
translation at the right endpoints. Where the translated path agrees with a second path, the
integrands of the per-interval Itô formulas coincide with the integrands built from that second
path, so the per-interval Lebesgue and Itô integrals collapse into single integrals over the
window.

## Main statements

* `LevyStochCalc.Brownian.Ito.sum_range_shift_telescope` — the pathwise telescoping identity.
* `LevyStochCalc.Brownian.Ito.stopped_sub_congr` — the increment of a cut-off integrand between
  two times depends on the integrand only between them.
* `LevyStochCalc.Brownian.Ito.stopped_sub_shift_funext` — the increment of the cut-off integrand
  of a translated path is the increment of the cut-off integrand of the path it agrees with.
* `LevyStochCalc.Brownian.Ito.sum_range_integral_stopped_sub_of_chain` — the Lebesgue integrals
  of the increments along a chain covering `(0, T]` sum to the integral over that window.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_sum_range_stopped_sub_of_chain` — the
  Itô integrals of those increments sum to the Itô integral over that window.
* `LevyStochCalc.Brownian.Ito.itoFormula_chain` — Itô's formula over the window for a path
  translated piecewise along a chain, with the per-interval increments as a hypothesis.
* `LevyStochCalc.Brownian.Ito.itoFormula_chain_path` — the same with the two endpoints
  identified with the values of the path the translations agree with.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal

universe u

section Pathwise

variable {Ω : Type*}

/-- The increment of a function of a path translated piecewise along a family of times splits
into the increments with the translation frozen on each interval and the increments of the
translation at the right endpoints. -/
theorem sum_range_shift_telescope {n : ℕ} (f : (Fin n → ℝ) → ℝ) (V : ℝ → Ω → Fin n → ℝ)
    (c : ℕ → Ω → Fin n → ℝ) (θ : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) :
    f (V (θ m ω) ω + c m ω) - f (V (θ 0 ω) ω + c 0 ω)
      = (∑ k ∈ Finset.range m,
            (f (V (θ (k + 1) ω) ω + c k ω) - f (V (θ k ω) ω + c k ω)))
        + ∑ k ∈ Finset.range m,
            (f (V (θ (k + 1) ω) ω + c (k + 1) ω) - f (V (θ (k + 1) ω) ω + c k ω)) := by
  have hsum : ∑ k ∈ Finset.range m,
        ((f (V (θ (k + 1) ω) ω + c k ω) - f (V (θ k ω) ω + c k ω))
          + (f (V (θ (k + 1) ω) ω + c (k + 1) ω) - f (V (θ (k + 1) ω) ω + c k ω)))
      = ∑ k ∈ Finset.range m,
          (f (V (θ (k + 1) ω) ω + c (k + 1) ω) - f (V (θ k ω) ω + c k ω)) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [← Finset.sum_add_distrib, hsum]
  exact (Finset.sum_range_sub (fun i => f (V (θ i ω) ω + c i ω)) m).symm
/-- The horizon clipped at a time equal to `0` is `0`. -/
theorem clipTime_eq_zero {τ : Ω → WithTop ℝ} {T : ℝ} {ω : Ω} (hT : 0 ≤ T)
    (h : τ ω = ((0 : ℝ) : WithTop ℝ)) : clipTime τ T ω = 0 := by
  rw [clipTime_eq_min h, min_eq_right hT]
/-- The horizon clipped at a time squeezed between `0` and `0` is `0`. -/
theorem clipTime_eq_zero_of_le_zero {τ : Ω → WithTop ℝ} {T : ℝ} {ω : Ω} (hT : 0 ≤ T)
    (hle : ((0 : ℝ) : WithTop ℝ) ≤ τ ω) (hge : τ ω ≤ ((0 : ℝ) : WithTop ℝ)) :
    clipTime τ T ω = 0 :=
  clipTime_eq_zero hT (le_antisymm hge hle)
end Pathwise

section Support

variable {Ω : Type*}

/-- The increment of a cut-off integrand between two times depends on the integrand only at the
times strictly beyond the first and at or before the second. -/
theorem stopped_sub_congr {K L : Ω → ℝ → ℝ} {τ₀ τ₁ : Ω → WithTop ℝ} {ω : Ω}
    (hmono : τ₀ ω ≤ τ₁ ω)
    (hagree : ∀ s : ℝ, τ₀ ω < ((s : ℝ) : WithTop ℝ) → ((s : ℝ) : WithTop ℝ) ≤ τ₁ ω →
      K ω s = L ω s) (s : ℝ) :
    Probability.stopped τ₁ K ω s - Probability.stopped τ₀ K ω s
      = Probability.stopped τ₁ L ω s - Probability.stopped τ₀ L ω s := by
  by_cases h₀ : ((s : ℝ) : WithTop ℝ) ≤ τ₀ ω
  · have h₁ : ((s : ℝ) : WithTop ℝ) ≤ τ₁ ω := h₀.trans hmono
    simp [Probability.stopped, h₀, h₁]
  · have hlt : τ₀ ω < ((s : ℝ) : WithTop ℝ) := not_le.mp h₀
    by_cases h₁ : ((s : ℝ) : WithTop ℝ) ≤ τ₁ ω
    · simp [Probability.stopped, h₀, h₁, hagree s hlt h₁]
    · simp [Probability.stopped, h₀, h₁]
/-- Between two times on which a translated path agrees with a second path, the increment of the
cut-off integrand built from the translated path is the increment of the one built from the
second path. -/
theorem stopped_sub_shift_apply {n : ℕ} {τ₀ τ₁ : Ω → WithTop ℝ} {ω : Ω} (hmono : τ₀ ω ≤ τ₁ ω)
    (Φ : (Fin n → ℝ) → ℝ) (g : Ω → ℝ → ℝ) {V X : ℝ → Ω → Fin n → ℝ} {b : Ω → Fin n → ℝ}
    (hagree : ∀ s : ℝ, τ₀ ω < ((s : ℝ) : WithTop ℝ) → ((s : ℝ) : WithTop ℝ) ≤ τ₁ ω →
      V s ω + b ω = X s ω) (s : ℝ) :
    Probability.stopped τ₁ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
      = Probability.stopped τ₁ (fun ω s => Φ (X s ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (X s ω) * g ω s) ω s :=
  stopped_sub_congr hmono (fun s h₁ h₂ => by rw [hagree s h₁ h₂]) s
/-- The two integrands of `stopped_sub_shift_apply` agree as functions of the sample point and
the time. -/
theorem stopped_sub_shift_funext {n : ℕ} {τ₀ τ₁ : Ω → WithTop ℝ} (hmono : ∀ ω, τ₀ ω ≤ τ₁ ω)
    (Φ : (Fin n → ℝ) → ℝ) (g : Ω → ℝ → ℝ) {V X : ℝ → Ω → Fin n → ℝ} {b : Ω → Fin n → ℝ}
    (hagree : ∀ (ω : Ω) (s : ℝ), τ₀ ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) ≤ τ₁ ω → V s ω + b ω = X s ω) :
    (fun (ω : Ω) (s : ℝ) =>
        Probability.stopped τ₁ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
          - Probability.stopped τ₀ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s)
      = fun ω s => Probability.stopped τ₁ (fun ω s => Φ (X s ω) * g ω s) ω s
          - Probability.stopped τ₀ (fun ω s => Φ (X s ω) * g ω s) ω s :=
  funext fun ω => funext fun s => stopped_sub_shift_apply (hmono ω) Φ g (hagree ω) s
end Support

section Collapse

variable {Ω : Type*}

/-- Along a chain of times covering `(0, T]` the integrals of the increments of a cut-off
integrand sum to the integral of the integrand over that window. -/
theorem sum_range_integral_stopped_sub_of_chain (σ : ℕ → Ω → WithTop ℝ) (K : Ω → ℝ → ℝ)
    {m : ℕ} {T : ℝ} {ω : Ω} (h0 : σ 0 ω ≤ ((0 : ℝ) : WithTop ℝ))
    (hm : ((T : ℝ) : WithTop ℝ) ≤ σ m ω)
    (hint : ∀ k, MeasureTheory.IntegrableOn
      (Probability.stopped (σ k) K ω) (Set.Ioc (0 : ℝ) T) volume) :
    ∑ k ∈ Finset.range m, ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped (σ (k + 1)) K ω s - Probability.stopped (σ k) K ω s) ∂volume
      = ∫ s in Set.Ioc (0 : ℝ) T, K ω s ∂volume := by
  have hsum : (∫ s in Set.Ioc (0 : ℝ) T, (∑ k ∈ Finset.range m,
          (Probability.stopped (σ (k + 1)) K ω s - Probability.stopped (σ k) K ω s)) ∂volume)
      = ∑ k ∈ Finset.range m, ∫ s in Set.Ioc (0 : ℝ) T,
          (Probability.stopped (σ (k + 1)) K ω s - Probability.stopped (σ k) K ω s) ∂volume :=
    MeasureTheory.integral_finsetSum _ fun k _ => (hint (k + 1)).sub (hint k)
  rw [← hsum]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s hs =>
    sum_range_stopped_eq_of_chain σ K h0 hm hs
end Collapse

section ItoCollapse

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- Along a chain of times covering `(0, T]` the Itô integrals of the increments of a cut-off
integrand sum to the Itô integral of the integrand at `T`. -/
theorem stochasticIntegralBrownian_sum_range_stopped_sub_of_chain
    (σ : ℕ → Ω → WithTop ℝ) (hσ : ∀ k, MeasureTheory.IsStoppingTime ℱ (σ k))
    {K : Ω → ℝ → ℝ} (hmK : Measurable (Function.uncurry K))
    (hpK : Probability.ProgressivelyMeasurable ℱ K)
    (hqK : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {m : ℕ} {T : ℝ} (h0 : ∀ ω, σ 0 ω ≤ ((0 : ℝ) : WithTop ℝ)) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ((T : ℝ) : WithTop ℝ) ≤ σ m ω →
      (∑ k ∈ Finset.range m, stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped (σ (k + 1)) K ω s - Probability.stopped (σ k) K ω s)
        (measurable_uncurry_stopped_sub (hσ k) (hσ (k + 1)) hmK)
        (progressivelyMeasurable_stopped_sub (hσ k) (hσ (k + 1)) hpK)
        (energy_stopped_sub_lt_top (hσ k) (hσ (k + 1)) hmK hqK) T ω)
      = stochasticIntegralBrownian W ℱ hℱ K hmK hpK hqK T ω := by
  classical
  obtain ⟨hms, hps, hqs, hae⟩ := _root_.Prove2MeSourceProof.h_4158bbe01732caa4bdb467b2 W ℱ hℱ
    (fun k ω s => Probability.stopped (σ (k + 1)) K ω s - Probability.stopped (σ k) K ω s)
    (fun k => measurable_uncurry_stopped_sub (hσ k) (hσ (k + 1)) hmK)
    (fun k => progressivelyMeasurable_stopped_sub (hσ k) (hσ (k + 1)) hpK)
    (fun k => energy_stopped_sub_lt_top (hσ k) (hσ (k + 1)) hmK hqK) (Finset.range m) hT
  have hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → ((s : ℝ) : WithTop ℝ) ≤ σ m ω →
      (∑ k ∈ Finset.range m,
          (Probability.stopped (σ (k + 1)) K ω s - Probability.stopped (σ k) K ω s))
        = K ω s := by
    intro ω s hs hsm
    rw [sum_range_stopped_sub, stopped_eq_zero_of_le_zero K (h0 ω) hs, sub_zero]
    simp [Probability.stopped, hsm]
  have hcongr := _root_.Prove2MeSourceProof.h_c9f8d91666f468ff1aabe966 (σ m) W ℱ hℱ (hσ m)
    hms hps hqs hmK hpK hqK hagree hT
  filter_upwards [hae, hcongr] with ω h1 h2 hmω
  exact h1.symm.trans (h2 hmω)
end ItoCollapse

section Algebra

/-- A sum over a range of the three terms of an Itô formula collapses termwise. -/
theorem sum_range_itoTerms {n d m : ℕ} {a : ℕ → Fin n → ℝ} {b : ℕ → Fin n → Fin d → ℝ}
    {e : ℕ → Fin n → Fin n → ℝ} {A : Fin n → ℝ} {B : Fin n → Fin d → ℝ}
    {E : Fin n → Fin n → ℝ} (ha : ∀ p, ∑ k ∈ Finset.range m, a k p = A p)
    (hb : ∀ p j, ∑ k ∈ Finset.range m, b k p j = B p j)
    (he : ∀ p q, ∑ k ∈ Finset.range m, e k p q = E p q) :
    ∑ k ∈ Finset.range m,
        ((∑ p : Fin n, a k p) + (∑ p : Fin n, ∑ j : Fin d, b k p j)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, e k p q)
      = (∑ p : Fin n, A p) + (∑ p : Fin n, ∑ j : Fin d, B p j)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, E p q := by
  have h1 : ∑ k ∈ Finset.range m, ∑ p : Fin n, a k p = ∑ p : Fin n, A p := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => ha p
  have h2 : ∑ k ∈ Finset.range m, ∑ p : Fin n, ∑ j : Fin d, b k p j
      = ∑ p : Fin n, ∑ j : Fin d, B p j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => hb p j
  have h3 : ∑ k ∈ Finset.range m, ∑ p : Fin n, ∑ q : Fin n, e k p q
      = ∑ p : Fin n, ∑ q : Fin n, E p q := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => he p q
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, h3]
end Algebra

section Assembly

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- Finitely many almost-everywhere identities hold simultaneously almost everywhere. -/
theorem ae_forall_lt {F G : ℕ → Ω → ℝ} {m : ℕ} (h : ∀ k < m, F k =ᵐ[P] G k) :
    ∀ᵐ ω ∂P, ∀ k < m, F k ω = G k ω := by
  rw [MeasureTheory.ae_all_iff]
  intro k
  by_cases hk : k < m
  · filter_upwards [h k hk] with ω hω
    exact fun _ => hω
  · exact Filter.Eventually.of_forall fun _ hk' => absurd hk' hk
variable {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ j : Fin d, IsBrownianFiltration (W.W j) ℱ')

end Assembly

end LevyStochCalc.Brownian.Ito


