-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardWindow_F000
-- name    : LevyStochCalc_Ito_PicardWindow_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:27:21.472038+00:00
-- url     : https://prove2.me/theorems/5866c24d-3915-493e-8b44-992096a7a3b7
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardWindow
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardWindow. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardLocality_F000
import Definitions.Def_LevyStochCalc_Ito_PicardLocality_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Solutions of the SDE on a window

`SolvesOn` records that a path map satisfies the jump-diffusion integral equation at every time
of `[0, T]`, in the `picardStep` form; the integrand hypotheses that make the two stochastic
integrals well-typed are bundled existentially, as in
`LevyStochCalc.Ito.Setting.JumpDiffusion.is_solution`, so that a solution can be re-read with any
proof of them. Two solutions on a common window and a common filtration agree, by the Bielecki
contraction.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### From an `S²` bound to the time-integrated energy -/

/-! ### Auxiliary Bielecki facts -/

omit [MeasurableSpace E] in
/-- Two path maps agreeing a.s. at every time of the window have equal Bielecki norms. -/
theorem bieleckiNorm_congr_ae_on (β T : ℝ) {Y Z : ℝ → Ω → (Fin n → ℝ)}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, Y t =ᵐ[P] Z t) :
    bieleckiNorm (P := P) β T Y = bieleckiNorm (P := P) β T Z := by
  unfold bieleckiNorm
  refine iSup_congr fun t => iSup_congr fun ht => ?_
  have hinner : (∫⁻ ω, ∑ i, (‖Y t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [h t ht] with ω hω
    rw [hω]
  rw [hinner]
omit [MeasurableSpace E] in
/-- A finite `S²` norm gives a finite Bielecki norm at weight `0`. -/
theorem bieleckiNorm_lt_top_of_supL2 {T : ℝ} (hT : 0 < T) {Z : ℝ → Ω → (Fin n → ℝ)}
    (hS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤) :
    bieleckiNorm (P := P) 0 T Z < ⊤ := by
  set M := ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P with hM
  have hMfin : M < ⊤ := hS T hT
  unfold bieleckiNorm
  have hMhalf : M ^ ((1 : ℝ) / 2) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hMfin.ne
  refine lt_of_le_of_lt ?_ hMhalf
  refine iSup_le fun t => iSup_le fun ht => ?_
  have hslice : (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ≤ M := by
    refine lintegral_mono fun ω => ?_
    exact le_iSup (fun u : Set.Icc (0 : ℝ) T =>
      ∑ i, (‖Z (u : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ⟨t, ht⟩
  calc ENNReal.ofReal (Real.exp (-(0 : ℝ) * t))
        * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      = (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2) := by
        simp
    _ ≤ M ^ ((1 : ℝ) / 2) := ENNReal.rpow_le_rpow hslice (by norm_num)
omit [MeasurableSpace E] in
/-- The Bielecki norm of a difference of two path maps of finite norm is finite. -/
theorem bieleckiNorm_sub_lt_top_of_lt_top {β : ℝ} (hβ : 0 ≤ β) (T : ℝ)
    {X Y : ℝ → Ω → (Fin n → ℝ)}
    (hXm : Measurable (Function.uncurry X)) (hYm : Measurable (Function.uncurry Y))
    (hX : bieleckiNorm (P := P) 0 T X < ⊤) (hY : bieleckiNorm (P := P) 0 T Y < ⊤) :
    bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i) < ⊤ := by
  have hneg : bieleckiNorm (P := P) 0 T (fun t ω => -(Y t ω))
      = bieleckiNorm (P := P) 0 T Y := by
    unfold bieleckiNorm
    refine iSup_congr fun t => iSup_congr fun _ => ?_
    congr 2
    exact lintegral_congr fun ω => Finset.sum_congr rfl fun i _ => by simp
  have hEq : (fun t ω i => X t ω i - Y t ω i)
      = fun t (ω : Ω) => X t ω + (fun i => -(Y t ω i)) := by
    funext t ω i
    simp [Pi.add_apply, sub_eq_add_neg]
  have hnegm : Measurable (Function.uncurry fun t (ω : Ω) => -(Y t ω)) :=
    measurable_neg.comp hYm
  have hadd := _root_.Prove2MeSourceProof.h_1a604e3d857ca06f911ef6c7 (P := P) 0 T X (fun t ω => -(Y t ω))
    (fun t => _root_.Prove2MeSourceProof.h_d9c9229a83986bc9d7b21f99 _ hXm t)
    (fun t => _root_.Prove2MeSourceProof.h_d9c9229a83986bc9d7b21f99 (fun t ω => -(Y t ω)) hnegm t)
  refine lt_of_le_of_lt (bieleckiNorm_le_bieleckiNorm_zero hβ T _) ?_
  rw [hEq]
  refine lt_of_le_of_lt hadd ?_
  rw [hneg]
  exact ENNReal.add_lt_top.mpr ⟨hX, hY⟩
/-- A finite extended real dominated by a strict multiple of itself vanishes. -/
theorem eq_zero_of_le_mul_self {a q : ℝ≥0∞} (ha : a ≠ ⊤) (hq : q < 1) (h : a ≤ q * a) :
    a = 0 := by
  by_contra h0
  have hlt : a * q < a * 1 := ENNReal.mul_lt_mul_right h0 ha hq
  rw [mul_one] at hlt
  rw [mul_comm q a] at h
  exact absurd h (not_le.mpr hlt)
/-! ### Solutions on a window -/

section Solves

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (x₀ : Fin n → ℝ)

/-- `X` satisfies the jump-diffusion integral equation, relative to `ℱ`, at every time of
`[0, T]`. The integrand hypotheses that make the two stochastic integrals well-typed are
bundled existentially, as in `JumpDiffusion.is_solution`. -/
structure SolvesOn (X : ℝ → Ω → (Fin n → ℝ)) (T : ℝ) : Prop where
  /-- Joint measurability of the diffusion integrand along `X`. -/
  h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
    Measurable (Function.uncurry fun ω s => coeffs.σ s (X s ω) i j)
  /-- Progressive measurability of the diffusion integrand along `X`. -/
  h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X s ω) i j
  /-- `L²` boundedness of the diffusion integrand on every finite horizon. -/
  h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤
  /-- Joint measurability of the jump integrand along `X`. -/
  h_γ_meas : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i
  /-- Marked progressive measurability of the jump integrand along `X`. -/
  h_γ_progMeas : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X s ω) e i
  /-- `L²` boundedness of the jump integrand on every finite horizon. -/
  h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤
  /-- The integral equation at every time of the window. -/
  eqn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i : Fin n,
    X t ω i = picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
      h_γ_meas h_γ_progMeas h_γ_sq t ω i
/-- A solution on a window is a solution on every shorter window. -/
theorem SolvesOn.mono {X : ℝ → Ω → (Fin n → ℝ)} {T T' : ℝ} (hTT : T' ≤ T)
    (h : SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T) :
    SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T' := by
  obtain ⟨a, b, c, e, f, g, heq⟩ := h
  exact ⟨a, b, c, e, f, g, fun t ht => heq t ⟨ht.1, ht.2.trans hTT⟩⟩
end Solves

/-! ### The canonical integrand hypotheses along a process with a finite `S²` norm -/

section Canonical

variable {ν : Measure E}
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}

end Canonical

/-! ### The window fixed point is a solution -/

section FixedPoint

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)

end FixedPoint

end LevyStochCalc.Ito.Picard


