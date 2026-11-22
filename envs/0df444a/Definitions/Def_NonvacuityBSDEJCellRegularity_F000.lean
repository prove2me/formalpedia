-- Prove2me | Definitions.Def_NonvacuityBSDEJCellRegularity_F000
-- name    : NonvacuityBSDEJCellRegularity_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:41:43.758469+00:00
-- url     : https://prove2.me/theorems/221590cb-ff7d-408f-b0cd-ca1d7774280b
-- title:
--   Source declarations: NonvacuityBSDEJCellRegularity
-- statement:
--   Source-preserving extracted declarations from NonvacuityBSDEJCellRegularity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_CellRegularity_F000
import Definitions.Def_NonvacuityBSDEJRate_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The path-regularity rate for the backward equation with the identity generator

For the scalar backward equation

  `Y_t = W_1 + ∫_t^1 Y_s ds − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

of `NonvacuityBSDEJExp` the Brownian integrand of every solution triple agrees `P ⊗ dt`-almost
everywhere on `Ω × [0, 1]` with the clamped weight `s ↦ e^{1 − max s 0}` and the jump integrand
carries marked energy `0`. The conditional cell average of an integrand constant in the sample
point is its deterministic cell average, so on the uniform grid of step `τ = 1 / N` the cell
error of the Brownian integrand is at most `e τ` at almost every time and the sum of its squares
over the `N` cells of the horizon is `e² τ²`, at most `e² τ`; hence
`CellRegularity D 1 Z U A (e ^ 2)` holds for every solution triple and every family `A` of marks.

## Main statements

* `lintegral_cell_sub_condCellAverage_le` — the conditional cell error of the Brownian
  integrand over a cell of length `τ` inside the horizon has energy at most `(e τ) ^ 2 * τ`.
* `cellRegularity_of_solvesBSDEJ_generator_id` — every solution triple of the equation obeys
  the path-regularity rate with constant `e ^ 2`, for every finite family of marks.
* `exists_solvesBSDEJ_cellRegularity` — on a probability space carrying such a driver the
  equation has a solution triple and every solution triple obeys that rate.

## References

* Zhang, J., *A numerical scheme for BSDEs*, Ann. Appl. Probab. **14(1)**, 2004, pp. 459–488,
  Theorem 3.1.
* Bouchard, B. & Elie, R., *Discrete-time approximation of decoupled Forward-Backward SDE with
  jumps*, Stochastic Processes Appl. **118(1)**, 2008, pp. 53–75, Theorem 2.1.
-/

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.BSDEJ.Solves
open LevyStochCalc.BSDEJ.PathRegularity
open LevyStochCalc.Driver (LevyDriver)

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Y' : ℝ → Ω → ℝ} {Z' : ℝ → Ω → (Fin 1 → ℝ)} {U' : ℝ → Ω → ℝ → ℝ} {a b τ : ℝ} {m N i : ℕ}

/-- The Brownian integrand of a solution of the backward equation with generator
`f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1` agrees almost surely, at almost every
time of a subinterval of the horizon, with the clamped weight `s ↦ e^{1 − max s 0}`. -/
theorem ae_ae_eq_expWeightClamp (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    (h : SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U')
    (hsub : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc a b)), Z' s ω 0 = expWeightClamp s := by
  filter_upwards [Measure.ae_ae_of_ae_prod (_root_.Prove2MeSourceProof.h_28ab96584fdceef9753ea692 D h)] with ω hω
  have hω' : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.Icc (0 : ℝ) 1 → Z' u ω 0 = expZ Ω u ω 0 :=
    (ae_restrict_iff' measurableSet_Icc).mp hω
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hω', compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu hu0 humem
  have hmem : u ∈ Set.Icc (0 : ℝ) 1 := hsub humem
  have hne : u ≠ 0 := by simpa using hu0
  have hIoc : u ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hmem.1 (Ne.symm hne), hmem.2⟩
  rw [hu hmem, expZ_eq_expWeightClamp hIoc ω 0]
/-- The conditional cell error of the Brownian integrand of such a solution over a cell of
length `τ > 0` contained in the horizon has energy at most `(e τ) ^ 2 * τ`. -/
theorem lintegral_cell_sub_condCellAverage_le (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    (h : SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U')
    (hτ : 0 < τ) (hsub : Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ) ⊆ Set.Icc (0 : ℝ) 1) :
    ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
        ∑ k : Fin 1, (‖Z' s ω k - condCellAverage_Z D τ Z' i ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal ((Real.exp 1 * τ) ^ 2 * τ) := by
  have hlen : ((i : ℝ) + 1) * τ - (i : ℝ) * τ = τ := by ring
  have hab : (i : ℝ) * τ < ((i : ℝ) + 1) * τ := by nlinarith
  have hint : ∀ᵐ ω ∂P, ∫ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ), Z' s ω 0
      = ∫ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ), expWeightClamp s := by
    filter_upwards [ae_ae_eq_expWeightClamp D h hsub] with ω hω
    exact setIntegral_congr_ae measurableSet_Icc ((ae_restrict_iff' measurableSet_Icc).mp hω)
  have hcond : (fun ω => condCellAverage_Z D τ Z' i ω 0) =ᵐ[P] fun _ =>
      τ⁻¹ * ∫ u in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ), expWeightClamp u := by
    refine (condCellAverage_Z_congr D τ
      (Z' := fun u (_ : Ω) (_ : Fin 1) => expWeightClamp u) hint).trans ?_
    rw [condCellAverage_Z_of_deterministic D τ expWeightClamp (fun _ _ _ => rfl) i 0]
  have hbound : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
      ∑ k : Fin 1, (‖Z' s ω k - condCellAverage_Z D τ Z' i ω k‖₊ : ℝ≥0∞) ^ 2
        ≤ ENNReal.ofReal ((Real.exp 1 * τ) ^ 2 * τ) := by
    filter_upwards [hcond, ae_ae_eq_expWeightClamp D h hsub] with ω hω hωs
    have hstep : ∀ᵐ s ∂(volume.restrict (Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ))),
        ∑ k : Fin 1, (‖Z' s ω k - condCellAverage_Z D τ Z' i ω k‖₊ : ℝ≥0∞) ^ 2
          ≤ ENNReal.ofReal ((Real.exp 1 * τ) ^ 2) := by
      have hnull : (volume.restrict (Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ)))
          {(i : ℝ) * τ} = 0 := by simp
      filter_upwards [hωs, compl_mem_ae_iff.mpr hnull, ae_restrict_mem measurableSet_Icc] with
        s hs1 hs0 hsmem
      have hne : s ≠ (i : ℝ) * τ := by simpa using hs0
      have hIoc : s ∈ Set.Ioc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ) :=
        ⟨lt_of_le_of_ne hsmem.1 (Ne.symm hne), hsmem.2⟩
      have hbd := abs_sub_intervalAverage_le _root_.Prove2MeSourceProof.h_5f044d421aced7bf9f1cdb5e hab hIoc
      rw [hlen, one_div] at hbd
      rw [Fin.sum_univ_one, hs1, hω]
      set x := expWeightClamp s
        - τ⁻¹ * ∫ u in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ), expWeightClamp u with hx
      clear_value x
      rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from (ofReal_norm x).symm,
        ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [abs_nonneg x])
    refine (lintegral_mono_ae hstep).trans (le_of_eq ?_)
    rw [setLIntegral_const, Real.volume_Icc, hlen, ← ENNReal.ofReal_mul (sq_nonneg _)]
  refine (lintegral_mono_ae hbound).trans (le_of_eq ?_)
  rw [lintegral_const, measure_univ, mul_one]
/-- The jump integrand of a solution of that equation vanishes almost everywhere on the
horizon. -/
theorem ae_ae_U_eq_zero (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    (h : SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U') :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      (fun e => U' s ω e) =ᵐ[Measure.dirac (1 : ℝ)] 0 := by
  have hmU : Measurable fun p : Ω × ℝ × ℝ => U' p.2.1 p.1 p.2.2 := h.U_meas
  have hzero : Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
      (fun ω s e => U' s ω e) = 0 := by
    obtain ⟨Y, hY, -⟩ := _root_.Prove2MeSourceProof.h_cdebc989955e2f6003b4385b D
    have hf0 : ∫⁻ _s in Set.Icc (0 : ℝ) 1, (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 < ⊤ := by
      rw [lintegral_generator_id_zero]
      exact ENNReal.zero_lt_top
    obtain ⟨-, huniq⟩ := _root_.Prove2MeSourceProof.h_01c878d1e4a6afef88ed0c78 D (fun _ y _ _ => y) (L := 1) zero_le_one
      measurable_generator_id lipschitz_generator_id one_pos hf0 (memLp_brownian_one D.W)
      (aestronglyMeasurable_brownian_one_augJoint D)
    simpa only [sub_zero] using (huniq Y' Y Z' (expZ Ω) U' (fun _ _ _ => (0 : ℝ)) h hY).2.2
  rw [Poisson.Compensated.markedEnergy_eq_eLpNorm_sq (φ := fun ω s e => U' s ω e) hmU 1] at hzero
  have hae : ∀ᵐ p ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (Measure.dirac (1 : ℝ)))),
      U' p.2.1 p.1 p.2.2 = 0 :=
    (eLpNorm_eq_zero_iff hmU.aestronglyMeasurable (by norm_num)).mp
      ((pow_eq_zero_iff two_ne_zero).mp hzero)
  filter_upwards [Measure.ae_ae_of_ae_prod hae] with ω hω
  filter_upwards [Measure.ae_ae_of_ae_prod hω] with s hs using hs
/-- The marked integrals of the jump integrand of such a solution along a finite family of marks
vanish almost surely at almost every time of a subinterval of the horizon. -/
theorem ae_ae_setIntegral_mark_eq_zero (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    (h : SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U')
    (hsub : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1) (A : Fin m → Set ℝ) :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc a b)), ∀ k : Fin m,
      ∫ e in A k, U' s ω e ∂(Measure.dirac (1 : ℝ)) = 0 := by
  filter_upwards [ae_ae_U_eq_zero D h] with ω hω
  filter_upwards [hω.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))] with s hs
  exact fun k => integral_eq_zero_of_ae (ae_restrict_of_ae hs)
/-- A cell of the uniform grid of step `τ` with `N` cells of total length `1` lies in `[0, 1]`. -/
theorem cell_subset_horizon (hτ : 0 < τ) (hNτ : (N : ℝ) * τ = 1) (hi : i < N) :
    Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ) ⊆ Set.Icc (0 : ℝ) 1 := by
  have hle : ((i : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hi
  exact Set.Icc_subset_Icc (mul_nonneg (Nat.cast_nonneg i) hτ.le)
    (le_of_le_of_eq (mul_le_mul_of_nonneg_right hle hτ.le) hNτ)
/-- The conditional cell errors of the Brownian integrand of such a solution over the uniform
grid of step `τ` with `N` cells and total length `1` sum to at most `e ^ 2 * τ`. -/
theorem sum_lintegral_cell_sub_condCellAverage_le
    (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    (h : SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U')
    (hτ : 0 < τ) (hNτ : (N : ℝ) * τ = 1) :
    ∑ i ∈ Finset.range N, ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
        ∑ k : Fin 1, (‖Z' s ω k - condCellAverage_Z D τ Z' i ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal (Real.exp 1 ^ 2 * τ) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · simp [h0] at hNτ
    · exact Nat.one_le_cast.mpr h0
  have hτ1 : τ ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hN1) hτ.le]
  have hee : (0 : ℝ) < Real.exp 1 ^ 2 := by positivity
  refine (Finset.sum_le_sum fun i hi => lintegral_cell_sub_condCellAverage_le D h hτ
    (cell_subset_horizon hτ hNτ (Finset.mem_range.mp hi))).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast N,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hkey : (N : ℝ) * ((Real.exp 1 * τ) ^ 2 * τ)
      = Real.exp 1 ^ 2 * τ ^ 2 * ((N : ℝ) * τ) := by ring
  rw [hkey, hNτ, mul_one]
  nlinarith [mul_nonneg (mul_nonneg hee.le hτ.le) (sub_nonneg.mpr hτ1)]
/-- The conditional cell errors of the marked integrals of the jump integrand of such a solution
over that grid all vanish. -/
theorem sum_lintegral_cell_mark_eq_zero (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    (h : SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U')
    (hτ : 0 < τ) (hNτ : (N : ℝ) * τ = 1) (A : Fin m → Set ℝ) :
    ∑ i ∈ Finset.range N, ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
        ∑ k : Fin m, (‖(∫ e in A k, U' s ω e ∂(Measure.dirac (1 : ℝ)))
          - condCellAverage_U D τ U' A i ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  have hsub := cell_subset_horizon hτ hNτ (Finset.mem_range.mp hi)
  have hcond : ∀ᵐ ω ∂P, ∀ k : Fin m, condCellAverage_U D τ U' A i ω k = 0 := by
    refine ae_all_iff.mpr fun k => ?_
    have hk : ∀ᵐ ω ∂P, ∫ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
        ∫ e in A k, U' s ω e ∂(Measure.dirac (1 : ℝ)) = 0 := by
      filter_upwards [ae_ae_setIntegral_mark_eq_zero D h hsub A] with ω hω
      exact integral_eq_zero_of_ae (by filter_upwards [hω] with s hs using hs k)
    filter_upwards [condCellAverage_U_of_ae_setIntegral_eq_zero D τ hk] with ω hω using hω
  refine (lintegral_congr_ae (g := fun _ => 0) ?_).trans lintegral_zero
  filter_upwards [hcond, ae_ae_setIntegral_mark_eq_zero D h hsub A] with ω hω1 hω2
  refine (lintegral_congr_ae (g := fun _ => 0) ?_).trans lintegral_zero
  filter_upwards [hω2] with s hs
  exact Finset.sum_eq_zero fun k _ => by rw [hs k, hω1 k, sub_zero, nnnorm_zero]; simp
/-! ### The witness -/

/-- Every solution triple of the backward equation with generator `f(s, y, z, u) = y`, terminal
datum `W_1` and horizon `1` obeys the `L²` path-regularity rate with constant `e ^ 2`, for every
finite family of marks. -/
theorem cellRegularity_of_solvesBSDEJ_generator_id
    (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    (h : SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U')
    (A : Fin m → Set ℝ) : CellRegularity D 1 Z' U' A (Real.exp 1 ^ 2) := by
  have key : ∀ N : ℕ, 0 < N → (0 : ℝ) < 1 / (N : ℝ) ∧ (N : ℝ) * (1 / (N : ℝ)) = 1 := by
    intro N hN
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hN)
    exact ⟨by positivity, by field_simp⟩
  refine ⟨by positivity, fun N hN =>
    sum_lintegral_cell_sub_condCellAverage_le D h (key N hN).1 (key N hN).2, fun N hN => ?_⟩
  rw [sum_lintegral_cell_mark_eq_zero D h (key N hN).1 (key N hN).2 A]
  simp
/-- On some probability space there are a Lévy driver with one Brownian coordinate and jump
intensity `δ_1` and a solution triple of the backward equation with generator
`f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1`; every solution triple of that
equation obeys the `L²` path-regularity rate with constant `e ^ 2`, for every family of marks. -/
theorem exists_solvesBSDEJ_cellRegularity :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))),
      (∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin 1 → ℝ)) (U : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y Z U) ∧
        ∀ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin 1 → ℝ)) (U' : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U' →
            ∀ (m : ℕ) (A : Fin m → Set ℝ), CellRegularity D 1 Z' U' A (Real.exp 1 ^ 2) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (1 : ℝ))
  exact ⟨Ω, inferInstance, P, inferInstance, D, exists_solvesBSDEJ_generator_id D,
    fun _ _ _ h _ A => cellRegularity_of_solvesBSDEJ_generator_id D h A⟩
end LevyStochCalc.Examples.Nonvacuity


