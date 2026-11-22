-- Prove2me | Definitions.Def_NonvacuityBSDEJRateU_F000
-- name    : NonvacuityBSDEJRateU_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:41:46.669183+00:00
-- url     : https://prove2.me/theorems/79e81cc0-018f-4e5b-9d23-04ee660ff46b
-- title:
--   Source declarations: NonvacuityBSDEJRateU
-- statement:
--   Source-preserving extracted declarations from NonvacuityBSDEJRateU. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_CellAverageRateMarked_F001
import Definitions.Def_NonvacuityBSDEJJump_F002
import Definitions.Def_NonvacuityBSDEJRate_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Cell averages of the jump integrand of a backward equation with jumps

For the scalar backward equation

  `Y_t = J_1 − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

of `NonvacuityBSDEJJump`, whose jump integrand is the window indicator `1_{(0, 1]}` and whose
terminal datum is its compensated integral `J_1` over the horizon, the pathwise cell average
`cellTimeAverage_U` over the uniform partition of `[0, 1]` into `M` cells returns the
window indicator itself, so the averaged integrand carries marked energy `1` for the intensity
`δ₁` while the averaging error carries marked energy `0`. The jump integrand of an arbitrary
solution triple differs from the window indicator by marked energy `0`, and at the mark `1`
carried by `δ₁` its cell averages agree almost surely with those of the window indicator.

The average subtracted here is the pathwise cell average `cellTimeAverage_U`, not the
`ℱ_{t_n}`-conditional projection; the equation is the single equation with vanishing generator,
terminal datum `J_1` and horizon `1`.

## Main statements

* `cellTimeAverage_U_jumpU` — the cell average of the window indicator over the uniform
  partition of `[0, 1]` into `M ≥ 1` cells is `1` at every time of `(0, 1]`.
* `cellTimeAverage_U_jumpU_eq` — that cell average is the window indicator itself.
* `markedEnergy_cellTimeAverage_U_jumpU` and
  `markedEnergy_jumpU_sub_cellTimeAverage_U` — the averaged integrand has marked energy
  `1` on `[0, 1]` and the averaging error marked energy `0`.
* `markedEnergy_sub_jumpU_eq_zero_of_solvesBSDEJ` — the jump integrand of a solution triple
  differs from the window indicator by marked energy `0`.
* `cellTimeAverage_U_eq_of_solvesBSDEJ` — almost surely the cell averages at the mark `1`
  of the jump integrand of a solution triple are the values of the window indicator.
* `markedEnergy_cellTimeAverage_U_of_solvesBSDEJ` — those cell averages have marked
  energy `1` on `[0, 1]`.
* `markedEnergy_sub_cellAverage_U_expWeight_le` — the cell-average error of the separated
  integrand `(s, e) ↦ e^{1 - max s 0} · e` has marked energy at most `(e / M) ^ 2`.
* `exists_solvesBSDEJ_cellAverage_U_nontrivial` — on a probability space carrying such a driver
  the equation has a solution triple, the cell averages of the window indicator carry marked
  energy `1` and vanishing averaging error, and the cell averages of the jump integrand of every
  solution triple carry marked energy `1`.

## References

* Bouchard, B. & Elie, R., *Discrete-time approximation of decoupled Forward-Backward SDE with
  jumps*, Stochastic Processes Appl. **118(1)**, 2008, pp. 53–75.
* Delong, Ł., *BSDEs with Jumps and their Actuarial and Financial Applications*, Springer 2013,
  §4.1.
-/

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.BSDEJ.Solves
open LevyStochCalc.BSDEJ.PathRegularity
open LevyStochCalc.Driver (LevyDriver)

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {M : ℕ}

/-! ### Cells of the uniform partition -/

/-- Every cell of the uniform partition of `[0, 1]` into `M ≥ 1` cells is contained in
`[0, 1]`. -/
theorem uniformPartition_cell_subset (hM : 0 < M) (n : Fin M) :
    Set.Icc (uniformPartition M n.castSucc) (uniformPartition M n.succ) ⊆ Set.Icc (0 : ℝ) 1 := by
  refine Set.Icc_subset_Icc ?_ ?_
  · rw [← uniformPartition_zero (M := M)]
    exact (strictMono_uniformPartition hM).monotone (Fin.zero_le _)
  · rw [← uniformPartition_last hM]
    exact (strictMono_uniformPartition hM).monotone (Fin.le_last _)
/-- A time lying in a cell of the uniform partition of `[0, 1]` into `M ≥ 1` cells lies in
`(0, 1]`. -/
theorem mem_Ioc_of_mem_uniformPartition_cell (hM : 0 < M) {n : Fin M} {s : ℝ}
    (h1 : uniformPartition M n.castSucc < s) (h2 : s ≤ uniformPartition M n.succ) :
    s ∈ Set.Ioc (0 : ℝ) 1 := by
  have hmono := strictMono_uniformPartition hM
  have hlo : (0 : ℝ) ≤ uniformPartition M n.castSucc := by
    rw [← uniformPartition_zero (M := M)]
    exact hmono.monotone (Fin.zero_le _)
  have hhi : uniformPartition M n.succ ≤ 1 := by
    rw [← uniformPartition_last hM]
    exact hmono.monotone (Fin.le_last _)
  exact ⟨lt_of_le_of_lt hlo h1, h2.trans hhi⟩
/-! ### The cell average of the window indicator -/

omit [MeasurableSpace Ω] in
/-- The pathwise cell average of the window indicator over the uniform partition of `[0, 1]`
into `M ≥ 1` cells is `1` at every time of `(0, 1]`. -/
theorem cellTimeAverage_U_jumpU (hM : 0 < M) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (ω : Ω) (e : ℝ) :
    cellTimeAverage_U (uniformPartition M) (jumpU Ω) s ω e = 1 := by
  classical
  have hmono := strictMono_uniformPartition hM
  obtain ⟨n₀, hn₀, huniq⟩ := _root_.Prove2MeSourceProof.h_aa940cfe8f26de935fbb8849 hmono uniformPartition_zero
    (uniformPartition_last hM) hs
  have hab : uniformPartition M n₀.castSucc < uniformPartition M n₀.succ :=
    hmono Fin.castSucc_lt_succ
  have hvol : (volume (Set.Icc (uniformPartition M n₀.castSucc)
      (uniformPartition M n₀.succ))).toReal
      = uniformPartition M n₀.succ - uniformPartition M n₀.castSucc := by
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  have hint : ∫ u in Set.Icc (uniformPartition M n₀.castSucc) (uniformPartition M n₀.succ),
      jumpU Ω u ω e
      = uniformPartition M n₀.succ - uniformPartition M n₀.castSucc := by
    have hcongr : ∫ u in Set.Icc (uniformPartition M n₀.castSucc)
        (uniformPartition M n₀.succ), jumpU Ω u ω e
        = ∫ _u in Set.Icc (uniformPartition M n₀.castSucc)
            (uniformPartition M n₀.succ), (1 : ℝ) := by
      refine setIntegral_congr_ae measurableSet_Icc ?_
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu0 humem
      have hmem := uniformPartition_cell_subset hM n₀ humem
      have hne : u ≠ 0 := by simpa using hu0
      have hIoc : u ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hmem.1 (Ne.symm hne), hmem.2⟩
      rw [jumpU_apply, Set.indicator_of_mem hIoc]
    rw [hcongr, setIntegral_const, smul_eq_mul, measureReal_def, hvol, mul_one]
  simp only [cellTimeAverage_U]
  rw [Finset.sum_eq_single n₀]
  · rw [if_pos hn₀, hint, one_div, inv_mul_cancel₀ (sub_ne_zero.mpr hab.ne')]
  · intro b _ hb
    exact if_neg fun hcon => hb (huniq b hcon)
  · intro hcon
    exact absurd (Finset.mem_univ n₀) hcon
omit [MeasurableSpace Ω] in
/-- The pathwise cell average of the window indicator over the uniform partition of `[0, 1]`
into `M ≥ 1` cells is the window indicator. -/
theorem cellTimeAverage_U_jumpU_eq (hM : 0 < M) :
    cellTimeAverage_U (uniformPartition M) (jumpU Ω) = jumpU Ω := by
  classical
  funext s ω e
  by_cases hs : s ∈ Set.Ioc (0 : ℝ) 1
  · rw [cellTimeAverage_U_jumpU hM hs ω e, jumpU_apply, Set.indicator_of_mem hs]
  · rw [jumpU_apply, Set.indicator_of_notMem hs]
    simp only [cellTimeAverage_U]
    refine Finset.sum_eq_zero fun n _ => if_neg ?_
    rintro ⟨h1, h2⟩
    exact hs (mem_Ioc_of_mem_uniformPartition_cell hM h1 h2)
/-- The pathwise cell averages of the window indicator over the uniform partition of `[0, 1]`
into `M ≥ 1` cells have marked energy `1` on `[0, 1]` for the intensity `δ_1`. -/
theorem markedEnergy_cellTimeAverage_U_jumpU (hM : 0 < M) :
    Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
      (fun ω s e => cellTimeAverage_U (uniformPartition M) (jumpU Ω) s ω e) = 1 := by
  rw [cellTimeAverage_U_jumpU_eq (Ω := Ω) hM]
  exact _root_.Prove2MeSourceProof.h_f155e4082a26872bbbd3bfda
/-- The cell-average error of the window indicator over the uniform partition of `[0, 1]` into
`M ≥ 1` cells has marked energy `0` on `[0, 1]` for the intensity `δ_1`. -/
theorem markedEnergy_jumpU_sub_cellTimeAverage_U (hM : 0 < M) :
    Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
      (fun ω s e => jumpU Ω s ω e
        - cellTimeAverage_U (uniformPartition M) (jumpU Ω) s ω e) = 0 := by
  rw [cellTimeAverage_U_jumpU_eq (Ω := Ω) hM]
  simp [Poisson.Compensated.markedEnergy]
/-! ### The jump integrand of an arbitrary solution -/

/-- The jump integrand of a solution of the backward equation with vanishing generator,
terminal datum the compensated integral of `1_{(0, 1]}` at time `1` and horizon `1` differs from
`1_{(0, 1]}` by marked energy `0` on `[0, 1]`. -/
theorem markedEnergy_sub_jumpU_eq_zero_of_solvesBSDEJ
    (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    {Y' : ℝ → Ω → ℝ} {Z' : ℝ → Ω → (Fin 1 → ℝ)} {U' : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (jumpLeg D 1) 1 Y' Z' U') :
    Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
      (fun ω s e => U' s ω e - jumpU Ω s ω e) = 0 := by
  obtain ⟨Y, hY, -⟩ := _root_.Prove2MeSourceProof.h_037e724daadf008d5ad1442c D
  have hf0 : ∫⁻ _s in Set.Icc (0 : ℝ) 1, (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 < ⊤ := by simp
  obtain ⟨-, huniq⟩ := _root_.Prove2MeSourceProof.h_01c878d1e4a6afef88ed0c78 D (fun _ _ _ _ => (0 : ℝ)) (L := 0) le_rfl
    measurable_generator_zero lipschitz_generator_zero zero_lt_one hf0 (memLp_jumpLeg_one D)
    (aestronglyMeasurable_jumpLeg_one D)
  exact (huniq Y' Y Z' (zeroZ Ω) U' (jumpU Ω) h hY).2.2
/-- The jump integrand of a solution of that equation agrees at the mark `1` with `1_{(0, 1]}`,
almost surely and at almost every time of `[0, 1]`. -/
theorem ae_eq_jumpU_of_solvesBSDEJ (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    {Y' : ℝ → Ω → ℝ} {Z' : ℝ → Ω → (Fin 1 → ℝ)} {U' : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (jumpLeg D 1) 1 Y' Z' U') :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), U' s ω 1 = jumpU Ω s ω 1 := by
  have hzero := markedEnergy_sub_jumpU_eq_zero_of_solvesBSDEJ D h
  have hmU : Measurable fun p : Ω × ℝ × ℝ => U' p.2.1 p.1 p.2.2 := h.U_meas
  have hmJ : Measurable fun p : Ω × ℝ × ℝ => jumpU Ω p.2.1 p.1 p.2.2 := jumpU_meas
  have hmd : Measurable fun p : Ω × ℝ × ℝ =>
      U' p.2.1 p.1 p.2.2 - jumpU Ω p.2.1 p.1 p.2.2 := hmU.sub hmJ
  rw [Poisson.Compensated.markedEnergy_eq_eLpNorm_sq
    (φ := fun ω s e => U' s ω e - jumpU Ω s ω e) hmd 1] at hzero
  have h0 : eLpNorm (fun p : Ω × ℝ × ℝ => U' p.2.1 p.1 p.2.2 - jumpU Ω p.2.1 p.1 p.2.2) 2
      (Poisson.Compensated.markedEnergyMeasure P (Measure.dirac (1 : ℝ)) 1) = 0 :=
    (pow_eq_zero_iff two_ne_zero).mp hzero
  have hae := (eLpNorm_eq_zero_iff hmd.aestronglyMeasurable (by norm_num)).mp h0
  have hae' : ∀ᵐ p ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
      (Measure.dirac (1 : ℝ)))), U' p.2.1 p.1 p.2.2 = jumpU Ω p.2.1 p.1 p.2.2 := by
    have hmeas : Poisson.Compensated.markedEnergyMeasure P (Measure.dirac (1 : ℝ)) 1
        = P.prod ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (Measure.dirac (1 : ℝ))) := rfl
    rw [← hmeas]
    filter_upwards [hae] with p hp
    have hp' : U' p.2.1 p.1 p.2.2 - jumpU Ω p.2.1 p.1 p.2.2 = 0 := hp
    linarith
  filter_upwards [Measure.ae_ae_of_ae_prod hae'] with ω hω
  filter_upwards [Measure.ae_ae_of_ae_prod hω] with s hs
  rwa [ae_dirac_eq, Filter.eventually_pure] at hs
omit [IsProbabilityMeasure P] in
/-- A jump integrand agreeing at the mark `1` with `1_{(0, 1]}` almost surely and at almost
every time of `[0, 1]` has, almost surely, the cell averages of `1_{(0, 1]}` at that mark over
the uniform partition of `[0, 1]` into `M ≥ 1` cells. -/
theorem cellTimeAverage_U_eq_of_ae_eq {U' : ℝ → Ω → ℝ → ℝ} (hM : 0 < M)
    (hU : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), U' s ω 1 = jumpU Ω s ω 1) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, cellTimeAverage_U (uniformPartition M) U' s ω 1
      = cellTimeAverage_U (uniformPartition M) (jumpU Ω) s ω 1 := by
  classical
  filter_upwards [hU] with ω hω
  have hω' : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.Icc (0 : ℝ) 1 → U' u ω 1 = jumpU Ω u ω 1 :=
    (ae_restrict_iff' measurableSet_Icc).mp hω
  have hint : ∀ n : Fin M,
      ∫ u in Set.Icc (uniformPartition M n.castSucc) (uniformPartition M n.succ), U' u ω 1
        = ∫ u in Set.Icc (uniformPartition M n.castSucc) (uniformPartition M n.succ),
            jumpU Ω u ω 1 := by
    intro n
    refine setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards [hω'] with u hu humem
    exact hu (uniformPartition_cell_subset hM n humem)
  intro s
  simp only [cellTimeAverage_U]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hc : uniformPartition M n.castSucc < s ∧ s ≤ uniformPartition M n.succ
  · rw [if_pos hc, if_pos hc, hint n]
  · rw [if_neg hc, if_neg hc]
/-- Almost surely, the cell averages at the mark `1` of the jump integrand of a solution over
the uniform partition of `[0, 1]` into `M ≥ 1` cells are the values of `1_{(0, 1]}`. -/
theorem cellTimeAverage_U_eq_of_solvesBSDEJ (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    {Y' : ℝ → Ω → ℝ} {Z' : ℝ → Ω → (Fin 1 → ℝ)} {U' : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (jumpLeg D 1) 1 Y' Z' U') (hM : 0 < M) :
    ∀ᵐ ω ∂P, ∀ s : ℝ,
      cellTimeAverage_U (uniformPartition M) U' s ω 1 = jumpU Ω s ω 1 := by
  filter_upwards [cellTimeAverage_U_eq_of_ae_eq hM (ae_eq_jumpU_of_solvesBSDEJ D h)]
    with ω hω
  intro s
  rw [hω s, cellTimeAverage_U_jumpU_eq (Ω := Ω) hM]
/-- The cell averages of the jump integrand of a solution over the uniform partition of `[0, 1]`
into `M ≥ 1` cells have marked energy `1` on `[0, 1]` for the intensity `δ_1`. -/
theorem markedEnergy_cellTimeAverage_U_of_solvesBSDEJ
    (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    {Y' : ℝ → Ω → ℝ} {Z' : ℝ → Ω → (Fin 1 → ℝ)} {U' : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (jumpLeg D 1) 1 Y' Z' U') (hM : 0 < M) :
    Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
      (fun ω s e => cellTimeAverage_U (uniformPartition M) U' s ω e) = 1 := by
  have hcta := cellTimeAverage_U_eq_of_solvesBSDEJ D h hM
  have key : Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
      (fun ω s e => cellTimeAverage_U (uniformPartition M) U' s ω e)
      = Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
        (fun ω s e => jumpU Ω s ω e) := by
    rw [Poisson.Compensated.markedEnergy, Poisson.Compensated.markedEnergy]
    refine lintegral_congr_ae ?_
    filter_upwards [hcta] with ω hω
    refine lintegral_congr fun s => ?_
    rw [lintegral_dirac, lintegral_dirac, hω s]
  rw [key]
  exact _root_.Prove2MeSourceProof.h_f155e4082a26872bbbd3bfda
/-! ### The rate for a separated Lipschitz marked integrand -/

/-- The cell-average error of the separated marked integrand `(s, e) ↦ e^{1 - max s 0} · e` over
the uniform partition of `[0, 1]` into `M ≥ 1` cells has marked energy at most `(e / M) ^ 2` on
`[0, 1]` for the intensity `δ_1`. -/
theorem markedEnergy_sub_cellAverage_U_expWeight_le (hM : 0 < M) :
    Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
        (fun ω s e => expWeightClamp s * e
          - cellTimeAverage_U (uniformPartition M)
              (fun u (_ : Ω) (e : ℝ) => expWeightClamp u * e) s ω e)
      ≤ ENNReal.ofReal ((Real.exp 1 / M) ^ 2) := by
  have hbd := markedEnergy_sub_cellTimeAverage_U_le_of_lipschitz
    (Ω := Ω) (E := ℝ) (φ := fun e : ℝ => e) (h := expWeightClamp) (π := uniformPartition M)
    (δ := 1 / M) (K := Real.exp 1) P (Measure.dirac (1 : ℝ))
    (strictMono_uniformPartition hM) uniformPartition_zero (uniformPartition_last hM)
    (uniformPartition_mesh hM) _root_.Prove2MeSourceProof.h_5f044d421aced7bf9f1cdb5e
  have hmark : ∫⁻ e : ℝ, (‖e‖₊ : ℝ≥0∞) ^ 2 ∂Measure.dirac (1 : ℝ) = 1 := by
    rw [lintegral_dirac]
    simp
  have heq : (Real.exp 1 * (1 / M)) ^ 2 * 1 = (Real.exp 1 / M) ^ 2 := by
    rw [mul_one, mul_one_div]
  rw [hmark, mul_one, heq] at hbd
  exact hbd
/-! ### The witness -/

/-- On some probability space there are a Lévy driver with one Brownian coordinate and jump
intensity `δ_1` and a solution triple of the backward equation with vanishing generator,
terminal datum the compensated integral of `1_{(0, 1]}` at time `1` and horizon `1`; for every
`M ≥ 1` the pathwise cell averages of `1_{(0, 1]}` over the uniform partition of `[0, 1]` into
`M` cells have marked energy `1` and vanishing averaging error, and the jump integrand of every
solution triple differs from `1_{(0, 1]}` by marked energy `0` and has cell averages of marked
energy `1`. -/
theorem exists_solvesBSDEJ_cellAverage_U_nontrivial :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))),
      (∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin 1 → ℝ)) (U : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (jumpLeg D 1) 1 Y Z U) ∧
        (∀ M : ℕ, 0 < M →
          Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
              (fun ω s e =>
                cellTimeAverage_U (uniformPartition M) (jumpU Ω) s ω e) = 1 ∧
            Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
              (fun ω s e => jumpU Ω s ω e
                - cellTimeAverage_U (uniformPartition M) (jumpU Ω) s ω e) = 0) ∧
        ∀ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin 1 → ℝ)) (U' : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (jumpLeg D 1) 1 Y' Z' U' →
            Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
                (fun ω s e => U' s ω e - jumpU Ω s ω e) = 0 ∧
              ∀ M : ℕ, 0 < M →
                Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
                  (fun ω s e =>
                    cellTimeAverage_U (uniformPartition M) U' s ω e) = 1 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (1 : ℝ))
  refine ⟨Ω, inferInstance, P, inferInstance, D, ?_,
    fun M hM => ⟨markedEnergy_cellTimeAverage_U_jumpU hM,
      markedEnergy_jumpU_sub_cellTimeAverage_U hM⟩,
    fun Y' Z' U' h => ⟨markedEnergy_sub_jumpU_eq_zero_of_solvesBSDEJ D h,
      fun M hM => markedEnergy_cellTimeAverage_U_of_solvesBSDEJ D h hM⟩⟩
  obtain ⟨Y, hY, -⟩ := _root_.Prove2MeSourceProof.h_037e724daadf008d5ad1442c D
  exact ⟨Y, zeroZ Ω, jumpU Ω, hY⟩
end LevyStochCalc.Examples.Nonvacuity


