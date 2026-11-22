-- Prove2me | Definitions.Def_NonvacuityBSDEJRate_F002
-- name    : NonvacuityBSDEJRate_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:36:27.134971+00:00
-- url     : https://prove2.me/theorems/533d5f15-d4cb-4202-b75b-459ecb1511ab
-- title:
--   Source declarations: NonvacuityBSDEJRate
-- statement:
--   Source-preserving extracted declarations from NonvacuityBSDEJRate. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_CellAverageRate_F001
import Definitions.Def_NonvacuityBSDEJRate_F001
import Definitions.Def_SourceProof_28ab96584fdceef9753ea692
import Definitions.Def_SourceProof_5f044d421aced7bf9f1cdb5e

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cell-average rate for the backward equation with the identity generator

For the scalar backward equation

  `Y_t = W_1 + ∫_t^1 Y_s ds − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

of `NonvacuityBSDEJExp`, the Brownian integrand of every solution triple agrees `P ⊗ dt`-almost
everywhere on `Ω × [0, 1]` with the windowed weight `e^{1-s} 1_{(0, 1]}(s)`, hence with the
globally Lipschitz clamped weight `s ↦ e^{1 - max s 0}`. Transporting the deterministic bound
`LevyStochCalc.BSDEJ.PathRegularity.energy_sub_cellTimeAverage_le_of_lipschitz` along that
agreement gives, for every solution triple and every strictly monotone partition of `[0, 1]` of
mesh at most `δ`, the energy bound `(e δ) ^ 2` for the difference between the integrand and its
pathwise cell average.

The average subtracted here is the pathwise cell average `cellTimeAverage_Z`, not the
`ℱ_{t_n}`-conditional projection; the equation is the single equation with generator
`f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1`.

## Main statements

* `abs_expWeightClamp_sub_le` — the clamped weight `s ↦ e^{1 - max s 0}` is Lipschitz with
  constant `e`.
* `ae_eq_expZ_of_solvesBSDEJ` — the Brownian integrand of a solution triple agrees with `expZ`
  almost everywhere for `P ⊗ dt` on `Ω × [0, 1]`.
* `energy_sub_cellAverage_le_of_solvesBSDEJ` — the cell-average error of the Brownian integrand
  of a solution triple has energy at most `(e δ) ^ 2` on the horizon.
* `exists_solvesBSDEJ_cellAverage_rate` — on a probability space carrying such a driver the
  equation has a solution triple and every solution triple obeys that bound.

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

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The clamped exponential weight -/

/-! ### The Brownian integrand of a solution -/

/-! ### The pathwise cell average of a solution -/

omit [IsProbabilityMeasure P] in
/-- A Brownian integrand agreeing with `expZ` almost everywhere for the product of the sample
measure with Lebesgue measure on `[0, 1]` has, almost surely, the pathwise cell averages of the
clamped weight over every strictly monotone partition of `[0, 1]`. -/
theorem cellTimeAverage_eq_of_ae_eq {M : ℕ} {π : Fin (M + 1) → ℝ}
    {Z' : ℝ → Ω → (Fin 1 → ℝ)} (hmono : StrictMono π) (h0 : π 0 = 0)
    (hT : π (Fin.last M) = 1)
    (hZ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) 1))),
      Z' p.2 p.1 0 = expZ Ω p.2 p.1 0) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, cellTimeAverage_Z π Z' s ω 0
      = cellTimeAverage_Z π (fun u (_ : Ω) (_ : Fin 1) => expWeightClamp u) s ω 0 := by
  have hsub : ∀ n : Fin M, Set.Icc (π n.castSucc) (π n.succ) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro n
    refine Set.Icc_subset_Icc ?_ ?_
    · rw [← h0]
      exact hmono.monotone (Fin.zero_le _)
    · rw [← hT]
      exact hmono.monotone (Fin.le_last _)
  filter_upwards [Measure.ae_ae_of_ae_prod hZ] with ω hω
  have hω' : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.Icc (0 : ℝ) 1 → Z' u ω 0 = expZ Ω u ω 0 :=
    (ae_restrict_iff' measurableSet_Icc).mp hω
  have hint : ∀ n : Fin M, ∫ u in Set.Icc (π n.castSucc) (π n.succ), Z' u ω 0
      = ∫ u in Set.Icc (π n.castSucc) (π n.succ), expWeightClamp u := by
    intro n
    refine setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards [hω', compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu hu0 humem
    have hmem : u ∈ Set.Icc (0 : ℝ) 1 := hsub n humem
    have hne : u ≠ 0 := by simpa using hu0
    have hIoc : u ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hmem.1 (Ne.symm hne), hmem.2⟩
    rw [hu hmem, expZ_eq_expWeightClamp hIoc ω 0]
  intro s
  simp only [cellTimeAverage_Z]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hc : π n.castSucc < s ∧ s ≤ π n.succ
  · rw [if_pos hc, if_pos hc, hint n]
  · rw [if_neg hc, if_neg hc]
/-! ### The rate -/

/-- The cell-average error of the Brownian integrand of a solution of the backward equation with
generator `f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1`, over a strictly monotone
partition of `[0, 1]` of mesh at most `δ`, has energy at most `(e δ) ^ 2 * 1` on the horizon. -/
theorem energy_sub_cellAverage_le_of_solvesBSDEJ (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    {Y' : ℝ → Ω → ℝ} {Z' : ℝ → Ω → (Fin 1 → ℝ)} {U' : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U')
    {M : ℕ} {π : Fin (M + 1) → ℝ} {δ : ℝ} (hmono : StrictMono π) (h0 : π 0 = 0)
    (hT : π (Fin.last M) = 1) (hδ : ∀ n : Fin M, π n.succ - π n.castSucc ≤ δ) :
    Brownian.Ito.energy P 1 (fun ω s => Z' s ω 0 - cellTimeAverage_Z π Z' s ω 0)
      ≤ ENNReal.ofReal ((Real.exp 1 * δ) ^ 2 * 1) := by
  have hZ := _root_.Prove2MeSourceProof.h_28ab96584fdceef9753ea692 D h
  have hCA := cellTimeAverage_eq_of_ae_eq hmono h0 hT hZ
  have hnull : (volume.restrict (Set.Icc (0 : ℝ) 1)) {(0 : ℝ)} = 0 := by simp
  have hkey : Brownian.Ito.energy P 1
        (fun ω s => Z' s ω 0 - cellTimeAverage_Z π Z' s ω 0)
      = Brownian.Ito.energy P 1 (fun ω s => expWeightClamp s
          - cellTimeAverage_Z π (fun u (_ : Ω) (_ : Fin 1) => expWeightClamp u)
              s ω 0) := by
    simp only [Brownian.Ito.energy]
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.ae_ae_of_ae_prod hZ, hCA] with ω h1 h2
    refine lintegral_congr_ae ?_
    filter_upwards [h1, compl_mem_ae_iff.mpr hnull, ae_restrict_mem measurableSet_Icc] with
      s hs1 hs0 hsmem
    have hne : s ≠ 0 := by simpa using hs0
    have hIoc : s ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hsmem.1 (Ne.symm hne), hsmem.2⟩
    rw [hs1, expZ_eq_expWeightClamp hIoc ω 0, h2 s]
  rw [hkey]
  exact energy_sub_cellTimeAverage_le_of_lipschitz P hmono h0 hT hδ
    _root_.Prove2MeSourceProof.h_5f044d421aced7bf9f1cdb5e (0 : Fin 1)
/-! ### The witness -/

/-- On some probability space there are a Lévy driver with one Brownian coordinate and jump
intensity `δ_1` and a solution triple of the backward equation with generator
`f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1`; for every solution triple of that
equation and every strictly monotone partition of `[0, 1]` of mesh at most `δ`, the energy of
the difference between the Brownian integrand and its pathwise cell average over the partition
is at most `(e δ) ^ 2`. -/
theorem exists_solvesBSDEJ_cellAverage_rate :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))),
      (∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin 1 → ℝ)) (U : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y Z U) ∧
        ∀ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin 1 → ℝ)) (U' : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U' →
            ∀ (M : ℕ) (π : Fin (M + 1) → ℝ) (δ : ℝ), StrictMono π → π 0 = 0 →
              π (Fin.last M) = 1 → (∀ n : Fin M, π n.succ - π n.castSucc ≤ δ) →
                Brownian.Ito.energy P 1
                    (fun ω s => Z' s ω 0 - cellTimeAverage_Z π Z' s ω 0)
                  ≤ ENNReal.ofReal ((Real.exp 1 * δ) ^ 2) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (1 : ℝ))
  refine ⟨Ω, inferInstance, P, inferInstance, D, exists_solvesBSDEJ_generator_id D,
    fun Y' Z' U' h M π δ hmono h0 hT hδ => ?_⟩
  have hrate := energy_sub_cellAverage_le_of_solvesBSDEJ D h hmono h0 hT hδ
  rwa [mul_one] at hrate
/-! ### The uniform partition -/

/-- The uniform partition `n ↦ n / M` of the horizon `[0, 1]` into `M` cells. -/
noncomputable def uniformPartition (M : ℕ) : Fin (M + 1) → ℝ := fun n => (n : ℝ) / M
variable {M : ℕ}

/-- The uniform partition of `[0, 1]` into a positive number of cells is strictly monotone. -/
theorem strictMono_uniformPartition (hM : 0 < M) : StrictMono (uniformPartition M) := by
  intro a b hab
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hlt : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := Nat.cast_lt.mpr (Fin.lt_def.mp hab)
  exact div_lt_div_of_pos_right hlt hMpos
/-- The uniform partition starts at the left endpoint of `[0, 1]`. -/
theorem uniformPartition_zero : uniformPartition M 0 = 0 := by
  show (((0 : Fin (M + 1)) : ℕ) : ℝ) / M = 0
  simp
/-- The uniform partition into a positive number of cells ends at the right endpoint of
`[0, 1]`. -/
theorem uniformPartition_last (hM : 0 < M) : uniformPartition M (Fin.last M) = 1 := by
  have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  show (((Fin.last M : Fin (M + 1)) : ℕ) : ℝ) / M = 1
  rw [Fin.val_last, div_self hMne]
/-- Every cell of the uniform partition into `M` cells has length `1 / M`. -/
theorem uniformPartition_mesh_eq (hM : 0 < M) (n : Fin M) :
    uniformPartition M n.succ - uniformPartition M n.castSucc = 1 / M := by
  have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  show (((n.succ : Fin (M + 1)) : ℕ) : ℝ) / M - (((n.castSucc : Fin (M + 1)) : ℕ) : ℝ) / M
    = 1 / M
  rw [Fin.val_succ, Fin.val_castSucc, div_sub_div_same]
  push_cast
  ring_nf
/-- The mesh of the uniform partition into `M` cells is at most `1 / M`. -/
theorem uniformPartition_mesh (hM : 0 < M) (n : Fin M) :
    uniformPartition M n.succ - uniformPartition M n.castSucc ≤ 1 / M :=
  (uniformPartition_mesh_eq hM n).le
/-! ### The rate along the uniform partitions -/

/-- The cell-average error of the Brownian integrand of a solution of the backward equation with
generator `f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1`, over the uniform partition
of `[0, 1]` into `M` cells, has energy at most `(e / M) ^ 2` on the horizon. -/
theorem energy_sub_cellAverage_le_of_solvesBSDEJ_uniform
    (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    {Y' : ℝ → Ω → ℝ} {Z' : ℝ → Ω → (Fin 1 → ℝ)} {U' : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U')
    (hM : 0 < M) :
    Brownian.Ito.energy P 1
        (fun ω s => Z' s ω 0 - cellTimeAverage_Z (uniformPartition M) Z' s ω 0)
      ≤ ENNReal.ofReal ((Real.exp 1 / M) ^ 2) := by
  have hrate := energy_sub_cellAverage_le_of_solvesBSDEJ D h (strictMono_uniformPartition hM)
    uniformPartition_zero (uniformPartition_last hM) (uniformPartition_mesh hM)
  have heq : (Real.exp 1 * (1 / M)) ^ 2 * 1 = (Real.exp 1 / M) ^ 2 := by
    rw [mul_one, mul_one_div]
  rwa [heq] at hrate
/-- On some probability space there are a Lévy driver with one Brownian coordinate and jump
intensity `δ_1` and a solution triple of the backward equation with generator
`f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1`; for every solution triple of that
equation and every positive `M`, the energy of the difference between the Brownian integrand and
its pathwise cell average over the uniform partition of `[0, 1]` into `M` cells is at most
`(e / M) ^ 2`. -/
theorem exists_solvesBSDEJ_cellAverage_rate_uniform :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))),
      (∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin 1 → ℝ)) (U : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y Z U) ∧
        ∀ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin 1 → ℝ)) (U' : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U' →
            ∀ M : ℕ, 0 < M →
              Brownian.Ito.energy P 1
                  (fun ω s => Z' s ω 0
                    - cellTimeAverage_Z (uniformPartition M) Z' s ω 0)
                ≤ ENNReal.ofReal ((Real.exp 1 / M) ^ 2) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (1 : ℝ))
  exact ⟨Ω, inferInstance, P, inferInstance, D, exists_solvesBSDEJ_generator_id D,
    fun _ _ _ h M hM => energy_sub_cellAverage_le_of_solvesBSDEJ_uniform D h hM⟩
end LevyStochCalc.Examples.Nonvacuity


