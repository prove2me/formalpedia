-- Prove2me | Definitions.Def_SourceProof_71f235c6c37a3ef4243fe9d4
-- name    : SourceProof_71f235c6c37a3ef4243fe9d4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:53:26.453175+00:00
-- url     : https://prove2.me/theorems/c51bed09-9d02-4707-86fd-78c22c06dca3
-- title:
--   LevyStochCalc source module: SourceProof_71f235c6c37a3ef4243fe9d4
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_sub_cells` comes from the `LevyStochCalc.Ito.ItoFormulaSimpleShiftIntegral` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaSimpleShiftCells_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for an increment translated by a simple random vector

On a cell where a stopping time and a simple random mark are both constant the translation is by
a fixed vector, so the cell indicator — bounded and known at the deterministic time carried by
the cell — passes inside the Itô integral of the increment, and the Itô integral of the increment
read along the mark splits over the cells. Itô's formula for the increment between the two
stopping times then applies on each cell with a constant shift, and recombining the cells gives
the formula for a function translated by the simple random vector. The cells themselves are
measurable at the deterministic times the stopping time takes as soon as the mark is measurable
at that stopping time.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_sub_cells` — the Itô integral of
  that increment splits over the cells.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_simpleShift` — Itô's formula for the increment of
  a path between two stopping times, for a function translated by a simple random vector.
* `LevyStochCalc.Brownian.Ito.measurableSet_cell_of_measurable` — a mark measurable at a stopping
  time has cells measurable at the deterministic times that stopping time takes.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section CellIntegral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α : Type*}
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_71f235c6c37a3ef4243fe9d4
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (hστ : ∀ ω, σ ω ≤ τ ω)
    {c : Ω → α} {Vs : Finset α} (hcVs : ∀ ω, c ω ∈ Vs)
    {J : Finset ℝ} {T : ℝ} (hJ0 : ∀ a ∈ J, 0 ≤ a) (hJT : ∀ a ∈ J, a < T)
    (hσJ : ∀ ω, (∃ a ∈ J, σ ω = ((a : ℝ) : WithTop ℝ)) ∨ σ ω = ⊤)
    (hcell : ∀ a ∈ J, ∀ v ∈ Vs,
      MeasurableSet[ℱ a] {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v})
    (K : α → Ω → ℝ → ℝ) (hmK : ∀ v, Measurable (Function.uncurry (K v)))
    (hpK : ∀ v, Probability.ProgressivelyMeasurable ℱ (K v))
    (hqK : ∀ (v : α) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖K v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {Kc : Ω → ℝ → ℝ} (hKc : ∀ ω s, Kc ω s = K (c ω) ω s)
    (hmc : Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s))
    (hpc : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s)
    (hqc : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hT : 0 < T) :
    ∀ᵐ ω ∂P, stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s)
        hmc hpc hqc T ω
      = ∑ x ∈ J ×ˢ Vs, cellWeight σ c x.1 x.2 ω * stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => Probability.stopped τ (K x.2) ω s - Probability.stopped σ (K x.2) ω s)
          (measurable_uncurry_stopped_sub hσ hτ (hmK x.2))
          (progressivelyMeasurable_stopped_sub hσ hτ (hpK x.2))
          (energy_stopped_sub_lt_top hσ hτ (hmK x.2) (hqK x.2)) T ω := by
  classical
  have hVeq : ∀ x : ℝ × α, (fun ω => LevyStochCalc.Brownian.Ito.hitInd σ x.1 ω * LevyStochCalc.Brownian.Ito.cellWeight σ c x.1 x.2 ω)
      = LevyStochCalc.Brownian.Ito.cellWeight σ c x.1 x.2 :=
    fun x => funext fun ω => LevyStochCalc.Brownian.Ito.hitInd_mul_cellWeight σ c x.1 x.2 ω
  have hgz : ∀ x : ℝ × α, ¬ (x.1 ∈ J ∧ x.2 ∈ Vs) →
      (fun (ω : Ω) (s : ℝ) => LevyStochCalc.Brownian.Ito.hitInd σ x.1 ω * LevyStochCalc.Brownian.Ito.cellWeight σ c x.1 x.2 ω
        * (LevyStochCalc.Probability.stopped τ (K x.2) ω s - LevyStochCalc.Probability.stopped σ (K x.2) ω s))
        = fun _ _ => (0 : ℝ) :=
    fun _ hx => LevyStochCalc.Brownian.Ito.cell_stopped_sub_eq_zero hcVs hσJ K hx
  have hgm : ∀ x : ℝ × α, Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      LevyStochCalc.Brownian.Ito.hitInd σ x.1 ω * LevyStochCalc.Brownian.Ito.cellWeight σ c x.1 x.2 ω
        * (LevyStochCalc.Probability.stopped τ (K x.2) ω s - LevyStochCalc.Probability.stopped σ (K x.2) ω s)) := by
    intro x
    by_cases hx : x.1 ∈ J ∧ x.2 ∈ Vs
    · have hV : Measurable fun ω => LevyStochCalc.Brownian.Ito.hitInd σ x.1 ω * LevyStochCalc.Brownian.Ito.cellWeight σ c x.1 x.2 ω := by
        rw [hVeq x]
        exact LevyStochCalc.Brownian.Ito.measurable_cellWeight σ c x.1 x.2 (hcell x.1 hx.1 x.2 hx.2)
      exact LevyStochCalc.Brownian.Ito.measurable_weight_mul_stopped_sub hσ hτ hV (hmK x.2)
    · rw [hgz x hx]
      exact measurable_const
  have hgp := _root_.Prove2MeSourceProof.h_d00127f498106978ba6c00a0 hσ hτ hστ hcVs hJ0 hσJ hcell K hpK
  have hgq : ∀ (x : ℝ × α) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖LevyStochCalc.Brownian.Ito.hitInd σ x.1 ω * LevyStochCalc.Brownian.Ito.cellWeight σ c x.1 x.2 ω
        * (LevyStochCalc.Probability.stopped τ (K x.2) ω s
          - LevyStochCalc.Probability.stopped σ (K x.2) ω s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro x
    refine LevyStochCalc.Brownian.Ito.energy_weight_mul_stopped_sub_lt_top hσ hτ
      (V := fun ω => LevyStochCalc.Brownian.Ito.hitInd σ x.1 ω * LevyStochCalc.Brownian.Ito.cellWeight σ c x.1 x.2 ω) (fun ω => ?_)
      (hmK x.2) (hqK x.2)
    rw [LevyStochCalc.Brownian.Ito.hitInd_mul_cellWeight]
    exact LevyStochCalc.Brownian.Ito.abs_cellWeight_le_one σ c x.1 x.2 ω
  have hsumEq := _root_.Prove2MeSourceProof.h_e8133b533716b7cb54a9c43e (J := J) hστ hcVs hσJ K hKc
  obtain ⟨hms, hps, hqs, hae⟩ := _root_.Prove2MeSourceProof.h_4158bbe01732caa4bdb467b2 W ℱ hℱ
    (fun (x : ℝ × α) (ω : Ω) (s : ℝ) => LevyStochCalc.Brownian.Ito.hitInd σ x.1 ω * LevyStochCalc.Brownian.Ito.cellWeight σ c x.1 x.2 ω
      * (LevyStochCalc.Probability.stopped τ (K x.2) ω s - LevyStochCalc.Probability.stopped σ (K x.2) ω s))
    hgm hgp hgq (J ×ˢ Vs) hT
  have hcongr := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hsumEq hmc hpc hqc hms hps hqs T
  have hcells : ∀ᵐ ω ∂P, ∀ x ∈ J ×ˢ Vs,
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
        (fun (ω : Ω) (s : ℝ) => LevyStochCalc.Brownian.Ito.hitInd σ x.1 ω * LevyStochCalc.Brownian.Ito.cellWeight σ c x.1 x.2 ω
          * (LevyStochCalc.Probability.stopped τ (K x.2) ω s - LevyStochCalc.Probability.stopped σ (K x.2) ω s))
        (hgm x) (hgp x) (hgq x) T ω
      = LevyStochCalc.Brownian.Ito.cellWeight σ c x.1 x.2 ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => LevyStochCalc.Probability.stopped τ (K x.2) ω s - LevyStochCalc.Probability.stopped σ (K x.2) ω s)
          (LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub hσ hτ (hmK x.2))
          (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub hσ hτ (hpK x.2))
          (LevyStochCalc.Brownian.Ito.energy_stopped_sub_lt_top hσ hτ (hmK x.2) (hqK x.2)) T ω := by
    rw [Filter.eventually_all_finset]
    intro x hx
    obtain ⟨haJ, hvVs⟩ := Finset.mem_product.mp hx
    have hpull := LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_hitInd_stopped_sub W ℱ hℱ hσ hτ hστ
      (hJ0 x.1 haJ) (hJT x.1 haJ) ⟨1, LevyStochCalc.Brownian.Ito.abs_cellWeight_le_one σ c x.1 x.2⟩
      (LevyStochCalc.Brownian.Ito.measurable_cellWeight σ c x.1 x.2 (hcell x.1 haJ x.2 hvVs))
      (LevyStochCalc.Brownian.Ito.stronglyMeasurable_cellWeight σ c x.1 x.2 (hcell x.1 haJ x.2 hvVs))
      (hmK x.2) (hpK x.2) (hqK x.2) (hgm x) (hgp x) (hgq x)
    filter_upwards [hpull] with ω hω
    rw [← hω, LevyStochCalc.Brownian.Ito.hitInd_mul_cellWeight]
  filter_upwards [hae, hcells] with ω h1 h2
  refine (congrFun hcongr ω).trans (h1.trans ?_)
  exact Finset.sum_congr rfl h2
end CellIntegral

section SimpleShift

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

end SimpleShift

section CellFromStoppingTime

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {α : Type*}

end CellFromStoppingTime

end LevyStochCalc.Brownian.Ito


