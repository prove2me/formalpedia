-- Prove2me | Definitions.Def_SourceProof_92f1c4f0edeefcc7ea434347
-- name    : SourceProof_92f1c4f0edeefcc7ea434347
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:11:24.939426+00:00
-- url     : https://prove2.me/theorems/b27274ea-de4d-4646-add2-f8f8d07d8e6e
-- title:
--   LevyStochCalc source module: SourceProof_92f1c4f0edeefcc7ea434347
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.exists_picardOutput` comes from the `LevyStochCalc.BSDEJ.PicardStep` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardStep_F000
import Definitions.Def_LevyStochCalc_BSDEJ_PicardStep_F001
import Definitions.Def_SourceProof_328d6eb72effc016d76dc016
import Definitions.Def_SourceProof_846c5a27154f5e7706e6988e
import Definitions.Def_SourceProof_86eed58355e5baf43a1330aa
import Definitions.Def_SourceProof_8a730e00388641e5c85f4c10
import Definitions.Def_SourceProof_9ba9941dfe7d03e124bfe576
import Definitions.Def_SourceProof_cf0436ca36261036186bd5e0

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# One Picard step of a backward equation with jumps

The Picard map of a backward equation with jumps sends a triple `(Y', Z', U')` to the triple
solving the equation whose generator is frozen along the input, that is to the martingale
representation of the terminal datum `ξ + ∫_0^T b_s ds` for `b = f(·, Y', Z', U')`.
`PicardOutput` is the predicate satisfied by the output triple: the fields of `SolvesBSDEJ` with
the drift integral taken along the input triple, together with the terminal value of `Y` and its
finite `S²` seminorm. A fixed point of the map, that is a `PicardOutput` whose input and output
triples agree, solves the backward equation.

The output is built from the martingale representation of the centred terminal datum
(`exists_picard_integrands_of_rightCont`), the everywhere-càdlàg versions of the two stochastic
legs (`exists_cadlag_brownianLeg`, `exists_cadlag_poissonLeg`) and the primitive of the drift
(`driftLeg`), as `Y_t = c + M^W_t + M^N_t − ∫_0^t b_s ds` with `c` the mean of the terminal
datum.

## Main definitions

* `LevyStochCalc.BSDEJ.Solves.PicardOutput` — the output triple of one Picard step.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.PicardOutput.toSolvesBSDEJ` — a fixed point of the Picard step
  solves the backward equation.
* `LevyStochCalc.BSDEJ.Solves.measurable_biSup_sq_of_rightContinuous` — the squared running
  supremum of a right-continuous process with measurable slices is measurable.
* `LevyStochCalc.BSDEJ.Solves.exists_picardOutput` — the Picard step has an output triple.

## References

* Tang–Li, *Necessary conditions for optimal control of stochastic systems with random jumps*,
  SIAM J. Control Optim. 32 (1994), §2.
* Barles–Buckdahn–Pardoux, *BSDEs and integral-partial differential equations*, Stochastics 60
  (1997), §2.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### The output of a Picard step -/

/-! ### Measurability of the running supremum -/

/-! ### The Picard step -/


theorem _root_.Prove2MeSourceProof.h_92f1c4f0edeefcc7ea434347 (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    (f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ) {T : ℝ} (hT : 0 < T) {ξ : Ω → ℝ}
    (hξ2 : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[augJoint D T] ξ P)
    (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin d → ℝ)) (U' : ℝ → Ω → E → ℝ)
    {b : Ω → ℝ → ℝ} (hbm : Measurable (Function.uncurry b))
    (hbp : Probability.ProgressivelyMeasurable (augJoint D).rightCont b)
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hb : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b p.1 p.2 = f p.2 (Y' p.2 p.1) (Z' p.2 p.1) (U' p.2 p.1)) :
    ∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ),
      PicardOutput D f ξ T Y' Z' U' Y Z U := by
  classical
  obtain ⟨Z, U, hZm, hZp, hZv, hZq, hUm, hUp, hUv, hUq, hrep⟩ :=
    _root_.Prove2MeSourceProof.h_86eed58355e5baf43a1330aa D hT hξ2 hξm hbm hbp hbz hbq
  obtain ⟨MW, hWad, hWme, hWae, hWcd, -, -, hWsup⟩ :=
    LevyStochCalc.BSDEJ.Solves.exists_cadlag_brownianLeg D T hT.le Z hZm hZp hZv hZq
  obtain ⟨MN, hNad, hNme, hNae, hNcd, -, -, hNsup⟩ :=
    LevyStochCalc.BSDEJ.Solves.exists_cadlag_poissonLeg D T hT.le U hUm hUp hUv hUq
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∫ ω, LevyStochCalc.BSDEJ.Solves.terminalDatum ξ b T ω ∂P := ⟨_, rfl⟩
  have hcen : ∀ ω : Ω, LevyStochCalc.BSDEJ.Solves.centred P (LevyStochCalc.BSDEJ.Solves.terminalDatum ξ b T) ω
      = ξ ω + (∫ s in Set.Icc (0 : ℝ) T, b ω s) - c := by
    intro ω
    rw [hc]
    rfl
  have hAme : Measurable (Function.uncurry (LevyStochCalc.BSDEJ.Solves.driftLeg b T)) := _root_.Prove2MeSourceProof.h_846c5a27154f5e7706e6988e hbm
  have hAsl : ∀ t : ℝ, Measurable (LevyStochCalc.BSDEJ.Solves.driftLeg b T t) := fun t =>
    hAme.comp (measurable_const.prodMk measurable_id)
  have hAct : ∀ ω : Ω, Continuous fun t => LevyStochCalc.BSDEJ.Solves.driftLeg b T t ω := _root_.Prove2MeSourceProof.h_cf0436ca36261036186bd5e0 hbz
  have hWsl : ∀ t : ℝ, Measurable (MW t) := fun t =>
    hWme.comp (measurable_const.prodMk measurable_id)
  have hNsl : ∀ t : ℝ, Measurable (MN t) := fun t =>
    hNme.comp (measurable_const.prodMk measurable_id)
  have hWam : AEMeasurable
      (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖MW t ω‖₊ : ℝ≥0∞) ^ 2) P :=
    (LevyStochCalc.BSDEJ.Solves.measurable_biSup_sq_of_rightContinuous hT.le hWsl fun ω t => (hWcd ω t).1).aemeasurable
  have hNam : AEMeasurable
      (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖MN t ω‖₊ : ℝ≥0∞) ^ 2) P :=
    (LevyStochCalc.BSDEJ.Solves.measurable_biSup_sq_of_rightContinuous hT.le hNsl fun ω t => (hNcd ω t).1).aemeasurable
  have hAam : AEMeasurable
      (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖-LevyStochCalc.BSDEJ.Solves.driftLeg b T t ω‖₊ : ℝ≥0∞) ^ 2) P :=
    (LevyStochCalc.BSDEJ.Solves.measurable_biSup_sq_of_rightContinuous (M := fun t ω => -LevyStochCalc.BSDEJ.Solves.driftLeg b T t ω) hT.le
      (fun t => (hAsl t).neg)
      fun ω t => (((hAct ω).neg).tendsto t).mono_left nhdsWithin_le_nhds).aemeasurable
  have hAsup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
      (‖-LevyStochCalc.BSDEJ.Solves.driftLeg b T t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by
    simpa only [nnnorm_neg] using _root_.Prove2MeSourceProof.h_328d6eb72effc016d76dc016 (P := P) hbm hbq
  refine ⟨fun t ω => c + MW t ω + MN t ω - LevyStochCalc.BSDEJ.Solves.driftLeg b T t ω, Z, U,
    { Z_meas := hZm, Z_prog := hZp, Z_vanish := hZv, Z_sq := hZq, U_meas := hUm,
      U_prog := hUp, U_vanish := hUv, U_sq := hUq, Y_meas := ?_, Y_adapted := ?_,
      Y_cadlag := ?_, eqn := ?_, Y_terminal := ?_, Y_sup := ?_ }⟩
  · exact ((measurable_const.add hWme).add hNme).sub hAme
  · exact fun t => ((measurable_const.add (hWad t)).add (hNad t)).sub
      (LevyStochCalc.BSDEJ.Solves.adapted_driftLeg_rightCont_of_rightCont hbm hbp hbz hbq
        (fun _s hs h0 => D.measurableSet_augFiltration_of_null hs h0) t)
  · intro ω t
    obtain ⟨hWr, L₁, hWl⟩ := hWcd ω t
    obtain ⟨hNr, L₂, hNl⟩ := hNcd ω t
    have hAr : Tendsto (fun s => LevyStochCalc.BSDEJ.Solves.driftLeg b T s ω) (𝓝[>] t) (𝓝 (LevyStochCalc.BSDEJ.Solves.driftLeg b T t ω)) :=
      ((hAct ω).tendsto t).mono_left nhdsWithin_le_nhds
    have hAl : Tendsto (fun s => LevyStochCalc.BSDEJ.Solves.driftLeg b T s ω) (𝓝[<] t) (𝓝 (LevyStochCalc.BSDEJ.Solves.driftLeg b T t ω)) :=
      ((hAct ω).tendsto t).mono_left nhdsWithin_le_nhds
    exact ⟨((tendsto_const_nhds.add hWr).add hNr).sub hAr,
      ⟨c + L₁ + L₂ - LevyStochCalc.BSDEJ.Solves.driftLeg b T t ω, ((tendsto_const_nhds.add hWl).add hNl).sub hAl⟩⟩
  · intro t ht
    have hbf : ∀ᵐ ω ∂P, ∫ s in Set.Icc t T, b ω s
        = ∫ s in Set.Icc t T, f s (Y' s ω) (Z' s ω) (U' s ω) := by
      filter_upwards [Measure.ae_ae_of_ae_prod hb] with ω hω
      exact integral_congr_ae
        (ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc ht.1 le_rfl) hω)
    filter_upwards [hrep, hWae t, hNae t, LevyStochCalc.BSDEJ.Solves.driftLeg_ae_eq hbm hbq T,
      _root_.Prove2MeSourceProof.h_8a730e00388641e5c85f4c10 hbm hbq ht.1 ht.2, hbf] with ω h1 h2 h3 h4 h5 h6
    rw [hcen ω] at h1
    rw [h2, h3]
    linarith [h1, h4, h5, h6]
  · filter_upwards [hrep, hWae T, hNae T, LevyStochCalc.BSDEJ.Solves.driftLeg_ae_eq hbm hbq T] with ω h1 h2 h3 h4
    rw [hcen ω] at h1
    rw [h2, h3, h4]
    linarith [h1]
  · have hstep := _root_.Prove2MeSourceProof.h_9ba9941dfe7d03e124bfe576 (μ := P) c MW MN
      (fun t ω => -LevyStochCalc.BSDEJ.Solves.driftLeg b T t ω) T hWam hNam hAam hWsup hNsup hAsup
    simpa only [← sub_eq_add_neg] using hstep
end LevyStochCalc.BSDEJ.Solves


