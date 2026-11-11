-- Prove2me | Definitions.Def_OAIQ240Bp018
-- name    : OAIQ240Bp018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:43:38.39503+00:00
-- url     : https://prove2.me/theorems/b4dcb032-ed74-4867-af82-2d7816db1687
-- title:
--   Definitions bundle OAIQ240Bp018 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 64 declarations of OpenAI's Lean: 60 definitions and 4 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.azInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.azInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst8`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst7`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compactJPerturbation`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedLinearized`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedMarkCorrection`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedMarkHolder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedZeroOrder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.constantZeroOrder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChart`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst10`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst11`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst13`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst14`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst16`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst7`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst8`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst9`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst10`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst11`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst13`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst15`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst16`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst17`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst5` and 20 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`BallPacking_Energy_CircularEnergy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Energy/CircularEnergy.lean), [`BallPacking_Energy_ResidualEnergy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Energy/ResidualEnergy.lean), [`BallPacking_Fredholm_FrameFredholm`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FrameFredholm.lean), [`BallPacking_Fredholm_FreeLinearization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FreeLinearization.lean), [`BallPacking_Fredholm_PointwiseMarkedCR`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/PointwiseMarkedCR.lean), [`BallPacking_Fredholm_TranslationContinuity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean).
--
--   **Imports.** It imports the published bundle `Def_BallPacking`; the bundles `OAIQ240Bp014` and `OAIQ240Bp015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ240Bp020` and `OAIQ240Bp021`; the statements `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_completedZeroOrder_compact`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedZeroOrder_compact_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_completed_markedCurve_contDiff`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completed_markedCurve_contDiff_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_freeChart_hasFDerivAt_eval`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChart_hasFDerivAt_eval_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChart_translation_zero_near_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_line_local_energy_of_slope`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_line_local_energy_of_slope_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_normalized_line_energy` and `OAI.HigherDimensionalBallPacking.Rigidity.exact_normalized_line_energy_bp240`; the proofs of `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_completedZeroOrder_compact`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedZeroOrder_compact_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_freeChart_hasFDerivAt_eval`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChart_hasFDerivAt_eval_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChart_translation_zero_near_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_normalized_line_energy` and `OAI.HigherDimensionalBallPacking.Rigidity.exact_normalized_line_energy_bp240`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp014
import Definitions.Def_OAIQ240Bp015

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FrameFredholm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance markedChartInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedChartInst2 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedChartInst3 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedChartInst4 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst6
local instance markedChartInst7 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance markedChartInst8 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance

local instance markedChartInst13_r663c9d_1 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markedChartInst14_r663c9d_1 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
variable {P : E → E →L[ℝ] E} (hP : BoundedCThree P) (b : ContDiffBump (0:ℂ))

local instance markedChartInst9 : NormedAddCommGroup (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance markedChartInst10 : NormedSpace ℝ (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance markedChartInst11 : NormedAddCommGroup (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance markedChartInst12 : NormedSpace ℝ (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_PointwiseMarkedCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {K : Set ℂ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst4
local instance ptCRInst5_r663c9d_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance ptCRInst6_r663c9d_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst11
def pointMarkedCR (J : E → E →L[ℝ] E) (p q : E) (u : COne ℂ E) (z : ℂ)
    (h : markedModel (E := E) K) : E :=
  fderiv ℝ (markedCurve p q (u+h.val)) z Complex.I -
    J (markedCurve p q (u+h.val) z) (fderiv ℝ (markedCurve p q (u+h.val)) z 1)


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst4
local instance compLinInst5 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance compLinInst6_r663c9d_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance compLinInst7 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst1
local instance compLinInst8_r663c9d_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance compLinInst9_r663c9d_1 : NormedAddCommGroup (HMap ℂ (End n)) := inferInstance
local instance compLinInst10_r663c9d_1 : NormedSpace ℝ (HMap ℂ (End n)) := inferInstance
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (p q : Phase n) (u : COne ℂ (Phase n))

variable {K : Set ℂ} (hK : IsCompact K) (he : ∀ z ∉ K, B < ‖markedCurve p q u z‖)

local instance compLinInst11_r663c9d_1 : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance compLinInst12_r663c9d_1 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance compLinInst13_r663c9d_1 : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance compLinInst14_r663c9d_1 : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
include he in
lemma completedQ_zero_outside : ∀ z ∉ K, valueCLM _ (completedQ hJ hstd p q u) z=0 := by
  intro z hz
  apply ContinuousLinearMap.ext
  intro v
  have hd := fderiv_standard_outside hstd (he z hz)
  calc
    _ = fderiv ℝ J (markedCurve p q u z) v (fderiv ℝ (markedCurve p q u) z 1) :=
      completedQ_value hJ hstd p q u z v
    _ = 0 := by rw [hd]; rfl

variable (b : ContDiffBump (0:ℂ)) (hb : K ⊆ Metric.closedBall (0:ℂ) b.rIn)

def completedMarkHolder : HMap ℂ (End n) :=
  jetValueCLM _ (completedStructureJet hJ hstd p q u)-const _ (standardJ n) +
    bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.compL ℝ (Phase n) (Phase n) (Phase n))
      (completedQ hJ hstd p q u)
      (mapCLM _ (ContinuousLinearMap.lsmul ℝ ℂ) (jetValueCLM _ (cutoffCoordinate b)))

include he hb in
lemma completedMarkHolder_value (z : ℂ) (v : Phase n) :
    valueCLM _ (completedMarkHolder hJ hstd p q u b) z v =
      J (markedCurve p q u z) v - Complex.I • v +
        fderiv ℝ J (markedCurve p q u z) (z • v) (fderiv ℝ (markedCurve p q u) z 1) := by
  have hcut : valueCLM _ (completedQ hJ hstd p q u) z ((b z • z) • v) =
      valueCLM _ (completedQ hJ hstd p q u) z (z • v) := by
    by_cases hz : z∈K
    · rw [b.one_of_mem_closedBall (hb hz),one_smul]
    · have hzero := completedQ_zero_outside hJ hstd p q u he z hz
      rw [hzero]; rfl
  change J (markedCurve p q u z) v-Complex.I • v +
    valueCLM _ (completedQ hJ hstd p q u) z ((b z • z) • v) = _
  exact congrArg (fun w : Phase n => J (markedCurve p q u z) v-Complex.I • v+w)
    (hcut.trans (completedQ_value hJ hstd p q u z (z • v)))

include he hb in
lemma completedMarkHolder_zero_outside : ∀ z ∉ K, valueCLM _ (completedMarkHolder hJ hstd p q u b) z=0 := by
  intro z hz
  apply ContinuousLinearMap.ext
  intro v
  have hj := hstd _ (he z hz)
  have hd := fderiv_standard_outside hstd (he z hz)
  calc
    _ = J (markedCurve p q u z) v-Complex.I • v +
        fderiv ℝ J (markedCurve p q u z) (z • v) (fderiv ℝ (markedCurve p q u) z 1) :=
      completedMarkHolder_value hJ hstd p q u he b hb z v
    _ = 0 := by rw [hj,hd]; change Complex.I • v-Complex.I • v+0=0; abel

def completedZeroOrder : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
  markedZeroOrder (completedQ hJ hstd p q u) (completedQ_zero_outside hJ hstd p q u he)

def completedMarkCorrection : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
  markedFiniteCorrection (completedMarkHolder hJ hstd p q u b)
    (completedMarkHolder_zero_outside hJ hstd p q u he b hb)

def completedLinearized : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
  completedPrincipal hJ hstd p q u he +
    (-completedZeroOrder hJ hstd p q u he + completedMarkCorrection hJ hstd p q u he b hb)


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst4
local instance freeFredInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
variable {K : Set ℂ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst6
local instance freeFredInst7 : NormedAddCommGroup (freeModel (E := E) K) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst8
local instance freeFredInst9 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance freeFredInst10 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance freeFredInst11 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst12
local instance freeFredInst13 : AddCommGroup (freeModel (E := E) K) := (freeFredInst7 (E := E) (K := K)).toAddCommGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst14
local instance freeFredInst15 : AddCommGroup (markedModel (E := E) K) := (freeFredInst9 (E := E) (K := K)).toAddCommGroup
local instance freeFredInst16 : Module ℝ (markedModel (E := E) K) := (freeFredInst10 (E := E) (K := K)).toModule
local instance freeFredInst17 : AddCommGroup (supportedHolder (E := E) K) := (freeFredInst11 (E := E) (K := K)).toAddCommGroup

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst18
variable (A C : HMap ℂ (E →L[ℝ] E))
  (hA : ∀ z ∉ K, valueCLM _ A z = complexI (E := E))
  (hC : ∀ z ∉ K, valueCLM _ C z = 0)

def constantZeroOrder : E →L[ℝ] supportedHolder (E := E) K :=
  ((holderCoefficientAction C).comp constHolderCLM).codRestrict _ (fun c => by
    apply (mem_supportedHolder _ _).mpr
    intro z hz
    change valueCLM _ C z c=0
    rw [hC z hz,zero_apply])

def freeLinearized : freeModel (E := E) K →L[ℝ] supportedHolder (E := E) K :=
  freePrincipal A hA-freeZeroOrder C hC


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance chartDerInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance chartDerInst2 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance chartDerInst3 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance chartDerInst4 : NormedSpace ℝ (HMap ℂ E) := inferInstance
variable {K : Set ℂ}
local instance chartDerInst5 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance chartDerInst6 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance

variable {n : ℕ}
local instance chartDerInst7_r663c9d_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance chartDerInst8 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

def compactJPerturbation (J : Phase n → End n) (x : Phase n) : End n := J x-standardJ n

lemma compactJPerturbation_compact {J : Phase n → End n} {B : ℝ}
    (hstd : ∀ x, B < ‖x‖ → J x = standardJ n) : HasCompactSupport (compactJPerturbation J) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Phase n) B)
  intro x hx
  by_contra hxB
  apply hx
  change J x-standardJ n=0
  rw [hstd x (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hxB),sub_self]


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst2
local instance freeChartInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance freeChartInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance freeChartInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance freeChartInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
variable {J : E → E →L[ℝ] E} (hJ : BoundedCThree J) (b : ContDiffBump (0:ℂ)) (p a : E)
local instance freeChartInst7 : NormedAddCommGroup (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance freeChartInst8 : NormedSpace ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance freeChartInst9 : NormedAddCommGroup (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance freeChartInst10 : NormedSpace ℝ (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance freeChartInst11 : AddCommGroup (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (freeChartInst7 (E := E) b).toAddCommGroup
local instance freeChartInst12_r663c9d_1 : Module ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (freeChartInst8 (E := E) b).toModule
local instance freeChartInst13 : TopologicalSpace (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (freeChartInst7 (E := E) b).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
local instance freeChartInst14 : AddCommGroup (COne ℂ E) := (freeChartInst3 (E := E)).toAddCommGroup
local instance freeChartInst15_r663c9d_1 : Module ℝ (COne ℂ E) := (freeChartInst4 (E := E)).toModule
local instance freeChartInst16 : TopologicalSpace (COne ℂ E) := (freeChartInst3 (E := E)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
variable (u : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))

def freeChart (v : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) :
    supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut) :=
  freeCR (E := E) (K := Metric.closedBall (0:ℂ) b.rOut) (u+v) - supportedSourceCutoff b
    (standardJetCR (u.val+v.val)-crSection hJ p (complexSlope a) (u.val+v.val))



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FreeLinearization
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HolderCompletion
variable {n : ℕ}
local instance afInst1_r663c9d_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance afInst2_r663c9d_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance afInst3_r663c9d_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance afInst4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance afInst5 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance afInst6 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_TranslationContinuity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
variable {n : ℕ}
local instance srInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup

end
section
variable {n : ℕ}
local instance azInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance azInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Energy_ResidualEnergy
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
open HolderCompletion
variable {n : ℕ}

def dirichletEnergy (v : ℂ → Phase n) (z : Plane) : ℝ :=
  stdDot n (fderiv ℝ (realCurve v) z (1,0)) (fderiv ℝ (realCurve v) z (1,0)) +
  stdDot n (fderiv ℝ (realCurve v) z (0,1)) (fderiv ℝ (realCurve v) z (0,1))


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}


local instance caInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance caInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Energy_CircularEnergy
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

def circleTrace (u : ℂ → Phase n) (r θ : ℝ) : Phase n := realCurve u (circlePlane r θ)


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

def radialCurveEnergy (u : ℂ → Phase n) (A : ℝ) : ℝ :=
  ∫ z : Plane, sourceRadialCutoff A z*dirichletEnergy u z



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end


