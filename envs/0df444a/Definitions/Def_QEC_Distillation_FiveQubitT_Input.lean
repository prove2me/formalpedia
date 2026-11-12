-- Prove2me | Definitions.Def_QEC_Distillation_FiveQubitT_Input
-- name    : QEC_Distillation_FiveQubitT_Input
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T14:19:05.521679+00:00
-- url     : https://prove2.me/theorems/1575c15c-3b80-47ce-b857-de90284de62d
-- title:
--   Input
-- statement:
--   Definitions and structural lemmas for Input, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_projectionSquaredOverlap_nonneg
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tDirectionFidelity_mem_Icc
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tFidelity_mem_Icc
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tProjector_isSymmetricProjection
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_scale_complete_of_adjoint_square_sum
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
open scoped BigOperators
abbrev tZeroDirection : TDirection := tReference
def tOneDirection : TDirection :=
  ⟨fun _ => .neg, by intro i; simp⟩
noncomputable def tZero : DensityOperator QubitSpace :=
  tMagicStateOfDirection tZeroDirection
noncomputable def tOne : DensityOperator QubitSpace :=
  tMagicStateOfDirection tOneDirection
noncomputable def tInputComponent : Fin 2 → DensityOperator QubitSpace
  | 0 => tZero
  | 1 => tOne
def tInputWeight (epsilon : Real) : Fin 2 → Real
  | 0 => 1 - epsilon
  | 1 => epsilon
noncomputable def tRawInputBranch (epsilon : Real) (word : Fin 2) :
    Operator QubitSpace :=
  (tInputWeight epsilon word : Complex) • (tInputComponent word).toOperator
noncomputable def tInputConditional (epsilon : Real) (word : Fin 2)
    (_hpositive : 0 < tInputWeight epsilon word) : DensityOperator QubitSpace :=
  tInputComponent word
theorem tInputWeight_nonneg (epsilon : Real) (hzero : 0 ≤ epsilon)
    (hone : epsilon ≤ 1) (word : Fin 2) : 0 ≤ tInputWeight epsilon word := by
  fin_cases word <;> simp [tInputWeight, hzero, sub_nonneg.mpr hone]
theorem tInputWeight_sum (epsilon : Real) :
    ∑ word : Fin 2, tInputWeight epsilon word = 1 := by
  simp [tInputWeight]
noncomputable def tDiagonalInput (epsilon : Real) (hzero : 0 ≤ epsilon)
    (hone : epsilon ≤ 1) : DensityOperator QubitSpace :=
  DensityOperator.convexCombination Finset.univ (tInputWeight epsilon)
    tInputComponent
    (by
      intro word _hword
      exact tInputWeight_nonneg epsilon hzero hone word)
    (by simpa using tInputWeight_sum epsilon)
theorem tZero_tOne_projector_sum :
    tProjector tZeroDirection + tProjector tOneDirection = 1 := by
  simp [tProjector, tZeroDirection, tOneDirection, tReference,
    tBlochOfDirection, signedCoordinateValue, blochProjector, blochOperator]
  module
def tInputSquaredOverlap (rho : DensityOperator QubitSpace) : Real :=
  projectionSquaredOverlap (tProjector tZeroDirection) rho
def tInputFidelity (rho : DensityOperator QubitSpace) : Real :=
  tDirectionFidelity rho tZeroDirection
def tInputError (rho : DensityOperator QubitSpace) : Real :=
  1 - tInputSquaredOverlap rho
theorem tDirectionSquaredOverlap_eq_tDirectionFidelity_sq
    (rho : DensityOperator QubitSpace) (d : TDirection) :
    projectionSquaredOverlap (tProjector d) rho =
      tDirectionFidelity rho d ^ 2 := by
  unfold tDirectionFidelity projectionFidelity
  rw [Real.sq_sqrt]
  exact projectionSquaredOverlap_nonneg (tProjector d) rho
    (tProjector_isSymmetricProjection d)
theorem tDirectionSquaredOverlap_zero_add_one
    (rho : DensityOperator QubitSpace) :
    projectionSquaredOverlap (tProjector tZeroDirection) rho +
      projectionSquaredOverlap (tProjector tOneDirection) rho = 1 := by
  unfold projectionSquaredOverlap
  rw [← Complex.add_re, ← map_add, ← add_mul,
    tZero_tOne_projector_sum, one_mul, rho.trace_one]
  norm_num
theorem tFidelity_sq_ge_half (rho : DensityOperator QubitSpace) :
    (1 / 2 : Real) ≤ tFidelity rho ^ 2 := by
  have hsum := tDirectionSquaredOverlap_zero_add_one rho
  rw [tDirectionSquaredOverlap_eq_tDirectionFidelity_sq,
    tDirectionSquaredOverlap_eq_tDirectionFidelity_sq] at hsum
  have hzero_nonneg := (tDirectionFidelity_mem_Icc rho tZeroDirection).1
  have hone_nonneg := (tDirectionFidelity_mem_Icc rho tOneDirection).1
  have hmax_nonneg := (tFidelity_mem_Icc rho).1
  have hzero_le : tDirectionFidelity rho tZeroDirection ≤ tFidelity rho := by
    unfold tFidelity
    exact Finset.le_sup' (tDirectionFidelity rho)
      (Finset.mem_univ tZeroDirection)
  have hone_le : tDirectionFidelity rho tOneDirection ≤ tFidelity rho := by
    unfold tFidelity
    exact Finset.le_sup' (tDirectionFidelity rho)
      (Finset.mem_univ tOneDirection)
  have hzero_sq : tDirectionFidelity rho tZeroDirection ^ 2 ≤
      tFidelity rho ^ 2 := by nlinarith
  have hone_sq : tDirectionFidelity rho tOneDirection ^ 2 ≤
      tFidelity rho ^ 2 := by nlinarith
  nlinarith
def tDiagonalBloch (epsilon : Real) : PauliAxis → Real :=
  fun _ => (1 - 2 * epsilon) * (Real.sqrt 3)⁻¹
noncomputable def tCycleTransport : UnitaryTransport QubitSpace QubitSpace :=
  hadamardTransport.trans phaseTransport
noncomputable def tTwirlUnitary : Fin 3 → UnitaryTransport QubitSpace QubitSpace
  | 0 => UnitaryTransport.identity QubitSpace
  | 1 => tCycleTransport
  | 2 => tCycleTransport.trans tCycleTransport
def tTwirlWeight (_ : Fin 3) : Real := 1 / 3
theorem tTwirlWeight_nonneg (i : Fin 3) : 0 ≤ tTwirlWeight i := by
  norm_num [tTwirlWeight]
theorem tTwirlWeight_sum : ∑ i : Fin 3, tTwirlWeight i = 1 := by
  norm_num [tTwirlWeight]
theorem tTwirlUnitary_adjoint_comp (i : Fin 3) :
    (LinearMap.adjoint (tTwirlUnitary i).toLinearEquiv.toLinearMap).comp
      (tTwirlUnitary i).toLinearEquiv.toLinearMap = 1 := by
  rw [(tTwirlUnitary i).adjoint_toLinearMap]
  apply LinearMap.ext
  intro x
  change (tTwirlUnitary i).toLinearEquiv.symm ((tTwirlUnitary i).toLinearEquiv x) = x
  exact (tTwirlUnitary i).toLinearEquiv.symm_apply_apply x
noncomputable def tTwirlAmplitude : Complex := (Real.sqrt 3 : Complex)⁻¹
theorem tTwirlAmplitude_sq :
    star tTwirlAmplitude * tTwirlAmplitude = (1 / 3 : Complex) := by
  unfold tTwirlAmplitude
  have hneReal : Real.sqrt 3 ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hne : (Real.sqrt 3 : Complex) ≠ 0 := by
    exact_mod_cast hneReal
  have hsqReal : Real.sqrt 3 * Real.sqrt 3 = 3 := by
    exact Real.mul_self_sqrt (by norm_num)
  have hsq : (Real.sqrt 3 : Complex) * (Real.sqrt 3 : Complex) = 3 := by
    exact_mod_cast hsqReal
  rw [RCLike.star_def, map_inv₀ (starRingEnd ℂ), Complex.conj_ofReal]
  field_simp [hne]
  rw [pow_two, hsq]
noncomputable def tTwirlKrausUnscaled :
    FiniteKrausFamily (Fin 3) QubitSpace QubitSpace where
  operator i := (tTwirlUnitary i).toLinearEquiv.toLinearMap
noncomputable def tTwirlKraus : FiniteKrausFamily (Fin 3) QubitSpace QubitSpace :=
  tTwirlKrausUnscaled.scale (fun _ => tTwirlAmplitude)
theorem tTwirlKraus_complete : tTwirlKraus.Complete := by
  apply FiniteKrausFamily.scale_complete_of_adjoint_square_sum
  calc
    (∑ i : Fin 3,
        (star tTwirlAmplitude * tTwirlAmplitude) •
          ((LinearMap.adjoint (tTwirlKrausUnscaled.operator i)).comp
            (tTwirlKrausUnscaled.operator i))) =
        ∑ _i : Fin 3, (1 / 3 : Complex) • (1 : Operator QubitSpace) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [tTwirlAmplitude_sq]
          exact congrArg (fun T : Operator QubitSpace => (1 / 3 : Complex) • T)
            (tTwirlUnitary_adjoint_comp i)
    _ = 1 := by
      rw [Fin.sum_univ_three]
      module
noncomputable def tTwirlChannel : QuantumChannel QubitSpace QubitSpace :=
  tTwirlKraus.toQuantumChannel tTwirlKraus_complete
noncomputable def tTwirl (rho : DensityOperator QubitSpace) :
    DensityOperator QubitSpace :=
  DensityOperator.convexCombination Finset.univ tTwirlWeight
    (fun i => (tTwirlUnitary i).conjDensity rho)
    (by
      intro i _hi
      exact tTwirlWeight_nonneg i)
    (by simpa using tTwirlWeight_sum)
def tHadamardBlochAction (r : PauliAxis → Real) : PauliAxis → Real
  | .x => r .z
  | .y => -r .y
  | .z => r .x
def tPhaseBlochAction (r : PauliAxis → Real) : PauliAxis → Real
  | .x => -r .y
  | .y => r .x
  | .z => r .z
def tCycleBlochAction (r : PauliAxis → Real) : PauliAxis → Real
  | .x => r .y
  | .y => r .z
  | .z => r .x
def tTwirlBloch (r : PauliAxis → Real) : PauliAxis → Real :=
  fun _ => (r .x + r .y + r .z) / 3
def tHStep (d : TDirection) : TDirection :=
  hadamardClifford • d
def tSStep (d : TDirection) : TDirection :=
  phaseClifford • d
noncomputable def tCanonicalizerCandidate : Fin 8 →
    UnitaryTransport QubitSpace QubitSpace
  | 0 => ((phaseTransport.trans hadamardTransport).trans phaseTransport).trans
      (phaseTransport.trans hadamardTransport)
  | 1 => phaseTransport.trans hadamardTransport
  | 2 => ((((hadamardTransport.trans phaseTransport).trans hadamardTransport).trans
      phaseTransport).trans phaseTransport).trans hadamardTransport
  | 3 => (phaseTransport.trans phaseTransport).trans hadamardTransport
  | 4 => ((hadamardTransport.trans phaseTransport).trans phaseTransport).trans
      hadamardTransport
  | 5 => hadamardTransport
  | 6 => (hadamardTransport.trans phaseTransport).trans hadamardTransport
  | 7 => UnitaryTransport.identity QubitSpace
def tCanonicalizerTarget : Fin 8 → TDirection → TDirection
  | 0 => fun d => tHStep (tSStep (tSStep (tHStep (tSStep d))))
  | 1 => fun d => tHStep (tSStep d)
  | 2 => fun d => tHStep (tSStep (tSStep (tHStep (tSStep (tHStep d)))))
  | 3 => fun d => tHStep (tSStep (tSStep d))
  | 4 => fun d => tHStep (tSStep (tSStep (tHStep d)))
  | 5 => fun d => tHStep d
  | 6 => fun d => tHStep (tSStep (tHStep d))
  | 7 => fun d => d
theorem tCanonicalizerCandidate_complete (d : TDirection) :
    ∃ i : Fin 8, tCanonicalizerTarget i d = tZeroDirection := by
  revert d
  decide +kernel
noncomputable def tCanonicalizerIndex (d : TDirection) : Fin 8 :=
  Classical.choose (tCanonicalizerCandidate_complete d)
noncomputable def tCanonicalizer (d : TDirection) :
    UnitaryTransport QubitSpace QubitSpace :=
  tCanonicalizerCandidate (tCanonicalizerIndex d)
noncomputable def tCanonicalizedInput (rho : DensityOperator QubitSpace) :
    DensityOperator QubitSpace :=
  (tCanonicalizer (tMaximizingDirection rho)).conjDensity rho
theorem tCanonicalizedInput_error_mem_Icc_half
    (rho : DensityOperator QubitSpace) :
    1 - tFidelity rho ^ 2 ∈ Set.Icc (0 : Real) (1 / 2) := by
  have hF := tFidelity_mem_Icc rho
  have hhalf := tFidelity_sq_ge_half rho
  constructor
  · nlinarith [mul_nonneg hF.1 (sub_nonneg.mpr hF.2)]
  · nlinarith
end BK05T
end Distillation
end QEC


