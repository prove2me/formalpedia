-- Prove2me | Definitions.Def_QEC_Distillation_PrimeQuditProtocol_VanishingOverhead
-- name    : QEC_Distillation_PrimeQuditProtocol_VanishingOverhead
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T01:26:49.7532+00:00
-- url     : https://prove2.me/theorems/d1a32eb9-4b32-4c5f-8619-712c4bc1336b
-- title:
--   Vanishing Overhead
-- statement:
--   Definitions and structural lemmas for Vanishing Overhead, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/VanishingOverhead.lean

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_evaluation_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_reedSolomonCode_product_le_dual
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_shortenedReedSolomonCode_dimension
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_apply
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_childInputSlot
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_kt19Routing_apply
import Theorems.Thm_QEC_Distillation_KT19Protocol_kt19OutputLabelDistribution_sum
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryDistillationRun_successProbability
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_zero
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode
attribute [local simp] QEC.Distillation.DependentBatch.transposeRouting_apply
attribute [local simp] QEC.Distillation.DependentBatch.transposeRouting_childInputSlot
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.KT19Protocol.KT19DistillationFamily.kt19Routing_apply
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.binaryDistillationRun_successProbability
attribute [local simp] QEC.Semantics.FiniteInstrument.branchOperator_zero
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg


set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.KT19VanishingOverhead
open Semantics
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19Protocol
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open Filter Topology
open scoped BigOperators
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
local instance instKT19VanishingOverheadClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
attribute [local instance] QEC.Distillation.KT19VanishingOverhead.instKT19VanishingOverheadClassicalDecidable
universe u
def kt19ExplicitL (p : Nat) : Nat := p / 4
def kt19ExplicitK (p : Nat) : Nat := p / 8
theorem kt19ExplicitParameters_admissible (p : Nat) (hp : Nat.Prime p)
    (hlarge : 32 ≤ p) :
    Admissible p (kt19ExplicitL p) (kt19ExplicitK p) := by
  refine ⟨hp, ?_, ?_, ?_, ?_⟩
  all_goals simp [kt19ExplicitL, kt19ExplicitK] <;> omega
noncomputable def kt19SelectedPunctureEquivFin (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) : SelectedPunctureLocation p k ≃ Fin k := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  refine
    { toFun := fun point => ⟨point.1.val, (Finset.mem_filter.mp point.2).2⟩
      invFun := fun index => ⟨(index.1 : ZMod p), by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (index.2.trans_le hkp)]
        exact index.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro point
    apply Subtype.ext
    exact ZMod.natCast_zmod_val point.1
  · intro index
    apply Fin.ext
    change ((index.1 : ZMod p).val) = index.1
    exact ZMod.val_natCast_of_lt (index.2.trans_le hkp)
noncomputable def kt19SelectedDeltaWord (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) (index : Fin k) : Word (ZMod p) (SelectedPunctureLocation p k) :=
  fun point => if kt19SelectedPunctureEquivFin p k hkp point = index then 1 else 0
noncomputable def kt19SelectedInterpolation (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) (word : Word (ZMod p) (SelectedPunctureLocation p k)) :
    Polynomial.degreeLT (ZMod p) k := by
  let equivalence := Lagrange.funEquivDegreeLT
    (s := selectedPunctureLocations p k) (v := fun point : ZMod p => point)
    (by
      intro left hleft right hright heq
      exact heq)
  let raw := equivalence.symm word
  refine ⟨raw.1, ?_⟩
  simpa [selectedPunctureLocations_card p k hkp] using raw.2
noncomputable def kt19ExplicitLogicalPolynomial (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) (index : Fin k) : Polynomial (ZMod p) :=
  -(kt19SelectedInterpolation p k hkp (kt19SelectedDeltaWord p k hkp index)).1
noncomputable def kt19SelectedNodalPolynomial (p k : Nat) [Fact p.Prime] :
    Polynomial (ZMod p) :=
  Lagrange.nodal (selectedPunctureLocations p k) (fun point : ZMod p => point)
noncomputable def kt19ExplicitStabilizerPolynomial (p l k : Nat)
    [Fact p.Prime] (index : Fin (l - k)) : Polynomial (ZMod p) :=
  kt19SelectedNodalPolynomial p k * Polynomial.X ^ (index : Nat)
noncomputable def kt19ExplicitLogicalRow (p l k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) :
    Fin k → Word (ZMod p) (KeptPunctureLocation p k) :=
  fun index => restrictKept p k
    (evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp index))
noncomputable def kt19ExplicitStabilizerRow (p l k : Nat) [Fact p.Prime] :
    Fin (l - k) → Word (ZMod p) (KeptPunctureLocation p k) :=
  fun index => restrictKept p k
    (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index))
noncomputable def kt19ExplicitRow (p l k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) :
    Fin k ⊕ Fin (l - k) → Word (ZMod p) (KeptPunctureLocation p k) :=
  Sum.elim (kt19ExplicitLogicalRow p l k hkp) (kt19ExplicitStabilizerRow p l k)
noncomputable def kt19ExplicitRowPolynomial (p l k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) : Fin k ⊕ Fin (l - k) → Polynomial (ZMod p) :=
  Sum.elim (kt19ExplicitLogicalPolynomial p k hkp)
    (kt19ExplicitStabilizerPolynomial p l k)
theorem kt19ExplicitRow_eq_restrictKept_evaluation (p l k : Nat)
    [Fact p.Prime] (hkp : k ≤ p) (index : Fin k ⊕ Fin (l - k)) :
    kt19ExplicitRow p l k hkp index =
      restrictKept p k (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp index)) := by
  rcases index with index | index <;> rfl
theorem kt19ExplicitLogicalPolynomial_degreeLT (p l k : Nat)
    [Fact p.Prime] (hkp : k ≤ p) (hkl : k ≤ l) (index : Fin k) :
    kt19ExplicitLogicalPolynomial p k hkp index ∈ Polynomial.degreeLT (ZMod p) l := by
  apply Submodule.neg_mem
  exact (Polynomial.degreeLT_mono (R := ZMod p) hkl)
    (kt19SelectedInterpolation p k hkp
      (kt19SelectedDeltaWord p k hkp index)).property
theorem kt19ExplicitStabilizerPolynomial_degreeLT (p l k : Nat)
    [Fact p.Prime] (hkp : k ≤ p) (hkl : k ≤ l) (index : Fin (l - k)) :
    kt19ExplicitStabilizerPolynomial p l k index ∈ Polynomial.degreeLT (ZMod p) l := by
  rw [Polynomial.mem_degreeLT]
  calc
    (kt19ExplicitStabilizerPolynomial p l k index).degree ≤
        (kt19SelectedNodalPolynomial p k).degree +
          (Polynomial.X ^ (index : Nat) : Polynomial (ZMod p)).degree :=
      Polynomial.degree_mul_le _ _
    _ = (k : WithBot ℕ) + (index : Nat) := by
      rw [kt19SelectedNodalPolynomial,
        Lagrange.degree_nodal, selectedPunctureLocations_card p k hkp]
      simp
    _ < (l : WithBot ℕ) := by
      exact_mod_cast (show k + (index : Nat) < l by omega)
theorem kt19ExplicitRowPolynomial_degreeLT (p l k : Nat)
    [Fact p.Prime] (hkp : k ≤ p) (hkl : k ≤ l)
    (index : Fin k ⊕ Fin (l - k)) :
    kt19ExplicitRowPolynomial p l k hkp index ∈ Polynomial.degreeLT (ZMod p) l := by
  rcases index with index | index
  · exact kt19ExplicitLogicalPolynomial_degreeLT p l k hkp hkl index
  · exact kt19ExplicitStabilizerPolynomial_degreeLT p l k hkp hkl index
theorem kt19RestrictSelected_evaluation_selectedInterpolation
    (p k : Nat) [Fact p.Prime] (hkp : k ≤ p)
    (word : Word (ZMod p) (SelectedPunctureLocation p k)) :
    restrictSelected p k (evaluationLinearMap p k
      (kt19SelectedInterpolation p k hkp word)) = word := by
  ext point
  change
    ((Lagrange.funEquivDegreeLT
      (s := selectedPunctureLocations p k) (v := fun point : ZMod p => point)
      (by
        intro left hleft right hright heq
        exact heq)).symm word).1.eval point.1 = word point
  exact congrFun ((Lagrange.funEquivDegreeLT
    (s := selectedPunctureLocations p k) (v := fun point : ZMod p => point)
    (by
      intro left hleft right hright heq
      exact heq)).apply_symm_apply word) point
theorem kt19ExplicitLogical_restrictSelected (p l k : Nat)
    [Fact p.Prime] (hkp : k ≤ p) (index : Fin k) :
    restrictSelected p k
      (evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp index)) =
        -(kt19SelectedDeltaWord p k hkp index) := by
  ext point
  simpa [kt19ExplicitLogicalPolynomial, evaluationMap] using
    congrArg Neg.neg
      (congrFun (kt19RestrictSelected_evaluation_selectedInterpolation p k hkp
        (kt19SelectedDeltaWord p k hkp index)) point)
theorem kt19ExplicitStabilizer_restrictSelected_zero (p l k : Nat)
    [Fact p.Prime] (index : Fin (l - k)) :
    restrictSelected p k
      (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index)) = 0 := by
  ext point
  change
    (kt19ExplicitStabilizerPolynomial p l k index).eval point.1 = 0
  rw [kt19ExplicitStabilizerPolynomial, Polynomial.eval_mul,
    kt19SelectedNodalPolynomial,
    Lagrange.eval_nodal_at_node
      (s := selectedPunctureLocations p k)
      (v := fun root : ZMod p => root) (i := point.1) point.2]
  simp
noncomputable def kt19ExplicitCoefficientPolynomial (p l k : Nat)
    [Fact p.Prime] (hkp : k ≤ p) (u : Fin k → ZMod p)
    (h : Fin (l - k) → ZMod p) : Polynomial (ZMod p) :=
  (∑ index : Fin k, u index • kt19ExplicitLogicalPolynomial p k hkp index) +
    ∑ index : Fin (l - k), h index • kt19ExplicitStabilizerPolynomial p l k index
theorem kt19ExplicitCoefficientPolynomial_degreeLT (p l k : Nat)
    [Fact p.Prime] (hkp : k ≤ p) (hkl : k ≤ l)
    (u : Fin k → ZMod p) (h : Fin (l - k) → ZMod p) :
    kt19ExplicitCoefficientPolynomial p l k hkp u h ∈ Polynomial.degreeLT (ZMod p) l := by
  apply Submodule.add_mem
  · exact Submodule.sum_mem (Polynomial.degreeLT (ZMod p) l) fun index _ =>
      Submodule.smul_mem _ _
        (kt19ExplicitLogicalPolynomial_degreeLT p l k hkp hkl index)
  · exact Submodule.sum_mem (Polynomial.degreeLT (ZMod p) l) fun index _ =>
      Submodule.smul_mem _ _
        (kt19ExplicitStabilizerPolynomial_degreeLT p l k hkp hkl index)
theorem kt19ExplicitCoefficient_restrictKept (p l k : Nat)
    [Fact p.Prime] (hkp : k ≤ p) (u : Fin k → ZMod p)
    (h : Fin (l - k) → ZMod p) :
    restrictKept p k (evaluationMap p
      (kt19ExplicitCoefficientPolynomial p l k hkp u h)) =
        (∑ index : Fin k, u index • kt19ExplicitLogicalRow p l k hkp index) +
          ∑ index : Fin (l - k), h index • kt19ExplicitStabilizerRow p l k index := by
  ext point
  simp only [restrictKept_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    kt19ExplicitLogicalRow, kt19ExplicitStabilizerRow, evaluationMap]
  rw [kt19ExplicitCoefficientPolynomial, Polynomial.eval_add,
    Polynomial.eval_finsetSum, Polynomial.eval_finsetSum]
  simp only [Algebra.smul_def, Polynomial.algebraMap_apply,
    Polynomial.eval_C_mul, Algebra.algebraMap_self_apply]
theorem kt19ExplicitCoefficient_eq_zero_of_restrictKept_zero
    (p l k : Nat) [Fact p.Prime] (hkp : k ≤ p) (hkl : k ≤ l)
    (hlength : l ≤ p - k) (u : Fin k → ZMod p)
    (h : Fin (l - k) → ZMod p)
    (hzero : (∑ index : Fin k, u index • kt19ExplicitLogicalRow p l k hkp index) +
      ∑ index : Fin (l - k), h index • kt19ExplicitStabilizerRow p l k index = 0) :
    kt19ExplicitCoefficientPolynomial p l k hkp u h = 0 := by
  have hreduced : restrictKept p k (evaluationMap p
      (kt19ExplicitCoefficientPolynomial p l k hkp u h)) = 0 := by
    rw [kt19ExplicitCoefficient_restrictKept]
    exact hzero
  apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq (keptPunctureLocations p k)
  · exact (Polynomial.mem_degreeLT.mp
      (kt19ExplicitCoefficientPolynomial_degreeLT p l k hkp hkl u h)).trans_le
        (by simpa [keptPunctureLocations_card p k hkp] using hlength)
  · exact WithBot.bot_lt_coe (keptPunctureLocations p k).card
  · intro point hpoint
    have hvalue := congrFun hreduced ⟨point, hpoint⟩
    simpa [evaluationMap] using hvalue
theorem kt19ExplicitCoefficient_restrictSelected (p l k : Nat)
    [Fact p.Prime] (hkp : k ≤ p) (u : Fin k → ZMod p)
    (h : Fin (l - k) → ZMod p) :
    restrictSelected p k (evaluationMap p
      (kt19ExplicitCoefficientPolynomial p l k hkp u h)) =
        ∑ index : Fin k, u index •
          -(kt19SelectedDeltaWord p k hkp index) := by
  ext point
  have hlogical (index : Fin k) :
      (kt19ExplicitLogicalPolynomial p k hkp index).eval point.1 =
        -kt19SelectedDeltaWord p k hkp index point := by
    simpa [evaluationMap] using congrFun
      (kt19ExplicitLogical_restrictSelected p l k hkp index) point
  have hstabilizer (index : Fin (l - k)) :
      (kt19ExplicitStabilizerPolynomial p l k index).eval point.1 = 0 := by
    simpa [evaluationMap] using congrFun
      (kt19ExplicitStabilizer_restrictSelected_zero p l k index) point
  simp only [restrictSelected_apply, Finset.sum_apply, Pi.smul_apply, evaluationMap]
  rw [kt19ExplicitCoefficientPolynomial, Polynomial.eval_add,
    Polynomial.eval_finsetSum, Polynomial.eval_finsetSum]
  simp [Algebra.smul_def, Polynomial.algebraMap_apply,
    Polynomial.eval_C_mul, Algebra.algebraMap_self_apply, hlogical, hstabilizer]
theorem kt19SelectedDelta_coefficients_zero (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) (u : Fin k → ZMod p)
    (hzero : ∑ index : Fin k, u index •
      -(kt19SelectedDeltaWord p k hkp index) = 0) : u = 0 := by
  funext index
  have hpoint := congrFun hzero
    ((kt19SelectedPunctureEquivFin p k hkp).symm index)
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply] at hpoint
  rw [Fintype.sum_eq_single index] at hpoint
  · have hneg : -u index = 0 := by
      simpa [kt19SelectedDeltaWord] using hpoint
    exact neg_eq_zero.mp hneg
  · intro other hne
    have hindexOther : index ≠ other := Ne.symm hne
    simp [kt19SelectedDeltaWord, hindexOther]
theorem kt19ExplicitStabilizerCombination_factor (p l k : Nat)
    [Fact p.Prime] (h : Fin (l - k) → ZMod p) :
    ∑ index : Fin (l - k), h index •
      kt19ExplicitStabilizerPolynomial p l k index =
        kt19SelectedNodalPolynomial p k *
          ∑ index : Fin (l - k), h index • (Polynomial.X ^ (index : Nat)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  simp [kt19ExplicitStabilizerPolynomial, Algebra.smul_def]
  ring
theorem kt19SelectedNodalPolynomial_ne_zero (p k : Nat) [Fact p.Prime] :
    kt19SelectedNodalPolynomial p k ≠ 0 := by
  simpa [kt19SelectedNodalPolynomial] using
    (Lagrange.nodal_monic (s := selectedPunctureLocations p k)
      (v := fun point : ZMod p => point)).ne_zero
theorem kt19MonomialCoefficients_zero (p n : Nat) [Fact p.Prime]
    (h : Fin n → ZMod p)
    (hzero : ∑ index : Fin n, h index •
      (Polynomial.X ^ (index : Nat) : Polynomial (ZMod p)) = 0) : h = 0 := by
  funext index
  have hcoeff := congrArg (fun polynomial : Polynomial (ZMod p) =>
    polynomial.coeff (index : Nat)) hzero
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
    Polynomial.coeff_X_pow, Polynomial.coeff_zero] at hcoeff
  rw [Fintype.sum_eq_single index] at hcoeff
  · simpa using hcoeff
  · intro other hne
    have hcoerce : (index : Nat) ≠ (other : Nat) := by
      intro hvalue
      exact hne (Fin.ext hvalue).symm
    simp [hcoerce]
theorem kt19Explicit_rows_independent (p l k : Nat) [NeZero p]
    [Fact p.Prime] (hadmissible : Admissible p l k)
    (u : Fin k → ZMod p) (h : Fin (l - k) → ZMod p)
    (hzero : (∑ index : Fin k, u index • kt19ExplicitLogicalRow p l k
        (hadmissible.2.2.1.trans hadmissible.2.2.2.1) index) +
      ∑ index : Fin (l - k), h index • kt19ExplicitStabilizerRow p l k index = 0) :
    u = 0 ∧ h = 0 := by
  rcases hadmissible with ⟨hp, hk, hkl, hlp, hproduct⟩
  have hkp : k ≤ p := hkl.trans hlp
  have hlength : l ≤ p - k := by omega
  have hpolynomial : kt19ExplicitCoefficientPolynomial p l k hkp u h = 0 :=
    kt19ExplicitCoefficient_eq_zero_of_restrictKept_zero p l k hkp hkl hlength u h
      (by simpa using hzero)
  have hselected : restrictSelected p k (evaluationMap p
      (kt19ExplicitCoefficientPolynomial p l k hkp u h)) = 0 := by
    rw [hpolynomial]
    ext point
    simp [evaluationMap]
  rw [kt19ExplicitCoefficient_restrictSelected] at hselected
  have hu : u = 0 := kt19SelectedDelta_coefficients_zero p k hkp u hselected
  have hstabilizer : ∑ index : Fin (l - k), h index •
      kt19ExplicitStabilizerPolynomial p l k index = 0 := by
    rw [kt19ExplicitCoefficientPolynomial, hu] at hpolynomial
    simpa using hpolynomial
  rw [kt19ExplicitStabilizerCombination_factor] at hstabilizer
  have hmonomial : ∑ index : Fin (l - k), h index •
      (Polynomial.X ^ (index : Nat) : Polynomial (ZMod p)) = 0 := by
    exact (mul_eq_zero.mp hstabilizer).resolve_left
      (kt19SelectedNodalPolynomial_ne_zero p k)
  exact ⟨hu, kt19MonomialCoefficients_zero p (l - k) h hmonomial⟩
noncomputable def kt19ExplicitStabilizerCarrier (p l k : Nat) [NeZero p]
    [Fact p.Prime] :
    Submodule (ZMod p) (PrimeQuditRegisterLabel p (KeptPunctureLocation p k)) :=
  Submodule.span (ZMod p) (Set.range (kt19ExplicitStabilizerRow p l k))
theorem kt19ExplicitStabilizer_mem_shortened (p l k : Nat) [NeZero p]
    [Fact p.Prime] (hkp : k ≤ p) (hkl : k ≤ l) (index : Fin (l - k)) :
    kt19ExplicitStabilizerRow p l k index ∈
      (shortenedReedSolomonCode p l k).carrier := by
  apply (mem_shortenedReedSolomonCode _).2
  refine ⟨evaluationLinearMap p l
    ⟨kt19ExplicitStabilizerPolynomial p l k index,
      kt19ExplicitStabilizerPolynomial_degreeLT p l k hkp hkl index⟩, ?_, ?_, ?_⟩
  · exact evaluation_mem_reedSolomonCode p l _
  · exact kt19ExplicitStabilizer_restrictSelected_zero p l k index
  · rfl
theorem kt19ExplicitStabilizerCarrier_le_shortened (p l k : Nat) [NeZero p]
    [Fact p.Prime] (hkp : k ≤ p) (hkl : k ≤ l) :
    kt19ExplicitStabilizerCarrier p l k ≤
      (shortenedReedSolomonCode p l k).carrier := by
  rw [kt19ExplicitStabilizerCarrier]
  apply Submodule.span_le.2
  rintro word ⟨index, rfl⟩
  exact kt19ExplicitStabilizer_mem_shortened p l k hkp hkl index
theorem kt19Explicit_stabilizer_rows_linearIndependent (p l k : Nat)
    [NeZero p] [Fact p.Prime] (hadmissible : Admissible p l k) :
    LinearIndependent (ZMod p) (kt19ExplicitStabilizerRow p l k) := by
  rw [Fintype.linearIndependent_iff]
  intro coefficient hzero index
  have hboth := kt19Explicit_rows_independent p l k hadmissible 0 coefficient
    (by simpa using hzero)
  simpa using congrFun hboth.2 index
theorem kt19ExplicitStabilizerCarrier_finrank (p l k : Nat) [NeZero p]
    [Fact p.Prime] (hadmissible : Admissible p l k) :
    Module.finrank (ZMod p) (kt19ExplicitStabilizerCarrier p l k) = l - k := by
  rw [kt19ExplicitStabilizerCarrier]
  simpa using finrank_span_eq_card
    (kt19Explicit_stabilizer_rows_linearIndependent p l k hadmissible)
theorem kt19ExplicitStabilizerCarrier_eq_shortened (p l k : Nat)
    [NeZero p] [Fact p.Prime] (hadmissible : Admissible p l k) :
    kt19ExplicitStabilizerCarrier p l k =
      (shortenedReedSolomonCode p l k).carrier := by
  have hkp : k ≤ p := hadmissible.2.2.1.trans hadmissible.2.2.2.1
  apply Submodule.eq_of_le_of_finrank_eq
    (kt19ExplicitStabilizerCarrier_le_shortened p l k hkp hadmissible.2.2.1)
  rw [kt19ExplicitStabilizerCarrier_finrank p l k hadmissible]
  simpa [Dimension_eq_finrank_carrier] using
    (shortenedReedSolomonCode_dimension p l k hkp hadmissible.2.2.1
      hadmissible.2.2.2.1).symm
theorem kt19Explicit_full_cubic_zero (p l k : Nat) [NeZero p]
    [Fact p.Prime] (hadmissible : Admissible p l k)
    (left middle right : Fin k ⊕ Fin (l - k)) :
    cubicPairing p
      (evaluationMap p (kt19ExplicitRowPolynomial p l k
        (hadmissible.2.2.1.trans hadmissible.2.2.2.1) left))
      (evaluationMap p (kt19ExplicitRowPolynomial p l k
        (hadmissible.2.2.1.trans hadmissible.2.2.2.1) middle))
      (evaluationMap p (kt19ExplicitRowPolynomial p l k
        (hadmissible.2.2.1.trans hadmissible.2.2.2.1) right)) = 0 := by
  rcases hadmissible with ⟨hp, hk, hkl, hlp, htriple⟩
  have hkp : k ≤ p := hkl.trans hlp
  let leftBounded : Polynomial.degreeLT (ZMod p) l :=
    ⟨kt19ExplicitRowPolynomial p l k hkp left,
      kt19ExplicitRowPolynomial_degreeLT p l k hkp hkl left⟩
  let middleBounded : Polynomial.degreeLT (ZMod p) l :=
    ⟨kt19ExplicitRowPolynomial p l k hkp middle,
      kt19ExplicitRowPolynomial_degreeLT p l k hkp hkl middle⟩
  let rightBounded : Polynomial.degreeLT (ZMod p) l :=
    ⟨kt19ExplicitRowPolynomial p l k hkp right,
      kt19ExplicitRowPolynomial_degreeLT p l k hkp hkl right⟩
  have hleft : evaluationLinearMap p l leftBounded ∈ (reedSolomonCode p l).carrier :=
    evaluation_mem_reedSolomonCode p l leftBounded
  have hmiddle : evaluationLinearMap p l middleBounded ∈ (reedSolomonCode p l).carrier :=
    evaluation_mem_reedSolomonCode p l middleBounded
  have hright : evaluationLinearMap p l rightBounded ∈ (reedSolomonCode p l).carrier :=
    evaluation_mem_reedSolomonCode p l rightBounded
  have hproduct : coordinatewiseProduct (evaluationLinearMap p l leftBounded)
      (evaluationLinearMap p l middleBounded) ∈ (reedSolomonCode p l).dual.carrier := by
    apply reedSolomonCode_product_le_dual p l htriple
    rw [coordinatewiseProductCode]
    exact Submodule.subset_span ⟨evaluationLinearMap p l leftBounded, hleft,
      evaluationLinearMap p l middleBounded, hmiddle, rfl⟩
  have horthogonal := ((reedSolomonCode p l).mem_dual _).1 hproduct
    (evaluationLinearMap p l rightBounded) hright
  exact horthogonal
theorem kt19Explicit_retained_cubic_add_selected_cubic_eq_full
    (p k : Nat) [NeZero p] [Fact p.Prime]
    (left middle right : Word (ZMod p) (ZMod p)) :
    cubicPairing p (restrictKept p k left) (restrictKept p k middle)
      (restrictKept p k right) +
      (∑ point : {point : ZMod p // point ∈ selectedPunctureLocations p k},
        left point.1 * middle point.1 * right point.1) = cubicPairing p left middle right := by
  classical
  change (∑ point : KeptPunctureLocation p k,
      left point.1 * middle point.1 * right point.1) +
      (∑ point : {point : ZMod p // point ∈ selectedPunctureLocations p k},
        left point.1 * middle point.1 * right point.1) =
    ∑ point : ZMod p, left point * middle point * right point
  rw [Finset.sum_coe_sort (keptPunctureLocations p k)
      (fun point => left point * middle point * right point),
    Finset.sum_coe_sort (selectedPunctureLocations p k)
      (fun point => left point * middle point * right point)]
  simpa [keptPunctureLocations] using
    (Finset.sum_filter_not_add_sum_filter
      (Finset.univ : Finset (ZMod p))
      (fun point => point ∈ selectedPunctureLocations p k)
      (fun point => left point * middle point * right point))
theorem kt19Explicit_cubic_restrict_eq_full_of_selected_sum_zero
    (p k : Nat) [NeZero p] [Fact p.Prime]
    (left middle right : Word (ZMod p) (ZMod p))
    (hselectedSum :
      (∑ point : {point : ZMod p // point ∈ selectedPunctureLocations p k},
        left point.1 * middle point.1 * right point.1) = 0) :
    cubicPairing p (restrictKept p k left) (restrictKept p k middle)
      (restrictKept p k right) = cubicPairing p left middle right := by
  have hsplit := kt19Explicit_retained_cubic_add_selected_cubic_eq_full p k left middle right
  rw [hselectedSum, add_zero] at hsplit
  exact hsplit
theorem kt19Explicit_selected_cubic_sum_zero_of_restrictSelected_zero
    (p k : Nat) [NeZero p] [Fact p.Prime]
    (left middle right : Word (ZMod p) (ZMod p))
    (hselected : restrictSelected p k left = 0) :
    (∑ point : {point : ZMod p // point ∈ selectedPunctureLocations p k},
      left point.1 * middle point.1 * right point.1) = 0 := by
  apply Finset.sum_eq_zero
  intro point _
  have hpoint : left point.1 = 0 := by
    simpa using congrFun hselected
      (⟨point.1, point.2⟩ : SelectedPunctureLocation p k)
  rw [hpoint]
  simp
theorem kt19SelectedDeltaWord_triple_product_zero (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) (left middle right : Fin k)
    (hnot : ¬ (left = middle ∧ middle = right))
    (point : SelectedPunctureLocation p k) :
    kt19SelectedDeltaWord p k hkp left point *
        kt19SelectedDeltaWord p k hkp middle point *
          kt19SelectedDeltaWord p k hkp right point = 0 := by
  by_cases hleftMiddle : left = middle
  · subst middle
    have hleftRight : left ≠ right := by
      intro hleftRight
      exact hnot ⟨rfl, hleftRight⟩
    by_cases hpoint : kt19SelectedPunctureEquivFin p k hkp point = left
    · simp [kt19SelectedDeltaWord, hpoint, hleftRight]
    · simp [kt19SelectedDeltaWord, hpoint]
  · by_cases hpoint : kt19SelectedPunctureEquivFin p k hkp point = left
    · simp [kt19SelectedDeltaWord, hpoint, hleftMiddle]
    · simp [kt19SelectedDeltaWord, hpoint]
theorem kt19ExplicitLogical_selected_triple_sum_zero (p l k : Nat)
    [NeZero p] [Fact p.Prime] (hkp : k ≤ p) (left middle right : Fin k)
    (hnot : ¬ (left = middle ∧ middle = right)) :
    (∑ point : {point : ZMod p // point ∈ selectedPunctureLocations p k},
      evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp left) point.1 *
        evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp middle) point.1 *
          evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp right) point.1) = 0 := by
  apply Finset.sum_eq_zero
  intro point _
  let selectedPoint : SelectedPunctureLocation p k := ⟨point.1, point.2⟩
  have hleft : evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp left) point.1 =
      -kt19SelectedDeltaWord p k hkp left selectedPoint := by
    simpa [selectedPoint] using congrFun
      (kt19ExplicitLogical_restrictSelected p l k hkp left) selectedPoint
  have hmiddle : evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp middle) point.1 =
      -kt19SelectedDeltaWord p k hkp middle selectedPoint := by
    simpa [selectedPoint] using congrFun
      (kt19ExplicitLogical_restrictSelected p l k hkp middle) selectedPoint
  have hright : evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp right) point.1 =
      -kt19SelectedDeltaWord p k hkp right selectedPoint := by
    simpa [selectedPoint] using congrFun
      (kt19ExplicitLogical_restrictSelected p l k hkp right) selectedPoint
  rw [hleft, hmiddle, hright]
  calc
    (-kt19SelectedDeltaWord p k hkp left selectedPoint) *
        (-kt19SelectedDeltaWord p k hkp middle selectedPoint) *
          (-kt19SelectedDeltaWord p k hkp right selectedPoint) =
        -(kt19SelectedDeltaWord p k hkp left selectedPoint *
          kt19SelectedDeltaWord p k hkp middle selectedPoint *
            kt19SelectedDeltaWord p k hkp right selectedPoint) := by ring
    _ = 0 := by
      rw [kt19SelectedDeltaWord_triple_product_zero p k hkp left middle right hnot]
      simp
theorem kt19Explicit_stabilizer_triple_zero (p l k : Nat) [NeZero p]
    [Fact p.Prime] (hadmissible : Admissible p l k)
    (left middle right : Fin k ⊕ Fin (l - k))
    (hcontains : (∃ index, left = Sum.inr index) ∨
      (∃ index, middle = Sum.inr index) ∨ (∃ index, right = Sum.inr index)) :
    cubicPairing p
      (kt19ExplicitRow p l k (hadmissible.2.2.1.trans hadmissible.2.2.2.1) left)
      (kt19ExplicitRow p l k (hadmissible.2.2.1.trans hadmissible.2.2.2.1) middle)
      (kt19ExplicitRow p l k (hadmissible.2.2.1.trans hadmissible.2.2.2.1) right) = 0 := by
  rcases hadmissible with ⟨hp, hk, hkl, hlp, htriple⟩
  have hkp : k ≤ p := hkl.trans hlp
  let hadmissible : Admissible p l k := ⟨hp, hk, hkl, hlp, htriple⟩
  rcases hcontains with ⟨index, rfl⟩ | ⟨index, rfl⟩ | ⟨index, rfl⟩
  · rw [kt19ExplicitRow_eq_restrictKept_evaluation p l k hkp (Sum.inr index),
      kt19ExplicitRow_eq_restrictKept_evaluation p l k hkp middle,
      kt19ExplicitRow_eq_restrictKept_evaluation p l k hkp right]
    simp only [kt19ExplicitRowPolynomial, Sum.elim_inr]
    calc
      _ = cubicPairing p
          (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index))
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp middle))
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp right)) :=
        kt19Explicit_cubic_restrict_eq_full_of_selected_sum_zero p k
          (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index))
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp middle))
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp right))
          (kt19Explicit_selected_cubic_sum_zero_of_restrictSelected_zero p k _ _ _
            (kt19ExplicitStabilizer_restrictSelected_zero p l k index))
      _ = 0 := kt19Explicit_full_cubic_zero p l k hadmissible
        (Sum.inr index) middle right
  · rw [kt19ExplicitRow_eq_restrictKept_evaluation p l k hkp left,
      kt19ExplicitRow_eq_restrictKept_evaluation p l k hkp (Sum.inr index),
      kt19ExplicitRow_eq_restrictKept_evaluation p l k hkp right]
    simp only [kt19ExplicitRowPolynomial, Sum.elim_inr]
    calc
      _ = cubicPairing p
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp left))
          (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index))
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp right)) :=
        kt19Explicit_cubic_restrict_eq_full_of_selected_sum_zero p k
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp left))
          (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index))
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp right))
          (by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (kt19Explicit_selected_cubic_sum_zero_of_restrictSelected_zero p k
                (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index))
                (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp left))
                (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp right))
                (kt19ExplicitStabilizer_restrictSelected_zero p l k index)))
      _ = 0 := kt19Explicit_full_cubic_zero p l k hadmissible
        left (Sum.inr index) right
  · rw [kt19ExplicitRow_eq_restrictKept_evaluation p l k hkp left,
      kt19ExplicitRow_eq_restrictKept_evaluation p l k hkp middle,
      kt19ExplicitRow_eq_restrictKept_evaluation p l k hkp (Sum.inr index)]
    simp only [kt19ExplicitRowPolynomial, Sum.elim_inr]
    calc
      _ = cubicPairing p
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp left))
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp middle))
          (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index)) :=
        kt19Explicit_cubic_restrict_eq_full_of_selected_sum_zero p k
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp left))
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp middle))
          (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index))
          (by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (kt19Explicit_selected_cubic_sum_zero_of_restrictSelected_zero p k
                (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index))
                (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp left))
                (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp middle))
                (kt19ExplicitStabilizer_restrictSelected_zero p l k index)))
      _ = 0 := kt19Explicit_full_cubic_zero p l k hadmissible
        left middle (Sum.inr index)
theorem kt19Explicit_logical_offDiagonal_zero (p l k : Nat) [NeZero p]
    [Fact p.Prime] (hadmissible : Admissible p l k)
    (left middle right : Fin k)
    (hnot : ¬ (left = middle ∧ middle = right)) :
    cubicPairing p
      (kt19ExplicitLogicalRow p l k
        (hadmissible.2.2.1.trans hadmissible.2.2.2.1) left)
      (kt19ExplicitLogicalRow p l k
        (hadmissible.2.2.1.trans hadmissible.2.2.2.1) middle)
      (kt19ExplicitLogicalRow p l k
        (hadmissible.2.2.1.trans hadmissible.2.2.2.1) right) = 0 := by
  rcases hadmissible with ⟨hp, hk, hkl, hlp, htriple⟩
  have hkp : k ≤ p := hkl.trans hlp
  let hadmissible : Admissible p l k := ⟨hp, hk, hkl, hlp, htriple⟩
  have hselected := kt19ExplicitLogical_selected_triple_sum_zero p l k hkp
    left middle right hnot
  have htransport := kt19Explicit_cubic_restrict_eq_full_of_selected_sum_zero p k
    (evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp left))
    (evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp middle))
    (evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp right)) hselected
  simpa [kt19ExplicitLogicalRow] using htransport.trans
    (kt19Explicit_full_cubic_zero p l k hadmissible
      (Sum.inl left) (Sum.inl middle) (Sum.inl right))
noncomputable def kt19ExplicitCubicRowFamily (p l k : Nat) [NeZero p]
    [Fact p.Prime] (hadmissible : Admissible p l k) :
    CubicRowFamily p (Fin k) (Fin (l - k)) (KeptPunctureLocation p k) := by
  let hkp : k ≤ p := hadmissible.2.2.1.trans hadmissible.2.2.2.1
  exact
    { logicalRow := kt19ExplicitLogicalRow p l k hkp
      stabilizerRow := kt19ExplicitStabilizerRow p l k
      rowIndependent := kt19Explicit_rows_independent p l k hadmissible
      stabilizerTriple_zero := kt19Explicit_stabilizer_triple_zero p l k hadmissible
      logicalTriple_offDiagonal_zero := kt19Explicit_logical_offDiagonal_zero p l k hadmissible }
theorem kt19ExplicitCubicRowFamily_stabilizerCarrier (p l k : Nat) [NeZero p]
    [Fact p.Prime] (hadmissible : Admissible p l k) :
    stabilizerCarrier (kt19ExplicitCubicRowFamily p l k hadmissible) =
      (shortenedReedSolomonCode p l k).carrier := by
  simpa [stabilizerCarrier, kt19ExplicitCubicRowFamily,
    kt19ExplicitStabilizerCarrier] using
    (kt19ExplicitStabilizerCarrier_eq_shortened p l k hadmissible)
noncomputable def kt19ExplicitFixedPrimeDistillationFamily (p l k : Nat)
    [NeZero p] [Fact p.Prime] (hfive : 5 ≤ p)
    (hadmissible : Admissible p l k) :
    KT19DistillationFamily p l k := by
  exact
    { primeAtLeastFive := ⟨Fact.out, hfive⟩
      admissible := hadmissible
      rowFamily := kt19ExplicitCubicRowFamily p l k hadmissible
      stabilizerCarrier_eq_shortened :=
        kt19ExplicitCubicRowFamily_stabilizerCarrier p l k hadmissible }
noncomputable def kt19ExplicitDistillationFamily (p : Nat) [NeZero p]
    [Fact p.Prime] (hlarge : 32 ≤ p) :
    KT19DistillationFamily p (kt19ExplicitL p) (kt19ExplicitK p) := by
  let hadmissible : Admissible p (kt19ExplicitL p) (kt19ExplicitK p) :=
    kt19ExplicitParameters_admissible p Fact.out hlarge
  exact kt19ExplicitFixedPrimeDistillationFamily p (kt19ExplicitL p)
    (kt19ExplicitK p) (by omega) hadmissible
def kt19PrimeQuditLabelEquiv (p : Nat) [NeZero p] (Site : Type u)
    [Fintype Site] [DecidableEq Site] :
    PrimeQuditRegisterLabel p Site ≃ Qudit.Label (fun _ : Site => p) where
  toFun label site := (ZMod.finEquiv p).symm (label site)
  invFun label site := ZMod.finEquiv p (label site)
  left_inv label := by
    funext site
    exact (ZMod.finEquiv p).apply_symm_apply (label site)
  right_inv label := by
    funext site
    exact (ZMod.finEquiv p).symm_apply_apply (label site)
noncomputable def kt19PrimeQuditRegisterQuditTransport
    (p : Nat) [NeZero p] (Site : Type u) [Fintype Site] [DecidableEq Site] :
    UnitaryTransport (PrimeQuditRegister p Site)
      (Qudit.QuditRegister (fun _ : Site => p)) := by
  let sourceBasis := EuclideanSpace.basisFun (PrimeQuditRegisterLabel p Site) Complex
  let targetBasis := EuclideanSpace.basisFun (Qudit.Label (fun _ : Site => p)) Complex
  let E := sourceBasis.equiv targetBasis (kt19PrimeQuditLabelEquiv p Site)
  exact
    { toLinearEquiv := E.toLinearEquiv
      map_inner := E.inner_map_map }
@[simp] theorem kt19PrimeQuditRegisterQuditTransport_apply_basis
    (p : Nat) [NeZero p] (Site : Type u) [Fintype Site] [DecidableEq Site]
    (label : PrimeQuditRegisterLabel p Site) :
    kt19PrimeQuditRegisterQuditTransport p Site
      (EuclideanSpace.basisFun (PrimeQuditRegisterLabel p Site) Complex label) =
        EuclideanSpace.basisFun (Qudit.Label (fun _ : Site => p)) Complex
          (kt19PrimeQuditLabelEquiv p Site label) := by
  dsimp [kt19PrimeQuditRegisterQuditTransport]
  rw [OrthonormalBasis.equiv_apply_basis]
noncomputable def kt19SelectedPortSubsystem (p k : Nat) [NeZero p]
    (port : Fin k) : QuditSubsystem (fun _ : Fin k => p) where
  selected := {port}
def kt19SelectedPortCoordinate (p k : Nat) [NeZero p]
    (port : Fin k) : (kt19SelectedPortSubsystem p k port).SelectedCoordinates :=
  ⟨port, by simp [kt19SelectedPortSubsystem]⟩
def kt19SelectedPortLabelEquiv (p k : Nat) [NeZero p]
    (port : Fin k) :
    Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions ≃
      PrimeQuditRegisterLabel p (KT19SingleResourceSite.{0}) where
  toFun label _ := ZMod.finEquiv p (label (kt19SelectedPortCoordinate p k port))
  invFun label selected := (ZMod.finEquiv p).symm (label default)
  left_inv label := by
    funext selected
    have hselected : selected = kt19SelectedPortCoordinate p k port := by
      apply Subtype.ext
      exact Finset.mem_singleton.mp selected.property
    rw [hselected]
    simp [kt19SelectedPortCoordinate]
  right_inv label := by
    funext site
    have hsite : site = default := Subsingleton.elim _ _
    rw [hsite]
    simp
noncomputable def kt19SelectedPortTransport (p k : Nat) [NeZero p]
    (port : Fin k) :
    UnitaryTransport (kt19SelectedPortSubsystem p k port).selectedSystem
      (KT19SingleQudit.{0} p) := by
  let sourceBasis := EuclideanSpace.basisFun
    (Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions) Complex
  let targetBasis := EuclideanSpace.basisFun
    (PrimeQuditRegisterLabel p KT19SingleResourceSite.{0}) Complex
  let E := sourceBasis.equiv targetBasis (kt19SelectedPortLabelEquiv p k port)
  exact
    { toLinearEquiv := E.toLinearEquiv
      map_inner := E.inner_map_map }
@[simp] theorem kt19SelectedPortTransport_apply_basis (p k : Nat) [NeZero p]
    (port : Fin k)
    (label : Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions) :
    kt19SelectedPortTransport p k port
      (EuclideanSpace.basisFun
        (Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions) Complex label) =
        EuclideanSpace.basisFun
          (PrimeQuditRegisterLabel p KT19SingleResourceSite.{0}) Complex
          (kt19SelectedPortLabelEquiv p k port label) := by
  dsimp [kt19SelectedPortTransport]
  rw [OrthonormalBasis.equiv_apply_basis]
theorem kt19SelectedPortDimensions_pos (p k : Nat) [NeZero p]
    (port : Fin k) :
    ∀ coordinate, 0 < (kt19SelectedPortSubsystem p k port).selectedDimensions coordinate := by
  intro coordinate
  exact Nat.pos_of_ne_zero (NeZero.ne p)
def kt19SelectedPortZeroLabel (p k : Nat) [NeZero p]
    (port : Fin k) :
    Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions :=
  Qudit.zeroLabel _ (kt19SelectedPortDimensions_pos p k port)
noncomputable def kt19SelectedPortMagicState (p k : Nat) [NeZero p]
    (port : Fin k) (label : PrimeQuditRegisterLabel p (Fin k)) :
    (kt19SelectedPortSubsystem p k port).selectedSystem :=
  (kt19SelectedPortTransport p k port).symm
    (magicRegisterKet p (kt19SingleSiteLabel (label port)))
noncomputable def kt19SelectedPortComplementState (p k : Nat) [NeZero p]
    (port : Fin k) (label : PrimeQuditRegisterLabel p (Fin k)) :
    (kt19SelectedPortSubsystem p k port).complementSystem :=
  WithLp.toLp 2 (fun right =>
    (((kt19PrimeQuditRegisterQuditTransport p (Fin k)) (magicRegisterKet p label)).ofLp
        ((kt19SelectedPortSubsystem p k port).recombineLabel
          (kt19SelectedPortZeroLabel p k port, right))) /
      (kt19SelectedPortMagicState p k port label).ofLp
        (kt19SelectedPortZeroLabel p k port))
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
noncomputable def kt19SelectedPortActualMarginal
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k) :
    DensityOperator (KT19SingleQudit.{0} p) :=
  (kt19SelectedPortTransport p k port).conjDensity
    ((kt19SelectedPortSubsystem p k port).selectedPartialTraceFromRegister.mapDensity
      ((kt19PrimeQuditRegisterQuditTransport p (Fin k)).conjDensity
        (family.run mu hmu_nonneg hmu_sum).acceptedOutput))
noncomputable def kt19SelectedPortDensity
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k) :
    DensityOperator (KT19SingleQudit.{0} p) :=
  kt19SelectedPortActualMarginal family mu hmu_nonneg hmu_sum port
noncomputable def kt19SelectedPortLabelDistribution
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k) (a : ZMod p) : ℝ :=
  ∑ label : PrimeQuditRegisterLabel p (Fin k),
    if label port = a then
      kt19OutputLabelDistribution (family.run mu hmu_nonneg hmu_sum).acceptedOutput label
    else 0
theorem kt19SelectedPortLabelDistribution_nonneg
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k) (a : ZMod p) :
    0 ≤ kt19SelectedPortLabelDistribution family mu hmu_nonneg hmu_sum port a := by
  unfold kt19SelectedPortLabelDistribution
  apply Finset.sum_nonneg
  intro label _
  by_cases hlabel : label port = a
  · simpa [hlabel] using kt19OutputLabelDistribution_nonneg
      (family.run mu hmu_nonneg hmu_sum).acceptedOutput label
  · simp [hlabel]
theorem kt19SelectedPortLabelDistribution_sum
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k) :
    ∑ a : ZMod p, kt19SelectedPortLabelDistribution
      family mu hmu_nonneg hmu_sum port a = 1 := by
  classical
  unfold kt19SelectedPortLabelDistribution
  calc
    (∑ a : ZMod p, ∑ label : PrimeQuditRegisterLabel p (Fin k),
        if label port = a then
          kt19OutputLabelDistribution (family.run mu hmu_nonneg hmu_sum).acceptedOutput label
        else 0) =
        ∑ label : PrimeQuditRegisterLabel p (Fin k), ∑ a : ZMod p,
          if label port = a then
            kt19OutputLabelDistribution
              (family.run mu hmu_nonneg hmu_sum).acceptedOutput label
          else 0 := Finset.sum_comm
    _ = ∑ label : PrimeQuditRegisterLabel p (Fin k),
        kt19OutputLabelDistribution (family.run mu hmu_nonneg hmu_sum).acceptedOutput label := by
      apply Finset.sum_congr rfl
      intro label _
      rw [Finset.sum_eq_single (label port)]
      · simp
      · intro other _ hother
        simp [hother, Ne.symm hother]
      · simp
    _ = 1 := kt19OutputLabelDistribution_sum
      (family.run mu hmu_nonneg hmu_sum).acceptedOutput
noncomputable def kt19SelectedPortTransportedChannel
    (p k : Nat) [NeZero p] (port : Fin k) :
    QuantumChannel (PrimeQuditRegister p (Fin k)) (KT19SingleQudit.{0} p) :=
  QuantumChannel.comp
    (QuantumChannel.unitaryConj (kt19SelectedPortTransport p k port))
    (QuantumChannel.comp
      (kt19SelectedPortSubsystem p k port).selectedPartialTraceFromRegister
      (QuantumChannel.unitaryConj
        (kt19PrimeQuditRegisterQuditTransport p (Fin k))))
noncomputable def kt19SelectedPortMagicWordDensity
    (p : Nat) [NeZero p] (a : ZMod p) : DensityOperator (KT19SingleQudit.{0} p) :=
  DensityOperator.pureDensity (magicRegisterKet p (kt19SingleSiteLabel a)) (by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
      magicRegisterKet_inner_self]
    norm_num)
def kt19SelectedPortSingleSiteLabelEquiv (p : Nat) [NeZero p] :
    ZMod p ≃ PrimeQuditRegisterLabel p KT19SingleResourceSite.{0} where
  toFun := kt19SingleSiteLabel
  invFun word := word default
  left_inv _ := rfl
  right_inv word := by
    funext site
    have hsite : site = default := Subsingleton.elim _ _
    rw [hsite]
    rfl
noncomputable def kt19SelectedPortRoutedMass
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (port : Fin k) (a : ZMod p) : ℝ :=
  ∑ error : Word (ZMod p) (KeptPunctureLocation p k),
    if kt19AcceptedWord family.rowFamily error ∧
        KT19DistillationFamily.kt19Routing family error port = a then
      wordProbability p mu error
    else 0
abbrev kt19FixedPrimeInputSlots (p k depth : Nat) [NeZero p] [Fact p.Prime] :=
  Fin depth → Fin (Fintype.card (KeptPunctureLocation p k))
abbrev kt19FixedPrimeOutputSlots (k depth : Nat) :=
  Fin depth → Fin k
def kt19FixedPrimeOutputPathEmpty (k : Nat) : kt19FixedPrimeOutputSlots k 0 :=
  fun index => Fin.elim0 index
def kt19FixedPrimeOutputPathAppend (k depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (port : Fin k) :
    kt19FixedPrimeOutputSlots k (depth + 1) :=
  Fin.lastCases port path
def kt19FixedPrimeOutputPathInit (k depth : Nat)
    (path : kt19FixedPrimeOutputSlots k (depth + 1)) :
    kt19FixedPrimeOutputSlots k depth :=
  fun index => path index.castSucc
def kt19FixedPrimeOutputPathLast (k depth : Nat)
    (path : kt19FixedPrimeOutputSlots k (depth + 1)) : Fin k :=
  path (Fin.last depth)
@[simp] theorem kt19FixedPrimeOutputPathInit_append (k depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (port : Fin k) :
    kt19FixedPrimeOutputPathInit k depth
      (kt19FixedPrimeOutputPathAppend k depth path port) = path := by
  funext index
  simp [kt19FixedPrimeOutputPathInit, kt19FixedPrimeOutputPathAppend]
@[simp] theorem kt19FixedPrimeOutputPathLast_append (k depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (port : Fin k) :
    kt19FixedPrimeOutputPathLast k depth
      (kt19FixedPrimeOutputPathAppend k depth path port) = port := by
  simp [kt19FixedPrimeOutputPathLast, kt19FixedPrimeOutputPathAppend]
structure KT19FixedPrimeDistribution (p : Nat) [NeZero p] [Fact p.Prime] where
  mass : ZMod p → ℝ
  mass_nonneg : ∀ a : ZMod p, 0 ≤ mass a
  mass_sum : ∑ a : ZMod p, mass a = 1
noncomputable def kt19FixedPrimeSuccessorDistribution
    (family : KT19DistillationFamily p l k)
    (distribution : KT19FixedPrimeDistribution p) (port : Fin k) :
    KT19FixedPrimeDistribution p where
  mass := kt19SelectedPortLabelDistribution family distribution.mass
    distribution.mass_nonneg distribution.mass_sum port
  mass_nonneg := kt19SelectedPortLabelDistribution_nonneg family distribution.mass
    distribution.mass_nonneg distribution.mass_sum port
  mass_sum := kt19SelectedPortLabelDistribution_sum family distribution.mass
    distribution.mass_nonneg distribution.mass_sum port
noncomputable def kt19FixedPrimePathDistribution
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) :
    ∀ (depth : Nat), kt19FixedPrimeOutputSlots k depth →
      KT19FixedPrimeDistribution p
  | 0, _ => initial
  | depth + 1, path =>
      kt19FixedPrimeSuccessorDistribution family
        (kt19FixedPrimePathDistribution family initial depth
          (kt19FixedPrimeOutputPathInit k depth path))
        (kt19FixedPrimeOutputPathLast k depth path)
abbrev kt19FixedPrimeParentOutputSlots (p k : Nat) [NeZero p] [Fact p.Prime] :=
  Fin (Fintype.card (KeptPunctureLocation p k)) × Fin k
abbrev kt19FixedPrimeChildInputSlots (p k : Nat) [NeZero p] [Fact p.Prime] :=
  Fin k × Fin (Fintype.card (KeptPunctureLocation p k))
def kt19FixedPrimeRouting (p k : Nat) [NeZero p] [Fact p.Prime] :
    kt19FixedPrimeParentOutputSlots p k ≃ kt19FixedPrimeChildInputSlots p k :=
  DependentBatch.parentPortTranspose
    (Fin (Fintype.card (KeptPunctureLocation p k))) (Fin k)
def kt19FixedPrimeChildInputSlot (p k : Nat) [NeZero p] [Fact p.Prime]
    (port : Fin k) (parent : Fin (Fintype.card (KeptPunctureLocation p k))) :
    kt19FixedPrimeChildInputSlots p k :=
  kt19FixedPrimeRouting p k (DependentBatch.childInputSlot port parent)
@[simp] theorem kt19FixedPrimeChildInputSlot_apply (p k : Nat)
    [NeZero p] [Fact p.Prime] (port : Fin k)
    (parent : Fin (Fintype.card (KeptPunctureLocation p k))) :
    kt19FixedPrimeChildInputSlot p k port parent = (port, parent) :=
  rfl
noncomputable def kt19FixedPrimeFreshParentRun
    (family : KT19DistillationFamily p l k)
    (distribution : KT19FixedPrimeDistribution p)
    (_parent : Fin (Fintype.card (KeptPunctureLocation p k))) :
    DistillationRun (KT19SingleQudit.{0} p)
      (PrimeQuditRegister p (KeptPunctureLocation p k))
      (PrimeQuditRegister p (Fin k)) :=
  family.run distribution.mass distribution.mass_nonneg distribution.mass_sum
noncomputable def kt19FixedPrimeFreshParentPortDensity
    (family : KT19DistillationFamily p l k)
    (distribution : KT19FixedPrimeDistribution p)
    (parent : Fin (Fintype.card (KeptPunctureLocation p k))) (port : Fin k) :
    DensityOperator (KT19SingleQudit.{0} p) :=
  (kt19SelectedPortTransport p k port).conjDensity
    ((kt19SelectedPortSubsystem p k port).selectedPartialTraceFromRegister.mapDensity
      ((kt19PrimeQuditRegisterQuditTransport p (Fin k)).conjDensity
        (kt19FixedPrimeFreshParentRun family distribution parent).acceptedOutput))
noncomputable def kt19FixedPrimeChildResources
    (family : KT19DistillationFamily p l k)
    (distribution : KT19FixedPrimeDistribution p) (port : Fin k) :
    ResourceInput (Fintype.card (KeptPunctureLocation p k))
      (KT19SingleQudit.{0} p) :=
  fun parent =>
    let source := (kt19FixedPrimeRouting p k).symm
      (kt19FixedPrimeChildInputSlot p k port parent)
    kt19FixedPrimeFreshParentPortDensity family distribution source.1 source.2
@[simp] theorem kt19FixedPrimeChildResources_apply
    (family : KT19DistillationFamily p l k)
    (distribution : KT19FixedPrimeDistribution p) (port : Fin k)
    (parent : Fin (Fintype.card (KeptPunctureLocation p k))) :
    kt19FixedPrimeChildResources family distribution port parent =
      kt19FixedPrimeFreshParentPortDensity family distribution parent port := by
  rfl
noncomputable def kt19FixedPrimeChildRun
    (family : KT19DistillationFamily p l k)
    (distribution : KT19FixedPrimeDistribution p) (port : Fin k) :
    DistillationRun (KT19SingleQudit.{0} p)
      (PrimeQuditRegister p (KeptPunctureLocation p k))
      (PrimeQuditRegister p (Fin k)) :=
  (FiniteInstrument.binaryDistillationRun
    (kt19ProtocolInstrument family.rowFamily) (kt19Accepts family.rowFamily)
    (kt19ProtocolInstrument_complete family.rowFamily)
    (Fintype.card (KeptPunctureLocation p k))
    (kt19FixedPrimeChildResources family distribution port)
    (kt19PrepareInput (q := p) (Site := KeptPunctureLocation p k))
    (kt19EndpointFallback (q := p) (Site := KeptPunctureLocation p k))).postprocess family.decoder
noncomputable def kt19FixedPrimePathRun
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) :
    DistillationRun (KT19SingleQudit.{0} p)
      (PrimeQuditRegister p (KeptPunctureLocation p k))
      (PrimeQuditRegister p (Fin k)) :=
  family.run (kt19FixedPrimePathDistribution family initial depth path).mass
    (kt19FixedPrimePathDistribution family initial depth path).mass_nonneg
    (kt19FixedPrimePathDistribution family initial depth path).mass_sum
def kt19FixedPrimeOutputPathPrefix (k depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (stage : Fin (depth + 1)) :
    kt19FixedPrimeOutputSlots k stage.1 :=
  fun index => path ⟨index.1,
    Nat.lt_of_lt_of_le index.2 (Nat.le_of_lt_succ stage.2)⟩
def kt19FixedPrimePathStagePath (k depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (stage : Fin depth) :
    kt19FixedPrimeOutputSlots k stage.1 :=
  kt19FixedPrimeOutputPathPrefix k depth path stage.castSucc
noncomputable def kt19FixedPrimePathStageRun
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (stage : Fin depth) :
    DistillationRun (KT19SingleQudit.{0} p)
      (PrimeQuditRegister p (KeptPunctureLocation p k))
      (PrimeQuditRegister p (Fin k)) :=
  kt19FixedPrimePathRun family initial stage.1
    (kt19FixedPrimePathStagePath k depth path stage)
noncomputable def kt19FixedPrimePathStageYield
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (stage : Fin depth) : NNReal :=
  ⟨(kt19FixedPrimePathStageRun family initial depth path stage).successProbability,
    (kt19FixedPrimePathStageRun family initial depth path stage).success_nonneg⟩
noncomputable def kt19FixedPrimePathStageTypedSuccessfulOutputCost
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (stage : Fin depth) : ℝ :=
  DependentBatch.typedSuccessfulOutputCost (KeptPunctureLocation p k) (Fin k)
    (kt19FixedPrimePathStageYield family initial depth path stage)
noncomputable def kt19FixedPrimePathYieldFactor
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) : NNReal :=
  ∏ stage : Fin depth, kt19FixedPrimePathStageYield family initial depth path stage
noncomputable def kt19FixedPrimePooledAcceptedOutput
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat) : NNReal :=
  ∑ path : kt19FixedPrimeOutputSlots k depth,
    kt19FixedPrimePathYieldFactor family initial depth path
theorem kt19FixedPrimeOutputSlots_nonempty
    (family : KT19DistillationFamily p l k) (depth : Nat) :
    Nonempty (kt19FixedPrimeOutputSlots k depth) := by
  rcases KT19DistillationFamily.outputPort_nonempty family with ⟨port⟩
  exact ⟨fun _ => port⟩
noncomputable def kt19FixedPrimePooledYield
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat) : NNReal :=
  kt19FixedPrimePooledAcceptedOutput family initial depth /
    Fintype.card (kt19FixedPrimeOutputSlots k depth)
noncomputable def kt19FixedPrimeTypedSuccessfulOutputCost
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat) : ℝ :=
  DependentBatch.typedSuccessfulOutputCost (kt19FixedPrimeInputSlots p k depth)
    (kt19FixedPrimeOutputSlots k depth)
    (kt19FixedPrimePooledYield family initial depth)
noncomputable def kt19FixedPrimePathError
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) : ℝ :=
  kt19ErrorRate (kt19FixedPrimePathDistribution family initial depth path).mass
noncomputable def kt19FixedPrimeIterationScale
    (family : KT19DistillationFamily p l k) : ℝ :=
  KT19DistillationFamily.smallErrorRecurrenceConstant family +
    4 * ((p - k : Nat) : ℝ) + 1
theorem kt19FixedPrimeRecurrenceConstant_nonneg
    (family : KT19DistillationFamily p l k) :
    0 ≤ KT19DistillationFamily.smallErrorRecurrenceConstant family := by
  unfold KT19DistillationFamily.smallErrorRecurrenceConstant
  positivity
theorem kt19FixedPrimeIterationScale_one_le
    (family : KT19DistillationFamily p l k) :
    1 ≤ kt19FixedPrimeIterationScale family := by
  unfold kt19FixedPrimeIterationScale
  have hcount_nonneg : (0 : ℝ) ≤ ((p - k : Nat) : ℝ) := Nat.cast_nonneg _
  nlinarith [kt19FixedPrimeRecurrenceConstant_nonneg family, hcount_nonneg]
theorem kt19FixedPrimeIterationScale_pos
    (family : KT19DistillationFamily p l k) :
    0 < kt19FixedPrimeIterationScale family :=
  lt_of_lt_of_le zero_lt_one (kt19FixedPrimeIterationScale_one_le family)
def kt19FixedPrimeInitialSmallDomain
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) : Prop :=
  kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass ≤ 1 / 4
noncomputable def kt19FixedPrimeErrorEnvelope
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) : Nat → ℝ
  | 0 => kt19ErrorRate initial.mass
  | depth + 1 =>
      kt19FixedPrimeIterationScale family ^ (l - k - 1) *
        (kt19FixedPrimeErrorEnvelope family initial depth) ^ (l - k)
noncomputable def kt19FixedPrimeReachedOutputError
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat) : ℝ := by
  classical
  exact Finset.univ.sup'
    ⟨(kt19FixedPrimeOutputSlots_nonempty family depth).some, Finset.mem_univ _⟩
    fun path => kt19FixedPrimePathError family initial depth path
def kt19FixedPrimeInitialDistribution
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) : KT19FixedPrimeDistribution p where
  mass := mu
  mass_nonneg := hmu_nonneg
  mass_sum := hmu_sum
noncomputable def kt19FixedPrimeScheduleTargetError
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ) (depth : Nat) : ℝ :=
  (kt19FixedPrimeIterationScale family * kt19ErrorRate mu) ^ ((l - k) ^ depth)
noncomputable def kt19FixedPrimeActualOutputError
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (depth : Nat) : ℝ :=
  kt19FixedPrimeReachedOutputError family
    (kt19FixedPrimeInitialDistribution mu hmu_nonneg hmu_sum) depth
noncomputable def kt19FixedPrimeExpectedYield
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (depth : Nat) : NNReal :=
  kt19FixedPrimePooledYield family
    (kt19FixedPrimeInitialDistribution mu hmu_nonneg hmu_sum) depth
noncomputable def kt19FixedPrimeSuccessfulOutputCost
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (depth : Nat) : ℝ :=
  kt19FixedPrimeTypedSuccessfulOutputCost family
    (kt19FixedPrimeInitialDistribution mu hmu_nonneg hmu_sum) depth
noncomputable def kt19FixedPrimeGamma (p l k : Nat) : ℝ :=
  Real.log (((p - k : Nat) : ℝ) / (k : ℝ)) / Real.log ((l - k : Nat) : ℝ)
noncomputable def kt19FixedPrimeLogGrowthBase
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ) : ℝ :=
  -Real.log (kt19FixedPrimeIterationScale family * kt19ErrorRate mu)
noncomputable def kt19FixedPrimeCostCoefficient
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ) : ℝ :=
  (6 / 5 : ℝ) /
    Real.rpow (kt19FixedPrimeLogGrowthBase family mu)
      (kt19FixedPrimeGamma p l k)
noncomputable def kt19SmallIIDRate
    (family : KT19DistillationFamily p l k) : ℝ :=
  1 / (4 * kt19FixedPrimeIterationScale family)
noncomputable def kt19SmallIIDLaw
    (family : KT19DistillationFamily p l k) : ZMod p → ℝ :=
  fun a => if a = 0 then 1 - kt19SmallIIDRate family
    else if a = 1 then kt19SmallIIDRate family else 0
theorem kt19SmallIIDRate_pos
    (family : KT19DistillationFamily p l k) :
    0 < kt19SmallIIDRate family := by
  unfold kt19SmallIIDRate
  exact one_div_pos.mpr
    (mul_pos (by norm_num) (kt19FixedPrimeIterationScale_pos family))
theorem kt19SmallIIDRate_le_one
    (family : KT19DistillationFamily p l k) :
    kt19SmallIIDRate family ≤ 1 := by
  unfold kt19SmallIIDRate
  have hden : (1 : ℝ) ≤ 4 * kt19FixedPrimeIterationScale family := by
    have hscale : (1 : ℝ) ≤ kt19FixedPrimeIterationScale family :=
      kt19FixedPrimeIterationScale_one_le family
    nlinarith
  exact (one_div_le_one_div_of_le (by norm_num) hden).trans_eq (by norm_num)
theorem kt19SmallIIDLaw_nonneg
    (family : KT19DistillationFamily p l k) (a : ZMod p) :
    0 ≤ kt19SmallIIDLaw family a := by
  unfold kt19SmallIIDLaw
  split_ifs
  · exact sub_nonneg.mpr (kt19SmallIIDRate_le_one family)
  · exact (kt19SmallIIDRate_pos family).le
  · exact le_rfl
theorem kt19SmallIIDLaw_sum
    (family : KT19DistillationFamily p l k) [Fact p.Prime] :
    ∑ a : ZMod p, kt19SmallIIDLaw family a = 1 := by
  classical
  let support : Finset (ZMod p) :=
    (Finset.univ.erase (0 : ZMod p)).erase 1
  have hsupport : ∑ a ∈ support, kt19SmallIIDLaw family a = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have haone : a ≠ 1 := (Finset.mem_erase.mp ha).1
    have hazero : a ≠ 0 :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
    simp [kt19SmallIIDLaw, hazero, haone]
  calc
    ∑ a : ZMod p, kt19SmallIIDLaw family a =
        (∑ a ∈ Finset.univ.erase (0 : ZMod p), kt19SmallIIDLaw family a) +
          kt19SmallIIDLaw family 0 := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p))]
    _ = (∑ a ∈ support, kt19SmallIIDLaw family a) +
          kt19SmallIIDLaw family 1 + kt19SmallIIDLaw family 0 := by
      rw [← Finset.sum_erase_add (a := (1 : ZMod p))
        (Finset.univ.erase (0 : ZMod p)) _ (by simp)]
    _ = 1 := by
      rw [hsupport]
      simp [kt19SmallIIDLaw]
end QEC.Distillation.KT19VanishingOverhead


