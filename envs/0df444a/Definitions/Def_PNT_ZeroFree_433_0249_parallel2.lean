-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0249_parallel2
-- name    : PNT_ZeroFree_433_0249_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:28:57.284469+00:00
-- url     : https://prove2.me/theorems/ce9f93a7-6a5d-466c-8c4a-e88edeb77325
-- title:
--   Zero-free region foundations: Eisenstein.InverseCorrespondence [0249_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.InverseCorrespondence
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/InverseCorrespondence.lean#L316-L556

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0130
import Definitions.Def_PNT_ZeroFree_433_0174_parallel1
import Definitions.Def_PNT_ZeroFree_433_0223_parallel1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel1
import Definitions.Def_PNT_ZeroFree_433_0237_parallel1
import Definitions.Def_PNT_ZeroFree_433_0239_parallel1
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1
import Definitions.Def_PNT_ZeroFree_433_0242_parallel2
import Definitions.Def_PNT_ZeroFree_433_0243_parallel1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel2
import Definitions.Def_PNT_ZeroFree_433_0246_parallel1
import Definitions.Def_PNT_ZeroFree_433_0249_parallel1
import Definitions.Def_PNT_ZeroFree_433_0255_parallel1
import Definitions.Def_PNT_ZeroFree_433_0259_parallel1
import Definitions.Def_PNT_ZeroFree_433_0275_parallel2
import Definitions.Def_PNT_ZeroFree_433_0280_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/InverseCorrespondence.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical


open Filter MeasureTheory
open scoped BigOperators Classical

namespace CubicEisenstein


section

open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma diagonal_unit_weighted_periodic (u t:Eisˣ) (j:ℕ) (h:Eis)
    (hr:(↑u⁻¹:Eis)^2*(t:Eis)=omega^j ∨ (↑u⁻¹:Eis)^2*(t:Eis)=-(omega^j))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j 0*(t:Eis))
    (v:ℝ) (hv:0<v) (s:ℂ) (m:Eis) (z:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (t:Eis))*
      upperSection (z+3*eisEmbedding m) v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m))=
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (t:Eis))*
      upperSection z v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  simpa only [diagonal_unit_eisenstein_rows,affineCuspBlock] using
    affineCuspBlock_weighted_periodic h (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis)) j 0 t.ne_zero
      (by simpa using hr) hbase v s m z


lemma diagonal_unit_fourier_shift (u t:Eisˣ) (j:ℕ) (h:Eis)
    (hr:(↑u⁻¹:Eis)^2*(t:Eis)=omega^j ∨ (↑u⁻¹:Eis)^2*(t:Eis)=-(omega^j))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j 0*(t:Eis))
    (v:ℝ) (hv:0<v) (s b:ℂ) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection (z+b) v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ShortDraftTrace.breveE (ninthCuspFrequency h*b)*
        ∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
          integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
            ShortDraftTrace.breveE (-ninthCuspFrequency h*z) :=
  period_integral_twisted_translation
    (fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s)
    (ninthCuspFrequency h) (diagonal_unit_weighted_periodic u t j h hr hbase v hv s) b


end

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedCuspRoot (b:Bool) : Eisˣ := if b then ramifiedOmegaUnit^2 else ramifiedOmegaUnit

def ramifiedCuspScaleUnit (b:Bool) : Eisˣ := if b then ramifiedOmegaUnit^2 else -ramifiedOmegaUnit


lemma ramifiedCuspRoot_val (b:Bool) : (ramifiedCuspRoot b:Eis)=omega^(ramifiedCuspDirectIndex b) := by
  cases b <;>simp [ramifiedCuspRoot,ramifiedCuspDirectIndex,ramifiedOmegaUnit_val]

lemma ramifiedCuspRoot_cube (b:Bool) : (ramifiedCuspRoot b:Eis)^3=1 := by
  rw [ramifiedCuspRoot_val,←pow_mul,Nat.mul_comm,pow_mul,omega_primitive.pow_eq_one,one_pow]

lemma ramifiedCuspRoot_primitive (b:Bool) :
    (ramifiedCuspRoot b:Eis)^2+(ramifiedCuspRoot b:Eis)+1=0 := by
  cases b
  · simpa [ramifiedCuspRoot,ramifiedOmegaUnit_val] using ramified_omega_relation
  · simp only [ramifiedCuspRoot,ite_true,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,←pow_mul]
    rw [show 2*2=4 from rfl,ramified_omega_four]
    linear_combination ramified_omega_relation

lemma ramifiedCuspScaleUnit_spec (b:Bool) :
    -(ramifiedCuspRoot b:Eis)*(1+2*(ramifiedCuspRoot b:Eis))=onceCuspScale (ramifiedCuspScaleUnit b) := by
  cases b
  · simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedTraceLambda,ramifiedOmegaUnit_val]
  · simp only [ramifiedCuspRoot,ramifiedCuspScaleUnit,ite_true,onceCuspScale,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,
      ramifiedTraceLambda]
    linear_combination -(2*omega^2)*ramified_omega_relation

lemma ramifiedCusp_neg_inv_square (b:Bool) :
    (↑(-(ramifiedCuspRoot b))⁻¹:Eis)^2=(ramifiedCuspRoot b:Eis) := by
  have hi:(↑(-(ramifiedCuspRoot b))⁻¹:Eis)=-(ramifiedCuspRoot b:Eis)^2:=by
    apply (-(ramifiedCuspRoot b)).inv_eq_of_mul_eq_one_right
    change -(ramifiedCuspRoot b:Eis)*(-(ramifiedCuspRoot b:Eis)^2)=1
    convert! ramifiedCuspRoot_cube b using 1 ;ring
  rw [hi]
  linear_combination (ramifiedCuspRoot b:Eis)*ramifiedCuspRoot_cube b

lemma ramifiedCusp_opposite_character (b:Bool) :
    (↑(-(ramifiedCuspRoot b))⁻¹:Eis)^2*(-(ramifiedCuspRoot b:Eis))=
      -(omega^(ramifiedCuspOppositeIndex b)) := by
  rw [ramifiedCusp_neg_inv_square,ramifiedCuspRoot_val]
  cases b
  · simp [ramifiedCuspDirectIndex,ramifiedCuspOppositeIndex,pow_two]
  · simp only [ramifiedCuspDirectIndex,ramifiedCuspOppositeIndex,ite_true,pow_one]
    rw [mul_neg,←pow_add,show 2+2=4 from rfl,ramified_omega_four]

lemma ramifiedCusp_direct_period_constant (b:Bool) :
    (3:Eis)∣onceCuspScale (ramifiedCuspScaleUnit b)+
      ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0*(ramifiedCuspRoot b:Eis) := by
  cases b
  · refine ⟨0,?_⟩
    simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedCuspDirectIndex,
      ramifiedAffineParameter,ramifiedOmegaUnit_val]
    ring
  · refine ⟨ramifiedTraceLambda*omega^2,?_⟩
    simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedCuspDirectIndex,
      ramifiedAffineParameter,ramifiedOmegaUnit_val]
    ring

lemma ramifiedCusp_opposite_period_constant (b:Bool) :
    (3:Eis)∣onceCuspScale (ramifiedCuspScaleUnit b)+
      ramifiedAffineParameter (ramifiedCuspOppositeIndex b) 0*(-(ramifiedCuspRoot b:Eis)) := by
  cases b
  · refine ⟨-(omega*ramifiedTraceLambda),?_⟩
    simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedCuspOppositeIndex,
      ramifiedAffineParameter,ramifiedOmegaUnit_val]
    ring
  · refine ⟨0,?_⟩
    simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedCuspOppositeIndex,
      ramifiedAffineParameter,ramifiedOmegaUnit_val]
    ring

lemma ramifiedCusp_unit_period_constant (b:Bool) :
    (3:Eis)∣onceCuspScale (ramifiedCuspScaleUnit b)+
      ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0 := by
  cases b
  · refine ⟨-omega^2,?_⟩
    simp [ramifiedCuspScaleUnit,ramifiedCuspDirectIndex,onceCuspScale,Units.val_neg,
      ramifiedOmegaUnit_val,ramifiedAffineParameter,Nat.cast_one,one_mul,sub_zero,
      ramifiedTraceLambda]
    linear_combination ramified_omega_relation
  · refine ⟨-omega^2,?_⟩
    simp only [ramifiedCuspScaleUnit,ramifiedCuspDirectIndex,ite_true,onceCuspScale,Units.val_pow_eq_pow_val,
      ramifiedOmegaUnit_val,ramifiedAffineParameter,Nat.cast_ofNat,Nat.cast_zero,sub_zero,
      ramifiedTraceLambda]
    linear_combination (2*omega+2)*ramified_omega_relation

lemma ramifiedCusp_support_standard (b:Bool) (h:Eis) :
    (3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b) ↔
      (3:Eis)∣h-(if b then -(omega-1) else omega-1) := by
  have hc:(3:Eis)∣onceCuspScale (ramifiedCuspScaleUnit b)-(if b then -(omega-1) else omega-1):=by
    cases b
    · refine ⟨1,?_⟩
      simp [ramifiedCuspScaleUnit,onceCuspScale,Units.val_neg,ramifiedOmegaUnit_val,
        ramifiedTraceLambda]
      linear_combination -2*ramified_omega_relation
    · refine ⟨0,?_⟩
      simp only [ramifiedCuspScaleUnit,ite_true,onceCuspScale,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,
        ramifiedTraceLambda]
      linear_combination (2*omega-1)*ramified_omega_relation
  constructor
  · intro hh
    convert! dvd_add hh hc using 1 ;ring
  · intro hh
    convert! dvd_sub hh hc using 1 ;ring

end

open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O


lemma ramifiedCusp_direct_base (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) :
    (3:Eis)∣h+ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0*(ramifiedCuspRoot b:Eis) := by
  convert! dvd_add hf (ramifiedCusp_direct_period_constant b) using 1 ;ring

lemma ramifiedCusp_opposite_base (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) :
    (3:Eis)∣h+ramifiedAffineParameter (ramifiedCuspOppositeIndex b) 0*(-(ramifiedCuspRoot b:Eis)) := by
  convert! dvd_add hf (ramifiedCusp_opposite_period_constant b) using 1 ;ring

lemma ramifiedCusp_unit_base (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) :
    (3:Eis)∣h+ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0 := by
  convert! dvd_add hf (ramifiedCusp_unit_period_constant b) using 1 ;ring

end CubicEisenstein


end

end OAI

end


