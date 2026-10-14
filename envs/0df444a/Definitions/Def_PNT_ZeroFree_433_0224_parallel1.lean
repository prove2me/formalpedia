-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0224_parallel1
-- name    : PNT_ZeroFree_433_0224_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:59:09.344752+00:00
-- url     : https://prove2.me/theorems/f8a523c9-3dbd-4151-a818-c90d2403a50e
-- title:
--   Zero-free region foundations: Eisenstein.ScatteringResidues [0224_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.ScatteringResidues
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ScatteringResidues.lean#L523-L630

import Definitions.Def_PNT_ZeroFree_433_0224_parallel1_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ScatteringResidues.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace CubicEisenstein

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


section

open scoped BigOperators Classical
open EisensteinEmbedding (omega3)
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss CubicRamified
local notation "Eis" => ActualEisensteinCubic.O


lemma trace_third_coordinate (k:Eis) :
    eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
      3 (by norm_num) (Ideal.Quotient.mk _ k)=
      Complex.exp (2*Real.pi*Complex.I*((ActualEisensteinCoordinates.coords k).2:ℂ)/3) := by
  rw [eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  have hh:=breveE_real_trace_of_O 3 k
  norm_num at hh
  convert! hh using 1 ;simp only [map_ofNat] ;congr 1 ;ring

end

open scoped BigOperators Classical
open EisensteinEmbedding (omega3)
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_symbol_primaryCoord (u:Eisˣ) (n j:ℕ)
    (hu:(u:Eis)=omega^j ∨ (u:Eis)=-(omega^j)) (A B:ℤ) :
    symbol (u.val*lambda^n) (primaryCoord A B)=
      (cubicExp (2*A-B))^j*(cubicExp A)^n := by
  have hp:=primaryCoord_primary A B
  rw [symbol_mul_numerator _ _ _ hp,symbol_pow_numerator _ _ hp,
    symbol_lambda_eq_linearRay _ hp,linearRay_primaryCoord]
  norm_num only [one_mul,zero_mul,add_zero]
  congr 1
  rcases hu with hu|hu
  · rw [hu,symbol_pow_numerator _ _ hp,symbol_omega_eq_linearRay _ hp,
      linearRay_primaryCoord]
    ring_nf
  · rw [hu,symbol_neg_numerator _ _ hp,symbol_pow_numerator _ _ hp,
      symbol_omega_eq_linearRay _ hp,linearRay_primaryCoord]
    ring_nf

lemma ramified_symbol_at_one (u:Eisˣ) (n j:ℕ)
    (hu:(u:Eis)=omega^j ∨ (u:Eis)=-(omega^j)) :
    symbol (u.val*lambda^n) (1+3*(1:Eis))=omega^(2*j+n) := by
  have he:(1+3*(1:Eis))=primaryCoord 1 0:=by rw [primaryCoord_eq];norm_num
  rw [he,ramified_symbol_primaryCoord u n j hu]
  norm_num [cubicExp]
  simp only [show Int.toNat (2 : ℤ) = 2 from by decide]
  rw [←pow_mul,←pow_add]

lemma ramified_symbol_at_omega (u:Eisˣ) (n j:ℕ)
    (hu:(u:Eis)=omega^j ∨ (u:Eis)=-(omega^j)) :
    symbol (u.val*lambda^n) (1+3*omega)=omega^(2*j) := by
  have he:(1+3*omega)=primaryCoord 0 1:=by rw [primaryCoord_eq];norm_num
  rw [he,ramified_symbol_primaryCoord u n j hu]
  norm_num [cubicExp]
  simp only [show Int.toNat (2 : ℤ) = 2 from by decide]
  rw [←pow_mul]

lemma ramifiedFrequencyChar_mk (k:Eis) (u:Eisˣ) (n:ℕ) (x:Eis) :
    ramifiedFrequencyChar k u n (Ideal.Quotient.mk _ x)=
      eisEmbedding (symbol (u.val*lambda^n) (1+3*x))*
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        3 (by norm_num) (Ideal.Quotient.mk _ (k*x)) := by
  rw [ramifiedFrequencyChar,AddChar.mul_apply,ramifiedQuotientChar,
    IdealGaussCRT.quotientAddChar_mk,AddChar.mulShift_apply,←map_mul]
  rfl

lemma coords_mul_omega_second (k:Eis) :
    (ActualEisensteinCoordinates.coords (k*omega)).2=
      (ActualEisensteinCoordinates.coords k).1-(ActualEisensteinCoordinates.coords k).2 := by
  conv_lhs => rw [←ActualEisensteinCoordinates.eval_coords k]
  have hw:omega=ActualEisensteinCoordinates.eval 0 1:=by
    simp only [ActualEisensteinCoordinates.eval,Int.cast_zero,Int.cast_one,zero_add,one_mul]
    rfl
  rw [hw,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval]
  ring

def ramifiedCongruence (k:Eis) (j n:ℕ):Prop:=
  (3:ℤ)∣(2*(j:ℤ)+(n:ℤ)+(ActualEisensteinCoordinates.coords k).2) ∧
  (3:ℤ)∣(2*(j:ℤ)+(ActualEisensteinCoordinates.coords k).1-
    (ActualEisensteinCoordinates.coords k).2)

lemma ramifiedFrequencyChar_eq_one_iff (k:Eis) (u:Eisˣ) (n j:ℕ)
    (hu:(u:Eis)=omega^j ∨ (u:Eis)=-(omega^j)) :
    ramifiedFrequencyChar k u n=1 ↔ ramifiedCongruence k j n := by
  rw [third_character_eq_one_iff_basis,ramifiedFrequencyChar_mk,
    ramifiedFrequencyChar_mk,ramified_symbol_at_one u n j hu,
    ramified_symbol_at_omega u n j hu,map_pow,map_pow,eisEmbedding_omega_actual,
    mul_one,trace_third_coordinate,trace_third_coordinate,coords_mul_omega_second,
    omega3_pow_exp_eq_one_iff,omega3_pow_exp_eq_one_iff]
  unfold ramifiedCongruence
  push_cast
  simp only [add_sub_assoc]


def ramifiedUnitIndex (u:Eisˣ):Fin 3:=Classical.choose (unit_eq_sign_omega u)

lemma ramifiedUnitIndex_spec (u:Eisˣ) :
    (u:Eis)=omega^(ramifiedUnitIndex u).val ∨
      (u:Eis)=-(omega^(ramifiedUnitIndex u).val):=
  Classical.choose_spec (unit_eq_sign_omega u)

def explicitRamifiedCoefficient (h:Eis) (u:Eisˣ) (n:ℕ):ℂ:=
  if hd:u.val*lambda^n∣3*h then
    let k:=Classical.choose hd
    if ramifiedCongruence k (ramifiedUnitIndex u).val n then
      ((3^n:ℕ):ℂ)*residueAdditive k 3 1 else 0
  else 0


end CubicEisenstein

end

end OAI

end


