-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0248_parallel1
-- name    : PNT_ZeroFree_433_0248_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:28:45.463297+00:00
-- url     : https://prove2.me/theorems/97823040-53d6-4675-a56f-5574a97ea2c1
-- title:
--   Zero-free region foundations: Eisenstein.CubeCuspAverage [0248_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.CubeCuspAverage
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CubeCuspAverage.lean#L143-L469

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0017
import Definitions.Def_PNT_ZeroFree_433_0046_1_1
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0089
import Definitions.Def_PNT_ZeroFree_433_0100
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0124_parallel1
import Definitions.Def_PNT_ZeroFree_433_0130
import Definitions.Def_PNT_ZeroFree_433_0174_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0223_parallel1
import Definitions.Def_PNT_ZeroFree_433_0224_parallel1_1_1
import Definitions.Def_PNT_ZeroFree_433_0241_parallel1
import Definitions.Def_PNT_ZeroFree_433_0242_parallel1
import Definitions.Def_PNT_ZeroFree_433_0243_parallel1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel2
import Definitions.Def_PNT_ZeroFree_433_0246_parallel1
import Definitions.Def_PNT_ZeroFree_433_0249_parallel1
import Definitions.Def_PNT_ZeroFree_433_0255_parallel1
import Definitions.Def_PNT_ZeroFree_433_0259_parallel1
import Definitions.Def_PNT_ZeroFree_433_0275_parallel2
import Definitions.Def_PNT_ZeroFree_433_0280_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CubeCuspAverage.lean
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


section

open scoped Classical MatrixGroups BigOperators
namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def cubeCuspTriangular {A:SL(2,Eis)} {p q:Eis} (d:CubeCuspData A p q) (hp:p≠0) : SL(2,ℂ) :=
  (integralComplexMatrix d.matrix)⁻¹*cubeAverageMatrix p hp q*integralComplexMatrix A

lemma cubeCuspTriangular_factor {A:SL(2,Eis)} {p q:Eis} (d:CubeCuspData A p q) (hp:p≠0) :
    cubeAverageMatrix p hp q*integralComplexMatrix A=
      integralComplexMatrix d.matrix*cubeCuspTriangular d hp := by
  unfold cubeCuspTriangular
  group

lemma cubeCuspTriangular_entries {A:SL(2,Eis)} {p q:Eis} (d:CubeCuspData A p q) (hp:p≠0) :
    cubeCuspTriangular d hp 0 0=(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val ∧
    cubeCuspTriangular d hp 1 0=0 ∧
    cubeCuspTriangular d hp 1 1=(cubeDilationRoot p)⁻¹*eisEmbedding p^(3-d.exponent.val) := by
  let B:=cubeAverageMatrix p hp q*integralComplexMatrix A
  have hz:=cubeDilationRoot_ne_zero p hp
  have he:=cubeDilationRoot_sq p
  have hx:eisEmbedding (A 0 0)+3*eisEmbedding q*eisEmbedding (A 1 0)=
      eisEmbedding p^d.exponent.val*eisEmbedding (d.matrix 0 0):=by
    simpa only [map_add,map_mul,map_pow,map_ofNat] using congrArg eisEmbedding d.first
  have hy:eisEmbedding p^3*eisEmbedding (A 1 0)=
      eisEmbedding p^d.exponent.val*eisEmbedding (d.matrix 1 0):=by
    simpa only [map_mul,map_pow] using congrArg eisEmbedding d.second
  have hB0:B 0 0=(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val*eisEmbedding (d.matrix 0 0):=by
    change (∑k:Fin 2,cubeAverageMatrix p hp q 0 k*integralComplexMatrix A k 0)=_
    rw [Fin.sum_univ_two]
    simp only [cubeAverageMatrix_entries,integralComplexMatrix_apply,Matrix.of_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    linear_combination (cubeDilationRoot p)⁻¹*hx
  have hB1:B 1 0=(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val*eisEmbedding (d.matrix 1 0):=by
    change (∑k:Fin 2,cubeAverageMatrix p hp q 1 k*integralComplexMatrix A k 0)=_
    rw [Fin.sum_univ_two]
    simp only [cubeAverageMatrix_entries,integralComplexMatrix_apply,Matrix.cons_val_one,
      Matrix.cons_val_zero,Matrix.cons_val_fin_one,Matrix.of_apply,zero_mul,zero_add]
    rw [mul_assoc,←hy,←he]
    field_simp
  have hinv:(integralComplexMatrix d.matrix : Matrix (Fin 2) (Fin 2) ℂ)⁻¹=
      !![eisEmbedding (d.matrix 1 1),-eisEmbedding (d.matrix 0 1);
        -eisEmbedding (d.matrix 1 0),eisEmbedding (d.matrix 0 0)] := by
    rw [Matrix.inv_def,Matrix.SpecialLinearGroup.det_coe,Ring.inverse_one,one_smul,Matrix.adjugate_fin_two]
    rfl
  have hT:cubeCuspTriangular d hp=(integralComplexMatrix d.matrix)⁻¹*B:=by
    dsimp [cubeCuspTriangular,B]
    group
  have hdet:eisEmbedding (d.matrix 0 0)*eisEmbedding (d.matrix 1 1)-
      eisEmbedding (d.matrix 0 1)*eisEmbedding (d.matrix 1 0)=1:=by
    have hd:d.matrix 0 0*d.matrix 1 1-d.matrix 0 1*d.matrix 1 0=1:=by
      simpa only [Matrix.det_fin_two] using d.matrix.property
    simpa only [map_sub,map_mul,map_one] using congrArg eisEmbedding hd
  have h00:cubeCuspTriangular d hp 0 0=(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val:=by
    rw [hT]
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,integralComplexMatrix_apply]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.of_apply,hB0,hB1]
    linear_combination (cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val*hdet
  have h10:cubeCuspTriangular d hp 1 0=0:=by
    rw [hT]
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,integralComplexMatrix_apply]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.of_apply,hB0,hB1]
    ring
  refine ⟨h00,h10,?_⟩
  have hd:cubeCuspTriangular d hp 0 0*cubeCuspTriangular d hp 1 1=1:=by
    simpa only [Matrix.det_fin_two,h10,mul_zero,sub_zero] using (cubeCuspTriangular d hp).property
  rw [h00] at hd
  have hnon:(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val≠0:=
    mul_ne_zero (inv_ne_zero hz) (pow_ne_zero _ (eisEmbedding_ne_zero hp))
  apply mul_left_cancel₀ hnon
  rw [hd]
  have hpow:eisEmbedding p^d.exponent.val*eisEmbedding p^(3-d.exponent.val)=eisEmbedding p^3:=by
    rw [←pow_add,Nat.add_sub_of_le (by omega:d.exponent.val≤3)]
  calc
    1=(cubeDilationRoot p)⁻¹^2*eisEmbedding p^3:=by rw [←he,inv_pow,inv_mul_cancel₀ (pow_ne_zero 2 hz)]
    _=_:=by rw [←hpow];ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeCuspTriangular_integral_scale {A:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData A p q) (hp:p≠0) :
    (cubeCuspTriangular d hp 0 0/cubeCuspTriangular d hp 1 1)*eisEmbedding (p^3)=
      eisEmbedding (p^(2*d.exponent.val)) := by
  obtain ⟨h00,_,h11⟩:=cubeCuspTriangular_entries d hp
  rw [h00,h11,map_pow,map_pow]
  have he:eisEmbedding p≠0:=eisEmbedding_ne_zero hp
  have hz:=cubeDilationRoot_ne_zero p hp
  have hpow:eisEmbedding p^3=eisEmbedding p^d.exponent.val*eisEmbedding p^(3-d.exponent.val):=by
    rw [←pow_add,Nat.add_sub_of_le (by omega:d.exponent.val≤3)]
  rw [hpow]
  have htwo:eisEmbedding p^(2*d.exponent.val)=(eisEmbedding p^d.exponent.val)^2:=by
    rw [mul_comm 2 d.exponent.val,pow_mul]
  rw [htwo]
  field_simp


end CubicEisenstein

namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma levelTwo_primary_shift_cases (A:levelTwo) :
    ∃t:Fin 2, lambda^2∣((A:SL(2,Eis)) 0 0+(t.val:Eis)*(A:SL(2,Eis)) 1 0)-1 ∨
      lambda^2∣(-((A:SL(2,Eis)) 0 0+(t.val:Eis)*(A:SL(2,Eis)) 1 0))-1 := by
  rcases integer_congruence_primary_cases ((A:SL(2,Eis)) 0 0)
    (levelTwoRight A 0 0) (levelTwo_entry_integer A 0 0) with ha|ha|ha
  · rcases integer_congruence_primary_cases ((A:SL(2,Eis)) 1 0)
      (levelTwoRight A 1 0) (levelTwo_entry_integer A 1 0) with hc|hc|hc
    · have h1:(3:Eis)∣1:=by
        have hd:(A:SL(2,Eis)) 0 0*(A:SL(2,Eis)) 1 1-
          (A:SL(2,Eis)) 0 1*(A:SL(2,Eis)) 1 0=1:=by
            simpa only [Matrix.det_fin_two] using (A:SL(2,Eis)).property
        rw [←hd]
        exact dvd_sub (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hc _)
      have hl:lambda∣(1:Eis):=(dvd_pow_self lambda (by decide:2≠0)).trans
        (lambda_sq_dvd_three.trans h1)
      exact (residue_lambda_prime.not_isUnit (isUnit_of_dvd_one hl)).elim
    · refine ⟨1,Or.inl ?_⟩
      convert! dvd_add (lambda_sq_dvd_three.trans ha) hc using 1 ; norm_num ; ring
    · refine ⟨1,Or.inr ?_⟩
      convert! dvd_add (dvd_neg.mpr (lambda_sq_dvd_three.trans ha)) hc using 1 ; norm_num ; ring
  · exact ⟨0,Or.inl (by simpa using ha)⟩
  · exact ⟨0,Or.inr (by simpa using ha)⟩

end CubicKubota


namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma matrix_mul_upper_first_column (A T:SL(2,Eis)) (hT:T 1 0=0) (i:Fin 2) :
    (A*T) i 0=A i 0*T 0 0 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,hT,mul_zero,add_zero]

namespace CubeCuspData
variable {A:SL(2,Eis)} {p q:Eis}

def right_upper (d:CubeCuspData A p q) (T:SL(2,Eis)) (hT:T 1 0=0) :
    CubeCuspData (A*T) p q where
  exponent:=d.exponent
  matrix:=d.matrix*T
  first:=by
    simp only [matrix_mul_upper_first_column _ T hT]
    linear_combination d.first*(T 0 0)
  second:=by
    simp only [matrix_mul_upper_first_column _ T hT]
    linear_combination d.second*(T 0 0)
  congruent:=by
    have he:(d.matrix*T)*(A*T)⁻¹=d.matrix*A⁻¹:=by group
    rw [he]
    exact d.congruent

lemma right_upper_exponent (d:CubeCuspData A p q) (T:SL(2,Eis)) (hT:T 1 0=0) :
    (d.right_upper T hT).exponent=d.exponent := rfl

lemma right_upper_character (d:CubeCuspData A p q) (T:SL(2,Eis)) (hT:T 1 0=0) :
    complexCharacter ⟨(d.right_upper T hT).matrix*(A*T)⁻¹,(d.right_upper T hT).congruent⟩=
      complexCharacter ⟨d.matrix*A⁻¹,d.congruent⟩ := by
  apply congrArg complexCharacter
  apply Subtype.ext
  change (d.matrix*T)*(A*T)⁻¹=d.matrix*A⁻¹
  group

end CubeCuspData
end CubicKubota
end

namespace CubicEisenstein

section

open MeasureTheory
open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O


lemma cubeAverage_cusp_integral (p:Eis) (hp:p≠0) (F:HyperbolicSpace→ℂ) (hF:Continuous F)
    (M:SL(2,Eis)) (b:Eis) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp F
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding b*z)) v hv))=
    (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
      ∑' r:Eis⧸Ideal.span {p^3}, ∫z in periodDomain,
        F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) •
          (integralComplexMatrix M • upperPoint (3*(eisEmbedding b*z)) v hv)) := by
  let:Finite (Eis⧸Ideal.span {p^3}):=finite_quotient_span (pow_ne_zero 3 hp)
  let:Fintype (Eis⧸Ideal.span {p^3}):=Fintype.ofFinite _
  let c:ℂ→UpperCoordinates:=fun z=>⟨(3*(eisEmbedding b*z),v),hv⟩
  have hc:Continuous c:=by
    apply Continuous.subtype_mk
    exact (continuous_const.mul (continuous_const.mul continuous_id)).prodMk continuous_const
  have hi (r:Eis⧸Ideal.span {p^3}):IntegrableOn (fun z=>
        F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) •
          (integralComplexMatrix M • upperPoint (3*(eisEmbedding b*z)) v hv))) periodDomain:=by
    apply periodDomain_integrable_of_continuous
    have hh:=(continuous_translatedUpperCoordinates
      (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r)*integralComplexMatrix M)).comp hc
    simpa only [Function.comp_def,c,mul_smul] using hF.comp hh
  unfold cubeAverage
  simp only [tsum_fintype]
  rw [integral_const_mul]
  congr 1
  exact integral_finsetSum _ (fun r _=>hi r)

end


end CubicEisenstein


end

end OAI

end


