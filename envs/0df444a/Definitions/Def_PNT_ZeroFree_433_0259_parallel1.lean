-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0259_parallel1
-- name    : PNT_ZeroFree_433_0259_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:21:11.498985+00:00
-- url     : https://prove2.me/theorems/6de71d81-ff19-48d2-a405-f7e7dbd305f9
-- title:
--   Zero-free region foundations: Eisenstein.SquarefreeCoefficients [0259_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.SquarefreeCoefficients
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/SquarefreeCoefficients.lean#L86-L550

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0076
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0124
import Definitions.Def_PNT_ZeroFree_433_0126
import Definitions.Def_PNT_ZeroFree_433_0127
import Definitions.Def_PNT_ZeroFree_433_0129_parallel2
import Definitions.Def_PNT_ZeroFree_433_0131_parallel1
import Definitions.Def_PNT_ZeroFree_433_0211_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0224_parallel1
import Definitions.Def_PNT_ZeroFree_433_0271_parallel1
import Definitions.Def_PNT_ZeroFree_433_0273_parallel1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/SquarefreeCoefficients.lean
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
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma primaryGenerator_squarefree_support (I:Ideal Eis) (hI:primaryGenerator I≠0)
    (hsq:Squarefree I) : primaryGenerator I=∏P∈primeSupport I,primaryPrime P := by
  have hI0:=primaryGenerator_ne_zero_ideal I hI
  have hn: (UniqueFactorizationMonoid.normalizedFactors I).Nodup:=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp hsq
  have hv:(primeSupport I).val=UniqueFactorizationMonoid.normalizedFactors I:=by
    simpa only [primeSupport, Multiset.toFinset_val] using hn.dedup
  unfold primaryGenerator
  rw [if_neg hI0]
  change _=((primeSupport I).val.map primaryPrime).prod
  rw [hv]

lemma primaryPrime_isPrime_of_mem (I P:Ideal Eis) (hI:primaryGenerator I≠0)
    (hP:P∈primeSupport I) : Prime (primaryPrime P) := by
  have hp0:=primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP)
  have hs:=primaryPrime_spec P hp0
  let:P.IsMaximal:=hs.1
  apply (Ideal.span_singleton_prime hp0).mp
  rw [hs.2.2.1]
  infer_instance

lemma primaryPrime_support_coprime (I:Ideal Eis) (hI:primaryGenerator I≠0)
    (P:Ideal Eis) (hP:P∈primeSupport I) (Q:Ideal Eis) (hQ:Q∈primeSupport I) (hne:P≠Q) :
    IsCoprime (primaryPrime P) (primaryPrime Q) := by
  have hp:=primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))
  have hq:=primaryPrime_spec Q (primaryPrime_factor_ne_zero I Q hI (Multiset.mem_toFinset.mp hQ))
  let:P.IsMaximal:=hp.1
  let:Q.IsMaximal:=hq.1
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [hp.2.2.1,hq.2.2.1]
  exact Ideal.isCoprime_of_isMaximal hne


end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O


def thetaSquarefreePart (I:Ideal Eis) : Ideal Eis :=
  ∏P∈(primeSupport I).filter (fun P=>(normalizedFactors I).count P%3=1),P

def thetaCubePart (I:Ideal Eis) : Ideal Eis :=
  ∏P∈primeSupport I,P^((normalizedFactors I).count P/3)

lemma thetaSquarefreePart_squarefree (I:Ideal Eis) : Squarefree (thetaSquarefreePart I) := by
  apply IdealMobiusDivisorSum.squarefree_support_product
  exact Finset.filter_subset _ _

lemma thetaParts_mul_cube (I:Ideal Eis) (hI:I≠0)
    (he:∀P∈normalizedFactors I,(normalizedFactors I).count P%3≠2) :
    thetaSquarefreePart I*thetaCubePart I^3=I := by
  rw [thetaSquarefreePart,Finset.prod_filter,thetaCubePart,←Finset.prod_pow,←Finset.prod_mul_distrib]
  calc
    _=∏P∈primeSupport I,P^((normalizedFactors I).count P):=by
      apply Finset.prod_congr rfl
      intro P hP
      have hp:=he P (Multiset.mem_toFinset.mp hP)
      have hm:(normalizedFactors I).count P%3=0 ∨ (normalizedFactors I).count P%3=1:=by omega
      rcases hm with hm|hm
      · rw [if_neg (by omega),one_mul,←pow_mul]
        congr 1
        omega
      · rw [if_pos hm,←pow_mul,←pow_succ']
        congr 1
        omega
    _=(normalizedFactors I).prod:=(Finset.prod_multiset_count (normalizedFactors I)).symm
    _=I:=Ideal.prod_normalizedFactors_eq_self hI


end


section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance p2mAnonymous_PNT_ZeroFree_433_0259_parallel1_1 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units


end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance p2mAnonymous_PNT_ZeroFree_433_0259_parallel1_2 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedDecayRatio : ℝ := (3:ℝ)^(-(1/3:ℝ))

lemma ramifiedDecayRatio_pos : 0<ramifiedDecayRatio :=
  Real.rpow_pos_of_pos (by norm_num) _

lemma ramifiedDecayRatio_lt_one : ramifiedDecayRatio<1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

lemma explicitRamifiedCoefficient_norm_le (h:Eis) (u:Eisˣ) (n:ℕ) :
    ‖explicitRamifiedCoefficient h u n‖≤(3^n:ℕ) := by
  unfold explicitRamifiedCoefficient
  split_ifs with hd
  · dsimp only
    split_ifs <;> simp [residueAdditive,breveE_norm]
  · simp

lemma ramifiedWeight_norm_scalar (n:ℕ) :
    ‖((3^n:ℕ):ℂ)^(-(4/3:ℂ))‖*(3^n:ℕ)=ramifiedDecayRatio^n := by
  have ha:0<(3:ℝ)^n:=pow_pos (by norm_num) _
  have hn:‖((3:ℂ)^n)^(-(4/3:ℂ))‖=((3:ℝ)^n)^(-(4/3:ℝ)):=by
    have he:=Complex.norm_cpow_eq_rpow_re_of_pos ha (-(4/3:ℂ))
    have hre:(-(4/3:ℂ)).re=-(4/3:ℝ):=by norm_num
    rw [hre] at he
    simpa only [Complex.ofReal_pow,Complex.ofReal_ofNat] using he
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  rw [hn]
  calc
    ((3:ℝ)^n)^(-(4/3:ℝ))*(3:ℝ)^n=
        ((3:ℝ)^n)^(-(4/3:ℝ))*((3:ℝ)^n)^(1:ℝ):=by rw [Real.rpow_one]
    _=((3:ℝ)^n)^(-(1/3:ℝ)):=by
      rw [←Real.rpow_add ha]
      congr 1
      norm_num
    _=(3:ℝ)^((n:ℝ)*(-(1/3:ℝ))):=(Real.rpow_natCast_mul (by norm_num) n _).symm
    _=(3:ℝ)^((-(1/3:ℝ))*(n:ℝ)):=by rw [mul_comm]
    _=ramifiedDecayRatio^n:=by
      rw [Real.rpow_mul (by norm_num),Real.rpow_natCast]
      rfl


end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance p2mAnonymous_PNT_ZeroFree_433_0259_parallel1_3 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedSourceFamilyConstant : ℝ :=
  (6*ramifiedDecayRatio^2/(1-ramifiedDecayRatio)+3)/(4*(9*Real.sqrt 3/2))

lemma ramifiedSourceFamilyConstant_nonneg : 0≤ramifiedSourceFamilyConstant := by
  have ht:0<1-ramifiedDecayRatio:=sub_pos.mpr ramifiedDecayRatio_lt_one
  unfold ramifiedSourceFamilyConstant
  positivity


end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def extraPeriodWitness : levelThree := by
  let M:SL(2,Eis):=⟨!![1+3*omega,3*omega^2;-3,1-3*omega],by
    rw [Matrix.det_fin_two_of]
    ring⟩
  refine ⟨M,levelThree_of_entries M ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨omega,by change 1+3*omega-1=3*omega;ring⟩
  · exact ⟨omega^2,by change 3*omega^2-0=3*omega^2;ring⟩
  · exact ⟨-1,by change -3-(0:Eis)=3*(-1);ring⟩
  · exact ⟨-omega,by change 1-3*omega-1=3*(-omega);ring⟩

def rationalLowerMinusThree : SL(2,ℤ):=⟨!![1,0;-3,1],by simp [Matrix.det_fin_two]⟩

lemma extraPeriodWitness_factor :
    integralComplexMatrix (extraPeriodWitness:SL(2,Eis))=
      complexTranslation (-eisEmbedding omega)*
        integralComplexMatrix (rationalEmbedding rationalLowerMinusThree)*
        complexTranslation (eisEmbedding omega) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, integralComplexMatrix_apply,
    rationalEmbedding, Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;>
    simp [extraPeriodWitness, rationalLowerMinusThree, complexTranslation, map_ofNat] <;> ring


end CubicEisenstein

end

end OAI

end


