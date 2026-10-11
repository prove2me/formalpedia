-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0243_parallel1
-- name    : PNT_ZeroFree_433_0243_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:24:14.266353+00:00
-- url     : https://prove2.me/theorems/3c3d82ea-bef3-4110-b324-90cccd61b2fb
-- title:
--   Zero-free region foundations: Eisenstein.CubeResidueStrata [0243_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.CubeResidueStrata
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CubeResidueStrata.lean#L160-L586

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0017
import Definitions.Def_PNT_ZeroFree_433_0044
import Definitions.Def_PNT_ZeroFree_433_0046_1_1
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0068_1
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0093
import Definitions.Def_PNT_ZeroFree_433_0123_parallel1
import Definitions.Def_PNT_ZeroFree_433_0126_parallel1
import Definitions.Def_PNT_ZeroFree_433_0132_parallel1
import Definitions.Def_PNT_ZeroFree_433_0143_parallel1
import Definitions.Def_PNT_ZeroFree_433_0148_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel1
import Definitions.Def_PNT_ZeroFree_433_0231_parallel1
import Definitions.Def_PNT_ZeroFree_433_0241_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CubeResidueStrata.lean
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

namespace CubicEisenstein


open scoped BigOperators Classical MatrixGroups Matrix

section
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal GoodElement)
local notation "Eis" => ActualEisensteinCubic.O
local notation "ramLambda" => (omega-1:Eis)

lemma halfPrimary_lambda_dvd_three : ramLambda ∣ (3:Eis) := by
  exact (dvd_pow_self ramLambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three

lemma halfPrimary_lambda_not_dvd_one : ¬ramLambda ∣ (1:Eis) := by
  intro h
  exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (isUnit_of_dvd_one h)

lemma halfPrimary_omega_pow (j:ℕ) : ramLambda ∣ omega^j-1 := by
  simpa only [one_pow] using sub_dvd_pow_sub_pow omega (1:Eis) j

lemma halfPrimary_not_negative (j:ℕ) : ¬ramLambda ∣ -(omega^j)-1 := by
  intro h
  have h2 : ramLambda ∣ (2:Eis) := by
    have hh:=dvd_add h (halfPrimary_omega_pow j)
    convert! dvd_neg.mpr hh using 1 ;ring
  apply halfPrimary_lambda_not_dvd_one
  convert! dvd_sub halfPrimary_lambda_dvd_three h2 using 1 ;ring

abbrev HalfPrimary := {b:Eis // ramLambda ∣ b-1}

lemma halfPrimary_ne_zero (b:HalfPrimary) : b.val≠0 := by
  intro h
  apply halfPrimary_lambda_not_dvd_one
  simpa only [h,zero_sub,dvd_neg] using b.2

lemma halfPrimary_not_dvd (b:HalfPrimary) : ¬ramLambda∣b.val := by
  intro h
  apply halfPrimary_lambda_not_dvd_one
  convert! dvd_sub h b.2 using 1 ;ring

def halfPrimaryFromAssociate (p:Fin 3×PrimaryLower) : HalfPrimary :=
  ⟨omega^p.1.val*p.2.val,by
    have ha:ramLambda∣p.2.val-1:=halfPrimary_lambda_dvd_three.trans p.2.2
    convert! dvd_add ((halfPrimary_omega_pow p.1.val).mul_right p.2.val) ha using 1 ;ring⟩

lemma halfPrimaryFromAssociate_injective : Function.Injective halfPrimaryFromAssociate := by
  intro p q hpq
  have he:omega^p.1.val*p.2.val=omega^q.1.val*q.2.val:=congrArg Subtype.val hpq
  have hunit (j:Fin 3):IsUnit (omega^j.val):=(omega_primitive.isUnit (by decide)).pow _
  have hs:(Ideal.span {p.2.val}:Ideal Eis)=Ideal.span {q.2.val}:=by
    simpa only [Ideal.span_singleton_mul_left_unit (hunit p.1),
      Ideal.span_singleton_mul_left_unit (hunit q.1)] using
      congrArg (fun z:Eis=>(Ideal.span {z}:Ideal Eis)) he
  have hab:p.2=q.2:=by
    apply Subtype.ext
    have hg:=congrArg primaryGenerator hs
    simpa only [primaryGenerator_span p.2.val (primaryLower_ne_zero p.2) (primaryLower_primary p.2),
      primaryGenerator_span q.2.val (primaryLower_ne_zero q.2) (primaryLower_primary q.2)] using hg
  have hj:p.1=q.1:=by
    apply Fin.ext
    apply omega_primitive.pow_inj p.1.isLt q.1.isLt
    rw [hab] at he
    exact mul_right_cancel₀ (primaryLower_ne_zero q.2) he
  exact Prod.ext hj hab


end

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def unitCuspUpper (b : Eis) : SL(2,Eis) := ⟨!![1,b;0,1],by simp [Matrix.det_fin_two]⟩
def unitCuspDiagonal (u : Eisˣ) : SL(2,Eis) := ⟨!![(u:Eis),0;0,(↑u⁻¹:Eis)],by
  simp [Matrix.det_fin_two]⟩


lemma unitCuspDiagonal_norm (u : Eisˣ) :
    ‖eisEmbedding (u:Eis)‖=1 ∧ ‖eisEmbedding (↑u⁻¹:Eis)‖=1 :=
  ⟨GaussGeneratorTransport.norm_eisEmbedding_unit u,
    GaussGeneratorTransport.norm_eisEmbedding_unit u⁻¹⟩

end CubicEisenstein

open scoped Classical MatrixGroups
namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

abbrev CubeResidueStrata (p:Eis) := Σj:Fin 4,CubicUnitResidue (p^(3-j.val))

def cubeResidueStratumMap (p:Eis) (x:CubeResidueStrata p) : Eis⧸Ideal.span {p^3} :=
  Ideal.Quotient.mk _ (p^x.1.val * GaussianShiftedPartition.representative (p^(3-x.1.val)) x.2.1)


end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def cubeStratumSymbol (p C:Eis) (j:Fin 4) (b:CubicUnitResidue (p^(3-j.val))) : ℂ :=
  eisEmbedding (symbol (GaussianShiftedPartition.representative (p^(3-j.val)) b.1*C) (p^(3-j.val)))

lemma unit_stratum_symbol_gauss (p C:Eis) (hp:lambda^2∣p-1) (n:ℕ) :
    (∑' b:CubicUnitResidue (p^n),
      eisEmbedding (symbol (GaussianShiftedPartition.representative (p^n) b.1*C) (p^n))) =
      cubicUnitGaussSum 0 (p^n)*eisEmbedding (symbol C (p^n)) := by
  rw [cubicUnitGaussSum]
  simp only [mul_zero,residueAdditive,map_zero,cuspFrequency,zero_div,zero_mul,
    AddChar.map_zero_eq_one,mul_one]
  rw [←tsum_mul_right]
  apply tsum_congr
  intro b
  rw [symbol_mul_numerator _ _ _ (primary_pow_congruence p hp n),map_mul]


end CubicEisenstein

open scoped Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma comparison_mod_three (A N:SL(2,Eis)) (hNA:N*A⁻¹∈levelThree) (i j:Fin 2) :
    (3:Eis)∣N i j-A i j := by
  have hh:Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (N*A⁻¹)=1:=hNA
  rw [map_mul,map_inv] at hh
  have he:=mul_inv_eq_one.mp hh
  have he' :=congrArg (fun B:SL(2,Eis⧸Ideal.span {(3:Eis)})=>B i j) he
  exact Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp he')

lemma comparison_primary (A N:SL(2,Eis)) (hNA:N*A⁻¹∈levelThree)
    (hA:lambda^2∣A 0 0-1) : lambda^2∣N 0 0-1 := by
  have hh:=lambda_sq_dvd_three.trans (comparison_mod_three A N hNA 0 0)
  simpa only [sub_add_sub_cancel] using dvd_add hh hA

lemma comparison_levelTwo (A:levelTwo) (N:SL(2,Eis))
    (hNA:N*(A:SL(2,Eis))⁻¹∈levelThree) : N∈levelTwo := by
  have hh:=Subgroup.mul_mem levelTwo (levelThree_le_levelTwo hNA) A.property
  simpa only [inv_mul_cancel_right] using hh


lemma cube_exponent_zero_of_lower_divisible (A N:SL(2,Eis)) (p q:Eis) (j:ℕ)
    (hp:Prime p) (hC:p∣A 1 0)
    (hx:A 0 0+3*q*A 1 0=p^j*N 0 0) : j=0 := by
  by_contra hj
  have hpx:p∣A 0 0+3*q*A 1 0:=by
    rw [hx]
    exact dvd_mul_of_dvd_left (dvd_pow_self p hj) (N 0 0)
  have hpa:p∣A 0 0:=by
    simpa only [add_sub_cancel_right] using dvd_sub hpx (dvd_mul_of_dvd_right hC (3*q))
  have hone:p∣(1:Eis):=by
    have hh:=dvd_sub (dvd_mul_of_dvd_left hpa (A 1 1)) (dvd_mul_of_dvd_right hC (A 0 1))
    have hd:A 0 0*A 1 1-A 0 1*A 1 0=1:=by
      simpa only [Matrix.det_fin_two] using A.property
    rwa [hd] at hh
  exact hp.not_isUnit (isUnit_of_dvd_one hone)

end CubicKubota

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma cube_affine_coefficient_unit (p C:Eis) (hprimary:lambda^2∣p-1) (hC:IsCoprime C p) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {p^3}) (3*C)) := by
  obtain ⟨t,ht⟩:=(three_dvd_primary_sub_one p hprimary)
  have hp3:IsCoprime p (3:Eis):=by
    refine ⟨1,-t,?_⟩
    linear_combination ht
  apply (isUnit_quotient_span_iff _ _).mpr
  exact hp3.pow_left.mul_right hC.symm.pow_left

def cubeCuspAffineEquiv (p A C:Eis) (hprimary:lambda^2∣p-1) (hC:IsCoprime C p) :
    (Eis⧸Ideal.span {p^3})≃(Eis⧸Ideal.span {p^3}) := by
  let a:=Ideal.Quotient.mk (Ideal.span {p^3}) A
  let u:Units (Eis⧸Ideal.span {p^3}):=(cube_affine_coefficient_unit p C hprimary hC).unit
  exact {
    toFun:=fun r=>a+(u:_) * r
    invFun:=fun r=>(↑u⁻¹:_)*(r-a)
    left_inv:=by
      intro r
      simp only [add_sub_cancel_left,←mul_assoc,Units.inv_mul,one_mul]
    right_inv:=by
      intro r
      simp only [←mul_assoc,Units.mul_inv,one_mul,add_sub_cancel] }

lemma cubeCuspAffineEquiv_apply (p A C:Eis) (hprimary:lambda^2∣p-1) (hC:IsCoprime C p)
    (r:Eis⧸Ideal.span {p^3}) :
    cubeCuspAffineEquiv p A C hprimary hC r=
      Ideal.Quotient.mk (Ideal.span {p^3}) A+
        Ideal.Quotient.mk (Ideal.span {p^3}) (3*C)*r := by
  simp only [cubeCuspAffineEquiv,IsUnit.unit_spec]
  rfl

lemma cubeCuspAffineEquiv_mk (p A C q:Eis) (hprimary:lambda^2∣p-1) (hC:IsCoprime C p) :
    cubeCuspAffineEquiv p A C hprimary hC (Ideal.Quotient.mk _ q)=
      Ideal.Quotient.mk (Ideal.span {p^3}) (A+3*q*C) := by
  rw [cubeCuspAffineEquiv_apply]
  simp only [map_add,map_mul]
  ring

end CubicEisenstein

open scoped Classical MatrixGroups BigOperators
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

structure CubeCuspData (A:SL(2,Eis)) (p q:Eis) where
  exponent : Fin 4
  matrix : SL(2,Eis)
  first : A 0 0+3*q*A 1 0=p^exponent.val*matrix 0 0
  second : p^3*A 1 0=p^exponent.val*matrix 1 0
  congruent : matrix*A⁻¹∈levelThree


namespace CubeCuspData
variable {A:SL(2,Eis)} {p q:Eis}

lemma lower_eq (d:CubeCuspData A p q) (hp:p≠0) :
    d.matrix 1 0=p^(3-d.exponent.val)*A 1 0 := by
  apply mul_left_cancel₀ (pow_ne_zero d.exponent.val hp)
  rw [←d.second,←mul_assoc,←pow_add,Nat.add_sub_of_le (by omega:d.exponent.val≤3)]

lemma unit_top (d:CubeCuspData A p q) (hp:p≠0) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {p^(3-d.exponent.val)}) (d.matrix 0 0)) := by
  apply (isUnit_quotient_span_iff _ _).mpr
  refine ⟨-d.matrix 0 1*A 1 0,d.matrix 1 1,?_⟩
  have hd:d.matrix 0 0*d.matrix 1 1-d.matrix 0 1*d.matrix 1 0=1:=by
    simpa only [Matrix.det_fin_two] using d.matrix.property
  rw [d.lower_eq hp] at hd
  linear_combination hd

def stratum (d:CubeCuspData A p q) (hp:p≠0) : CubeResidueStrata p :=
  ⟨d.exponent,⟨Ideal.Quotient.mk _ (d.matrix 0 0),d.unit_top hp⟩⟩


end CubeCuspData
end CubicKubota

end

end OAI

end


