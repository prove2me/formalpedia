-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0257_parallel1
-- name    : PNT_ZeroFree_433_0257_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:33:20.71198+00:00
-- url     : https://prove2.me/theorems/6af703d3-ff9f-4a62-8dc0-8e8a34c3077d
-- title:
--   Zero-free region foundations: Eisenstein.PrimeRecurrence [0257_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.PrimeRecurrence
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/PrimeRecurrence.lean#L327-L554

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0088
import Definitions.Def_PNT_ZeroFree_433_0096
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0131
import Definitions.Def_PNT_ZeroFree_433_0131_parallel1
import Definitions.Def_PNT_ZeroFree_433_0132
import Definitions.Def_PNT_ZeroFree_433_0159_parallel1
import Definitions.Def_PNT_ZeroFree_433_0178_parallel1
import Definitions.Def_PNT_ZeroFree_433_0189_parallel1
import Definitions.Def_PNT_ZeroFree_433_0194_parallel1
import Definitions.Def_PNT_ZeroFree_433_0196_parallel1
import Definitions.Def_PNT_ZeroFree_433_0199_parallel1
import Definitions.Def_PNT_ZeroFree_433_0215_parallel2
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel2
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0220_parallel1
import Definitions.Def_PNT_ZeroFree_433_0224_parallel1
import Definitions.Def_PNT_ZeroFree_433_0227_parallel2
import Definitions.Def_PNT_ZeroFree_433_0229
import Definitions.Def_PNT_ZeroFree_433_0229_parallel2
import Definitions.Def_PNT_ZeroFree_433_0230_parallel1
import Definitions.Def_PNT_ZeroFree_433_0232_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0236_parallel1
import Definitions.Def_PNT_ZeroFree_433_0243_parallel2
import Definitions.Def_PNT_ZeroFree_433_0248_parallel1
import Definitions.Def_PNT_ZeroFree_433_0253_parallel1
import Definitions.Def_PNT_ZeroFree_433_0263_parallel2
import Definitions.Def_PNT_ZeroFree_433_0266_parallel1
import Definitions.Def_PNT_ZeroFree_433_0270_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/PrimeRecurrence.lean
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
open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma rational_inversion_complex :
    integralComplexMatrix (rationalEmbedding ModularGroup.S)=complexWeyl := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [integralComplexMatrix_apply, rationalEmbedding,
    Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.S, complexWeyl]


end

section
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O
local instance p2mAnonymous_PNT_ZeroFree_433_0257_parallel1_1 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

abbrev PrincipalRamifiedIndex (h:Eis) := Eisˣ × Fin (ramifiedFrequencyBound h+1)

def principalRamifiedIndex (h:Eis) (i:PrincipalRamifiedIndex h) : Eis :=
  h*(9*(i.1.val*lambda^(i.2.val+2)))

def principalRamifiedWeight (h:Eis) (i:PrincipalRamifiedIndex h) (s:ℂ) : ℂ :=
  ((3^(i.2.val+2):ℕ):ℂ)^(-s)*explicitRamifiedCoefficient h i.1 (i.2.val+2)

lemma principalRamifiedWeight_analytic (h:Eis) (i:PrincipalRamifiedIndex h) (s:ℂ) :
    AnalyticAt ℂ (principalRamifiedWeight h i) s := by
  apply AnalyticAt.mul _ analyticAt_const
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  exact Eventually.of_forall fun z=>(differentiableAt_id.neg).const_cpow
    (Or.inl (by exact_mod_cast (pow_ne_zero (i.2.val+2) (by norm_num : (3:ℕ)≠0))))


end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance p2mAnonymous_PNT_ZeroFree_433_0257_parallel1_2 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

lemma arithmeticResidueSum_frequency_cube (h c p:Eis) (hc:c≠0)
    (hlevel:(3:Eis)∣c) (hprimary:lambda^2∣p-1) (hcp:IsCoprime c p) :
    arithmeticResidueSum (h*p^3) c=arithmeticResidueSum h c := by
  have ht:denominatorCondition c p:=⟨hcp,three_dvd_lambda_sq.trans hprimary⟩
  have hb:(eisEmbedding (symbol c p))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime c p hprimary hcp,map_one]
  have h1:=arithmeticResidueSum_frequency_twist h c p hc hlevel ht
  have h2:=arithmeticResidueSum_frequency_twist (h*p) c p hc hlevel ht
  have h3:=arithmeticResidueSum_frequency_twist (h*p*p) c p hc hlevel ht
  rw [show h*p^3=h*p*p*p by ring]
  calc
    _=eisEmbedding (symbol c p)^3*arithmeticResidueSum (h*p*p*p) c:=by rw [hb,one_mul]
    _=eisEmbedding (symbol c p)^2*arithmeticResidueSum (h*p*p) c:=by rw [pow_succ,mul_assoc,h3]
    _=eisEmbedding (symbol c p)*arithmeticResidueSum (h*p) c:=by rw [pow_two,mul_assoc,h2]
    _=arithmeticResidueSum h c:=h1

lemma ramified_prime_Gauss_cancel (h c p:Eis) (hc:c≠0) (hlevel:(3:Eis)∣c)
    (hp:Prime p) (hprimary:lambda^2∣p-1) (hcp:IsCoprime c p) :
    arithmeticResidueSum h c*primeCubicGauss p hp hprimary 1 (h*(9*c))=
      arithmeticResidueSum (h*p) c*primeCubicGauss p hp hprimary 1 (9*h) := by
  have ht:denominatorCondition c p:=⟨hcp,three_dvd_lambda_sq.trans hprimary⟩
  have hA:=arithmeticResidueSum_frequency_twist h c p hc hlevel ht
  have hG:=cubicUnitGaussSum_frequency_twist (9*h) p c hp.ne_zero hprimary hcp.symm
  rw [←primeCubicGauss_one_eq p hp hprimary,←primeCubicGauss_one_eq p hp hprimary] at hG
  rw [show (9*h)*c=h*(9*c) by ring] at hG
  have hb:eisEmbedding (symbol c p)≠0:=by
    have hcube:(eisEmbedding (symbol c p))^3=1:=by
      rw [←map_pow,symbol_cube_of_isCoprime c p hprimary hcp,map_one]
    intro hz
    simp only [hz,zero_pow (by decide : (3:ℕ)≠0)] at hcube
    exact zero_ne_one hcube
  apply mul_left_cancel₀ hb
  calc
    _=arithmeticResidueSum h c*(eisEmbedding (symbol c p)*
      primeCubicGauss p hp hprimary 1 (h*(9*c))):=by ring
    _=arithmeticResidueSum h c*primeCubicGauss p hp hprimary 1 (9*h):=by rw [hG]
    _=(eisEmbedding (symbol c p)*arithmeticResidueSum (h*p) c)*
      primeCubicGauss p hp hprimary 1 (9*h):=by rw [hA]
    _=_:=by ring

lemma ramified_prime_frequency_not_dvd (h p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hph:¬p∣h) (u:Eisˣ) (n:ℕ) :
    ¬p∣h*(9*(u.val*lambda^n)) := by
  intro hd
  rcases hp.dvd_mul.mp hd with hh|hc
  · exact hph hh
  have hcp: IsCoprime (9*(u.val*lambda^n)) p := by
    have h3: IsCoprime (3:Eis) p:=(primary_coprime_three p hprimary).symm
    have hram: IsCoprime (u.val*lambda^n) p:=
      (ramified_primary_coprime u n p hprimary).of_mul_left_right
    convert! h3.pow_left (m:=2) |>.mul_left hram using 1 ; norm_num
  exact hp.not_isUnit (hcp.symm.isUnit_of_dvd hc)

lemma sourceRayPhase_mul_primary (h p:Eis) (hprimary:lambda^2∣p-1) :
    ShortDraftTrace.breveE (cuspFrequency (h*p))=
      ShortDraftTrace.breveE (cuspFrequency h) := by
  obtain ⟨d,hd⟩:=three_dvd_lambda_sq.trans hprimary
  have hp:p=1+3*d:=by linear_combination hd
  have he:cuspFrequency (h*p)=cuspFrequency h+cuspFrequency h*(3*eisEmbedding d):=by
    rw [hp,cuspFrequency,cuspFrequency,map_mul,map_add,map_mul,map_one,map_ofNat]
    ring
  rw [he,AddChar.map_add_eq_mul,cuspFrequency_period,mul_one]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance p2mAnonymous_PNT_ZeroFree_433_0257_parallel1_3 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units


end CubicEisenstein

end

end OAI

end


