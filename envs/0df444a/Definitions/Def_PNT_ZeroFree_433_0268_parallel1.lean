-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0268_parallel1
-- name    : PNT_ZeroFree_433_0268_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:29:34.768652+00:00
-- url     : https://prove2.me/theorems/2c0cfcc8-fb46-4ea7-914d-3654d2b6e3d4
-- title:
--   Zero-free region foundations: Eisenstein.RamifiedValuation [0268_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.RamifiedValuation
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/RamifiedValuation.lean#L86-L540

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0096
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0130
import Definitions.Def_PNT_ZeroFree_433_0174_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0220_parallel1
import Definitions.Def_PNT_ZeroFree_433_0223_parallel1
import Definitions.Def_PNT_ZeroFree_433_0231_parallel1
import Definitions.Def_PNT_ZeroFree_433_0241
import Definitions.Def_PNT_ZeroFree_433_0244_parallel2
import Definitions.Def_PNT_ZeroFree_433_0246_parallel1
import Definitions.Def_PNT_ZeroFree_433_0249_parallel1
import Definitions.Def_PNT_ZeroFree_433_0255_parallel1
import Definitions.Def_PNT_ZeroFree_433_0259_parallel1
import Definitions.Def_PNT_ZeroFree_433_0263_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0265_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0275_parallel2
import Definitions.Def_PNT_ZeroFree_433_0280_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/RamifiedValuation.lean
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
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedFunction_valuation_ne_two (F:Eis→ℂ)
    (hzero:∀(p:Eis),Prime p→lambda^2∣p-1→∀h:Eis,¬p∣h→∀k:ℕ,k%3=2→F (h*p^k)=0)
    (I P:Ideal Eis) (hI:primaryGenerator I≠0) (hP:P∈normalizedFactors I)
    (u:Eisˣ) (m:ℕ) (hF:F ((u.val*lambda^m)*primaryGenerator I)≠0) :
    (normalizedFactors I).count P%3≠2 := by
  have hI0:=primaryGenerator_ne_zero_ideal I hI
  have hprime:=prime_of_normalized_factor P hP
  let p:=primaryPrime P
  have hp0:p≠0:=primaryPrime_factor_ne_zero I P hI hP
  have hps:=primaryPrime_spec P hp0
  have hp:Prime p:=primaryPrime_isPrime_of_mem I P hI (Multiset.mem_toFinset.mpr hP)
  obtain ⟨J,hJ,hnot⟩:=(FiniteMultiplicity.of_prime_left hprime hI0).exists_eq_pow_mul_and_not_dvd
  have hgen:primaryGenerator I=p^(multiplicity P I)*primaryGenerator J:=by
    calc
      _=primaryGenerator (P^(multiplicity P I)*J):=congrArg primaryGenerator hJ
      _=p^(multiplicity P I)*primaryGenerator J:=by
        rw [primaryGenerator_mul,primaryGenerator_pow]
        have he:primaryGenerator P=p:=by
          rw [←hps.2.2.1,primaryGenerator_span p hp0 hps.2.2.2]
        rw [he]
  have hgJ:primaryGenerator J≠0:=by
    intro hz
    exact hI (by rw [hgen,hz,mul_zero])
  have hpd:¬p∣primaryGenerator J:=by
    intro hd
    apply hnot
    rw [Ideal.dvd_iff_le,←hps.2.2.1,←(primaryGenerator_spec J hgJ).1,
      Ideal.span_singleton_le_span_singleton]
    exact hd
  have hbase:¬p∣(u.val*lambda^m)*primaryGenerator J:=by
    intro hd
    rcases hp.dvd_mul.mp hd with hd|hd
    · exact hp.not_isUnit (((ramified_primary_coprime u m p hps.2.2.2).of_mul_left_right).symm.isUnit_of_dvd hd)
    · exact hpd hd
  have hcount:=multiplicity_eq_count_normalizedFactors hprime.irreducible hI0
  rw [normalize_normalized_factor P hP] at hcount
  intro hc
  have hm:(multiplicity P I)%3=2:=by rwa [hcount]
  apply hF
  rw [hgen,show (u.val*lambda^m)*(p^(multiplicity P I)*primaryGenerator J)=
    ((u.val*lambda^m)*primaryGenerator J)*p^(multiplicity P I) by ring]
  exact hzero p hp hps.2.2.2 _ hbase _ hm


end


open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O


end

section
open scoped Classical BigOperators

open ActualEisensteinCubic CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

abbrev ThetaPrimaryCubePair :=
  {I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
  {J:Ideal Eis // primaryGenerator J≠0}

def thetaPrimaryProduct (p : ThetaPrimaryCubePair) : GoodIdeal :=
  ⟨p.1.val*p.2.val^3,by
    rw [primaryGenerator_mul,primaryGenerator_pow]
    exact mul_ne_zero p.1.property.2 (pow_ne_zero 3 p.2.property)⟩

lemma thetaPrimaryProduct_injective : Function.Injective thetaPrimaryProduct := by
  intro p q he
  have hprod : p.1.val*p.2.val^3=q.1.val*q.2.val^3 := congrArg Subtype.val he
  have h := squarefree_cube_decomposition_unique
    (primaryGenerator_ne_zero_ideal _ p.2.property)
    (primaryGenerator_ne_zero_ideal _ q.2.property) p.1.property.1 q.1.property.1 hprod
  exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)

abbrev ThetaFullIndex := Eisˣ × ℕ × ThetaPrimaryCubePair

def thetaFullFrequency (p : ThetaFullIndex) : Eis :=
  (p.1.val*lambda^p.2.1)*primaryGenerator p.2.2.1.val*
    (primaryGenerator p.2.2.2.val)^3

lemma thetaFullFrequency_product (p : ThetaFullIndex) :
    thetaFullFrequency p=p.1.val*(lambda^p.2.1*primaryGenerator (thetaPrimaryProduct p.2.2).val) := by
  simp only [thetaFullFrequency,thetaPrimaryProduct,primaryGenerator_mul,primaryGenerator_pow]
  ring

lemma thetaFullFrequency_ne_zero (p : ThetaFullIndex) : thetaFullFrequency p≠0 := by
  rw [thetaFullFrequency_product]
  exact mul_ne_zero p.1.ne_zero
    (mul_ne_zero (pow_ne_zero _ PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero)
      (thetaPrimaryProduct p.2.2).property)

lemma thetaFullFrequency_span (p : ThetaFullIndex) :
    Ideal.span {thetaFullFrequency p}=ramifiedIdeal^p.2.1*(thetaPrimaryProduct p.2.2).val := by
  rw [thetaFullFrequency_product,Ideal.span_singleton_mul_left_unit p.1.isUnit,
    lambdaFactor_generator_span]

theorem thetaFullFrequency_injective : Function.Injective thetaFullFrequency := by
  rintro ⟨u,m,p⟩ ⟨v,n,q⟩ he
  have hs := congrArg (fun x:Eis=>Ideal.span {x}) he
  rw [thetaFullFrequency_span,thetaFullFrequency_span] at hs
  have hmap : lambdaFactorMap (m,thetaPrimaryProduct p)=lambdaFactorMap (n,thetaPrimaryProduct q) :=
    Subtype.ext hs
  have hij := lambdaFactorMap_bijective.1 hmap
  have hmn : m=n := congrArg Prod.fst hij
  have hpq : p=q := thetaPrimaryProduct_injective (congrArg Prod.snd hij)
  subst n
  subst q
  have huv : u=v := by
    apply Units.ext
    have hh : lambda^m*primaryGenerator (thetaPrimaryProduct p).val≠0 :=
      mul_ne_zero (pow_ne_zero _ PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero)
        (thetaPrimaryProduct p).property
    apply mul_right_cancel₀ hh
    simpa only [thetaFullFrequency_product] using he
  subst v
  rfl

end

section
open scoped BigOperators Classical MatrixGroups
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

structure SourceCuspDatum where
  gamma : levelTwo
  index : Fin 3
  lower_ne_zero :
    (integralComplexMatrix (gamma:SL(2,Eis))*integralComplexMatrix (cuspRepresentative index)) 1 0≠0

namespace SourceCuspDatum

def matrix (d : SourceCuspDatum) : SL(2,ℂ) :=
  integralComplexMatrix (d.gamma:SL(2,Eis))*integralComplexMatrix (cuspRepresentative d.index)
def point (d : SourceCuspDatum) : ℂ := d.matrix 0 0/d.matrix 1 0
def dualPoint (d : SourceCuspDatum) : ℂ := -d.matrix 1 1/d.matrix 1 0
def heightScale (d : SourceCuspDatum) : ℝ := ‖d.matrix 1 0‖^2
def multiplier (d : SourceCuspDatum) : ℂ := -star (levelTwoComplexCharacter d.gamma)/(d.matrix 1 0)^2

lemma heightScale_pos (d : SourceCuspDatum) : 0<d.heightScale :=
  sq_pos_of_pos (norm_pos_iff.mpr d.lower_ne_zero)

lemma multiplier_norm (d : SourceCuspDatum) : ‖d.multiplier‖=d.heightScale⁻¹ := by
  rw [multiplier,norm_div,norm_neg,norm_star,norm_levelTwoComplexCharacter,norm_pow,one_div]
  rfl

lemma multiplier_ne_zero (d : SourceCuspDatum) : d.multiplier≠0 := by
  intro hz
  have h:=d.multiplier_norm
  rw [hz,norm_zero] at h
  exact (inv_pos.mpr d.heightScale_pos).ne' h.symm

end SourceCuspDatum

lemma exists_sourceCuspDatum (a c : Eis) (hc : c≠0) :
    ∃d:SourceCuspDatum,d.point=eisEmbedding a/eisEmbedding c := by
  obtain ⟨M,hMc,hratio⟩:=exists_integral_matrix_cusp_ratio a c hc
  obtain ⟨G,j,T,hT,_,_,hM⟩:=three_cusp_decomposition M
  let g:SL(2,ℂ):=integralComplexMatrix (G:SL(2,Eis))*integralComplexMatrix (cuspRepresentative j)
  have he:integralComplexMatrix M=g*integralComplexMatrix T:=by
    rw [hM,map_mul,map_mul]
  have ht:integralComplexMatrix T 1 0=0:=by rw [integralComplexMatrix_apply,hT,map_zero]
  have hmc:(g*integralComplexMatrix T) 1 0≠0:=by
    rw [←he,integralComplexMatrix_apply]
    exact eisEmbedding_ne_zero hMc
  obtain ⟨hg,hr⟩:=upper_triangular_right_cusp_ratio g (integralComplexMatrix T) ht hmc
  refine ⟨⟨G,j,hg⟩,?_⟩
  change g 0 0/g 1 0=_
  rw [←hr,←he]
  exact hratio

def rationalSourceCusp (a c : Eis) (hc : c≠0) : SourceCuspDatum :=
  (exists_sourceCuspDatum a c hc).choose

lemma rationalSourceCusp_point (a c : Eis) (hc : c≠0) :
    (rationalSourceCusp a c hc).point=eisEmbedding a/eisEmbedding c :=
  (exists_sourceCuspDatum a c hc).choose_spec


def finiteTwistCusp (c : Eis) (hc : c≠0) (h : Eis⧸Ideal.span {c}) : SourceCuspDatum :=
  rationalSourceCusp (-3*Quotient.out h) c hc

lemma finiteTwistCusp_point (c : Eis) (hc : c≠0) (h : Eis⧸Ideal.span {c}) :
    (finiteTwistCusp c hc h).point=thetaFourierTranslation c h := by
  rw [finiteTwistCusp,rationalSourceCusp_point,thetaFourierTranslation,TraceLambdaPhase.eisLam_sq]
  simp only [map_mul,map_neg,map_ofNat]


end


end CubicEisenstein

end

end OAI

end


