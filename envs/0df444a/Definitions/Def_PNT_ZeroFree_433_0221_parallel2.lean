-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0221_parallel2
-- name    : PNT_ZeroFree_433_0221_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:41:34.366274+00:00
-- url     : https://prove2.me/theorems/fd8c557f-24a4-48bf-b135-e93ce7058392
-- title:
--   Zero-free region foundations: Eisenstein.SourceProjection [0221_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.SourceProjection
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/SourceProjection.lean#L96-L551

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0008
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0017
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0088
import Definitions.Def_PNT_ZeroFree_433_0093
import Definitions.Def_PNT_ZeroFree_433_0094
import Definitions.Def_PNT_ZeroFree_433_0099
import Definitions.Def_PNT_ZeroFree_433_0123_parallel1
import Definitions.Def_PNT_ZeroFree_433_0146_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0220_parallel1
import Definitions.Def_PNT_ZeroFree_433_0221_parallel1
import Definitions.Def_PNT_ZeroFree_433_0227_parallel1
import Definitions.Def_PNT_ZeroFree_433_0231_parallel2
import Definitions.Def_PNT_ZeroFree_433_0234_parallel1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/SourceProjection.lean
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

open scoped BigOperators Classical
namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O


lemma ramified_affine_isUnit (u:Eisˣ) (n:ℕ)
    (x:Eis⧸Ideal.span {u.val*lambda^n}) : IsUnit (1+3*x) := by
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  have hh:denominatorCondition (u.val*lambda^n) (1+3*d):=
    ramified_denominator_condition u n _ ⟨d,by ring⟩
  simpa only [map_add,map_one,map_mul,map_ofNat] using
    (isUnit_quotient_span_iff _ _).mpr hh.1

def ramifiedAffineEquiv (u:Eisˣ) (n:ℕ) :
    (Eis⧸Ideal.span {u.val*lambda^n})≃AdmissibleResidue (u.val*lambda^n):=
  (Equiv.subtypeUnivEquiv (ramified_affine_isUnit u n)).symm.trans (affineResidueEquiv _)

theorem ramified_arithmetic_affine (h:Eis) (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    arithmeticResidueSum h (u.val*lambda^n)=
      ∑'x:Eis⧸Ideal.span {u.val*lambda^n},
        eisEmbedding (symbol (u.val*lambda^n)
          (1+3*GaussianShiftedPartition.representative (u.val*lambda^n) x))*
        residueAdditive h (u.val*lambda^n)
          (1+3*GaussianShiftedPartition.representative (u.val*lambda^n) x) := by
  rw [arithmeticResidueSum,←(ramifiedAffineEquiv u n).tsum_eq]
  apply tsum_congr
  intro x
  let a:=u.val*lambda^n
  let d:=1+3*GaussianShiftedPartition.representative a x
  have hd:(3:Eis)∣d-1:=⟨_,by dsimp [d];ring⟩
  have hrep:3*a∣denominatorRep a ((ramifiedAffineEquiv u n) x).val-d:=
    denominatorRep_mk_congr a d
  change eisEmbedding (symbol a (denominatorRep a ((ramifiedAffineEquiv u n) x).val))*
    residueAdditive h a (denominatorRep a ((ramifiedAffineEquiv u n) x).val)=_
  rw [row_symbol_congr_modulus a _ d (ramifiedElement_level u n hn) hd hrep,
    residueAdditive_congr h a _ d (ramifiedElement_ne_zero u n) hrep]

def ramifiedReduction (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    (Eis⧸Ideal.span {u.val*lambda^n})→+*(Eis⧸Ideal.span {(3:Eis)}):=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
    (ramifiedElement_level u n hn))

lemma ramifiedReduction_surjective (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    Function.Surjective (ramifiedReduction u n hn):=
  Ideal.Quotient.factor_surjective _

lemma ramifiedReduction_rep (u:Eisˣ) (n:ℕ) (hn:2≤n)
    (x:Eis⧸Ideal.span {u.val*lambda^n}) :
    (3:Eis)∣GaussianShiftedPartition.representative (u.val*lambda^n) x-
      GaussianShiftedPartition.representative 3 (ramifiedReduction u n hn x) := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  rw [GaussianShiftedPartition.representative_spec]
  have hh:=congrArg (ramifiedReduction u n hn)
    (GaussianShiftedPartition.representative_spec (u.val*lambda^n) x)
  exact hh

lemma residueAdditive_ramified_scale (h k a d:Eis) (ha:a≠0) (hk:3*h=a*k) :
    residueAdditive h a d=residueAdditive k 3 d := by
  unfold residueAdditive cuspFrequency
  congr 1
  have he:=congrArg eisEmbedding hk
  simp only [map_mul,map_ofNat] at he
  have ha':eisEmbedding a≠0:=eisEmbedding_ne_zero ha
  simp only [map_ofNat]
  field_simp
  linear_combination eisLam⁻¹*eisEmbedding d*he

def ramifiedNineSum (k:Eis) (u:Eisˣ) (n:ℕ):ℂ:=
  ∑'x:Eis⧸Ideal.span {(3:Eis)},
    eisEmbedding (symbol (u.val*lambda^n)
      (1+3*GaussianShiftedPartition.representative 3 x))*
      residueAdditive k 3 (1+3*GaussianShiftedPartition.representative 3 x)

lemma ramifiedReduction_kernel_card (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    Nat.card (ramifiedReduction u n hn).toAddMonoidHom.ker=3^(n-2) := by
  have hc:=card_ring_eq_card_mul_kernel (ramifiedReduction u n hn)
    (ramifiedReduction_surjective u n hn)
  change Ideal.absNorm (Ideal.span {u.val*lambda^n})=
    Ideal.absNorm (Ideal.span {(3:Eis)})*Nat.card (ramifiedReduction u n hn).toAddMonoidHom.ker at hc
  rw [ramifiedElement_absNorm,three_absNorm] at hc
  have hn':n=2+(n-2):=by omega
  have hp:(3:ℕ)^n=9*3^(n-2):=by
    conv_lhs => rw [hn']
    rw [pow_add]
    norm_num
  omega


end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedLinearChar (u:Eisˣ) (n:ℕ):AddChar Eis ℂ where
  toFun x:=eisEmbedding (symbol (u.val*lambda^n) (1+3*x))
  map_zero_eq_one':=by simp
  map_add_eq_mul':=by
    intro x y
    have hp (z:Eis):(3:Eis)∣1+3*z-1:=⟨z,by ring⟩
    have hprod:(3:Eis)∣(1+3*x)*(1+3*y)-1:=⟨x+y+3*x*y,by ring⟩
    rw [ramified_symbol_congr_mod_nine u n (1+3*(x+y))
      ((1+3*x)*(1+3*y)) (hp _) hprod ⟨-x*y,by ring⟩,
      symbol_mul_denominator,map_mul]

lemma ramifiedLinearChar_period (u:Eisˣ) (n:ℕ) (x:Eis)
    (hx:x∈Ideal.span {(3:Eis)}) : ramifiedLinearChar u n x=1 := by
  obtain ⟨w,rfl⟩:=Ideal.mem_span_singleton.mp hx
  change eisEmbedding (symbol (u.val*lambda^n) (1+3*(3*w)))=1
  rw [ramified_symbol_congr_mod_nine u n _ 1 ⟨3*w,by ring⟩ (by simp) ⟨w,by ring⟩]
  simp

def ramifiedQuotientChar (u:Eisˣ) (n:ℕ):AddChar (Eis⧸Ideal.span {(3:Eis)}) ℂ:=
  IdealGaussCRT.quotientAddChar _ (ramifiedLinearChar u n) (ramifiedLinearChar_period u n)

lemma ramifiedQuotientChar_rep (u:Eisˣ) (n:ℕ) (x:Eis⧸Ideal.span {(3:Eis)}) :
    ramifiedQuotientChar u n x=
      eisEmbedding (symbol (u.val*lambda^n)
        (1+3*GaussianShiftedPartition.representative 3 x)) := by
  conv_lhs => rw [←GaussianShiftedPartition.representative_spec 3 x]
  rfl

def ramifiedFrequencyChar (k:Eis) (u:Eisˣ) (n:ℕ):
    AddChar (Eis⧸Ideal.span {(3:Eis)}) ℂ:=
  ramifiedQuotientChar u n *
    (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
      3 (by norm_num)).mulShift (Ideal.Quotient.mk _ k)

lemma ramifiedFrequencyChar_rep (k:Eis) (u:Eisˣ) (n:ℕ)
    (x:Eis⧸Ideal.span {(3:Eis)}) :
    ramifiedFrequencyChar k u n x=
      eisEmbedding (symbol (u.val*lambda^n)
        (1+3*GaussianShiftedPartition.representative 3 x))*
      residueAdditive k 3 (3*GaussianShiftedPartition.representative 3 x) := by
  rw [ramifiedFrequencyChar,AddChar.mul_apply,ramifiedQuotientChar_rep]
  congr 1
  conv_lhs => rw [←GaussianShiftedPartition.representative_spec 3 x]
  simp only [AddChar.mulShift_apply,←map_mul,eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  unfold residueAdditive cuspFrequency
  simp only [map_mul,map_ofNat]
  congr 1
  field_simp

theorem ramifiedNineSum_eq_character_test (k:Eis) (u:Eisˣ) (n:ℕ) :
    ramifiedNineSum k u n=
      if ramifiedFrequencyChar k u n=1 then 9*residueAdditive k 3 1 else 0 := by
  let:Finite (Eis⧸Ideal.span {(3:Eis)}):=finite_quotient_span (by norm_num)
  let:Fintype (Eis⧸Ideal.span {(3:Eis)}):=Fintype.ofFinite _
  have hcard:(Fintype.card (Eis⧸Ideal.span {(3:Eis)}):ℂ)=9:=by
    have hh:=three_absNorm
    change Nat.card (Eis⧸Ideal.span {(3:Eis)})=9 at hh
    exact_mod_cast (show Fintype.card (Eis⧸Ideal.span {(3:Eis)})=9 by
      simpa only [Nat.card_eq_fintype_card] using hh)
  have he:ramifiedNineSum k u n=residueAdditive k 3 1*
      ∑'x:Eis⧸Ideal.span {(3:Eis)},ramifiedFrequencyChar k u n x:=by
    rw [ramifiedNineSum,←tsum_mul_left]
    apply tsum_congr
    intro x
    rw [ramifiedFrequencyChar_rep,residueAdditive_add]
    ring
  rw [he,tsum_fintype]
  split_ifs with hchar
  · rw [AddChar.sum_eq_card_of_eq_one hchar,hcard]
    ring
  · rw [AddChar.sum_eq_zero_of_ne_one hchar,mul_zero]


end CubicEisenstein

namespace CubicKubota

open scoped Classical MatrixGroups

section
open ActualEisensteinCubic
open CubicEisenstein


instance levelThreeInTwo_finiteIndex : levelThreeInTwo.FiniteIndex := by
  let : levelThree.FiniteIndex := levelThree_finiteIndex
  change (levelThree.comap levelTwo.subtype).FiniteIndex
  constructor
  rw [Subgroup.index_comap]
  exact (Subgroup.isFiniteRelIndex_of_finiteIndex
    (H := levelThree) (K := levelTwo.subtype.range)).relIndex_ne_zero


instance rationalCongruenceThree_finiteIndex : rationalCongruenceThree.FiniteIndex := by
  have he : rationalCongruenceThree=levelThree.comap rationalEmbedding := by
    ext r
    exact mem_rationalCongruenceThree r
  rw [he]
  let : levelThree.FiniteIndex := levelThree_finiteIndex
  constructor
  rw [Subgroup.index_comap]
  exact (Subgroup.isFiniteRelIndex_of_finiteIndex
    (H := levelThree) (K := rationalEmbedding.range)).relIndex_ne_zero

theorem finite_rational_representatives : ∃R : Finset (SL(2,ℤ)),
    ∀g : levelTwo,∃r∈R,(g:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding r)⁻¹∈levelThree := by
  let : Fintype (levelTwo ⧸ levelThreeInTwo) := Fintype.ofFinite _
  let sectionMap : (levelTwo ⧸ levelThreeInTwo)→SL(2,ℤ) :=
    fun q => (rationalQuotient_surjective q).choose
  have hsection : ∀q,rationalQuotient (sectionMap q)=q :=
    fun q => (rationalQuotient_surjective q).choose_spec
  refine ⟨Finset.univ.image sectionMap,fun g => ?_⟩
  let q := QuotientGroup.mk' levelThreeInTwo g
  refine ⟨sectionMap q,Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩,?_⟩
  have he : QuotientGroup.mk' levelThreeInTwo (g*(rationalLift (sectionMap q))⁻¹)=1 := by
    rw [map_mul,map_inv]
    change q*(rationalQuotient (sectionMap q))⁻¹=1
    rw [hsection,mul_inv_cancel]
  exact (QuotientGroup.eq_one_iff (N:=levelThreeInTwo)
    (g*(rationalLift (sectionMap q))⁻¹)).mp he

end

open ActualEisensteinCubic


end CubicKubota

open scoped BigOperators Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic
open CubicEisenstein


instance sourceQuotientFintype : Fintype (levelTwo ⧸ levelThreeInTwo) := Fintype.ofFinite _


end CubicKubota

end

end OAI

end


