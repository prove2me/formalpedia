-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0221_parallel1
-- name    : PNT_ZeroFree_433_0221_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:56:26.429225+00:00
-- url     : https://prove2.me/theorems/ac9a2df5-0ce9-4c68-96b8-634f603405ff
-- title:
--   Zero-free region foundations: Eisenstein.SourceProjection [0221_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.SourceProjection
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/SourceProjection.lean#L314-L557

import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0130_parallel1
import Definitions.Def_PNT_ZeroFree_433_0158_parallel1
import Definitions.Def_PNT_ZeroFree_433_0188_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0228_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0260_parallel1
import Definitions.Def_PNT_ZeroFree_433_0262_parallel1
import Definitions.Def_PNT_ZeroFree_433_0303_parallel1
import Definitions.Def_PNT_ZeroFree_433_0329_parallel1
import Definitions.Def_PNT_ZeroFree_433_0330_parallel1

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


namespace CubicKubota

open scoped Classical MatrixGroups

section
open ActualEisensteinCubic
open CubicEisenstein

def levelThreeInTwo : Subgroup levelTwo := levelThree.comap levelTwo.subtype

instance levelThreeInTwo_normal : levelThreeInTwo.Normal := by
  constructor
  intro n hn g
  exact (levelThreeConjugate (g:SL(2,ActualEisensteinCubic.O)) ⟨(n:SL(2,ActualEisensteinCubic.O)),hn⟩).property


def rationalLift : SL(2,ℤ)→*levelTwo where
  toFun r := ⟨rationalEmbedding r,rational_mem_levelTwo r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

def rationalQuotient : SL(2,ℤ)→*(levelTwo ⧸ levelThreeInTwo) :=
  (QuotientGroup.mk' levelThreeInTwo).comp rationalLift

theorem rationalQuotient_surjective : Function.Surjective rationalQuotient := by
  intro q
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective levelThreeInTwo q
  obtain ⟨n,r,hr⟩ := g.property
  refine ⟨r,?_⟩
  let n2 : levelTwo := ⟨(n:SL(2,ActualEisensteinCubic.O)),levelThree_le_levelTwo n.property⟩
  have he : g=n2*rationalLift r := Subtype.ext hr.symm
  have hn : QuotientGroup.mk' levelThreeInTwo n2=1 :=
    (QuotientGroup.eq_one_iff n2).mpr n.property
  change QuotientGroup.mk' levelThreeInTwo (rationalLift r)=_
  rw [he,map_mul,hn,one_mul]

def rationalCongruenceThree : Subgroup (SL(2,ℤ)) := rationalQuotient.ker

instance rationalCongruenceThree_normal : rationalCongruenceThree.Normal := by
  unfold rationalCongruenceThree
  infer_instance

theorem mem_rationalCongruenceThree (r : SL(2,ℤ)) :
    r∈rationalCongruenceThree ↔ rationalEmbedding r∈levelThree := by
  change QuotientGroup.mk' levelThreeInTwo (rationalLift r)=1 ↔ _
  exact QuotientGroup.eq_one_iff _

def rationalQuotientEquiv : (SL(2,ℤ) ⧸ rationalCongruenceThree) ≃*
    (levelTwo ⧸ levelThreeInTwo) :=
  QuotientGroup.quotientKerEquivOfSurjective rationalQuotient rationalQuotient_surjective


end

open ActualEisensteinCubic

lemma three_dvd_intCast_iff (a : ℤ) : (3:ActualEisensteinCubic.O)∣(a:ActualEisensteinCubic.O) ↔ (3:ℤ)∣a := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨u,v,huv⟩ := ActualEisensteinCoordinates.exists_coordinates x
    have he : ActualEisensteinCoordinates.eval a 0=
        ActualEisensteinCoordinates.eval (3*u) (3*v) := by
      dsimp [ActualEisensteinCoordinates.eval]
      rw [hx,huv]
      push_cast
      ring
    exact ⟨u,(ActualEisensteinCoordinates.unique_coordinates he).1⟩
  · rintro ⟨b,hb⟩
    refine ⟨(b:ActualEisensteinCubic.O),?_⟩
    simpa only [Int.cast_mul,Int.cast_ofNat] using congrArg (fun z : ℤ => (z:ActualEisensteinCubic.O)) hb

lemma mem_levelThree_iff_entries (g : SL(2,ActualEisensteinCubic.O)) : g∈levelThree ↔
    ∀i j,(3:ActualEisensteinCubic.O)∣g i j-(if i=j then 1 else 0) := by
  constructor
  · intro hg i j
    exact levelThree_entry ⟨g,hg⟩ i j
  · intro h
    change Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:ActualEisensteinCubic.O)})) g=1
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change Ideal.Quotient.mk (Ideal.span {(3:ActualEisensteinCubic.O)}) (g i j)=
      (1:Matrix (Fin 2) (Fin 2) (ActualEisensteinCubic.O ⧸ Ideal.span {(3:ActualEisensteinCubic.O)})) i j
    rw [Matrix.one_apply]
    have he := (Ideal.Quotient.mk_eq_mk_iff_sub_mem (g i j) (if i=j then 1 else 0)).mpr
      (Ideal.mem_span_singleton.mpr (h i j))
    simpa only [apply_ite,map_one,map_zero] using he

def rationalReductionThree : SL(2,ℤ)→*SL(2,ZMod 3) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3))

lemma rationalReductionThree_eq_one_iff (g : SL(2,ℤ)) :
    rationalReductionThree g=1 ↔ g∈rationalCongruenceThree := by
  rw [mem_rationalCongruenceThree,mem_levelThree_iff_entries]
  constructor
  · intro hg i j
    have he := congrArg (fun h : SL(2,ZMod 3) => h i j) hg
    change (g i j:ZMod 3)=(1:Matrix (Fin 2) (Fin 2) (ZMod 3)) i j at he
    rw [Matrix.one_apply] at he
    have hd : (3:ℤ)∣g i j-(if i=j then 1 else 0) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
      simpa only [Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero] using sub_eq_zero.mpr he
    have hO := (three_dvd_intCast_iff (g i j-(if i=j then 1 else 0))).mpr hd
    simpa only [rationalEmbedding,Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply,Matrix.map_apply,Int.coe_castRingHom,
      Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero] using hO
  · intro hg
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (g i j:ZMod 3)=(1:Matrix (Fin 2) (Fin 2) (ZMod 3)) i j
    rw [Matrix.one_apply]
    apply sub_eq_zero.mp
    have hd : (3:ℤ)∣g i j-(if i=j then 1 else 0) := by
      apply (three_dvd_intCast_iff _).mp
      simpa only [rationalEmbedding,Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply,Matrix.map_apply,Int.coe_castRingHom,
        Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero] using hg i j
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hd
    simpa only [Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero] using hz

abbrev RationalBruhatIndex := Fin 2 × (Fin 3 ⊕ (Fin 3 × Fin 3))

def rationalBruhatRep (i : RationalBruhatIndex) : SL(2,ℤ) :=
  ModularGroup.S^(2*i.1.val) * match i.2 with
    | Sum.inl a => ModularGroup.T^a.val
    | Sum.inr ab => ModularGroup.T^ab.1.val*ModularGroup.S*ModularGroup.T^ab.2.val

lemma rationalBruhat_complete : ∀g : SL(2,ZMod 3),
    ∃i : RationalBruhatIndex,rationalReductionThree (rationalBruhatRep i)=g := by
  decide +kernel

lemma rationalReductionThree_surjective : Function.Surjective rationalReductionThree := by
  intro g
  obtain ⟨i,hi⟩ := rationalBruhat_complete g
  exact ⟨rationalBruhatRep i,hi⟩

lemma rationalBruhat_injective : Function.Injective
    (fun i : RationalBruhatIndex => rationalReductionThree (rationalBruhatRep i)) := by
  decide +kernel

def rationalBruhatEquiv : RationalBruhatIndex ≃ SL(2,ZMod 3) :=
  Equiv.ofBijective (fun i => rationalReductionThree (rationalBruhatRep i))
    ⟨rationalBruhat_injective,rationalBruhat_complete⟩

lemma card_SLThree : Fintype.card (SL(2,ZMod 3))=24 := by
  rw [←Fintype.card_congr rationalBruhatEquiv]
  decide

lemma rationalCongruenceThree_eq_ker : rationalCongruenceThree=rationalReductionThree.ker := by
  ext g
  exact (rationalReductionThree_eq_one_iff g).symm

def rationalCongruenceEquivSLThree : (SL(2,ℤ) ⧸ rationalCongruenceThree) ≃* SL(2,ZMod 3) :=
  (QuotientGroup.quotientMulEquivOfEq rationalCongruenceThree_eq_ker).trans
    (QuotientGroup.quotientKerEquivOfSurjective rationalReductionThree rationalReductionThree_surjective)

def sourceQuotientEquivSLThree : (levelTwo ⧸ levelThreeInTwo) ≃* SL(2,ZMod 3) :=
  rationalQuotientEquiv.symm.trans rationalCongruenceEquivSLThree

lemma sourceQuotient_card : Nat.card (levelTwo ⧸ levelThreeInTwo)=24 := by
  rw [Nat.card_congr sourceQuotientEquivSLThree.toEquiv,Nat.card_eq_fintype_card,card_SLThree]

lemma levelThreeInTwo_index : levelThreeInTwo.index=24 := sourceQuotient_card

theorem twentyFour_rational_representatives (g : levelTwo) :
    ∃i : RationalBruhatIndex,
      (g:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding (rationalBruhatRep i))⁻¹∈levelThree := by
  obtain ⟨r,hr⟩ := rationalQuotient_surjective (QuotientGroup.mk' levelThreeInTwo g)
  obtain ⟨i,hi⟩ := rationalBruhat_complete (rationalReductionThree r)
  refine ⟨i,?_⟩
  have hred : rationalReductionThree (r*(rationalBruhatRep i)⁻¹)=1 := by
    rw [map_mul,map_inv,hi,mul_inv_cancel]
  have hker := (rationalReductionThree_eq_one_iff _).mp hred
  have hquot : rationalQuotient r=rationalQuotient (rationalBruhatRep i) := by
    have hz : rationalQuotient (r*(rationalBruhatRep i)⁻¹)=1 := hker
    rw [map_mul,map_inv,mul_inv_eq_one] at hz
    exact hz
  have he : QuotientGroup.mk' levelThreeInTwo
      (g*(rationalLift (rationalBruhatRep i))⁻¹)=1 := by
    rw [map_mul,map_inv,←hr,hquot]
    exact mul_inv_cancel _
  exact (QuotientGroup.eq_one_iff (N:=levelThreeInTwo)
    (g*(rationalLift (rationalBruhatRep i))⁻¹)).mp he

end CubicKubota

open scoped BigOperators Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic
open CubicEisenstein

lemma rationalQuotient_eq_iff_reduction (r s : SL(2,ℤ)) :
    rationalQuotient r=rationalQuotient s ↔
      rationalReductionThree r=rationalReductionThree s := by
  have hleft : rationalQuotient r=rationalQuotient s ↔ r*s⁻¹∈rationalCongruenceThree := by
    change _ ↔ rationalQuotient (r*s⁻¹)=1
    rw [map_mul,map_inv,mul_inv_eq_one]
  rw [hleft,←rationalReductionThree_eq_one_iff,map_mul,map_inv,mul_inv_eq_one]

lemma levelTwoComplexCharacter_rationalLift (r : SL(2,ℤ)) :
    levelTwoComplexCharacter (rationalLift r)=1 := levelTwoComplexCharacter_rational r

def rationalCosetEquiv : RationalBruhatIndex ≃ (levelTwo ⧸ levelThreeInTwo) :=
  Equiv.ofBijective (fun i => rationalQuotient (rationalBruhatRep i)) ⟨by
    intro i j h
    exact rationalBruhat_injective ((rationalQuotient_eq_iff_reduction _ _).mp h),by
    intro q
    obtain ⟨r,hr⟩ := rationalQuotient_surjective q
    obtain ⟨i,hi⟩ := rationalBruhat_complete (rationalReductionThree r)
    exact ⟨i,((rationalQuotient_eq_iff_reduction _ _).mpr hi).trans hr⟩⟩


def sourceRationalSection (q : levelTwo ⧸ levelThreeInTwo) : SL(2,ℤ) :=
  rationalBruhatRep (rationalCosetEquiv.symm q)

lemma sourceRationalSection_spec (q : levelTwo ⧸ levelThreeInTwo) :
    rationalQuotient (sourceRationalSection q)=q := rationalCosetEquiv.apply_symm_apply q


end CubicKubota

end

end OAI

end


