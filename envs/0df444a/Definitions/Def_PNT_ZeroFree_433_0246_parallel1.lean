-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0246_parallel1
-- name    : PNT_ZeroFree_433_0246_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:21:29.626289+00:00
-- url     : https://prove2.me/theorems/d6710a22-7632-4ad5-969f-e3c227ae3a0c
-- title:
--   Zero-free region foundations: Eisenstein.IntegralCover [0246_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.IntegralCover
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/IntegralCover.lean#L85-L656

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0017
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0124
import Definitions.Def_PNT_ZeroFree_433_0124_parallel1
import Definitions.Def_PNT_ZeroFree_433_0126
import Definitions.Def_PNT_ZeroFree_433_0127
import Definitions.Def_PNT_ZeroFree_433_0129_parallel2
import Definitions.Def_PNT_ZeroFree_433_0131_parallel1
import Definitions.Def_PNT_ZeroFree_433_0131_parallel2
import Definitions.Def_PNT_ZeroFree_433_0211_parallel1
import Definitions.Def_PNT_ZeroFree_433_0220_parallel1
import Definitions.Def_PNT_ZeroFree_433_0271_parallel1
import Definitions.Def_PNT_ZeroFree_433_0273_parallel1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/IntegralCover.lean
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

section
open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedOmegaUnit : Eisˣ := (omega_primitive.isUnit (by decide)).unit
lemma ramifiedOmegaUnit_val : (ramifiedOmegaUnit:Eis)=omega :=
  (omega_primitive.isUnit (by decide)).unit_spec


def onceCuspRayUnit (u t:Eisˣ) (l:Fin 3) : Eisˣ := u⁻¹^2*t*ramifiedOmegaUnit^l.val

def onceCuspRayIndex (u t:Eisˣ) (l:Fin 3) : Fin 3 :=
  Classical.choose (unit_eq_sign_omega (onceCuspRayUnit u t l))


end


open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding


end CubicEisenstein

section

open scoped Classical MatrixGroups BigOperators
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def cubeCuspHeightWeight (p:Eis) (j:Fin 4) : ℂ :=
  (((Ideal.absNorm (Ideal.span {p}):ℝ)^((2*(j.val:ℝ)-3)/3)):ℝ)

lemma cubeCuspHeightWeight_zero (p:Eis) :
    cubeCuspHeightWeight p 0=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹ := by
  unfold cubeCuspHeightWeight
  generalize Ideal.absNorm (Ideal.span {p}) = n
  norm_num [Real.rpow_neg_one]

lemma cubeCuspHeightWeight_three (p:Eis) :
    cubeCuspHeightWeight p 3=(Ideal.absNorm (Ideal.span {p}):ℂ) := by
  unfold cubeCuspHeightWeight
  generalize Ideal.absNorm (Ideal.span {p}) = n
  norm_num


end CubicKubota

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def cubeDilationRoot (p:Eis) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (eisEmbedding p^3) (by decide : 0<2))

lemma cubeDilationRoot_sq (p:Eis) : cubeDilationRoot p^2=eisEmbedding p^3 :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (eisEmbedding p^3) (by decide : 0<2))

lemma cubeDilationRoot_ne_zero (p:Eis) (hp:p≠0) : cubeDilationRoot p≠0 := by
  intro h
  have hs:=cubeDilationRoot_sq p
  rw [h,zero_pow (by decide)] at hs
  exact pow_ne_zero 3 (eisEmbedding_ne_zero hp) hs.symm

def cubeAverageMatrix (p:Eis) (hp:p≠0) (q:Eis) : SL(2,ℂ) :=
  complexDiagonal (cubeDilationRoot p)⁻¹ (inv_ne_zero (cubeDilationRoot_ne_zero p hp)) *
    complexTranslation (3*eisEmbedding q)

lemma cubeAverageMatrix_entries (p:Eis) (hp:p≠0) (q:Eis) :
    (cubeAverageMatrix p hp q : Matrix (Fin 2) (Fin 2) ℂ)=
      !![(cubeDilationRoot p)⁻¹,(cubeDilationRoot p)⁻¹*(3*eisEmbedding q);0,cubeDilationRoot p] := by
  unfold cubeAverageMatrix
  rw [Matrix.SpecialLinearGroup.coe_mul]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [complexDiagonal, complexTranslation, Matrix.mul_apply, Fin.sum_univ_two]

lemma cubeAverageMatrix_add_multiple (p:Eis) (hp:p≠0) (q n:Eis) :
    cubeAverageMatrix p hp (q+p^3*n)=
      complexTranslation (3*eisEmbedding n)*cubeAverageMatrix p hp q := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, cubeAverageMatrix_entries]
  apply Matrix.ext
  intro i j
  have hz := cubeDilationRoot_ne_zero p hp
  have he := cubeDilationRoot_sq p
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, complexTranslation,
      map_add, map_mul, map_pow]
  rw [← he]
  field_simp

lemma cubeAverageMatrix_translate_one (p:Eis) (hp:p≠0) (q t:Eis)
    (ht:3*t=1-p^3) :
    cubeAverageMatrix p hp q*complexTranslation 1=
      complexTranslation 1*cubeAverageMatrix p hp (q+t) := by
  have ht':3*eisEmbedding t=1-eisEmbedding p^3:=by
    simpa only [map_mul,map_sub,map_one,map_ofNat,map_pow] using congrArg eisEmbedding ht
  have hz:=cubeDilationRoot_ne_zero p hp
  have he:=cubeDilationRoot_sq p
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, cubeAverageMatrix_entries]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, complexTranslation, map_add]
  field_simp
  linear_combination -ht'-he

def cubeAverage (p:Eis) (hp:p≠0) (F:HyperbolicSpace→ℂ) (w:HyperbolicSpace) : ℂ :=
  (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
    ∑' r:Eis⧸Ideal.span {p^3},
      F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) • w)

lemma cubeAverage_summand_congr (p:Eis) (hp:p≠0) (F:HyperbolicSpace→ℂ)
    (hF:∀n:Eis,∀w:HyperbolicSpace,F (complexTranslation (3*eisEmbedding n) • w)=F w)
    (a b:Eis) (hab:p^3∣a-b) (w:HyperbolicSpace) :
    F (cubeAverageMatrix p hp a • w)=F (cubeAverageMatrix p hp b • w) := by
  obtain ⟨n,hn⟩:=hab
  have ha:a=b+p^3*n:=by linear_combination hn
  rw [ha,cubeAverageMatrix_add_multiple,mul_smul,hF]

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeAverageMatrix_action (p:Eis) (hp:p≠0) (q:Eis)
    (z:ℂ) (v:ℝ) (hv:0<v) :
    cubeAverageMatrix p hp q • upperPoint z v hv =
      upperPoint ((z+3*eisEmbedding q)/eisEmbedding p^3)
        (v/‖eisEmbedding p‖^3) (div_pos hv (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) 3)) := by
  rw [cubeAverageMatrix,mul_smul,complexTranslation_action,complexDiagonal_action]
  apply upperPoint_congr
  · rw [inv_pow,cubeDilationRoot_sq]
    ring
  · have hn:‖cubeDilationRoot p‖^2=‖eisEmbedding p‖^3:=by
      rw [←norm_pow,cubeDilationRoot_sq,norm_pow]
    rw [Complex.normSq_eq_norm_sq,norm_inv,inv_pow,hn]
    ring

theorem cubeAverage_period_one (p:Eis) (hp:p≠0) (hprimary:lambda^2∣p-1)
    (F:HyperbolicSpace→ℂ)
    (hF:∀n:Eis,∀w:HyperbolicSpace,F (complexTranslation (3*eisEmbedding n) • w)=F w)
    (hF1:∀w:HyperbolicSpace,F (complexTranslation 1 • w)=F w)
    (w:HyperbolicSpace) :
    cubeAverage p hp F (complexTranslation 1 • w)=cubeAverage p hp F w := by
  have hd:(3:Eis)∣1-p^3:=by
    have hh:=(three_dvd_primary_sub_one p hprimary).trans (sub_one_dvd_pow_sub_one p 3)
    simpa only [neg_sub] using dvd_neg.mpr hh
  obtain ⟨t,ht⟩:=hd
  let a:(Eis⧸Ideal.span {p^3})≃(Eis⧸Ideal.span {p^3}):=
    { toFun:=fun r=>r+Ideal.Quotient.mk _ t
      invFun:=fun r=>r-Ideal.Quotient.mk _ t
      left_inv:=fun r=>add_sub_cancel_right r _
      right_inv:=fun r=>sub_add_cancel r _ }
  let f (r:Eis⧸Ideal.span {p^3}):=
    F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) • w)
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) •
        (complexTranslation 1 • w))=f (a r) := by
    rw [←mul_smul,cubeAverageMatrix_translate_one p hp _ t ht.symm,mul_smul,hF1]
    apply cubeAverage_summand_congr p hp F hF
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    rw [map_add,GaussianShiftedPartition.representative_spec,
      GaussianShiftedPartition.representative_spec]
    rfl
  unfold cubeAverage
  congr 1
  calc
    _ = ∑' r,f (a r):=tsum_congr hpoint
    _ = ∑' r,f r:=a.tsum_eq f

end CubicEisenstein
end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def integralCoverMap {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K) :
    IntegralOrbitQuotient H→IntegralOrbitQuotient K :=
  Quotient.map' id (by
    rintro w u ⟨M,hM⟩
    exact ⟨Subgroup.inclusion hHK M,hM⟩)

lemma integralCoverMap_projection {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K) (w : HyperbolicSpace) :
    integralCoverMap hHK (integralOrbitProjection H w)=integralOrbitProjection K w := rfl


lemma integralCoverMap_continuous {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K) :
    Continuous (integralCoverMap hHK) := continuous_id.quotient_map' _

lemma integralCoverMap_surjective {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K) :
    Function.Surjective (integralCoverMap hHK) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ w => exact ⟨integralOrbitProjection H w,rfl⟩

abbrev IntegralCoverCosets (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) := K ⧸ H.subgroupOf K

def integralCoverRep (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) (q : IntegralCoverCosets H K) : K := q.out


lemma integralCoverRep_mul_projection {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K)
    (q : IntegralCoverCosets H K) (h : H) :
    ((integralCoverRep H K q*Subgroup.inclusion hHK h : K) : IntegralCoverCosets H K)=q := by
  rw [QuotientGroup.mk_mul_of_mem _ (show Subgroup.inclusion hHK h∈H.subgroupOf K from h.property)]
  exact QuotientGroup.out_eq' q


end CubicEisenstein

end

end OAI

end


