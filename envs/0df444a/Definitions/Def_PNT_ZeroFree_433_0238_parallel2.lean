-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0238_parallel2
-- name    : PNT_ZeroFree_433_0238_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:19:48.288245+00:00
-- url     : https://prove2.me/theorems/c36c0dae-e9a6-4fb9-885c-bcbaa378dae2
-- title:
--   Zero-free region foundations: Reciprocity.CubeCorrespondence [0238_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Reciprocity.CubeCorrespondence
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/CubeCorrespondence.lean#L338-L502

import Mathlib.GroupTheory.Index
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0123_parallel1
import Definitions.Def_PNT_ZeroFree_433_0124
import Definitions.Def_PNT_ZeroFree_433_0126
import Definitions.Def_PNT_ZeroFree_433_0127
import Definitions.Def_PNT_ZeroFree_433_0129_parallel2
import Definitions.Def_PNT_ZeroFree_433_0211_parallel1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0271_parallel1
import Definitions.Def_PNT_ZeroFree_433_0273_parallel1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/CubeCorrespondence.lean
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

namespace CubicKubota

open scoped Classical MatrixGroups


section
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

def cubeKernelCorrespondence (p : Eis) : Subgroup (cubeCorrespondence p) :=
  (finiteCubicMultiplier.comp (cubeCorrespondenceLeft p)).ker

def cubeKernelLeft (p : Eis) : cubeKernelCorrespondence p →* finiteCubicMultiplier.ker where
  toFun x := ⟨cubeCorrespondenceLeft p x.1,x.property⟩
  map_one' := by apply Subtype.ext; exact map_one (cubeCorrespondenceLeft p)
  map_mul' x y := by apply Subtype.ext; exact map_mul (cubeCorrespondenceLeft p) x.1 y.1

lemma cubeKernel_right_mem (p : Eis) (hp : p ≠ 0) (x : cubeKernelCorrespondence p) :
    cubeCorrespondenceRight p x.1 ∈ finiteCubicMultiplier.ker := by
  apply (finiteCubicMultiplier_eq_one _).mpr
  rw [←cubeCorrespondence_character p hp x.1]
  exact (finiteCubicMultiplier_eq_one _).mp x.property

def cubeKernelRight (p : Eis) (hp : p ≠ 0) :
    cubeKernelCorrespondence p →* finiteCubicMultiplier.ker where
  toFun x := ⟨cubeCorrespondenceRight p x.1,cubeKernel_right_mem p hp x⟩
  map_one' := by apply Subtype.ext; exact map_one (cubeCorrespondenceRight p)
  map_mul' x y := by apply Subtype.ext; exact map_mul (cubeCorrespondenceRight p) x.1 y.1

lemma cubeKernelLeft_range (p : Eis) :
    (cubeKernelLeft p).range =
      (cubeCorrespondenceLeft p).range.comap finiteCubicMultiplier.ker.subtype := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨x.1,rfl⟩
  · rintro ⟨x,hx⟩
    have hmem : x∈cubeKernelCorrespondence p := by
      change finiteCubicMultiplier (cubeCorrespondenceLeft p x)=1
      rw [hx]
      exact y.property
    exact ⟨⟨x,hmem⟩,Subtype.ext hx⟩

lemma cubeKernelRight_range (p : Eis) (hp : p ≠ 0) :
    (cubeKernelRight p hp).range =
      (cubeCorrespondenceRight p).range.comap finiteCubicMultiplier.ker.subtype := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨x.1,rfl⟩
  · rintro ⟨x,hx⟩
    have hmem : x∈cubeKernelCorrespondence p := by
      apply (finiteCubicMultiplier_eq_one _).mpr
      rw [cubeCorrespondence_character p hp x,hx]
      exact (finiteCubicMultiplier_eq_one _).mp y.property
    exact ⟨⟨x,hmem⟩,Subtype.ext hx⟩

lemma cubeKernel_finite_covers (p : Eis) (hp : p ≠ 0) :
    Function.Injective (cubeKernelLeft p) ∧ Function.Injective (cubeKernelRight p hp) ∧
    (cubeKernelLeft p).range.FiniteIndex ∧ (cubeKernelRight p hp).range.FiniteIndex := by
  have hcov := cubeCorrespondence_finite_covers p hp
  let := hcov.2.2.1
  let := hcov.2.2.2
  refine ⟨?_,?_,?_,?_⟩
  · intro x y h
    apply Subtype.ext
    apply hcov.1
    exact congrArg Subtype.val h
  · intro x y h
    apply Subtype.ext
    apply hcov.2.1
    exact congrArg Subtype.val h
  · rw [cubeKernelLeft_range]
    infer_instance
  · rw [cubeKernelRight_range]
    infer_instance

def cubeKernelLeftGlobal (p : Eis) : cubeKernelCorrespondence p →* SL(2,Eis) :=
  levelThree.subtype.comp (finiteCubicMultiplier.ker.subtype.comp (cubeKernelLeft p))

def cubeKernelRightGlobal (p : Eis) (hp : p ≠ 0) :
    cubeKernelCorrespondence p →* SL(2,Eis) :=
  levelThree.subtype.comp (finiteCubicMultiplier.ker.subtype.comp (cubeKernelRight p hp))

lemma cubeKernelLeftGlobal_le (p : Eis) :
    (cubeKernelLeftGlobal p).range ≤ globalKubotaKernel := by
  rintro M ⟨x,rfl⟩
  exact ⟨(cubeKernelLeft p x).1,(cubeKernelLeft p x).property,rfl⟩

lemma cubeKernelRightGlobal_le (p : Eis) (hp : p ≠ 0) :
    (cubeKernelRightGlobal p hp).range ≤ globalKubotaKernel := by
  rintro M ⟨x,rfl⟩
  exact ⟨(cubeKernelRight p hp x).1,(cubeKernelRight p hp x).property,rfl⟩


lemma cubeKernelGlobal_intertwining (p : Eis) (hp : p ≠ 0) (x : cubeKernelCorrespondence p) :
    cubeDiagonal p * (cubeKernelLeftGlobal p x).val =
      (cubeKernelRightGlobal p hp x).val * cubeDiagonal p := x.1.property

end

open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeArchimedean_correspondence (p : Eis) (hp : p ≠ 0) :
    ∃ g : SL(2,ℂ), g 0 1=0 ∧ g 1 0=0 ∧ g 0 0/g 1 1=eisEmbedding p^3 ∧
      ∀ x : cubeKernelCorrespondence p,
        g*integralComplexMatrix (cubeKernelLeftGlobal p x)=
          integralComplexMatrix (cubeKernelRightGlobal p hp x)*g := by
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (eisEmbedding p^3) (by decide : 0<2)
  have hz0 : z≠0 := by
    intro he
    rw [he,zero_pow (by decide)] at hz
    exact pow_ne_zero 3 (eisEmbedding_ne_zero hp) hz.symm
  let g : SL(2,ℂ) := ⟨!![z,0;0,z⁻¹],by simp [Matrix.det_fin_two_of,hz0]⟩
  refine ⟨g,rfl,rfl,?_,?_⟩
  · change z/z⁻¹=eisEmbedding p^3
    rw [div_inv_eq_mul,←pow_two,hz]
  · intro x
    have he := cubeCorrespondence_entries p x.1
    have ha : (((x.1).1.1 : levelThree) : SL(2,Eis)) 0 0 =
        (((x.1).1.2 : levelThree) : SL(2,Eis)) 0 0 :=
      mul_left_cancel₀ (pow_ne_zero 3 hp) (he.1.trans (mul_comm _ _))
    have he00 := congrArg eisEmbedding ha
    have he01 := congrArg eisEmbedding he.2.1
    have he10 := congrArg eisEmbedding he.2.2.1
    have he11 := congrArg eisEmbedding he.2.2.2
    simp only [map_mul,map_pow] at he01 he10
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
        integralComplexMatrix_apply]
    · change z*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 0 0)+0*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 1 0) =
        eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 0 0)*z+eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 0 1)*0
      rw [he00]
      ring
    · change z*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 0 1)+0*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 1 1) =
        eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 0 0)*0+eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 0 1)*z⁻¹
      rw [←he01,←hz]
      field_simp
      ring
    · change 0*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 0 0)+z⁻¹*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 1 0) =
        eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 1 0)*z+eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 1 1)*0
      rw [he10,←hz]
      field_simp
      ring
    · change 0*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 0 1)+z⁻¹*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 1 1) =
        eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 1 0)*0+eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 1 1)*z⁻¹
      rw [he11]
      ring

end CubicKubota


end

end OAI

end


