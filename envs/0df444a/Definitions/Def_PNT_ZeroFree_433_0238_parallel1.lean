-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0238_parallel1
-- name    : PNT_ZeroFree_433_0238_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:24:18.829005+00:00
-- url     : https://prove2.me/theorems/4c9707e7-2fdc-48c8-bdd7-57490ec79ef0
-- title:
--   Zero-free region foundations: Reciprocity.CubeCorrespondence [0238_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Reciprocity.CubeCorrespondence
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/CubeCorrespondence.lean#L207-L330

import Definitions.Def_PNT_ZeroFree_433_0238_parallel1_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
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
open ActualEisensteinCubic CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O


lemma cubeCorrespondence_character (p : Eis) (hp : p ≠ 0) (MN : cubeCorrespondence p) :
    complexCharacter (cubeCorrespondenceLeft p MN) =
      complexCharacter (cubeCorrespondenceRight p MN) := by
  exact congrArg ConcreteTraceCRT.eisEmbedding (cubeCorrespondence_value p hp MN)

end

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def cubePrincipalLevel (p : Eis) : Subgroup levelThree :=
  ((Matrix.SpecialLinearGroup.map (n:=Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3:Eis)*p^3}))).comp levelThree.subtype).ker

lemma cubePrincipalLevel_entry (p : Eis) (M : cubePrincipalLevel p) (i j : Fin 2) :
    (3:Eis)*p^3 ∣ ((M.1 : levelThree) : SL(2,Eis)) i j-(if i=j then 1 else 0) := by
  have hm : Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)*p^3})) ((M.1 : levelThree) : SL(2,Eis)) = 1 := M.property
  have h := congrArg (fun N : SL(2,Eis ⧸ Ideal.span {(3:Eis)*p^3}) => N i j) hm
  change Ideal.Quotient.mk (Ideal.span {(3:Eis)*p^3})
    (((M.1 : levelThree) : SL(2,Eis)) i j) =
      (1 : Matrix (Fin 2) (Fin 2) (Eis ⧸ Ideal.span {(3:Eis)*p^3})) i j at h
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  simpa only [Matrix.one_apply, apply_ite, map_one, map_zero] using h

lemma cubePrincipalLevel_finiteIndex (p : Eis) (hp : p ≠ 0) :
    (cubePrincipalLevel p).FiniteIndex := by
  let : Finite (Eis ⧸ Ideal.span {(3:Eis)*p^3}) :=
    finite_quotient_span (mul_ne_zero (by norm_num) (pow_ne_zero 3 hp))
  unfold cubePrincipalLevel
  infer_instance

lemma cubePrincipalLevel_left_mate (p : Eis) (M : cubePrincipalLevel p) :
    ∃ N : levelThree, ((M.1 : levelThree),N) ∈ cubeCorrespondence p := by
  obtain ⟨c,hc⟩ : (3:Eis)*p^3 ∣ ((M.1 : levelThree) : SL(2,Eis)) 1 0 := by
    simpa using cubePrincipalLevel_entry p M 1 0
  let A : SL(2,Eis) := M.1
  let N : SL(2,Eis) := ⟨!![A 0 0,p^3*A 0 1;3*c,A 1 1],by
    have hd := A.property
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of]
    change A 1 0=(3:Eis)*p^3*c at hc
    rw [hc] at hd
    linear_combination hd⟩
  have hN : N∈levelThree := by
    apply (mem_levelThree_iff_entries N).mpr
    intro i j
    fin_cases i <;> fin_cases j
    · exact levelThree_entry M.1 0 0
    · change (3:Eis)∣p^3*A 0 1-0
      simpa using dvd_mul_of_dvd_right (levelThree_upper M.1) (p^3)
    · change (3:Eis)∣3*c-0
      simp
    · exact levelThree_entry M.1 1 1
  refine ⟨⟨N,hN⟩,?_⟩
  change cubeDiagonal p*A.val=N.val*cubeDiagonal p
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cubeDiagonal,N,Matrix.mul_apply,Fin.sum_univ_two]
  · ring
  · change A 1 0=(3:Eis)*p^3*c at hc
    change A 1 0=3*c*p^3
    rw [hc]
    ring

lemma cubePrincipalLevel_right_mate (p : Eis) (N : cubePrincipalLevel p) :
    ∃ M : levelThree, (M,(N.1 : levelThree)) ∈ cubeCorrespondence p := by
  obtain ⟨b,hb⟩ : (3:Eis)*p^3 ∣ ((N.1 : levelThree) : SL(2,Eis)) 0 1 := by
    simpa using cubePrincipalLevel_entry p N 0 1
  let A : SL(2,Eis) := N.1
  let M : SL(2,Eis) := ⟨!![A 0 0,3*b;p^3*A 1 0,A 1 1],by
    have hd := A.property
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of]
    change A 0 1=(3:Eis)*p^3*b at hb
    rw [hb] at hd
    linear_combination hd⟩
  have hM : M∈levelThree := by
    apply (mem_levelThree_iff_entries M).mpr
    intro i j
    fin_cases i <;> fin_cases j
    · exact levelThree_entry N.1 0 0
    · change (3:Eis)∣3*b-0
      simp
    · change (3:Eis)∣p^3*A 1 0-0
      simpa using dvd_mul_of_dvd_right (levelThree_lower N.1) (p^3)
    · exact levelThree_entry N.1 1 1
  refine ⟨⟨M,hM⟩,?_⟩
  change cubeDiagonal p*M.val=A.val*cubeDiagonal p
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cubeDiagonal,M,Matrix.mul_apply,Fin.sum_univ_two]
  · ring
  · change A 0 1=(3:Eis)*p^3*b at hb
    change p^3*(3*b)=A 0 1
    rw [hb]
    ring
  · ring

lemma cubePrincipalLevel_le_left_range (p : Eis) :
    cubePrincipalLevel p ≤ (cubeCorrespondenceLeft p).range := by
  intro M hM
  obtain ⟨N,hN⟩ := cubePrincipalLevel_left_mate p ⟨M,hM⟩
  exact ⟨⟨(M,N),hN⟩,rfl⟩

lemma cubePrincipalLevel_le_right_range (p : Eis) :
    cubePrincipalLevel p ≤ (cubeCorrespondenceRight p).range := by
  intro N hN
  obtain ⟨M,hM⟩ := cubePrincipalLevel_right_mate p ⟨N,hN⟩
  exact ⟨⟨(M,N),hM⟩,rfl⟩

lemma cubeCorrespondence_finite_covers (p : Eis) (hp : p ≠ 0) :
    Function.Injective (cubeCorrespondenceLeft p) ∧
    Function.Injective (cubeCorrespondenceRight p) ∧
    (cubeCorrespondenceLeft p).range.FiniteIndex ∧
    (cubeCorrespondenceRight p).range.FiniteIndex := by
  let : (cubePrincipalLevel p).FiniteIndex := cubePrincipalLevel_finiteIndex p hp
  exact ⟨cubeCorrespondenceLeft_injective p hp,cubeCorrespondenceRight_injective p hp,
    Subgroup.finiteIndex_of_le (cubePrincipalLevel_le_left_range p),
    Subgroup.finiteIndex_of_le (cubePrincipalLevel_le_right_range p)⟩

end


end CubicKubota


end

end OAI

end


