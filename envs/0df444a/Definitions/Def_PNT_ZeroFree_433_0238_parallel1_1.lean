-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0238_parallel1_1
-- name    : PNT_ZeroFree_433_0238_parallel1_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:22:47.547659+00:00
-- url     : https://prove2.me/theorems/ce39519e-2154-4c00-9e75-d4667ee65112
-- title:
--   Zero-free region foundations: Reciprocity.CubeCorrespondence [0238_parallel1_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Reciprocity.CubeCorrespondence
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/CubeCorrespondence.lean#L6-L205

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0068_1
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0083
import Definitions.Def_PNT_ZeroFree_433_0089
import Definitions.Def_PNT_ZeroFree_433_0131_parallel1
import Definitions.Def_PNT_ZeroFree_433_0136_parallel1
import Definitions.Def_PNT_ZeroFree_433_0137_parallel1
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0144_parallel1
import Definitions.Def_PNT_ZeroFree_433_0161_parallel1
import Definitions.Def_PNT_ZeroFree_433_0184_parallel1
import Definitions.Def_PNT_ZeroFree_433_0185_parallel1
import Definitions.Def_PNT_ZeroFree_433_0190_parallel1
import Definitions.Def_PNT_ZeroFree_433_0203_parallel1
import Definitions.Def_PNT_ZeroFree_433_0221_parallel1
import Definitions.Def_PNT_ZeroFree_433_0228_parallel1
import Definitions.Def_PNT_ZeroFree_433_0231_parallel1
import Definitions.Def_PNT_ZeroFree_433_0263_parallel1
import Definitions.Def_PNT_ZeroFree_433_0332_parallel1
import Definitions.Def_PNT_ZeroFree_433_0506_parallel1_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/CubeCorrespondence.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace RSLocal

instance (priority := 100) finiteIndex_comap {G H : Type*} [Group G] [Group H]
    (N : Subgroup H) [N.FiniteIndex] (f : G →* H) : (N.comap f).FiniteIndex := by
  constructor
  rw [Subgroup.index_comap]
  exact (Subgroup.isFiniteRelIndex_of_finiteIndex (H := N) (K := f.range)).relIndex_ne_zero

end RSLocal

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

def cubeDiagonal (p : Eis) : Matrix (Fin 2) (Fin 2) Eis := !![p^3,0;0,1]

def cubeCorrespondence (p : Eis) : Subgroup (levelThree × levelThree) where
  carrier := {MN | cubeDiagonal p * (MN.1 : SL(2,Eis)).val =
    (MN.2 : SL(2,Eis)).val * cubeDiagonal p}
  one_mem' := by simp
  mul_mem' := by
    rintro ⟨M,N⟩ ⟨M',N'⟩ h h'
    change cubeDiagonal p * ((M : SL(2,Eis)).val * (M' : SL(2,Eis)).val) =
      ((N : SL(2,Eis)).val * (N' : SL(2,Eis)).val) * cubeDiagonal p
    calc
      _ = (cubeDiagonal p * (M : SL(2,Eis)).val) * (M' : SL(2,Eis)).val :=
        (Matrix.mul_assoc _ _ _).symm
      _ = ((N : SL(2,Eis)).val * cubeDiagonal p) * (M' : SL(2,Eis)).val := by rw [h]
      _ = (N : SL(2,Eis)).val * (cubeDiagonal p * (M' : SL(2,Eis)).val) := Matrix.mul_assoc _ _ _
      _ = (N : SL(2,Eis)).val * ((N' : SL(2,Eis)).val * cubeDiagonal p) := by rw [h']
      _ = _ := (Matrix.mul_assoc _ _ _).symm
  inv_mem' := by
    rintro ⟨M,N⟩ h
    change cubeDiagonal p * ((M : SL(2,Eis))⁻¹).val =
      ((N : SL(2,Eis))⁻¹).val * cubeDiagonal p
    calc
      _ = (((N : SL(2,Eis))⁻¹).val * ((N : SL(2,Eis)).val * cubeDiagonal p)) *
          ((M : SL(2,Eis))⁻¹).val := by
        simp only [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
          inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
      _ = (((N : SL(2,Eis))⁻¹).val * (cubeDiagonal p * (M : SL(2,Eis)).val)) *
          ((M : SL(2,Eis))⁻¹).val := by rw [h]
      _ = _ := by
        simp only [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
          mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]

def cubeCorrespondenceLeft (p : Eis) : cubeCorrespondence p →* levelThree :=
  (MonoidHom.fst levelThree levelThree).comp (cubeCorrespondence p).subtype

def cubeCorrespondenceRight (p : Eis) : cubeCorrespondence p →* levelThree :=
  (MonoidHom.snd levelThree levelThree).comp (cubeCorrespondence p).subtype

lemma cubeCorrespondence_entries (p : Eis) (MN : cubeCorrespondence p) :
    p^3 * ((MN.1.1 : levelThree) : SL(2,Eis)) 0 0 =
      (((MN.1.2 : levelThree) : SL(2,Eis)) 0 0) * p^3 ∧
    p^3 * ((MN.1.1 : levelThree) : SL(2,Eis)) 0 1 =
      (((MN.1.2 : levelThree) : SL(2,Eis)) 0 1) ∧
    (((MN.1.1 : levelThree) : SL(2,Eis)) 1 0) =
      (((MN.1.2 : levelThree) : SL(2,Eis)) 1 0) * p^3 ∧
    (((MN.1.1 : levelThree) : SL(2,Eis)) 1 1) =
      (((MN.1.2 : levelThree) : SL(2,Eis)) 1 1) := by
  have h := MN.property
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) Eis => A 0 0) h
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) Eis => A 0 1) h
  have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) Eis => A 1 0) h
  have h11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) Eis => A 1 1) h
  norm_num [cubeDiagonal, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  exact ⟨h00,h01,h10,h11⟩

lemma cubeCorrespondenceLeft_injective (p : Eis) (hp : p ≠ 0) :
    Function.Injective (cubeCorrespondenceLeft p) := by
  intro x y h
  have hx := cubeCorrespondence_entries p x
  have hy := cubeCorrespondence_entries p y
  have hM : x.1.1=y.1.1 := h
  apply Subtype.ext
  apply Prod.ext hM
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact mul_right_cancel₀ (pow_ne_zero 3 hp) (hx.1.symm.trans (by rw [hM]; exact hy.1))
  · exact hx.2.1.symm.trans (by rw [hM]; exact hy.2.1)
  · exact mul_right_cancel₀ (pow_ne_zero 3 hp) (hx.2.2.1.symm.trans (by rw [hM]; exact hy.2.2.1))
  · exact hx.2.2.2.symm.trans (by rw [hM]; exact hy.2.2.2)

lemma cubeCorrespondenceRight_injective (p : Eis) (hp : p ≠ 0) :
    Function.Injective (cubeCorrespondenceRight p) := by
  intro x y h
  have hx := cubeCorrespondence_entries p x
  have hy := cubeCorrespondence_entries p y
  have hN : x.1.2=y.1.2 := h
  apply Subtype.ext
  refine Prod.ext ?_ hN
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact mul_left_cancel₀ (pow_ne_zero 3 hp) (hx.1.trans (by rw [hN]; exact hy.1.symm))
  · exact mul_left_cancel₀ (pow_ne_zero 3 hp) (hx.2.1.trans (by rw [hN]; exact hy.2.1.symm))
  · exact hx.2.2.1.trans (by rw [hN]; exact hy.2.2.1.symm)
  · exact hx.2.2.2.trans (by rw [hN]; exact hy.2.2.2.symm)

lemma cubeCorrespondence_value (p : Eis) (hp : p ≠ 0) (MN : cubeCorrespondence p) :
    value (cubeCorrespondenceLeft p MN) = value (cubeCorrespondenceRight p MN) := by
  have he := cubeCorrespondence_entries p MN
  let M : levelThree := MN.1.1
  let N : levelThree := MN.1.2
  have ha : (M : SL(2,Eis)) 0 0 = (N : SL(2,Eis)) 0 0 :=
    mul_left_cancel₀ (pow_ne_zero 3 hp) (he.1.trans (mul_comm _ _))
  have hc : (M : SL(2,Eis)) 1 0 = p^3 * (N : SL(2,Eis)) 1 0 :=
    he.2.2.1.trans (mul_comm _ _)
  have hd : (M : SL(2,Eis)) 0 0 * (M : SL(2,Eis)) 1 1 -
      (M : SL(2,Eis)) 0 1 * (M : SL(2,Eis)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (M : SL(2,Eis)).property
  have hcop : IsCoprime p ((N : SL(2,Eis)) 0 0) := by
    refine ⟨-(M : SL(2,Eis)) 0 1 * p^2 * (N : SL(2,Eis)) 1 0,
      (M : SL(2,Eis)) 1 1,?_⟩
    rw [ha,hc] at hd
    linear_combination hd
  change symbol ((M : SL(2,Eis)) 1 0) ((M : SL(2,Eis)) 0 0) =
    symbol ((N : SL(2,Eis)) 1 0) ((N : SL(2,Eis)) 0 0)
  rw [ha,hc,symbol_mul_numerator _ _ _ (levelThree_primary N),
    symbol_pow_numerator _ _ (levelThree_primary N),
    symbol_cube_of_isCoprime _ _ (levelThree_primary N) hcop,one_mul]


end


end CubicKubota


end

end OAI

end


