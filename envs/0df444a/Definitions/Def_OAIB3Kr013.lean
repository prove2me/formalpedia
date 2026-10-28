-- Prove2me | Definitions.Def_OAIB3Kr013
-- name    : OAIB3Kr013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T17:22:11.155987+00:00
-- url     : https://prove2.me/theorems/e51fe6b6-875a-49bf-874e-e3b2609a6d86
-- title:
--   Definitions bundle OAIB3Kr013 of the split of OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 246 declarations of OpenAI's Lean: 72 definitions, 4 instances and 170 theorems. The definitions and types are `OAI.KirchbergRordam.GeneralEndpointMultiplicity.rightBase`, `OAI.KirchbergRordam.GeneralEndpointMultiplicity.rightRep`, `OAI.KirchbergRordam.GenericRW.FieldCalculus.Data.Matrices`, `OAI.KirchbergRordam.GenericRW.FieldCalculus.Data.coeff`, `OAI.KirchbergRordam.GenericRW.FieldCalculus.Data.matrices`, `OAI.KirchbergRordam.GenericRW.FieldCalculus.Data.scalarMul`, `OAI.KirchbergRordam.GenericRW.FlipPath.block`, `OAI.KirchbergRordam.GenericRW.FlipPath.conePath`, `OAI.KirchbergRordam.GenericRW.FlipPath.flatK`, `OAI.KirchbergRordam.GenericRW.FlipPath.scalarG`, `OAI.KirchbergRordam.GenericRW.FlipPath.scalarQ`, `OAI.KirchbergRordam.GenericRW.FlipPath.weightedC`, `OAI.KirchbergRordam.GenericRW.FlipPath.weightedK`, `OAI.KirchbergRordam.GenericRW.FullRankWeighted.instPartialOrderAlgebra`, `OAI.KirchbergRordam.GenericRW.FullRankWeighted.ofSquareZero`, `OAI.KirchbergRordam.GenericRW.FullRankWeighted.power`, `OAI.KirchbergRordam.GenericRW.FullRankWeighted.tensor`, `OAI.KirchbergRordam.GenericRW.HereditaryTransport.conjugate`, `OAI.KirchbergRordam.GenericRW.HereditaryTransport.copies`, `OAI.KirchbergRordam.GenericRW.HereditaryTransport.copy`, `OAI.KirchbergRordam.GenericRW.HereditaryTransport.cross`, `OAI.KirchbergRordam.GenericRW.HereditaryTransport.crossLinear`, `OAI.KirchbergRordam.GenericRW.HereditaryTransport.embed`, `OAI.KirchbergRordam.GenericRW.HereditaryTransport.hom`, `OAI.KirchbergRordam.GenericRW.HereditaryTransport.tripleUnits`, `OAI.KirchbergRordam.GenericRW.MaxTensor.columnWord`, `OAI.KirchbergRordam.GenericRW.MaxTensor.cornerWord`, `OAI.KirchbergRordam.GenericRW.MaxTensor.defectWord`, `OAI.KirchbergRordam.GenericRW.MaxTensor.instPartialOrderAlgebra`, `OAI.KirchbergRordam.GenericRW.MaxTensor.map`, `OAI.KirchbergRordam.GenericRW.MaxTensor.powerHom`, `OAI.KirchbergRordam.GenericRW.OrderZero.Pair.actionLeft`, `OAI.KirchbergRordam.GenericRW.OrderZero.Pair.actionRight`, `OAI.KirchbergRordam.GenericRW.OrderZero.Pair.dimensionDropHom`, `OAI.KirchbergRordam.GenericRW.OrderZero.Pair.instSMulComplexSubtypeContinuousMapElemRealUnitIntervalMemNonUnitalStarSubalgebraDomainProdField`, `OAI.KirchbergRordam.GenericRW.OrderZero.Pair.liftLinear`, `OAI.KirchbergRordam.GenericRW.OrderZero.Pair.weighted`, `OAI.KirchbergRordam.GenericRW.OrderZero.WeightedUnits.coneHom`, `OAI.KirchbergRordam.GenericRW.OrderZero.WeightedUnits.cutoffHom`, `OAI.KirchbergRordam.GenericRW.OrderZero.WeightedUnits.defectCopies` and 32 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CharacterCriterion_AmplifiedComparison`, `CharacterCriterion_BalancedLimit`, `CharacterCriterion_ConeModel`, `CharacterCriterion_DropSections`, `CharacterCriterion_FieldCalculus`, `CharacterCriterion_FiniteDrop`, `CharacterCriterion_FlipPath`, `CharacterCriterion_FullComparison`, `CharacterCriterion_FunctionalCalculus`, `CharacterCriterion_GeneralSystem`, `CharacterCriterion_HereditaryTransport`, `CharacterCriterion_MinTensor`, `CharacterCriterion_OrderZero`, `CharacterCriterion_OrderZeroPair`, `CharacterCriterion_PrimeChannels`, `CharacterCriterion_PrimePresentation`, `CharacterCriterion_RepresentedLabels`, `CharacterCriterion_SpatialTensor`, `CharacterCriterion_TensorSections`, `CharacterCriterion_WeightedUnits`.
--
--   **Imports.** It imports the published bundle `Def_CharacterCriterion`; the bundles `OAIB3Kr010`, `OAIB3Kr011` and `OAIB3Kr012` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIB3Kr015`; the statement `OAI.KirchbergRordam.PrimeDropPresentation.Channels.finite_control`; the proofs of `OAI.KirchbergRordam.GenericRW.FullSquareZero.exists_full_square_zero`, `OAI.KirchbergRordam.PrimeDropPresentation.central_no_character`, `OAI.KirchbergRordam.PrimeDropPresentation.stage_to_central`, `OAI.KirchbergRordam.PrimeSquareUnitary.fibers`, `OAI.KirchbergRordam.character_criterion` and `OAI.KirchbergRordam.spatial_absorption_of_central_maximal_half_flip`.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr010
import Definitions.Def_OAIB3Kr011
import Definitions.Def_OAIB3Kr012

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_RepresentedLabels
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PureStates.locallyConvexReal _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology


namespace KirchbergRordam.GenericRW.TripleTensor
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor
lemma first_second (a : A) (b : B) :
    Commute (first (C := C) a) (second (A := A) b) := legs_commute _ _
lemma first_third (a : A) (c : C) :
    Commute (first (B := B) a) (third (A := A) c) := legs_commute _ _
lemma second_third (b : B) (c : C) :
    Commute (second (A := A) b) (third (A := A) c) := (legs_commute b c).map includeRight

variable {E : Type*} [CStarAlgebra E]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


def complementSecond (π : Algebra A B C →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    MaxTensor.Algebra A C →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  MaxTensor.lift (A := A) (B := C) (C := H →L[ℂ] H)
    (π.comp first) (π.comp third) (fun a c => (first_third a c).map π)

def complementThird (π : Algebra A B C →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    MaxTensor.Algebra A B →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  MaxTensor.lift (A := A) (B := B) (C := H →L[ℂ] H)
    (π.comp first) (π.comp second) (fun a b => (first_second a b).map π)
end KirchbergRordam.GenericRW.TripleTensor
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_SpatialTensor
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace


open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.GenericRW.MaxTensor
universe u
variable {A B C E F : Type u} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  [CStarAlgebra E] [CStarAlgebra F]

def map (φ : A →⋆ₐ[ℂ] E) (ψ : B →⋆ₐ[ℂ] F) : Algebra A B →⋆ₐ[ℂ] Algebra E F :=
  lift (includeLeft.comp φ) (includeRight.comp ψ) (fun a b => legs_commute (φ a) (ψ b))
end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.GenericRW.TripleTensor
universe u
variable {A B C : Type u} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor

def firstTwo : MaxTensor.Algebra A B →⋆ₐ[ℂ] Algebra A B C :=
  lift first second first_second

lemma firstTwo_third (ab : MaxTensor.Algebra A B) (c : C) :
    Commute (firstTwo ab) (third c) := by
  apply Commute.symm
  apply MaxTensor.commute_of_legs firstTwo (third c) ?_ ?_ ab
  · intro a
    have he := DFunLike.congr_fun (lift_includeLeft (first (A := A) (B := B) (C := C))
      (second (A := A) (B := B) (C := C)) first_second) a
    change firstTwo (includeLeft a) = first a at he
    rw [he]
    exact (first_third a c).symm
  · intro b
    have he := DFunLike.congr_fun (lift_includeRight (first (A := A) (B := B) (C := C))
      (second (A := A) (B := B) (C := C)) first_second) b
    change firstTwo (includeRight b) = second b at he
    rw [he]
    exact (second_third b c).symm


def reassociate : MaxTensor.Algebra (MaxTensor.Algebra A B) C →⋆ₐ[ℂ] Algebra A B C :=
  lift firstTwo third firstTwo_third
end KirchbergRordam.GenericRW.TripleTensor

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_HereditaryTransport
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.ConeModel.coneSubringClass _root_.OAI.KirchbergRordam.GenericRW.ConeModel.defectClosed _root_.OAI.KirchbergRordam.GenericRW.ConeModel.defectZero _root_.OAI.KirchbergRordam.GenericRW.ConeModel.instCStarAlgebraSubtypeContinuousMapElemRealUnitIntervalM2MemStarSubalgebraComplexCone _root_.OAI.KirchbergRordam.GenericRW.ConeModel.instNonUnitalCStarAlgebraSubtypeContinuousMapElemRealUnitIntervalM2MemStarSubalgebraComplexConeNonUnitalStarSubalgebraDefect _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelFintype _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.GenericRW.dimensionDropClosed _root_.OAI.KirchbergRordam.GenericRW.dropSubringClass _root_.OAI.KirchbergRordam.GenericRW.instCStarAlgebraSubtypeContinuousMapElemRealUnitIntervalM6MemStarSubalgebraComplexDimensionDrop23 _root_.OAI.KirchbergRordam.GenericRW.instFiniteDimensionalComplexM6 _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n


namespace KirchbergRordam.GenericRW

open scoped ContinuousMapZero BigOperators ComplexOrder

namespace SquareZeroCone.WeightedMatrix
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedMatrix A)

def coneHom : ConeModel.Cone →⋆ₐ[ℂ] A :=
  ((Unitization.starLift (R := ℂ) (A := ConeMatrix) (C := A)) W.matrixHom).comp
    ConeModel.equiv.symm.toStarAlgHom

lemma coneHom_corner (i j : Fin rankNum) : W.coneHom (ConeModel.corner i j) = W.x i j := by
  change (Unitization.starLift W.matrixHom)
    (ConeModel.equiv.symm (ConeModel.toCone
      (Unitization.inr (Matrix.single i j (IntervalCalculus.coordMul 1))))) = _
  rw [show ConeModel.toCone = ConeModel.equiv.toStarAlgHom from rfl]
  change (Unitization.starLift W.matrixHom) (ConeModel.equiv.symm
    (ConeModel.equiv (Unitization.inr (Matrix.single i j (IntervalCalculus.coordMul 1))))) = _
  rw [StarAlgEquiv.symm_apply_apply]
  change algebraMap ℂ A 0 + W.matrixHom (Matrix.single i j (IntervalCalculus.coordMul 1)) = W.x i j
  rw [map_zero, zero_add, W.matrixHom_single, W.coeff_coordMul, map_one, mul_one]
end SquareZeroCone.WeightedMatrix
end KirchbergRordam.GenericRW


namespace KirchbergRordam.GenericRW.HereditaryTransport
open ClosedRightRange
variable {A : Type*} [CStarAlgebra A]


instance instNonUnitalCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplexCorner (a : A) (ha : IsSelfAdjoint a) : NonUnitalCStarAlgebra (corner a ha) := inferInstance

def embed (a : A) (ha : IsSelfAdjoint a) (x : A) : corner a ha := ⟨a*x*a,mem_corner a ha x⟩

lemma dense (a : A) (ha : IsSelfAdjoint a) : DenseRange (embed a ha) := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro x
  rw [closure_subtype]
  change (x : A) ∈ closure (Subtype.val '' Set.range (embed a ha))
  have h : Subtype.val '' Set.range (embed a ha) = Set.range (fun z : A => a*z*a) := by
    ext y
    simp only [Set.mem_image,Set.mem_range]
    constructor
    · rintro ⟨_,⟨z,rfl⟩,rfl⟩; exact ⟨z,rfl⟩
    · rintro ⟨z,rfl⟩; exact ⟨embed a ha z,⟨z,rfl⟩,rfl⟩
  rw [h]
  exact x.property

variable {a v : A} (ha : IsSelfAdjoint a) (hv : star a*a=star v*v)


include hv

lemma left_embed (x : A) : left (v := v) ha (embed a ha x)=v*x*a := by
  unfold left
  have he : (⟨(embed a ha x : A),in_space (embed a ha x).property⟩ : space a) =
      ClosedRightRange.embed a (x*a) := Subtype.ext (mul_assoc a x a)
  rw [he,transport_embed hv,mul_assoc]

lemma star_left_mem (x : corner a ha) : star (left (v := v) ha x) ∈ space a := by
  refine (dense a ha).induction_on x ((closed a).preimage (continuous_left ha).star) ?_
  intro y
  rw [left_embed ha hv,star_mul,ha.star_eq]
  exact mem_space a (star (v*y))


def conjugate (x : corner a ha) : A :=
  star (transport a v ⟨star (left (v := v) ha x),star_left_mem ha hv x⟩)

lemma continuous_conjugate : Continuous (conjugate ha hv) := by
  exact ((transport a v).continuous.comp
    ((continuous_left ha).star.subtype_mk _)).star

lemma conjugate_embed (x : A) : conjugate ha hv (embed a ha x)=v*x*star v := by
  unfold conjugate
  have he : star (left (v := v) ha (embed a ha x))=a*(star x*star v) := by
    rw [left_embed ha hv,star_mul,star_mul,ha.star_eq]
  change star (transport a v ⟨_,_⟩)=_
  rw [show (⟨star (left (v := v) ha (embed a ha x)),_⟩ : space a)=
    ClosedRightRange.embed a (star x*star v) from Subtype.ext he]
  rw [transport_embed hv,star_mul,star_mul,star_star,star_star]

lemma conjugate_add (x y : corner a ha) : conjugate ha hv (x+y)=conjugate ha hv x+conjugate ha hv y := by
  refine (dense a ha).induction_on₂
    (isClosed_eq ((continuous_conjugate ha hv).comp (continuous_fst.add continuous_snd))
      (((continuous_conjugate ha hv).comp continuous_fst).add
        ((continuous_conjugate ha hv).comp continuous_snd))) ?_ x y
  intro x y
  have he : embed a ha x+embed a ha y=embed a ha (x+y) := by ext; change a*x*a+a*y*a=a*(x+y)*a; noncomm_ring
  rw [he,conjugate_embed,conjugate_embed,conjugate_embed]
  noncomm_ring

lemma conjugate_zero : conjugate ha hv 0=0 := by
  have hz : embed a ha (0 : A)=0 := by ext; simp [embed]
  rw [← hz,conjugate_embed]; simp

lemma conjugate_smul (c : ℂ) (x : corner a ha) : conjugate ha hv (c • x)=c • conjugate ha hv x := by
  refine (dense a ha).induction_on x (isClosed_eq
    ((continuous_conjugate ha hv).comp (continuous_const_smul c))
    ((continuous_conjugate ha hv).const_smul c)) ?_
  intro x
  have he : c • embed a ha x=embed a ha (c • x) := by
    ext; change c • (a*x*a)=a*(c • x)*a; simp only [mul_smul_comm,smul_mul_assoc]
  rw [he,conjugate_embed,conjugate_embed]
  simp only [mul_smul_comm,smul_mul_assoc]

lemma conjugate_mul (x y : corner a ha) : conjugate ha hv (x*y)=conjugate ha hv x*conjugate ha hv y := by
  refine (dense a ha).induction_on₂
    (isClosed_eq ((continuous_conjugate ha hv).comp (continuous_fst.mul continuous_snd))
      (((continuous_conjugate ha hv).comp continuous_fst).mul
        ((continuous_conjugate ha hv).comp continuous_snd))) ?_ x y
  intro x y
  have he : embed a ha x*embed a ha y=embed a ha (x*a*a*y) := by ext; change (a*x*a)*(a*y*a)=a*(x*a*a*y)*a; noncomm_ring
  rw [he,conjugate_embed,conjugate_embed,conjugate_embed]
  calc
    _=v*x*(star a*a)*y*star v := by rw [ha.star_eq]; noncomm_ring
    _=v*x*(star v*v)*y*star v := by rw [hv]
    _=_ := by noncomm_ring

lemma conjugate_star (x : corner a ha) : conjugate ha hv (star x)=star (conjugate ha hv x) := by
  refine (dense a ha).induction_on x (isClosed_eq
    ((continuous_conjugate ha hv).comp continuous_star) (continuous_conjugate ha hv).star) ?_
  intro x
  have he : star (embed a ha x)=embed a ha (star x) := by
    ext; change star (a*x*a)=a*star x*a; rw [star_mul,star_mul,ha.star_eq]; noncomm_ring
  rw [he,conjugate_embed,conjugate_embed,star_mul,star_mul,star_star]
  noncomm_ring


def hom : corner a ha →⋆ₙₐ[ℂ] A where
  toFun := conjugate ha hv
  map_zero' := conjugate_zero ha hv
  map_add' := conjugate_add ha hv
  map_mul' := conjugate_mul ha hv
  map_smul' := conjugate_smul ha hv
  map_star' := conjugate_star ha hv

end KirchbergRordam.GenericRW.HereditaryTransport

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_ConeModel
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelFintype _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.GenericRW.dimensionDropClosed _root_.OAI.KirchbergRordam.GenericRW.dropSubringClass _root_.OAI.KirchbergRordam.GenericRW.instCStarAlgebraSubtypeContinuousMapElemRealUnitIntervalM6MemStarSubalgebraComplexDimensionDrop23 _root_.OAI.KirchbergRordam.GenericRW.instFiniteDimensionalComplexM6 _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]

namespace KirchbergRordam.GenericRW.SquareZeroCone.WeightedMatrix
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedMatrix A)

lemma coneHom_scalar (f : C(unitInterval,ℂ)) : W.coneHom (ConeModel.scalar f)=W.eval f := by
  have he : W.coneHom.comp ConeModel.scalar=W.eval := by
    apply IntervalCalculus.ext_coord
    change W.coneHom (ConeModel.scalar IntervalCalculus.coord)=W.eval _
    rw [ConeModel.scalar_coord,map_sum]
    simp only [W.coneHom_corner,W.diagonal]
    exact (IntervalCalculus.hom_coord W.h_nonneg W.norm_h_le).symm
  exact DFunLike.congr_fun he f

lemma coneHom_tip : W.coneHom ConeModel.tip=1-W.h := by
  rw [coneHom_scalar,map_sub,map_one,IntervalCalculus.hom_coord]

lemma coneHom_hereditary (f : HereditaryTransport.corner ConeModel.tip ConeModel.tip_selfAdjoint) :
    W.coneHom f ∈ HereditaryTransport.corner (1-W.h)
      ((IsSelfAdjoint.one A).sub (IsSelfAdjoint.of_nonneg W.h_nonneg)) := by
  let ha := (IsSelfAdjoint.one A).sub (IsSelfAdjoint.of_nonneg W.h_nonneg)
  refine (HereditaryTransport.dense ConeModel.tip ConeModel.tip_selfAdjoint).induction_on f
    ((HereditaryTransport.cornerClosed (1-W.h) ha).preimage
      ((map_continuous W.coneHom).comp continuous_subtype_val)) ?_
  intro x
  change W.coneHom (ConeModel.tip*x*ConeModel.tip) ∈ _
  rw [map_mul,map_mul,W.coneHom_tip]
  exact HereditaryTransport.mem_corner (1-W.h) ha (W.coneHom x)

end KirchbergRordam.GenericRW.SquareZeroCone.WeightedMatrix

namespace KirchbergRordam.GenericRW.SquareZeroCone.WeightedMatrix
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedMatrix A)


def defectHom : ConeModel.Defect →⋆ₙₐ[ℂ] HereditaryTransport.corner (1-W.h)
    ((IsSelfAdjoint.one A).sub (IsSelfAdjoint.of_nonneg W.h_nonneg)) where
  toFun f := ⟨W.coneHom (f:ConeModel.Cone),W.coneHom_hereditary (ConeModel.toHereditary f)⟩
  map_zero' := Subtype.ext (map_zero W.coneHom)
  map_add' _ _ := Subtype.ext (map_add W.coneHom _ _)
  map_mul' _ _ := Subtype.ext (map_mul W.coneHom _ _)
  map_smul' c _ := Subtype.ext (map_smul W.coneHom c _)
  map_star' _ := Subtype.ext (map_star W.coneHom _)

lemma defectHom_scalar (f : C(unitInterval,ℂ)) (hf : f 1=0) :
    (W.defectHom (ConeModel.scalarDefect f hf):A)=W.eval f := W.coneHom_scalar f

end KirchbergRordam.GenericRW.SquareZeroCone.WeightedMatrix
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FlipPath
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelFintype _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.GenericRW.dimensionDropClosed _root_.OAI.KirchbergRordam.GenericRW.dropSubringClass _root_.OAI.KirchbergRordam.GenericRW.instCStarAlgebraSubtypeContinuousMapElemRealUnitIntervalM6MemStarSubalgebraComplexDimensionDrop23 _root_.OAI.KirchbergRordam.GenericRW.instFiniteDimensionalComplexM6 _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n


namespace KirchbergRordam.GenericRW.FlipPath
open scoped BigOperators



def block : M4 →+* Matrix (Fin rankNum) (Fin rankNum) ConeModel.M2 where
  toFun m j k := CStarMatrix.ofMatrix (fun r s => m (r,j) (s,k))
  map_zero' := rfl
  map_add' _ _ := rfl
  map_one' := by
    ext j k r s
    change (if (r,j)=(s,k) then (1:ℂ) else 0)=((1 : Matrix (Fin rankNum) (Fin rankNum) ConeModel.M2) j k) r s
    by_cases hjk : j=k
    · subst k; simp [Prod.mk.injEq,CStarMatrix.one_apply]
    · simp [hjk,Prod.mk.injEq,CStarMatrix.zero_apply]
  map_mul' m n := by
    ext j k r s
    change (∑ u : Fin rankNum × Fin rankNum,m (r,j) u*n u (s,k))=
      ((∑ l : Fin rankNum,(CStarMatrix.ofMatrix (fun r s => m (r,j) (s,l)))*
        (CStarMatrix.ofMatrix (fun r s => n (r,l) (s,k)))) r s)
    simp only [Fintype.sum_prod_type, ConeModel.matrixSum_entry, CStarMatrix.mul_apply]
    change (∑ a : Fin rankNum, ∑ b : Fin rankNum, m (r,j) (a,b) * n (a,b) (s,k)) =
      ∑ b : Fin rankNum, ∑ a : Fin rankNum, m (r,j) (a,b) * n (a,b) (s,k)
    exact Finset.sum_comm

lemma block_star (m : M4) : block (star m)=star (block m) := rfl


def conePath (j k : Fin rankNum) : ConeModel.Cone :=
  ⟨⟨fun t => block (path t) j k,by
      change Continuous (fun t : unitInterval => (fun r s => path t (r,j) (s,k)))
      exact continuous_pi fun r => continuous_pi fun s =>
        (continuous_apply (s,k)).comp ((continuous_apply (r,j)).comp path_continuous)⟩,by
    change block (path 0) j k ∈ (⊥ : StarSubalgebra ℂ ConeModel.M2)
    rw [path_zero,map_one,Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

lemma conePath_star_mul (i j : Fin rankNum) :
    ∑ k,star (conePath k i)*conePath k j=if i=j then 1 else 0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  have h := congrArg (fun m => block m i j) (path_star_mul t)
  rw [map_mul,block_star,map_one] at h
  simp only [Matrix.mul_apply,Matrix.star_apply,Matrix.one_apply] at h
  rw [ConeModel.evaluate_sum]
  by_cases hij : i=j
  · rw [ite_eq_left hij] at h ⊢; exact h
  · rw [ite_eq_right hij] at h ⊢; exact h

lemma conePath_mul_star (i j : Fin rankNum) :
    ∑ k,conePath i k*star (conePath j k)=if i=j then 1 else 0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  have h := congrArg (fun m => block m i j) (path_mul_star t)
  rw [map_mul,block_star,map_one] at h
  simp only [Matrix.mul_apply,Matrix.star_apply,Matrix.one_apply] at h
  rw [ConeModel.evaluate_sum]
  by_cases hij : i=j
  · rw [ite_eq_left hij] at h ⊢; exact h
  · rw [ite_eq_right hij] at h ⊢; exact h

end KirchbergRordam.GenericRW.FlipPath

namespace KirchbergRordam.GenericRW.FlipPath
open scoped BigOperators
open ConeModel RWFunctions

def flatK (i j : Fin rankNum) : Cone := scalar q*star (conePath j i)

def weightedK : Matrix (Fin rankNum) (Fin rankNum) Defect := fun i j => ⟨flatK i j,by
  change algebraMap ℂ ConeModel.M2 (q 1)*star ((conePath j i : C(unitInterval,ConeModel.M2)) 1)=0
  rw [q_one,map_zero,zero_mul]⟩

def scalarG : Defect := scalarDefect g g_one

def scalarQ : Defect := scalarDefect q q_one

lemma scalarQ_star : star scalarQ=scalarQ := by
  apply Subtype.ext
  change star (scalar q)=scalar q
  rw [← map_star,q_star]

lemma scalarQ_sq : scalarQ*scalarQ=scalarG := by
  apply Subtype.ext
  change scalar q*scalar q=scalar g
  rw [← map_mul,q_sq]

lemma weighted_mul (x y : Cone) : (x*scalar q)*(scalar q*y)=scalar g*(x*y) := by
  calc
    _=x*(scalar q*scalar q)*y := by noncomm_ring
    _=x*scalar g*y := by rw [← map_mul,q_sq]
    _=_ := by rw [← (scalar_commute g x).eq]; noncomm_ring

lemma weighted_mul' (x y : Cone) : (scalar q*x)*(y*scalar q)=scalar g*(x*y) := by
  rw [(scalar_commute q x).eq,← (scalar_commute q y).eq]
  exact weighted_mul x y

lemma flatK_star_mul (i j : Fin rankNum) :
    ∑ k,star (flatK k i)*flatK k j=if i=j then scalar g else 0 := by
  simp only [flatK,star_mul,star_star,← map_star,q_star,weighted_mul]
  rw [← Finset.mul_sum,conePath_mul_star]
  split_ifs <;> simp

lemma flatK_mul_star (i j : Fin rankNum) :
    ∑ k,flatK i k*star (flatK j k)=if i=j then scalar g else 0 := by
  simp only [flatK,star_mul,star_star,← map_star,q_star,weighted_mul']
  rw [← Finset.mul_sum,conePath_star_mul]
  split_ifs <;> simp

lemma coe_defect_sum {ι : Type*} (s : Finset ι) (f : ι → Defect) :
    ((∑ i ∈ s, f i : Defect):Cone) = ∑ i ∈ s, (f i:Cone) :=
  map_sum (NonUnitalStarSubalgebraClass.subtype Defect) f s

lemma weightedK_star_mul :
    (star weightedK*weightedK : Matrix (Fin rankNum) (Fin rankNum) Defect) =
      Matrix.diagonal (fun _ => scalarG) := by
  apply Matrix.ext; intro i j
  apply Subtype.ext
  have h := flatK_star_mul i j
  simp only [Matrix.mul_apply,Matrix.star_apply,Matrix.diagonal_apply]
  rw [coe_defect_sum]
  by_cases hij : i=j
  · rw [ite_eq_left hij] at h ⊢; exact h
  · rw [ite_eq_right hij] at h ⊢; exact h

lemma weightedK_mul_star :
    (weightedK*star weightedK : Matrix (Fin rankNum) (Fin rankNum) Defect) =
      Matrix.diagonal (fun _ => scalarG) := by
  apply Matrix.ext; intro i j
  apply Subtype.ext
  have h := flatK_mul_star i j
  simp only [Matrix.mul_apply,Matrix.star_apply,Matrix.diagonal_apply]
  rw [coe_defect_sum]
  by_cases hij : i=j
  · rw [ite_eq_left hij] at h ⊢; exact h
  · rw [ite_eq_right hij] at h ⊢; exact h

end KirchbergRordam.GenericRW.FlipPath
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_OrderZero
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelFintype _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.GenericRW.dimensionDropClosed _root_.OAI.KirchbergRordam.GenericRW.dropSubringClass _root_.OAI.KirchbergRordam.GenericRW.instCStarAlgebraSubtypeContinuousMapElemRealUnitIntervalM6MemStarSubalgebraComplexDimensionDrop23 _root_.OAI.KirchbergRordam.GenericRW.instFiniteDimensionalComplexM6 _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n


namespace KirchbergRordam.GenericRW.HereditaryTransport
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {a : A} (ha : IsSelfAdjoint a) (s : ι → A)
variable (hs : ∀ i j, star (s i)*s j=if i=j then star a*a else 0)

def copy (i : ι) : corner a ha →⋆ₙₐ[ℂ] A := hom ha (copy_norm s hs i)

omit [Fintype ι] in
lemma copy_embed (i : ι) (x : A) : copy ha s hs i (embed a ha x)=s i*x*star (s i) :=
  conjugate_embed ha (copy_norm s hs i) x

omit [Fintype ι] in
lemma continuous_copy (i : ι) : Continuous (copy ha s hs i) :=
  continuous_conjugate ha (copy_norm s hs i)

omit [Fintype ι] in
lemma copy_orthogonal {i j : ι} (hij : i≠j) (x y : corner a ha) :
    copy ha s hs i x*copy ha s hs j y=0 := by
  refine (dense a ha).induction_on₂ (isClosed_eq
    (((continuous_copy ha s hs i).comp continuous_fst).mul
      ((continuous_copy ha s hs j).comp continuous_snd)) continuous_const) ?_ x y
  intro x y
  rw [copy_embed,copy_embed]
  calc
    _=s i*x*(star (s i)*s j)*y*star (s j) := by noncomm_ring
    _=0 := by simp [hs,hij]


def copies : corner a ha →⋆ₙₐ[ℂ] A where
  toFun x := ∑ i,copy ha s hs i x
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum]
  map_star' x := by simp only [map_star,star_sum]
  map_mul' x y := by
    simp only [map_mul,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    symm
    apply Finset.sum_eq_single i
    · intro j _ hij
      exact copy_orthogonal ha s hs hij x y
    · simp

lemma continuous_copies : Continuous (copies ha s hs) :=
  continuous_finsetSum _ fun i _ => continuous_copy ha s hs i

lemma copies_orthogonal (hz : ∀ i, a*s i=0) (x y : corner a ha) :
    (x : A)*copies ha s hs y=0 := by
  change (x:A)*(∑ i,copy ha s hs i y)=0
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i _
  refine (dense a ha).induction_on₂ (isClosed_eq
    (continuous_subtype_val.comp continuous_fst |>.mul
      ((continuous_copy ha s hs i).comp continuous_snd)) continuous_const) ?_ x y
  intro x y
  rw [copy_embed]
  change (a*x*a)*(s i*y*star (s i))=0
  calc
    _=a*x*(a*s i)*y*star (s i) := by noncomm_ring
    _=0 := by rw [hz]; simp


lemma copies_commute (m : ι → ι → A) (hm : ∀ i j, star (m i j)=m j i)
    (hms : ∀ j k i, m j k*s i=if k=i then s j else 0)
    (j k : ι) (x : corner a ha) : Commute (m j k) (copies ha s hs x) := by
  change m j k*copies ha s hs x=copies ha s hs x*m j k
  refine (dense a ha).induction_on x (isClosed_eq
    (continuous_const.mul (continuous_copies ha s hs))
    ((continuous_copies ha s hs).mul continuous_const)) ?_
  intro x
  have hr (i : ι) : star (s i)*m j k=if j=i then star (s k) else 0 := by
    calc
      _=star (m k j*s i) := by rw [star_mul,hm]
      _=_ := by rw [hms]; split_ifs <;> simp
  change m j k*(∑ i,copy ha s hs i (embed a ha x))=
    (∑ i,copy ha s hs i (embed a ha x))*m j k
  simp only [copy_embed,Finset.mul_sum,Finset.sum_mul]
  calc
    _=∑ i,(m j k*s i)*x*star (s i) := by
      apply Finset.sum_congr rfl; intro i _; noncomm_ring
    _=s j*x*star (s k) := by simp [hms]
    _=∑ i,s i*x*(star (s i)*m j k) := by simp [hr]
    _=_ := by apply Finset.sum_congr rfl; intro i _; noncomm_ring

end KirchbergRordam.GenericRW.HereditaryTransport

namespace KirchbergRordam.GenericRW.HereditaryTransport
open ClosedRightRange
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [DecidableEq ι]
variable {a : A} (ha : IsSelfAdjoint a) (s : ι → A)
variable (hs : ∀ i j, star (s i)*s j=if i=j then star a*a else 0)


include hs in
lemma left_cross_inner (i j : ι) (x y : corner a ha) :
    star (left (v := s i) ha x)*left (v := s j) ha y=
      if i=j then star (x:A)*(y:A) else 0 := by
  refine (dense a ha).induction_on₂ (isClosed_eq
    (((continuous_left ha).comp continuous_fst).star.mul
      ((continuous_left ha).comp continuous_snd))
    (by split_ifs <;> fun_prop)) ?_ x y
  intro x y
  rw [left_embed ha (copy_norm s hs i),left_embed ha (copy_norm s hs j),star_mul,star_mul,ha.star_eq]
  change (a*(star x*star (s i)))*(s j*y*a)=if i=j then star (a*x*a)*(a*y*a) else 0
  calc
    _=a*star x*(star (s i)*s j)*y*a := by noncomm_ring
    _=_ := by
      rw [hs]
      split_ifs
      · simp only [ha.star_eq,star_mul]
        noncomm_ring
      · simp


def cross (i j : ι) (x : corner a ha) : A :=
  star (transport a (s j) ⟨star (left (v := s i) ha x),
    star_left_mem ha (copy_norm s hs i) x⟩)

lemma continuous_cross (i j : ι) : Continuous (cross ha s hs i j) :=
  ((transport a (s j)).continuous.comp ((continuous_left ha).star.subtype_mk _)).star

lemma cross_embed (i j : ι) (x : A) : cross ha s hs i j (embed a ha x)=s i*x*star (s j) := by
  unfold cross
  have he : star (left (v := s i) ha (embed a ha x))=a*(star x*star (s i)) := by
    rw [left_embed ha (copy_norm s hs i),star_mul,star_mul,ha.star_eq]
  change star (transport a (s j) ⟨_,_⟩)=_
  rw [show (⟨star (left (v := s i) ha (embed a ha x)),_⟩ : space a)=
    ClosedRightRange.embed a (star x*star (s i)) from Subtype.ext he]
  rw [transport_embed (copy_norm s hs j),star_mul,star_mul,star_star,star_star]

lemma cross_zero (i j : ι) : cross ha s hs i j 0=0 := by
  have hz : embed a ha (0:A)=0 := by ext; simp [HereditaryTransport.embed]
  rw [← hz,cross_embed]; simp

lemma cross_add (i j : ι) (x y : corner a ha) :
    cross ha s hs i j (x+y)=cross ha s hs i j x+cross ha s hs i j y := by
  refine (dense a ha).induction_on₂ (isClosed_eq
    ((continuous_cross ha s hs i j).comp (continuous_fst.add continuous_snd))
    (((continuous_cross ha s hs i j).comp continuous_fst).add
      ((continuous_cross ha s hs i j).comp continuous_snd))) ?_ x y
  intro x y
  have he : embed a ha x+embed a ha y=embed a ha (x+y) := by
    ext; change a*x*a+a*y*a=a*(x+y)*a; noncomm_ring
  rw [he,cross_embed,cross_embed,cross_embed]
  noncomm_ring

lemma cross_smul (i j : ι) (c : ℂ) (x : corner a ha) :
    cross ha s hs i j (c • x)=c • cross ha s hs i j x := by
  refine (dense a ha).induction_on x (isClosed_eq
    ((continuous_cross ha s hs i j).comp (continuous_const_smul c))
    ((continuous_cross ha s hs i j).const_smul c)) ?_
  intro x
  have he : c • embed a ha x=embed a ha (c • x) := by
    ext; change c • (a*x*a)=a*(c • x)*a; simp only [mul_smul_comm,smul_mul_assoc]
  rw [he,cross_embed,cross_embed]
  simp only [mul_smul_comm,smul_mul_assoc]

def crossLinear (i j : ι) : corner a ha →ₗ[ℂ] A where
  toFun := cross ha s hs i j
  map_add' := cross_add ha s hs i j
  map_smul' := cross_smul ha s hs i j

lemma cross_inner (i j : ι) (x y : corner a ha) :
    cross ha s hs i j (x*star y)=left (v := s i) ha x*star (left (v := s j) ha y) := by
  refine (dense a ha).induction_on₂ (isClosed_eq
    ((continuous_cross ha s hs i j).comp (continuous_fst.mul continuous_snd.star))
    (((continuous_left ha).comp continuous_fst).mul ((continuous_left ha).comp continuous_snd).star)) ?_ x y
  intro x y
  have he : embed a ha x*star (embed a ha y)=embed a ha (x*a*a*star y) := by
    ext; change (a*x*a)*star (a*y*a)=a*(x*a*a*star y)*a
    rw [star_mul,star_mul,ha.star_eq]; noncomm_ring
  rw [he,cross_embed,left_embed ha (copy_norm s hs i),left_embed ha (copy_norm s hs j),star_mul,star_mul,ha.star_eq]
  noncomm_ring

lemma cross_diagonal (i : ι) (x : corner a ha) : cross ha s hs i i x=copy ha s hs i x := rfl

include hs in
lemma corner_mul_left (hz : ∀ i, a*s i=0) (i : ι) (x y : corner a ha) :
    (x:A)*left (v := s i) ha y=0 := by
  refine (dense a ha).induction_on₂ (isClosed_eq
    ((continuous_subtype_val.comp continuous_fst).mul ((continuous_left ha).comp continuous_snd))
    continuous_const) ?_ x y
  intro x y
  rw [left_embed ha (copy_norm s hs i)]
  change (a*x*a)*(s i*y*a)=0
  calc
    _=a*x*(a*s i)*y*a := by noncomm_ring
    _=0 := by rw [hz]; simp

end KirchbergRordam.GenericRW.HereditaryTransport

namespace KirchbergRordam.GenericRW.HereditaryTransport

open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {a : A} (ha : IsSelfAdjoint a) (s : ι → A)
variable (hs : ∀ i j, star (s i)*s j=if i=j then star a*a else 0)

omit [Fintype ι] in
lemma copy_mul_left (j i : ι) (x y : corner a ha) :
    copy ha s hs j x*left (v := s i) ha y=
      if j=i then left (v := s i) ha (x*y) else 0 := by
  refine (dense a ha).induction_on₂ (isClosed_eq
    (((continuous_copy ha s hs j).comp continuous_fst).mul
      ((continuous_left ha).comp continuous_snd))
    (by split_ifs; exact (continuous_left ha).comp (continuous_fst.mul continuous_snd); exact continuous_const)) ?_ x y
  intro x y
  have he : embed a ha x*embed a ha y=embed a ha (x*a*a*y) := by
    ext; change (a*x*a)*(a*y*a)=a*(x*a*a*y)*a; noncomm_ring
  rw [copy_embed,left_embed ha (copy_norm s hs i),he,left_embed ha (copy_norm s hs i)]
  calc
    _=s j*x*(star (s j)*s i)*y*a := by noncomm_ring
    _=_ := by
      rw [hs]
      split_ifs with h
      · subst j; rw [ha.star_eq]; noncomm_ring
      · simp

lemma copies_mul_left (i : ι) (x y : corner a ha) :
    copies ha s hs x*left (v := s i) ha y=left (v := s i) ha (x*y) := by
  change (∑ j,copy ha s hs j x)*left (v := s i) ha y=_
  simp only [Finset.sum_mul,copy_mul_left]
  simp

omit [Fintype ι] in
include hs in
lemma units_mul_left (m : ι → ι → A)
    (hms : ∀ j k i,m j k*s i=if k=i then s j else 0)
    (j k i : ι) (x : corner a ha) :
    m j k*left (v := s i) ha x=if k=i then left (v := s j) ha x else 0 := by
  refine (dense a ha).induction_on x (isClosed_eq
    (continuous_const.mul (continuous_left ha)) (by split_ifs; exact continuous_left ha; exact continuous_const)) ?_
  intro x
  rw [left_embed ha (copy_norm s hs i),left_embed ha (copy_norm s hs j)]
  calc
    _=(m j k*s i)*x*a := by noncomm_ring
    _=_ := by rw [hms]; split_ifs <;> simp

lemma left_mul_copies (hz : ∀ i,a*s i=0) (i : ι) (x y : corner a ha) :
    left (v := s i) ha x*copies ha s hs y=0 := by
  refine (dense a ha).induction_on₂ (isClosed_eq
    (((continuous_left ha).comp continuous_fst).mul
      ((continuous_copies ha s hs).comp continuous_snd)) continuous_const) ?_ x y
  intro x y
  rw [left_embed ha (copy_norm s hs i)]
  change (s i*x*a)*(∑ j,copy ha s hs j (embed a ha y))=0
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero; intro j _
  rw [copy_embed]
  calc
    _=s i*x*(a*s j)*y*star (s j) := by noncomm_ring
    _=0 := by rw [hz]; simp

end KirchbergRordam.GenericRW.HereditaryTransport

namespace KirchbergRordam.GenericRW.HereditaryTransport
open scoped BigOperators CStarAlgebra
variable {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {a : A} (ha : IsSelfAdjoint a) (s : ι → A)
variable (hs : ∀ i j, star (s i)*s j=if i=j then star a*a else 0)


include hs in
lemma frame_inner (K : Matrix ι ι (corner a ha)) (i j : ι) :
    star (frame ha s K i)*frame ha s K j=((star K*K) i j : A) := by
  unfold frame
  simp only [star_sum,Finset.sum_mul,Finset.mul_sum,left_cross_inner ha s hs]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  change (∑ r,star (K r i : A)*(K r j : A))=↑(∑ r,star (K r i)*K r j)
  exact (map_sum (corner a ha).toSubmodule.subtype (fun r => star (K r i)*K r j) Finset.univ).symm

lemma frame_total (K : Matrix ι ι (corner a ha)) :
    ∑ i,frame ha s K i*star (frame ha s K i)=
      ∑ j,∑ k,cross ha s hs j k ((K*star K) j k) := by
  unfold frame
  simp only [star_sum,Finset.sum_mul,Finset.mul_sum]
  calc
    _=∑ i,∑ j,∑ k,crossLinear ha s hs j k (K j i*star (K k i)) := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro k _
      exact (cross_inner ha s hs j k _ _).symm
    _=∑ j,∑ k,crossLinear ha s hs j k (∑ i,K j i*star (K k i)) := by
      simp only [map_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_comm]
    _=_ := rfl

lemma frame_total_diagonal (K : Matrix ι ι (corner a ha)) (h : corner a ha)
    (hK : K*star K=Matrix.diagonal (fun _ => h)) :
    ∑ i,frame ha s K i*star (frame ha s K i)=copies ha s hs h := by
  rw [frame_total ha s hs,hK]
  change (∑ j,∑ k,cross ha s hs j k (Matrix.diagonal (fun _ => h) j k))=∑ j,copy ha s hs j h
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_eq_single j]
  · simp only [Matrix.diagonal_apply_eq,cross_diagonal]
  · intro k _ hkj
    rw [Matrix.diagonal_apply_ne _ hkj.symm,cross_zero]
  · simp

include hs in
lemma corner_mul_frame (hz : ∀ i,a*s i=0) (K : Matrix ι ι (corner a ha))
    (x : corner a ha) (i : ι) : (x:A)*frame ha s K i=0 := by
  unfold frame
  rw [Finset.mul_sum]
  exact Finset.sum_eq_zero fun j _ => corner_mul_left ha s hs hz j x (K j i)

end KirchbergRordam.GenericRW.HereditaryTransport

namespace KirchbergRordam.GenericRW.OrderZero
open scoped BigOperators ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


namespace WeightedUnits

variable [Nontrivial A]

abbrev coneHom (W : WeightedUnits (Fin rankNum) A) : ConeModel.Cone →⋆ₐ[ℂ] A := W.toWeightedMatrix.coneHom

lemma coneHom_corner (W : WeightedUnits (Fin rankNum) A) (i j : Fin rankNum) :
    W.coneHom (ConeModel.corner i j)=W.x i j := W.toWeightedMatrix.coneHom_corner i j

end WeightedUnits
end KirchbergRordam.GenericRW.OrderZero

namespace KirchbergRordam.GenericRW.HereditaryTransport
open scoped BigOperators CStarAlgebra
variable {A : Type*} [CStarAlgebra A]
variable {a : A} (ha : IsSelfAdjoint a) (s : Fin rankNum → A)
variable (hs : ∀ i j, star (s i)*s j=if i=j then star a*a else 0)
variable (hz : ∀ i,a*s i=0)
variable (K : Matrix (Fin rankNum) (Fin rankNum) (corner a ha))
variable (h q : corner a ha) (hq : star q=q) (hqq : q*q=h)
variable (hK : star K*K=Matrix.diagonal (fun _ => h))
variable (hK' : K*star K=Matrix.diagonal (fun _ => h))

include hs hK in
lemma frame_inner_diagonal (i j : Fin rankNum) :
    star (frame ha s K i)*frame ha s K j=if i=j then (h:A) else 0 := by
  rw [frame_inner ha s hs,hK,Matrix.diagonal_apply]
  split_ifs <;> rfl

include hs hz hq hqq hK in
lemma triple_relations (i j : Fin (rankNum+1)) : triple ha s K q i*star (triple ha s K q j)=if i=j then (h:A) else 0 := by
  have hval : star (q:A)=(q:A) := congrArg Subtype.val hq
  have hvalq : (q:A)*(q:A)=(h:A) := congrArg Subtype.val hqq
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  · simp [hval, hvalq]
  · simp [corner_mul_frame ha s hs hz, Ne.symm (Fin.castSucc_ne_last _)]
  · simpa only [triple_castSucc, triple_last, Fin.castSucc_ne_last, ↓reduceIte, star_mul,
      star_star, star_zero] using congrArg star (corner_mul_frame ha s hs hz K q _)
  · simp [frame_inner_diagonal ha s hs K h hK]

include hs hq hqq hK' in
lemma triple_total : ∑ i,star (triple ha s K q i)*triple ha s K q i=copies ha s hs h+(h:A) := by
  have hval : star (q:A)=(q:A) := congrArg Subtype.val hq
  have hvalq : (q:A)*(q:A)=(h:A) := congrArg Subtype.val hqq
  rw [Fin.sum_univ_castSucc]
  simp only [triple_castSucc,triple_last,star_star,hval,hvalq]
  rw [frame_total_diagonal ha s hs K h hK']


include hs hz hq hqq hK' in
lemma triple_norm (hn : ‖(h:A)‖≤1) : ‖∑ i,star (triple ha s K q i)*triple ha s K q i‖≤1 := by
  have hh : IsSelfAdjoint h := by
    rw [← hqq]
    change star (q*q)=q*q
    rw [star_mul,hq]
  have hhA : IsSelfAdjoint (h:A) := hh.map (NonUnitalStarSubalgebraClass.subtype (corner a ha))
  have hhB : IsSelfAdjoint (copies ha s hs h) := hh.map (copies ha s hs)
  rw [triple_total ha s hs K h q hq hqq hK',add_comm,
    hhA.norm_add_eq_max hhB (copies_orthogonal ha s hs hz h h)]
  apply max_le hn
  exact (NonUnitalStarAlgHom.norm_apply_le (copies ha s hs) h).trans hn

variable [PartialOrder A] [StarOrderedRing A]


def tripleUnits (hn : ‖(h:A)‖≤1) : OrderZero.WeightedUnits (Fin (rankNum+1)) A :=
  OrderZero.gram (triple ha s K q) (h:A)
    (triple_relations ha s hs hz K h q hq hqq hK)
    (triple_norm ha s hs hz K h q hq hqq hK' hn)

end KirchbergRordam.GenericRW.HereditaryTransport
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_WeightedUnits
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelFintype _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.GenericRW.dimensionDropClosed _root_.OAI.KirchbergRordam.GenericRW.dropSubringClass _root_.OAI.KirchbergRordam.GenericRW.instCStarAlgebraSubtypeContinuousMapElemRealUnitIntervalM6MemStarSubalgebraComplexDimensionDrop23 _root_.OAI.KirchbergRordam.GenericRW.instFiniteDimensionalComplexM6 _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n


namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedUnits (Fin rankNum) A) {v : A}
variable (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v)

omit [StarOrderedRing A] in
include h0 in
lemma total_mul_v : W.h*v=v := by
  calc
    W.h*v=W.h*(W.x 0 0*v) := by rw [h0]
    _=(W.x 0 0*W.x 0 0)*v := by rw [W.mul_x]; simp only [ite_true,mul_assoc]
    _=v := by rw [mul_assoc,h0,h0]

omit [StarOrderedRing A] in
include h0 in
lemma defect_mul_v : (1-W.h)*v=0 := by rw [sub_mul,one_mul,W.total_mul_v h0,sub_self]


def polarVectors (v : A) (i : Fin rankNum) : A := W.x i 0*v*CFC.sqrt (1-W.h)

omit [StarOrderedRing A] in
include hv h0 in
lemma column_inner (i j : Fin rankNum) :
    star (W.x i 0*v)*(W.x j 0*v)=if i=j then 1-W.h else 0 := by
  rw [star_mul,W.star_x]
  calc
    _=star v*(W.x 0 i*W.x j 0)*v := by noncomm_ring
    _=if i=j then 1-W.h else 0 := by
      rw [W.mul_x]
      split_ifs with hij
      · rw [mul_assoc,mul_assoc,h0,W.total_mul_v h0,hv]
      · simp

include hv h0 in
lemma polarVectors_inner (i j : Fin rankNum) :
    star (W.polarVectors v i)*W.polarVectors v j=
      if i=j then star (1-W.h)*(1-W.h) else 0 := by
  have hr : star (CFC.sqrt (1-W.h))=CFC.sqrt (1-W.h) :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (1-W.h))).star_eq
  change star ((W.x i 0*v)*CFC.sqrt (1-W.h))*((W.x j 0*v)*CFC.sqrt (1-W.h))=_
  rw [star_mul,hr]
  calc
    _=CFC.sqrt (1-W.h)*(star (W.x i 0*v)*(W.x j 0*v))*CFC.sqrt (1-W.h) := by noncomm_ring
    _=if i=j then star (1-W.h)*(1-W.h) else 0 := by
      rw [W.column_inner hv h0]
      split_ifs
      · rw [W.defect_selfAdjoint.star_eq]
        have hs := CFC.sqrt_mul_sqrt_self (1-W.h) (W.defect_nonneg hv)
        calc
          _=CFC.sqrt (1-W.h)*(CFC.sqrt (1-W.h)*CFC.sqrt (1-W.h))*CFC.sqrt (1-W.h) := by rw [hs]
          _=(CFC.sqrt (1-W.h)*CFC.sqrt (1-W.h))*(CFC.sqrt (1-W.h)*CFC.sqrt (1-W.h)) := by noncomm_ring
          _=_ := by rw [hs]
      · simp

include h0 in
lemma polarVectors_annihilate (i : Fin rankNum) : (1-W.h)*W.polarVectors v i=0 := by
  unfold polarVectors
  calc
    _=(W.x i 0*(1-W.h)*v)*CFC.sqrt (1-W.h) := by rw [← mul_assoc,← mul_assoc,← (W.commute_defect i 0).eq]
    _=0 := by rw [mul_assoc _ (1-W.h),W.defect_mul_v h0,mul_zero,zero_mul]

include h0 in
lemma units_polarVectors (j k i : Fin rankNum) :
    W.x j k*W.polarVectors v i=if k=i then W.polarVectors v j else 0 := by
  unfold polarVectors
  calc
    _=(W.x j k*W.x i 0)*v*CFC.sqrt (1-W.h) := by noncomm_ring
    _=_ := by
      rw [W.mul_x]
      split_ifs
      · rw [← (W.commute_h j 0).eq,mul_assoc _ W.h,W.total_mul_v h0]
      · simp


def defectCopies : HereditaryTransport.corner (1-W.h) W.defect_selfAdjoint →⋆ₙₐ[ℂ] A :=
  HereditaryTransport.copies W.defect_selfAdjoint (W.polarVectors v) (W.polarVectors_inner hv h0)

lemma defectCopies_orthogonal (x y : HereditaryTransport.corner (1-W.h) W.defect_selfAdjoint) :
    (x:A)*W.defectCopies hv h0 y=0 :=
  HereditaryTransport.copies_orthogonal W.defect_selfAdjoint (W.polarVectors v)
    (W.polarVectors_inner hv h0) (W.polarVectors_annihilate h0) x y

lemma defectCopies_commute (j k : Fin rankNum)
    (x : HereditaryTransport.corner (1-W.h) W.defect_selfAdjoint) :
    Commute (W.x j k) (W.defectCopies hv h0 x) :=
  HereditaryTransport.copies_commute W.defect_selfAdjoint (W.polarVectors v)
    (W.polarVectors_inner hv h0) W.x W.star_x (W.units_polarVectors h0) j k x

end KirchbergRordam.GenericRW.OrderZero.WeightedUnits

namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
open scoped CStarAlgebra BigOperators
open ConeModel FlipPath HereditaryTransport
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedUnits (Fin rankNum) A)

abbrev lambda : Defect →⋆ₙₐ[ℂ] HereditaryTransport.corner (1-W.h) W.defect_selfAdjoint :=
  W.toWeightedMatrix.defectHom

def rwK : Matrix (Fin rankNum) (Fin rankNum) (HereditaryTransport.corner (1-W.h) W.defect_selfAdjoint) :=
  fun i j => W.lambda (weightedK i j)
def rwH := W.lambda scalarG
def rwQ := W.lambda scalarQ

lemma rwQ_star : star W.rwQ=W.rwQ := by
  change star (W.lambda scalarQ)=W.lambda scalarQ
  rw [← map_star,scalarQ_star]
lemma rwQ_sq : W.rwQ*W.rwQ=W.rwH := by
  change W.lambda scalarQ*W.lambda scalarQ=W.lambda scalarG
  rw [← map_mul,scalarQ_sq]

lemma rwK_star_mul : star W.rwK*W.rwK=Matrix.diagonal (fun _ => W.rwH) := by
  apply Matrix.ext; intro i j
  have he := congrArg (fun matrix : Matrix (Fin rankNum) (Fin rankNum) Defect =>
    W.lambda (matrix i j)) weightedK_star_mul
  simp only [Matrix.mul_apply,Matrix.star_apply,map_sum,map_mul,map_star,
    Matrix.diagonal_apply] at he ⊢
  split_ifs at he ⊢ <;> simpa only [map_zero,rwK,rwH] using he
lemma rwK_mul_star : W.rwK*star W.rwK=Matrix.diagonal (fun _ => W.rwH) := by
  apply Matrix.ext; intro i j
  have he := congrArg (fun matrix : Matrix (Fin rankNum) (Fin rankNum) Defect =>
    W.lambda (matrix i j)) weightedK_mul_star
  simp only [Matrix.mul_apply,Matrix.star_apply,map_sum,map_mul,map_star,
    Matrix.diagonal_apply] at he ⊢
  split_ifs at he ⊢ <;> simpa only [map_zero,rwK,rwH] using he

lemma rwH_norm : ‖(W.rwH:A)‖≤1 := by
  have h₁ := NonUnitalStarAlgHom.norm_apply_le W.lambda scalarG
  have h₂ := NonUnitalStarAlgHom.norm_apply_le ConeModel.scalar RWFunctions.g
  exact h₁.trans (h₂.trans RWFunctions.g_norm)

def rwAlpha {v : A} (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v) : WeightedUnits (Fin (rankNum+1)) A :=
  tripleUnits W.defect_selfAdjoint (W.polarVectors v) (W.polarVectors_inner hv h0)
    (W.polarVectors_annihilate h0) W.rwK W.rwH W.rwQ W.rwQ_star W.rwQ_sq
      W.rwK_star_mul W.rwK_mul_star W.rwH_norm

lemma rwAlpha_total {v : A} (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v) :
    (W.rwAlpha hv h0).h=W.defectCopies hv h0 W.rwH+(W.rwH:A) :=
  triple_total W.defect_selfAdjoint (W.polarVectors v) (W.polarVectors_inner hv h0)
    W.rwK W.rwH W.rwQ W.rwQ_star W.rwQ_sq W.rwK_mul_star

end KirchbergRordam.GenericRW.OrderZero.WeightedUnits

namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
open scoped CStarAlgebra BigOperators
open ConeModel FlipPath HereditaryTransport
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedUnits (Fin rankNum) A)

lemma lambda_remainder (f : C(unitInterval,ℂ)) :
    (W.lambda (scalarRemainder f):A)=W.toWeightedMatrix.eval f-algebraMap ℂ A (f 1) := by
  rw [show (W.lambda (scalarRemainder f):A)=
    W.toWeightedMatrix.eval (f-ContinuousMap.const _ (f 1)) from
      W.toWeightedMatrix.defectHom_scalar _ _,map_sub]
  congr 1
  exact AlgHomClass.commutes W.toWeightedMatrix.eval (f 1)

lemma scalar_mul_left {v : A} (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v)
    (f : C(unitInterval,ℂ)) (i : Fin rankNum) (x : HereditaryTransport.corner (1-W.h) W.defect_selfAdjoint) :
    W.toWeightedMatrix.eval f*left (v := W.polarVectors v i) W.defect_selfAdjoint x=
      (f 1) • left (v := W.polarVectors v i) W.defect_selfAdjoint x := by
  have h := corner_mul_left W.defect_selfAdjoint (W.polarVectors v) (W.polarVectors_inner hv h0)
    (W.polarVectors_annihilate h0) i (W.lambda (scalarRemainder f)) x
  rw [W.lambda_remainder,sub_mul,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul] at h
  exact sub_eq_zero.mp h

lemma scalar_mul_copies {v : A} (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v)
    (f : C(unitInterval,ℂ)) (x : HereditaryTransport.corner (1-W.h) W.defect_selfAdjoint) :
    W.toWeightedMatrix.eval f*W.defectCopies hv h0 x=(f 1) • W.defectCopies hv h0 x := by
  have h := W.defectCopies_orthogonal hv h0 (W.lambda (scalarRemainder f)) x
  rw [W.lambda_remainder,sub_mul,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul] at h
  exact sub_eq_zero.mp h

lemma copies_mul_scalar {v : A} (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v)
    (f : C(unitInterval,ℂ)) (x : HereditaryTransport.corner (1-W.h) W.defect_selfAdjoint) :
    W.defectCopies hv h0 x*W.toWeightedMatrix.eval f=(f 1) • W.defectCopies hv h0 x := by
  have h := congrArg star (W.scalar_mul_copies hv h0 (star f) (star x))
  simpa only [map_star,star_mul,star_star,star_smul,ContinuousMap.star_apply] using h

end KirchbergRordam.GenericRW.OrderZero.WeightedUnits

namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
open scoped CStarAlgebra BigOperators
open ConeModel FlipPath HereditaryTransport RWFunctions
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedUnits (Fin rankNum) A)
variable {v : A} (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v)

lemma rwH_val : (W.rwH:A)=W.toWeightedMatrix.eval g := W.toWeightedMatrix.defectHom_scalar _ _

def rwL : A := 1-(W.rwAlpha hv h0).h

lemma rwL_eq : W.rwL hv h0=(1-(W.rwH:A))-W.defectCopies hv h0 W.rwH := by
  unfold rwL
  rw [W.rwAlpha_total hv h0]
  noncomm_ring

lemma rwL_nonneg : 0≤W.rwL hv h0 :=
  sub_nonneg.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg _ (W.rwAlpha hv h0).nonneg).mp
    (W.rwAlpha hv h0).norm_le)

lemma rwL_norm : ‖W.rwL hv h0‖≤1 := by
  rw [CStarAlgebra.norm_le_one_iff_of_nonneg _ (W.rwL_nonneg hv h0)]
  exact sub_le_self _ (W.rwAlpha hv h0).nonneg

lemma rwL_commute (i j : Fin rankNum) : Commute (W.rwL hv h0) (W.x i j) := by
  rw [W.rwL_eq hv h0,W.rwH_val]
  exact ((Commute.one_left _).sub_left (W.toWeightedMatrix.commute_eval i j g).symm).sub_left
    (W.defectCopies_commute hv h0 i j W.rwH).symm

lemma rwL_commute_scalar (f : C(unitInterval,ℂ)) :
    Commute (W.rwL hv h0) (W.toWeightedMatrix.eval f) := by
  rw [W.rwL_eq hv h0]
  apply Commute.sub_left
  · rw [W.rwH_val]
    exact (Commute.one_left _).sub_left ((Commute.all g f).map W.toWeightedMatrix.eval)
  · change W.defectCopies hv h0 W.rwH*W.toWeightedMatrix.eval f=
      W.toWeightedMatrix.eval f*W.defectCopies hv h0 W.rwH
    rw [W.copies_mul_scalar hv h0,W.scalar_mul_copies hv h0]

def rwR : A := W.rwL hv h0*W.toWeightedMatrix.eval j

lemma rwR_selfAdjoint : IsSelfAdjoint (W.rwR hv h0) := by
  change star (W.rwL hv h0*W.toWeightedMatrix.eval j)=_
  rw [star_mul,← map_star,j_star,(IsSelfAdjoint.of_nonneg (W.rwL_nonneg hv h0)).star_eq,
    (W.rwL_commute_scalar hv h0 j).symm.eq]
  rfl

lemma rwR_commute (i k : Fin rankNum) : Commute (W.rwR hv h0) (W.x i k) :=
  (W.rwL_commute hv h0 i k).mul_left (W.toWeightedMatrix.commute_eval i k j).symm

lemma rwR_total : W.rwR hv h0*W.h=W.rwL hv h0 := by
  have hr : (1-g)*j*IntervalCalculus.coord=1-g := by
    ext t; exact residual_inverse t
  have he : (1-W.toWeightedMatrix.eval g)*W.toWeightedMatrix.eval j*W.h=
      1-W.toWeightedMatrix.eval g := by
    have ht := congrArg W.toWeightedMatrix.eval hr
    simpa only [map_mul,map_sub,map_one,IntervalCalculus.hom_coord,toWeightedMatrix] using ht
  have hc : W.defectCopies hv h0 W.rwH*(W.toWeightedMatrix.eval j*W.h)=
      W.defectCopies hv h0 W.rwH := by
    have ht := W.copies_mul_scalar hv h0 (j*IntervalCalculus.coord) W.rwH
    have h₁ : (j*IntervalCalculus.coord) 1=1 := by
      change j 1*(((1:unitInterval):ℝ):ℂ)=1
      rw [j_one]
      norm_num
    rw [h₁,one_smul,map_mul,IntervalCalculus.hom_coord] at ht
    exact ht

  rw [rwR,W.rwL_eq hv h0,W.rwH_val,sub_mul,sub_mul,he,mul_assoc,hc]

def rwBeta : WeightedUnits (Fin rankNum) A :=
  W.rescale (W.rwR hv h0) (W.rwL hv h0) (W.rwR_selfAdjoint hv h0)
    (W.rwR_commute hv h0) (W.rwR_total hv h0) (W.rwL_nonneg hv h0) (W.rwL_norm hv h0)

lemma rw_complementary : (W.rwAlpha hv h0).h+(W.rwBeta hv h0).h=1 := by
  change (W.rwAlpha hv h0).h+(1-(W.rwAlpha hv h0).h)=1
  noncomm_ring

end KirchbergRordam.GenericRW.OrderZero.WeightedUnits

namespace KirchbergRordam.GenericRW.FlipPath
open ConeModel RWFunctions
open scoped BigOperators

def weightedC (r i : Fin rankNum) : Defect := weightedK r i*scalarQ

lemma weightedC_val (r i : Fin rankNum) : (weightedC r i:Cone)=scalar g*star (conePath i r) := by
  change (scalar q*star (conePath i r))*scalar q=scalar g*star (conePath i r)
  rw [mul_assoc,← (scalar_commute q (star (conePath i r))).eq,← mul_assoc,← map_mul,q_sq]

lemma conePath_top {t : unitInterval} (ht : (2/3:ℝ)≤t) (i r : Fin rankNum) :
    (conePath i r:C(unitInterval,ConeModel.M2)) t=
      CStarMatrix.ofMatrix (Matrix.single r i 1) := by
  ext a b
  change path t (a,i) (b,r)=(Matrix.single r i 1) a b
  rw [path_top ht]
  simp [flip,Matrix.single,eq_comm,ite_and]

lemma weightedC_apply (r i : Fin rankNum) (t : unitInterval) :
    (weightedC r i:C(unitInterval,ConeModel.M2)) t=
      algebraMap ℂ ConeModel.M2 (g t)*star ((conePath i r:C(unitInterval,ConeModel.M2)) t) :=
  congrArg (fun x : Cone => (x:C(unitInterval,ConeModel.M2)) t) (weightedC_val r i)

lemma weightedC_residual_apply (r i : Fin rankNum) (t : unitInterval) :
    (((weightedC r i-scalarG*weightedC r i:Defect):Cone):C(unitInterval,ConeModel.M2)) t=
      (g t-g t*g t) • star ((conePath i r:C(unitInterval,ConeModel.M2)) t) := by
  change (weightedC r i:C(unitInterval,ConeModel.M2)) t-
    algebraMap ℂ ConeModel.M2 (g t)*(weightedC r i:C(unitInterval,ConeModel.M2)) t=_
  rw [weightedC_apply,scalar_weight]

lemma weightedC_flip_pointwise (r i j k : Fin rankNum) (t : unitInterval) :
    ((g t-g t*g t) • star ((conePath i r:C(unitInterval,ConeModel.M2)) t))*
      (algebraMap ℂ ConeModel.M2 (RWFunctions.j t)*(((t:ℝ):ℂ) • e j k))=
    if r=j then (g t-g t*g t) • star ((conePath i k:C(unitInterval,ConeModel.M2)) t) else 0 := by
  by_cases ht : (2/3:ℝ)≤t
  · rw [conePath_top ht,conePath_top ht]
    change ((g t-g t*g t) • star (e r i))*(algebraMap ℂ ConeModel.M2 (RWFunctions.j t)*((t:ℝ):ℂ) • e j k)=_
    rw [Algebra.algebraMap_eq_smul_one,e_star]
    simp only [smul_mul_assoc,mul_smul_comm,one_mul,smul_smul]
    rw [e_mul]
    have hgg : ((t:ℝ):ℂ)*RWFunctions.j t*(g t-g t*g t)=g t-g t*g t := by
      calc
        _=g t*((1-g t)*RWFunctions.j t*((t:ℝ):ℂ)) := by ring
        _=_ := by rw [residual_inverse]; ring
    by_cases hrj : r=j
    · rw [ite_eq_left hrj,ite_eq_left hrj,hgg]
      change _=(g t-g t*g t) • star (e k i)
      rw [e_star]
    · rw [ite_eq_right hrj,ite_eq_right hrj,smul_zero]
  · have hg := g_low (le_of_lt (lt_of_not_ge ht))
    rw [hg,one_mul,sub_self,zero_smul,zero_mul,zero_smul,ite_self]


lemma weightedC_flip (r i j k : Fin rankNum) :
    defectMul (weightedC r i-scalarG*weightedC r i)
      (scalar RWFunctions.j*ConeModel.corner j k)=
      if r=j then weightedC k i-scalarG*weightedC k i else 0 := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  have hz : ((0:Defect):C(unitInterval,ConeModel.M2)) t=0 := rfl
  change ((((weightedC r i-scalarG*weightedC r i:Defect):Cone):C(unitInterval,ConeModel.M2)) t*
    (algebraMap ℂ ConeModel.M2 (RWFunctions.j t)*(ConeModel.corner j k:C(unitInterval,ConeModel.M2)) t))=_
  rw [weightedC_residual_apply,corner_apply]
  change ((g t-g t*g t) • star ((conePath i r:C(unitInterval,ConeModel.M2)) t))*
      (algebraMap ℂ ConeModel.M2 (RWFunctions.j t)*(((t:ℝ):ℂ) • e j k))=_
  rw [weightedC_flip_pointwise]
  by_cases hrj : r=j
  · rw [ite_eq_left hrj,ite_eq_left hrj,weightedC_residual_apply]
  · rw [ite_eq_right hrj,ite_eq_right hrj]; exact hz.symm
end KirchbergRordam.GenericRW.FlipPath
namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
open scoped CStarAlgebra BigOperators
open ConeModel FlipPath HereditaryTransport RWFunctions
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedUnits (Fin rankNum) A)
variable {v : A} (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v)

set_option synthInstance.maxHeartbeats 400000 in
def rwLeft (i : Fin rankNum) : Defect →ₗ[ℂ] A where
  toFun x := leftLinear W.defect_selfAdjoint (W.polarVectors v) i (W.lambda x)
  map_add' x y := by rw [map_add,map_add]
  map_smul' c x := by rw [map_smul,map_smul]; rfl

lemma rwLeft_sub (r : Fin rankNum) (x y : Defect) :
    W.rwLeft (v := v) r (x-y)=W.rwLeft (v := v) r x-W.rwLeft (v := v) r y :=
  map_sub (W.rwLeft (v := v) r) x y

include hv h0

lemma rwLeft_mul (r : Fin rankNum) (x : Defect) (y : Cone) :
    W.rwLeft (v := v) r (defectMul x y)=W.rwLeft (v := v) r x*W.coneHom y := by
  apply left_mul_of_eq W.defect_selfAdjoint (copy_norm _ (W.polarVectors_inner hv h0) r)
  change W.coneHom ((x:Cone)*y)=W.coneHom (x:Cone)*W.coneHom y
  exact map_mul _ _ _

lemma rw_spoke (i : Fin rankNum) : (W.rwAlpha hv h0).x (Fin.castSucc i) (Fin.last rankNum)=
    ∑ r,W.rwLeft (v := v) r (weightedC r i) := by
  have he (r : Fin rankNum) := W.rwLeft_mul hv h0 r (weightedK r i) (scalar q)
  rw [W.toWeightedMatrix.coneHom_scalar,← W.toWeightedMatrix.defectHom_scalar q q_one] at he
  have h (r : Fin rankNum) : W.rwLeft (v := v) r (weightedC r i)=
      left (v := W.polarVectors v r) W.defect_selfAdjoint (W.rwK r i)*(W.rwQ:A) := he r
  change star (triple W.defect_selfAdjoint (W.polarVectors v) W.rwK W.rwQ i.castSucc) *
    triple W.defect_selfAdjoint (W.polarVectors v) W.rwK W.rwQ (Fin.last rankNum) = _
  rw [triple_castSucc,triple_last,star_star]
  simp only [frame,Finset.sum_mul]
  exact Finset.sum_congr rfl fun r _ => (h r).symm

lemma rwLeft_scalar (r : Fin rankNum) (f : C(unitInterval,ℂ)) (x : Defect) :
    W.toWeightedMatrix.eval f*W.rwLeft (v := v) r x=(f 1) • W.rwLeft (v := v) r x :=
  W.scalar_mul_left hv h0 f r (W.lambda x)

lemma rwLeft_units (j k r : Fin rankNum) (x : Defect) :
    W.x j k*W.rwLeft (v := v) r x=if k=r then W.rwLeft (v := v) j x else 0 :=
  units_mul_left W.defect_selfAdjoint (W.polarVectors v) (W.polarVectors_inner hv h0)
    W.x (W.units_polarVectors h0) j k r (W.lambda x)

lemma rwL_mul_left (r : Fin rankNum) (x : Defect) :
    W.rwL hv h0*W.rwLeft (v := v) r x=W.rwLeft (v := v) r (x-scalarG*x) := by
  have hH : (W.rwH:A)*W.rwLeft (v := v) r x=0 :=
    corner_mul_left W.defect_selfAdjoint (W.polarVectors v) (W.polarVectors_inner hv h0)
      (W.polarVectors_annihilate h0) r W.rwH (W.lambda x)
  have hP : W.defectCopies hv h0 W.rwH*W.rwLeft (v := v) r x=
      W.rwLeft (v := v) r (scalarG*x) := by
    change copies W.defect_selfAdjoint (W.polarVectors v) _ _*left W.defect_selfAdjoint _=_
    rw [copies_mul_left]
    change left W.defect_selfAdjoint (W.lambda scalarG*W.lambda x)=left W.defect_selfAdjoint (W.lambda (scalarG*x))
    rw [map_mul]
  calc
    _=W.rwLeft (v := v) r x-(W.rwH:A)*W.rwLeft (v := v) r x-
        W.defectCopies hv h0 W.rwH*W.rwLeft (v := v) r x := by
      rw [W.rwL_eq hv h0]
      noncomm_ring
    _=W.rwLeft (v := v) r x-W.rwLeft (v := v) r (scalarG*x) :=
      (congrArg₂ (fun y z : A => W.rwLeft (v := v) r x-y-z) hH hP).trans
        (by simp only [sub_zero])
    _=_ := (W.rwLeft_sub r x (scalarG*x)).symm

lemma rwBeta_mul_spoke (i j k : Fin rankNum) :
    (W.rwBeta hv h0).x j k*(W.rwAlpha hv h0).x (Fin.castSucc i) (Fin.last rankNum)=
      W.rwLeft (v := v) j (weightedC k i-scalarG*weightedC k i) := by
  rw [W.rw_spoke hv h0]
  change (W.rwL hv h0*W.toWeightedMatrix.eval RWFunctions.j*W.x j k)*_= _
  rw [mul_assoc,mul_assoc,Finset.mul_sum]
  simp only [W.rwLeft_units hv h0]
  rw [Finset.sum_ite_eq,ite_eq_left (Finset.mem_univ k)]
  have hj : W.toWeightedMatrix.eval RWFunctions.j*W.rwLeft (v := v) j (weightedC k i)=
      W.rwLeft (v := v) j (weightedC k i) := by
    simpa only [j_one,one_smul] using W.rwLeft_scalar hv h0 j RWFunctions.j (weightedC k i)
  rw [hj]
  exact W.rwL_mul_left hv h0 j (weightedC k i)

lemma rwLeft_mul_beta (r j k : Fin rankNum) (x : Defect) :
    W.rwLeft (v := v) r x*(W.rwBeta hv h0).x j k=
      W.rwLeft (v := v) r (defectMul (x-scalarG*x) (scalar RWFunctions.j*ConeModel.corner j k)) := by
  have hP : W.rwLeft (v := v) r x*W.defectCopies hv h0 W.rwH=0 :=
    left_mul_copies W.defect_selfAdjoint (W.polarVectors v) (W.polarVectors_inner hv h0)
      (W.polarVectors_annihilate h0) r (W.lambda x) W.rwH
  have hH : W.rwLeft (v := v) r x*(W.rwH:A)=W.rwLeft (v := v) r (scalarG*x) := by
    have h := W.rwLeft_mul hv h0 r x (scalar g)
    rw [W.toWeightedMatrix.coneHom_scalar,← W.rwH_val] at h
    rw [← h]
    congr 1
    apply Subtype.ext
    exact (scalar_commute g (x:Cone)).symm.eq
  have hL : W.rwLeft (v := v) r x*W.rwL hv h0=W.rwLeft (v := v) r (x-scalarG*x) := by
    calc
      _=W.rwLeft (v := v) r x-W.rwLeft (v := v) r x*(W.rwH:A)-
          W.rwLeft (v := v) r x*W.defectCopies hv h0 W.rwH := by
        rw [W.rwL_eq hv h0]
        noncomm_ring
      _=W.rwLeft (v := v) r x-W.rwLeft (v := v) r (scalarG*x) :=
        (congrArg₂ (fun y z : A => W.rwLeft (v := v) r x-y-z) hH hP).trans
          (by simp only [sub_zero])
      _=_ := (W.rwLeft_sub r x (scalarG*x)).symm
  have hm : W.coneHom (scalar RWFunctions.j*ConeModel.corner j k)=
      W.toWeightedMatrix.eval RWFunctions.j*W.x j k :=
    (map_mul W.coneHom _ _).trans (congrArg₂ (fun x y : A => x*y)
      (W.toWeightedMatrix.coneHom_scalar RWFunctions.j) (W.coneHom_corner j k))
  change W.rwLeft (v := v) r x*(W.rwL hv h0*W.toWeightedMatrix.eval RWFunctions.j*W.x j k)=_
  calc
    _=(W.rwLeft (v := v) r x*W.rwL hv h0)*(W.toWeightedMatrix.eval RWFunctions.j*W.x j k) := by noncomm_ring
    _=W.rwLeft (v := v) r (x-scalarG*x)*W.coneHom (scalar RWFunctions.j*ConeModel.corner j k) :=
      congrArg₂ (fun x y : A => x*y) hL hm.symm
    _=_ := (W.rwLeft_mul hv h0 r (x-scalarG*x) (scalar RWFunctions.j*ConeModel.corner j k)).symm

lemma rw_commute_spoke (i j k : Fin rankNum) :
    Commute ((W.rwBeta hv h0).x j k) ((W.rwAlpha hv h0).x (Fin.castSucc i) (Fin.last rankNum)) := by
  change _=_
  rw [W.rwBeta_mul_spoke hv h0,W.rw_spoke hv h0,Finset.sum_mul]
  simp only [W.rwLeft_mul_beta hv h0,weightedC_flip]
  rw [Finset.sum_eq_single j]
  · rw [ite_eq_left rfl]
  · intro r _ hrj
    rw [ite_eq_right hrj,map_zero]
  · simp

end KirchbergRordam.GenericRW.OrderZero.WeightedUnits
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FieldCalculus
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelFintype _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]

namespace KirchbergRordam.GenericRW.FieldCalculus
open scoped BigOperators
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [CStarAlgebra A]


namespace Data
variable (D : Data X ι A)

def coeff (i j : ι) : D.Domain →L[ℂ] A := (D.aux i j).extendOfNorm (Vanish.multiplier D.p)

lemma coeff_mul (i j : ι) (f : C(X,ℂ)) :
    D.coeff i j (Vanish.multiplier D.p f) = D.x i j*D.eval f := by
  exact LinearMap.extendOfNorm_eq (Vanish.multiplier_dense D.p)
    ⟨1,fun f => by change ‖D.x i j*D.eval f‖ ≤ 1*‖D.p*f‖; simpa only [one_mul] using D.bound i j f⟩ f

lemma star_coeff (i j : ι) (f : D.Domain) :
    star (D.coeff i j f) = D.coeff j i (star f) := by
  refine (Vanish.multiplier_dense D.p).induction_on f (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro g
  rw [D.multiplier_star,D.coeff_mul,D.coeff_mul,star_mul,D.star_x,map_star]
  simpa only [map_star] using (D.commute_eval j i (star g)).symm.eq

lemma product_coeff (i j k l : ι) (f g : D.Domain) :
    D.coeff i j f * D.coeff k l g = if j=k then D.coeff i l (f*g) else 0 := by
  refine (Vanish.multiplier_dense D.p).induction_on₂ (p := fun f g =>
    D.coeff i j f * D.coeff k l g = if j=k then D.coeff i l (f*g) else 0)
    (isClosed_eq (by fun_prop) (by by_cases hjk : j=k <;> simp only [hjk,↓reduceIte] <;> fun_prop)) ?_ f g
  intro f g
  rw [D.multiplier_product,D.coeff_mul,D.coeff_mul,D.coeff_mul]
  have he : (D.x i j*D.eval f)*(D.x k l*D.eval g) =
      (D.x i j*D.x k l)*(D.eval f*D.eval g) := by
    rw [mul_assoc (D.x i j),← mul_assoc (D.eval f),(D.commute_eval k l f).symm.eq]
    noncomm_ring
  rw [he,D.mul_x]
  split_ifs with hjk
  · rw [map_mul,map_mul,← (D.commute_eval i l D.p).eq]
    noncomm_ring
  · simp


def scalarMul (f : C(X,ℂ)) : D.Domain →L[ℂ] D.Domain :=
  { toFun := fun g => ⟨f*(g:C(X,ℂ)), by intro t ht; simp [g.property t ht]⟩
    map_add' := by intro g h; ext t; simp [mul_add]
    map_smul' := by intro c g; ext t; simp
    cont := by fun_prop }

lemma scalar_coeff (i j : ι) (f : C(X,ℂ)) (g : D.Domain) :
    D.coeff i j (D.scalarMul f g) = D.eval f * D.coeff i j g := by
  refine (Vanish.multiplier_dense D.p).induction_on g (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro u
  have he : D.scalarMul f (Vanish.multiplier D.p u) = Vanish.multiplier D.p (f*u) := by
    apply Subtype.ext
    change f*(D.p*u)=D.p*(f*u)
    ring
  rw [he,D.coeff_mul,D.coeff_mul,map_mul]
  rw [← mul_assoc, (D.commute_eval i j f).eq, mul_assoc]

abbrev Matrices := Matrix ι ι D.Domain

def matrices : D.Matrices →ₗ[ℂ] A where
  toFun m := ∑ i,∑ j,D.coeff i j (m i j)
  map_add' m n := by simp [Finset.sum_add_distrib]
  map_smul' c m := by simp [Finset.smul_sum]

omit instSize in
lemma matrices_single.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    {X : Type contextLevel1}
    [TopologicalSpace X]
    [CompactSpace X]
    [T2Space X]
    {ι : Type contextLevel2}
    [Fintype ι]
    [DecidableEq ι]
    {A : Type contextLevel3}
    [CStarAlgebra A]
    (D : KirchbergRordam.GenericRW.FieldCalculus.Data X ι A)
    (i j : ι) (f : D.Domain) :
    D.matrices (Matrix.single i j f) = D.coeff i j f := by
  simp [matrices,Matrix.single,ite_and,apply_ite]

lemma matrices_product (m n : D.Matrices) : D.matrices (m*n) = D.matrices m*D.matrices n := by
  induction m using Matrix.induction_on' with
  | h_zero => simp
  | h_add m m' hm hm' => simp only [add_mul,map_add,hm,hm']
  | h_std_basis i j f =>
    induction n using Matrix.induction_on' with
    | h_zero => simp
    | h_add n n' hn hn' => simp only [mul_add,map_add,hn,hn']
    | h_std_basis k l g =>
      by_cases h : j=k
      · subst k
        rw [Matrix.single_mul_single_same,D.matrices_single,D.matrices_single,
          D.matrices_single,D.product_coeff,ite_eq_left rfl]
      · rw [Matrix.single_mul_single_of_ne (h := h),D.matrices_single,D.matrices_single,
          D.product_coeff,ite_eq_right h,map_zero]

lemma matrices_star (m : D.Matrices) : D.matrices (star m) = star (D.matrices m) := by
  simp only [matrices,LinearMap.coe_mk,AddHom.coe_mk,star_sum,D.star_coeff]
  exact Finset.sum_comm


end Data
end KirchbergRordam.GenericRW.FieldCalculus
namespace KirchbergRordam.GenericRW.OrderZero
open scoped BigOperators
open IntervalCalculus
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]


namespace Pair
variable (P : Pair ι κ A)

lemma left_x_coeff (i j : ι) (u v : ι × κ) (f : P.field.Domain) :
    P.left.x i j*P.field.coeff u v f =
      if j=u.1 then P.field.coeff (i,u.2) v (P.field.scalarMul (1-coord) f) else 0 := by
  refine (Vanish.multiplier_dense P.field.p).induction_on f
    (isClosed_eq (by fun_prop) (by by_cases h : j=u.1 <;> simp only [h,↓reduceIte] <;> fun_prop)) ?_
  intro g
  rw [P.field.coeff_mul]
  rw [← mul_assoc,P.left_x_field]
  by_cases h : j=u.1
  · rw [ite_eq_left h,ite_eq_left h,P.field.scalar_coeff,P.field.coeff_mul]
    change (P.left.h*P.field.x (i,u.2) v)*P.eval g =
      P.eval (1-coord)*(P.field.x (i,u.2) v*P.eval g)
    rw [map_sub,map_one,hom_coord,← P.left_h,mul_assoc]
  · simp [h]

lemma right_x_coeff (i j : κ) (u v : ι × κ) (f : P.field.Domain) :
    P.right.x i j*P.field.coeff u v f =
      if j=u.2 then P.field.coeff (u.1,i) v (P.field.scalarMul coord f) else 0 := by
  refine (Vanish.multiplier_dense P.field.p).induction_on f
    (isClosed_eq (by fun_prop) (by by_cases h : j=u.2 <;> simp only [h,↓reduceIte] <;> fun_prop)) ?_
  intro g
  rw [P.field.coeff_mul,← mul_assoc,P.right_x_field]
  by_cases h : j=u.2
  · rw [ite_eq_left h,ite_eq_left h,P.field.scalar_coeff,P.field.coeff_mul]
    change (P.right.h*P.field.x (u.1,i) v)*P.eval g =
      P.eval coord*(P.field.x (u.1,i) v*P.eval g)
    rw [hom_coord,mul_assoc]
  · simp [h]
end Pair
end KirchbergRordam.GenericRW.OrderZero
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_DropSections
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelFintype _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]


namespace KirchbergRordam.GenericRW.DropSections
open scoped Matrix Kronecker BigOperators ComplexOrder
open IntervalCalculus

lemma interior_star (f : DimensionDrop23) : interior (star f)=star (interior f) := by
  apply embed_injective
  change entries (star f.val)-leftPart (endLeft (star f))-rightPart (endRight (star f)) =
    star (entries f.val-leftPart (endLeft f)-rightPart (endRight f))
  rw [map_star,endLeft_star,endRight_star,leftPart_star,rightPart_star,star_sub,star_sub]

lemma interior_one : interior 1=0 := by
  apply embed_injective
  change entries 1-leftPart (endLeft 1)-rightPart (endRight 1)=0
  simp only [show entries 1=1 from entries.map_one',endLeft_one,endRight_one]
  change 1-times (1-coord) (leftConst 1)-times coord (rightConst 1)=0
  rw [show leftConst 1=1 from leftConst.map_one',show rightConst 1=1 from rightConst.map_one']
  ext i j t
  change (1:Mat) i j t-((1-coord)* (1:Mat) i j) t-(coord*(1:Mat) i j) t=0
  simp only [ContinuousMap.mul_apply,ContinuousMap.sub_apply,ContinuousMap.one_apply]
  ring


end KirchbergRordam.GenericRW.DropSections
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_OrderZeroPair
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelFintype _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n


namespace KirchbergRordam.GenericRW.OrderZero.Pair
open scoped Matrix Kronecker BigOperators
open IntervalCalculus
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (P : Pair ι κ A)
local instance instSMulComplexSubtypeContinuousMapElemRealUnitIntervalMemNonUnitalStarSubalgebraDomainProdField : SMul ℂ P.field.Domain := (NonUnitalStarSubalgebra.instModule P.field.Domain).toSMul

def weighted : Matrix (ι×κ) (ι×κ) ℂ →ₗ[ℂ] P.field.Matrices where
  toFun m u v := Vanish.multiplier P.weight (ContinuousMap.const _ (m u v))
  map_add' m n := by ext u v t; change P.weight t*(m u v+n u v)=P.weight t*m u v+P.weight t*n u v; ring
  map_smul' z m := by ext u v t; change P.weight t*(z*m u v)=z*(P.weight t*m u v); ring

lemma weighted_coeff (u v : ι×κ) (z : ℂ) :
    P.field.coeff u v (Vanish.multiplier P.weight (ContinuousMap.const _ z)) = z • P.field.x u v := by
  change P.field.coeff u v (Vanish.multiplier P.field.p (ContinuousMap.const _ z)) = _
  rw [P.field.coeff_mul]
  have he : ContinuousMap.const unitInterval z=z • (1:C(unitInterval,ℂ)) := by ext t; simp
  rw [he,map_smul,map_one,mul_smul_comm,mul_one]

lemma weighted_single (u v : ι×κ) (z : ℂ) :
    P.weighted (Matrix.single u v z)=
      Matrix.single u v (Vanish.multiplier P.weight (ContinuousMap.const _ z)) := by
  ext i j t
  change P.weight t * (Matrix.single u v z) i j =
    ((Matrix.single u v (Vanish.multiplier P.weight (ContinuousMap.const _ z))) i j).val t
  by_cases hi : u=i <;> by_cases hj : v=j <;> simp [Matrix.single,hi,hj]

lemma weighted_kronecker (a : Matrix ι ι ℂ) (b : Matrix κ κ ℂ) :
    P.field.matrices (P.weighted (a ⊗ₖ b)) = P.left.linear a*P.right.linear b := by
  induction a using Matrix.induction_on' with
  | h_zero => simp
  | h_add a a' ha ha' => simp only [Matrix.add_kronecker,map_add,add_mul,ha,ha']
  | h_std_basis i j z =>
    induction b using Matrix.induction_on' with
    | h_zero => simp
    | h_add b b' hb hb' => simp only [Matrix.kronecker_add,map_add,mul_add,hb,hb']
    | h_std_basis k l w =>
      rw [Matrix.single_kronecker_single,P.weighted_single]
      change P.field.matrices (Matrix.single (i,k) (j,l)
        (Vanish.multiplier P.field.p (ContinuousMap.const _ (z*w)))) = _
      rw [P.field.matrices_single]
      change P.field.coeff (i,k) (j,l)
        (Vanish.multiplier P.weight (ContinuousMap.const _ (z*w))) = _
      rw [P.weighted_coeff,P.left.linear_single,P.right.linear_single]
      change (z*w) • (P.left.x i j*P.right.x k l) = _
      rw [smul_mul_assoc,mul_smul_comm,smul_smul]

lemma weighted_left (a : Matrix ι ι ℂ) :
    P.field.matrices (P.weighted (a ⊗ₖ (1:Matrix κ κ ℂ))) = P.left.linear a*P.right.h := by
  rw [P.weighted_kronecker,P.right.linear_one]

lemma weighted_right (b : Matrix κ κ ℂ) :
    P.field.matrices (P.weighted ((1:Matrix ι ι ℂ) ⊗ₖ b)) = P.left.h*P.right.linear b := by
  rw [P.weighted_kronecker,P.left.linear_one]

def actionLeft (a : Matrix ι ι ℂ) (m : P.field.Matrices) : P.field.Matrices :=
  fun u v => ∑ j, (@HSMul.hSMul ℂ P.field.Domain P.field.Domain inferInstance (a u.1 j) (P.field.scalarMul (1-coord) (m (j,u.2) v)))

def actionRight (a : Matrix κ κ ℂ) (m : P.field.Matrices) : P.field.Matrices :=
  fun u v => ∑ j, (@HSMul.hSMul ℂ P.field.Domain P.field.Domain inferInstance (a u.2 j) (P.field.scalarMul coord (m (u.1,j) v)))

lemma left_x_matrices (i j : ι) (m : P.field.Matrices) :
    P.left.x i j*P.field.matrices m =
      ∑ l : κ,∑ v : ι×κ, P.field.coeff (i,l) v (P.field.scalarMul (1-coord) (m (j,l) v)) := by
  simp only [FieldCalculus.Data.matrices,LinearMap.coe_mk,AddHom.coe_mk,
    Finset.mul_sum,P.left_x_coeff,Fintype.sum_prod_type]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

lemma right_x_matrices (i j : κ) (m : P.field.Matrices) :
    P.right.x i j*P.field.matrices m =
      ∑ k : ι,∑ v : ι×κ, P.field.coeff (k,i) v (P.field.scalarMul coord (m (k,j) v)) := by
  simp only [FieldCalculus.Data.matrices,LinearMap.coe_mk,AddHom.coe_mk,
    Finset.mul_sum,P.right_x_coeff,Fintype.sum_prod_type]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

lemma linear_field_left (a : Matrix ι ι ℂ) (m : P.field.Matrices) :
    P.left.linear a*P.field.matrices m = P.field.matrices (P.actionLeft a m) := by
  change (∑ i,∑ j,a i j • P.left.x i j)*P.field.matrices m = _
  conv_lhs =>
    simp only [Finset.sum_mul,smul_mul_assoc,P.left_x_matrices,Finset.smul_sum]
  change (∑ i,∑ j,∑ l,∑ v,a i j • P.field.coeff (i,l) v
    (P.field.scalarMul (1-coord) (m (j,l) v))) = _
  simp only [FieldCalculus.Data.matrices,LinearMap.coe_mk,AddHom.coe_mk,actionLeft,
    Fintype.sum_prod_type,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

lemma linear_field_right (a : Matrix κ κ ℂ) (m : P.field.Matrices) :
    P.right.linear a*P.field.matrices m = P.field.matrices (P.actionRight a m) := by
  change (∑ i,∑ j,a i j • P.right.x i j)*P.field.matrices m = _
  conv_lhs =>
    simp only [Finset.sum_mul,smul_mul_assoc,P.right_x_matrices,Finset.smul_sum]
  change (∑ i,∑ j,∑ k,∑ v,a i j • P.field.coeff (k,i) v
    (P.field.scalarMul coord (m (k,j) v))) = _
  simp only [FieldCalculus.Data.matrices,LinearMap.coe_mk,AddHom.coe_mk,actionRight,
    Fintype.sum_prod_type,map_sum,map_smul]
  conv_lhs =>
    arg 2; ext i
    rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]

end KirchbergRordam.GenericRW.OrderZero.Pair

namespace KirchbergRordam.GenericRW.OrderZero.Pair
open scoped Matrix Kronecker BigOperators ComplexOrder
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (P : Pair (Fin rankNum) (Fin (rankNum+1)) A)

lemma interior_matrices_star (m : DropSections.Interior) :
    P.field.matrices (star m) = star (P.field.matrices m) :=
  P.field.matrices_star m

lemma interior_matrices_product (m n : DropSections.Interior) :
    P.field.matrices (m*n) = P.field.matrices m * P.field.matrices n :=
  P.field.matrices_product m n

lemma interior_matrices_add (m n : DropSections.Interior) :
    P.field.matrices (m+n) = P.field.matrices m + P.field.matrices n :=
  P.field.matrices.map_add m n

lemma interior_matrices_sub (m n : DropSections.Interior) :
    P.field.matrices (m-n) = P.field.matrices m - P.field.matrices n :=
  map_sub P.field.matrices m n

lemma interior_matrices_neg (m : DropSections.Interior) :
    P.field.matrices (-m) = -P.field.matrices m :=
  map_neg P.field.matrices m

lemma interior_matrices_zero : P.field.matrices (0 : DropSections.Interior) = 0 :=
  map_zero P.field.matrices

omit [Nontrivial A] [StarOrderedRing A] in
lemma left_linear_commute_h (a : DropSections.Small2) : Commute (P.left.linear a) P.right.h := by
  change Commute (∑ i,∑ j,a i j • P.left.x i j) P.right.h
  exact Commute.sum_left _ _ _ fun i _ =>
    Commute.sum_left _ _ _ fun j _ => (P.left_commute_right_h i j).smul_left (a i j)

omit [Nontrivial A] [StarOrderedRing A] in
lemma left_right_linear_commute (a : DropSections.Small2) (b : DropSections.Small3) :
    Commute (P.left.linear a) (P.right.linear b) := by
  change Commute (∑ i,∑ j,a i j • P.left.x i j) (∑ k,∑ l,b k l • P.right.x k l)
  exact Commute.sum_left _ _ _ fun i _ => Commute.sum_left _ _ _ fun j _ =>
    Commute.sum_right _ _ _ fun k _ => Commute.sum_right _ _ _ fun l _ =>
      ((P.commute i j k l).smul_left (a i j)).smul_right (b k l)

lemma left_product (a c : DropSections.Small2) :
    P.left.linear a*P.left.linear c = P.left.linear (a*c)-P.field.matrices
      (DropSections.weighted ((a*c) ⊗ₖ (1:DropSections.Small3))) := by
  change _=P.left.linear (a*c)-P.field.matrices (P.weighted ((a*c) ⊗ₖ 1))
  rw [P.left.linear_mul,P.weighted_left,P.left_h,sub_mul,one_mul,
    (P.left_linear_commute_h (a*c)).eq]

lemma right_product (b d : DropSections.Small3) :
    P.right.linear b*P.right.linear d = P.right.linear (b*d)-P.field.matrices
      (DropSections.weighted ((1:DropSections.Small2) ⊗ₖ (b*d))) := by
  change _=P.right.linear (b*d)-P.field.matrices (P.weighted (1 ⊗ₖ (b*d)))
  rw [P.right.linear_mul,P.weighted_right]
  have he : P.right.h=1-P.left.h := (eq_sub_iff_add_eq).mpr (by rw [add_comm,P.sum_one])
  rw [he,sub_mul,one_mul]

lemma cross_product (a : DropSections.Small2) (b : DropSections.Small3) :
    P.left.linear a*P.right.linear b=P.field.matrices (DropSections.weighted (a ⊗ₖ b)) :=
  (P.weighted_kronecker a b).symm

lemma cross_product_rev (a : DropSections.Small2) (b : DropSections.Small3) :
    P.right.linear b*P.left.linear a=P.field.matrices (DropSections.weighted (a ⊗ₖ b)) := by
  rw [← (P.left_right_linear_commute a b).eq,P.cross_product]

lemma field_left (a : DropSections.Small2) (m : DropSections.Interior) :
    P.left.linear a*P.field.matrices m=P.field.matrices (DropSections.actionLeft a m) :=
  P.linear_field_left a m

lemma field_right (b : DropSections.Small3) (m : DropSections.Interior) :
    P.right.linear b*P.field.matrices m=P.field.matrices (DropSections.actionRight b m) :=
  P.linear_field_right b m

lemma field_left_rev (a : DropSections.Small2) (m : DropSections.Interior) :
    P.field.matrices m*P.left.linear a=P.field.matrices (DropSections.actionLeftRev m a) := by
  calc
    _ = star (star (P.left.linear a) * star (P.field.matrices m)) := by
      rw [star_mul, star_star, star_star]
    _ = star (P.left.linear (star a) * P.field.matrices (star m)) :=
      congrArg star (congrArg₂ (· * ·) (P.left.linear_star a).symm
        (P.interior_matrices_star m).symm)
    _ = star (P.field.matrices (DropSections.actionLeft (star a) (star m))) :=
      congrArg star (P.field_left _ _)
    _ = _ := (P.interior_matrices_star _).symm

lemma field_right_rev (b : DropSections.Small3) (m : DropSections.Interior) :
    P.field.matrices m*P.right.linear b=P.field.matrices (DropSections.actionRightRev m b) := by
  calc
    _ = star (star (P.right.linear b) * star (P.field.matrices m)) := by
      rw [star_mul, star_star, star_star]
    _ = star (P.right.linear (star b) * P.field.matrices (star m)) :=
      congrArg star (congrArg₂ (· * ·) (P.right.linear_star b).symm
        (P.interior_matrices_star m).symm)
    _ = star (P.field.matrices (DropSections.actionRight (star b) (star m))) :=
      congrArg star (P.field_right _ _)
    _ = _ := (P.interior_matrices_star _).symm


def liftLinear : DimensionDrop23 →ₗ[ℂ] A :=
  P.left.linear.comp DropSections.endLeft + P.right.linear.comp DropSections.endRight +
    P.field.matrices.comp DropSections.interior

lemma lift_apply (f : DimensionDrop23) : P.liftLinear f=
    P.left.linear (DropSections.endLeft f)+P.right.linear (DropSections.endRight f)+
      P.field.matrices (DropSections.interior f) := rfl

lemma lift_mul (f g : DimensionDrop23) : P.liftLinear (f*g)=P.liftLinear f*P.liftLinear g := by
  simp only [P.lift_apply,DropSections.endLeft_mul,DropSections.endRight_mul,DropSections.interior_mul,
    P.interior_matrices_add,P.interior_matrices_sub,P.interior_matrices_neg,
    P.interior_matrices_product]
  simp only [add_mul,mul_add,P.left_product,P.right_product,P.cross_product,P.cross_product_rev,
    P.field_left,P.field_right,P.field_left_rev,P.field_right_rev]
  abel

lemma lift_one : P.liftLinear 1=1 := by
  rw [P.lift_apply,DropSections.endLeft_one,DropSections.endRight_one,DropSections.interior_one,
    P.interior_matrices_zero,add_zero,P.left.linear_one,P.right.linear_one,P.sum_one]

lemma lift_star (f : DimensionDrop23) : P.liftLinear (star f)=star (P.liftLinear f) := by
  simp only [P.lift_apply,DropSections.endLeft_star,DropSections.endRight_star,DropSections.interior_star,
    P.left.linear_star,P.right.linear_star,star_add]
  exact congrArg (fun value => star (P.left.linear (DropSections.endLeft f)) +
    star (P.right.linear (DropSections.endRight f)) + value)
    (P.interior_matrices_star (DropSections.interior f))


def dimensionDropHom : DimensionDrop23 →⋆ₐ[ℂ] A where
  toFun := P.liftLinear
  map_zero' := map_zero P.liftLinear
  map_one' := P.lift_one
  map_add' := map_add P.liftLinear
  map_mul' := P.lift_mul
  commutes' c := by simp only [Algebra.algebraMap_eq_smul_one,map_smul,P.lift_one]
  map_star' := P.lift_star

end KirchbergRordam.GenericRW.OrderZero.Pair

namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
open scoped CStarAlgebra BigOperators
open ConeModel FlipPath HereditaryTransport RWFunctions
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedUnits (Fin rankNum) A)
variable {v : A} (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v)

lemma rwAlpha_diagonal (i : Fin (rankNum+1)) : 0 ≤ (W.rwAlpha hv h0).x i i := by
  change 0 ≤ star (triple W.defect_selfAdjoint (W.polarVectors v) W.rwK W.rwQ i)*
    triple W.defect_selfAdjoint (W.polarVectors v) W.rwK W.rwQ i
  exact star_mul_self_nonneg _

lemma rwAlpha_corner : (W.rwAlpha hv h0).x (Fin.last rankNum) (Fin.last rankNum)=(W.rwH:A) := by
  change star (triple W.defect_selfAdjoint (W.polarVectors v) W.rwK W.rwQ (Fin.last rankNum)) *
    triple W.defect_selfAdjoint (W.polarVectors v) W.rwK W.rwQ (Fin.last rankNum) = (W.rwH:A)
  rw [triple_last]
  rw [show star (W.rwQ:A)=(W.rwQ:A) from congrArg Subtype.val W.rwQ_star]
  exact congrArg Subtype.val W.rwQ_sq

lemma rw_commute_corner (j k : Fin rankNum) :
    Commute ((W.rwBeta hv h0).x j k) ((W.rwAlpha hv h0).x (Fin.last rankNum) (Fin.last rankNum)) := by
  rw [W.rwAlpha_corner hv h0,W.rwH_val]
  change Commute (W.rwL hv h0*W.toWeightedMatrix.eval RWFunctions.j*W.x j k)
    (W.toWeightedMatrix.eval g)
  exact ((W.rwL_commute_scalar hv h0 g).mul_left
    ((Commute.all RWFunctions.j g).map W.toWeightedMatrix.eval)).mul_left
      (W.toWeightedMatrix.commute_eval j k g)

lemma rw_commute_row (i : Fin (rankNum+1)) (j k : Fin rankNum) :
    Commute ((W.rwBeta hv h0).x j k) ((W.rwAlpha hv h0).x i (Fin.last rankNum)) := by
  induction i using Fin.lastCases with
  | last => exact W.rw_commute_corner hv h0 j k
  | cast i => exact W.rw_commute_spoke hv h0 i j k

lemma rw_commute_col (i : Fin (rankNum+1)) (j k : Fin rankNum) :
    Commute ((W.rwBeta hv h0).x j k) ((W.rwAlpha hv h0).x (Fin.last rankNum) i) := by
  have h := (W.rw_commute_row hv h0 i k j).star_star
  simpa only [(W.rwBeta hv h0).star_x,(W.rwAlpha hv h0).star_x] using h


def rwPair : OrderZero.Pair (Fin rankNum) (Fin (rankNum+1)) A where
  left := W.rwBeta hv h0
  right := W.rwAlpha hv h0
  commute j k := (W.rwAlpha hv h0).commute_of_spokes (Fin.last rankNum) (W.rwAlpha_diagonal hv h0) _
    (fun i => W.rw_commute_row hv h0 i j k) (fun i => W.rw_commute_col hv h0 i j k)
  sum_one := by rw [add_comm]; exact W.rw_complementary hv h0

end KirchbergRordam.GenericRW.OrderZero.WeightedUnits

namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

def rwHom (W : WeightedUnits (Fin rankNum) A) {v : A}
    (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v) : DimensionDrop23 →⋆ₐ[ℂ] A :=
  (W.rwPair hv h0).dimensionDropHom
end KirchbergRordam.GenericRW.OrderZero.WeightedUnits
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FunctionalCalculus
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.labelFintype _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n


namespace KirchbergRordam.GenericRW

namespace ExactCut
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


theorem exists_exact_cut {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : CuntzBelow a b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ z : A, star z*z = cut a δ ∧ z*star z ∈ ClosedRightRange.hereditary b := by
  obtain ⟨x,hx⟩ := hab.approx (half_pos hδ)
  let y := CFC.sqrt b*x*CFC.sqrt (cut a δ)
  obtain ⟨z,hz,hzm⟩ := Domination.exists_factor (cut_nonneg a δ)
    (le_of_lt (div_pos (by norm_num : (0:ℝ)<2) hδ)) (cut_dominated ha hb hδ hx)
  refine ⟨z,hz,?_⟩
  have hy : y ∈ ClosedRightRange.space b := by
    exact ClosedRightRange.mul_right_mem
      (ClosedRightRange.mul_right_mem (Domination.sqrt_mem_self b hb) x) _
  have hzb : z ∈ ClosedRightRange.space b := ClosedRightRange.space_le hy hzm
  exact ClosedRightRange.self_mul_star_mem_hereditary (IsSelfAdjoint.of_nonneg hb) hzb
end ExactCut
end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
section
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedUnits (Fin rankNum) A)
omit [Nontrivial A] in
lemma cutoffRescale_corner : W.cutoffRescale.x 0 0=cfc RWCut.f (W.x 0 0) := by
  change cfc RWCut.j W.h*W.x 0 0=_
  rw [((W.commute_h 0 0).symm.cfc_real RWCut.j).eq]
  have hm : W.x 0 0*W.h=W.x 0 0*W.x 0 0 := by
    rw [(W.commute_h 0 0).eq,W.mul_x,ite_eq_left rfl]
  rw [Intertwining.cfc (IsSelfAdjoint.of_nonneg W.nonneg) (W.star_x 0 0) hm RWCut.j RWCut.j_cont]
  exact RWCut.function_mul _ (W.star_x 0 0)

omit [Nontrivial A] in

theorem exists_cutoff_relations
    (hcomp : CuntzBelow (1-W.h) (ExactCut.cut (W.x 0 0) (1/2))) :
    ∃ v : A, star v*v=1-W.cutoffRescale.h ∧ W.cutoffRescale.x 0 0*v=v := by
  have hp : 0≤1-W.h := sub_nonneg.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg W.h W.nonneg).mp W.norm_le)
  obtain ⟨z,hz,hzm⟩ := ExactCut.exists_exact_cut hp (ExactCut.cut_nonneg _ _) hcomp (by norm_num : (0:ℝ)<1/2)
  let v : A := (Real.sqrt 2:ℝ) • z
  have hev : star v*v=(2:ℝ) • ExactCut.cut (1-W.h) (1/2) := by
    dsimp only [v]
    rw [star_smul,star_trivial,smul_mul_smul_comm,Real.mul_self_sqrt (by norm_num),hz]
  refine ⟨v,hev.trans (RWCut.rescaled_defect W.nonneg).symm,?_⟩
  have hfix : W.cutoffRescale.x 0 0*(z*star z)=z*star z := by
    rw [W.cutoffRescale_corner]
    exact RWCut.fixes_hereditary (RWCut.fixes_cut (W.star_x 0 0)) hzm
  have hfv := RWCut.fixes_of_mul_star hfix
  dsimp only [v]
  rw [mul_smul_comm,hfv]
end

variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

def cutoffHom (W : WeightedUnits (Fin rankNum) A)
    (hcomp : CuntzBelow (1-W.h) (ExactCut.cut (W.x 0 0) (1/2))) :
    DimensionDrop23 →⋆ₐ[ℂ] A :=
  W.cutoffRescale.rwHom (W.exists_cutoff_relations hcomp).choose_spec.1
    (W.exists_cutoff_relations hcomp).choose_spec.2
end KirchbergRordam.GenericRW.OrderZero.WeightedUnits
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_AmplifiedComparison
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
variable [instPauliData : KirchbergRordam.GenericRW.PauliData]


namespace KirchbergRordam.GenericRW.MaxTensor
open scoped BigOperators
universe u
variable {P Q : Type u} [CStarAlgebra P] [CStarAlgebra Q]

lemma pure_mul (a c : P) (b d : Q) : pure a b*pure c d=pure (a*c) (b*d) :=
  AmplifiedComparison.pair_mul includeLeft includeRight legs_commute a c b d
lemma pure_star (a : P) (b : Q) : star (pure a b)=pure (star a) (star b) :=
  AmplifiedComparison.pair_star includeLeft includeRight legs_commute a b
omit instSize instPauliData in
lemma pure_sum_left
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type u}
    {Q : Type u}
    [CStarAlgebra P]
    [CStarAlgebra Q]
    {I : Type*} [Fintype I] (f : I→P) (b : Q) :
    pure (∑ i,f i) b=∑ i,pure (f i) b := by simp only [pure,map_sum,Finset.sum_mul]
omit instSize instPauliData in
lemma pure_sum_right
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type u}
    {Q : Type u}
    [CStarAlgebra P]
    [CStarAlgebra Q]
    {I : Type*} [Fintype I] (a : P) (f : I→Q) :
    pure a (∑ i,f i)=∑ i,pure a (f i) := by simp only [pure,map_sum,Finset.mul_sum]

end KirchbergRordam.GenericRW.MaxTensor
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FullComparison
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
variable [instPauliData : KirchbergRordam.GenericRW.PauliData]


namespace KirchbergRordam.GenericRW.MaxTensor
open scoped CStarAlgebra BigOperators
variable {P : Type*} [CStarAlgebra P]
variable {I : Type*} [Fintype I]
variable [PartialOrder P] [StarOrderedRing P]

def defectWord (n : ℕ) (G : P) : powerPack P n := word n (fun _=>G)
def cornerWord (n : ℕ) (c G : P) (j : Fin (n+1)) : powerPack P n :=
  word n (fun i=>if i=j then c else G)
def columnWord (n : ℕ) (G : P) (j : Fin (n+1)) (v : P) : powerPack P n :=
  word n (fun i=>if i=j then v*CFC.sqrt G else 1)

end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.GenericRW.MaxTensor
universe u
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
def powerHom (φ : A →⋆ₐ[ℂ] B) : (n : ℕ) → powerPack A n →⋆ₐ[ℂ] powerPack B n
  | 0 => φ
  | n+1 => lift (includeLeft.comp φ) (includeRight.comp (powerHom φ n))
      (fun a b => legs_commute (φ a) (powerHom φ n b))
end KirchbergRordam.GenericRW.MaxTensor

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FiniteDrop
attribute [-instance] _root_.OAI.KirchbergRordam.MaxTensor.instCStarRingAlgebra _root_.OAI.KirchbergRordam.MinTensor.instCStarRingAlgebra _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal _root_.OAI.KirchbergRordam.StarCompletion.completionNormedStarGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
variable [instPauliData : KirchbergRordam.GenericRW.PauliData]


namespace KirchbergRordam.GenericRW.MaxTensor
open scoped BigOperators
universe u
variable {P Q : Type u} [CStarAlgebra P] [CStarAlgebra Q]

omit instSize instPauliData in
lemma norm_pure_le
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type u}
    {Q : Type u}
    [CStarAlgebra P]
    [CStarAlgebra Q]
    (a : P) (b : Q) : ‖pure a b‖≤‖a‖*‖b‖ :=
  (norm_mul_le _ _).trans (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le includeLeft a)
    (NonUnitalStarAlgHom.norm_apply_le includeRight b) (norm_nonneg _) (norm_nonneg _))

variable [PartialOrder P] [StarOrderedRing P] [PartialOrder Q] [StarOrderedRing Q]
local instance instPartialOrderAlgebra : PartialOrder (Algebra P Q) := CStarAlgebra.spectralOrder _
local instance instStarOrderedRingAlgebra : StarOrderedRing (Algebra P Q) := CStarAlgebra.spectralOrderedRing _
lemma pure_nonneg {a : P} {b : Q} (ha : 0≤a) (hb : 0≤b) : 0≤pure a b := by
  have he : star (pure (CFC.sqrt a) (CFC.sqrt b))*pure (CFC.sqrt a) (CFC.sqrt b)=pure a b := by
    rw [pure_star,pure_mul,(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq,
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)).star_eq,
      CFC.sqrt_mul_sqrt_self _ ha,CFC.sqrt_mul_sqrt_self _ hb]
  rw [← he]
  exact star_mul_self_nonneg _
end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.GenericRW.FullRankWeighted
open scoped BigOperators
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor OrderZero Fullness
universe u
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
local instance instPartialOrderAlgebra : PartialOrder (Algebra A B) := CStarAlgebra.spectralOrder _

def tensor (W : WeightedUnits I A) (V : WeightedUnits J B) : WeightedUnits (I×J) (Algebra A B) where
  h := pure W.h V.h
  x i j := pure (W.x i.1 j.1) (V.x i.2 j.2)
  nonneg := pure_nonneg W.nonneg V.nonneg
  norm_le := (norm_pure_le _ _).trans (by nlinarith [W.norm_le,V.norm_le,norm_nonneg W.h,norm_nonneg V.h])
  star_x i j := by rw [pure_star,W.star_x,V.star_x]
  mul_x i j k l := by
    rw [pure_mul,W.mul_x,V.mul_x]
    by_cases h1 : j.1=k.1 <;> by_cases h2 : j.2=k.2 <;>
      simp [h1,h2,Prod.ext_iff,pure_mul]
  diagonal := by
    simp only [Fintype.sum_prod_type,← pure_sum_right,← pure_sum_left,W.diagonal,V.diagonal]

end KirchbergRordam.GenericRW.FullRankWeighted

namespace KirchbergRordam.GenericRW.FullRankWeighted
open scoped BigOperators
open OrderZero
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {w : A} (hw : w * w = 0)
omit hw in
omit instSize instPauliData in
lemma abs_mul_self_zero.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {w : A}
    (hw : w * w = 0)
    : CFC.sqrt (star w * w) * w = 0 := by
  apply Intertwining.sqrt_mul_eq_zero (star_mul_self_nonneg w)
  rw [mul_assoc, hw, mul_zero]

omit hw in
omit instSize instPauliData in
lemma self_mul_coabs_zero.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {w : A}
    (hw : w * w = 0)
    : w * CFC.sqrt (w * star w) = 0 := by
  apply Intertwining.mul_sqrt_eq_zero (mul_star_self_nonneg w)
  rw [← mul_assoc, hw, zero_mul]

include hw in
lemma abs_coabs_zero : CFC.sqrt (star w * w) * CFC.sqrt (w * star w) = 0 := by
  apply Intertwining.mul_sqrt_eq_zero (mul_star_self_nonneg w)
  rw [← mul_assoc, abs_mul_self_zero hw, zero_mul]

omit instSize instPauliData in
lemma self_abs.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {w : A}
    : w * CFC.sqrt (star w * w) = CFC.sqrt (w * star w) * w :=
  Intertwining.sqrt (star_mul_self_nonneg w) (mul_star_self_nonneg w) (mul_assoc _ _ _).symm


def ofSquareZero (hw : w * w = 0) (hn : ‖w‖ ≤ 1) : WeightedUnits (Fin 2) A := by
  let a := CFC.sqrt (star w * w)
  let b := CFC.sqrt (w * star w)
  let x : Fin 2 → Fin 2 → A := ![![a, star w], ![w, b]]
  have ha : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have hb : IsSelfAdjoint b := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have haa : a * a = star w * w := CFC.sqrt_mul_sqrt_self _
  have hbb : b * b = w * star w := CFC.sqrt_mul_sqrt_self _
  have hab : a * b = 0 := abs_coabs_zero hw
  have hba : b * a = 0 := by simpa only [star_mul, ha.star_eq, hb.star_eq, star_zero] using congrArg star hab
  have haw : a * w = 0 := abs_mul_self_zero hw
  have hwb : w * b = 0 := self_mul_coabs_zero hw
  have hwa : w * a = b * w := self_abs
  have hwsa : star w * a = 0 := by simpa only [star_mul, ha.star_eq, star_zero] using congrArg star haw
  have hbws : b * star w = 0 := by simpa only [star_mul, hb.star_eq, star_zero] using congrArg star hwb
  have hbw : a * star w = star w * b := by
    simpa only [star_mul, ha.star_eq, hb.star_eq] using congrArg star hwa
  have hws : star w * star w = 0 := by simpa only [star_mul, star_zero] using congrArg star hw
  refine ⟨a + b, x, add_nonneg (CFC.sqrt_nonneg _) (CFC.sqrt_nonneg _), ?_, ?_, ?_, by simp [Fin.sum_univ_two, x]⟩
  · rw [ha.norm_add_eq_max hb hab]
    dsimp only [a, b]
    rw [CFC.norm_sqrt (star w * w), CFC.norm_sqrt (w * star w), CStarRing.norm_star_mul_self, CStarRing.norm_self_mul_star,
      Real.sqrt_mul_self (norm_nonneg _), max_self]
    exact hn
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [x, ha.star_eq, hb.star_eq]
  · intro i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [x, add_mul, haa, hbb, hab, hba, haw, hwb, hwsa, hbws, hws, hw, hwa, hbw]


end KirchbergRordam.GenericRW.FullRankWeighted

namespace KirchbergRordam.GenericRW.FullRankWeighted
open scoped BigOperators
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor OrderZero Fullness
universe u
variable {P : Type u} [CStarAlgebra P]

attribute [local instance] OAI.KirchbergRordam.GenericRW.FullRankWeighted.instPartialOrderCarrierPowerPack
attribute [local instance] OAI.KirchbergRordam.GenericRW.FullRankWeighted.instStarOrderedRingCarrierPowerPack
attribute [local instance] OAI.KirchbergRordam.GenericRW.FullRankWeighted.instPartialOrder_solutions
attribute [local instance] OAI.KirchbergRordam.GenericRW.FullRankWeighted.instStarOrderedRing_solutions
def power (W : WeightedUnits (Fin 2) P) : (k : ℕ) → WeightedUnits (Row k) (powerPack P k)
  | 0 => W
  | k+1 => tensor W (power W k)

end KirchbergRordam.GenericRW.FullRankWeighted

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_BalancedLimit
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder


namespace KirchbergRordam

open scoped Matrix Kronecker ComplexOrder

instance dimensionDropClosed : IsClosed
    (dimensionDropSubalgebra : Set C(unitInterval, M6)) := by
  change IsClosed ((fun f : C(unitInterval, M6) => f 0) ⁻¹' (leftMatrix.range : Set M6) ∩
    (fun f : C(unitInterval, M6) => f 1) ⁻¹' (rightMatrix.range : Set M6))
  exact ((leftMatrix.range.toSubalgebra.toSubmodule.closed_of_finiteDimensional).preimage
    (continuous_eval_const (0 : unitInterval))).inter
    ((rightMatrix.range.toSubalgebra.toSubmodule.closed_of_finiteDimensional).preimage
    (continuous_eval_const (1 : unitInterval)))


instance instCStarAlgebraSubtypeContinuousMapElemRealUnitIntervalM6MemStarSubalgebraComplexDimensionDrop23 : CStarAlgebra DimensionDrop23 :=
  StarSubalgebra.cstarAlgebra dimensionDropSubalgebra

end KirchbergRordam


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_TensorSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace

namespace KirchbergRordam.PrimeDimensionDrop
open scoped CStarAlgebra ComplexOrder
open MatrixTensor
variable {p q : ℕ}

def leftRamp (a : Mat (Fin p)) : Algebra p q :=
  ⟨⟨fun t => ((1-(t:ℝ):ℝ):ℂ) • MatrixTensor.leftMatrix a,by fun_prop⟩,by
    apply (mem_iff _).mpr
    constructor
    · exact ⟨a,by simp⟩
    · exact ⟨0,by simp⟩⟩
def rightRamp (b : Mat (Fin q)) : Algebra p q :=
  ⟨⟨fun t => ((t:ℝ):ℂ) • MatrixTensor.rightMatrix b,by fun_prop⟩,by
    apply (mem_iff _).mpr
    constructor
    · exact ⟨0,by change MatrixTensor.leftMatrix (κ:=Fin q) (0 : Mat (Fin p)) = (0:ℂ) • MatrixTensor.rightMatrix b; rw [map_zero,zero_smul]⟩
    · exact ⟨b,by change MatrixTensor.rightMatrix (ι:=Fin p) b = (1:ℂ) • MatrixTensor.rightMatrix b; rw [one_smul]⟩⟩

def interiorRamp (t : unitInterval) (a : Fiber p q) : Algebra p q :=
  ⟨⟨fun s => (((s:ℝ)*(1-s)/(t*(1-t)):ℝ):ℂ) • a,by fun_prop⟩,by
    apply (mem_iff _).mpr
    constructor <;> refine ⟨0,?_⟩ <;> simp⟩
end KirchbergRordam.PrimeDimensionDrop
namespace KirchbergRordam.MatrixTensor
open scoped TensorProduct CStarAlgebra ComplexOrder Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
def tensorRange (S : StarSubalgebra ℂ (Mat ι)) (T : StarSubalgebra ℂ (Mat κ)) :
    StarSubalgebra ℂ (Mat (ι×κ)) := (subKronecker S T).range
end KirchbergRordam.MatrixTensor
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MinTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
namespace KirchbergRordam.MinTensor
open scoped TensorProduct
universe u


attribute [instance] RepresentationPair.normH RepresentationPair.innerH
  RepresentationPair.completeH RepresentationPair.normK RepresentationPair.innerK
  RepresentationPair.completeK


end KirchbergRordam.MinTensor

namespace KirchbergRordam.MinTensor
open scoped TensorProduct CStarAlgebra
universe u
variable (A B : Type u) [CStarAlgebra A] [CStarAlgebra B]

variable {A B}
instance instCStarAlgebraAlgebra : CStarAlgebra (Algebra A B) where

def of : Raw A B →⋆ₐ[ℂ] Algebra A B where
  __ := UniformSpace.Completion.coeRingHom
  commutes' _ := rfl
  map_star' x := (StarCompletion.star_coe _ x).symm
@[simp] lemma norm_of (x : Raw A B) : ‖of x‖ = seminorm x :=
  UniformSpace.Completion.norm_coe x

def includeLeft : A →⋆ₐ[ℂ] Algebra A B := of.comp (rawEquiv.toStarAlgHom.comp {
  toAlgHom := _root_.Algebra.TensorProduct.includeLeft
  map_star' a := by simp })

def includeRight : B →⋆ₐ[ℂ] Algebra A B := of.comp (rawEquiv.toStarAlgHom.comp {
  toAlgHom := _root_.Algebra.TensorProduct.includeRight
  map_star' b := by simp })
lemma legs_commute (a : A) (b : B) :
    Commute (includeLeft (B := B) a) (includeRight (A := A) b) := by
  change of (rawEquiv (a ⊗ₜ[ℂ] (1 : B))) * of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b)) =
    of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b)) * of (rawEquiv (a ⊗ₜ[ℂ] (1 : B)))
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  simp only [_root_.Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]


def fromMaximal : MaxTensor.Algebra A B →⋆ₐ[ℂ] Algebra A B :=
  MaxTensor.lift includeLeft includeRight legs_commute
@[simp] lemma fromMaximal_of (x : A ⊗[ℂ] B) :
    fromMaximal (MaxTensor.of (MaxTensor.rawEquiv x)) =
      of (rawEquiv (A := A) (B := B) x) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a b =>
    change MaxTensor.lift includeLeft includeRight legs_commute
      (MaxTensor.of (a ⊗ₜ[ℂ] b)) = _
    rw [MaxTensor.lift_of_tmul]
    change of (rawEquiv (a ⊗ₜ[ℂ] (1 : B))) * of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b)) = of (rawEquiv (a ⊗ₜ[ℂ] b))
    rw [← map_mul, ← map_mul]
    congr 2
    simp only [_root_.Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
end KirchbergRordam.MinTensor
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_GeneralSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.GeneralEndpointMultiplicity
open MatrixDiagonalPath MatrixBlockReindex DiagonalIteration EndpointMultiplicity
open scoped ComplexOrder CStarAlgebra
variable {P Q R E : Type*} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeR : Fintype R] [Fintype E]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqR : DecidableEq R] [DecidableEq E]
def rightBase (h : 2≤Fintype.card (E ⊕ (P×R))) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat ((Q×E)⊕((P×Q)×R)) :=
  (CStarMatrix.reindexₐ ℂ ℂ (rightExpand (P:=P) (Q:=Q) (R:=R) (E:=E)).symm).toStarAlgHom.comp
    (MatrixTensor.rightMatrix.comp (DropMatrixRepresentations.representation _ h))
def rightRep (h : 2≤Fintype.card (E ⊕ (P×R))) (v : unitary (Mat (P×Q))) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat ((Q×E)⊕((P×Q)×R)) :=
  (conj (duplicateUnitary (P:=Q×E) (Q:=P×Q) (R:=R) v)).toStarAlgHom.comp (rightBase (P:=P) (Q:=Q) (R:=R) h)
end KirchbergRordam.GeneralEndpointMultiplicity
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.PrimeDropPresentation.Iteration
open scoped CStarAlgebra ComplexOrder
open Filter Topology
open MatrixDiagonalPath DiagonalIteration GeneralDropSystem
variable (S : PrimeDropPresentation)

abbrev diagonalSystem : DiagonalIteration.System where
  obj n := PrimeDimensionDrop.Fiber (S.size n) (S.size n+1)
  slot n := Slot (S.stepData n)
  diagonal n := (CStarMatrix.reindexₐ ℂ ℂ (zeroReindex (S.stepData n))).toStarAlgHom.comp block
  eigen n := eigenpath (S.stepData n)
  twist n := (MatrixPermutationPath.path 1
    ((zeroReindex (S.stepData n)).symm.trans (oneReindex (S.stepData n)))).toContinuousMap

def normalizedPath (n k : ℕ) (t : unitInterval) :
    unitary (PrimeDimensionDrop.Fiber (S.size (n+k)) (S.size (n+k)+1)) :=
  (diagonalSystem S).unitaryPath n k t * star ((diagonalSystem S).unitaryPath n k 0)
lemma normalizedPath_continuous (n k : ℕ) : Continuous (normalizedPath S n k) :=
  ((diagonalSystem S).unitaryPath_continuous n k).mul continuous_const
@[simp] lemma normalizedPath_zero (n k : ℕ) : normalizedPath S n k 0=1 := by
  exact mul_inv_cancel _

end KirchbergRordam.PrimeDropPresentation.Iteration
namespace KirchbergRordam.PrimeDropPresentation.Channels
open MatrixDiagonalPath MatrixBlockReindex DiagonalIteration GeneralEndpointMultiplicity
open DropMatrixRepresentations DropChannels GeneralDropSystem
open BalancedDropSystem (half)
open scoped CStarAlgebra ComplexOrder
variable (S : PrimeDropPresentation)
lemma zeroCount (n : ℕ) :
    2≤Fintype.card (Fin (S.stepData n).zeroEnd ⊕ (Fin (S.size n+1)×Fin (S.stepData n).zeroMid)) := by
  simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using S.zero_copies n
lemma oneCount (n : ℕ) :
    2≤Fintype.card (Fin (S.stepData n).oneEnd ⊕ (Fin (S.size n)×Fin (S.stepData n).oneMid)) := by
  simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using S.one_copies n

def zeroRep (n : ℕ) (v : unitary (PrimeDimensionDrop.Fiber (S.size n) (S.size n+1))) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat (Fin (S.size (n+1))) :=
  (CStarMatrix.reindexₐ ℂ ℂ (zeroOuter (S.stepData n))).toStarAlgHom.comp
    (leftRep (P:=Fin (S.size n)) (Q:=Fin (S.size n+1)) (R:=Fin (S.stepData n).zeroMid)
      (E:=Fin (S.stepData n).zeroEnd) (zeroCount S n) v)
def oneRep (n : ℕ) (v : unitary (PrimeDimensionDrop.Fiber (S.size n) (S.size n+1))) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat (Fin (S.size (n+1)+1)) :=
  (CStarMatrix.reindexₐ ℂ ℂ (oneOuter (S.stepData n))).toStarAlgHom.comp
    (rightRep (P:=Fin (S.size n)) (Q:=Fin (S.size n+1)) (R:=Fin (S.stepData n).oneMid)
      (E:=Fin (S.stepData n).oneEnd) (oneCount S n) v)
end KirchbergRordam.PrimeDropPresentation.Channels
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimeChannels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.PrimeDropPresentation.Channels
open MatrixDiagonalPath DiagonalIteration PrimeDropPresentation.Iteration
open GeneralDropSystem DropChannels
open BalancedDropSystem (half)
variable (S : PrimeDropPresentation)
open MultiplicativeChannel (Channel)
open scoped CStarAlgebra ComplexOrder
open Filter Topology

def finalPath (n k : ℕ) := normalizedPath S n (k+1)
def endPath (n k : ℕ) (t : unitInterval) := finalPath S n k t*star (finalPath S n k 1)
lemma endPath_continuous (n k : ℕ) : Continuous (endPath S n k) :=
  (normalizedPath_continuous S n (k+1)).mul continuous_const
@[simp] lemma endPath_one (n k : ℕ) : endPath S n k 1=1 := mul_inv_cancel _
end KirchbergRordam.PrimeDropPresentation.Channels
end

end OAI
end


