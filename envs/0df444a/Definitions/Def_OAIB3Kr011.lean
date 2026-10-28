-- Prove2me | Definitions.Def_OAIB3Kr011
-- name    : OAIB3Kr011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T17:04:39.86089+00:00
-- url     : https://prove2.me/theorems/66a66caa-fcbe-4652-a3d0-5a127c01df05
-- title:
--   Definitions bundle OAIB3Kr011 of the split of OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 323 declarations of OpenAI's Lean: 98 definitions, 1 inductive type or structure, 13 instances and 211 theorems. The definitions and types are `OAI.KirchbergRordam.GenericRW.AmplifiedComparison.gramVector`, `OAI.KirchbergRordam.GenericRW.ConeCube.Tensor`, `OAI.KirchbergRordam.GenericRW.ConeCube.expansion`, `OAI.KirchbergRordam.GenericRW.ConeCube.family`, `OAI.KirchbergRordam.GenericRW.ConeCube.first`, `OAI.KirchbergRordam.GenericRW.ConeCube.h`, `OAI.KirchbergRordam.GenericRW.ConeCube.hScalar`, `OAI.KirchbergRordam.GenericRW.ConeCube.instPartialOrderCarrierTensor`, `OAI.KirchbergRordam.GenericRW.ConeCube.p`, `OAI.KirchbergRordam.GenericRW.ConeCube.repr`, `OAI.KirchbergRordam.GenericRW.ConeCube.scalarLeg`, `OAI.KirchbergRordam.GenericRW.ConeCube.tail`, `OAI.KirchbergRordam.GenericRW.ConeCube.u`, `OAI.KirchbergRordam.GenericRW.ConeCube.weighted`, `OAI.KirchbergRordam.GenericRW.ConeCube.x`, `OAI.KirchbergRordam.GenericRW.ConeCube.y`, `OAI.KirchbergRordam.GenericRW.ConeCube.κ`, `OAI.KirchbergRordam.GenericRW.ConeCut.g`, `OAI.KirchbergRordam.GenericRW.ConeCut.instLESubtypeContinuousMapElemRealUnitIntervalM2MemStarSubalgebraComplexCone`, `OAI.KirchbergRordam.GenericRW.ConeCut.instPartialOrderSubtypeContinuousMapElemRealUnitIntervalM2MemStarSubalgebraComplexCone`, `OAI.KirchbergRordam.GenericRW.ConeCut.q`, `OAI.KirchbergRordam.GenericRW.ConeCut.unit`, `OAI.KirchbergRordam.GenericRW.ConeCut.z`, `OAI.KirchbergRordam.GenericRW.ConeDrop.instPartialOrderCarrierPowerPack`, `OAI.KirchbergRordam.GenericRW.ConeDrop.instPartialOrderSubtypeContinuousMapElemRealUnitIntervalM2MemStarSubalgebraComplexCone`, `OAI.KirchbergRordam.GenericRW.ConeModel.Defect`, `OAI.KirchbergRordam.GenericRW.ConeModel.corner`, `OAI.KirchbergRordam.GenericRW.ConeModel.defectMul`, `OAI.KirchbergRordam.GenericRW.ConeModel.defectSubalgebra`, `OAI.KirchbergRordam.GenericRW.ConeModel.entry`, `OAI.KirchbergRordam.GenericRW.ConeModel.entryWeight`, `OAI.KirchbergRordam.GenericRW.ConeModel.equiv`, `OAI.KirchbergRordam.GenericRW.ConeModel.evaluate`, `OAI.KirchbergRordam.GenericRW.ConeModel.fromWeight`, `OAI.KirchbergRordam.GenericRW.ConeModel.scalarDefect`, `OAI.KirchbergRordam.GenericRW.ConeModel.scalarRemainder`, `OAI.KirchbergRordam.GenericRW.ConeModel.tip`, `OAI.KirchbergRordam.GenericRW.ConeModel.toCone`, `OAI.KirchbergRordam.GenericRW.ConeModel.toHereditary`, `OAI.KirchbergRordam.GenericRW.ConeModel.unitCoefficients` and 59 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CharacterCriterion_AmplifiedComparison`, `CharacterCriterion_ConeCube`, `CharacterCriterion_ConeModel`, `CharacterCriterion_ConePauli`, `CharacterCriterion_CubeCalculus`, `CharacterCriterion_CubeField`, `CharacterCriterion_DropSections`, `CharacterCriterion_FactorIndependence`, `CharacterCriterion_FieldCalculus`, `CharacterCriterion_FiniteDrop`, `CharacterCriterion_FlipPath`, `CharacterCriterion_FunctionalCalculus`, `CharacterCriterion_HereditaryTransport`, `CharacterCriterion_MatrixSimplex`, `CharacterCriterion_MaxTensor`, `CharacterCriterion_Pauli`, `CharacterCriterion_WeightedUnits`.
--
--   **Imports.** It imports the bundles `OAIB3Kr004`, `OAIB3Kr007`, `OAIB3Kr008` and `OAIB3Kr009` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIB3Kr013`; the statement `OAI_KirchbergRordam_PrimeSquareUnitary_section_reflect`; the proof of `OAI_KirchbergRordam_PrimeSquareUnitary_section_reflect`.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIB3Kr004
import Definitions.Def_OAIB3Kr007
import Definitions.Def_OAIB3Kr008
import Definitions.Def_OAIB3Kr009

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Pauli
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.ConeModel.coneClosed _root_.OAI.KirchbergRordam.GenericRW.ConeModel.coneSubringClass _root_.OAI.KirchbergRordam.GenericRW.ConeModel.instCStarAlgebraSubtypeContinuousMapElemRealUnitIntervalM2MemStarSubalgebraComplexCone _root_.OAI.KirchbergRordam.GenericRW.ConeModel.instFiniteDimensionalComplexM2 _root_.OAI.KirchbergRordam.GenericRW.DetectingSpace.quotientNormedRing _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.GenericRW.PureStates.locallyConvexReal _root_.OAI.KirchbergRordam.GenericRW.StarCompletion.completionNormedAlgebra _root_.OAI.KirchbergRordam.GenericRW.StarCompletion.completionStar _root_.OAI.KirchbergRordam.GenericRW.StarCompletion.completionStarRing _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


namespace KirchbergRordam.GenericRW
instance instNeZeroNatN [Size] : NeZero Size.n := ⟨Nat.ne_of_gt Size.positive⟩

section
open scoped Matrix BigOperators
attribute [local instance] PauliData.finite PauliData.decidable

end
open scoped Matrix BigOperators

end KirchbergRordam.GenericRW

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MaxTensor
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.DetectingSpace.quotientNormedRing _root_.OAI.KirchbergRordam.GenericRW.PureStates.locallyConvexReal _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped TensorProduct

namespace KirchbergRordam.GenericRW

namespace MaxTensor

variable (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]


variable {A B}

lemma legs_commute (a : A) (b : B) :
    Commute (includeLeft (B := B) a) (includeRight (A := A) b) := by
  change of (rawEquiv (a ⊗ₜ[ℂ] (1 : B))) * of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b)) =
    of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b)) * of (rawEquiv (a ⊗ₜ[ℂ] (1 : B)))
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  simp only [_root_.Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]


open scoped CStarAlgebra


universe u


attribute [instance] CStarPack.inst

end MaxTensor
end KirchbergRordam.GenericRW
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FactorIndependence
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.DetectingSpace.quotientNormedRing _root_.OAI.KirchbergRordam.GenericRW.PureStates.locallyConvexReal _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct


open scoped InnerProductSpace

namespace KirchbergRordam.GenericRW.MaxTensor
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

open scoped CStarAlgebra


lemma commute_of_legs (π : Algebra A B →⋆ₐ[ℂ] C) (T : C)
    (hL : ∀ a, Commute T (π (includeLeft a)))
    (hR : ∀ b, Commute T (π (includeRight b))) :
    ∀ x, Commute T (π x) := by
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    change IsClosed {x | T * π x = π x * T}
    exact isClosed_eq (continuous_const.mul (map_continuous π))
      ((map_continuous π).mul continuous_const)
  | ih x =>
    suffices ∀ tensor : A ⊗[ℂ] B, Commute T (π (of (rawEquiv tensor))) from this x
    intro tensor
    induction tensor using OAI.tensorInductionOn with
    | add x y hx hy => simpa only [map_add] using hx.add_right hy
    | tmul a b =>
      change Commute T (π (of (a ⊗ₜ[ℂ] b)))
      rw [of_tmul, map_mul]
      exact (hL a).mul_right (hR b)

end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.GenericRW.MaxTensor
section
universe u
variable (D : Type u) [CStarAlgebra D]


lemma commute_legs (n : ℕ) (i j : Fin (n+1)) (hij : i ≠ j) (a b : D) :
    Commute (leg D n i a) (leg D n j b) := by
  induction n with
  | zero => exact (hij ((Fin.eq_zero i).trans (Fin.eq_zero j).symm)).elim
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => exact legs_commute a (leg D n j b)
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (legs_commute b (leg D n i a)).symm
      | succ j => exact (ih i j (fun h => hij (congrArg Fin.succ h))).map includeRight

variable {D} {C : Type*} [CStarAlgebra C]

lemma commute_of_power_legs (n : ℕ) (π : (powerPack D n) →⋆ₐ[ℂ] C) (T : C)
    (h : ∀ i a, Commute T (π (leg D n i a))) : ∀ x, Commute T (π x) := by
  induction n with
  | zero => exact fun x => h 0 x
  | succ n ih =>
    apply commute_of_legs π T
    · exact fun a => h 0 a
    · exact ih (π.comp includeRight) (fun i a => h i.succ a)

end

end KirchbergRordam.GenericRW.MaxTensor

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_HereditaryTransport
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.ConeModel.coneSubringClass _root_.OAI.KirchbergRordam.GenericRW.ConeModel.instCStarAlgebraSubtypeContinuousMapElemRealUnitIntervalM2MemStarSubalgebraComplexCone _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
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
namespace ConeModel
open scoped ContinuousMapZero BigOperators ComplexOrder

def evaluate (t : unitInterval) : Cone →⋆ₐ[ℂ] M2 := (eval t).comp coneSubalgebra.subtype

lemma evaluate_sum {ι : Type*} (s : Finset ι) (f : ι → Cone) (t : unitInterval) :
    ((∑ i ∈ s, f i : Cone): C(unitInterval,M2)) t = ∑ i ∈ s, (f i:C(unitInterval,M2)) t :=
  map_sum (evaluate t) f s

lemma evaluate_add (f g : Cone) (t : unitInterval) :
    ((f+g:Cone):C(unitInterval,M2)) t = (f:C(unitInterval,M2)) t + (g:C(unitInterval,M2)) t := rfl

lemma matrixSum_entry {ι : Type*} (s : Finset ι) (f : ι → M2) (i j : Fin rankNum) :
    (∑ k ∈ s, f k) i j = ∑ k ∈ s, f k i j := Matrix.sum_apply i j s f

lemma coefficients_zero (m : ConeMatrix) : coefficients m 0 = 0 := by
  ext i j
  exact map_zero (m i j)

abbrev unitCoefficients : Unitization ℂ ConeMatrix →⋆ₐ[ℂ] C(unitInterval, M2) :=
  (Unitization.starLift (R := ℂ) (A := ConeMatrix) (C := C(unitInterval, M2))) coefficients

lemma unitCoefficients_zero (m : Unitization ℂ ConeMatrix) :
    unitCoefficients m 0 = algebraMap ℂ M2 m.fst := by
  change (algebraMap ℂ C(unitInterval, M2) m.fst + coefficients m.snd) 0 = _
  rw [ContinuousMap.add_apply, coefficients_zero, add_zero]
  rfl

def toCone : Unitization ℂ ConeMatrix →⋆ₐ[ℂ] Cone :=
  unitCoefficients.codRestrict coneSubalgebra fun m => by
    change unitCoefficients m 0 ∈ (⊥ : StarSubalgebra ℂ M2)
    rw [unitCoefficients_zero]
    exact StarSubalgebra.algebraMap_mem _ _

lemma toCone_injective : Function.Injective toCone := by
  intro m n h
  have he := congrArg (fun f : Cone => (f : C(unitInterval, M2)) 0) h
  change unitCoefficients m 0 = unitCoefficients n 0 at he
  rw [unitCoefficients_zero, unitCoefficients_zero] at he
  have hf : m.fst = n.fst := (FaithfulSMul.algebraMap_injective ℂ M2) he
  apply Unitization.ext hf
  ext i j t
  have hh := congrArg (fun f : Cone => (f : C(unitInterval, M2)) t i j) h
  change (algebraMap ℂ M2 m.fst + coefficients m.snd t) i j =
    (algebraMap ℂ M2 n.fst + coefficients n.snd t) i j at hh
  rw [hf] at hh
  exact add_left_cancel hh

lemma toCone_surjective : Function.Surjective toCone := by
  intro f
  obtain ⟨c, hc⟩ := f.property
  let m : ConeMatrix := fun i j =>
    ⟨⟨fun t => (f : C(unitInterval, M2)) t i j - (algebraMap ℂ M2 c) i j, by
      fun_prop⟩, by
      change (f : C(unitInterval, M2)) 0 i j - (algebraMap ℂ M2 c) i j = 0
      rw [show (f : C(unitInterval, M2)) 0 = algebraMap ℂ M2 c from hc.symm]
      exact sub_self _⟩
  refine ⟨⟨c, m⟩, ?_⟩
  apply Subtype.ext
  ext t i j
  change (algebraMap ℂ M2 c) i j + ((f : C(unitInterval, M2)) t i j -
    (algebraMap ℂ M2 c) i j) = (f : C(unitInterval, M2)) t i j
  ring


def equiv : Unitization ℂ ConeMatrix ≃⋆ₐ[ℂ] Cone :=
  StarAlgEquiv.ofBijective toCone ⟨toCone_injective, toCone_surjective⟩

end ConeModel

open scoped ContinuousMapZero BigOperators ComplexOrder
namespace ConeModel

def corner (i j : Fin rankNum) : Cone :=
  toCone (Unitization.inr (Matrix.single i j (IntervalCalculus.coordMul 1)))

lemma corner_apply (i j : Fin rankNum) (t : unitInterval) :
    (corner i j : C(unitInterval, M2)) t =
      (t : ℂ) • CStarMatrix.ofMatrix (Matrix.single i j 1) := by
  ext k l
  change ((algebraMap ℂ M2 0) + coefficients (Matrix.single i j (IntervalCalculus.coordMul 1)) t) k l = _
  simp only [map_zero, zero_add, coefficients_apply]
  by_cases hi : i = k <;> by_cases hj : j = l <;>
    simp [Matrix.single, hi, hj, IntervalCalculus.coordMul_apply]

end ConeModel

end KirchbergRordam.GenericRW


namespace KirchbergRordam.GenericRW.HereditaryTransport
open ClosedRightRange
variable {A : Type*} [CStarAlgebra A]


instance cornerClosed (a : A) (ha : IsSelfAdjoint a) : IsClosed (corner a ha : Set A) := isClosed_closure

omit instSize in
lemma mem_corner.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    (a : A) (ha : IsSelfAdjoint a) (x : A) : a*x*a ∈ corner a ha :=
  subset_closure ⟨x,rfl⟩

end KirchbergRordam.GenericRW.HereditaryTransport

namespace KirchbergRordam.GenericRW
namespace Vanish
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]


instance closed (S : Set X) : IsClosed ((algebra S : NonUnitalStarSubalgebra ℂ C(X,ℂ)) : Set C(X,ℂ)) := by
  change IsClosed {f : C(X,ℂ) | ∀ t ∈ S, f t = 0}
  convert (isClosed_biInter fun (t : X) (_ : t ∈ S) =>
    isClosed_eq (continuous_eval_const t : Continuous (fun f : C(X,ℂ) => f t)) (continuous_const (y := (0:ℂ)))) using 1
  ext f; simp

instance instNonUnitalCStarAlgebraSubtypeContinuousMapComplexMemNonUnitalStarSubalgebraFunctions (S : Set X) : NonUnitalCStarAlgebra (Functions S) := inferInstance


omit instSize in
lemma multiplier_dense.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {X : Type contextLevel1}
    [TopologicalSpace X]
    [CompactSpace X]
    [T2Space X]
    (p : C(X,ℂ)) : DenseRange (multiplier p) := by
  let I : Ideal C(X,ℂ) := Ideal.span {p}
  have hs : ContinuousMap.setOfIdeal I = {t | p t = 0}ᶜ := by
    ext t
    rw [ContinuousMap.mem_setOfIdeal]
    constructor
    · rintro ⟨f,hf,hne⟩ ht
      obtain ⟨g,rfl⟩ := Ideal.mem_span_singleton'.mp hf
      apply hne
      simp [show p t=0 from ht]
    · intro ht
      exact ⟨p,Ideal.subset_span rfl,ht⟩
  have hi : (fun f : Functions {t | p t=0} => (f : C(X,ℂ))) '' Set.range (multiplier p) = I := by
    ext f
    constructor
    · rintro ⟨g,⟨v,rfl⟩,rfl⟩
      exact Ideal.mul_mem_right _ I (Ideal.subset_span rfl)
    · intro hf
      obtain ⟨g,hg⟩ := Ideal.mem_span_singleton'.mp hf
      refine ⟨multiplier p g,⟨g,rfl⟩,?_⟩
      change p*g=f
      rw [mul_comm,hg]
  apply (isUniformEmbedding_subtype_val.isEmbedding.isInducing.dense_iff).mpr
  intro f
  rw [hi,← Ideal.coe_closure,← ContinuousMap.idealOfSet_ofIdeal_eq_closure,hs]
  intro t ht
  exact f.property t (by simpa only [compl_compl] using ht)

end Vanish
end KirchbergRordam.GenericRW
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_ConeModel
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
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


namespace KirchbergRordam.GenericRW.ConeModel
open scoped ComplexOrder ContinuousMapZero BigOperators
open IntervalCalculus HereditaryTransport

abbrev tip : Cone := scalar (1-coord)
lemma tip_selfAdjoint : IsSelfAdjoint tip := by
  apply IsSelfAdjoint.map
  ext t
  simp [coord]

lemma scalar_continuous : Continuous scalar := by
  apply Continuous.subtype_mk
  let g : C(ℂ,M2) := ⟨algebraMap ℂ M2,(algebraMapCLM ℂ M2).continuous⟩
  exact g.continuous_postcomp


def entry (i j : Fin rankNum) (f : C(unitInterval,ℂ)₀) : Cone :=
  ⟨⟨fun t => f t • CStarMatrix.ofMatrix (Matrix.single i j (1:ℂ)),by fun_prop⟩,by
    change f 0 • _ ∈ (⊥ : StarSubalgebra ℂ M2)
    rw [map_zero,zero_smul]
    exact zero_mem _⟩

lemma entry_continuous (i j : Fin rankNum) : Continuous (entry i j) := by
  apply Continuous.subtype_mk
  let g : C(ℂ,M2) := ⟨fun c => c • CStarMatrix.ofMatrix (Matrix.single i j (1:ℂ)),by fun_prop⟩
  exact g.continuous_postcomp.comp ContinuousMapZero.isEmbedding_toContinuousMap.continuous

lemma scalar_tip_mem (f : C(unitInterval,ℂ)) (hf : f 1=0) : scalar f ∈ HereditaryTransport.corner tip tip_selfAdjoint := by
  let p : C(unitInterval,ℂ) := (1-coord)^2
  have hzero (t : unitInterval) (ht : p t=0) : t=1 := by
    have h : (1-((t:ℝ):ℂ))^2=0 := ht
    have hc : ((t:ℝ):ℂ)=1 := by
      have := sq_eq_zero_iff.mp h
      exact (sub_eq_zero.mp this).symm
    apply Subtype.ext
    exact_mod_cast hc
  let f' : Vanish.Functions {t | p t=0} := ⟨f,by intro t ht; rw [hzero t ht]; exact hf⟩
  have hh (x : Vanish.Functions {t | p t=0}) : scalar x.val ∈ HereditaryTransport.corner tip tip_selfAdjoint := by
    refine (Vanish.multiplier_dense p).induction_on x
      ((cornerClosed tip tip_selfAdjoint).preimage (scalar_continuous.comp continuous_subtype_val)) ?_
    intro g
    have he : scalar ((Vanish.multiplier p g).val)=tip*scalar g*tip := by
      change scalar (p*g)=scalar (1-coord)*scalar g*scalar (1-coord)
      rw [← map_mul,← map_mul]
      congr 1
      dsimp [p]
      ring
    rw [he]
    exact HereditaryTransport.mem_corner tip tip_selfAdjoint (scalar g)
  exact hh f'

def entryWeight : C(unitInterval,ℂ) := coord*(1-coord)^2

omit instSize in
lemma weight_zero
    [KirchbergRordam.GenericRW.Size]
    : entryWeight 0=0 := by simp [entryWeight,coord]

def fromWeight (f : Vanish.Functions {t | entryWeight t=0}) : C(unitInterval,ℂ)₀ :=
  ⟨f.val,f.property 0 weight_zero⟩

lemma fromWeight_continuous : Continuous fromWeight := by
  rw [ContinuousMapZero.isEmbedding_toContinuousMap.continuous_iff]
  exact continuous_subtype_val

lemma entry_tip_mem (i j : Fin rankNum) (f : C(unitInterval,ℂ)₀) (hf : f 1=0) :
    entry i j f ∈ HereditaryTransport.corner tip tip_selfAdjoint := by
  have hzero (t : unitInterval) (ht : entryWeight t=0) : t=0 ∨ t=1 := by
    change ((t:ℝ):ℂ)*(1-((t:ℝ):ℂ))^2=0 at ht
    rcases mul_eq_zero.mp ht with h|h
    · left; apply Subtype.ext; exact_mod_cast h
    · right; apply Subtype.ext
      have hc : ((t:ℝ):ℂ)=1 := (sub_eq_zero.mp (sq_eq_zero_iff.mp h)).symm
      exact_mod_cast hc
  let f' : Vanish.Functions {t | entryWeight t=0} := ⟨(f:C(unitInterval,ℂ)),by
    intro t ht
    rcases hzero t ht with rfl|rfl
    · exact map_zero f
    · exact hf⟩
  have hh (x : Vanish.Functions {t | entryWeight t=0}) :
      entry i j (fromWeight x) ∈ HereditaryTransport.corner tip tip_selfAdjoint := by
    refine (Vanish.multiplier_dense entryWeight).induction_on x
      ((cornerClosed tip tip_selfAdjoint).preimage ((entry_continuous i j).comp fromWeight_continuous)) ?_
    intro g
    have he : entry i j (fromWeight (Vanish.multiplier entryWeight g))=
        tip*entry i j (coordMul g)*tip := by
      apply Subtype.ext
      apply ContinuousMap.ext
      intro t
      change ((((t:ℝ):ℂ)*(1-((t:ℝ):ℂ))^2)*g t) • CStarMatrix.ofMatrix (Matrix.single i j (1:ℂ))=
        (algebraMap ℂ M2 (1-((t:ℝ):ℂ)))*
          ((((t:ℝ):ℂ)*g t) • CStarMatrix.ofMatrix (Matrix.single i j (1:ℂ)))*
          (algebraMap ℂ M2 (1-((t:ℝ):ℂ)))
      simp only [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,smul_smul]
      congr 1
      ring
    rw [he]
    exact HereditaryTransport.mem_corner tip tip_selfAdjoint _
  exact hh f'


lemma vanish_one_mem {f : Cone} (hf : (f:C(unitInterval,M2)) 1=0) :
    f ∈ HereditaryTransport.corner tip tip_selfAdjoint := by
  let c : C(unitInterval,ℂ) := ⟨fun t => (f:C(unitInterval,M2)) t 0 0,by fun_prop⟩
  have hc1 : c 1=0 := by change (f:C(unitInterval,M2)) 1 0 0=0; rw [hf]; rfl
  have hsc := scalar_tip_mem c hc1
  obtain ⟨z,hz⟩ := f.property
  have hz' : (f:C(unitInterval,M2)) 0=algebraMap ℂ M2 z := hz.symm
  let r (i j : Fin rankNum) : C(unitInterval,ℂ)₀ := ⟨⟨fun t =>
      (f:C(unitInterval,M2)) t i j-(algebraMap ℂ M2 (c t)) i j,by fun_prop⟩,by
    change (f:C(unitInterval,M2)) 0 i j-(algebraMap ℂ M2 ((f:C(unitInterval,M2)) 0 0 0)) i j=0
    rw [hz']
    have hz00 : (algebraMap ℂ M2 z) 0 0=z := by simp [Algebra.algebraMap_eq_smul_one]
    rw [hz00]
    exact sub_self _⟩
  have hr (i j : Fin rankNum) : r i j 1=0 := by
    change (f:C(unitInterval,M2)) 1 i j-(algebraMap ℂ M2 (c 1)) i j=0
    rw [hf,hc1,map_zero]; exact sub_self _
  have he : f=scalar c+∑ i,∑ j,entry i j (r i j) := by
    apply Subtype.ext
    ext t u v
    simp only [evaluate_add,evaluate_sum,CStarMatrix.add_apply,matrixSum_entry]
    change (f:C(unitInterval,M2)) t u v = (algebraMap ℂ M2 (c t)) u v +
      ∑ i, ∑ j, (r i j t) * (Matrix.single i j (1:ℂ)) u v
    simp [Matrix.single, ite_and, mul_ite, r]
  rw [he]
  exact (HereditaryTransport.corner tip tip_selfAdjoint).add_mem hsc
    ((HereditaryTransport.corner tip tip_selfAdjoint).sum_mem fun i _ =>
      (HereditaryTransport.corner tip tip_selfAdjoint).sum_mem fun j _ => entry_tip_mem i j (r i j) (hr i j))

end KirchbergRordam.GenericRW.ConeModel

namespace KirchbergRordam.GenericRW.ConeModel
open scoped ComplexOrder BigOperators
open IntervalCalculus
lemma scalar_coord : scalar coord = ∑ i : Fin rankNum, corner i i := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  rw [evaluate_sum]
  change algebraMap ℂ M2 (coord t) = ∑ i : Fin rankNum, (corner i i:C(unitInterval,M2)) t
  simp only [corner_apply]
  ext i j
  rw [matrixSum_entry]
  change (algebraMap ℂ M2 (coord t)) i j = ∑ k : Fin rankNum, (t:ℂ) * (Matrix.single k k (1:ℂ)) i j
  simp [coord, Algebra.algebraMap_eq_smul_one, Matrix.single, ite_and, mul_ite, CStarMatrix.one_apply]
end KirchbergRordam.GenericRW.ConeModel

namespace KirchbergRordam.GenericRW.ConeModel
open scoped ComplexOrder CStarAlgebra


def defectSubalgebra : NonUnitalStarSubalgebra ℂ Cone where
  carrier := {f | (f:C(unitInterval,M2)) 1=0}
  zero_mem' := rfl
  add_mem' := by intro f g hf hg; change (f:C(unitInterval,M2)) 1+(g:C(unitInterval,M2)) 1=0; rw [hf,hg,add_zero]
  mul_mem' := by intro f g hf hg; change (f:C(unitInterval,M2)) 1*(g:C(unitInterval,M2)) 1=0; rw [hf,zero_mul]
  smul_mem' := by intro c f hf; change c • (f:C(unitInterval,M2)) 1=0; rw [hf,smul_zero]
  star_mem' := by intro f hf; change star ((f:C(unitInterval,M2)) 1)=0; rw [hf,star_zero]

abbrev Defect := defectSubalgebra
instance defectZero : Zero Defect := ⟨⟨0, rfl⟩⟩

instance defectClosed : IsClosed (defectSubalgebra : Set Cone) :=
  isClosed_singleton.preimage ((continuous_eval_const (1:unitInterval)).comp continuous_subtype_val)
instance instNonUnitalCStarAlgebraSubtypeContinuousMapElemRealUnitIntervalM2MemStarSubalgebraComplexConeNonUnitalStarSubalgebraDefect : NonUnitalCStarAlgebra Defect := inferInstance


def toHereditary : Defect →⋆ₙₐ[ℂ] HereditaryTransport.corner tip tip_selfAdjoint where
  toFun f := ⟨f,vanish_one_mem f.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl


def scalarDefect (f : C(unitInterval,ℂ)) (hf : f 1=0) : Defect :=
  ⟨scalar f,by change algebraMap ℂ M2 (f 1)=0; rw [hf,map_zero]⟩

end KirchbergRordam.GenericRW.ConeModel

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FlipPath
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
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

abbrev M2 := Matrix (Fin rankNum) (Fin rankNum) ℂ
abbrev M4 := Matrix (Fin rankNum × Fin rankNum) (Fin rankNum × Fin rankNum) ℂ

def flip : M4 := fun i j => if i.1=j.2 ∧ i.2=j.1 then 1 else 0

lemma flip_star : star flip=flip := by
  ext i j
  simp only [Matrix.star_apply,flip]
  split_ifs <;> simp_all

lemma flip_mul : flip*flip=1 := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp only [Matrix.mul_apply,flip,Fintype.sum_prod_type]
  simp [Matrix.one_apply,Prod.mk.injEq,ite_and]

def left (a : M2) : M4 := fun i j => a i.1 j.1 * if i.2=j.2 then 1 else 0
def right (a : M2) : M4 := fun i j => (if i.1=j.1 then 1 else 0) * a i.2 j.2

lemma flip_exchange (a : M2) : right a*flip=flip*left a := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,left,right,flip]
  simp [ite_and,mul_ite,ite_mul,eq_comm]


omit instSize in
lemma phase_zero
    [KirchbergRordam.GenericRW.Size]
    : phase 0=1 := by simp [phase,angle]
omit instSize in
lemma phase_top
    [KirchbergRordam.GenericRW.Size]
    {t : unitInterval} (ht : 2/3 ≤ (t:ℝ)) : phase t= -1 := by
  have h : angle t=1 := by change min (max (3*(t:ℝ)-1) 0) 1=1; rw [min_eq_right]; exact le_max_of_le_left (by linarith)
  simp [phase,h,Complex.exp_pi_mul_I]

omit instSize in
lemma phase_unitary
    [KirchbergRordam.GenericRW.Size]
    (t : unitInterval) : star (phase t)*phase t=1 := by
  have hn : ‖phase t‖=1 := Complex.norm_exp_ofReal_mul_I _
  rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,hn]
  norm_num


def path (t : unitInterval) : M4 := ((1+phase t)/2) • (1:M4)+((1-phase t)/2) • flip

lemma path_zero : path 0=1 := by simp [path,phase_zero]
lemma path_top {t : unitInterval} (ht : 2/3 ≤ (t:ℝ)) : path t=flip := by simp [path,phase_top ht]

lemma path_continuous : Continuous path := by unfold path; fun_prop

lemma path_star_mul (t : unitInterval) : star (path t)*path t=1 := by
  have hz := phase_unitary t
  have hs : star (2:ℂ)=2 := by simp
  simp only [path,star_add,star_smul,star_one,flip_star,star_div₀,hs,star_add,star_sub,
    smul_add,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_smul,one_mul,mul_one,flip_mul]
  have h1 : (star ((1:ℂ)+phase t)/2)*((1+phase t)/2)+
      (star ((1:ℂ)-phase t)/2)*((1-phase t)/2)=1 := by
    simp only [star_add,star_sub,star_one]; calc
      _=(1+star (phase t)*phase t)/2 := by ring
      _=1 := by rw [hz]; norm_num
  have h2 : (star ((1:ℂ)+phase t)/2)*((1-phase t)/2)+
      (star ((1:ℂ)-phase t)/2)*((1+phase t)/2)=0 := by
    simp only [star_add,star_sub,star_one]; calc
      _=(1-star (phase t)*phase t)/2 := by ring
      _=0 := by rw [hz]; norm_num
  calc
    _=(((1+star (phase t))/2)*((1+phase t)/2)+((1-star (phase t))/2)*((1-phase t)/2)) • (1:M4)+
      (((1+star (phase t))/2)*((1-phase t)/2)+((1-star (phase t))/2)*((1+phase t)/2)) • flip := by
        rw [add_smul,add_smul]; module
    _=1 := by simp only [star_add,star_sub,star_one] at h1 h2; rw [h1,h2,one_smul,zero_smul,add_zero]

lemma path_mul_star (t : unitInterval) : path t*star (path t)=1 := by
  exact mul_eq_one_comm.mp (path_star_mul t)



end KirchbergRordam.GenericRW.FlipPath

namespace KirchbergRordam.GenericRW.ConeModel
lemma scalar_commute (f : C(unitInterval,ℂ)) (x : Cone) : Commute (scalar f) x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  exact Algebra.commutes (f t) ((x:C(unitInterval,M2)) t)
end KirchbergRordam.GenericRW.ConeModel

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_WeightedUnits
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
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


namespace KirchbergRordam.GenericRW.ConeModel

def scalarRemainder (f : C(unitInterval,ℂ)) : Defect :=
  scalarDefect (f-ContinuousMap.const _ (f 1)) (by simp)
end KirchbergRordam.GenericRW.ConeModel

namespace KirchbergRordam.GenericRW.ConeModel

def defectMul (x : Defect) (y : Cone) : Defect :=
  ⟨(x:Cone)*y,by
    change (x:C(unitInterval,M2)) 1*(y:C(unitInterval,M2)) 1=0
    rw [x.property,zero_mul]⟩
end KirchbergRordam.GenericRW.ConeModel

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FieldCalculus
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
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

open scoped Matrix Kronecker ComplexOrder

instance instFiniteDimensionalComplexM6 : FiniteDimensional ℂ M6 :=
  inferInstanceAs (FiniteDimensional ℂ (Matrix (Fin rankNum × Fin (rankNum+1)) (Fin rankNum × Fin (rankNum+1)) ℂ))

instance dimensionDropClosed : IsClosed
    (dimensionDropSubalgebra : Set C(unitInterval, M6)) := by
  change IsClosed ((fun f : C(unitInterval, M6) => f 0) ⁻¹' (leftMatrix.range : Set M6) ∩
    (fun f : C(unitInterval, M6) => f 1) ⁻¹' (rightMatrix.range : Set M6))
  exact ((leftMatrix.range.toSubalgebra.toSubmodule.closed_of_finiteDimensional).preimage
    (continuous_eval_const (0 : unitInterval))).inter
    ((rightMatrix.range.toSubalgebra.toSubmodule.closed_of_finiteDimensional).preimage
    (continuous_eval_const (1 : unitInterval)))


instance dropSubringClass : SubringClass
    (StarSubalgebra ℂ C(unitInterval, M6)) C(unitInterval, M6) :=
  StarSubalgebra.subringClass (R := ℂ) (A := C(unitInterval, M6))

instance instCStarAlgebraSubtypeContinuousMapElemRealUnitIntervalM6MemStarSubalgebraComplexDimensionDrop23 : CStarAlgebra DimensionDrop23 :=
  StarSubalgebra.cstarAlgebra dimensionDropSubalgebra

end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.FieldCalculus
open scoped BigOperators
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [CStarAlgebra A]


namespace Data
variable (D : Data X ι A)
abbrev Domain := Vanish.Functions {t | D.p t=0}

end Data
end KirchbergRordam.GenericRW.FieldCalculus
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_DropSections
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
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


namespace KirchbergRordam.GenericRW.DropSections
open scoped Matrix Kronecker BigOperators ComplexOrder
open IntervalCalculus
abbrev Ix := Fin rankNum × Fin (rankNum+1)
abbrev Mat := Matrix Ix Ix Scalar
abbrev Small2 := Matrix (Fin rankNum) (Fin rankNum) ℂ
abbrev Small3 := Matrix (Fin (rankNum+1)) (Fin (rankNum+1)) ℂ


def entries : C(unitInterval,M6) →⋆ₐ[ℂ] Mat where
  toFun f i j := ⟨fun t => f t i j, by
    exact (continuous_apply j).comp ((continuous_apply i).comp
      f.continuous)⟩
  map_zero' := by ext i j t; rfl
  map_one' := by ext i j t; by_cases h : i=j <;> simp [Matrix.one_apply,h]
  map_add' _ _ := by ext i j t; rfl
  map_mul' f g := by
    ext i j t
    change (∑ k, f t i k * g t k j) = ((∑ k, _ * _) : Scalar) t
    simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply]
    rfl
  commutes' c := by ext i j t; by_cases h : i=j <;> simp [Algebra.algebraMap_eq_smul_one,h]
  map_star' f := by ext i j t; rfl

lemma entries_apply (f : C(unitInterval,M6)) (i j : Ix) (t : unitInterval) :
    entries f i j t = f t i j := rfl


def constMat : Matrix Ix Ix ℂ →⋆ₐ[ℂ] Mat where
  toFun a i j := ContinuousMap.const _ (a i j)
  map_zero' := by ext i j t; rfl
  map_one' := by ext i j t; by_cases h : i=j <;> simp [Matrix.one_apply,h]
  map_add' _ _ := by ext i j t; rfl
  map_mul' a b := by
    ext i j t
    change (∑ k, a i k * b k j) =
      ((∑ k, ContinuousMap.const _ (a i k) * ContinuousMap.const _ (b k j)) : Scalar) t
    simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.const_apply]
  commutes' c := by ext i j t; by_cases h : i=j <;> simp [Algebra.algebraMap_eq_smul_one,h]
  map_star' _ := by ext i j t; rfl

def leftConst : Small2 →⋆ₐ[ℂ] Mat := constMat.comp leftMatrixAlgebra

def rightConst : Small3 →⋆ₐ[ℂ] Mat := constMat.comp rightMatrixAlgebra


def times (p : Scalar) : Mat →ₗ[ℂ] Mat where
  toFun a i j := p*a i j
  map_add' a b := by ext i j t; change p t*(a i j t+b i j t)=p t*a i j t+p t*b i j t; ring
  map_smul' c a := by ext i j t; change p t*(c*a i j t)=c*(p t*a i j t); ring

lemma times_mul (p q : Scalar) (a b : Mat) : times p a*times q b=times (p*q) (a*b) := by
  ext i j t
  change ((∑ k, (p * a i k) * (q * b k j)) : Scalar) t =
    ((p * q) * (∑ k, a i k * b k j)) t
  simp only [ContinuousMap.mul_apply, ContinuousMap.sum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

def leftPart : Small2 →ₗ[ℂ] Mat := (times (1-coord)).comp leftConst.toLinearMap
def rightPart : Small3 →ₗ[ℂ] Mat := (times coord).comp rightConst.toLinearMap


def endLeft : DimensionDrop23 →ₗ[ℂ] Small2 where
  toFun f i j := entries f.val (i,0) (j,0) 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def endRight : DimensionDrop23 →ₗ[ℂ] Small3 where
  toFun f i j := entries f.val (0,i) (0,j) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma at_zero (f : DimensionDrop23) (i j : Ix) :
    entries f.val i j 0 = leftMatrixAlgebra (endLeft f) i j := by
  obtain ⟨a,ha⟩ := f.property.1
  change leftMatrix a = f.val 0 at ha
  have he : endLeft f = CStarMatrix.ofMatrixL.symm a := by
    ext u v
    change CStarMatrix.ofMatrixL.symm (f.val 0) (u,0) (v,0) = _
    rw [← ha]
    change (CStarMatrix.ofMatrixL.symm a u v)*(1:ℂ)=_
    exact mul_one _
  rw [he,entries_apply,← ha]
  rfl

lemma at_one (f : DimensionDrop23) (i j : Ix) :
    entries f.val i j 1 = rightMatrixAlgebra (endRight f) i j := by
  obtain ⟨a,ha⟩ := f.property.2
  change rightMatrix a = f.val 1 at ha
  have he : endRight f = CStarMatrix.ofMatrixL.symm a := by
    ext u v
    change CStarMatrix.ofMatrixL.symm (f.val 1) (0,u) (0,v) = _
    rw [← ha]
    change (1:ℂ)*(CStarMatrix.ofMatrixL.symm a u v)=_
    exact one_mul _
  rw [he,entries_apply,← ha]
  rfl



def weight : Scalar := (1-coord)*coord
abbrev InteriorScalar := Vanish.Functions {t | weight t=0}
abbrev Interior := Matrix Ix Ix InteriorScalar

omit instSize in
lemma weight_zero
    [KirchbergRordam.GenericRW.Size]
    (t : unitInterval) : weight t=0 ↔ t=0 ∨ t=1 := by
  change (1-(t:ℝ):ℂ)*(t:ℝ)=0 ↔ _
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h|h
    · right
      apply Subtype.ext
      exact_mod_cast (sub_eq_zero.mp h).symm
    · left
      apply Subtype.ext
      exact_mod_cast h
  · rintro (rfl|rfl) <;> simp


def embed : Interior →ₗ[ℂ] Mat where
  toFun m i j := m i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma embed_injective : Function.Injective embed := by
  intro a b h
  funext i j
  apply Subtype.ext
  exact congr_fun (congr_fun h i) j

lemma embed_mul (m n : Interior) : embed (m*n)=embed m*embed n := by
  ext i j t
  change ((∑ k, m i k*n k j : InteriorScalar) : Scalar) t =
    (∑ k, (m i k : Scalar)*(n k j : Scalar)) t
  simp

lemma embed_star (m : Interior) : embed (star m)=star (embed m) := rfl

def residual : DimensionDrop23 →ₗ[ℂ] Mat :=
  entries.toLinearMap.comp dimensionDropSubalgebra.subtype.toLinearMap -
    leftPart.comp endLeft - rightPart.comp endRight


def interior : DimensionDrop23 →ₗ[ℂ] Interior where
  toFun f i j := ⟨residual f i j, by
    intro t ht
    rcases (weight_zero t).mp ht with rfl|rfl
    · change entries f.val i j 0 - (1-coord 0)*leftMatrixAlgebra (endLeft f) i j -
        coord 0*rightMatrixAlgebra (endRight f) i j = 0
      simp [at_zero]
    · change entries f.val i j 1 - (1-coord 1)*leftMatrixAlgebra (endLeft f) i j -
        coord 1*rightMatrixAlgebra (endRight f) i j = 0
      simp [at_one]⟩
  map_add' f g := by
    funext i j
    apply Subtype.ext
    exact congr_fun (congr_fun (map_add residual f g) i) j
  map_smul' c f := by
    funext i j
    apply Subtype.ext
    exact congr_fun (congr_fun (map_smul residual c f) i) j

lemma decomposition (f : DimensionDrop23) :
    entries f.val = leftPart (endLeft f)+rightPart (endRight f)+embed (interior f) := by
  change entries f.val = leftPart (endLeft f)+rightPart (endRight f)+
    (entries f.val-leftPart (endLeft f)-rightPart (endRight f))
  abel



lemma endLeft_mul (f g : DimensionDrop23) : endLeft (f*g)=endLeft f*endLeft g := by
  ext i j
  change ∑ u : Ix, entries f.val (i,0) u 0*entries g.val u (j,0) 0 = _
  simp [at_zero,leftMatrixAlgebra,Fintype.sum_prod_type,Matrix.mul_apply,Matrix.one_apply]

lemma endRight_mul (f g : DimensionDrop23) : endRight (f*g)=endRight f*endRight g := by
  ext i j
  change ∑ u : Ix, entries f.val (0,i) u 1*entries g.val u (0,j) 1 = _
  simp [at_one,rightMatrixAlgebra,Fintype.sum_prod_type,Matrix.mul_apply,Matrix.one_apply]

lemma endLeft_one : endLeft 1=1 := by
  ext i j
  change (1 : M6) (i,0) (j,0) = (1 : Small2) i j
  simp [CStarMatrix.one_apply,Matrix.one_apply]

lemma endRight_one : endRight 1=1 := by
  ext i j
  change (1 : M6) (0,i) (0,j) = (1 : Small3) i j
  simp [CStarMatrix.one_apply,Matrix.one_apply]

lemma endLeft_star (f : DimensionDrop23) : endLeft (star f)=star (endLeft f) := rfl
lemma endRight_star (f : DimensionDrop23) : endRight (star f)=star (endRight f) := rfl

lemma times_star (p : Scalar) (m : Mat) : star (times p m)=times (star p) (star m) := by
  ext i j t
  change star (p t*m j i t)=star (p t)*star (m j i t)
  rw [star_mul,mul_comm]

lemma leftPart_star (a : Small2) : leftPart (star a)=star (leftPart a) := by
  change times (1-coord) (leftConst (star a))=star (times (1-coord) (leftConst a))
  rw [times_star,map_star]
  have hc : star coord=coord := by ext t; simp [coord]
  rw [star_sub,star_one,hc]

lemma rightPart_star (a : Small3) : rightPart (star a)=star (rightPart a) := by
  change times coord (rightConst (star a))=star (times coord (rightConst a))
  rw [times_star,map_star]
  have hc : star coord=coord := by ext t; simp [coord]
  rw [hc]


local instance instSMulComplexSubtypeContinuousMapElemRealUnitIntervalMemNonUnitalStarSubalgebraInteriorScalar : SMul ℂ InteriorScalar := (NonUnitalStarSubalgebra.instModule InteriorScalar).toSMul

def weighted : Matrix Ix Ix ℂ →ₗ[ℂ] Interior where
  toFun m u v := Vanish.multiplier weight (ContinuousMap.const _ (m u v))
  map_add' m n := by ext u v t; change weight t*(m u v+n u v)=weight t*m u v+weight t*n u v; ring
  map_smul' z m := by ext u v t; change weight t*(z*m u v)=z*(weight t*m u v); ring

def scalarMul (p : Scalar) (f : InteriorScalar) : InteriorScalar :=
  ⟨p*f.val,by intro t ht; simp [f.property t ht]⟩

def actionLeft (a : Small2) (m : Interior) : Interior :=
  fun u v => ∑ j, (a u.1 j) • scalarMul (1-coord) (m (j,u.2) v)

def actionRight (a : Small3) (m : Interior) : Interior :=
  fun u v => ∑ j, (a u.2 j) • scalarMul coord (m (u.1,j) v)

lemma embed_actionLeft (a : Small2) (m : Interior) :
    embed (actionLeft a m)=leftPart a*embed m := by
  ext u v t
  change ((∑ j, (a u.1 j) • scalarMul (1-coord) (m (j,u.2) v) : InteriorScalar) : Scalar) t =
    ((∑ k : Ix, ((1-coord) * ContinuousMap.const _ (a u.1 k.1 * (1 : Small3) u.2 k.2)) *
      (m k v).val) : Scalar) t
  simp [scalarMul, Fintype.sum_prod_type, Matrix.one_apply, mul_left_comm, mul_comm]

lemma embed_actionRight (a : Small3) (m : Interior) :
    embed (actionRight a m)=rightPart a*embed m := by
  ext u v t
  change ((∑ j, (a u.2 j) • scalarMul coord (m (u.1,j) v) : InteriorScalar) : Scalar) t =
    ((∑ k : Ix, (coord * ContinuousMap.const _ ((1 : Small2) u.1 k.1 * a u.2 k.2)) *
      (m k v).val) : Scalar) t
  rcases u with ⟨u1,u2⟩
  simp [scalarMul, Fintype.sum_prod_type, Matrix.one_apply, mul_left_comm, mul_comm]

def actionLeftRev (m : Interior) (a : Small2) : Interior := star (actionLeft (star a) (star m))
def actionRightRev (m : Interior) (a : Small3) : Interior := star (actionRight (star a) (star m))

lemma embed_actionLeftRev (m : Interior) (a : Small2) :
    embed (actionLeftRev m a)=embed m*leftPart a := by
  rw [actionLeftRev,embed_star,embed_actionLeft,embed_star,leftPart_star]
  exact (star_mul (star (leftPart a)) (star (embed m))).trans (by rw [star_star,star_star])

lemma embed_actionRightRev (m : Interior) (a : Small3) :
    embed (actionRightRev m a)=embed m*rightPart a := by
  rw [actionRightRev,embed_star,embed_actionRight,embed_star,rightPart_star]
  exact (star_mul (star (rightPart a)) (star (embed m))).trans (by rw [star_star,star_star])

lemma leftPart_mul (a c : Small2) :
    leftPart a*leftPart c=leftPart (a*c)-embed (weighted ((a*c) ⊗ₖ (1:Small3))) := by
  change times (1-coord) (leftConst a)*times (1-coord) (leftConst c)=
    times (1-coord) (leftConst (a*c))-times weight (constMat ((a*c) ⊗ₖ (1:Small3)))
  rw [times_mul,← map_mul]
  ext i j t
  change ((1-coord t)*(1-coord t))*leftMatrixAlgebra (a*c) i j =
    (1-coord t)*leftMatrixAlgebra (a*c) i j-((1-coord t)*coord t)*leftMatrixAlgebra (a*c) i j
  ring

lemma rightPart_mul (b d : Small3) :
    rightPart b*rightPart d=rightPart (b*d)-embed (weighted ((1:Small2) ⊗ₖ (b*d))) := by
  change times coord (rightConst b)*times coord (rightConst d)=
    times coord (rightConst (b*d))-times weight (constMat ((1:Small2) ⊗ₖ (b*d)))
  rw [times_mul,← map_mul]
  ext i j t
  change (coord t*coord t)*rightMatrixAlgebra (b*d) i j =
    coord t*rightMatrixAlgebra (b*d) i j-((1-coord t)*coord t)*rightMatrixAlgebra (b*d) i j
  ring

lemma leftConst_rightConst (a : Small2) (b : Small3) :
    leftConst a*rightConst b=constMat (a ⊗ₖ b) := by
  change constMat (a ⊗ₖ (1:Small3))*constMat ((1:Small2) ⊗ₖ b)=_
  rw [← map_mul,← Matrix.mul_kronecker_mul,mul_one,one_mul]

lemma rightConst_leftConst (a : Small2) (b : Small3) :
    rightConst b*leftConst a=constMat (a ⊗ₖ b) := by
  change constMat ((1:Small2) ⊗ₖ b)*constMat (a ⊗ₖ (1:Small3))=_
  rw [← map_mul,← Matrix.mul_kronecker_mul,mul_one,one_mul]

lemma leftPart_rightPart (a : Small2) (b : Small3) :
    leftPart a*rightPart b=embed (weighted (a ⊗ₖ b)) := by
  change times (1-coord) (leftConst a)*times coord (rightConst b)=times weight (constMat (a ⊗ₖ b))
  rw [times_mul,leftConst_rightConst]
  rfl

lemma rightPart_leftPart (a : Small2) (b : Small3) :
    rightPart b*leftPart a=embed (weighted (a ⊗ₖ b)) := by
  change times coord (rightConst b)*times (1-coord) (leftConst a)=times weight (constMat (a ⊗ₖ b))
  rw [times_mul,rightConst_leftConst,mul_comm coord]
  rfl


lemma interior_mul (f g : DimensionDrop23) :
    interior (f*g) = -weighted ((endLeft f*endLeft g) ⊗ₖ (1:Small3))-
      weighted ((1:Small2) ⊗ₖ (endRight f*endRight g))+
      weighted (endLeft f ⊗ₖ endRight g)+weighted (endLeft g ⊗ₖ endRight f)+
      actionLeft (endLeft f) (interior g)+actionRight (endRight f) (interior g)+
      actionLeftRev (interior f) (endLeft g)+actionRightRev (interior f) (endRight g)+
      interior f*interior g := by
  apply embed_injective
  change entries ((f*g).val)-leftPart (endLeft (f*g))-rightPart (endRight (f*g)) = _
  rw [show entries ((f*g).val)=entries f.val*entries g.val from entries.map_mul' f.val g.val,
    endLeft_mul,endRight_mul,decomposition f,decomposition g]
  simp only [map_add,map_sub,map_neg,embed_actionLeft,embed_actionRight,
    embed_actionLeftRev,embed_actionRightRev,embed_mul,mul_add,add_mul,
    leftPart_mul,rightPart_mul,leftPart_rightPart,rightPart_leftPart]
  abel

end KirchbergRordam.GenericRW.DropSections
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FunctionalCalculus
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
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
namespace Domination
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit instSize in
lemma invReg_cont
    [KirchbergRordam.GenericRW.Size]
    {τ : ℝ} (hτ : 0 < τ) : Continuous (invReg τ) := by
  apply Continuous.inv₀ (by fun_prop)
  intro t
  exact ne_of_gt (add_pos_of_nonneg_of_pos (le_max_right t 0) hτ)

lemma remReg_cont {τ : ℝ} (hτ : 0 < τ) : Continuous (remReg τ) := by
  exact continuous_const.sub (continuous_id.mul (invReg_cont hτ))

omit instSize in
lemma remReg_nonneg
    [KirchbergRordam.GenericRW.Size]
    {τ t : ℝ} (hτ : 0 < τ) (ht : 0 ≤ t) :
    0 ≤ remReg τ t := by
  dsimp only [remReg, invReg]
  rw [max_eq_left ht]
  have hs : 0 < t + τ := add_pos_of_nonneg_of_pos ht hτ
  rw [sub_nonneg, ← div_eq_mul_inv, div_le_one hs]
  linarith

omit instSize in
lemma remReg_bound
    [KirchbergRordam.GenericRW.Size]
    {τ t : ℝ} (hτ : 0 < τ) (ht : 0 ≤ t) :
    (remReg τ t) * t * (remReg τ t) ≤ τ := by
  have hs : 0 < t + τ := add_pos_of_nonneg_of_pos ht hτ
  have he : remReg τ t = τ / (t + τ) := by
    dsimp only [remReg, invReg]
    rw [max_eq_left ht]
    field_simp
    ring
  rw [he]
  apply (le_of_mul_le_mul_right ?_ (sq_pos_of_pos hs))
  field_simp
  nlinarith [sq_nonneg t, mul_nonneg ht hτ.le]

omit instSize in
lemma norm_sandwich_sqrt_sq.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    (h : A) {e : A} (he : 0 ≤ e) (hh : IsSelfAdjoint h) :
    ‖h * CFC.sqrt e‖ ^ 2 = ‖h * e * h‖ := by
  rw [pow_two, ← CStarRing.norm_self_mul_star, star_mul,
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg e)).star_eq, hh.star_eq]
  congr 1
  rw [mul_assoc, ← mul_assoc (CFC.sqrt e), CFC.sqrt_mul_sqrt_self e, ← mul_assoc]

lemma norm_sandwich_le {e T : A} (he : 0 ≤ e) {C : ℝ} (hC : 0 ≤ C)
    (hle : e ≤ C • T) (h : A) (hh : IsSelfAdjoint h) :
    ‖h * CFC.sqrt e‖ ^ 2 ≤ C * ‖h * T * h‖ := by
  rw [norm_sandwich_sqrt_sq h he hh]
  have hle' := star_right_conjugate_le_conjugate hle h
  rw [hh.star_eq, mul_smul_comm, smul_mul_assoc] at hle'
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hle'
    (by simpa only [hh.star_eq] using star_right_conjugate_nonneg he h)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] using hn


lemma regularizer_estimate {e T : A} (he : 0 ≤ e) (hT : 0 ≤ T)
    {C τ : ℝ} (hC : 0 ≤ C) (hle : e ≤ C • T) (hτ : 0 < τ) :
    ‖(1 - T * cfc (invReg τ) T) * CFC.sqrt e‖ ^ 2 ≤ C * τ := by
  have hTs := IsSelfAdjoint.of_nonneg hT
  have hid : cfc (fun t : ℝ => t) T = T := cfc_id ℝ T hTs
  let h := cfc (remReg τ) T
  have hh : IsSelfAdjoint h := cfc_predicate (remReg τ) T
  have heq : h = 1 - T * cfc (invReg τ) T := by
    change cfc (fun t : ℝ => 1 - t * invReg τ t) T = _
    rw [cfc_sub (fun _ : ℝ => 1) (fun t : ℝ => t * invReg τ t) T
      continuous_const.continuousOn (continuous_id.mul (invReg_cont hτ)).continuousOn,
      cfc_const _ _ hTs, map_one,
      cfc_mul (fun t : ℝ => t) (invReg τ) T continuous_id.continuousOn (invReg_cont hτ).continuousOn,
      hid]
  rw [← heq]
  apply (norm_sandwich_le he hC hle h hh).trans
  apply mul_le_mul_of_nonneg_left _ hC
  have hc : h * T * h = cfc (fun t : ℝ => remReg τ t * t * remReg τ t) T := by
    rw [cfc_mul (fun t : ℝ => remReg τ t * t) (remReg τ) T
      ((remReg_cont hτ).mul continuous_id).continuousOn (remReg_cont hτ).continuousOn,
      cfc_mul (remReg τ) (fun t : ℝ => t) T (remReg_cont hτ).continuousOn continuous_id.continuousOn, hid]
  rw [hc]
  apply norm_cfc_le hτ.le
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg hT ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (remReg_nonneg hτ ht0) ht0)
    (remReg_nonneg hτ ht0))]
  exact remReg_bound hτ ht0

end

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma sqrt_mem_right_range {e T : A} (he : 0 ≤ e) (hT : 0 ≤ T)
    {C : ℝ} (hC : 0 ≤ C) (hle : e ≤ C • T) :
    CFC.sqrt e ∈ ClosedRightRange.space T := by
  change CFC.sqrt e ∈ closure (Set.range (fun x : A => T * x))
  rw [Metric.mem_closure_iff]
  intro ε hε
  let τ := ε ^ 2 / (C + 1)
  have hτ : 0 < τ := div_pos (sq_pos_of_pos hε) (by linarith)
  refine ⟨T * (cfc (invReg τ) T * CFC.sqrt e), ⟨_, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  have heq : CFC.sqrt e - T * (cfc (invReg τ) T * CFC.sqrt e) =
      (1 - T * cfc (invReg τ) T) * CFC.sqrt e := by noncomm_ring
  rw [heq]
  have hn := regularizer_estimate he hT hC hle hτ
  have ht : C * τ < ε ^ 2 := by
    dsimp only [τ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by linarith : 0 < C+1)).mpr
    nlinarith [sq_pos_of_pos hε]
  nlinarith [norm_nonneg ((1 - T * cfc (invReg τ) T) * CFC.sqrt e)]

lemma sqrt_mem_self (e : A) (he : 0 ≤ e) : CFC.sqrt e ∈ ClosedRightRange.space e :=
  sqrt_mem_right_range he he (by norm_num : (0:ℝ) ≤ 1) (by simp)

lemma sqrt_right_range_eq (e : A) (he : 0 ≤ e) :
    ClosedRightRange.space (CFC.sqrt e) = ClosedRightRange.space e := by
  apply le_antisymm
  · exact ClosedRightRange.space_le (sqrt_mem_self e he)
  · have hh := ClosedRightRange.space_mul_le (CFC.sqrt e) (CFC.sqrt e)
    rwa [CFC.sqrt_mul_sqrt_self e he] at hh


lemma exists_factor {e y : A} (he : 0 ≤ e) {C : ℝ} (hC : 0 ≤ C)
    (hle : e ≤ C • (star y * y)) :
    ∃ z : A, star z * z = e ∧ z ∈ ClosedRightRange.space y := by
  let a := CFC.sqrt (star y * y)
  have ha : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have haa : star a * a = star y * y := by
    rw [ha.star_eq]
    exact CFC.sqrt_mul_sqrt_self _
  have hmem : CFC.sqrt e ∈ ClosedRightRange.space a := by
    rw [sqrt_right_range_eq _ (star_mul_self_nonneg y)]
    exact sqrt_mem_right_range he (star_mul_self_nonneg y) hC hle
  let x : ClosedRightRange.space a := ⟨CFC.sqrt e, hmem⟩
  refine ⟨ClosedRightRange.transport a y x, ?_, ClosedRightRange.transport_mem haa x⟩
  rw [ClosedRightRange.transport_inner haa]
  change star (CFC.sqrt e) * CFC.sqrt e = e
  rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg e)).star_eq, CFC.sqrt_mul_sqrt_self e he]

end Domination


section
variable {A : Type*} [CStarAlgebra A]


namespace CuntzBelow
omit instSize in
lemma approx.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {a b : A} (h : CuntzBelow a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : A, ‖a - star x * b * x‖ < ε := by
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.mp h ε hε
  exact ⟨x, by simpa only [dist_eq_norm] using hx⟩

end CuntzBelow
end

end KirchbergRordam.GenericRW

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_ConePauli
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
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n


variable [instPauliData : KirchbergRordam.GenericRW.PauliData]
namespace KirchbergRordam.GenericRW.Pauli
open scoped Matrix BigOperators Kronecker
lemma e_star (i : Label) : star (e i)=e i := PauliData.e_star i
lemma e_square (i : Label) : e i*e i=1 := PauliData.e_square i
lemma trace_mul (i j : Label) : Matrix.trace (e i*e j)=if i=j then (rankNum:ℂ) else 0 :=
  PauliData.trace_mul i j
end KirchbergRordam.GenericRW.Pauli

namespace KirchbergRordam.GenericRW.PauliPower
open scoped Matrix BigOperators Kronecker

instance labelFintype : (n : ℕ) → Fintype (Label n)
  | 0 => inferInstanceAs (Fintype (Pauli.Label))
  | n+1 => letI := labelFintype n; inferInstanceAs (Fintype (Pauli.Label × Label n))
instance labelDecidableEq : (n : ℕ) → DecidableEq (Label n)
  | 0 => inferInstanceAs (DecidableEq (Pauli.Label))
  | n+1 => letI := labelDecidableEq n; inferInstanceAs (DecidableEq (Pauli.Label × Label n))

omit instSize instPauliData in
lemma row_card
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (n : ℕ) : Fintype.card (Row n)=rankNum^(n+1) := by
  induction n with
  | zero =>
    change Fintype.card (Fin rankNum) = rankNum ^ (0 + 1)
    simp
  | succ n ih =>
    change Fintype.card (Fin rankNum × Row n)=_
    simp only [Fintype.card_prod,Fintype.card_fin,ih,pow_succ]
    ring
lemma label_card (n : ℕ) : Fintype.card (Label n)=(rankNum*rankNum)^(n+1) := by
  induction n with
  | zero =>
    change Fintype.card PauliData.Label = (rankNum * rankNum) ^ (0 + 1)
    simpa only [Nat.zero_add, pow_one] using PauliData.card
  | succ n ih =>
    change Fintype.card (Pauli.Label × Label n)=_
    simp only [Fintype.card_prod,PauliData.card,ih,pow_succ]
    ring

lemma e_star (n : ℕ) (a : Label n) : star (e n a)=e n a := by
  induction n with
  | zero => exact Pauli.e_star a
  | succ n ih =>
    change (Matrix.kronecker (Pauli.e a.1) (e n a.2)).conjTranspose=_
    dsimp only [Matrix.kronecker]
    rw [Matrix.conjTranspose_kronecker]
    change Matrix.kronecker (star (Pauli.e a.1)) (star (e n a.2))=_
    rw [Pauli.e_star,ih]
    rfl

lemma e_square (n : ℕ) (a : Label n) : e n a*e n a=1 := by
  induction n with
  | zero => exact Pauli.e_square a
  | succ n ih =>
    change Matrix.kronecker (Pauli.e a.1) (e n a.2)*Matrix.kronecker (Pauli.e a.1) (e n a.2)=_
    dsimp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul,Pauli.e_square,ih,Matrix.one_kronecker_one]
    rfl

lemma trace_mul (n : ℕ) (a b : Label n) :
    Matrix.trace (e n a*e n b)=if a=b then (rankNum:ℂ)^(n+1) else 0 := by
  induction n with
  | zero =>
    change Matrix.trace (Pauli.e a * Pauli.e b) =
      if (a : Pauli.Label) = b then (rankNum : ℂ) ^ (0 + 1) else 0
    split_ifs with hab
    · have hab' : (a : Pauli.Label) = b := hab
      simpa only [Nat.zero_add, pow_one] using
        (Pauli.trace_mul a b).trans (ite_eq_left hab')
    · have hab' : (a : Pauli.Label) ≠ b := hab
      exact (Pauli.trace_mul a b).trans (ite_eq_right hab')
  | succ n ih =>
    change Matrix.trace (Matrix.kronecker (Pauli.e a.1) (e n a.2)*
      Matrix.kronecker (Pauli.e b.1) (e n b.2))=_
    dsimp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul,Matrix.trace_kronecker,Pauli.trace_mul,ih]
    have hab : a=b ↔ a.1=b.1 ∧ a.2=b.2 := Prod.ext_iff
    by_cases h1 : a.1=b.1 <;> by_cases h2 : a.2=b.2 <;>
      simp [h1,h2,hab,pow_succ,mul_comm]

lemma coeff_e (n : ℕ) (a b : Label n) : coeff n a (e n b)=if a=b then 1 else 0 := by
  rw [coeff_apply,trace_mul]
  split_ifs <;> simp

lemma independent (n : ℕ) : LinearIndependent ℂ (e n) := by
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  have h := congrArg (coeff n i) hf
  simpa [map_sum,map_smul,coeff_e] using h

def basis (n : ℕ) : Module.Basis (Label n) ℂ (Mat n) :=
  basisOfLinearIndependentOfCardEqFinrank' (e n) (independent n) (by
    simp only [Mat,Module.finrank_matrix,label_card,row_card,Module.finrank_self,mul_one]
    rw [← mul_pow])

lemma basis_apply (n : ℕ) (a : Label n) : basis n a=e n a := by simp [basis]
lemma coeff_sum (n : ℕ) (x : Mat n) : ∑ a,coeff n a x • e n a=x := by
  have he (a : Label n) : (basis n).repr x a=coeff n a x := by
    have h := congrArg (coeff n a) ((basis n).sum_repr x)
    simpa [map_sum,map_smul,basis_apply,coeff_e] using h
  simpa only [he,basis_apply] using (basis n).sum_repr x

def ce (n : ℕ) (a : Label n) : CMat n := CStarMatrix.ofMatrix (e n a)
lemma ccoeff_ce (n : ℕ) (a b : Label n) : ccoeff n a (ce n b)=if a=b then 1 else 0 :=
  coeff_e n a b
lemma ccoeff_sum (n : ℕ) (x : CMat n) : ∑ a,ccoeff n a x • ce n a=x := by
  exact congrArg CStarMatrix.ofMatrix (coeff_sum n (CStarMatrix.ofMatrix.symm x))
lemma ce_star (n : ℕ) (a : Label n) : star (ce n a)=ce n a :=
  congrArg CStarMatrix.ofMatrix (e_star n a)
lemma ce_square (n : ℕ) (a : Label n) : ce n a*ce n a=1 :=
  congrArg CStarMatrix.ofMatrix (e_square n a)
end KirchbergRordam.GenericRW.PauliPower

namespace KirchbergRordam.GenericRW.ConePauli
open Topology
open scoped CStarAlgebra BigOperators
open ConeModel
abbrev E (i : Pauli.Label) : M2 := PauliPower.ce 0 i
lemma E_zero : E (0:Pauli.Label)=1 := congrArg CStarMatrix.ofMatrix Pauli.e_zero
def p (i : Pauli.Label) : C(unitInterval,ℂ) := if i=0 then 1 else ⟨fun t => ((t:ℝ):ℂ), by fun_prop⟩
def u (i : Pauli.Label) : Cone := ⟨⟨fun t => p i t • E i,(p i).continuous.smul continuous_const⟩,by
  change p i 0 • E i ∈ (⊥ : StarSubalgebra ℂ M2)
  by_cases hi : i=0
  · subst i
    simp only [p, E_zero]
    change (1:ℂ) • (1:M2)∈(⊥ : StarSubalgebra ℂ M2)
    simpa only [one_smul] using (one_mem (⊥ : StarSubalgebra ℂ M2))
  · simp only [p,ite_eq_right hi,ContinuousMap.coe_mk,Set.Icc.coe_zero,Complex.ofReal_zero,zero_smul]
    exact zero_mem _⟩
omit instSize instPauliData in
lemma scalar_commute
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (f : C(unitInterval,ℂ)) (a : Cone) : Commute (scalar f) a := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  exact Algebra.commutes (f t) ((a:C(unitInterval,M2)) t)
lemma u_gram (i : Pauli.Label) : star (u i)*u i=scalar (star (p i)*p i) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change star (p i t • E i)*(p i t • E i)=algebraMap ℂ M2 (star (p i t)*p i t)
  have hstar : star (E i) = E i := PauliPower.ce_star 0 i
  have hsquare : E i * E i = 1 := PauliPower.ce_square 0 i
  rw [star_smul,smul_mul_smul_comm,hstar,hsquare]
  exact (Algebra.algebraMap_eq_smul_one _).symm

def sectionMap (i : Pauli.Label) : C(unitInterval,ℂ) →L[ℂ] C(unitInterval,M2) :=
  (ContinuousLinearMap.toSpanSingleton ℂ (E i)).compLeftContinuous ℂ unitInterval

def coeff (i : Pauli.Label) (f : Cone) : C(unitInterval,ℂ) :=
  ⟨fun t => PauliPower.ccoeff 0 i ((f:C(unitInterval,M2)) t),(PauliPower.ccoeff 0 i).continuous.comp f.val.continuous⟩
lemma coeff_zero (i : Pauli.Label) (hi : i≠0) (f : Cone) : coeff i f 0=0 := by
  obtain ⟨c,hc⟩ := f.property
  change PauliPower.ccoeff 0 i ((f:C(unitInterval,M2)) 0)=0
  change algebraMap ℂ M2 c=(f:C(unitInterval,M2)) 0 at hc
  rw [← hc]
  rw [Algebra.algebraMap_eq_smul_one]
  have hcoeff : PauliPower.ccoeff 0 i (1 : M2) = 0 := by
    calc
      _ = PauliPower.ccoeff 0 i (E (0 : Pauli.Label)) :=
        congrArg (PauliPower.ccoeff 0 i) E_zero.symm
      _ = if i = 0 then 1 else 0 := PauliPower.ccoeff_ce 0 i (0 : Pauli.Label)
      _ = 0 := ite_eq_right hi
  exact ((PauliPower.ccoeff 0 i).map_smul c (1 : M2)).trans
    ((congrArg (c • ·) hcoeff).trans (smul_zero c))
lemma reconstruct (f : Cone) : ∑ i,sectionMap i (coeff i f)=(f:C(unitInterval,M2)) := by
  apply ContinuousMap.ext
  intro t
  simp only [ContinuousMap.sum_apply]
  change ∑ i:Pauli.Label,PauliPower.ccoeff 0 i ((f:C(unitInterval,M2)) t) • E i=_
  exact PauliPower.ccoeff_sum 0 ((f:C(unitInterval,M2)) t)

def expansion : (Pauli.Label→C(unitInterval,ℂ)) →ₗ[ℂ] Cone where
  toFun f := ∑ i,scalar (f i)*u i
  map_add' f g := by simp [map_add,add_mul,Finset.sum_add_distrib]
  map_smul' c f := by simp [map_smul,Finset.smul_sum]

lemma expansion_single (i : Pauli.Label) (f : C(unitInterval,ℂ)) :
    expansion (Pi.single i f)=scalar f*u i := by
  dsimp only [expansion,LinearMap.coe_mk,AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro b _ hbi
    rw [Pi.single_eq_of_ne hbi,map_zero,zero_mul]
  · intro hi; exact (hi (Finset.mem_univ i)).elim

lemma dense : DenseRange expansion := by
  let S : Submodule ℂ Cone := (LinearMap.range expansion).topologicalClosure
  have hclosed : IsClosed (S:Set Cone) := Submodule.isClosed_topologicalClosure _
  have hbase (i : Pauli.Label) (f : C(unitInterval,ℂ)) : scalar f*u i ∈ S := by
    apply (LinearMap.range expansion).le_topologicalClosure
    exact ⟨Pi.single i f,expansion_single i f⟩
  have hsec (i : Pauli.Label) (f : C(unitInterval,ℂ)) (hf : i≠0→f 0=0) :
      ∃ a:Cone,a∈S ∧ (a:C(unitInterval,M2))=sectionMap i f := by
    have hz : ∀ t,p i t=0→f t=0 := by
      intro t ht
      by_cases hi : i=0
      · simp [p,hi] at ht
      · have ht0 : t=0 := by
          apply Subtype.ext
          change (t:ℝ)=0
          exact_mod_cast (show ((t:ℝ):ℂ)=0 by simpa [p,hi] using ht)
        rw [ht0]
        exact hf hi
    let v : Vanish.Functions {t | p i t=0} := ⟨f,fun t ht => hz t ht⟩
    have hmem (g : Vanish.Functions {t | p i t=0}) :
        sectionMap i g.val ∈ Set.range (fun a:S => (a.val:C(unitInterval,M2))) := by
      refine (Vanish.multiplier_dense (p i)).induction_on g ?_ ?_
      · have hs : IsClosedEmbedding (fun a:S => (a.val:C(unitInterval,M2))) :=
          coneClosed.isClosedEmbedding_subtypeVal.comp hclosed.isClosedEmbedding_subtypeVal
        exact hs.isClosed_range.preimage ((sectionMap i).continuous.comp continuous_subtype_val)
      · intro f
        refine ⟨⟨scalar f*u i,hbase i f⟩,?_⟩
        apply ContinuousMap.ext
        intro t
        change algebraMap ℂ M2 (f t)*(p i t • E i)=(p i t*f t) • E i
        rw [Algebra.algebraMap_eq_smul_one,smul_mul_smul_comm,one_mul,mul_comm]
    obtain ⟨a,ha⟩ := hmem v
    exact ⟨a.val,a.property,ha⟩
  have hall (f : Cone) : f∈S := by
    have h (i : Pauli.Label) := hsec i (coeff i f) (fun hi => coeff_zero i hi f)
    choose a ha he using h
    have hf : ∑ i,a i=f := by
      apply Subtype.ext
      change coneSubalgebra.subtype (∑ i,a i)=_
      rw [map_sum]
      change ∑ i,(a i:C(unitInterval,M2))=(f:C(unitInterval,M2))
      simp_rw [he]
      exact reconstruct f
    rw [← hf]
    exact Submodule.sum_mem S (fun i _ => ha i)
  intro f
  exact hall f
end KirchbergRordam.GenericRW.ConePauli

namespace KirchbergRordam.GenericRW.MatrixTensor
open scoped Matrix Kronecker
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]


omit instSize instPauliData in
lemma algebra_legs_commute.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    {κ : Type contextLevel2}
    [Fintype ι]
    [Fintype κ]
    [DecidableEq ι]
    [DecidableEq κ]
    (a : Matrix ι ι ℂ) (b : Matrix κ κ ℂ) :
    Commute (leftMatrixAlgebra (κ:=κ) a) (rightMatrixAlgebra (ι:=ι) b) := by
  change Matrix.kronecker a 1 * Matrix.kronecker 1 b = Matrix.kronecker 1 b * Matrix.kronecker a 1
  dsimp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul]
  simp

lemma legs_commute (a : Mat ι) (b : Mat κ) :
    Commute (leftMatrix (κ:=κ) a) (rightMatrix (ι:=ι) b) :=
  (algebra_legs_commute (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b)).map
    CStarMatrix.ofMatrixStarAlgEquiv

omit instSize instPauliData in
lemma algebra_legs_product.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    {κ : Type contextLevel2}
    [Fintype ι]
    [Fintype κ]
    [DecidableEq ι]
    [DecidableEq κ]
    (a : Matrix ι ι ℂ) (b : Matrix κ κ ℂ) :
    leftMatrixAlgebra (κ:=κ) a*rightMatrixAlgebra (ι:=ι) b=Matrix.kronecker a b := by
  change Matrix.kronecker a 1 * Matrix.kronecker 1 b = Matrix.kronecker a b
  dsimp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul]
  simp

lemma legs_product (a : Mat ι) (b : Mat κ) :
    leftMatrix (κ:=κ) a*rightMatrix (ι:=ι) b=CStarMatrix.ofMatrix (Matrix.kronecker a b) := by
  exact congrArg CStarMatrix.ofMatrix
    (algebra_legs_product (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b))
end KirchbergRordam.GenericRW.MatrixTensor
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_CubeCalculus
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


namespace KirchbergRordam.GenericRW.CubeCalculus
open scoped CStarAlgebra
variable {I A : Type*} [CStarAlgebra A]
omit instSize instPauliData in
lemma ext_coord.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {I : Type contextLevel1}
    {A : Type contextLevel2}
    [CStarAlgebra A]
    (φ ψ : C(I→unitInterval,ℂ) →⋆ₐ[ℂ] A)
    (h : ∀ i,φ (coord i)=ψ (coord i)) : φ=ψ := by
  let S : StarSubalgebra ℂ C(I→unitInterval,ℂ) := StarAlgHom.equalizer φ ψ
  have hc : IsClosed (S : Set C(I→unitInterval,ℂ)) := isClosed_eq (map_continuous φ) (map_continuous ψ)
  have hs : S.SeparatesPoints := by
    intro x y hxy
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
    refine ⟨coord i,⟨coord i,h i,rfl⟩,?_⟩
    intro he
    apply hi
    apply Subtype.ext
    change ((x i:ℝ):ℂ)=((y i:ℝ):ℂ) at he
    exact_mod_cast he
  have ht : S=⊤ := by
    rw [← le_antisymm (StarSubalgebra.topologicalClosure_minimal le_rfl hc) S.le_topologicalClosure]
    exact ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hs
  apply StarAlgHom.ext
  intro f
  exact show f∈S from ht ▸ trivial
end KirchbergRordam.GenericRW.CubeCalculus


namespace KirchbergRordam.GenericRW.CubeFrame
open scoped BigOperators CStarAlgebra
variable {X B T I : Type*} [TopologicalSpace X] [CompactSpace X]
variable [CStarAlgebra B] [CStarAlgebra T] [Fintype I] [DecidableEq I]
variable (κ : C(X,ℂ) →⋆ₐ[ℂ] B) (ρ : B →⋆ₐ[ℂ] C(X,T))
variable (p : I→C(X,ℂ)) (u : I→B) (e : I→T)
variable (hc : ∀ f a,Commute (κ f) a)
variable (hu : ∀ i,star (u i)*u i=κ (star (p i)*p i))

omit hc hu in
omit [Fintype I] [DecidableEq I] in
omit instSize instPauliData in
lemma term_norm.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {X : Type contextLevel1}
    {B : Type contextLevel2}
    {I : Type contextLevel3}
    [TopologicalSpace X]
    [CompactSpace X]
    [CStarAlgebra B]
    (κ : C(X, ℂ) →⋆ₐ[ℂ] B)
    (p : I → C(X, ℂ))
    (u : I → B)
    (hc : ∀ (f : C(X, ℂ)) (a : B), Commute (κ f) a)
    (hu : ∀ (i : I), Star.star (u i) * u i = κ (Star.star (p i) * p i))
    (f : C(X,ℂ)) (i : I) : ‖κ f*u i‖≤‖f*p i‖ := by
  have he : star (κ f*u i)*(κ f*u i)=κ (star (f*p i)*(f*p i)) := by
    rw [star_mul,← map_star,mul_assoc,← mul_assoc (κ (star f)),← map_mul]
    rw [← mul_assoc,← (hc (star f*f) (star (u i))).eq,mul_assoc,hu,← map_mul]
    congr 1
    simp only [star_mul]
    ring
  have hn : ‖κ f*u i‖*‖κ f*u i‖≤‖f*p i‖*‖f*p i‖ := by
    rw [← CStarRing.norm_star_mul_self,he,← CStarRing.norm_star_mul_self]
    exact NonUnitalStarAlgHom.norm_apply_le κ _
  nlinarith [norm_nonneg (κ f*u i),norm_nonneg (f*p i)]

variable (hκ : ∀ f t,ρ (κ f) t=algebraMap ℂ T (f t))
variable (hρ : ∀ i t,ρ (u i) t=p i t • e i)
variable (ℓ : I→T →L[ℂ] ℂ) (hℓ : ∀ i j,ℓ i (e j)=if i=j then 1 else 0)

omit hκ hρ hℓ in
omit [CompactSpace X] in
omit instSize instPauliData in
lemma coefficient.{contextLevel1, contextLevel2, contextLevel3, contextLevel4}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {X : Type contextLevel1}
    {B : Type contextLevel2}
    {T : Type contextLevel3}
    {I : Type contextLevel4}
    [TopologicalSpace X]
    [CStarAlgebra B]
    [CStarAlgebra T]
    [Fintype I]
    [DecidableEq I]
    (κ : C(X, ℂ) →⋆ₐ[ℂ] B)
    (ρ : B →⋆ₐ[ℂ] C(X, T))
    (p : I → C(X, ℂ))
    (u : I → B)
    (e : I → T)
    (hκ : ∀ (f : C(X, ℂ)) (t : X), (ρ (κ f)) t = (Algebra.algebraMap ℂ T) (f t))
    (hρ : ∀ (i : I) (t : X), (ρ (u i)) t = (p i) t • e i)
    (ℓ : I → T →L[ℂ] ℂ)
    (hℓ : ∀ (i j : I), (ℓ i) (e j) = if i = j then 1 else 0)
    (f : I→C(X,ℂ)) (i : I) (t : X) :
    ℓ i (ρ (expansion κ u f) t)= (f i*p i) t := by
  simp only [expansion,map_sum,ContinuousMap.sum_apply,map_mul,ContinuousMap.mul_apply,hκ,hρ,
    Algebra.algebraMap_eq_smul_one,smul_mul_smul_comm,one_mul,map_smul,hℓ]
  simp

include hc hu hκ hρ hℓ in
lemma expansion_norm (f : I→C(X,ℂ)) :
    ‖expansion κ u f‖≤(∑ i,‖ℓ i‖)*‖ρ (expansion κ u f)‖ := by
  apply (norm_sum_le _ _).trans
  calc
    ∑ i,‖κ (f i)*u i‖ ≤ ∑ i,‖f i*p i‖ := Finset.sum_le_sum fun i _ => term_norm κ p u hc hu _ i
    _ ≤ ∑ i,‖ℓ i‖*‖ρ (expansion κ u f)‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      intro t
      rw [← coefficient κ ρ p u e hκ hρ ℓ hℓ f i t]
      exact ((ℓ i).le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (ContinuousMap.norm_coe_le_norm _ t) (norm_nonneg _))
    _ = _ := (Finset.sum_mul ..).symm

include hc hu hκ hρ hℓ in


theorem faithful (hd : DenseRange (expansion κ u)) : Function.Injective ρ := by
  have hb (x : B) : ‖x‖≤(∑ i,‖ℓ i‖)*‖ρ x‖ := by
    apply hd.induction_on (p:=fun x => ‖x‖≤(∑ i,‖ℓ i‖)*‖ρ x‖) x
    · exact isClosed_le continuous_norm (continuous_const.mul (map_continuous ρ).norm)
    · exact expansion_norm κ ρ p u e hc hu hκ hρ ℓ hℓ
  intro x y hxy
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have hz : ρ (x-y)=0 := by rw [map_sub,hxy,sub_self]
  simpa only [hz,norm_zero,mul_zero] using hb (x-y)

include hc hu hκ hρ hℓ in
lemma closed_range (hd : DenseRange (expansion κ u)) : IsClosed (Set.range ρ) :=
  (NonUnitalStarAlgHom.isometry ρ (faithful κ ρ p u e hc hu hκ hρ ℓ hℓ hd)).isClosedEmbedding.isClosed_range
end KirchbergRordam.GenericRW.CubeFrame

namespace KirchbergRordam.GenericRW.CubeFrame
open scoped BigOperators
variable {X B T I : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable [CStarAlgebra B] [CStarAlgebra T] [Fintype I] [DecidableEq I]

omit [CompactSpace X] [T2Space X] in
omit instSize instPauliData in
lemma scalarSection_continuous.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {X : Type contextLevel1}
    {T : Type contextLevel2}
    [TopologicalSpace X]
    [CStarAlgebra T]
    (a : T) : Continuous (scalarSection (X:=X) a) := by
  let g : C(ℂ,T) := ⟨fun c => c • a,by fun_prop⟩
  exact g.continuous_postcomp

variable (κ : C(X,ℂ) →⋆ₐ[ℂ] B) (ρ : B →⋆ₐ[ℂ] C(X,T))
variable (p : I→C(X,ℂ)) (u : I→B) (e : I→T)
variable (hκ : ∀ f t,ρ (κ f) t=algebraMap ℂ T (f t))
variable (hρ : ∀ i t,ρ (u i) t=p i t • e i)
include hκ hρ in
omit [Fintype I] [DecidableEq I] in


lemma coefficient_mem_range (hclosed : IsClosed (Set.range ρ)) (i : I)
    (f : C(X,ℂ)) (hf : ∀ t,p i t=0 → f t=0) :
    scalarSection (e i) f ∈ Set.range ρ := by
  let f' : Vanish.Functions {t | p i t=0} := ⟨f,hf⟩
  have h (g : Vanish.Functions {t | p i t=0}) :
      scalarSection (e i) g.val ∈ Set.range ρ := by
    refine (Vanish.multiplier_dense (p i)).induction_on g
      (hclosed.preimage ((scalarSection_continuous (e i)).comp continuous_subtype_val)) ?_
    intro a
    refine ⟨κ a*u i,?_⟩
    ext t
    simp only [map_mul,ContinuousMap.mul_apply,hκ,hρ,
      Algebra.algebraMap_eq_smul_one,smul_mul_smul_comm,one_mul]
    change (a t*p i t) • e i = (p i t*a t) • e i
    rw [mul_comm]
  exact h f'

variable (ℓ : I→T →L[ℂ] ℂ)
variable (hspan : ∀ a : T,∑ i,ℓ i a • e i=a)
include hκ hρ hspan in
omit [DecidableEq I] in


theorem section_mem_range (hclosed : IsClosed (Set.range ρ)) (f : C(X,T))
    (hf : ∀ i t,p i t=0 → ℓ i (f t)=0) : f∈Set.range ρ := by
  let c (i : I) : C(X,ℂ) := ⟨fun t => ℓ i (f t),(ℓ i).continuous.comp f.continuous⟩
  have hm (i : I) : scalarSection (e i) (c i) ∈ Set.range ρ :=
    coefficient_mem_range κ ρ p u e hκ hρ hclosed i (c i) (hf i)
  have hs : ∑ i,scalarSection (e i) (c i)=f := by
    ext t
    simp only [ContinuousMap.sum_apply]
    exact hspan (f t)
  rw [← hs]
  change (∑ i,scalarSection (e i) (c i)) ∈ ρ.range
  exact sum_mem fun i _ => hm i

variable (hc : ∀ f a,Commute (κ f) a)
variable (hu : ∀ i,star (u i)*u i=κ (star (p i)*p i))
variable (hℓ : ∀ i j,ℓ i (e j)=if i=j then 1 else 0)
include hc hu hκ hρ hℓ hspan in


theorem exists_unique_lift (hd : DenseRange (expansion κ u)) (f : C(X,T))
    (hf : ∀ i t,p i t=0 → ℓ i (f t)=0) :
    ∃! b : B,ρ b=f ∧ ‖b‖=‖f‖ := by
  have hi := faithful κ ρ p u e hc hu hκ hρ ℓ hℓ hd
  obtain ⟨b,hb⟩ := section_mem_range κ ρ p u e hκ hρ ℓ hspan
    (closed_range κ ρ p u e hc hu hκ hρ ℓ hℓ hd) f hf
  refine ⟨b,⟨hb,?_⟩,?_⟩
  · rw [← hb]
    simpa only [map_zero,dist_zero_right] using
      ((NonUnitalStarAlgHom.isometry ρ hi).dist_eq b 0).symm
  · intro a ha
    exact hi (ha.1.trans hb.symm)
end KirchbergRordam.GenericRW.CubeFrame
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_ConeCube
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


namespace KirchbergRordam.GenericRW.ConeCube
open scoped CStarAlgebra BigOperators ComplexOrder
open ConeModel _root_.OAI.KirchbergRordam.GenericRW.MaxTensor
abbrev Tensor (n : ℕ) := powerPack Cone n

def first (n : ℕ) : C(Cube n,unitInterval) := ⟨fun t=>t 0,continuous_apply 0⟩
def tail (n : ℕ) : C(Cube (n+1),Cube n) := ⟨fun t i=>t i.succ,by fun_prop⟩

def repr : (n : ℕ)→Tensor n→⋆ₐ[ℂ] C(Cube n,Fiber n)
  | 0 => ((first 0).compStarAlgHom' ℂ M2).comp coneSubalgebra.subtype
  | n+1 =>
    let l := (post (MatrixTensor.leftMatrix (κ:=PauliPower.Row n))).comp
      (((first (n+1)).compStarAlgHom' ℂ M2).comp coneSubalgebra.subtype)
    let r := (post (MatrixTensor.rightMatrix (ι:=Fin Size.n))).comp
      (((tail n).compStarAlgHom' ℂ (Fiber n)).comp (repr n))
    lift l r (by intro a b; apply ContinuousMap.ext; intro t; exact (MatrixTensor.legs_commute _ _).eq)

lemma repr_left (n : ℕ) (a : Cone) (t : Cube (n+1)) :
    repr (n+1) (includeLeft a) t=MatrixTensor.leftMatrix (κ:=PauliPower.Row n) ((a:C(unitInterval,M2)) (t 0)) := by
  exact DFunLike.congr_fun (DFunLike.congr_fun (lift_includeLeft _ _ _) a) t
lemma repr_right (n : ℕ) (b : Tensor n) (t : Cube (n+1)) :
    repr (n+1) (includeRight b) t=MatrixTensor.rightMatrix (ι:=Fin Size.n) (repr n b (tail n t)) := by
  exact DFunLike.congr_fun (DFunLike.congr_fun (lift_includeRight _ _ _) b) t
lemma repr_leg (n : ℕ) (i : Fin (n+1)) (a : Cone) (t : Cube n) :
    repr n (leg Cone n i a) t=matLeg n i ((a:C(unitInterval,M2)) (t i)) := by
  induction n with
  | zero =>
    change (a:C(unitInterval,M2)) (t 0)=(a:C(unitInterval,M2)) (t i)
    rw [Fin.eq_zero i]
  | succ n ih =>
    induction i using Fin.cases with
    | zero => exact repr_left n a t
    | succ i =>
      change repr (n+1) (includeRight (leg Cone n i a)) t=_
      rw [repr_right,ih]
      rfl

lemma scalar_leg_commute (n : ℕ) (i : Fin (n+1)) (f : C(unitInterval,ℂ)) (a : Tensor n) :
    Commute (leg Cone n i (scalar f)) a := by
  apply commute_of_power_legs n (StarAlgHom.id ℂ (Tensor n)) _ _ a
  intro j b
  change Commute (leg Cone n i (scalar f)) (leg Cone n j b)
  by_cases hij : i=j
  · subst j; exact (ConePauli.scalar_commute f b).map (leg Cone n i)
  · exact commute_legs Cone n i j hij (scalar f) b

def scalarLeg (n : ℕ) (i : Fin (n+1)) : C(unitInterval,ℂ)→⋆ₐ[ℂ] Tensor n :=
  (leg Cone n i).comp scalar
def κ (n : ℕ) : C(Cube n,ℂ)→⋆ₐ[ℂ] Tensor n :=
  CentralCalculus.hom (scalarLeg n) (scalar_leg_commute n)
lemma κ_commute (n : ℕ) (f : C(Cube n,ℂ)) (a : Tensor n) : Commute (κ n f) a :=
  CentralCalculus.hom_commute _ _ f a
lemma κ_coordinate (n : ℕ) (i : Fin (n+1)) (f : C(unitInterval,ℂ)) :
    κ n (JointCalculus.coordinate i f)=leg Cone n i (scalar f) :=
  CentralCalculus.hom_coordinate _ _ i f

lemma repr_κ (n : ℕ) (f : C(Cube n,ℂ)) (t : Cube n) :
    repr n (κ n f) t=algebraMap ℂ (Fiber n) (f t) := by
  let φ := ((point t).comp (repr n)).comp (κ n)
  let ψ := (StarAlgHom.ofId ℂ (Fiber n)).comp (point (A:=ℂ) t)
  have he : φ=ψ := by
    apply CubeCalculus.ext_coord
    intro i
    change repr n (κ n (JointCalculus.coordinate i
      ⟨fun s:unitInterval=>((s:ℝ):ℂ),by fun_prop⟩)) t=_
    rw [κ_coordinate,repr_leg,scalar_apply]
    exact (matLeg n i).commutes _
  exact DFunLike.congr_fun he f

lemma κ_first (n : ℕ) (f : C(unitInterval,ℂ)) :
    κ (n+1) (f.comp (first (n+1)))=includeLeft (scalar f) := κ_coordinate (n+1) 0 f
lemma κ_tail (n : ℕ) (f : C(Cube n,ℂ)) :
    κ (n+1) (f.comp (tail n))=includeRight (κ n f) := by
  let φ := (κ (n+1)).comp ((tail n).compStarAlgHom' ℂ ℂ)
  let ψ := (includeRight (A:=Cone)).comp (κ n)
  have he : φ=ψ := by
    apply CubeCalculus.ext_coord
    intro i
    change κ (n+1) (JointCalculus.coordinate i.succ
      ⟨fun s:unitInterval=>((s:ℝ):ℂ),by fun_prop⟩)=
      includeRight (κ n (JointCalculus.coordinate i
      ⟨fun s:unitInterval=>((s:ℝ):ℂ),by fun_prop⟩))
    rw [κ_coordinate,κ_coordinate]
    rfl
  exact DFunLike.congr_fun he f

def p : (n : ℕ)→Label n→C(Cube n,ℂ)
  | 0,a => (ConePauli.p a).comp (first 0)
  | n+1,a => ((ConePauli.p a.1).comp (first (n+1)))*((p n a.2).comp (tail n))
def u : (n : ℕ)→Label n→Tensor n
  | 0,a => ConePauli.u a
  | n+1,a => includeLeft (ConePauli.u a.1)*includeRight (u n a.2)

omit instSize instPauliData in
lemma commuting_gram
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A B E : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [CStarAlgebra E] (φ : A→⋆ₐ[ℂ] E) (ψ : B→⋆ₐ[ℂ] E)
    (hc : ∀ a b, Commute (φ a) (ψ b)) (x:A) (y:B) :
    star (φ x*ψ y)*(φ x*ψ y)=φ (star x*x)*ψ (star y*y) := by
  rw [star_mul,← map_star ψ y,← map_star φ x]
  calc
    ψ (star y)*φ (star x)*(φ x*ψ y)=ψ (star y)*φ (star x*x)*ψ y := by
      rw [map_mul]; noncomm_ring
    _ = _ := by rw [← (hc (star x*x) (star y)).eq,mul_assoc,← map_mul]
lemma gram_product {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] (x:A) (y:B) :
    star (includeLeft (B:=B) x*includeRight (A:=A) y)*(includeLeft (B:=B) x*includeRight (A:=A) y)=
      includeLeft (B:=B) (star x*x)*includeRight (A:=A) (star y*y) :=
  commuting_gram includeLeft includeRight legs_commute x y

lemma u_gram (n : ℕ) (a : Label n) : star (u n a)*u n a=κ n (star (p n a)*p n a) := by
  induction n with
  | zero =>
    rw [show star (p 0 a)*p 0 a=JointCalculus.coordinate (0:Fin 1)
      (star (ConePauli.p a)*ConePauli.p a) from rfl,κ_coordinate]
    exact ConePauli.u_gram a
  | succ n ih =>
    have hp : star (p (n+1) a)*p (n+1) a=
        (star (ConePauli.p a.1)*ConePauli.p a.1).comp (first (n+1))*
          (star (p n a.2)*p n a.2).comp (tail n) := by
      apply ContinuousMap.ext; intro t
      simp only [p,ContinuousMap.mul_apply,ContinuousMap.star_apply,ContinuousMap.comp_apply,star_mul]
      ring
    rw [hp,map_mul,κ_first,κ_tail]
    exact (gram_product (ConePauli.u a.1) (u n a.2)).trans
      (congrArg₂ (fun x y => includeLeft (B := Tensor n) x * includeRight (A := Cone) y)
        (ConePauli.u_gram a.1) (ih a.2))

lemma ce_product (n : ℕ) (a : Label (n+1)) :
    MatrixTensor.leftMatrix (κ:=PauliPower.Row n) (ConePauli.E a.1)*MatrixTensor.rightMatrix (ι:=Fin Size.n) (PauliPower.ce n a.2)=
      PauliPower.ce (n+1) a := MatrixTensor.legs_product _ _
lemma repr_u (n : ℕ) (a : Label n) (t : Cube n) :
    repr n (u n a) t=p n a t • PauliPower.ce n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let ρ : MaxTensor.Algebra Cone (Tensor n)→⋆ₐ[ℂ] C(Cube (n+1),Fiber (n+1)) := repr (n+1)
    change ρ (includeLeft (ConePauli.u a.1)*includeRight (u n a.2)) t=_
    rw [map_mul]
    change (repr (n+1) (includeLeft (ConePauli.u a.1))*
      repr (n+1) (includeRight (u n a.2))) t=_
    rw [ContinuousMap.mul_apply,repr_left,repr_right,ih]
    change MatrixTensor.leftMatrix (κ:=PauliPower.Row n) (ConePauli.p a.1 (t 0) • ConePauli.E a.1)*
      MatrixTensor.rightMatrix (ι:=Fin Size.n) (p n a.2 (tail n t) • PauliPower.ce n a.2)=_
    rw [map_smul,map_smul,smul_mul_smul_comm,ce_product]
    rfl

def expansion (n : ℕ) : (Label n→C(Cube n,ℂ))→ₗ[ℂ] Tensor n where
  toFun f := ∑ i,κ n (f i)*u n i
  map_add' f g := by simp [map_add,add_mul,Finset.sum_add_distrib]
  map_smul' c f := by simp [map_smul,Finset.smul_sum]

lemma expansion_zero (f : Pauli.Label→C(unitInterval,ℂ)) :
    expansion 0 (fun i => (f i).comp (first 0))=ConePauli.expansion f := by
  dsimp only [expansion,ConePauli.expansion,LinearMap.coe_mk,AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (·*ConePauli.u i) (κ_coordinate 0 (0:Fin 1) (f i))

lemma expansion_product (n : ℕ) (f : Pauli.Label→C(unitInterval,ℂ)) (g : Label n→C(Cube n,ℂ)) :
    includeLeft (ConePauli.expansion f)*includeRight (expansion n g)=
      expansion (n+1) (fun a => (f a.1).comp (first (n+1))*(g a.2).comp (tail n)) := by
  let κ' : C(Cube (n+1),ℂ)→⋆ₐ[ℂ] MaxTensor.Algebra Cone (Tensor n) := κ (n+1)
  have result : (includeLeft (∑ i,scalar (f i)*ConePauli.u i)*includeRight (∑ j,κ n (g j)*u n j) :
    MaxTensor.Algebra Cone (Tensor n)) =
    ∑ a:Pauli.Label×Label n,κ' ((f a.1).comp (first (n+1))*(g a.2).comp (tail n))*
      (includeLeft (ConePauli.u a.1)*includeRight (u n a.2)) := by
    rw [map_sum,map_sum,Finset.sum_mul,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [map_mul]
    have hfirst : ∀ h,κ' (h.comp (first (n+1)))=includeLeft (scalar h) := κ_first n
    have htail : ∀ h,κ' (h.comp (tail n))=includeRight (κ n h) := κ_tail n
    rw [hfirst,htail]
    have hc := (legs_commute (ConePauli.u i) (κ n (g j))).eq
    calc
      _ = includeLeft (scalar (f i))*(includeLeft (ConePauli.u i)*includeRight (κ n (g j)))*
        includeRight (u n j) := by noncomm_ring
      _ = _ := by rw [hc]; noncomm_ring
  exact result

lemma dense (n : ℕ) : DenseRange (expansion n) := by
  induction n with
  | zero =>
    let S : Submodule ℂ (Tensor 0) := (LinearMap.range (expansion 0)).topologicalClosure
    have hc : IsClosed (S:Set (Tensor 0)) := Submodule.isClosed_topologicalClosure _
    intro x
    change x∈S
    refine ConePauli.dense.induction_on x hc ?_
    intro f
    apply (LinearMap.range (expansion 0)).le_topologicalClosure
    exact ⟨fun i=>(f i).comp (first 0),expansion_zero f⟩
  | succ n ih =>
    let S : Submodule ℂ (Tensor (n+1)) := (LinearMap.range (expansion (n+1))).topologicalClosure
    have hc : IsClosed (S:Set (Tensor (n+1))) := Submodule.isClosed_topologicalClosure _
    have hp (a : Cone) (b : Tensor n) : includeLeft a*includeRight b ∈ S := by
      refine ConePauli.dense.induction_on a
        (hc.preimage ((map_continuous (includeLeft (B:=Tensor n))).mul continuous_const)) ?_
      intro f
      refine ih.induction_on b
        (hc.preimage (continuous_const.mul (map_continuous (includeRight (A:=Cone))))) ?_
      intro g
      rw [expansion_product]
      exact (LinearMap.range (expansion (n+1))).le_topologicalClosure ⟨_,rfl⟩
    intro x
    change x∈S
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact hc
    | ih x =>
      let inclusion : (Cone ⊗[ℂ] Tensor n) →ₗ[ℂ] Tensor (n+1) :=
        of.toLinearMap.comp rawEquiv.toStarAlgHom.toLinearMap
      suffices ∀ tensor : Cone ⊗[ℂ] Tensor n, inclusion tensor ∈ S from this x
      intro tensor
      induction tensor using OAI.tensorInductionOn with
      | add x y hx hy => rw [map_add]; exact S.add_mem hx hy
      | tmul a b =>
        change of (a ⊗ₜ[ℂ] b) ∈ S
        rw [of_tmul]
        exact hp a b


lemma faithful (n : ℕ) : Function.Injective (repr n) :=
  CubeFrame.faithful (κ n) (repr n) (p n) (u n) (PauliPower.ce n)
    (κ_commute n) (u_gram n) (repr_κ n) (repr_u n)
    (PauliPower.ccoeff n) (PauliPower.ccoeff_ce n) (dense n)


theorem exists_unique_lift (n : ℕ) (f : C(Cube n,Fiber n))
    (hf : ∀ a t,p n a t=0 → PauliPower.ccoeff n a (f t)=0) :
    ∃! b : Tensor n,repr n b=f ∧ ‖b‖=‖f‖ :=
  CubeFrame.exists_unique_lift (κ n) (repr n) (p n) (u n) (PauliPower.ce n)
    (repr_κ n) (repr_u n) (PauliPower.ccoeff n) (PauliPower.ccoeff_sum n)
    (κ_commute n) (u_gram n) (PauliPower.ccoeff_ce n) (dense n) f hf

end KirchbergRordam.GenericRW.ConeCube


namespace KirchbergRordam.GenericRW.ConeCube
open scoped CStarAlgebra ComplexOrder BigOperators
open ConeModel

lemma matLeg_commute (n : ℕ) (i j : Fin (n+1)) (hij : i≠j) (a b : M2) :
    Commute (matLeg n i a) (matLeg n j b) := by
  induction n with
  | zero => exact (hij ((Fin.eq_zero i).trans (Fin.eq_zero j).symm)).elim
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => exact MatrixTensor.legs_commute _ _
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (MatrixTensor.legs_commute _ _).symm
      | succ j => exact (ih i j (fun h=>hij (congrArg Fin.succ h))).map MatrixTensor.rightMatrix


lemma p_zero (n : ℕ) (a : Label n) (t : Cube n) (hp : p n a t=0) :
    ∃ j,t j=0 ∧ PauliSupport.coord n a j≠0 := by
  induction n with
  | zero =>
    refine ⟨0,?_,?_⟩
    · by_cases ha : a=(0:Pauli.Label)
      · subst a; simp [p,ConePauli.p,first] at hp
      · have eval_nonzero : ∀ label : Pauli.Label, label ≠ 0 →
            ConePauli.p label (t 0) = ((t 0 : ℝ) : ℂ) := by
          intro label hlabel
          simp [ConePauli.p, hlabel]
        have hz : ((t 0:ℝ):ℂ)=0 := (eval_nonzero a ha).symm.trans hp
        apply Subtype.ext
        exact_mod_cast hz
    · intro ha
      change a=(0:Pauli.Label) at ha
      subst a
      simp [p,ConePauli.p,first] at hp
  | succ n ih =>
    change ConePauli.p a.1 (t 0)*p n a.2 (tail n t)=0 at hp
    rcases mul_eq_zero.mp hp with hp|hp
    · have ha : a.1≠0 := by intro ha; simp [ha,ConePauli.p] at hp
      refine ⟨0,?_,ha⟩
      have hz : ((t 0:ℝ):ℂ)=0 := by simpa [ConePauli.p,ha] using hp
      apply Subtype.ext
      exact_mod_cast hz
    · obtain ⟨j,hj,hne⟩ := ih a.2 (tail n t) hp
      exact ⟨j.succ,hj,hne⟩
end KirchbergRordam.GenericRW.ConeCube
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MatrixSimplex
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


namespace KirchbergRordam.GenericRW.MatrixMix
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
omit [Fintype ι] in
omit instSize instPauliData in
lemma e_star.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [DecidableEq ι]
    (i j : ι) : star (e i j)=e j i := by
  change (Matrix.single i j (1:ℂ)).conjTranspose=_
  simp [Matrix.conjTranspose_single,e]
omit instSize instPauliData in
lemma e_mul.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [Fintype ι]
    [DecidableEq ι]
    (i j k l : ι) : e i j*e k l=if j=k then e i l else 0 := by
  by_cases h : j=k
  · subst k; simp [e]
  · simp [e,h]
omit instSize instPauliData in
lemma e_sum.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [Fintype ι]
    [DecidableEq ι]
    : ∑ i : ι,e i i=1 := by
  ext i j
  simp [e,Matrix.sum_apply,Matrix.single_apply,Matrix.one_apply,ite_and]

variable (φ : Mat ι →⋆ₐ[ℂ] A) (ψ : Mat κ →⋆ₐ[ℂ] A)
variable (hc : ∀ a b,Commute (φ a) (ψ b))
include hc in
lemma x_star (i j : ι×κ) : star (x φ ψ i j)=x φ ψ j i := by
  simp only [x,star_mul,← map_star,e_star]
  exact (hc _ _).eq.symm
include hc in
lemma x_mul (i j k l : ι×κ) : x φ ψ i j*x φ ψ k l=if j=k then x φ ψ i l else 0 := by
  unfold x
  calc
    _=φ (e i.1 j.1)*φ (e k.1 l.1)*(ψ (e i.2 j.2)*ψ (e k.2 l.2)) := by
      rw [mul_assoc,← mul_assoc (ψ _),← (hc _ _).eq]; noncomm_ring
    _=_ := by
      rw [← map_mul,← map_mul,e_mul,e_mul]
      by_cases h1 : j.1=k.1 <;> by_cases h2 : j.2=k.2 <;>
        simp [h1,h2,Prod.ext_iff]
lemma x_sum : ∑ i : ι×κ,x φ ψ i i=1 := by
  simp only [x,Fintype.sum_prod_type,← Finset.mul_sum,← map_sum,e_sum,map_one,mul_one]

omit instSize instPauliData in
lemma linear_single.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {ι : Type contextLevel2}
    {κ : Type contextLevel3}
    [Fintype ι]
    [Fintype κ]
    [DecidableEq ι]
    [DecidableEq κ]
    (φ : KirchbergRordam.GenericRW.MatrixMix.Mat ι →⋆ₐ[ℂ] A)
    (ψ : KirchbergRordam.GenericRW.MatrixMix.Mat κ →⋆ₐ[ℂ] A)
    (i j : ι×κ) (z : ℂ) : linear φ ψ (Matrix.single i j z)=z • x φ ψ i j := by
  simp [linear,Matrix.single,ite_and]
lemma linear_one : linear φ ψ 1=1 := by simpa [linear,Matrix.one_apply] using x_sum φ ψ
include hc in
lemma linear_star (a : Mat (ι×κ)) : linear φ ψ (star a)=star (linear φ ψ a) := by
  simp only [linear,LinearMap.coe_mk,AddHom.coe_mk,star_sum,star_smul,x_star φ ψ hc]
  exact Finset.sum_comm
include hc in
lemma linear_mul (a b : Mat (ι×κ)) : linear φ ψ (a*b)=linear φ ψ a*linear φ ψ b := by
  induction a using Matrix.induction_on' with
  | h_zero => simp
  | h_add a a' ha ha' => simp only [add_mul,map_add,ha,ha']
  | h_std_basis i j z =>
    induction b using Matrix.induction_on' with
    | h_zero => simp
    | h_add b b' hb hb' => simp only [mul_add,map_add,hb,hb']
    | h_std_basis k l w =>
      by_cases h : j=k
      · subst k
        rw [Matrix.single_mul_single_same,linear_single,linear_single,linear_single]
        simp [smul_smul,x_mul φ ψ hc,mul_comm]
      · rw [Matrix.single_mul_single_of_ne (h:=h)]
        simp [linear_single,x_mul φ ψ hc,h]

def tensor : Mat (ι×κ) →⋆ₐ[ℂ] A where
  toFun := linear φ ψ
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,linear_one,Algebra.algebraMap_eq_smul_one]
  map_one' := linear_one φ ψ
  map_mul' := linear_mul φ ψ hc
  map_star' := linear_star φ ψ hc

lemma tensor_kronecker (a : Mat ι) (b : Mat κ) :
    tensor φ ψ hc (Matrix.kronecker a b)=φ a*ψ b := by
  simp only [Matrix.kronecker]
  induction a using Matrix.induction_on' with
  | h_zero => simp
  | h_add a a' ha ha' => simp only [Matrix.add_kronecker,map_add,add_mul,ha,ha']
  | h_std_basis i j z =>
    induction b using Matrix.induction_on' with
    | h_zero => simp
    | h_add b b' hb hb' => simp only [Matrix.kronecker_add,map_add,mul_add,hb,hb']
    | h_std_basis k l w =>
      rw [Matrix.single_kronecker_single]
      change linear φ ψ (Matrix.single (i,k) (j,l) (z*w))=_
      rw [linear_single]
      have he (i j : ι) (z : ℂ) : Matrix.single i j z=z • e i j := by simp [e]
      have hf (i j : κ) (z : ℂ) : Matrix.single i j z=z • e i j := by simp [e]
      rw [he,hf,map_smul,map_smul,smul_mul_smul_comm]
      rfl

variable {φ ψ}
lemma tensor_mem (S : StarSubalgebra ℂ A) (hφ : ∀ a,φ a∈S) (hψ : ∀ b,ψ b∈S)
    (a : Mat (ι×κ)) : tensor φ ψ hc a∈S := by
  change (∑ i,∑ j,a i j • x φ ψ i j)∈S
  exact S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem (S.mul_mem (hφ _) (hψ _)) _
end KirchbergRordam.GenericRW.MatrixMix


namespace KirchbergRordam.GenericRW.MatrixMix
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]
variable {ι κ X : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable [TopologicalSpace X]
lemma tensor_continuous (φ : X → Mat ι →⋆ₐ[ℂ] A) (ψ : X → Mat κ →⋆ₐ[ℂ] A)
    (hc : ∀ z a b,Commute (φ z a) (ψ z b))
    (hφ : ∀ a,Continuous fun z => φ z a) (hψ : ∀ b,Continuous fun z => ψ z b)
    (a : X → Mat (ι×κ)) (ha : Continuous a) :
    Continuous fun z => tensor (φ z) (ψ z) (hc z) (a z) := by
  change Continuous fun z => ∑ i,∑ j,a z i j • (φ z (e i.1 j.1)*ψ z (e i.2 j.2))
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp ((continuous_apply i).comp ha)).smul ((hφ _).mul (hψ _))

variable (φ ψ : Mat (Fin Size.n) →⋆ₐ[ℂ] A) (hc : ∀ a b,Commute (φ a) (ψ b))
lemma tensor_left (a : Mat (Fin Size.n)) : tensor φ ψ hc (FlipPath.left a)=φ a := by
  have he : FlipPath.left a=Matrix.kronecker a 1 := by ext i j; simp [FlipPath.left,Matrix.one_apply]
  rw [he,tensor_kronecker,map_one,mul_one]
lemma tensor_right (a : Mat (Fin Size.n)) : tensor φ ψ hc (FlipPath.right a)=ψ a := by
  have he : FlipPath.right a=Matrix.kronecker 1 a := by ext i j; simp [FlipPath.right,Matrix.one_apply]
  rw [he,tensor_kronecker,map_one,one_mul]

def u (t : unitInterval) : A := tensor φ ψ hc (FlipPath.path t)
lemma u_star_mul (t : unitInterval) : star (u φ ψ hc t)*u φ ψ hc t=1 := by
  rw [u,← map_star,← map_mul,FlipPath.path_star_mul,map_one]
lemma u_mul_star (t : unitInterval) : u φ ψ hc t*star (u φ ψ hc t)=1 := by
  rw [u,← map_star,← map_mul,FlipPath.path_mul_star,map_one]
lemma u_zero : u φ ψ hc 0=1 := by rw [u,FlipPath.path_zero,map_one]

def interpolate (t : unitInterval) : Mat (Fin Size.n) →⋆ₐ[ℂ] A where
  toFun a := u φ ψ hc t*φ a*star (u φ ψ hc t)
  map_zero' := by simp
  map_add' a b := by simp [mul_add,add_mul]
  map_one' := by rw [map_one,mul_one,u_mul_star]
  map_mul' a b := by
    rw [map_mul]
    calc
      _=u φ ψ hc t*φ a*(star (u φ ψ hc t)*u φ ψ hc t)*φ b*star (u φ ψ hc t) := by rw [u_star_mul]; noncomm_ring
      _=_ := by noncomm_ring
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,map_one,Algebra.algebraMap_eq_smul_one,mul_smul_comm,mul_one,smul_mul_assoc,u_mul_star]
  map_star' a := by rw [map_star,star_mul,star_mul,star_star]; noncomm_ring

lemma interpolate_zero (a : Mat (Fin Size.n)) : interpolate φ ψ hc 0 a=φ a := by
  change u φ ψ hc 0*φ a*star (u φ ψ hc 0)=_
  rw [u_zero,star_one,one_mul,mul_one]
lemma interpolate_top {t : unitInterval} (ht : 2/3≤(t:ℝ)) (a : Mat (Fin Size.n)) :
    interpolate φ ψ hc t a=ψ a := by
  calc
    _=tensor φ ψ hc (FlipPath.path t*FlipPath.left a*star (FlipPath.path t)) := by
      rw [map_mul,map_mul,map_star,tensor_left]; rfl
    _=tensor φ ψ hc (FlipPath.right a) := by
      congr 1
      rw [FlipPath.path_top ht,FlipPath.flip_star,← FlipPath.flip_exchange,mul_assoc,FlipPath.flip_mul,mul_one]
    _=_ := tensor_right φ ψ hc a

lemma interpolate_mem (S : StarSubalgebra ℂ A) (hφ : ∀ a,φ a∈S) (hψ : ∀ b,ψ b∈S)
    (t : unitInterval) (a : Mat (Fin Size.n)) : interpolate φ ψ hc t a∈S := by
  have hu : u φ ψ hc t∈S := tensor_mem hc S hφ hψ _
  exact S.mul_mem (S.mul_mem hu (hφ a)) (S.star_mem' hu)

lemma interpolate_continuous
    (φ ψ : X → Mat (Fin Size.n) →⋆ₐ[ℂ] A) (hc : ∀ z a b,Commute (φ z a) (ψ z b))
    (hφ : ∀ a,Continuous fun z => φ z a) (hψ : ∀ b,Continuous fun z => ψ z b)
    (t : X → unitInterval) (ht : Continuous t) (a : Mat (Fin Size.n)) :
    Continuous fun z => interpolate (φ z) (ψ z) (hc z) (t z) a := by
  have hu : Continuous fun z => u (φ z) (ψ z) (hc z) (t z) :=
    tensor_continuous φ ψ hc hφ hψ _ (FlipPath.path_continuous.comp ht)
  exact (hu.mul (hφ a)).mul hu.star
end KirchbergRordam.GenericRW.MatrixMix
namespace KirchbergRordam.GenericRW

namespace CoordinateSimplex

variable {ι : Type*} [Fintype ι]

lemma le_one (weights : CoordinateSimplex ι) (index : ι) : weights index ≤ 1 := by
  rw [← sum_eq_one weights]
  exact Finset.single_le_sum (fun entry _ => zero_le weights entry) (Finset.mem_univ index)

end CoordinateSimplex
end KirchbergRordam.GenericRW
namespace KirchbergRordam.GenericRW.MatrixSimplex
open scoped BigOperators
open MatrixMix
variable {A : Type*} [CStarAlgebra A]
abbrev Simplex (n : ℕ) := CoordinateSimplex (Fin (n+1))

def last {n : ℕ} (r : Simplex (n+1)) : unitInterval :=
  ⟨r (Fin.last (n+1)),CoordinateSimplex.zero_le r _,CoordinateSimplex.le_one r _⟩
def den {n : ℕ} (r : Simplex (n+1)) : ℝ := max (1-last r) (1/3)
include instSize instPauliData in
lemma den_pos {n : ℕ} (r : Simplex (n+1)) : 0<den r := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
include instSize instPauliData in
lemma prev_sum {n : ℕ} (r : Simplex (n+1)) :
    ∑ i : Fin (n+1),r i.castSucc=1-(last r:ℝ) := by
  have h := CoordinateSimplex.sum_eq_one r
  rw [Fin.sum_univ_castSucc] at h
  change _+ (last r:ℝ)=1 at h
  linarith

def prev {n : ℕ} (r : Simplex (n+1)) : Simplex n :=
  ⟨fun i => r i.castSucc/den r + if i=0 then 1-(1-last r)/den r else 0,by
    constructor
    · intro i
      apply add_nonneg (div_nonneg (CoordinateSimplex.zero_le r _) (den_pos r).le)
      split_ifs
      · apply sub_nonneg.mpr
        exact (div_le_one (den_pos r)).mpr (le_max_left _ _)
      · exact le_rfl
    · rw [Finset.sum_add_distrib,← Finset.sum_div,prev_sum]
      simp⟩
lemma prev_apply {n : ℕ} (r : Simplex (n+1)) (h : (last r:ℝ)≤2/3) (i : Fin (n+1)) :
    prev r i=r i.castSucc/(1-last r) := by
  have hd : den r=1-last r := max_eq_left (by linarith)
  have hn : (1-(last r:ℝ))≠0 := by linarith
  change r i.castSucc / den r + (if i=0 then 1-(1-last r)/den r else 0)=_
  simp [hd,div_self hn]
lemma prev_pos {n : ℕ} (r : Simplex (n+1)) (h : (last r:ℝ)≤2/3) (i : Fin (n+1))
    (hi : 0<prev r i) : 0<r i.castSucc := by
  rw [prev_apply r h] at hi
  exact (div_pos_iff.mp hi).elim (fun h => h.1) (fun h => False.elim (by linarith [CoordinateSimplex.zero_le r i.castSucc]))
include instSize instPauliData in
lemma last_continuous {n : ℕ} : Continuous (last (n:=n)) := by
  apply Continuous.subtype_mk
  exact (continuous_apply _).comp continuous_subtype_val
lemma prev_continuous {n : ℕ} : Continuous (prev (n:=n)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  have hd : Continuous (den (n:=n)) := by
    exact (continuous_const.sub (continuous_subtype_val.comp last_continuous)).max continuous_const
  have hq : Continuous fun r : Simplex (n+1) => (1-(last r:ℝ))/den r :=
    (continuous_const.sub (continuous_subtype_val.comp last_continuous)).div hd (fun r => (den_pos r).ne')
  apply Continuous.add
  · exact ((continuous_apply _).comp continuous_subtype_val).div hd (fun r => (den_pos r).ne')
  · by_cases hi : i=0
    · simp only [ite_eq_left hi]
      exact (show Continuous (fun _ : Simplex (n+1) => (1:ℝ)) from continuous_const).sub hq
    · simp only [ite_eq_right hi]; exact continuous_const

structure Family {n : ℕ} (φ : Fin (n+1) → Mat (Fin Size.n) →⋆ₐ[ℂ] A) where
  hom : Simplex n → Mat (Fin Size.n) →⋆ₐ[ℂ] A
  continuous : ∀ a,Continuous fun r => hom r a
  support : ∀ r (S : StarSubalgebra ℂ A), (∀ i,0<r i → ∀ a,φ i a∈S) → ∀ a,hom r a∈S
  vertex : ∀ i a,hom (CoordinateSimplex.vertex i) a=φ i a

variable {n : ℕ} {φ : Fin (n+2) → Mat (Fin Size.n) →⋆ₐ[ℂ] A}
variable (hc : ∀ i j,i≠j → ∀ a b,Commute (φ i a) (φ j b))
variable (F : Family (fun i : Fin (n+1) => φ i.castSucc))

include hc in
lemma family_commute (r : Simplex (n+1)) (a b : Mat (Fin Size.n)) :
    Commute (F.hom (prev r) a) (φ (Fin.last (n+1)) b) := by
  let S := StarSubalgebra.centralizer ℂ (Set.range (φ (Fin.last (n+1))))
  have hm : F.hom (prev r) a∈S := F.support _ S (by
    intro i _ c
    rw [StarSubalgebra.mem_centralizer_iff]
    rintro _ ⟨d,rfl⟩
    constructor
    · exact (hc i.castSucc (Fin.last _) (Fin.castSucc_ne_last i) c d).eq.symm
    · rw [← map_star]
      exact (hc i.castSucc (Fin.last _) (Fin.castSucc_ne_last i) c (star d)).eq.symm) a
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp hm) _ ⟨b,rfl⟩).1.symm

def extendHom (r : Simplex (n+1)) : Mat (Fin Size.n) →⋆ₐ[ℂ] A :=
  interpolate (F.hom (prev r)) (φ (Fin.last (n+1))) (family_commute hc F r) (last r)

lemma extend_support (r : Simplex (n+1)) (S : StarSubalgebra ℂ A)
    (hs : ∀ i,0<r i → ∀ a,φ i a∈S) (a : Mat (Fin Size.n)) : extendHom hc F r a∈S := by
  by_cases ht : 2/3≤(last r:ℝ)
  · rw [extendHom,interpolate_top _ _ _ ht]
    exact hs _ (by change 0<(last r:ℝ); linarith) a
  · have ht' : (last r:ℝ)≤2/3 := (lt_of_not_ge ht).le
    have hp : ∀ a,F.hom (prev r) a∈S := F.support _ S (fun i hi => hs _ (prev_pos r ht' i hi))
    by_cases hz : last r=0
    · rw [extendHom,hz,interpolate_zero]; exact hp a
    · apply interpolate_mem _ _ _ S hp (hs _ ?_) _ a
      have hne : (last r:ℝ)≠0 := fun h => hz (Subtype.ext h)
      exact lt_of_le_of_ne (last r).2.1 hne.symm

lemma prev_vertex (i : Fin (n+1)) :
    prev (CoordinateSimplex.vertex i.castSucc)=CoordinateSimplex.vertex i := by
  have hz : last (CoordinateSimplex.vertex i.castSucc)=0 := by
    apply Subtype.ext
    simp [last,Fin.castSucc_ne_last,eq_comm]
  ext j
  rw [prev_apply _ (by rw [hz]; norm_num)]
  simp [hz,Pi.single_apply,Fin.castSucc_inj]

lemma extend_vertex (i : Fin (n+2)) (a : Mat (Fin Size.n)) :
    extendHom hc F (CoordinateSimplex.vertex i) a=φ i a := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · apply interpolate_top
    norm_num [last]
  · have hz : last (CoordinateSimplex.vertex j.castSucc)=0 := by
      apply Subtype.ext
      simp [last,Fin.castSucc_ne_last,eq_comm]
    rw [extendHom,hz,interpolate_zero,prev_vertex,F.vertex]

def extend : Family φ where
  hom := extendHom hc F
  continuous a := interpolate_continuous _ _ _ (fun b => (F.continuous b).comp prev_continuous)
    (fun _ => continuous_const) last last_continuous a
  support := extend_support hc F
  vertex := extend_vertex hc F


theorem exists_family (n : ℕ) (φ : Fin (n+1) → Mat (Fin Size.n) →⋆ₐ[ℂ] A)
    (hc : ∀ i j,i≠j → ∀ a b,Commute (φ i a) (φ j b)) : Nonempty (Family φ) := by
  induction n with
  | zero =>
    refine ⟨{hom := fun _ => φ 0
             continuous := fun _ => continuous_const
             support := ?_
             vertex := ?_}⟩
    · intro r S hs a
      have coordinate_one : r 0 = 1 := by
        simpa using CoordinateSimplex.sum_eq_one r
      exact hs 0 (by rw [coordinate_one]; norm_num) a
    · intro i a
      have : i=0 := Fin.eq_zero i
      subst i
      rfl
  | succ n ih =>
    obtain ⟨F⟩ := ih (fun i => φ i.castSucc) (fun i j hij => hc _ _ (fun h => hij (Fin.castSucc_inj.mp h)))
    exact ⟨extend hc F⟩
end KirchbergRordam.GenericRW.MatrixSimplex
namespace KirchbergRordam.GenericRW.CubeWeights
open scoped BigOperators
variable {n : ℕ}
omit instSize instPauliData in
lemma coord_le_radius
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {n : ℕ}
    (t : Cube n) (i : Fin (n+1)) : (t i:ℝ)≤radius t :=
  Finset.le_sup' (fun i => (t i:ℝ)) (Finset.mem_univ i)
lemma radius_pos (t : Punctured n) : 0<radius t.1 := by
  by_contra! h
  have ht : t.1=0 := by
    ext i
    apply le_antisymm
    · exact (coord_le_radius t.1 i).trans h
    · exact (t.1 i).2.1
  exact t.2 ht
omit instSize instPauliData in
lemma radius_continuous
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {n : ℕ}
    : Continuous (radius (n:=n)) :=
  Continuous.finset_sup'_apply _ (fun i _ => continuous_subtype_val.comp (continuous_apply i))
omit instSize instPauliData in
lemma radius_attained
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {n : ℕ}
    (t : Cube n) : ∃ i,radius t=(t i:ℝ) := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => (t i:ℝ))
  exact ⟨i,hi⟩

omit instSize instPauliData in
lemma weight_nonneg
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {n : ℕ}
    (t : Punctured n) (i : Fin (n+1)) : 0≤weight t i := le_max_right _ _
lemma total_pos (t : Punctured n) : 0<total t := by
  obtain ⟨i,hi⟩ := radius_attained t.1
  have hw : weight t i=1/2 := by
    rw [weight,← hi,div_self (radius_pos t).ne']; norm_num
  exact lt_of_lt_of_le (by rw [hw]; norm_num) (Finset.single_le_sum (fun j _ => weight_nonneg t j) (Finset.mem_univ i))

def normalized (t : Punctured n) : CoordinateSimplex (Fin (n+1)) :=
  ⟨fun i => weight t i/total t,fun i => div_nonneg (weight_nonneg t i) (total_pos t).le,by
    rw [← Finset.sum_div,← total,div_self (total_pos t).ne']⟩
lemma normalized_apply (t : Punctured n) (i : Fin (n+1)) : normalized t i=weight t i/total t := rfl
lemma normalized_continuous : Continuous (normalized (n:=n)) := by
  have hw (i : Fin (n+1)) : Continuous fun t : Punctured n => weight t i :=
    (((continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val)).div
      (radius_continuous.comp continuous_subtype_val) (fun t => (radius_pos t).ne')).sub continuous_const).max continuous_const
  have ht : Continuous (total (n:=n)) := continuous_finsetSum _ fun i _ => hw i
  apply Continuous.subtype_mk
  exact continuous_pi fun i => (hw i).div ht (fun t => (total_pos t).ne')
lemma normalized_zero (t : Punctured n) (i : Fin (n+1)) (hi : t.1 i=0) : normalized t i=0 := by
  rw [normalized_apply,weight,hi]
  norm_num
lemma normalized_support (t : Punctured n) (i : Fin (n+1)) (hi : 0<normalized t i) : 0<(t.1 i:ℝ) := by
  by_contra! h
  have hz : t.1 i=0 := Subtype.ext (le_antisymm h (t.1 i).2.1)
  rw [normalized_zero t i hz] at hi
  exact (lt_irrefl _ hi)

omit instSize instPauliData in
lemma g_continuous
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (δ : ℝ) : Continuous (g δ) := by unfold g; fun_prop
omit instSize instPauliData in
lemma g_nonneg
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (δ : ℝ) (t : unitInterval) : 0≤g δ t := le_max_right _ _
omit instSize instPauliData in
lemma g_le_one
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {δ : ℝ} (hδ : 0<δ) (t : unitInterval) : g δ t≤1 := by
  apply max_le _ zero_le_one
  have : 0≤2*(t:ℝ)/δ := div_nonneg (mul_nonneg (by norm_num) t.2.1) hδ.le
  linarith
omit instSize instPauliData in
lemma g_zero
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (δ : ℝ) : g δ 0=1 := by simp [g]
lemma H_continuous (δ : ℝ) : Continuous (H (n:=n) δ) :=
  continuous_const.sub (continuous_finsetProd _ fun i _ => (g_continuous δ).comp (continuous_apply i))
lemma H_zero (δ : ℝ) : H (n:=n) δ 0=0 := by simp [H,g_zero]
lemma H_nonneg {δ : ℝ} (hδ : 0<δ) (t : Cube n) : 0≤H δ t := by
  apply sub_nonneg.mpr
  exact Finset.prod_le_one (fun i _ => g_nonneg δ (t i)) (fun i _ => g_le_one hδ (t i))
lemma H_le_one (δ : ℝ) (t : Cube n) : H δ t≤1 := by
  have hp : 0≤∏ i,g δ (t i) := Finset.prod_nonneg (fun i _ => g_nonneg δ (t i))
  unfold H; linarith
end KirchbergRordam.GenericRW.CubeWeights
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_CubeField
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

namespace KirchbergRordam.GenericRW.CubeField
open scoped BigOperators Topology
open Filter MatrixMix MatrixSimplex CubeWeights
variable {A : Type*} [CStarAlgebra A]
variable {n : ℕ} {φ : Fin (n+1) → Mat (Fin Size.n) →⋆ₐ[ℂ] A}
variable (F : Family φ)

lemma norm_matrix_unit (ψ : Mat (Fin Size.n) →⋆ₐ[ℂ] A) (i j : Fin Size.n) : ‖ψ (e i j)‖≤1 := by
  have hp : IsStarProjection (ψ (e j j)) := ⟨by change ψ _*ψ _=ψ _; rw [← map_mul,e_mul,ite_eq_left rfl],by change star (ψ _) = ψ _; rw [← map_star,e_star]⟩
  have hn := hp.norm_le _
  have he : ‖ψ (e i j)‖*‖ψ (e i j)‖=‖ψ (e j j)‖ := by
    rw [← CStarRing.norm_star_mul_self,← map_star,← map_mul,e_star,e_mul,ite_eq_left rfl]
  nlinarith [norm_nonneg (ψ (e i j))]

def dampedFun (f : C(Cube n,ℝ)) (i j : Fin Size.n) (t : Cube n) : A :=
  if ht : t≠0 then f t • F.hom (normalized ⟨t,ht⟩) (e i j) else 0
lemma damped_zero (f : C(Cube n,ℝ)) (i j : Fin Size.n) : dampedFun F f i j 0=0 := by simp [dampedFun]
lemma damped_norm (f : C(Cube n,ℝ)) (i j : Fin Size.n) (t : Cube n) : ‖dampedFun F f i j t‖≤‖f t‖ := by
  unfold dampedFun
  split_ifs
  · rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_matrix_unit _ _ _)
  · simp only [norm_zero]; exact norm_nonneg (f t)
lemma damped_continuous (f : C(Cube n,ℝ)) (hf : f 0=0) (i j : Fin Size.n) :
    Continuous (dampedFun F f i j) := by
  have ho : ContinuousOn (dampedFun F f i j) {t | t≠0} := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun t : Punctured n => dampedFun F f i j t.1)
    have hh := ((f.continuous.comp continuous_subtype_val).smul
      ((F.continuous (e i j)).comp normalized_continuous))
    exact hh.congr (fun t => by simp [dampedFun,t.2])
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t=0
  · subst t
    change Tendsto (dampedFun F f i j) _ (𝓝 (dampedFun F f i j 0))
    rw [damped_zero]
    apply squeeze_zero_norm (damped_norm F f i j)
    simpa [ContinuousAt,hf] using f.continuous.norm.continuousAt (x:=0)
  · exact ho.continuousAt (isOpen_ne.mem_nhds ht)

def damped (f : C(Cube n,ℝ)) (hf : f 0=0) (i j : Fin Size.n) : C(Cube n,A) :=
  ⟨dampedFun F f i j,damped_continuous F f hf i j⟩

def scalarH (δ : ℝ) : C(Cube n,ℝ) := ⟨H δ,H_continuous δ⟩
def x (δ : ℝ) (i j : Fin Size.n) : C(Cube n,A) := damped F (scalarH δ) (H_zero δ) i j

def h (δ : ℝ) : C(Cube n,A) := ⟨fun t => H δ t • (1:A),(H_continuous δ).smul continuous_const⟩
lemma x_apply (δ : ℝ) (i j : Fin Size.n) (t : Punctured n) :
    x F δ i j t.1=H δ t.1 • F.hom (normalized t) (e i j) := by simp [x,damped,dampedFun,t.2,scalarH]
lemma x_zero (δ : ℝ) (i j : Fin Size.n) : x F δ i j 0=0 := damped_zero F _ _ _

lemma x_star (δ : ℝ) (i j : Fin Size.n) : star (x F δ i j)=x F δ j i := by
  ext t
  by_cases ht : t=0
  · subst t; simp [x_zero]
  · change star (x F δ i j t)=_
    rw [x_apply F δ i j ⟨t,ht⟩,x_apply F δ j i ⟨t,ht⟩,star_smul,star_trivial,← map_star,e_star]
lemma x_mul (δ : ℝ) (i j k l : Fin Size.n) :
    x F δ i j*x F δ k l=if j=k then h δ*x F δ i l else 0 := by
  ext t
  by_cases ht : t=0
  · subst t; by_cases hjk : j=k <;> simp [hjk,x_zero,h,H_zero]
  · change x F δ i j t*x F δ k l t=_
    rw [x_apply F δ i j ⟨t,ht⟩,x_apply F δ k l ⟨t,ht⟩,smul_mul_smul_comm,← map_mul,e_mul]
    by_cases hjk : j=k
    · rw [ite_eq_left hjk,ite_eq_left hjk]
      change _=H δ t • (1:A)*x F δ i l t
      rw [x_apply F δ i l ⟨t,ht⟩,smul_mul_smul_comm,one_mul]
    · simp [hjk]
lemma x_diagonal (δ : ℝ) : ∑ i : Fin Size.n,x F δ i i=h δ := by
  ext t
  by_cases ht : t=0
  · subst t; simp [x_zero,h,H_zero]
  · simp only [ContinuousMap.sum_apply]
    simp_rw [x_apply F δ _ _ ⟨t,ht⟩]
    rw [← Finset.smul_sum,← map_sum,e_sum,map_one]
    rfl

lemma x_support (δ : ℝ) (t : Cube n) (S : StarSubalgebra ℂ A)
    (hs : ∀ k,0<(t k:ℝ) → ∀ a,φ k a∈S) (i j : Fin Size.n) : x F δ i j t∈S := by
  by_cases ht : t=0
  · subst t; rw [x_zero]; exact S.zero_mem
  · rw [x_apply F δ i j ⟨t,ht⟩]
    exact S.smul_mem (F.support _ S (fun k hk => hs k (normalized_support ⟨t,ht⟩ k hk)) _) _

end KirchbergRordam.GenericRW.CubeField

namespace KirchbergRordam.GenericRW.CubeField
open scoped BigOperators CStarAlgebra
open MatrixMix MatrixSimplex CubeWeights
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {n : ℕ} {φ : Fin (n+1) → Mat (Fin Size.n) →⋆ₐ[ℂ] A} (F : Family φ)
omit [PartialOrder A] [StarOrderedRing A] in
lemma h_norm {δ : ℝ} (hδ : 0<δ) : ‖(h δ : C(Cube n,A))‖≤1 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro t
  change ‖H δ t • (1:A)‖≤1
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (H_nonneg hδ t)]
  have hn : ‖(1:A)‖≤1 := (IsStarProjection.one (R:=A)).norm_le _
  exact (mul_le_of_le_one_right (H_nonneg hδ t) hn).trans (H_le_one δ t)

end KirchbergRordam.GenericRW.CubeField

namespace KirchbergRordam.GenericRW.ConeCube
open scoped CStarAlgebra ComplexOrder BigOperators
open ConeModel MatrixSimplex
local instance instPartialOrderCarrierTensor (n : ℕ) : PartialOrder (Tensor n) := CStarAlgebra.spectralOrder _
local instance instStarOrderedRingCarrierTensor (n : ℕ) : StarOrderedRing (Tensor n) := CStarAlgebra.spectralOrderedRing _

def family (n : ℕ) : Family (matLeg n) := (exists_family n (matLeg n) (matLeg_commute n)).some

lemma x_face_commute (n : ℕ) (δ : ℝ) (i l : Fin Size.n) (t : Cube n) (j : Fin (n+1))
    (hj : t j=0) (b : M2) : Commute (matLeg n j b) (CubeField.x (family n) δ i l t) := by
  let S := StarSubalgebra.centralizer ℂ (Set.range (matLeg n j))
  have hm : CubeField.x (family n) δ i l t∈S := CubeField.x_support _ _ _ S (by
    intro k hk a
    have hkj : k≠j := by intro h; subst k; rw [hj] at hk; exact (lt_irrefl (0:ℝ)) hk
    rw [StarSubalgebra.mem_centralizer_iff]
    rintro _ ⟨c,rfl⟩
    constructor
    · exact (matLeg_commute n j k hkj.symm c a).eq
    · rw [← map_star]
      exact (matLeg_commute n j k hkj.symm (star c) a).eq) i l
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp hm) _ ⟨b,rfl⟩).1

lemma x_liftable (n : ℕ) (δ : ℝ) (i j : Fin Size.n) :
    ∃! b : Tensor n,repr n b=CubeField.x (family n) δ i j ∧
      ‖b‖=‖CubeField.x (family n) δ i j‖ := by
  apply exists_unique_lift
  intro a t ha
  obtain ⟨k,hk,hne⟩ := p_zero n a t ha
  exact ccoeff_zero n a k hne _ (x_face_commute n δ i j t k hk)

def x (n : ℕ) (δ : ℝ) (i j : Fin Size.n) : Tensor n := (x_liftable n δ i j).exists.choose
lemma repr_x (n : ℕ) (δ : ℝ) (i j : Fin Size.n) :
    repr n (x n δ i j)=CubeField.x (family n) δ i j := ((x_liftable n δ i j).exists.choose_spec).1

def hScalar (n : ℕ) (δ : ℝ) : C(Cube n,ℂ) :=
  ⟨fun t => ((CubeWeights.H δ t:ℝ):ℂ),Complex.continuous_ofReal.comp (CubeWeights.H_continuous δ)⟩
def h (n : ℕ) (δ : ℝ) : Tensor n := κ n (hScalar n δ)
lemma repr_h (n : ℕ) (δ : ℝ) : repr n (h n δ)=CubeField.h δ := by
  apply ContinuousMap.ext
  intro t
  rw [h,repr_κ]
  change algebraMap ℂ (Fiber n) (((CubeWeights.H δ t):ℝ):ℂ)=CubeWeights.H δ t • (1:Fiber n)
  rw [Algebra.algebraMap_eq_smul_one]
  exact Complex.coe_smul _ _
lemma h_nonneg (n : ℕ) {δ : ℝ} (hδ : 0<δ) : 0≤h n δ := by
  apply map_nonneg (κ n)
  intro t
  exact Complex.zero_le_real.mpr (CubeWeights.H_nonneg hδ t)
lemma h_norm (n : ℕ) {δ : ℝ} (hδ : 0<δ) : ‖h n δ‖≤1 := by
  have hn : ‖h n δ‖=‖repr n (h n δ)‖ := by
    exact (NonUnitalStarAlgHom.norm_map (repr n) (faithful n) _).symm
  rw [hn,repr_h]
  exact CubeField.h_norm hδ


def weighted (n : ℕ) {δ : ℝ} (hδ : 0<δ) : OrderZero.WeightedUnits (Fin Size.n) (Tensor n) where
  h := h n δ
  x := x n δ
  nonneg := h_nonneg n hδ
  norm_le := h_norm n hδ
  star_x i j := by apply faithful n; rw [map_star,repr_x,repr_x]; exact CubeField.x_star _ _ _ _
  mul_x i j k l := by
    have product_eq := CubeField.x_mul (family n) δ i j k l
    apply faithful n
    rw [map_mul,repr_x,repr_x]
    refine product_eq.trans ?_
    split_ifs <;> simp [map_mul,repr_h,repr_x]
  diagonal := by
    apply faithful n
    rw [map_sum,repr_h]
    simp_rw [repr_x]
    exact CubeField.x_diagonal _ _
end KirchbergRordam.GenericRW.ConeCube
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


namespace KirchbergRordam.GenericRW.AmplifiedComparison
open scoped CStarAlgebra
open scoped BigOperators
variable {P R B : Type*} [CStarAlgebra P] [CStarAlgebra R] [CStarAlgebra B]
variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
variable (φ : P →⋆ₐ[ℂ] B) (ψ : R →⋆ₐ[ℂ] B)
variable (hc : ∀ a b, Commute (φ a) (ψ b))

omit hc in
omit instSize instPauliData in
lemma pair_mul.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type contextLevel1}
    {R : Type contextLevel2}
    {B : Type contextLevel3}
    [CStarAlgebra P]
    [CStarAlgebra R]
    [CStarAlgebra B]
    (φ : P →⋆ₐ[ℂ] B)
    (ψ : R →⋆ₐ[ℂ] B)
    (hc : ∀ (a : P) (b : R), Commute (φ a) (ψ b))
    (a c : P) (b d : R) : pair φ ψ a b*pair φ ψ c d=pair φ ψ (a*c) (b*d) := by
  simp only [pair,map_mul]
  calc
    (φ a*ψ b)*(φ c*ψ d)=φ a*(ψ b*φ c)*ψ d := by noncomm_ring
    _=φ a*(φ c*ψ b)*ψ d := by rw [← (hc c b).eq]
    _=_ := by noncomm_ring
omit hc in
omit instSize instPauliData in
lemma pair_star.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type contextLevel1}
    {R : Type contextLevel2}
    {B : Type contextLevel3}
    [CStarAlgebra P]
    [CStarAlgebra R]
    [CStarAlgebra B]
    (φ : P →⋆ₐ[ℂ] B)
    (ψ : R →⋆ₐ[ℂ] B)
    (hc : ∀ (a : P) (b : R), Commute (φ a) (ψ b))
    (a : P) (b : R) : star (pair φ ψ a b)=pair φ ψ (star a) (star b) := by
  simp only [pair,star_mul,map_star]
  simpa only [map_star] using (hc (star a) (star b)).eq.symm

variable [PartialOrder P] [StarOrderedRing P]
variable (y : J→P) (hy : ∀ j,0≤y j) (horth : ∀ j k,j≠k → y j*y k=0)
variable (u : J→I→P) (z : I→R) (v : J→R) (e : R)
variable (hz : ∀ i l,star (z i)*z l=if i=l then e else 0)

def gramVector (j : J) (i : I) : B := pair φ ψ (CFC.sqrt (y j)*u j i) (z i*v j)
end KirchbergRordam.GenericRW.AmplifiedComparison
namespace KirchbergRordam.GenericRW.MaxTensor
open scoped BigOperators
universe u
variable {P Q : Type u} [CStarAlgebra P] [CStarAlgebra Q]

def pure (a : P) (b : Q) : Algebra P Q := includeLeft a*includeRight b
omit instSize instPauliData in
@[simp] lemma pure_zero_left
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type u}
    {Q : Type u}
    [CStarAlgebra P]
    [CStarAlgebra Q]
    (b : Q) : pure (0:P) b=0 := by simp [pure]
omit instSize instPauliData in
@[simp] lemma pure_zero_right
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type u}
    {Q : Type u}
    [CStarAlgebra P]
    [CStarAlgebra Q]
    (a : P) : pure a (0:Q)=0 := by simp [pure]
omit instSize instPauliData in
@[simp] lemma pure_one
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type u}
    {Q : Type u}
    [CStarAlgebra P]
    [CStarAlgebra Q]
    : pure (1:P) (1:Q)=1 := by simp [pure]

def word : (n : ℕ) → (Fin (n+1)→P) → powerPack P n
  | 0,f => f 0
  | n+1,f => pure (f 0) (word n (fun i => f i.succ))

end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.GenericRW.ConeCut
open scoped CStarAlgebra ComplexOrder BigOperators
open ConeModel MatrixMix
local instance instPartialOrderSubtypeContinuousMapElemRealUnitIntervalM2MemStarSubalgebraComplexCone : PartialOrder Cone := CStarAlgebra.spectralOrder _
local instance instLESubtypeContinuousMapElemRealUnitIntervalM2MemStarSubalgebraComplexCone : LE Cone := (CStarAlgebra.spectralOrder Cone).toLE

def unit (i j : Fin Size.n) : M2 := CStarMatrix.ofMatrix (e i j)
omit instSize instPauliData in
lemma coeff_continuous
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (δ : ℝ) : Continuous (coeff δ) := by unfold coeff; fun_prop
omit instSize instPauliData in
lemma coeff_zero
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {δ : ℝ} (hδ : 0≤δ) : coeff δ 0=0 := by simp [coeff,max_eq_right (neg_nonpos.mpr hδ)]

def q (δ : ℝ) (hδ : 0≤δ) : Cone :=
  ⟨⟨fun t=>coeff δ t • unit 0 0,(coeff_continuous δ).smul continuous_const⟩,by
    change coeff δ 0 • unit 0 0∈(⊥:StarSubalgebra ℂ M2)
    rw [coeff_zero hδ,zero_smul]
    exact zero_mem _⟩
def z (δ : ℝ) (hδ : 0≤δ) (i : Fin Size.n) : Cone :=
  ⟨⟨fun t=>Real.sqrt (coeff δ t) • unit i 0,(coeff_continuous δ).sqrt.smul continuous_const⟩,by
    change Real.sqrt (coeff δ 0) • unit i 0∈(⊥:StarSubalgebra ℂ M2)
    rw [coeff_zero hδ,Real.sqrt_zero,zero_smul]
    exact zero_mem _⟩

def g (δ : ℝ) : Cone := scalar ⟨fun t => (CubeWeights.g δ t:ℂ),Complex.continuous_ofReal.comp (CubeWeights.g_continuous δ)⟩
end KirchbergRordam.GenericRW.ConeCut

namespace KirchbergRordam.GenericRW.ConeCube
open scoped CStarAlgebra ComplexOrder BigOperators
open ConeModel _root_.OAI.KirchbergRordam.GenericRW.MaxTensor

def y (n : ℕ) (δ : ℝ) (hδ : 0≤δ) (j : Fin (n+1)) : Tensor n :=
  word n (fun i => if i=j then ConeCut.q δ hδ else ConeCut.g δ)
end KirchbergRordam.GenericRW.ConeCube
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FiniteDrop
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


namespace KirchbergRordam.GenericRW.ConeDrop
open scoped CStarAlgebra ComplexOrder BigOperators
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor ConeModel
local instance instPartialOrderSubtypeContinuousMapElemRealUnitIntervalM2MemStarSubalgebraComplexCone : PartialOrder Cone := CStarAlgebra.spectralOrder _
variable {P : Type*} [CStarAlgebra P]
local instance instPartialOrderCarrierPowerPack (n : ℕ) : PartialOrder (powerPack P n) := CStarAlgebra.spectralOrder _
end KirchbergRordam.GenericRW.ConeDrop

end

end OAI
end


