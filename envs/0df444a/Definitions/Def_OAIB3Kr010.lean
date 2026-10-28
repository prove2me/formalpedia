-- Prove2me | Definitions.Def_OAIB3Kr010
-- name    : OAIB3Kr010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T17:03:16.104294+00:00
-- url     : https://prove2.me/theorems/aff64352-e566-4245-a256-ca07f16b8774
-- title:
--   Definitions bundle OAIB3Kr010 of the split of OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 51 declarations of OpenAI's Lean: 30 definitions, 4 instances and 17 theorems. The definitions and types are `OAI.KirchbergRordam.BalancedDropHalfFlip.squareMap`, `OAI.KirchbergRordam.CStarInductiveLimit.stageHom`, `OAI.KirchbergRordam.CStarInductiveLimit.stageSeq`, `OAI.KirchbergRordam.CStarInductiveLimit.toUltrapower`, `OAI.KirchbergRordam.DimensionDrop23`, `OAI.KirchbergRordam.DropChannels.left`, `OAI.KirchbergRordam.DropChannels.right`, `OAI.KirchbergRordam.DropMatrixRepresentations.blockRepresentation`, `OAI.KirchbergRordam.DropMatrixRepresentations.leftEvaluation`, `OAI.KirchbergRordam.DropMatrixRepresentations.leftValue`, `OAI.KirchbergRordam.DropMatrixRepresentations.representation`, `OAI.KirchbergRordam.DropMatrixRepresentations.rightEvaluation`, `OAI.KirchbergRordam.DropMatrixRepresentations.rightValue`, `OAI.KirchbergRordam.EndpointMultiplicity.duplicate`, `OAI.KirchbergRordam.EndpointMultiplicity.duplicateUnitary`, `OAI.KirchbergRordam.FourLegSymmetries.Algebra`, `OAI.KirchbergRordam.FourLegSymmetries.H`, `OAI.KirchbergRordam.FourLegSymmetries.K`, `OAI.KirchbergRordam.GeneralEndpointMultiplicity.leftBase`, `OAI.KirchbergRordam.GeneralEndpointMultiplicity.leftRep`, `OAI.KirchbergRordam.MatrixTensor.subKronecker`, `OAI.KirchbergRordam.MultiplicativeChannel.restrictDrop`, `OAI.KirchbergRordam.PrimeTensorSections.SquareFiber`, `OAI.KirchbergRordam.PrimeTensorSections.leftSection`, `OAI.KirchbergRordam.PrimeTensorSections.rightSection`, `OAI.KirchbergRordam.PrimeTensorSections.sectionMap`, `OAI.KirchbergRordam.dimensionDropSubalgebra`, `OAI.KirchbergRordam.leftMatrix`, `OAI.KirchbergRordam.matrixEval`, `OAI.KirchbergRordam.rightMatrix`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`CharacterCriterion_BalancedLimit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/BalancedLimit.lean), [`CharacterCriterion_DiagonalIteration`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/DiagonalIteration.lean), [`CharacterCriterion_EndpointMultiplicity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/EndpointMultiplicity.lean), [`CharacterCriterion_FourLegSymmetries`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/FourLegSymmetries.lean), [`CharacterCriterion_GeneralSystem`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/GeneralSystem.lean), [`CharacterCriterion_MultiplicativeChannels`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/MultiplicativeChannels.lean), [`CharacterCriterion_PrimeSpectrum`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/PrimeSpectrum.lean), [`CharacterCriterion_TensorSections`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/TensorSections.lean).
--
--   **Imports.** It imports the published bundle `Def_CharacterCriterion`; the bundles `OAIB3Kr007` and `OAIB3Kr008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIB3Kr013` and `OAIB3Kr014`; the statements `OAI_KirchbergRordam_PrimeDropPresentation_to_central`, `OAI.KirchbergRordam.PrimeTensorSections.irreducible_fiber_bound` and `OAI_KirchbergRordam_PrimeTensorSections_sectionRange_closed`; the proofs of `OAI.KirchbergRordam.MatrixTensor.representation_bound`, `OAI_KirchbergRordam_PrimeDropPresentation_to_central`, `OAI.KirchbergRordam.PrimeTensorSections.irreducible_fiber_bound`, `OAI_KirchbergRordam_PrimeTensorSections_sectionMap_isometry` and `OAI_KirchbergRordam_PrimeTensorSections_sectionRange_closed`.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr007
import Definitions.Def_OAIB3Kr008

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_BalancedLimit
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


def leftMatrix : M2 →⋆ₐ[ℂ] M6 :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (leftMatrixAlgebra.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)


def rightMatrix : M3 →⋆ₐ[ℂ] M6 :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (rightMatrixAlgebra.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)


def matrixEval (t : unitInterval) : C(unitInterval, M6) →⋆ₐ[ℂ] M6 where
  toFun f := f t
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl


def dimensionDropSubalgebra : StarSubalgebra ℂ C(unitInterval, M6) :=
  leftMatrix.range.comap (matrixEval 0) ⊓ rightMatrix.range.comap (matrixEval 1)


abbrev DimensionDrop23 := dimensionDropSubalgebra

instance dropSubringClass : SubringClass
    (StarSubalgebra ℂ C(unitInterval, M6)) C(unitInterval, M6) :=
  StarSubalgebra.subringClass (R := ℂ) (A := C(unitInterval, M6))

@[ext]
theorem drop_ext {f g : DimensionDrop23}
    (h : ∀ t, (f : C(unitInterval, M6)) t = (g : C(unitInterval, M6)) t) : f = g := by
  apply Subtype.ext
  exact ContinuousMap.ext h

end KirchbergRordam


namespace KirchbergRordam.CStarInductiveLimit
open Filter Topology
open scoped CStarAlgebra
variable {B : Type*} [CStarAlgebra B]

def stageSeq (S : System) (φ : ∀ n, S.obj n →⋆ₐ[ℂ] B)
    (n : ℕ) (x : S.obj n) : NormUltrapower.BoundedSeq B :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun m => if h : n ≤ m then φ m (S.map n m h x) else 0)
    ‖x‖ (fun m => by
      split_ifs with h
      · exact (NonUnitalStarAlgHom.norm_apply_le (φ m) _).trans_eq (S.norm_map n m h x)
      · exact (norm_zero (E:=B)).le.trans (norm_nonneg x))

lemma stageSeq_apply (S : System) (φ : ∀ n, S.obj n →⋆ₐ[ℂ] B)
    (n m : ℕ) (h : n ≤ m) (x : S.obj n) :
    stageSeq S φ n x m=φ m (S.map n m h x) := dite_eq_left h

def stageHom (S : System) (φ : ∀ n, S.obj n →⋆ₐ[ℂ] B)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤Filter.atTop) (n : ℕ) :
    S.obj n →⋆ₐ[ℂ] NormUltrapower.Algebra B ω where
  toFun x := NormUltrapower.quotientMap ω (stageSeq S φ n x)
  map_add' x y := by
    rw [← map_add]
    apply quotient_eq_of_eventuallyEq
    filter_upwards [hω (eventually_ge_atTop n)] with m hm
    simp only [BoundedContinuousFunction.add_apply,stageSeq_apply S φ n m hm,map_add]
  map_mul' x y := by
    rw [← map_mul]
    apply quotient_eq_of_eventuallyEq
    filter_upwards [hω (eventually_ge_atTop n)] with m hm
    simp only [BoundedContinuousFunction.mul_apply,stageSeq_apply S φ n m hm,map_mul]
  map_zero' := by
    rw [← map_zero (NormUltrapower.quotientMap ω)]
    apply quotient_eq_of_eventuallyEq
    filter_upwards [hω (eventually_ge_atTop n)] with m hm
    simp only [stageSeq_apply S φ n m hm,map_zero]
    rfl
  map_one' := by
    rw [← map_one (NormUltrapower.quotientMap ω)]
    apply quotient_eq_of_eventuallyEq
    filter_upwards [hω (eventually_ge_atTop n)] with m hm
    simp only [stageSeq_apply S φ n m hm,map_one]
    rfl
  commutes' z := by
    rw [← (NormUltrapower.quotientMap ω).commutes]
    apply quotient_eq_of_eventuallyEq
    filter_upwards [hω (eventually_ge_atTop n)] with m hm
    rw [stageSeq_apply S φ n m hm]
    exact (congrArg (φ m) ((S.map n m hm).commutes z)).trans ((φ m).commutes z)
  map_star' x := by
    rw [← map_star]
    apply quotient_eq_of_eventuallyEq
    filter_upwards [hω (eventually_ge_atTop n)] with m hm
    simp only [BoundedContinuousFunction.star_apply,stageSeq_apply S φ n m hm,map_star]

lemma stageHom_map (S : System) (φ : ∀ n, S.obj n →⋆ₐ[ℂ] B)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤Filter.atTop)
    (i j : ℕ) (hij : i ≤ j) (x : S.obj i) :
    stageHom S φ ω hω j (S.map i j hij x)=stageHom S φ ω hω i x := by
  apply quotient_eq_of_eventuallyEq
  filter_upwards [hω (eventually_ge_atTop j)] with m hm
  rw [stageSeq_apply S φ j m hm,stageSeq_apply S φ i m (hij.trans hm),S.map_map]


def toUltrapower (S : System) (φ : ∀ n, S.obj n →⋆ₐ[ℂ] B)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤Filter.atTop) :
    Algebra S →⋆ₐ[ℂ] NormUltrapower.Algebra B ω :=
  lift S (stageHom S φ ω hω) (stageHom_map S φ ω hω)

end KirchbergRordam.CStarInductiveLimit


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimeSpectrum
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

namespace KirchbergRordam.MatrixTensor
open scoped TensorProduct CStarAlgebra ComplexOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
instance matrixFinite : FiniteDimensional ℂ (Mat ι) :=
  inferInstanceAs (FiniteDimensional ℂ (Matrix ι ι ℂ))
instance subClosed (S : StarSubalgebra ℂ (Mat ι)) : IsClosed (S : Set (Mat ι)) :=
  S.toSubalgebra.toSubmodule.closed_of_finiteDimensional
instance subCStar (S : StarSubalgebra ℂ (Mat ι)) : CStarAlgebra S :=
  StarSubalgebra.cstarAlgebra S

def subKronecker (S : StarSubalgebra ℂ (Mat ι)) (T : StarSubalgebra ℂ (Mat κ)) :
    (S ⊗[ℂ] T) →⋆ₐ[ℂ] Mat (ι×κ) :=
  MaxTensor.liftRaw (MatrixTensor.leftMatrix.comp S.subtype) (MatrixTensor.rightMatrix.comp T.subtype)
    (fun a b => legs_commute a.val b.val)

end KirchbergRordam.MatrixTensor

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

namespace KirchbergRordam.PrimeTensorSections
open scoped CStarAlgebra ComplexOrder TensorProduct
open PrimeDimensionDrop MatrixTensor
variable {p q r k : ℕ}
abbrev SquareFiber (p q r k : ℕ) := Mat ((Fin p×Fin q)×(Fin r×Fin k))

def leftSection : Algebra p q →⋆ₐ[ℂ] C(Square,SquareFiber p q r k) where
  toFun f := ⟨fun x => MatrixTensor.leftMatrix (f.val x.1),
    (map_continuous MatrixTensor.leftMatrix).comp (f.val.continuous.comp continuous_fst)⟩
  map_zero' := by apply ContinuousMap.ext; intro x; exact map_zero MatrixTensor.leftMatrix
  map_one' := by apply ContinuousMap.ext; intro x; exact map_one MatrixTensor.leftMatrix
  map_add' f g := by apply ContinuousMap.ext; intro x; exact map_add MatrixTensor.leftMatrix _ _
  map_mul' f g := by apply ContinuousMap.ext; intro x; exact map_mul MatrixTensor.leftMatrix _ _
  commutes' z := by apply ContinuousMap.ext; intro x; exact MatrixTensor.leftMatrix.commutes z
  map_star' f := by apply ContinuousMap.ext; intro x; exact map_star MatrixTensor.leftMatrix _
def rightSection : Algebra r k →⋆ₐ[ℂ] C(Square,SquareFiber p q r k) where
  toFun f := ⟨fun x => MatrixTensor.rightMatrix (f.val x.2),
    (map_continuous MatrixTensor.rightMatrix).comp (f.val.continuous.comp continuous_snd)⟩
  map_zero' := by apply ContinuousMap.ext; intro x; exact map_zero MatrixTensor.rightMatrix
  map_one' := by apply ContinuousMap.ext; intro x; exact map_one MatrixTensor.rightMatrix
  map_add' f g := by apply ContinuousMap.ext; intro x; exact map_add MatrixTensor.rightMatrix _ _
  map_mul' f g := by apply ContinuousMap.ext; intro x; exact map_mul MatrixTensor.rightMatrix _ _
  commutes' z := by apply ContinuousMap.ext; intro x; exact MatrixTensor.rightMatrix.commutes z
  map_star' f := by apply ContinuousMap.ext; intro x; exact map_star MatrixTensor.rightMatrix _
lemma sections_commute (a : Algebra p q) (b : Algebra r k) :
    Commute (leftSection (r:=r) (k:=k) a) (rightSection (p:=p) (q:=q) b) := by
  apply ContinuousMap.ext
  intro x
  exact legs_commute (a.val x.1) (b.val x.2)
def sectionMap : MaxTensor.Algebra (Algebra p q) (Algebra r k) →⋆ₐ[ℂ]
    C(Square,SquareFiber p q r k) := by
  refine MaxTensor.lift (A:=Algebra p q) (B:=Algebra r k) (C:=C(Square,SquareFiber p q r k)) ?_ ?_ ?_
  · exact leftSection
  · exact rightSection
  · exact sections_commute
@[simp] lemma sectionMap_left (a : Algebra p q) (x : Square) :
    sectionMap (r:=r) (k:=k) (MaxTensor.includeLeft a) x = MatrixTensor.leftMatrix (a.val x.1) := by
  change MaxTensor.lift (C:=C(Square,SquareFiber p q r k)) _ _ _ (MaxTensor.of (a ⊗ₜ[ℂ] (1 : Algebra r k))) x = _
  rw [MaxTensor.lift_of_tmul]
  change (leftSection (r:=r) (k:=k) a * rightSection (p:=p) (q:=q) (1 : Algebra r k)) x = _
  change MatrixTensor.leftMatrix (a.val x.1) * MatrixTensor.rightMatrix (1:Fiber r k)=_
  rw [map_one,mul_one]
@[simp] lemma sectionMap_right (b : Algebra r k) (x : Square) :
    sectionMap (p:=p) (q:=q) (MaxTensor.includeRight b) x = MatrixTensor.rightMatrix (b.val x.2) := by
  change MaxTensor.lift (C:=C(Square,SquareFiber p q r k)) _ _ _ (MaxTensor.of ((1 : Algebra p q) ⊗ₜ[ℂ] b)) x = _
  rw [MaxTensor.lift_of_tmul]
  change (leftSection (r:=r) (k:=k) (1 : Algebra p q) * rightSection (p:=p) (q:=q) b) x = _
  change MatrixTensor.leftMatrix (1:Fiber p q) * MatrixTensor.rightMatrix (b.val x.2)=_
  rw [map_one,one_mul]
@[simp] lemma sectionMap_tmul (a : Algebra p q) (b : Algebra r k) (x : Square) :
    sectionMap (MaxTensor.of (a ⊗ₜ[ℂ] b)) x = subKronecker
      (evaluation p q x.1).range (evaluation r k x.2).range
      (⟨evaluation p q x.1 a,⟨a,rfl⟩⟩ ⊗ₜ[ℂ] ⟨evaluation r k x.2 b,⟨b,rfl⟩⟩) := by
  rw [MaxTensor.of_tmul,map_mul,ContinuousMap.mul_apply,sectionMap_left,sectionMap_right]
  rfl

end KirchbergRordam.PrimeTensorSections
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FourLegSymmetries
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

namespace KirchbergRordam.FourLegSymmetries
open scoped CStarAlgebra ComplexOrder Matrix Kronecker
open MatrixTensor MatrixPermutationPath
variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
abbrev Algebra (P Q : Type*) := MatrixTensor.Mat (Index P Q)
def H : unitary (Algebra P Q) := perm hflip
def K : unitary (Algebra P Q) := perm kflip
lemma H_selfadjoint : star (H (P:=P) (Q:=Q) : Algebra P Q)=(H (P:=P) (Q:=Q) : Algebra P Q) := by
  change (hflip⁻¹.permMatrix ℂ)ᴴ = hflip⁻¹.permMatrix ℂ
  rw [Matrix.conjTranspose_permMatrix]
  rfl
lemma K_selfadjoint : star (K (P:=P) (Q:=Q) : Algebra P Q)=(K (P:=P) (Q:=Q) : Algebra P Q) := by
  change (kflip⁻¹.permMatrix ℂ)ᴴ = kflip⁻¹.permMatrix ℂ
  rw [Matrix.conjTranspose_permMatrix]
  rfl
lemma flips_commute : Commute (H (P:=P) (Q:=Q)) K := by
  change perm hflip * perm kflip=perm kflip*perm hflip
  rw [←perm_mul,←perm_mul]
  congr 1

end KirchbergRordam.FourLegSymmetries


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_DiagonalIteration
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

namespace KirchbergRordam.DiagonalIteration
open scoped CStarAlgebra ComplexOrder
open Filter Topology
attribute [instance] System.cstar System.finite
end KirchbergRordam.DiagonalIteration
namespace KirchbergRordam.BalancedDropHalfFlip
open scoped CStarAlgebra ComplexOrder
open Filter Topology
universe u

variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
def squareMap (φ : A →⋆ₐ[ℂ] B) : MaxTensor.Algebra A A →⋆ₐ[ℂ] MaxTensor.Algebra B B :=
  MaxTensor.lift (MaxTensor.includeLeft.comp φ) (MaxTensor.includeRight.comp φ)
    (fun a b => MaxTensor.legs_commute (φ a) (φ b))
end KirchbergRordam.BalancedDropHalfFlip
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_EndpointMultiplicity
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

namespace KirchbergRordam.DropMatrixRepresentations
open MatrixDiagonalPath MatrixBlockReindex
open scoped CStarAlgebra ComplexOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
lemma left_injective [Nonempty κ] : Function.Injective (MatrixTensor.leftMatrix (ι:=ι) (κ:=κ)) := by
  intro a b h
  ext i j
  let k : κ := Classical.choice inferInstance
  have he := congrArg (fun m : Mat (ι×κ) => m (i,k) (j,k)) h
  simpa [left_apply] using he
lemma right_injective [Nonempty ι] : Function.Injective (MatrixTensor.rightMatrix (ι:=ι) (κ:=κ)) := by
  intro a b h
  ext i j
  let k : ι := Classical.choice inferInstance
  have he := congrArg (fun m : Mat (ι×κ) => m (k,i) (k,j)) h
  simpa [right_apply] using he
variable (p q : ℕ) [instNeZerop : NeZero p] [instNeZeroq : NeZero q]
def leftValue (f : PrimeDimensionDrop.Algebra p q) : Mat (Fin p) := Classical.choose f.property.1
omit instNeZerop instNeZeroq in
lemma leftValue_spec
    (p : ℕ)
    (q : ℕ)
    [NeZero p]
    [NeZero q]
    (f : PrimeDimensionDrop.Algebra p q) :
    MatrixTensor.leftMatrix (κ:=Fin q) (leftValue p q f)=f.val 0 := Classical.choose_spec f.property.1
def rightValue (f : PrimeDimensionDrop.Algebra p q) : Mat (Fin q) := Classical.choose f.property.2
omit instNeZerop instNeZeroq in
lemma rightValue_spec
    (p : ℕ)
    (q : ℕ)
    [NeZero p]
    [NeZero q]
    (f : PrimeDimensionDrop.Algebra p q) :
    MatrixTensor.rightMatrix (ι:=Fin p) (rightValue p q f)=f.val 1 := Classical.choose_spec f.property.2
def leftEvaluation : PrimeDimensionDrop.Algebra p q →⋆ₐ[ℂ] Mat (Fin p) where
  toFun := leftValue p q
  map_zero' := left_injective (κ:=Fin q) (by rw [map_zero,leftValue_spec]; rfl)
  map_one' := left_injective (κ:=Fin q) (by rw [map_one,leftValue_spec]; rfl)
  map_add' a b := left_injective (κ:=Fin q) (by rw [leftValue_spec,map_add,leftValue_spec,leftValue_spec]; rfl)
  map_mul' a b := left_injective (κ:=Fin q) (by rw [leftValue_spec,map_mul,leftValue_spec,leftValue_spec]; rfl)
  commutes' z := left_injective (κ:=Fin q) (by rw [AlgHomClass.commutes,leftValue_spec]; rfl)
  map_star' a := left_injective (κ:=Fin q) (by rw [leftValue_spec,map_star,leftValue_spec]; rfl)
def rightEvaluation : PrimeDimensionDrop.Algebra p q →⋆ₐ[ℂ] Mat (Fin q) where
  toFun := rightValue p q
  map_zero' := right_injective (ι:=Fin p) (by rw [map_zero,rightValue_spec]; rfl)
  map_one' := right_injective (ι:=Fin p) (by rw [map_one,rightValue_spec]; rfl)
  map_add' a b := right_injective (ι:=Fin p) (by rw [rightValue_spec,map_add,rightValue_spec,rightValue_spec]; rfl)
  map_mul' a b := right_injective (ι:=Fin p) (by rw [rightValue_spec,map_mul,rightValue_spec,rightValue_spec]; rfl)
  commutes' z := right_injective (ι:=Fin p) (by rw [AlgHomClass.commutes,rightValue_spec]; rfl)
  map_star' a := right_injective (ι:=Fin p) (by rw [rightValue_spec,map_star,rightValue_spec]; rfl)
def blockRepresentation (a b : ℕ) : DimensionDrop23 →⋆ₐ[ℂ]
    Mat ((Fin 2×Fin a) ⊕ (Fin 3×Fin b)) :=
  sumBlock.comp (((MatrixTensor.leftMatrix (κ:=Fin a)).comp (leftEvaluation 2 3)).prod
    ((MatrixTensor.leftMatrix (κ:=Fin b)).comp (rightEvaluation 2 3)))
def representation (ι : Type*) [Fintype ι] [DecidableEq ι] (hι : 2≤Fintype.card ι) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat ι := by
  let a := (two_three (Fintype.card ι) hι).choose
  let b := (two_three (Fintype.card ι) hι).choose_spec.choose
  have h : 2*a+3*b=Fintype.card ι := (two_three (Fintype.card ι) hι).choose_spec.choose_spec
  let e : ((Fin 2×Fin a) ⊕ (Fin 3×Fin b)) ≃ ι :=
    BalancedDropSystem.cardEquiv (by simpa using h)
  exact (CStarMatrix.reindexₐ ℂ ℂ e).toStarAlgHom.comp (blockRepresentation a b)
end KirchbergRordam.DropMatrixRepresentations
namespace KirchbergRordam.EndpointMultiplicity
open MatrixDiagonalPath MatrixBlockReindex DiagonalIteration
open scoped ComplexOrder CStarAlgebra
variable {P Q R : Type*} [Fintype P] [Fintype Q] [Fintype R]
  [DecidableEq P] [DecidableEq Q] [DecidableEq R]
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
def duplicate : Mat P × Mat Q →⋆ₐ[ℂ] Mat (P ⊕ (Q×R)) :=
  sumBlock.comp ((StarAlgHom.fst ℂ (Mat P) (Mat Q)).prod
    ((block.comp (constHom R)).comp (StarAlgHom.snd ℂ (Mat P) (Mat Q))))
def duplicateUnitary (v : unitary (Mat Q)) : unitary (Mat (P⊕(Q×R))) :=
  Unitary.map (StarMonoidHom.ofClass (duplicate (P:=P) (Q:=Q) (R:=R)))
    (prodUnitary (1:unitary (Mat P)) v)
end KirchbergRordam.EndpointMultiplicity
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MultiplicativeChannels
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

namespace KirchbergRordam.MultiplicativeChannel
open scoped CStarAlgebra ComplexOrder
variable (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]


variable {A B}
variable {C : Type*} [CStarAlgebra C]

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

def restrictDrop (p q : ℕ) (φ : Channel A C(unitInterval,PrimeDimensionDrop.Fiber p q))
    (hφ : ∀ a, φ a∈PrimeDimensionDrop.subalgebra p q) :
    Channel A (PrimeDimensionDrop.Algebra p q) where
  linear := {
    toFun a := ⟨φ a,hφ a⟩
    map_add' a b := by apply Subtype.ext; exact map_add φ a b
    map_smul' z a := by apply Subtype.ext; exact map_smul φ z a }
  norm_le a := φ.norm_le a
  mul_eq a b := by apply Subtype.ext; exact φ.mul_eq a b
end KirchbergRordam.MultiplicativeChannel
namespace KirchbergRordam.DropChannels
open MatrixDiagonalPath DiagonalIteration
open MultiplicativeChannel (Channel weighted restrictDrop)
open scoped CStarAlgebra ComplexOrder
variable {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
variable (p q : ℕ)
variable (w : unitInterval → unitary (PrimeDimensionDrop.Fiber p q)) (hw : Continuous w)
def left (h0 : w 0=1) (ρ : D →⋆ₐ[ℂ] Mat (Fin p)) :
    Channel D (PrimeDimensionDrop.Algebra p q) :=
  restrictDrop p q (weighted leftScalar leftScalar_norm
    (conjugated w hw (MatrixTensor.leftMatrix.comp ρ))) (fun d => by
      constructor
      · refine ⟨ρ d,?_⟩
        change MatrixTensor.leftMatrix (ρ d)=leftScalar 0 • conj (w 0) (MatrixTensor.leftMatrix (ρ d))
        rw [leftScalar_zero,h0,conj_one,one_smul]
      · refine ⟨0,?_⟩
        change MatrixTensor.rightMatrix 0=leftScalar 1 • _
        rw [map_zero,leftScalar_one,zero_smul])
def right (h1 : w 1=1) (ρ : D →⋆ₐ[ℂ] Mat (Fin q)) :
    Channel D (PrimeDimensionDrop.Algebra p q) :=
  restrictDrop p q (weighted rightScalar rightScalar_norm
    (conjugated w hw (MatrixTensor.rightMatrix.comp ρ))) (fun d => by
      constructor
      · refine ⟨0,?_⟩
        change MatrixTensor.leftMatrix 0=rightScalar 0 • _
        rw [map_zero,rightScalar_zero,zero_smul]
      · refine ⟨ρ d,?_⟩
        change MatrixTensor.rightMatrix (ρ d)=rightScalar 1 • conj (w 1) (MatrixTensor.rightMatrix (ρ d))
        rw [rightScalar_one,h1,conj_one,one_smul])
end KirchbergRordam.DropChannels
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

namespace KirchbergRordam.GeneralDropSystem
open MatrixDiagonalPath MatrixBlockReindex
open BalancedDropSystem (half lowerPath upperPath lower_zero lower_one upper_zero upper_one)
open scoped CStarAlgebra Matrix ComplexOrder

variable {p q P Q : ℕ} (d : Data p q P Q)
lemma matrix_isTopologicalSemiring {SourceIndex : Type*} [Fintype SourceIndex] :
    IsTopologicalSemiring (MatrixDiagonalPath.Mat SourceIndex) := inferInstance

lemma matrix_continuousStar {SourceIndex : Type*} [Fintype SourceIndex] :
    ContinuousStar (MatrixDiagonalPath.Mat SourceIndex) := inferInstance

@[simp] lemma rawStep_apply (f) (t : unitInterval) :
    rawStep d f t=interpolate (zeroReindex d) (oneReindex d) t (evaluationBlock (eigenpath d) t f) := rfl
end KirchbergRordam.GeneralDropSystem
namespace KirchbergRordam.GeneralEndpointMultiplicity
open MatrixDiagonalPath MatrixBlockReindex DiagonalIteration EndpointMultiplicity
open scoped ComplexOrder CStarAlgebra
variable {P Q R E : Type*} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeR : Fintype R] [Fintype E]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqR : DecidableEq R] [DecidableEq E]
def leftBase (h : 2≤Fintype.card (E ⊕ (Q×R))) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat ((P×E)⊕((P×Q)×R)) :=
  (CStarMatrix.reindexₐ ℂ ℂ (leftExpand (P:=P) (Q:=Q) (R:=R) (E:=E)).symm).toStarAlgHom.comp
    (MatrixTensor.rightMatrix.comp (DropMatrixRepresentations.representation _ h))

def leftRep (h : 2≤Fintype.card (E ⊕ (Q×R))) (v : unitary (Mat (P×Q))) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat ((P×E)⊕((P×Q)×R)) :=
  (conj (duplicateUnitary (P:=P×E) (Q:=P×Q) (R:=R) v)).toStarAlgHom.comp (leftBase (P:=P) (Q:=Q) (R:=R) h)
end KirchbergRordam.GeneralEndpointMultiplicity
end

end OAI
end


