-- Prove2me | Definitions.Def_Q221FA001
-- name    : Q221FA001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T15:35:15.302034+00:00
-- url     : https://prove2.me/theorems/22f9db71-b29c-4383-b991-d3e420c5a217
-- title:
--   Definitions bundle Q221FA001 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.extreme_left_right_asymmetry`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 42 declarations of OpenAI's Lean: 23 definitions, 1 inductive type or structure, 7 instances and 11 theorems. The definitions and types are `OAI.LittleFinitistic.Nakayama.DA`, `OAI.LittleFinitistic.Nakayama.Frame`, `OAI.LittleFinitistic.Nakayama.coind`, `OAI.LittleFinitistic.Nakayama.daEquiv`, `OAI.LittleFinitistic.Nakayama.rightMult`, `OAI.LittleFinitistic.OrdinarySimulation.Compression.tensorAction`, `OAI.LittleFinitistic.Rickard.nonGenerationHasDerivedCategory`, `OAI.LittleFinitistic.Rickard.orthogonalStalksHasDerivedCategory`, `OAI.LittleFinitistic.Rickard.perpendicular`, `OAI.LittleFinitistic.Rickard.productD`, `OAI.LittleFinitistic.Rickard.productTerm`, `OAI.LittleFinitistic.Rickard.reducedComplex`, `OAI.LittleFinitistic.Rickard.reducedD`, `OAI.LittleFinitistic.Rickard.reducedProductsHasDerivedCategory`, `OAI.LittleFinitistic.Rickard.reducedTerm`, `OAI.LittleFinitistic.Rickard.sumD`, `OAI.LittleFinitistic.Rickard.sumInclusion`, `OAI.LittleFinitistic.Rickard.sumTerm`, `OAI.LittleFinitistic.Rickard.translatedResolution`, `OAI.LittleFinitistic.SelectedBasic.chainSystem`, `OAI.LittleFinitistic.SplitBasic.oppositeAugmentation`, `OAI.LittleFinitistic.SplitBasic.productAugmentation`, `OAI.LittleFinitistic.SplitBasic.squareZeroAugmentation`, `OAI.circleMeasurableSpace`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`FinitisticAsymmetry_Augmentation_SplitBasic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/FinitisticAsymmetry/Augmentation/SplitBasic.lean), [`FinitisticAsymmetry_Main`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/FinitisticAsymmetry/Main.lean), [`FinitisticAsymmetry_Nakayama_Modules`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/FinitisticAsymmetry/Nakayama/Modules.lean), [`FinitisticAsymmetry_Rickard_NonGeneration`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/FinitisticAsymmetry/Rickard/NonGeneration.lean), [`FinitisticAsymmetry_Rickard_Orthogonal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/FinitisticAsymmetry/Rickard/Orthogonal.lean), [`FinitisticAsymmetry_Rickard_OrthogonalStalks`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/FinitisticAsymmetry/Rickard/OrthogonalStalks.lean), [`FinitisticAsymmetry_Rickard_ReducedProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/FinitisticAsymmetry/Rickard/ReducedProducts.lean), [`FinitisticAsymmetry_Rickard_ResolutionFamily`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/FinitisticAsymmetry/Rickard/ResolutionFamily.lean), [`FinitisticAsymmetry_Transport_ScalarRestriction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/FinitisticAsymmetry/Transport/ScalarRestriction.lean), [`Finitistic_Ordinary_OrdinaryCompression`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Ordinary/OrdinaryCompression.lean).
--
--   **Imports.** It imports the bundle `OAIQ023F036` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q221FA002`; the proof of `OAI.LittleFinitistic.Main.infinite_littleFinitisticDimension`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import Mathlib.Algebra.Homology.Embedding.Restriction
import Mathlib.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Idempotents.Biproducts
import Mathlib.CategoryTheory.Idempotents.FunctorExtension
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Localization.Linear
import Mathlib.CategoryTheory.Localization.Preadditive
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.CategoryTheory.Triangulated.Generators
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_OAIQ023F036

section
-- module Solutions.Q221_FA.Compat
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Augmentation_SplitBasic
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace LittleFinitistic.SplitBasic
universe v
variable {k : Type v} [Field k]

section SquareZero
variable {R M : Type v} [Ring R] [Algebra k R] [AddCommGroup M]
  [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
  [Module k M] [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]
variable {ι : Type v} (χ : R →ₐ[k] (ι → k))
def squareZeroAugmentation : TrivSqZeroExt R M →ₐ[k] (ι → k) :=
  χ.comp (TrivSqZeroExt.fstHom k R M)
end SquareZero

section Product
variable {R S ι κ : Type v} [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable (χ : R →ₐ[k] (ι → k)) (ψ : S →ₐ[k] (κ → k))
def productAugmentation : R × S →ₐ[k] (Sum ι κ → k) where
  toFun x := Sum.elim (χ x.1) (ψ x.2)
  map_one' := by ext i; cases i <;> simp
  map_zero' := by ext i; cases i <;> simp
  map_add' x y := by ext i; cases i <;> simp
  map_mul' x y := by ext i; cases i <;> simp
  commutes' r := by ext i; cases i <;> simp
end Product

section Opposite
variable {R ι : Type v} [Ring R] [Algebra k R] (χ : R →ₐ[k] (ι → k))
def oppositeAugmentation : Rᵐᵒᵖ →ₐ[k] (ι → k) where
  toFun x := χ x.unop
  map_one' := χ.map_one
  map_zero' := χ.map_zero
  map_add' x y := χ.map_add _ _
  map_mul' x y := by simp [map_mul, mul_comm]
  commutes' r := χ.commutes r
end Opposite
end LittleFinitistic.SplitBasic

end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Nakayama_Modules
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Nakayama
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

abbrev rightMult (M : ModuleCat.{u} R) (r : R) : (M →ₗ[R] R) →ₗ[k] (M →ₗ[R] R) :=
  LinearMap.compRight k (LinearMap.mulRight R r)

@[simp] lemma rightMult_apply (M : ModuleCat.{u} R) (r : R) (f : M →ₗ[R] R) (x : M) :
    rightMult k R M r f x = f x * r := rfl

variable {k R}

variable (k R)

abbrev coind (V : ModuleCat.{u} k) :=
  (ModuleCat.coextendScalars (algebraMap k R)).obj V

instance coind_modulek (V : ModuleCat.{u} k) : Module k (coind k R V) :=
  inferInstanceAs (Module k ((ModuleCat.restrictScalars (algebraMap k R)).obj
    (ModuleCat.of R R) →ₗ[k] V))

instance coind_tower (V : ModuleCat.{u} k) : IsScalarTower k R (coind k R V) where
  smul_assoc a r h := by
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro x
    change R at x
    change h (x * (a • r)) = a • h (x*r)
    rw [mul_smul_comm]
    rw [Algebra.smul_def]
    exact h.map_smul a (x*r)

instance coind_comm (V : ModuleCat.{u} k) : SMulCommClass R k (coind k R V) where
  smul_comm _ _ _ := rfl

abbrev DA := coind k R (ModuleCat.of k k)

def daEquiv : DA k R ≃ₗ[k] Module.Dual k R where
  toFun h := {
    toFun := h
    map_add' := h.map_add
    map_smul' a r := by
      rw [Algebra.smul_def]
      exact h.map_smul a r }
  invFun h := {
    toFun := h
    map_add' := h.map_add
    map_smul' a r := by
      change R at r
      change h (algebraMap k R a * r) = a • h r
      rw [← Algebra.smul_def]
      exact h.map_smul a r }
  left_inv h := rfl
  right_inv h := rfl
  map_add' f g := rfl
  map_smul' a h := rfl

structure Frame (M : ModuleCat.{u} R) where
  n : ℕ
  b : Fin n → M
  c : Fin n → (M →ₗ[R] R)
  expand : ∀ x, ∑ i, c i x • b i = x

variable {k R}

variable (k R)

lemma coind_smul_eval (V : ModuleCat.{u} k) (g : coind k R V) (a : k) (r : R) :
    g (a • r) = a • g r := by
  rw [Algebra.smul_def]
  exact g.map_smul a r

end LittleFinitistic.Nakayama

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Rickard_Orthogonal
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace LittleFinitistic.Rickard
universe u v t
variable {C : Type u} [Category.{v} C]

section
variable [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

def perpendicular (X : C) : ObjectProperty C :=
  ((ObjectProperty.singleton X).shiftClosure ℤ).leftOrthogonal

instance perpendicular_isClosedUnderIsomorphisms (X : C) :
    (perpendicular X).IsClosedUnderIsomorphisms := inferInstanceAs
      (((ObjectProperty.singleton X).shiftClosure ℤ).leftOrthogonal.IsClosedUnderIsomorphisms)

instance perpendicular_isTriangulated (X : C) : (perpendicular X).IsTriangulated :=
  inferInstanceAs (((ObjectProperty.singleton X).shiftClosure ℤ).leftOrthogonal.IsTriangulated)

end

end LittleFinitistic.Rickard

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Rickard_OrthogonalStalks
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
namespace LittleFinitistic.Rickard
universe u
variable {R : Type u} [Ring R]
local instance orthogonalStalksHasDerivedCategory : HasDerivedCategory (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

end LittleFinitistic.Rickard

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Rickard_ReducedProducts
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Rickard
universe u
variable {R : Type u} [Ring R]
variable (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)

abbrev productTerm (j : ℤ) := ∀ i, (K i).X j
abbrev sumTerm (j : ℤ) := Π₀ i, (K i).X j
abbrev reducedTerm (j : ℤ) := productTerm K j × sumTerm K (j+1)

def productD (j : ℤ) : productTerm K j →ₗ[R] productTerm K (j+1) :=
  LinearMap.pi (fun i => ((K i).d j (j+1)).hom.comp (LinearMap.proj i))

def sumD (j : ℤ) : sumTerm K j →ₗ[R] sumTerm K (j+1) :=
  DFinsupp.mapRange.linearMap (fun i => ((K i).d j (j+1)).hom)

@[simp] lemma productD_apply (j : ℤ) (p : productTerm K j) (i : ℕ) :
    productD K j p i = (K i).d j (j+1) (p i) := rfl
@[simp] lemma sumD_apply (j : ℤ) (s : sumTerm K j) (i : ℕ) :
    sumD K j s i = (K i).d j (j+1) (s i) := rfl

def sumInclusion (j : ℤ) : sumTerm K j →ₗ[R] productTerm K j :=
  LinearMap.pi (fun i => DFinsupp.lapply i)

@[simp] lemma sumInclusion_apply (j : ℤ) (s : sumTerm K j) (i : ℕ) :
    sumInclusion K j s i = s i := rfl

lemma d_d_apply (i : ℕ) (j : ℤ) (p : (K i).X j) :
    (K i).d (j+1) (j+1+1) ((K i).d j (j+1) p) = 0 := by
  exact ConcreteCategory.congr_hom ((K i).d_comp_d j (j+1) (j+1+1)) p

def reducedD (j : ℤ) : reducedTerm K j →ₗ[R] reducedTerm K (j+1) :=
  ((productD K j).comp (LinearMap.fst R _ _) +
    (sumInclusion K (j+1)).comp (LinearMap.snd R _ _)).prod
      (-(sumD K (j+1)).comp (LinearMap.snd R _ _))

@[simp] lemma reducedD_fst (j : ℤ) (x : reducedTerm K j) (i : ℕ) :
    (reducedD K j x).1 i = (K i).d j (j+1) (x.1 i) + x.2 i := rfl
@[simp] lemma reducedD_snd (j : ℤ) (x : reducedTerm K j) (i : ℕ) :
    (reducedD K j x).2 i = -(K i).d (j+1) (j+1+1) (x.2 i) := rfl

lemma reducedD_sq (j : ℤ) :
    (reducedD K (j+1)).comp (reducedD K j) = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · ext i
    simp only [LinearMap.comp_apply, reducedD_fst, reducedD_snd, map_add,
      d_d_apply, zero_add, add_neg_cancel, LinearMap.zero_apply, Prod.fst_zero, Pi.zero_apply]
  · apply DFinsupp.ext
    intro i
    simp only [LinearMap.comp_apply, reducedD_snd, map_neg, d_d_apply, neg_zero,
      LinearMap.zero_apply, Prod.snd_zero, DFinsupp.zero_apply]

def reducedComplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.of (fun j => ModuleCat.of R (reducedTerm K j))
    (fun j => ModuleCat.ofHom (reducedD K j)) (fun j => by
      apply ModuleCat.hom_ext
      exact reducedD_sq K j)

@[simp] lemma reducedComplex_d (j : ℤ) :
    (reducedComplex K).d j (j+1) = ModuleCat.ofHom (reducedD K j) := by
  simp [reducedComplex, CochainComplex.of]

local instance reducedProductsHasDerivedCategory : HasDerivedCategory (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

end LittleFinitistic.Rickard

end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Rickard_ResolutionFamily
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Rickard

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
open PDMinimal

def translatedResolution (M : FiniteModule k R) (d : ℕ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (complex M).extend (ComplexShape.embeddingUpIntLE d)

end LittleFinitistic.Rickard

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Rickard_NonGeneration
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Rickard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
local instance nonGenerationHasDerivedCategory : HasDerivedCategory (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

end LittleFinitistic.Rickard

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Transport_ScalarRestriction
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]

section RestrictionAlongSurjection
universe v
variable {R S : Type v} [Ring R] [Ring S]

open CategoryTheory.Limits

instance restrictScalars_preservesFiniteLimits (f : R →+* S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{v} f) where
  preservesFiniteLimits _ _ _ := { preservesLimit := fun {_} => inferInstance }

instance restrictScalars_preservesFiniteColimits (f : R →+* S) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{v} f) where
  preservesFiniteColimits _ _ _ := { preservesColimit := fun {_} => inferInstance }

end RestrictionAlongSurjection

end LittleFinitistic
end
end
end

end OAI
end

section
-- module Solutions.Q221_FA.Finitistic_Ordinary_OrdinaryCompression
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainLeft _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteTensorRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instSMulCommClassChainAlgebraEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.towerTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.commuteActions _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.instModuleMulOppositeTensorProductChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.towerRight _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.tensor_smul _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.tensor_vertex_smul _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.arrow_mul _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.augmentation_zero_iff _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.resolutionMap_value _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.smul_diagonal _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.smul_radical _root_.OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra.supportedIdealEquiv_d _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.right_action _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.action_tmul_mk _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.evaluation_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

namespace Compression
variable (P : CochainComplex (ModuleCat.{u} A) ℤ) (a : ℤ) (l : ℕ)

/-- The commuting actions give the actual tensor-algebra representation. -/
def tensorAction : (A ⊗[k] ChainAlgebra k l) →ₐ[k] Module.End k (Compression P a l) :=
  Algebra.TensorProduct.lift (Algebra.lsmul k k (Compression P a l))
    (Algebra.lsmul k k (Compression P a l)) (by
      intro r x
      ext v
      change r • (x • v) = x • (r • v)
      exact (smul_comm x r v).symm)

@[simp] theorem tensorAction_tmul (r : A) (x : ChainAlgebra k l) (v : Compression P a l) :
    tensorAction (k := k) P a l (r ⊗ₜ[k] x) v = r • (x • v) := rfl

end Compression
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.SelectedBasic
open SelectedOrdinaryAlgebra SelectedFixedDiagram QuadraticEncoding
open OrdinarySimulation SplitBasic

def chainSystem := ChainAlgebra.directedSystem ℂ length
end LittleFinitistic.SelectedBasic

end
end

end OAI
end


