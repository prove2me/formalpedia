-- Prove2me | Definitions.Def_Q221FA002
-- name    : Q221FA002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T15:44:28.096525+00:00
-- url     : https://prove2.me/theorems/28a395c3-2532-4046-afe3-ee43626d381a
-- title:
--   Definitions bundle Q221FA002 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.extreme_left_right_asymmetry`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 19 definitions, 7 instances and 4 theorems. The definitions and types are `OAI.LittleFinitistic.DirectedBound.DirectedSystem.augmentation`, `OAI.LittleFinitistic.Nakayama.Object.value`, `OAI.LittleFinitistic.Nakayama.coindBasisMap`, `OAI.LittleFinitistic.Nakayama.coindInclusion`, `OAI.LittleFinitistic.Nakayama.coindLine`, `OAI.LittleFinitistic.Nakayama.coindRetraction`, `OAI.LittleFinitistic.Nakayama.etaMap`, `OAI.LittleFinitistic.Nakayama.functor`, `OAI.LittleFinitistic.Nakayama.map`, `OAI.LittleFinitistic.Nakayama.moduleCoindInclusion`, `OAI.LittleFinitistic.Rickard.nakayamaComplex`, `OAI.LittleFinitistic.SelectedBasic.Vertices`, `OAI.LittleFinitistic.SelectedBasic.augmentationA`, `OAI.LittleFinitistic.SelectedBasic.augmentationC`, `OAI.LittleFinitistic.SelectedBasic.baseSystem`, `OAI.LittleFinitistic.SelectedBasic.diagonalAugmentation`, `OAI.LittleFinitistic.SelectedBasic.tensorSystem`, `OAI.LittleFinitistic.TriangularConstruction.rightCornerSection`, `OAI.LittleFinitistic.TriangularConstruction.toC`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`FinitisticAsymmetry_Augmentation_Directed`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/FinitisticAsymmetry/Augmentation/Directed.lean), [`FinitisticAsymmetry_Main`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/FinitisticAsymmetry/Main.lean), [`FinitisticAsymmetry_Nakayama_Coinduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/FinitisticAsymmetry/Nakayama/Coinduction.lean), [`FinitisticAsymmetry_Nakayama_Modules`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/FinitisticAsymmetry/Nakayama/Modules.lean), [`FinitisticAsymmetry_Rickard_ResolutionFamily`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/FinitisticAsymmetry/Rickard/ResolutionFamily.lean), [`FinitisticAsymmetry_Triangular_Algebra`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/FinitisticAsymmetry/Triangular/Algebra.lean).
--
--   **Imports.** It imports the bundles `Q221FA000` and `Q221FA001` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.LittleFinitistic.CummingsConstruction.injectivesGenerate` and `OAI.LittleFinitistic.extreme_left_right_asymmetry`.
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
import Definitions.Def_Q221FA000
import Definitions.Def_Q221FA001

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Augmentation_Directed
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.vertexTensorEquiv_symm _root_.OAI.LittleFinitistic.VertexDecomposition.equiv_apply _root_.OAI.LittleFinitistic.VertexDecomposition.equiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace LittleFinitistic.DirectedBound
universe u

namespace DirectedSystem
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] {n : ℕ}
variable (D : DirectedSystem k A n)

def augmentation : A →ₐ[k] (D.Vertices → k) where
  toFun := D.coefficient
  map_zero' := by ext i; apply (D.coefficient_eq_iff _ _ _).mpr; simp
  map_one' := by ext i; apply (D.coefficient_eq_iff _ _ _).mpr; simp [D.idem]
  map_add' a b := by
    ext i
    apply (D.coefficient_eq_iff _ _ _).mpr
    simp [mul_add, add_mul, D.coefficient_spec, add_smul]
  map_mul' a b := by
    ext i
    apply (D.coefficient_eq_iff _ _ _).mpr
    rw [D.diagonal_mul, D.coefficient_spec, D.coefficient_spec, smul_mul_smul_comm, D.idem]
    rfl
  commutes' c := by
    ext i
    apply (D.coefficient_eq_iff _ _ _).mpr
    rw [← (Algebra.commutes c (D.e i)), ← Algebra.smul_def, smul_mul_assoc, D.idem]
    rfl

end DirectedSystem
end LittleFinitistic.DirectedBound

end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Nakayama_Modules
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
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

namespace Object
variable {k R}
def value {M : ModuleCat.{u} R} (x : Object k R M) : Module.Dual k (M →ₗ[R] R) := x
instance instAddCommGroup (M : ModuleCat.{u} R) : AddCommGroup (Object k R M) := inferInstanceAs (AddCommGroup (Module.Dual k (M →ₗ[R] R)))
instance instModule (M : ModuleCat.{u} R) : Module k (Object k R M) := inferInstanceAs (Module k (Module.Dual k (M →ₗ[R] R)))
@[ext] lemma ext {M : ModuleCat.{u} R} {x y : Object k R M} (h : ∀ f, value x f = value y f) : x = y := LinearMap.ext h
instance instModule_1 (M : ModuleCat.{u} R) : Module R (Object k R M) where
  smul r f := (value f).comp (rightMult k R M r)
  one_smul f := by
    ext g
    change (value f) (rightMult k R M 1 g) = (value f) g
    congr 1
    ext x
    exact mul_one _
  mul_smul r s f := by
    ext g
    change (value f) ((rightMult k R M (r*s)) g) =
      (value f) (rightMult k R M s (rightMult k R M r g))
    congr 1
    ext x
    simp [mul_assoc]
  smul_zero r := by ext g; rfl
  smul_add r f g := by ext h; rfl
  zero_smul f := by
    ext g
    change (value f) (rightMult k R M 0 g) = 0
    have : rightMult k R M 0 g = 0 := by ext x; exact mul_zero _
    rw [this, map_zero]
  add_smul r s f := by
    ext g
    change (value f) (rightMult k R M (r+s) g) =
      (value f) (rightMult k R M r g) + (value f) (rightMult k R M s g)
    rw [← map_add]
    congr 1
    ext x
    simp [mul_add]

instance instSMulCommClass (M : ModuleCat.{u} R) : SMulCommClass R k (Object k R M) where
  smul_comm r a f := by ext g; rfl
instance instIsScalarTower (M : ModuleCat.{u} R) : IsScalarTower k R (Object k R M) where
  smul_assoc a r f := by
    ext g
    change (value f) (rightMult k R M (a • r) g) = a • (value f) (rightMult k R M r g)
    rw [← map_smul]
    congr 1
    ext x
    exact mul_smul_comm _ _ _
end Object

variable {k R}
def map {M N : ModuleCat.{u} R} (f : M ⟶ N) : Object k R M →ₗ[R] Object k R N where
  toFun h := (Object.value h).comp (LinearMap.lcomp k R f.hom)
  map_add' _ _ := rfl
  map_smul' r h := by
    ext g
    change (Object.value h) (rightMult k R M r ((LinearMap.lcomp k R f.hom) g)) =
      (Object.value h) ((LinearMap.lcomp k R f.hom) (rightMult k R N r g))
    rfl

variable (k R)
def functor : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (Object k R M)
  map f := ModuleCat.ofHom (map f)
  map_id M := by ext h g; rfl
  map_comp f g := by ext h φ; rfl
instance instAdditiveModuleCatFunctor : (functor k R).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    apply Object.ext
    intro φ
    change (Object.value h) ((LinearMap.lcomp k R (f+g).hom) φ) =
      (Object.value h) ((LinearMap.lcomp k R f.hom) φ) +
      (Object.value h) ((LinearMap.lcomp k R g.hom) φ)
    rw [← map_add]
    congr 1
    ext x
    exact map_add φ _ _

def etaMap (M : ModuleCat.{u} R) (p : M) : DA k R →ₗ[R] Object k R M where
  toFun h := (daEquiv k R h).comp (LinearMap.applyₗ' k p)
  map_add' h g := rfl
  map_smul' r h := by
    apply Object.ext
    intro φ
    change h (φ p * r) = h (φ p * r)
    rfl

@[simp] lemma etaMap_apply (M : ModuleCat.{u} R) (p : M) (h : DA k R)
    (φ : M →ₗ[R] R) : Object.value (etaMap k R M p h) φ = h (φ p) := rfl

variable {k R}

variable (k R)

def coindInclusion (M : ModuleCat.{u} R) :
    (functor k R).obj M ⟶ coind k R (ModuleCat.of k (Object k R M)) :=
  ModuleCat.ofHom {
    toFun := fun h => {
      toFun := fun r => (show R from r) • h
      map_add' := fun r s => add_smul _ _ _
      map_smul' := fun a r => by
        change R at r
        change (algebraMap k R a * r) • h = a • (r • h)
        rw [← Algebra.smul_def, smul_assoc] }
    map_add' := fun h g => by
      apply LinearMap.ext
      intro r
      exact smul_add _ _ _
    map_smul' := fun r h => by
      apply LinearMap.ext
      intro s
      exact (mul_smul (show R from s) r h).symm }

def coindRetraction (M : ModuleCat.{u} R) (F : Frame R M) :
    coind k R (ModuleCat.of k (Object k R M)) ⟶ (functor k R).obj M :=
  ModuleCat.ofHom {
    toFun := fun g => {
      toFun := fun φ => ∑ i, Object.value (g (φ (F.b i))) (F.c i)
      map_add' := fun φ ψ => by
        change ∑ i, Object.value (g ((φ+ψ) (F.b i))) (F.c i) = _
        have hg (r s : R) : g (r+s) = g r + g s := g.map_add r s
        simp only [LinearMap.add_apply, hg]
        change ∑ i, (Object.value (g (φ (F.b i))) (F.c i) +
          Object.value (g (ψ (F.b i))) (F.c i)) = _
        exact Finset.sum_add_distrib
      map_smul' := fun a φ => by
        change ∑ i, Object.value (g ((a • φ) (F.b i))) (F.c i) =
          a • (∑ i, Object.value (g (φ (F.b i))) (F.c i))
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun x : Object k R M => Object.value x (F.c i))
          (coind_smul_eval k R (ModuleCat.of k (Object k R M)) g a (φ (F.b i))) }
    map_add' := fun g h => by
      apply Object.ext
      intro φ
      change ∑ i, (Object.value (g (φ (F.b i))) (F.c i) +
        Object.value (h (φ (F.b i))) (F.c i)) = _
      exact Finset.sum_add_distrib
    map_smul' := fun r g => by
      apply Object.ext
      intro φ
      rfl }

end LittleFinitistic.Nakayama

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Nakayama_Coinduction
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Module
namespace LittleFinitistic.Nakayama
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

variable {k R}
def coindLine (V : ModuleCat.{u} k) (v : V) : DA k R →ₗ[R] coind k R V :=
  ((ModuleCat.coextendScalars (algebraMap k R)).map
    (ModuleCat.ofHom ((LinearMap.id : k →ₗ[k] k).smulRight v))).hom

omit [FiniteDimensional k R] in
@[simp] lemma coindLine_apply (V : ModuleCat.{u} k) (v : V) (φ : DA k R) (r : R) :
    coindLine V v φ r = φ r • v := rfl

omit [FiniteDimensional k R] in
@[simp] lemma coind_zero_eval (V : ModuleCat.{u} k) (r : R) :
    (0 : coind k R V) r = 0 := rfl

variable {ι : Type u}
def coindBasisMap (V : ModuleCat.{u} k) (b : Basis ι k V) :
    (Π₀ _ : ι, DA k R) →ₗ[R] coind k R V := by
  classical
  exact DFinsupp.lsum ℤ (fun i => coindLine V (b i))

variable (k R)

def moduleCoindInclusion (M : ModuleCat.{u} R) :
    M ⟶ coind k R ((ModuleCat.restrictScalars (algebraMap k R)).obj M) :=
  (ModuleCat.restrictCoextendScalarsAdj (algebraMap k R)).unit.app M

end LittleFinitistic.Nakayama

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Rickard_ResolutionFamily
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
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

variable (k)
def nakayamaComplex (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (Nakayama.functor k R).mapHomologicalComplex (.up ℤ) |>.obj P

end LittleFinitistic.Rickard

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Triangular_Algebra
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.CummingsConstruction.NewInjective.instModuleT _root_.OAI.LittleFinitistic.CummingsConstruction.instAlgebraT _root_.OAI.LittleFinitistic.CummingsConstruction.newRegularπ_epi _root_.OAI.LittleFinitistic.CummingsConstruction.periodicAug_quasiIso _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CummingsConstruction.cval_mul _root_.OAI.LittleFinitistic.CummingsConstruction.ehead_mul _root_.OAI.LittleFinitistic.CummingsConstruction.epsDifferential_sq _root_.OAI.LittleFinitistic.CummingsConstruction.etail_mul _root_.OAI.LittleFinitistic.CummingsConstruction.newDifferential_sq _root_.OAI.LittleFinitistic.CummingsConstruction.oval_mul
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
namespace TriangularConstruction
universe v
variable (C E U : Type v)

namespace OffDiagonal
variable [Ring C] [Ring E] [AddCommGroup U]

variable (k : Type v) [Field k] [_root_.Algebra k C] [_root_.Algebra k E] [Module k U]

instance instFiniteDimensional [FiniteDimensional k U] : FiniteDimensional k (OffDiagonal C E U) :=
  inferInstanceAs (FiniteDimensional k U)

end OffDiagonal

variable [Ring C] [Ring E] [AddCommGroup U] [Module E U] [Module Cᵐᵒᵖ U]
  [SMulCommClass E Cᵐᵒᵖ U]

def toC : Algebra C E U →+* C where
  toFun x := x.fst.1
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def rightCornerSection :
    ((ModuleCat.restrictScalars (toC C E U).op).obj (ModuleCat.of Cᵐᵒᵖ Cᵐᵒᵖ)) →ₗ[
      (Algebra C E U)ᵐᵒᵖ] (Algebra C E U)ᵐᵒᵖ where
  toFun c := MulOpposite.op ((c.unop, 0), 0)
  map_add' c d := by
    apply MulOpposite.unop_injective
    apply TrivSqZeroExt.ext
    · apply Prod.ext
      · rfl
      · exact (zero_add (0 : E)).symm
    · exact (zero_add (0 : U)).symm
  map_smul' r c := by
    apply MulOpposite.unop_injective
    apply TrivSqZeroExt.ext
    · apply Prod.ext
      · rfl
      · exact (zero_mul _).symm
    · change 0 = (0 : E) • (offValue r.unop.snd) + MulOpposite.op r.unop.fst.1 • (0 : U)
      simp

end TriangularConstruction

end LittleFinitistic
end
end
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

def baseSystem := ThreeVertexAlgebra.directedSystem (composition P)
def tensorSystem := TensorDirected.directedSystem baseSystem chainSystem
abbrev Vertices := Sum baseSystem.Vertices tensorSystem.Vertices

def diagonalAugmentation : D →ₐ[ℂ] (Vertices → ℂ) :=
  productAugmentation baseSystem.augmentation tensorSystem.augmentation

def augmentationA : A →ₐ[ℂ] (Vertices → ℂ) :=
  squareZeroAugmentation (M := X) diagonalAugmentation

def augmentationC : Aᵐᵒᵖ →ₐ[ℂ] (Vertices → ℂ) := oppositeAugmentation augmentationA
end LittleFinitistic.SelectedBasic

end
end

end OAI
end


