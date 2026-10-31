-- Prove2me | Definitions.Def_OAIQ023F005
-- name    : OAIQ023F005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:47:18.388897+00:00
-- url     : https://prove2.me/theorems/959f0d3f-15ae-4d4d-adc3-0068cd8e3ea7
-- title:
--   Definitions bundle OAIQ023F005 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 119 declarations of OpenAI's Lean: 72 definitions, 1 inductive type or structure, 9 instances and 37 theorems. The definitions and types are `OAI.DerivedBar.BimoduleTensor.derivedIterateCongr`, `OAI.DerivedBar.BimoduleTensor.derivedTensorCongr`, `OAI.DerivedBar.BimoduleTensor.explicitBarTotal`, `OAI.DerivedBar.BimoduleTensor.freeBarTensorIso`, `OAI.DerivedBar.BimoduleTensor.freeBarTensorNatIso`, `OAI.DerivedBar.BimoduleTensor.freeEquiv`, `OAI.DerivedBar.BimoduleTensor.instModuleCarrier_solutions_1`, `OAI.DerivedBar.BimoduleTensor.resolvedTensor`, `OAI.DerivedBar.BimoduleTensor.resolvedTensorIso`, `OAI.DerivedBar.BimoduleTensor.tensorBarBicomplexIso`, `OAI.DerivedBar.BimoduleTensor.tensorFunctorObjIso`, `OAI.DerivedBar.BimoduleTensor.tensorResolution`, `OAI.DerivedBar.BimoduleTensor.tensorResolutionIso`, `OAI.DerivedBar.BimoduleTensor.tensorTotalExplicitIso`, `OAI.DerivedBar.BimoduleTensor.twoSidedBarBicomplex`, `OAI.DerivedBar.BimoduleTensor.twoSidedBarFunctor`, `OAI.DerivedBar.BimoduleTensor.twoSidedBarMap`, `OAI.DerivedBar.IterateSupport.object`, `OAI.DerivedBar.IterateSupport.resolvedModel`, `OAI.DerivedBar.IterateSupport.resolvedModelIso`, `OAI.DerivedBar.Multibar.Indexed.assemble`, `OAI.DerivedBar.Multibar.Indexed.inclusion`, `OAI.DerivedBar.Multibar.Indexed.outerInclusion`, `OAI.DerivedBar.Multibar.Indexed.outerRetraction`, `OAI.DerivedBar.Multibar.Indexed.retraction`, `OAI.DerivedBar.Multibar.freeBarObjIso`, `OAI.DerivedBar.Multibar.freeBarPatternIso`, `OAI.DerivedBar.Multibar.termPatternIso`, `OAI.DerivedBar.Multibar.twoSidedBarObjIso`, `OAI.DerivedBar.Multibar.twoSidedBarPatternIso`, `OAI.DerivedBar.RecursiveTotal.derivedIterateIndexedIso`, `OAI.DerivedBar.RecursiveTotal.indexedDifferential`, `OAI.DerivedBar.RecursiveTotal.indexedFlatIso`, `OAI.DerivedBar.RecursiveTotal.indexedModule`, `OAI.DerivedBar.RecursiveTotal.indexedMultibar`, `OAI.DerivedBar.RecursiveTotal.innerSummandIso`, `OAI.DerivedBar.RecursiveTotal.instModuleCarrier_solutions`, `OAI.DerivedBar.RecursiveTotal.instModuleCarrier_solutions_1`, `OAI.DerivedBar.RecursiveTotal.instModuleCarrier_solutions_2`, `OAI.DerivedBar.RecursiveTotal.leadingSummandIso` and 33 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Bar_BarAdditive`, `Finitistic_Bar_BarBimoduleCongruence`, `Finitistic_Bar_IndexedMultibarTotal`, `Finitistic_Bar_IntegerDerivedMultibar`, `Finitistic_Bar_LiteralMultibarCoordinates`, `Finitistic_Bar_ModuleMultibarCoordinates`, `Finitistic_Bar_MultibarDecomposition`, `Finitistic_Bar_MultibarFlattenDerived`, `Finitistic_Bar_MultibarSigns`, `Finitistic_Bar_PatternTensorCoherence`, `Finitistic_Bar_TotalBar`, `Finitistic_Bar_TotalBarComparison`, `Finitistic_Bar_TotalBarContraction`, `Finitistic_Bar_TotalBarDerived`, `Finitistic_Bar_TotalBarFunctor`, `Finitistic_Bar_TotalBarResolution`, `Finitistic_Bar_TotalBarTensor`, `Finitistic_Bar_TwoSided`, `Finitistic_Bar_TwoSidedBarFunctor`, `Finitistic_Bar_TwoSidedWeight`, `Finitistic_Bar_Weight`, `Finitistic_Bimodule_BimoduleBar`, `Finitistic_Bimodule_BimoduleComparison`, `Finitistic_Bimodule_BimoduleDerived`, `Finitistic_Bimodule_BimoduleTensor`, `Finitistic_Encoding_PathBasisIso`, `Finitistic_Encoding_QuadraticEncoding`, `Finitistic_Iteration_IntegerIterateAmplitude`, `Finitistic_Iteration_IntegerIterateSupport`, `Finitistic_Rectification_VertexFunctor`.
--
--   **Imports.** It imports the bundles `OAIQ023F000` and `OAIQ023F001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F010`, `OAIQ023F011`, `OAIQ023F012` and `OAIQ023F013`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ023F000
import Definitions.Def_OAIQ023F001

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TwoSided
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK
attribute [-simp] _root_.OAI.DerivedBar.Balanced.collapse_tmul _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory
noncomputable section

namespace DerivedBar
namespace FreeBaseChange
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (V W U : Type u) [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]

/-- Extension commutes with the map on arbitrary free tensors, not just generators. -/
theorem map_coefficient (h : A ⊗[k] V →ₗ[A] A ⊗[k] W) (z : A ⊗[k] V) :
    map f V W h (coefficient f V z) = coefficient f W (h z) := by
  induction z using OAI.tensorInductionOn with
  | tmul a v =>
    rw [coefficient_tmul, map_tmul]
    have hz : a ⊗ₜ[k] v = a • ((1 : A) ⊗ₜ[k] v) := by
      simp [TensorProduct.smul_tmul']
    rw [hz, h.map_smul, coefficient_smul]
  | add x y hx hy => simp_all

/-- Composition of actual free-module maps is preserved by extension. -/
theorem map_comp (h : A ⊗[k] V →ₗ[A] A ⊗[k] W)
    (g : A ⊗[k] W →ₗ[A] A ⊗[k] U) :
    map f V U (g.comp h) = (map f W U g).comp (map f V W h) := by
  apply AlgebraTensorModule.ext
  intro d v
  change d • coefficient f U (g (h (1 ⊗ₜ[k] v))) =
    map f W U g (d • coefficient f W (h (1 ⊗ₜ[k] v)))
  rw [LinearMap.map_smul, map_coefficient]

@[simp] theorem map_zero : map f V W 0 = 0 := by
  apply AlgebraTensorModule.ext
  intro d v
  simp only [map_tmul, LinearMap.zero_apply, _root_.map_zero, smul_zero]

@[simp] theorem map_id : map f V V LinearMap.id = LinearMap.id := by
  apply AlgebraTensorModule.ext
  intro d v
  simp [map_tmul, TensorProduct.smul_tmul']

end FreeBaseChange

universe u
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct
noncomputable section

namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [IsScalarTower k D X]
variable (V : Type u) [AddCommGroup V] [Module k V] [Module D V] [IsScalarTower k D V]

variable [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X]

variable (W : Type u) [AddCommGroup W] [Module k W]

theorem descend_insert : (descend k D X W).comp (insert k D X W) = LinearMap.id := by
  apply AlgebraTensorModule.ext
  intro x w
  simp only [LinearMap.comp_apply, insert_tmul, descend_quotient, collapse_tmul,
    MulOpposite.op_one, one_smul, LinearMap.id_apply]

/-- Genuine X ⊗_D (D ⊗_k W) ≅ X ⊗_k W, with no flatness of X. -/
def freeEquiv : tensor k D X (D ⊗[k] W) ≃ₗ[D] X ⊗[k] W :=
  LinearEquiv.ofLinearMap (descend k D X W) (insert k D X W)
    (descend_insert k D X W) (insert_descend k D X W)
end DerivedBar.BimoduleTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBar
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory
noncomputable section

namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

variable (N : Type u) [AddCommGroup N] [Module k N] [Module D N] [IsScalarTower k D N]

/-- Balanced X tensor of the actual free projective resolution of N. -/
def tensorResolution : ChainComplex (ModuleCat D) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of D (tensor k D X (DerivedBar.term k D N (n+1))))
    (fun n => ModuleCat.ofHom (map k D X _ _ (DerivedBar.differential k D N (n+1))))
    (fun n => by
      apply ModuleCat.hom_ext
      change (map k D X _ _ (DerivedBar.differential k D N (n+1))).comp
        (map k D X _ _ (DerivedBar.differential k D N (n+1+1))) = 0
      rw [← map_comp, DerivedBar.differential_sq, map_zero])

/-- The explicit two-sided bar is isomorphic to genuine balanced tensor of the free resolution. -/
def tensorResolutionIso : tensorResolution k D X N ≅ barComplex k D X N :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (freeEquiv k D X (DerivedBar.term k D N n)).toModuleIso)
    (by
      intro i j hij
      change j+1 = i at hij
      subst i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      simp only [tensorResolution, barComplex, ChainComplex.of_d,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        LinearEquiv.toModuleIso_hom]
      exact freeMap_descend k D X (DerivedBar.term k D N (j+1))
        (DerivedBar.term k D N j) (DerivedBar.differential k D N (j+1)) z)
end DerivedBar.BimoduleTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleDerived
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory
noncomputable section

namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

attribute [local instance] OAI.DerivedBar.BimoduleTensor.instModuleCarrier_solutions
attribute [local instance] OAI.DerivedBar.BimoduleTensor.instIsScalarTowerCarrier_solutions
/-- Tensor of X with the verified absolute bar projective resolution.
This construction applies the genuine balanced functor to every differential. -/
def resolvedTensor (N : ModuleCat.{u} D) : ChainComplex (ModuleCat.{u} D) ℕ :=
  ((tensorFunctor k D X).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (DerivedBar.projectiveResolution k D N).complex

end DerivedBar.BimoduleTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleComparison
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI
open CategoryTheory
noncomputable section

namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- Coherence between the categorical tensor functor and the literal balancing quotient. -/
def tensorFunctorObjIso (V : Type u) [AddCommGroup V] [Module k V]
    [Module D V] [IsScalarTower k D V] :
    (tensorFunctor k D X).obj (ModuleCat.of D V) ≅ ModuleCat.of D (tensor k D X V) := by
  have h := scalarModule_eq k D V
  cases h
  exact Iso.refl _

omit [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X] in
/-- The scalar-action coherence is natural for every D-linear map. -/
theorem tensorFunctorObjIso_natural (V W : Type u)
    [AddCommGroup V] [Module k V] [Module D V] [IsScalarTower k D V]
    [AddCommGroup W] [Module k W] [Module D W] [IsScalarTower k D W]
    (h : V →ₗ[D] W) :
    (tensorFunctor k D X).map (ModuleCat.ofHom h) ≫ (tensorFunctorObjIso k D X W).hom =
      (tensorFunctorObjIso k D X V).hom ≫ ModuleCat.ofHom (map k D X V W h) := by
  have hV := scalarModule_eq k D V
  have hW := scalarModule_eq k D W
  cases hV
  cases hW
  rfl

local instance instModuleCarrier_solutions_1 (V : ModuleCat.{u} D) : Module k V := scalarModule k D V
local instance instIsScalarTowerCarrier_solutions_1 (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- The categorical derived-resolution model and the explicit balanced bar complex agree. -/
def resolvedTensorIso (N : ModuleCat.{u} D) :
    resolvedTensor k D X N ≅ tensorResolution k D X N :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => tensorFunctorObjIso k D X (DerivedBar.term k D N (n+1)))
    (by
      intro i j hij
      change j+1 = i at hij
      subst i
      simpa only [tensorResolution, resolvedTensor, DerivedBar.projectiveResolution,
        DerivedBar.complex, ChainComplex.of_d, Functor.mapHomologicalComplex_obj_d] using (tensorFunctorObjIso_natural k D X (DerivedBar.term k D N (j+1+1))
        (DerivedBar.term k D N (j+1)) (DerivedBar.differential k D N (j+1))).symm)

end DerivedBar.BimoduleTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TwoSidedBarFunctor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory TensorProduct
open scoped TensorProduct
noncomputable section
namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local notation "c" => ComplexShape.down ℕ

attribute [local instance] OAI.DerivedBar.BimoduleTensor.instModuleCarrier_solutions_2
attribute [local instance] OAI.DerivedBar.BimoduleTensor.instIsScalarTowerCarrier_solutions_2
/-- The component comparison to the explicit two-sided bar. -/
def freeBarTensorIso (N : ModuleCat.{u} D) :
    ((barFunctor k D ⋙ (tensorFunctor k D X).mapHomologicalComplex c).obj N) ≅
      barComplex k D X N :=
  resolvedTensorIso k D X N ≪≫ tensorResolutionIso k D X N

/-- The two-sided bar map is defined on literal tensor coordinates. -/
def twoSidedBarMap {V W : ModuleCat.{u} D} (f : V ⟶ W) :
    barComplex k D X V ⟶ barComplex k D X W where
  f n := ModuleCat.ofHom (barTermMap k D X f n)
  comm' i j hij := by
    change j+1=i at hij
    subst i
    apply ModuleCat.hom_ext
    simpa only [barComplex, ChainComplex.of_d, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
      using! barDifferential_natural k D X f j

/-- A functor with both maps and differential defined on the explicit bar tensors. -/
def twoSidedBarFunctor : ModuleCat.{u} D ⥤ ChainComplex (ModuleCat.{u} D) ℕ where
  obj N := barComplex k D X N
  map f := twoSidedBarMap k D X f
  map_id N := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply AlgebraTensorModule.ext
    intro x v
    change x ⊗ₜ[k] termMap k D N N LinearMap.id n v = x ⊗ₜ[k] v
    rw [termMap_id]; rfl
  map_comp {V W U} f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply AlgebraTensorModule.ext
    intro x v
    change x ⊗ₜ[k] termMap k D V U (g.hom.comp f.hom) n v =
      x ⊗ₜ[k] termMap k D W U g.hom n (termMap k D V W f.hom n v)
    rw [termMap_comp]; rfl

instance twoSidedBarFunctor_preservesZero : (twoSidedBarFunctor k D X).PreservesZeroMorphisms where
  map_zero V W := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply AlgebraTensorModule.ext
    intro x v
    change x ⊗ₜ[k] termMap k D V W 0 n v = 0
    rw [termMap_zero, LinearMap.zero_apply, TensorProduct.tmul_zero]

/-- Natural comparison, preserving the exterior D-action. -/
def freeBarTensorNatIso :
    barFunctor k D ⋙ (tensorFunctor k D X).mapHomologicalComplex c ≅
      twoSidedBarFunctor k D X :=
  NatIso.ofComponents (freeBarTensorIso k D X) (by
    intro V W f
    apply HomologicalComplex.Hom.ext
    funext n
    change (tensorFunctor k D X).map (ModuleCat.ofHom (termMap k D V W f.hom (n+1))) ≫
        (tensorFunctorObjIso k D X (term k D W (n+1))).hom ≫
        (freeEquiv k D X (term k D W n)).toModuleIso.hom =
      (tensorFunctorObjIso k D X (term k D V (n+1))).hom ≫
        (freeEquiv k D X (term k D V n)).toModuleIso.hom ≫
        ModuleCat.ofHom (barTermMap k D X f n)
    rw [← Category.assoc, tensorFunctorObjIso_natural, Category.assoc]
    congr 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (freeMap_termMap k D X f n ▸
      freeMap_descend k D X (term k D V n) (term k D W n)
        (termMap k D V W f.hom (n+1)) z).symm)

/-- The literal two-sided bar bicomplex of an arbitrary nonnegative chain input. -/
def twoSidedBarBicomplex (Z : ChainComplex (ModuleCat.{u} D) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} D) c c :=
  HomologicalComplex₂.flip (((twoSidedBarFunctor k D X).mapHomologicalComplex c).obj Z)

end DerivedBar.BimoduleTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_BarAdditive
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory TensorProduct
open scoped TensorProduct
noncomputable section
namespace DerivedBar
universe u
variable (k D : Type u) [Field k] [Ring D] [Algebra k D]
variable (V W : Type u) [AddCommGroup V] [Module k V] [Module D V] [IsScalarTower k D V]
  [AddCommGroup W] [Module k W] [Module D W] [IsScalarTower k D W]

/-- Each iterated free bar term preserves addition of maps. -/
theorem termMap_add (f g : V →ₗ[D] W) (n : ℕ) :
    termMap k D V W (f+g) n = termMap k D V W f n + termMap k D V W g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply AlgebraTensorModule.ext
    intro d v
    change d ⊗ₜ[k] termMap k D V W (f+g) n v =
      d ⊗ₜ[k] termMap k D V W f n v + d ⊗ₜ[k] termMap k D V W g n v
    rw [ih, LinearMap.add_apply, TensorProduct.tmul_add]

local instance barAdditiveScalarModule (N : ModuleCat.{u} D) : Module k N :=
  BimoduleTensor.scalarModule k D N
local instance barAdditiveScalarTower (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

instance barFunctor_additive : (barFunctor k D).Additive where
  map_add := by
    intro V W f g
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    exact termMap_add k D V W f.hom g.hom (n+1)

namespace BimoduleTensor
variable (X : Type u) [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

instance twoSidedBarFunctor_additive : (twoSidedBarFunctor k D X).Additive where
  map_add := by
    intro V W f g
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply AlgebraTensorModule.ext
    intro x v
    change x ⊗ₜ[k] termMap k D V W (f.hom+g.hom) n v =
      x ⊗ₜ[k] termMap k D V W f.hom n v + x ⊗ₜ[k] termMap k D V W g.hom n v
    rw [termMap_add, LinearMap.add_apply, TensorProduct.tmul_add]
end BimoduleTensor
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TotalBar
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
noncomputable section
namespace DerivedBar
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]

/-- Total terms are projective for every nonnegative input, without projectivity
or flatness assumptions on the input terms. -/
instance barTotal_projective (Z : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    Projective ((barTotal k A Z).X n) where
  factors f e he := by
    dsimp only [barTotal] at f ⊢
    refine ⟨(barBicomplex k A Z).totalDesc
      (fun i q h => Projective.factorThru
        ((barBicomplex k A Z).ιTotal _ i q n h ≫ f) e), ?_⟩
    apply HomologicalComplex₂.total.hom_ext
    intro i q h
    simp

end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TotalBarContraction
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.DerivedBar.SquareZero.projection_base _root_.OAI.DerivedBar.SquareZero.projection_ideal_succ _root_.OAI.DerivedBar.SquareZero.projection_ideal_zero _root_.OAI.DerivedBar.SquareZero.twoSidedProjection_tmul _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
noncomputable section
namespace DerivedBar
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Z : ChainComplex (ModuleCat.{u} A) ℕ)
local notation "B" => barBicomplex k A Z
local notation "T" => barTotal k A Z
local notation "c" => ComplexShape.down ℕ
local notation "F" => moduleForgetAdd A

attribute [local instance] OAI.DerivedBar.instModuleCarrier_solutions_2
attribute [local instance] OAI.DerivedBar.instIsScalarTowerCarrier_solutions_2
/-- The additive section commutes with the input differential. -/
theorem barTotalSectionF_comm (n : ℕ) :
    barTotalSectionF k A Z (n+1) ≫ (F).map ((T).d (n+1) n) =
      (F).map (Z.d (n+1) n) ≫ barTotalSectionF k A Z n := by
  dsimp only [barTotal]
  dsimp only [barTotalSectionF]
  erw [Category.assoc, ← Functor.map_comp]
  simp only [barTotal, HomologicalComplex₂.total_d, comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    barTotal_d₁_zero, zero_add]
  erw [barTotal_d₂_succ k A Z 0 n n (by omega)]
  simp only [pow_zero, one_smul]
  erw [Functor.map_comp, ← Category.assoc, ← barUnit_natural]

/-- The row contraction identity, expressed in additive maps. -/
theorem barUnit_identity (i q : ℕ) :
    barUnit k A Z (i+1) q ≫ (F).map (ModuleCat.ofHom (differential k A (Z.X q) (i+1))) +
      (F).map (ModuleCat.ofHom (differential k A (Z.X q) i)) ≫ barUnit k A Z i q = 𝟙 _ := by
  ext x
  exact contraction_identity k A (Z.X q) i x

/-- The vertical contributions cancel because unit insertion changes bar parity. -/
theorem barTotal_vertical_cancel (i q n : ℕ) (h : i+q=n) :
    barTotalDV k A Z i (q+1) n ≫ barTotalH k A Z n +
      barRaise k A Z i (q+1) ≫ barTotalDV k A Z (i+1) (q+1) (n+1) = 0 := by
  dsimp only [barTotalDV]
  erw [barTotal_d₂_succ k A Z i q n h,
    barTotal_d₂_succ k A Z (i+1) q (n+1) (by omega)]
  erw [Functor.map_units_smul, Functor.map_units_smul,
    Functor.map_comp, Functor.map_comp, Linear.units_smul_comp,
    Linear.comp_units_smul, Category.assoc, ι_barTotalH]
  dsimp only [barRaise]
  erw [barUnit_natural_assoc]
  erw [pow_succ, mul_neg_one, Units.neg_smul, add_neg_cancel]

/-- Total contraction equation in degree zero. -/
theorem barTotalH_identity_zero :
    barTotalH k A Z 0 ≫ (F).map ((T).d 1 0) +
      (F).map ((barTotalAugmentation k A Z).f 0) ≫ barTotalSectionF k A Z 0 = 𝟙 _ := by
  dsimp only [barTotal]
  apply totalAdd_hom_ext B
  intro i q h
  have hi : i=0 := by omega
  have hq : q=0 := by omega
  subst i q
  erw [comp_add, ← Category.assoc, ι_barTotalH]
  erw [Category.assoc, ι_barTotal_d]
  dsimp only [barTotalDH, barTotalDV]
  erw [barTotal_d₁_succ k A Z 0 0 0 rfl, barTotal_d₂_zero]
  erw [Functor.map_zero, add_zero, Functor.map_comp]
  have ha : (F).map ((B).ιTotal c 0 0 0 h) ≫
      (F).map ((barTotalAugmentation k A Z).f 0) =
        (F).map (ModuleCat.ofHom (differential k A (Z.X 0) 0)) := by
    erw [← Functor.map_comp]
    change (F).map (_ ≫ barTotalAugmentationF k A Z 0) = _
    erw [ι_barTotalAugmentationF_zero]
    simp
    rfl
  erw [← Category.assoc ((F).map ((B).ιTotal c 0 0 0 h))
    ((F).map ((barTotalAugmentation k A Z).f 0)) (barTotalSectionF k A Z 0), ha]
  dsimp only [barTotalSectionF]
  erw [← Category.assoc]
  dsimp only [barRaise]
  erw [← Category.assoc, ← add_comp, barUnit_identity]
  ext x
  rfl

theorem barTotal_horizontal_identity (n i q : ℕ) (h : i+q=n+1) :
    barTotalDH k A Z i q n ≫ barTotalH k A Z n +
      barRaise k A Z i q ≫ barTotalDH k A Z (i+1) q (n+1) +
      (F).map ((B).ιTotal c i q (n+1) h) ≫
        (F).map ((barTotalAugmentation k A Z).f (n+1)) ≫
          barTotalSectionF k A Z (n+1) = (F).map ((B).ιTotal c i q (n+1) h) := by
  dsimp only [barTotalDH]
  erw [barTotal_d₁_succ k A Z i q (n+1) h]
  cases i with
  | zero =>
    have hq : q=n+1 := by omega
    subst q
    erw [barTotal_d₁_zero, Functor.map_zero, zero_comp, zero_add,
      Functor.map_comp]
    dsimp only [barTotalAugmentation]
    erw [← Functor.map_comp_assoc (F) ((B).ιTotal c 0 (n+1) (n+1) h)
      (barTotalAugmentationF k A Z (n+1)) (barTotalSectionF k A Z (n+1))]
    erw [ι_barTotalAugmentationF_zero]
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
    dsimp only [barTotalSectionF]
    erw [← Category.assoc]
    dsimp only [barRaise]
    erw [← Category.assoc, ← add_comp, barUnit_identity]
    ext x
    rfl
  | succ i =>
    erw [barTotal_d₁_succ k A Z i q n (by omega)]
    erw [Functor.map_comp, Functor.map_comp, Category.assoc,
      ι_barTotalH k A Z i q n (by omega)]
    dsimp only [barTotalAugmentation]
    erw [← Functor.map_comp_assoc (F) ((B).ιTotal c (i+1) q (n+1) h)
      (barTotalAugmentationF k A Z (n+1)) (barTotalSectionF k A Z (n+1))]
    erw [ι_barTotalAugmentationF_succ k A Z i q (n+1) h]
    erw [Functor.map_zero, zero_comp, add_zero, ← Category.assoc, ← Category.assoc]
    dsimp only [barRaise]
    erw [← add_comp]
    ext x
    exact congrArg ((F).map ((B).ιTotal c (i+1) q (n+1) h)).hom
      ((add_comm _ _).trans (contraction_identity k A (Z.X q) (i+1) x))

/-- Total contraction equation in every positive degree. -/
theorem barTotalH_identity_succ (n : ℕ) :
    (F).map ((T).d (n+1) n) ≫ barTotalH k A Z n +
      barTotalH k A Z (n+1) ≫ (F).map ((T).d (n+2) (n+1)) +
      (F).map ((barTotalAugmentation k A Z).f (n+1)) ≫
        barTotalSectionF k A Z (n+1) = 𝟙 _ := by
  dsimp only [barTotal]
  apply totalAdd_hom_ext B
  intro i q h
  have hv : barTotalDV k A Z i q n ≫ barTotalH k A Z n +
      barRaise k A Z i q ≫ barTotalDV k A Z (i+1) q (n+1) = 0 := by
    cases q with
    | zero =>
      dsimp only [barTotalDV]
      erw [barTotal_d₂_zero, barTotal_d₂_zero, Functor.map_zero,
        Functor.map_zero, zero_comp, comp_zero, add_zero]
    | succ q => exact barTotal_vertical_cancel k A Z i q n (by omega)
  have hh := barTotal_horizontal_identity k A Z n i q h
  erw [comp_add, comp_add, ← Category.assoc, ← Category.assoc,
    ι_barTotalH k A Z i q (n+1) h]
  erw [ι_barTotal_d, Category.assoc, ι_barTotal_d, add_comp, comp_add]
  calc
    _ = (barTotalDH k A Z i q n ≫ barTotalH k A Z n +
        barRaise k A Z i q ≫ barTotalDH k A Z (i+1) q (n+1) +
        (F).map ((B).ιTotal c i q (n+1) h) ≫
          (F).map ((barTotalAugmentation k A Z).f (n+1)) ≫
            barTotalSectionF k A Z (n+1)) +
      (barTotalDV k A Z i q n ≫ barTotalH k A Z n +
        barRaise k A Z i q ≫ barTotalDV k A Z (i+1) q (n+1)) :=
      add_interleave _ _ _ _ _
    _ = _ := by
      erw [hh, hv, add_zero]
      ext x
      rfl
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TotalBarResolution
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace DerivedBar
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Z : ChainComplex (ModuleCat.{u} A) ℕ)
local notation "c" => ComplexShape.down ℕ
local notation "P" => CategoryTheory.Functor.obj
  (CategoryTheory.Functor.mapHomologicalComplex (moduleForgetAdd A) (ComplexShape.down ℕ)) (barTotal k A Z)
local notation "Q" => CategoryTheory.Functor.obj
  (CategoryTheory.Functor.mapHomologicalComplex (moduleForgetAdd A) (ComplexShape.down ℕ)) Z
local notation "π" => CategoryTheory.Functor.map
  (CategoryTheory.Functor.mapHomologicalComplex (moduleForgetAdd A) (ComplexShape.down ℕ)) (barTotalAugmentation k A Z)

/-- Unit insertion is an actual additive chain section of the total augmentation. -/
def barTotalSection : Q ⟶ P where
  f := barTotalSectionF k A Z
  comm' i j h := by
    change j+1=i at h
    subst i
    exact barTotalSectionF_comm k A Z j

/-- The explicit additive contraction, with its degree condition. -/
def barTotalHomotopy : Homotopy (𝟙 P) (π ≫ barTotalSection k A Z) where
  hom i j := if h : i+1=j then barTotalH k A Z i ≫ ((P).XIsoOfEq h).hom else 0
  zero i j h := by
    change ¬ i+1=j at h
    exact dite_eq_right h
  comm i := by
    rw [prevD_eq _ (by rfl : (c).Rel (i+1) i)]
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
    cases i with
    | zero =>
      rw [dNext_eq_zero _ 0 (by simp), zero_add]
      exact (barTotalH_identity_zero k A Z).symm
    | succ n =>
      rw [dNext_eq _ (by rfl : (c).Rel (n+1) n)]
      simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
      exact (barTotalH_identity_succ k A Z n).symm

/-- The total augmentation is a homotopy equivalence after forgetting the A-action.
The inverse and homotopy are explicit unit insertions, not A-linear splittings. -/
def barTotalAdditiveEquiv : HomotopyEquiv P Q where
  hom := π
  inv := barTotalSection k A Z
  homotopyHomInvId := (barTotalHomotopy k A Z).symm
  homotopyInvHomId := Homotopy.ofEq (by
    apply HomologicalComplex.Hom.ext
    funext n
    exact barTotalSectionF_augmentation k A Z n)

/-- The actual D-linear total-bar augmentation is a quasi-isomorphism for every
nonnegative chain input; neither projectivity nor flatness of the input is assumed. -/
instance barTotalAugmentation_quasiIso : QuasiIso (barTotalAugmentation k A Z) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (barTotalAugmentation k A Z) (moduleForgetAdd A)]
  exact (barTotalAdditiveEquiv k A Z).quasiIso_hom

end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TotalBarFunctor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.barFunctor_additive _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace DerivedBar
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
local notation "c" => ComplexShape.down ℕ

attribute [local instance] OAI.DerivedBar.instModuleCarrier_solutions_3
attribute [local instance] OAI.DerivedBar.instIsScalarTowerCarrier_solutions_3
/-- The augmentation is natural for all chain maps, not only quasi-isomorphisms. -/
def barTotalAugmentationNat : barTotalFunctor k A ⟶ 𝟭 _ where
  app Z := barTotalAugmentation k A Z
  naturality {Z W} f := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply HomologicalComplex₂.total.hom_ext (K := barBicomplex k A Z)
    intro i q h
    change i+q=n at h
    change (barBicomplex k A Z).ιTotal c i q n h ≫ ((barTotalFunctor k A).map f).f n ≫ barTotalAugmentationF k A W n =
      (barBicomplex k A Z).ιTotal c i q n h ≫ barTotalAugmentationF k A Z n ≫ f.f n
    erw [ι_barTotalFunctor_map_assoc]
    cases i with
    | zero =>
      have hq : q=n := by omega
      subst q
      erw [Category.assoc, augmentation_zero_diagonal k A W n h,
        ← Category.assoc, augmentation_zero_diagonal k A Z n h]
      exact ModuleCat.hom_ext (differential_natural k A (Z.X n) (W.X n) (f.f n).hom 0)
    | succ i =>
      erw [Category.assoc, ι_barTotalAugmentationF_succ k A W i q n h,
        ← Category.assoc, ι_barTotalAugmentationF_succ k A Z i q n h]
      simp only [zero_comp]
      exact comp_zero
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TotalBarTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
namespace DerivedBar
universe u
variable (k D : Type u) [Field k] [Ring D] [Algebra k D]

/-- Resolving a quasi-isomorphism gives a quasi-isomorphism between projective complexes. -/
instance barTotalFunctor_map_quasiIso {Z W : ChainComplex (ModuleCat.{u} D) ℕ}
    (f : Z ⟶ W) [QuasiIso f] : QuasiIso ((barTotalFunctor k D).map f) := by
  apply (quasiIso_iff_comp_right (K := barTotal k D Z) (L := barTotal k D W)
    ((barTotalFunctor k D).map f) (barTotalAugmentation k D W)).mp
  erw [(barTotalAugmentationNat k D).naturality f]
  exact inferInstanceAs (QuasiIso (barTotalAugmentation k D Z ≫ f))

variable (X : Type u) [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- The resolved tensor construction preserves all quasi-isomorphisms. -/
instance tensorTotalFunctor_map_quasiIso {Z W : ChainComplex (ModuleCat.{u} D) ℕ}
    (f : Z ⟶ W) [QuasiIso f] : QuasiIso ((tensorTotalFunctor k D X).map f) := by
  let : ∀ n, Projective (((barTotalFunctor k D).obj Z).X n) := barTotal_projective k D Z
  let : ∀ n, Projective (((barTotalFunctor k D).obj W).X n) := barTotal_projective k D W
  exact additive_map_quasiIso_of_projective D (BimoduleTensor.tensorFunctor k D X)
    ((barTotalFunctor k D).map f)

/-- Repeated resolution and balanced tensor, proceeding from the right as in Section 6.
The identification with the independently signed literal multibar is a separate obligation. -/
def tensorTotalIterate : ℕ → (ChainComplex (ModuleCat.{u} D) ℕ ⥤ ChainComplex (ModuleCat.{u} D) ℕ)
  | 0 => 𝟭 _
  | r+1 => tensorTotalIterate r ⋙ tensorTotalFunctor k D X

end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TotalBarComparison
attribute [-instance] _root_.OAI.DerivedBar.BimoduleTensor.twoSidedBarFunctor_additive _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.barFunctor_additive _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Preadditive
open scoped TensorProduct
noncomputable section
namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local notation "c" => ComplexShape.down ℕ

/-- The termwise balanced/free comparison is an isomorphism of bicomplexes. -/
def tensorBarBicomplexIso (Z : ChainComplex (ModuleCat.{u} D) ℕ) :
    mapBicomplex (tensorFunctor k D X) (barBicomplex k D Z) ≅
      twoSidedBarBicomplex k D X Z :=
  (HomologicalComplex₂.flipFunctor _ c c).mapIso
    ((NatIso.mapHomologicalComplex (freeBarTensorNatIso k D X) c).app Z)

/-- The explicit two-sided total bar on a nonnegative chain complex. -/
def explicitBarTotal (Z : ChainComplex (ModuleCat.{u} D) ℕ) :
    ChainComplex (ModuleCat.{u} D) ℕ :=
  (twoSidedBarBicomplex k D X Z).total c

/-- Resolving the whole input and applying balanced tensor gives precisely the
explicit two-sided bar total. Finite diagonal sums suffice; X need not be flat. -/
def tensorTotalExplicitIso (Z : ChainComplex (ModuleCat.{u} D) ℕ) :
    (tensorTotalFunctor k D X).obj Z ≅ explicitBarTotal k D X Z :=
  totalMapIso (tensorFunctor k D X) (barBicomplex k D Z) ≪≫
    HomologicalComplex₂.total.mapIso (tensorBarBicomplexIso k D X Z) c

@[simp] theorem explicitBarTotal_d₁_zero (Z : ChainComplex (ModuleCat.{u} D) ℕ)
    (q n : ℕ) : (twoSidedBarBicomplex k D X Z).d₁ c 0 q n = 0 := by
  apply HomologicalComplex₂.d₁_eq_zero
  simp

@[simp] theorem explicitBarTotal_d₂_zero (Z : ChainComplex (ModuleCat.{u} D) ℕ)
    (i n : ℕ) : (twoSidedBarBicomplex k D X Z).d₂ c i 0 n = 0 := by
  apply HomologicalComplex₂.d₂_eq_zero
  simp
end DerivedBar.BimoduleTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TotalBarDerived
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Functor HomologicalComplex
noncomputable section
namespace DerivedBar
universe u
variable (k D : Type u) [Field k] [Ring D] [Algebra k D]
local notation "c" => ComplexShape.down ℕ

variable (X : Type u) [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- Ordinary balanced tensor on chains followed by the quasi-isomorphism localization. -/
def ordinaryTensorToDerived : ChainComplex (ModuleCat.{u} D) ℕ ⥤ chainDerived D :=
  (BimoduleTensor.tensorFunctor k D X).mapHomologicalComplex c ⋙ chainQ D

omit [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X] in
theorem tensorTotal_inverts : (chainQuasiIso D).IsInvertedBy
    (tensorTotalFunctor k D X ⋙ chainQ D) := by
  intro Z U f hf
  have : QuasiIso f := hf
  exact Localization.inverts (chainQ D) (chainQuasiIso D) _
    (show QuasiIso ((tensorTotalFunctor k D X).map f) from inferInstance)

/-- Left derived balanced tensor on the localization of nonnegative chain complexes. -/
def derivedTensor : chainDerived D ⥤ chainDerived D :=
  Localization.lift (tensorTotalFunctor k D X ⋙ chainQ D)
    (tensorTotal_inverts k D X) (chainQ D)

def derivedTensorResolutionIso : chainQ D ⋙ derivedTensor k D X ≅
    barTotalFunctor k D ⋙ ordinaryTensorToDerived k D X :=
  Localization.fac (tensorTotalFunctor k D X ⋙ chainQ D)
    (tensorTotal_inverts k D X) (chainQ D)

/-- Genuine derived functor iteration, with the manuscript's right-to-left order. -/
def derivedTensorIterate : ℕ → (chainDerived D ⥤ chainDerived D)
  | 0 => 𝟭 _
  | r+1 => derivedTensorIterate r ⋙ derivedTensor k D X

/-- Successive resolve-and-tensor complexes represent iteration of the genuine
left derived functor. No derived comparison is included as a hypothesis. -/
def derivedTensorIterateIso : (r : ℕ) →
    chainQ D ⋙ derivedTensorIterate k D X r ≅ tensorTotalIterate k D X r ⋙ chainQ D
  | 0 => (Functor.rightUnitor _ ) ≪≫ (Functor.leftUnitor _).symm
  | r+1 =>
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (derivedTensorIterateIso r) (derivedTensor k D X) ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (tensorTotalIterate k D X r) (derivedTensorResolutionIso k D X) ≪≫
      (Functor.associator _ _ _).symm

/-- The independent recursive multibar. Every new block uses the explicit
endpoint-minus-tail horizontal differential and the standard vertical total sign. -/
def explicitMultibar : ℕ → ChainComplex (ModuleCat.{u} D) ℕ → ChainComplex (ModuleCat.{u} D) ℕ
  | 0, Z => Z
  | r+1, Z => BimoduleTensor.explicitBarTotal k D X (explicitMultibar r Z)

def iterateExplicitMultibarIso (Z : ChainComplex (ModuleCat.{u} D) ℕ) : (r : ℕ) →
    (tensorTotalIterate k D X r).obj Z ≅ explicitMultibar k D X r Z
  | 0 => Iso.refl _
  | r+1 => (tensorTotalFunctor k D X).mapIso (iterateExplicitMultibarIso Z r) ≪≫
      BimoduleTensor.tensorTotalExplicitIso k D X (explicitMultibar k D X r Z)

/-- The independent recursive multibar represents genuine finite derived iteration. -/
def derivedIterateMultibarIso (Z : ChainComplex (ModuleCat.{u} D) ℕ) (r : ℕ) :
    (derivedTensorIterate k D X r).obj ((chainQ D).obj Z) ≅
      (chainQ D).obj (explicitMultibar k D X r Z) :=
  (derivedTensorIterateIso k D X r).app Z ≪≫
    (chainQ D).mapIso (iterateExplicitMultibarIso k D X Z r)

/-- The final leading D-bar resolution leaves the represented derived iterate unchanged. -/
def derivedIterateLeadingBarIso (Z : ChainComplex (ModuleCat.{u} D) ℕ) (r : ℕ) :
    (derivedTensorIterate k D X r).obj ((chainQ D).obj Z) ≅
      (chainQ D).obj (barTotal k D (explicitMultibar k D X r Z)) := by
  have := Localization.inverts (chainQ D) (chainQuasiIso D)
    (barTotalAugmentation k D (explicitMultibar k D X r Z))
    (show QuasiIso (barTotalAugmentation k D (explicitMultibar k D X r Z)) from inferInstance)
  exact derivedIterateMultibarIso k D X Z r ≪≫
    (asIso ((chainQ D).map (barTotalAugmentation k D (explicitMultibar k D X r Z)))).symm
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_BarBimoduleCongruence
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Functor TensorProduct
open scoped TensorProduct
namespace DerivedBar.BimoduleTensor
universe u
variable (k D : Type u) [Field k] [Ring D] [Algebra k D]
variable {X Y : Type u}
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup Y] [Module k Y] [Module D Y] [Module Dᵐᵒᵖ Y]
  [SMulCommClass D Dᵐᵒᵖ Y] [IsScalarTower k D Y] [IsScalarTower k Dᵐᵒᵖ Y]
variable (e : X ≃ₗ[D] Y) (he : ∀ d : Dᵐᵒᵖ, ∀ x, e (d • x) = d • e x)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module D V] [IsScalarTower k D V]

/-- The same actual tensor equivalence descends to the genuine bar-derived functor. -/
def derivedTensorCongr : derivedTensor k D X ≅ derivedTensor k D Y :=
  (Localization.fullyFaithfulWhiskeringLeft (chainQ D) (chainQuasiIso D) (chainDerived D)).preimageIso
    (derivedTensorResolutionIso k D X ≪≫
      isoWhiskerLeft (barTotalFunctor k D)
        (isoWhiskerRight (NatIso.mapHomologicalComplex (tensorFunctorCongr k D e he) (.down ℕ)) (chainQ D)) ≪≫
      (derivedTensorResolutionIso k D Y).symm)

/-- All finite genuine iterations are compatible with the original bimodule equivalence. -/
def derivedIterateCongr : (r : ℕ) → derivedTensorIterate k D X r ≅ derivedTensorIterate k D Y r
  | 0 => Iso.refl _
  | r+1 => isoWhiskerRight (derivedIterateCongr r) (derivedTensor k D X) ≪≫
      isoWhiskerLeft (derivedTensorIterate k D Y r) (derivedTensorCongr k D e he)
end DerivedBar.BimoduleTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_MultibarFlattenDerived
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory
noncomputable section
namespace DerivedBar
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- The actual sequence of two-sided X bars, ending in one leading free D bar. -/
def leadingBarSequence (r j : ℕ) :
    ModuleCat.{u} D ⥤ ChainComplex (ModuleCat.{u} D) ℕ :=
  if j < r then BimoduleTensor.twoSidedBarFunctor k D X else barFunctor k D

instance leadingBarSequence_additive (r j : ℕ) :
    (leadingBarSequence k D X r j).Additive := by
  unfold leadingBarSequence
  split <;> infer_instance

variable (Z : ChainComplex (ModuleCat.{u} D) ℕ)

/-- Before the final D bar, the actual recursive complexes agree. -/
theorem leadingBarSequence_prefix (r n : ℕ) (h : n ≤ r) :
    RecursiveTotal.iter (leadingBarSequence k D X r) Z n = explicitMultibar k D X n Z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : n < r := by omega
    simp only [RecursiveTotal.iter, RecursiveTotal.bicomplex, leadingBarSequence,
      ite_eq_left hn, ih (by omega), explicitMultibar,
      BimoduleTensor.explicitBarTotal, BimoduleTensor.twoSidedBarBicomplex]

/-- The final recursive total is precisely the manuscript's leading D bar. -/
theorem leadingBarSequence_total (r : ℕ) :
    RecursiveTotal.iter (leadingBarSequence k D X r) Z (r+1) =
      barTotal k D (explicitMultibar k D X r Z) := by
  simp only [RecursiveTotal.iter, RecursiveTotal.bicomplex, leadingBarSequence,
    lt_self_iff_false, ite_false, if_false, leadingBarSequence_prefix k D X Z r r le_rfl,
    barTotal, barBicomplex]

/-- Literal finite direct sums, equipped with the independently recursive bar
faces. No count differential or derived comparison is used in this definition. -/
def flatLeadingMultibar (r : ℕ) : ChainComplex (ModuleCat.{u} D) ℕ :=
  RecursiveTotal.flatComplex (leadingBarSequence k D X r) Z (r+1)

/-- Chain isomorphism distributing all recursive X and leading-D totals. -/
def flatLeadingMultibarIso (r : ℕ) : flatLeadingMultibar k D X Z r ≅
    barTotal k D (explicitMultibar k D X r Z) :=
  RecursiveTotal.flattenChainIso (leadingBarSequence k D X r) Z (r+1) ≪≫
    eqToIso (leadingBarSequence_total k D X Z r)

/-- The flattened complex represents actual finite iteration of the constructed
left derived tensor. This uses the previously proved derived universal property. -/
def derivedIterateFlatIso (r : ℕ) :
    (derivedTensorIterate k D X r).obj ((chainQ D).obj Z) ≅
      (chainQ D).obj (flatLeadingMultibar k D X Z r) :=
  derivedIterateLeadingBarIso k D X Z r ≪≫
    (chainQ D).mapIso (flatLeadingMultibarIso k D X Z r).symm
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_Weight
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar
namespace SquareZero
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

/-- (TrivSqZeroExt D X) pure bar word with precisely r factors in the square-zero ideal. -/
inductive Word : (n r : ℕ) → term k (TrivSqZeroExt D X) N n → Prop
  | nil (v : N) : Word 0 0 v
  | base {n r : ℕ} {v : term k (TrivSqZeroExt D X) N n} (d : D) (h : Word n r v) :
      Word (n+1) r ((inl d : (TrivSqZeroExt D X)) ⊗ₜ[k] v)
  | ideal {n r : ℕ} {v : term k (TrivSqZeroExt D X) N n} (x : X) (h : Word n r v) :
      Word (n+1) (r+1) ((inr x : (TrivSqZeroExt D X)) ⊗ₜ[k] v)

/-- The homogeneous subspace, defined by actual tensors rather than formal signs. -/
def weight (n r : ℕ) : Submodule k (term k (TrivSqZeroExt D X) N n) :=
  Submodule.span k {v | Word k D X N n r v}

variable {k D X N}

theorem base_tmul_mem {n r : ℕ} (d : D) {v : term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ weight k D X N n r) :
    (inl d : (TrivSqZeroExt D X)) ⊗ₜ[k] v ∈ weight k D X N (n+1) r :=
  map_span_mem k (TensorProduct.mk k (TrivSqZeroExt D X) (term k (TrivSqZeroExt D X) N n) (inl d)) _ _
    (fun _ h => Submodule.subset_span (Word.base d h)) hv

theorem ideal_tmul_mem {n r : ℕ} (x : X) {v : term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ weight k D X N n r) :
    (inr x : (TrivSqZeroExt D X)) ⊗ₜ[k] v ∈ weight k D X N (n+1) (r+1) :=
  map_span_mem k (TensorProduct.mk k (TrivSqZeroExt D X) (term k (TrivSqZeroExt D X) N n) (inr x)) _ _
    (fun _ h => Submodule.subset_span (Word.ideal x h)) hv

end SquareZero
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_TwoSidedWeight
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar.SquareZero
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

/-- Count-r submodule of the two-sided bar term, with the leading D coefficient uncounted. -/
def twoSidedWeight (n r : ℕ) : Submodule D (D ⊗[k] term k (TrivSqZeroExt D X) N n) :=
  Submodule.span D {w | ∃ (d : D) (v : term k (TrivSqZeroExt D X) N n),
    Word k D X N n r v ∧ w = d ⊗ₜ[k] v}

variable {k D X N}

theorem tensor_weight_mem {n r : ℕ} (d : D) {v : term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ weight k D X N n r) : d ⊗ₜ[k] v ∈ twoSidedWeight k D X N n r := by
  let g := TensorProduct.mk k D (term k (TrivSqZeroExt D X) N n) d
  have hle : weight k D X N n r ≤
      ((twoSidedWeight k D X N n r).restrictScalars k).comap g := by
    apply Submodule.span_le.mpr
    intro z hz
    exact Submodule.subset_span ⟨d, z, hz, rfl⟩
  exact hle hv

end DerivedBar.SquareZero

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_MultibarSigns
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
attribute [-simp] _root_.OAI.DerivedBar.termMap_tmul _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct
open TensorProduct TrivSqZeroExt
noncomputable section

namespace DerivedBar.SquareZero
universe u

variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

/-- Projection to count r, rescaled by one minus sign per base/ideal inversion.
For block lengths i₀,...,iᵣ the exponent is Σⱼ (r-j)iⱼ. -/
def signedProjection : (n r : ℕ) → Module.End k (term k (TrivSqZeroExt D X) N n)
  | 0, 0 => LinearMap.id
  | 0, _+1 => 0
  | n+1, 0 => TensorProduct.map (baseProjection k D X) (signedProjection n 0)
  | n+1, r+1 => (-1 : k)^(r+1) •
      TensorProduct.map (baseProjection k D X) (signedProjection n (r+1)) +
      TensorProduct.map (idealProjection k D X) (signedProjection n r)

@[simp] theorem signedProjection_base (n r : ℕ) (d : D)
    (v : term k (TrivSqZeroExt D X) N n) :
    signedProjection k D X N (n+1) r ((inl d : TrivSqZeroExt D X) ⊗ₜ[k] v) =
      (-1 : k)^r • ((inl d : TrivSqZeroExt D X) ⊗ₜ[k]
        signedProjection k D X N n r v) := by
  cases r <;> simp [signedProjection]

@[simp] theorem signedProjection_ideal_zero (n : ℕ) (x : X)
    (v : term k (TrivSqZeroExt D X) N n) :
    signedProjection k D X N (n+1) 0 ((inr x : TrivSqZeroExt D X) ⊗ₜ[k] v) = 0 := by
  simp [signedProjection]

@[simp] theorem signedProjection_ideal_succ (n r : ℕ) (x : X)
    (v : term k (TrivSqZeroExt D X) N n) :
    signedProjection k D X N (n+1) (r+1) ((inr x : TrivSqZeroExt D X) ⊗ₜ[k] v) =
      (inr x : TrivSqZeroExt D X) ⊗ₜ[k] signedProjection k D X N n r v := by
  simp [signedProjection]

variable {k D X N}

variable (k D X N)

/-- The signed count operator preserves the exterior left D-action. -/
def twoSidedSignedProjection (n r : ℕ) :
    Module.End D (D ⊗[k] term k (TrivSqZeroExt D X) N n) :=
  AlgebraTensorModule.lTensor D D (signedProjection k D X N n r)

end DerivedBar.SquareZero

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_PatternTensorCoherence
attribute [-instance] _root_.OAI.DerivedBar.BimoduleTensor.twoSidedBarFunctor_additive _root_.OAI.DerivedBar.barFunctor_additive _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory TensorProduct
open scoped TensorProduct
noncomputable section
namespace DerivedBar.Multibar
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N] [Module D N] [IsScalarTower k D N]

/-- Exterior actions agree as well as the underlying field-tensor modules. -/
def termPatternIso (i : ℕ) (p : List Bool) :
    ModuleCat.of D (DerivedBar.term k D (patternTerm k D X N p) i) ≅
      ModuleCat.of D (patternTerm k D X N (List.replicate i false ++ p)) := by
  induction i with
  | zero => exact Iso.refl _
  | succ i ih =>
    let e := ih.toLinearEquiv
    exact (AlgebraTensorModule.congr (LinearEquiv.refl D D) (e.restrictScalars k)).toModuleIso

/-- Coherence between canonical categorical scalars and supplied compatible scalars. -/
def freeBarObjIso (V : Type u) [AddCommGroup V] [Module k V]
    [Module D V] [IsScalarTower k D V] (i : ℕ) :
    ((DerivedBar.barFunctor k D).obj (ModuleCat.of D V)).X i ≅
      ModuleCat.of D (DerivedBar.term k D V (i+1)) := by
  have h := BimoduleTensor.scalarModule_eq k D V
  cases h
  exact Iso.refl _

/-- The same coherence for arbitrary X bimodule coefficients. -/
def twoSidedBarObjIso (V : Type u) [AddCommGroup V] [Module k V]
    [Module D V] [IsScalarTower k D V] (i : ℕ) :
    ((BimoduleTensor.twoSidedBarFunctor k D X).obj (ModuleCat.of D V)).X i ≅
      ModuleCat.of D (X ⊗[k] DerivedBar.term k D V i) := by
  have h := BimoduleTensor.scalarModule_eq k D V
  cases h
  exact Iso.refl _

/-- Coherence of a free bar term with a literal leading block. -/
def freeBarPatternIso (i : ℕ) (p : List Bool) :
    ((DerivedBar.barFunctor k D).obj (ModuleCat.of D (patternTerm k D X N p))).X i ≅
      ModuleCat.of D (patternTerm k D X N (List.replicate (i+1) false ++ p)) :=
  freeBarObjIso k D (patternTerm k D X N p) i ≪≫ termPatternIso k D X N (i+1) p

/-- Coherence of a two-sided bar term with its literal X and D slots. -/
def twoSidedBarPatternIso (i : ℕ) (p : List Bool) :
    ((BimoduleTensor.twoSidedBarFunctor k D X).obj
      (ModuleCat.of D (patternTerm k D X N p))).X i ≅
      ModuleCat.of D (patternTerm k D X N (true :: (List.replicate i false ++ p))) :=
  twoSidedBarObjIso k D X (patternTerm k D X N p) i ≪≫
    (AlgebraTensorModule.congr (LinearEquiv.refl D X)
      ((termPatternIso k D X N i p).toLinearEquiv.restrictScalars k)).toModuleIso
end DerivedBar.Multibar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_MultibarDecomposition
attribute [-instance] _root_.OAI.DerivedBar.Multibar.Indexed.shape_finite _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct TrivSqZeroExt
noncomputable section

namespace DerivedBar.Multibar.Indexed
universe u

attribute [local instance] OAI.DerivedBar.Multibar.Indexed.instDecidableEqShape
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

def inclusion : {n r : ℕ} → (p : Shape n r) →
    tensor k D X N p →ₗ[k] DerivedBar.term k (TrivSqZeroExt D X) N n
  | _, _, .nil => LinearMap.id
  | _, _, .base p => TensorProduct.map (inlAlgHom k D X).toLinearMap (inclusion p)
  | _, _, .ideal p => TensorProduct.map ((inrHom D X).restrictScalars k) (inclusion p)

def retraction : {n r : ℕ} → (p : Shape n r) →
    DerivedBar.term k (TrivSqZeroExt D X) N n →ₗ[k] tensor k D X N p
  | _, _, .nil => LinearMap.id
  | _, _, .base p => TensorProduct.map (fstHom k D X).toLinearMap (retraction p)
  | _, _, .ideal p => TensorProduct.map ((sndHom D X).restrictScalars k) (retraction p)

theorem retraction_inclusion {n r : ℕ} (p : Shape n r) (v : tensor k D X N p) :
    retraction k D X N p (inclusion k D X N p v) = v := by
  induction p with
  | nil => rfl
  | base p ih =>
    induction v using OAI.tensorInductionOn with
    | tmul d v =>
      change d ⊗ₜ[k] retraction k D X N p (inclusion k D X N p v) = _
      rw [ih]
    | add v w hv hw => simp only [map_add, hv, hw]
  | ideal p ih =>
    induction v using OAI.tensorInductionOn with
    | tmul x v =>
      change x ⊗ₜ[k] retraction k D X N p (inclusion k D X N p v) = _
      rw [ih]
    | add v w hv hw => simp only [map_add, hv, hw]

theorem inclusion_mem {n r : ℕ} (p : Shape n r) (v : tensor k D X N p) :
    inclusion k D X N p v ∈ SquareZero.weight k D X N n r := by
  induction p with
  | nil => exact Submodule.subset_span (SquareZero.Word.nil v)
  | base p ih =>
    induction v using OAI.tensorInductionOn with
    | tmul d v => exact SquareZero.base_tmul_mem d (ih v)
    | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw
  | ideal p ih =>
    induction v using OAI.tensorInductionOn with
    | tmul x v => exact SquareZero.ideal_tmul_mem x (ih v)
    | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw

/-- Every homogeneous word is an actual tensor in one of the prescribed blocks. -/
theorem word_inclusion {n r : ℕ} {z : DerivedBar.term k (TrivSqZeroExt D X) N n}
    (hz : SquareZero.Word k D X N n r z) :
    ∃ (p : Shape n r) (v : tensor k D X N p), inclusion k D X N p v = z := by
  induction hz with
  | nil v => exact ⟨.nil, v, rfl⟩
  | base d h ih =>
    obtain ⟨p, v, hv⟩ := ih
    exact ⟨.base p, d ⊗ₜ[k] v, by change (inl d : TrivSqZeroExt D X) ⊗ₜ[k] _ = _; rw [hv]⟩
  | ideal x h ih =>
    obtain ⟨p, v, hv⟩ := ih
    exact ⟨.ideal p, x ⊗ₜ[k] v, by change (inr x : TrivSqZeroExt D X) ⊗ₜ[k] _ = _; rw [hv]⟩

def outerInclusion {n r : ℕ} (p : Shape n r) : outerTensor k D X N p →ₗ[D]
    D ⊗[k] DerivedBar.term k (TrivSqZeroExt D X) N n :=
  AlgebraTensorModule.lTensor D D (inclusion k D X N p)

def outerRetraction {n r : ℕ} (p : Shape n r) :
    D ⊗[k] DerivedBar.term k (TrivSqZeroExt D X) N n →ₗ[D] outerTensor k D X N p :=
  AlgebraTensorModule.lTensor D D (retraction k D X N p)

theorem outerRetraction_inclusion {n r : ℕ} (p : Shape n r) (v : outerTensor k D X N p) :
    outerRetraction k D X N p (outerInclusion k D X N p v) = v := by
  induction v using OAI.tensorInductionOn with
  | tmul d v =>
    change d ⊗ₜ[k] retraction k D X N p (inclusion k D X N p v) = _
    rw [retraction_inclusion]
  | add v w hv hw => simp only [map_add, hv, hw]

theorem outerInclusion_mem {n r : ℕ} (p : Shape n r) (v : outerTensor k D X N p) :
    outerInclusion k D X N p v ∈ SquareZero.twoSidedWeight k D X N n r := by
  induction v using OAI.tensorInductionOn with
  | tmul d v => exact SquareZero.tensor_weight_mem d (inclusion_mem k D X N p v)
  | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw

/-- The actual sum of all tensor-block inclusions in count r and degree n. -/
def assemble (n r : ℕ) : (⨁ p : Shape n r, outerTensor k D X N p) →ₗ[D]
    SquareZero.twoSidedWeight k D X N n r :=
  DirectSum.toModule D (Shape n r) _ (fun p =>
    (outerInclusion k D X N p).codRestrict _ (outerInclusion_mem k D X N p))

/-- Surjectivity is proved from the original homogeneous-word spanning definition. -/
theorem assemble_surjective (n r : ℕ) : Function.Surjective (assemble k D X N n r) := by
  let S := LinearMap.range (assemble k D X N n r)
  have hle : SquareZero.twoSidedWeight k D X N n r ≤
      S.map (SquareZero.twoSidedWeight k D X N n r).subtype := by
    apply Submodule.span_le.mpr
    rintro z ⟨d, v, hv, rfl⟩
    obtain ⟨p, w, hw⟩ := word_inclusion k D X N hv
    refine ⟨assemble k D X N n r (DirectSum.lof D _ _ p (d ⊗ₜ[k] w)), ⟨_, rfl⟩, ?_⟩
    simp only [assemble, DirectSum.toModule_lof, LinearMap.codRestrict_apply,
      Submodule.subtype_apply]
    change d ⊗ₜ[k] inclusion k D X N p w = d ⊗ₜ[k] v
    rw [hw]
  intro v
  obtain ⟨w, ⟨z, hz⟩, hw⟩ := hle v.property
  refine ⟨z, ?_⟩
  apply Subtype.ext
  rw [hz]
  exact hw

end DerivedBar.Multibar.Indexed

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_LiteralMultibarCoordinates
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory TensorProduct
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.RecursiveTotal
open DerivedBar.Multibar
universe u

variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance instModuleCarrier_solutions (N : ModuleCat.{u} D) : Module k N := BimoduleTensor.scalarModule k D N
local instance instIsScalarTowerCarrier_solutions (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (Z : ChainComplex (ModuleCat.{u} D) ℕ)
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "c" => ComplexShape.down ℕ

/-- Every inner summand is isomorphic, D-linearly, to its literal field tensor. -/
def innerSummandIso : (r n : ℕ) → (t : Index r n) →
    summand (fun _ => XB) Z r n t ≅
      ModuleCat.of D (patternTerm k D X (Z.X (inputDegree r t)) (innerPattern r t))
  | 0, _, _ => Iso.refl _
  | r+1, _, ⟨p,t⟩ =>
    (XB ⋙ HomologicalComplex.eval _ c p.val.1).mapIso (innerSummandIso r p.val.2 t) ≪≫
      twoSidedBarPatternIso k D X (Z.X (inputDegree r t)) p.val.1 (innerPattern r t)

/-- The prefix of the leading sequence is exactly the sequence of X bars,
also at the literal summand level. -/
theorem leadingSummand_prefix (r m n : ℕ) (h : m ≤ r) (t : Index m n) :
    summand (leadingBarSequence k D X r) Z m n t = summand (fun _ => XB) Z m n t := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    rcases t with ⟨⟨⟨i,q⟩,hq⟩,t⟩
    change (degreeFunctor (leadingBarSequence k D X r) m i).obj _ = _
    simp only [degreeFunctor, leadingBarSequence, ite_eq_left (show m < r by omega),
      Functor.comp_obj, summand, ih q (by omega) t]

/-- The source tensor D ⊗ D^i₀ ⊗ X ⊗ ... ⊗ D^iᵣ ⊗ Z^q,
with every field scalar action and every exterior D action checked. -/
def leadingSummandIso (r n : ℕ) (t : Index (r+1) n) :
    summand (leadingBarSequence k D X r) Z (r+1) n t ≅
      ModuleCat.of D (D ⊗[k]
        patternTerm k D X (Z.X (inputDegree (r+1) t)) (leadingPattern r n t)) := by
  rcases t with ⟨⟨⟨i,q⟩,h⟩,t⟩
  simp only [summand, degreeFunctor, leadingBarSequence, lt_self_iff_false, ite_false, if_false]
  change ((barFunctor k D ⋙ HomologicalComplex.eval _ c i).obj
      (summand (leadingBarSequence k D X r) Z r q t)) ≅ _
  exact (barFunctor k D ⋙ HomologicalComplex.eval _ c i).mapIso
      (eqToIso (leadingSummand_prefix k D X Z r r q le_rfl t) ≪≫
        innerSummandIso k D X Z r q t) ≪≫
    freeBarPatternIso k D X (Z.X (inputDegree r t)) i (innerPattern r t)
end DerivedBar.RecursiveTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_ModuleMultibarCoordinates
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.RecursiveTotal
open DerivedBar.Multibar
universe u
local notation "c" => ComplexShape.down ℕ
attribute [local instance] OAI.DerivedBar.RecursiveTotal.instDecidableEqIndex_2
local instance instDecidableEqShape_r160664_1 (r n : ℕ) : DecidableEq (Multibar.Indexed.Shape r n) := Classical.decEq _
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance instModuleCarrier_solutions_1 (N : ModuleCat.{u} D) : Module k N := BimoduleTensor.scalarModule k D N
variable (N : ModuleCat.{u} D)
local notation "Z" => (Functor.obj (ChainComplex.single₀ (ModuleCat D)) N)

/-- Positive final input degrees contribute zero, without any assumption on X. -/
theorem moduleSummand_isZero (r n : ℕ) (t : Index (r+1) n)
    (h : inputDegree (r+1) t ≠ 0) :
    IsZero (summand (leadingBarSequence k D X r) Z (r+1) n t) :=
  summand_isZero _ Z _ _ t (HomologicalComplex.isZero_single_obj_X c 0 N _ h)

local instance instIsScalarTowerCarrier_solutions_1_r160664_1 (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
/-- Each surviving recursive-total summand is the exact previously indexed
block tensor in degree r+n; the input is the original D-module. -/
def moduleSummandIso (r n : ℕ)
    (t : {t : Index (r+1) n // inputDegree (r+1) t=0}) :
    summand (leadingBarSequence k D X r) Z (r+1) n t.val ≅
      ModuleCat.of D (Multibar.Indexed.outerTensor k D X N (moduleShapeEquiv r n t)) := by
  have h : Multibar.Indexed.tensor k D X N (moduleShapeEquiv r n t) =
      patternTerm k D X N (leadingPattern r n t.val) := by
    rw [Multibar.Indexed.tensor_toList, moduleShape_toList]
  have e : summand (leadingBarSequence k D X r) Z (r+1) n t.val ≅
      ModuleCat.of D (D ⊗[k] patternTerm k D X N (leadingPattern r n t.val)) := by
    have hn : (Z).X (inputDegree (r+1) t.val) = N := by
      rw [t.property]
      rfl
    exact leadingSummandIso k D X Z r n t.val ≪≫ eqToIso
      (congrArg (fun V : ModuleCat D => ModuleCat.of D
        (D ⊗[k] patternTerm k D X V (leadingPattern r n t.val))) hn)
  exact e ≪≫ eqToIso (congrArg (fun V : ModuleCat k => ModuleCat.of D (D ⊗[k] V)) h.symm)

/-- The exact block tensor after reindexing supported summands by Shape. -/
def reindexedModuleSummandIso (r n : ℕ) (p : Multibar.Indexed.Shape (r+n) r) :
    summand (leadingBarSequence k D X r) Z (r+1) n ((moduleShapeEquiv r n).symm p).val ≅
      ModuleCat.of D (Multibar.Indexed.outerTensor k D X N p) := by
  exact moduleSummandIso k D X N r n ((moduleShapeEquiv r n).symm p) ≪≫
    eqToIso (congrArg (fun s : Multibar.Indexed.Shape (r+n) r =>
      ModuleCat.of D (Multibar.Indexed.outerTensor k D X N s))
        ((moduleShapeEquiv r n).apply_symm_apply p))

/-- All recursive-total terms are identified with the manuscript's exact finite
sum of tensor blocks. This includes discarding only proved zero input-degree terms. -/
def moduleFlatCoordinates (r n : ℕ) :
    (flatLeadingMultibar k D X Z r).X n ≅
      ModuleCat.of D (⨁ p : Multibar.Indexed.Shape (r+n) r,
        Multibar.Indexed.outerTensor k D X N p) := by
  let V := summand (leadingBarSequence k D X r) Z (r+1) n
  let P := fun t : Index (r+1) n => inputDegree (r+1) t=0
  let e := moduleShapeEquiv r n
  exact supportIso V P (moduleSummand_isZero k D X N r n) ≪≫
    (DirectSum.lequivCongrLeft D (M := fun t : {t // P t} => V t.val) e).toModuleIso ≪≫
    (DirectSum.congrLinearEquiv (fun p =>
      (reindexedModuleSummandIso k D X N r n p).toLinearEquiv)).toModuleIso

end DerivedBar.RecursiveTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IndexedMultibarTotal
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive TensorProduct
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.RecursiveTotal
open DerivedBar.Multibar
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance instModuleCarrier_solutions_2 (N : ModuleCat.{u} D) : Module k N := BimoduleTensor.scalarModule k D N
variable (N : ModuleCat.{u} D)
local notation "Z" => (Functor.obj (ChainComplex.single₀ (ModuleCat D)) N)
local notation "F" => flatLeadingMultibar k D X Z

local instance instIsScalarTowerCarrier_solutions_2_r160664_1 (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
abbrev indexedModule (r n : ℕ) : ModuleCat.{u} D :=
  ModuleCat.of D (⨁ p : Multibar.Indexed.Shape (r+n) r,
    Multibar.Indexed.outerTensor k D X N p)

/-- The independently recursive multibar faces in the exact Shape coordinates.
This uses the horizontal/vertical differential of RecursiveTotal, not the count
complex differential. -/
def indexedDifferential (r n : ℕ) : indexedModule k D X N r (n+1) ⟶ indexedModule k D X N r n :=
  (moduleFlatCoordinates k D X N r (n+1)).inv ≫
    (F r).d (n+1) n ≫ (moduleFlatCoordinates k D X N r n).hom

theorem indexedDifferential_sq (r n : ℕ) :
    indexedDifferential k D X N r (n+1) ≫ indexedDifferential k D X N r n = 0 := by
  simp only [indexedDifferential, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc ((F r).d (n+2) (n+1)), HomologicalComplex.d_comp_d,
    zero_comp, comp_zero]

/-- Exact tensor-block coordinates, with the unshifted multibar total degree n. -/
def indexedMultibar (r : ℕ) : ChainComplex (ModuleCat.{u} D) ℕ :=
  ChainComplex.of (indexedModule k D X N r) (indexedDifferential k D X N r)
    (indexedDifferential_sq k D X N r)

/-- Chain isomorphism from the exact tensor-block direct sum to the recursive flat model. -/
def indexedFlatIso (r : ℕ) : indexedMultibar k D X N r ≅ F r :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (moduleFlatCoordinates k D X N r n).symm)
    (by
      intro i j hij
      change j+1=i at hij
      subst i
      change (moduleFlatCoordinates k D X N r (j+1)).inv ≫ (F r).d (j+1) j =
        (indexedMultibar k D X N r).d (j+1) j ≫ (moduleFlatCoordinates k D X N r j).inv
      simp only [indexedMultibar, ChainComplex.of_d, indexedDifferential,
        Category.assoc, Iso.hom_inv_id, Category.comp_id])

/-- Genuine derived tensor iteration represented by the exact indexed block
complex. No count splitting or projective-dimension statement is assumed. -/
def derivedIterateIndexedIso (r : ℕ) :
    (derivedTensorIterate k D X r).obj ((chainQ D).obj Z) ≅
      (chainQ D).obj (indexedMultibar k D X N r) :=
  derivedIterateFlatIso k D X Z r ≪≫ (chainQ D).mapIso (indexedFlatIso k D X N r).symm
end DerivedBar.RecursiveTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_IntegerDerivedMultibar
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
namespace DerivedBar
universe u
variable (D : Type u) [Ring D]

attribute [local instance] OAI.DerivedBar.instHasDerivedCategoryModuleCat_solutions
theorem integerQ_inverts : (chainQuasiIso D).IsInvertedBy (integerQ D) := by
  intro Z W f hf
  have : QuasiIso f := hf
  exact inferInstanceAs (IsIso (DerivedCategory.Q.map
    (HomologicalComplex.extendMap f ComplexShape.embeddingDownNat)))

/-- Comparison from the nonnegative-chain localization into the genuine integer
cochain derived category, obtained by its localization universal property. -/
def chainToIntegerDerived : chainDerived D ⥤ DerivedCategory (ModuleCat.{u} D) :=
  Localization.lift (integerQ D) (integerQ_inverts D) (chainQ D)

def chainToIntegerDerivedIso : chainQ D ⋙ chainToIntegerDerived D ≅ integerQ D :=
  Localization.fac (integerQ D) (integerQ_inverts D) (chainQ D)

variable (k X : Type u) [Field k] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "Z" => (Functor.obj (ChainComplex.single₀ (ModuleCat D)) N)

/-- The constructed finite derived iterate, now viewed in the actual integer
cochain derived category, is represented by the exact indexed block complex.
This does not assert an extension of the tensor functor to arbitrary integer inputs. -/
def integerDerivedIterateIndexedIso (r : ℕ) :
    (chainToIntegerDerived D).obj
      ((derivedTensorIterate k D X r).obj ((chainQ D).obj Z)) ≅
    DerivedCategory.Q.obj
      ((integerExtension D).obj (RecursiveTotal.indexedMultibar k D X N r)) :=
  (chainToIntegerDerived D).mapIso (RecursiveTotal.derivedIterateIndexedIso k D X N r) ≪≫
    (chainToIntegerDerivedIso D).app (RecursiveTotal.indexedMultibar k D X N r)

end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_QuadraticEncoding
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.QuadraticEncoding
universe u v
variable {k : Type u} [Field k] {d t : ℕ}

def basis (i : Fin (d + 1)) : Arrows k d := Pi.single i 1

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_PathBasisIso
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace LittleFinitistic.PathBasisIso
universe u
variable (k : Type u) [Field k] (d : ℕ)
abbrev family : Fin (d+1) → ModuleCat.{u} k := fun _ => ModuleCat.of k (QuadraticEncoding.Arrows k d)

end LittleFinitistic.PathBasisIso

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Iteration_IntegerIterateSupport
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace DerivedBar.IterateSupport
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)

attribute [local instance] OAI.DerivedBar.IterateSupport.instHasDerivedCategoryModuleCat_solutions
/-- The already constructed genuine derived iterate, viewed in integer degrees. -/
abbrev object (r : ℕ) := (chainToIntegerDerived D).obj
  ((derivedTensorIterate k D X r).obj
    ((chainQ D).obj ((ChainComplex.single₀ (ModuleCat D)).obj N)))

/-- Every actual iterate is cohomologically nonpositive. This uses the proved
integer comparison and its actual nonnegative chain representative. -/
instance isLE_zero (r : ℕ) : (object k D X N r).IsLE 0 := by
  let Z := RecursiveTotal.indexedMultibar k D X N r
  have : ((integerExtension D).obj Z).IsStrictlyLE 0 :=
    inferInstanceAs (CochainComplex.IsStrictlyLE (Z.extend ComplexShape.embeddingDownNat) 0)
  have : (DerivedCategory.Q.obj ((integerExtension D).obj Z)).IsLE 0 := inferInstance
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (integerDerivedIterateIndexedIso D k X N r).symm 0

end DerivedBar.IterateSupport

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Iteration_IntegerIterateAmplitude
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace DerivedBar.IterateSupport
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [IsScalarTower k D X]
variable (g : ℕ) (hg : ∀ M : ModuleCat.{u} D, HasProjectiveDimensionLE M g)
variable (N : ModuleCat.{u} D)

abbrev resolvedModel (r : ℕ) := (tensorTotalIterate k D X r).obj
  ((ChainComplex.single₀ (ModuleCat D)).obj N)

attribute [local instance] OAI.DerivedBar.IterateSupport.instHasDerivedCategoryModuleCat_solutions_2
def resolvedModelIso (r : ℕ) : object k D X N r ≅
    DerivedCategory.Q.obj ((integerExtension D).obj (resolvedModel k D X N r)) :=
  (chainToIntegerDerived D).mapIso
    ((derivedTensorIterateIso k D X r).app ((ChainComplex.single₀ (ModuleCat D)).obj N)) ≪≫
    (chainToIntegerDerivedIso D).app (resolvedModel k D X N r)

end DerivedBar.IterateSupport

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexFunctor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.VertexFunctor
universe u
variable {A B : Type u} [Ring A] [Ring B]
variable (β : B →+* A) (e : A) (he : e*e=e) (hc : ∀ b, e*β b=β b*e)

def inclusion (M : ModuleCat.{u} A) : fixed β e hc M →ₗ[B] restricted β M :=
  (fixed β e hc M).subtype

end LittleFinitistic.VertexFunctor

end

end OAI
end


