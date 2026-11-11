-- Prove2me | Definitions.Def_Q221FA000
-- name    : Q221FA000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T15:24:00.089222+00:00
-- url     : https://prove2.me/theorems/fea1db78-d0ef-4aa3-bcd7-7158cd825b71
-- title:
--   Definitions bundle Q221FA000 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.extreme_left_right_asymmetry`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 187 declarations of OpenAI's Lean: 107 definitions, 29 instances and 51 theorems. The definitions and types are `OAI.ExternalTensor.rightMap`, `OAI.LittleFinitistic.AsymmetryConstruction.Lambda`, `OAI.LittleFinitistic.ConcreteTensorEvaluation.moduleEvaluation`, `OAI.LittleFinitistic.ConcreteTensorEvaluation.tensorCongr`, `OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexIso`, `OAI.LittleFinitistic.CummingsConstruction.NewCorner`, `OAI.LittleFinitistic.CummingsConstruction.NewInjective`, `OAI.LittleFinitistic.CummingsConstruction.NewInjective.act`, `OAI.LittleFinitistic.CummingsConstruction.NewInjective.value`, `OAI.LittleFinitistic.CummingsConstruction.SimpleSum`, `OAI.LittleFinitistic.CummingsConstruction.SimpleSum.rightCharacter`, `OAI.LittleFinitistic.CummingsConstruction.SimpleSum.value`, `OAI.LittleFinitistic.CummingsConstruction.T`, `OAI.LittleFinitistic.CummingsConstruction.augmentation`, `OAI.LittleFinitistic.CummingsConstruction.coindField`, `OAI.LittleFinitistic.CummingsConstruction.cval`, `OAI.LittleFinitistic.CummingsConstruction.ehead`, `OAI.LittleFinitistic.CummingsConstruction.epsDifferential`, `OAI.LittleFinitistic.CummingsConstruction.etail`, `OAI.LittleFinitistic.CummingsConstruction.extendedInjective`, `OAI.LittleFinitistic.CummingsConstruction.extendedRegular`, `OAI.LittleFinitistic.CummingsConstruction.lastCoordinate`, `OAI.LittleFinitistic.CummingsConstruction.newAugmentation`, `OAI.LittleFinitistic.CummingsConstruction.newCharacter`, `OAI.LittleFinitistic.CummingsConstruction.newDifferential`, `OAI.LittleFinitistic.CummingsConstruction.newIdem`, `OAI.LittleFinitistic.CummingsConstruction.newInjectiveInclusion`, `OAI.LittleFinitistic.CummingsConstruction.newInjectiveObj`, `OAI.LittleFinitistic.CummingsConstruction.newInjectiveRetraction`, `OAI.LittleFinitistic.CummingsConstruction.newInjectiveπ`, `OAI.LittleFinitistic.CummingsConstruction.newProjection`, `OAI.LittleFinitistic.CummingsConstruction.newRegular`, `OAI.LittleFinitistic.CummingsConstruction.newRegularι`, `OAI.LittleFinitistic.CummingsConstruction.newRegularπ`, `OAI.LittleFinitistic.CummingsConstruction.newSimple`, `OAI.LittleFinitistic.CummingsConstruction.newSimpleι`, `OAI.LittleFinitistic.CummingsConstruction.oldCharacter`, `OAI.LittleFinitistic.CummingsConstruction.oldSimple`, `OAI.LittleFinitistic.CummingsConstruction.oldSingleDerivedIso`, `OAI.LittleFinitistic.CummingsConstruction.oldSingleι` and 67 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `FinitisticAsymmetry_Asymmetry`, `FinitisticAsymmetry_Augmentation_Directed`, `FinitisticAsymmetry_Derived_BoundedGeneration`, `FinitisticAsymmetry_Derived_ComplexSums`, `FinitisticAsymmetry_Derived_Coproducts`, `FinitisticAsymmetry_Derived_DerivedSums`, `FinitisticAsymmetry_Derived_ExactExtension`, `FinitisticAsymmetry_Derived_LocalizingRetracts`, `FinitisticAsymmetry_Derived_ModuleGeneration`, `FinitisticAsymmetry_Derived_ModuleSums`, `FinitisticAsymmetry_Derived_Telescopes`, `FinitisticAsymmetry_Derived_Truncations`, `FinitisticAsymmetry_Derived_UpperTruncation`, `FinitisticAsymmetry_Kasch_Radical`, `FinitisticAsymmetry_Nakayama_Modules`, `FinitisticAsymmetry_Triangular_Algebra`, `FinitisticAsymmetry_Triangular_Augmentation`, `FinitisticAsymmetry_Triangular_Generation`, `FinitisticAsymmetry_Triangular_InjectiveCorners`, `FinitisticAsymmetry_Triangular_InjectiveResolution`, `FinitisticAsymmetry_Triangular_Socle`, `Finitistic_Localization_ConcreteTensorEvaluation`, `Finitistic_Rectification_ExternalTensor`.
--
--   **Imports.** It imports the bundle `OAIQ023F028` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q221FA002`; the statement `OAI.LittleFinitistic.CummingsConstruction.injectivesGenerate`; the proof of `OAI.LittleFinitistic.Main.infinite_littleFinitisticDimension`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Localization.Linear
import Mathlib.CategoryTheory.Triangulated.Generators
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.FinCases
import Definitions.Def_OAIQ023F028

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_Coproducts
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
namespace LittleFinitistic.DerivedSupport

section
universe u v w t
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {ι : Type t} {c : ComplexShape ι} {I : Type w}
variable {K : I → HomologicalComplex C c}

def cofanEvalIsColimit (s : Cofan K) (hs : IsColimit s)
    [HasColimitsOfShape (Discrete I) C] (j : ι) :
    IsColimit (Cofan.mk (s.pt.X j) (fun i => (s.inj i).f j)) :=
  (Cofan.isColimitMapCoconeEquiv (eval C c j) K s)
    (isColimitOfPreserves (eval C c j) hs)

def homotopyCofanDesc (s : Cofan K) (hs : IsColimit s)
    [HasColimitsOfShape (Discrete I) C] {Y : HomologicalComplex C c}
    (f g : s.pt ⟶ Y) (h : ∀ i, Homotopy (s.inj i ≫ f) (s.inj i ≫ g)) : Homotopy f g where
  hom j l := (cofanEvalIsColimit s hs j).desc (Cofan.mk _ fun i => (h i).hom j l)
  zero j l hrel := by
    apply (cofanEvalIsColimit s hs j).hom_ext
    intro i
    simp only [comp_zero]
    change (s.inj i.as).f j ≫ _ = 0
    rw [show (s.inj i.as).f j ≫ (cofanEvalIsColimit s hs j).desc
      (Cofan.mk _ fun i => (h i).hom j l) = (h i.as).hom j l from
        (cofanEvalIsColimit s hs j).fac _ i]
    exact (h i.as).zero j l hrel
  comm j := by
    apply (cofanEvalIsColimit s hs j).hom_ext
    intro i
    have hh := (h i.as).comm j
    dsimp only [HomologicalComplex.comp_f] at hh
    have fac (a b : ι) : (s.inj i.as).f a ≫
        (cofanEvalIsColimit s hs a).desc (Cofan.mk _ fun i => (h i).hom a b) =
          (h i.as).hom a b := (cofanEvalIsColimit s hs a).fac _ i
    let a : s.pt.X (c.next j) ⟶ Y.X j :=
      (cofanEvalIsColimit s hs (c.next j)).desc (Cofan.mk _ fun i => (h i).hom (c.next j) j)
    let b : s.pt.X j ⟶ Y.X (c.prev j) :=
      (cofanEvalIsColimit s hs j).desc (Cofan.mk _ fun i => (h i).hom j (c.prev j))
    change (s.inj i.as).f j ≫ f.f j = (s.inj i.as).f j ≫
      (s.pt.d j (c.next j) ≫ a + b ≫ Y.d (c.prev j) j + g.f j)
    dsimp only [a, b]
    rw [Preadditive.comp_add, Preadditive.comp_add,
      (s.inj i.as).comm_assoc, fac, ← Category.assoc, fac]
    exact hh

def quotientCofanIsColimit (s : Cofan K) (hs : IsColimit s)
    [HasColimitsOfShape (Discrete I) C] :
    IsColimit (Cofan.mk ((HomotopyCategory.quotient C c).obj s.pt)
      (fun i => (HomotopyCategory.quotient C c).map (s.inj i))) := by
  let Q := HomotopyCategory.quotient C c
  refine Cofan.IsColimit.mk _
    (fun t => Q.map (hs.desc (Cofan.mk t.pt.as (fun i => (t.inj i).out)))) ?_ ?_
  · intro t i
    change Q.map (s.inj i) ≫ Q.map _ = _
    rw [← Q.map_comp, Cofan.IsColimit.inj_desc]
    exact HomotopyCategory.quotient_map_out _
  · intro t m hm
    obtain ⟨m, rfl⟩ := Q.map_surjective m
    apply HomotopyCategory.eq_of_homotopy
    apply homotopyCofanDesc s hs
    intro i
    apply HomotopyCategory.homotopyOfEq
    change ∀ i, Q.map (s.inj i) ≫ Q.map m = t.inj i at hm
    rw [Q.map_comp, hm, Cofan.IsColimit.inj_desc]
    exact (HomotopyCategory.quotient_map_out _).symm

end

open CategoryTheory.MorphismProperty
universe u₁ u₂ v₁ v₂ w
variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]
variable (W : MorphismProperty C) (F : C ⥤ D) [F.IsLocalization W] [F.Additive]
variable [W.HasRightCalculusOfFractions] {I : Type w}
  [HasColimitsOfShape (Discrete I) C] [W.IsStableUnderCoproductsOfShape I]

omit [Preadditive C] [W.HasRightCalculusOfFractions] in
lemma cofan_desc_mem {X Y : I → C} (s : Cofan Y) (hs : IsColimit s)
    (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, W (f i)) :
    W (Sigma.desc (fun i => f i ≫ s.inj i)) := by
  exact IsStableUnderColimitsOfShape.condition _ _ _ _
    (colimit.isColimit (Discrete.functor X)) hs
    (Discrete.natTrans fun i => f i.as) (fun i => hf i.as) _
    (fun i => by
      change Sigma.ι X i.as ≫ _ = f i.as ≫ s.inj i.as
      exact Sigma.ι_desc _ _)

include W

lemma localizationCofan_zero {X : I → C} (s : Cofan X) (hs : IsColimit s)
    {Y : C} (d : F.obj s.pt ⟶ F.obj Y)
    (hd : ∀ i, F.map (s.inj i) ≫ d = 0) : d = 0 := by
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction F W d
  let ρ (i : I) : W.RightFraction (X i) φ.X' :=
    (LeftFraction.mk (s.inj i) φ.s φ.hs).rightFraction
  have hρ (i : I) : (ρ i).s ≫ s.inj i = (ρ i).f ≫ φ.s :=
    (LeftFraction.mk (s.inj i) φ.s φ.hs).rightFraction_fac
  have hz (i : I) : F.map ((ρ i).f ≫ φ.f) = F.map (0 : (ρ i).X' ⟶ Y) := by
    have hr := congrArg (fun f => F.map (ρ i).s ≫ f) (hd i)
    rw [hφ] at hr
    simpa only [RightFraction.map, comp_zero, ← F.map_comp_assoc, hρ,
      F.map_comp, Category.assoc, IsIso.hom_inv_id_assoc, F.map_zero] using hr
  have hex (i : I) := (W.map_eq_iff_precomp F ((ρ i).f ≫ φ.f) 0).mp (hz i)
  choose Z t ht htf using hex
  let q : (∐ Z) ⟶ φ.X' := Sigma.desc (fun i => t i ≫ (ρ i).f)
  have hq : W (q ≫ φ.s) := by
    have eq : q ≫ φ.s = Sigma.desc (fun i => (t i ≫ (ρ i).s) ≫ s.inj i) := by
      apply Sigma.hom_ext
      intro i
      simp only [q, Sigma.ι_desc_assoc, Sigma.ι_desc, Category.assoc, hρ]
    rw [eq]
    exact cofan_desc_mem W s hs _ (fun i => W.comp_mem _ _ (ht i) (ρ i).hs)
  have hqf : q ≫ φ.f = 0 := by
    apply Sigma.hom_ext
    intro i
    simpa only [q, Sigma.ι_desc_assoc, comp_zero, Category.assoc] using htf i
  let : IsIso (F.map (q ≫ φ.s)) := Localization.inverts F W _ hq
  apply (cancel_epi (F.map (q ≫ φ.s))).mp
  rw [comp_zero, F.map_comp, hφ]
  let : IsIso (F.map φ.s) := Localization.inverts F W _ φ.hs
  simp only [RightFraction.map, Category.assoc]
  rw [IsIso.hom_inv_id_assoc, ← F.map_comp, hqf, F.map_zero]

lemma localizationCofan_hom_ext {X : I → C} (s : Cofan X) (hs : IsColimit s)
    {Y : C} (f g : F.obj s.pt ⟶ F.obj Y)
    (h : ∀ i, F.map (s.inj i) ≫ f = F.map (s.inj i) ≫ g) : f = g := by
  apply sub_eq_zero.mp
  exact localizationCofan_zero W F s hs (f - g) (fun i => by simp [Preadditive.comp_sub, h i])

omit [Preadditive C] [Preadditive D] [F.Additive] in
lemma localizationCofan_lift {X : I → C} (s : Cofan X) (hs : IsColimit s)
    {Y : C} (f : ∀ i, F.obj (X i) ⟶ F.obj Y) :
    ∃ g : F.obj s.pt ⟶ F.obj Y, ∀ i, F.map (s.inj i) ≫ g = f i := by
  choose φ hφ using fun i => Localization.exists_rightFraction F W (f i)
  let q : (∐ fun i => (φ i).X') ⟶ s.pt := Sigma.desc (fun i => (φ i).s ≫ s.inj i)
  have hq : W q := cofan_desc_mem W s hs _ (fun i => (φ i).hs)
  let : IsIso (F.map q) := Localization.inverts F W _ hq
  let p : (∐ fun i => (φ i).X') ⟶ Y := Sigma.desc (fun i => (φ i).f)
  refine ⟨inv (F.map q) ≫ F.map p, ?_⟩
  intro i
  apply (cancel_epi (F.map (φ i).s)).mp
  have he : F.map (φ i).s ≫ F.map (s.inj i) =
      F.map (Sigma.ι (fun i => (φ i).X') i) ≫ F.map q := by
    simp only [← F.map_comp, q, Sigma.ι_desc]
  rw [← Category.assoc, he, Category.assoc, IsIso.hom_inv_id_assoc,
    ← F.map_comp,
    show Sigma.ι (fun i => (φ i).X') i ≫ p = (φ i).f from Sigma.ι_desc _ _, hφ]
  simp only [RightFraction.map, IsIso.hom_inv_id_assoc]

def localizationCofanIsColimit {X : I → C} (s : Cofan X) (hs : IsColimit s) :
    IsColimit (Cofan.mk (F.obj s.pt) (fun i => F.map (s.inj i))) := by
  letI : F.EssSurj := Localization.essSurj F W
  let lift (t : Cofan (fun i => F.obj (X i))) : F.obj s.pt ⟶ t.pt :=
    (localizationCofan_lift W F s hs (fun i => t.inj i ≫ (F.objObjPreimageIso t.pt).inv)).choose ≫
      (F.objObjPreimageIso t.pt).hom
  have fac (t : Cofan (fun i => F.obj (X i))) (i : I) :
      F.map (s.inj i) ≫ lift t = t.inj i := by
    dsimp only [lift]
    rw [← Category.assoc, (localizationCofan_lift W F s hs _).choose_spec i]
    simp
  refine Cofan.IsColimit.mk _ lift fac ?_
  intro t m hm
  apply (cancel_mono (F.objObjPreimageIso t.pt).inv).mp
  apply localizationCofan_hom_ext W F s hs
  intro i
  rw [← Category.assoc, ← Category.assoc, fac]
  exact congrArg (fun f => f ≫ (F.objObjPreimageIso t.pt).inv) (hm i)

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_ComplexSums
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
namespace LittleFinitistic.DerivedSupport
universe u v w t
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type t} {c : ComplexShape ι} {I : Type w}
variable [HasColimitsOfShape (Discrete I) C]

def bundleComplex (K : I → HomologicalComplex C c) :
    HomologicalComplex (Discrete I ⥤ C) c where
  X j := Discrete.functor (fun i => (K i).X j)
  d j l := Discrete.natTrans (fun i => (K i.as).d j l)
  shape j l hjl := by ext i; exact (K i.as).shape _ _ hjl
  d_comp_d' i j l _ _ := by ext a; exact (K a.as).d_comp_d i j l

def bundleComplexMap {K L : I → HomologicalComplex C c} (f : ∀ i, K i ⟶ L i) :
    bundleComplex K ⟶ bundleComplex L where
  f j := Discrete.natTrans (fun i => (f i.as).f j)
  comm' j l _ := by ext i; exact (f i.as).comm _ _

def sumComplex (K : I → HomologicalComplex C c) : HomologicalComplex C c :=
  (colim.mapHomologicalComplex c).obj (bundleComplex K)

def sumComplexMap {K L : I → HomologicalComplex C c} (f : ∀ i, K i ⟶ L i) :
    sumComplex K ⟶ sumComplex L := (colim.mapHomologicalComplex c).map (bundleComplexMap f)

def sumComplexInj (K : I → HomologicalComplex C c) (i : I) : K i ⟶ sumComplex K where
  f j := Sigma.ι (fun i => (K i).X j) i
  comm' j l _ := by
    exact colimit.ι_map ((bundleComplex K).d j l) (Discrete.mk i)

@[reassoc] lemma sumComplexInj_map {K L : I → HomologicalComplex C c}
    (f : ∀ i, K i ⟶ L i) (i : I) :
    sumComplexInj K i ≫ sumComplexMap f = f i ≫ sumComplexInj L i := by
  ext j
  exact colimit.ι_map ((bundleComplexMap f).f j) (Discrete.mk i)

def sumComplexCofan (K : I → HomologicalComplex C c) : Cofan K :=
  Cofan.mk (sumComplex K) (sumComplexInj K)

def sumComplexIsColimit (K : I → HomologicalComplex C c) : IsColimit (sumComplexCofan K) :=
  HomologicalComplex.isColimitOfEval _ _ (fun j =>
    (Cofan.isColimitMapCoconeEquiv (eval C c j) K (sumComplexCofan K)).symm
      (colimit.isColimit (Discrete.functor (fun i => (K i).X j))))

lemma sumComplexMap_quasiIso [HasExactColimitsOfShape (Discrete I) C]
    {K L : I → HomologicalComplex C c} (f : ∀ i, K i ⟶ L i) [∀ i, QuasiIso (f i)] :
    QuasiIso (sumComplexMap f) := by
  have : QuasiIso (bundleComplexMap f) := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro i
    change QuasiIso (f i.as)
    infer_instance
  exact inferInstanceAs (QuasiIso ((colim.mapHomologicalComplex c).map (bundleComplexMap f)))

def homotopySumCofan (X : I → HomotopyCategory C c) : Cofan X :=
  Cofan.mk ((HomotopyCategory.quotient C c).obj (sumComplex (fun i => (X i).as)))
    (fun i => (HomotopyCategory.quotient C c).map (sumComplexInj (fun j => (X j).as) i))

def homotopySumIsColimit (X : I → HomotopyCategory C c) :
    IsColimit (homotopySumCofan X) :=
  quotientCofanIsColimit _ (sumComplexIsColimit (fun i => (X i).as))

instance homotopyHasCoproducts : HasColimitsOfShape (Discrete I) (HomotopyCategory C c) where
  has_colimit F := by
    let X (i : I) := F.obj ⟨i⟩
    let : HasColimit (Discrete.functor X) := ⟨_, homotopySumIsColimit X⟩
    exact hasColimit_of_iso (F := Discrete.functor X)
      (Discrete.natIso (fun i => Iso.refl (F.obj i)))

instance homotopyQuasiIsoCoproducts [HasExactColimitsOfShape (Discrete I) C] :
    (HomotopyCategory.quasiIso C c).IsStableUnderCoproductsOfShape I := by
  apply MorphismProperty.IsStableUnderCoproductsOfShape.mk
  intro X Y _ _ f hf
  let Q := HomotopyCategory.quotient C c
  let a := (colimit.isColimit (Discrete.functor X)).coconePointUniqueUpToIso (homotopySumIsColimit X)
  let b := (colimit.isColimit (Discrete.functor Y)).coconePointUniqueUpToIso (homotopySumIsColimit Y)
  have hq (i : I) : QuasiIso (f i).out := by
    rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomotopyCategory.quotient_map_out]
    exact hf i
  have h : HomotopyCategory.quasiIso C c (Q.map (sumComplexMap (fun i => (f i).out))) := by
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact sumComplexMap_quasiIso _
  refine ((HomotopyCategory.quasiIso C c).arrow_mk_iso_iff ?_).2 h
  refine Arrow.isoMk a b ?_
  apply Sigma.hom_ext
  intro i
  have ha : Sigma.ι X i ≫ a.hom = Q.map (sumComplexInj (fun j => (X j).as) i) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk i)
  have hb : Sigma.ι Y i ≫ b.hom = Q.map (sumComplexInj (fun j => (Y j).as) i) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk i)
  change Sigma.ι X i ≫ a.hom ≫ Q.map (sumComplexMap (fun i => (f i).out)) =
    Sigma.ι X i ≫ Limits.Sigma.map f ≫ b.hom
  erw [Sigma.ι_map_assoc, hb, ← Category.assoc, ha, ← Q.map_comp, sumComplexInj_map,
    Q.map_comp, HomotopyCategory.quotient_map_out]
  rfl

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_DerivedSums
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
namespace LittleFinitistic.DerivedSupport
universe u v w z
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{z} C]
variable {I : Type w} [HasColimitsOfShape (Discrete I) C]
  [HasExactColimitsOfShape (Discrete I) C]

def derivedHomotopyCofanIsColimit {X : I → HomotopyCategory C (ComplexShape.up ℤ)}
    (s : Cofan X) (hs : IsColimit s) :
    IsColimit (Cofan.mk (DerivedCategory.Qh.obj s.pt)
      (fun i => DerivedCategory.Qh.map (s.inj i))) :=
  localizationCofanIsColimit (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    DerivedCategory.Qh s hs

def derivedCofanIsColimit {X : I → CochainComplex C ℤ} (s : Cofan X) (hs : IsColimit s) :
    IsColimit (Cofan.mk (DerivedCategory.Q.obj s.pt)
      (fun i => DerivedCategory.Q.map (s.inj i))) := by
  let h := derivedHomotopyCofanIsColimit _ (quotientCofanIsColimit s hs)
  let e := DerivedCategory.quotientCompQhIso C
  refine Cofan.IsColimit.mk _ (fun t =>
    (e.app s.pt).inv ≫ h.desc (Cofan.mk t.pt (fun i => (e.app (X i)).hom ≫ t.inj i))) ?_ ?_
  · intro t i
    change DerivedCategory.Q.map (s.inj i) ≫ (e.app s.pt).inv ≫
      h.desc (Cofan.mk t.pt (fun i => (e.app (X i)).hom ≫ t.inj i)) = t.inj i
    have hn : DerivedCategory.Q.map (s.inj i) ≫ (e.app s.pt).inv =
        (e.app (X i)).inv ≫ DerivedCategory.Qh.map
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (s.inj i)) :=
      e.inv.naturality (s.inj i)
    have hf : DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (s.inj i)) ≫
        h.desc (Cofan.mk t.pt (fun j => (e.app (X j)).hom ≫ t.inj j)) =
        (e.app (X i)).hom ≫ t.inj i := h.fac _ (Discrete.mk i)
    rw [← Category.assoc, hn, Category.assoc, hf]
    exact Iso.inv_hom_id_assoc _ _
  · intro t m hm
    apply (cancel_epi (e.app s.pt).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    apply h.hom_ext
    intro i
    change DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      (s.inj i.as)) ≫ _ = _
    rw [IsColimit.fac]
    change DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      (s.inj i.as)) ≫ (e.app s.pt).hom ≫ m = (e.app (X i.as)).hom ≫ t.inj i.as
    have hn : DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (s.inj i.as)) ≫ (e.app s.pt).hom =
        (e.app (X i.as)).hom ≫ DerivedCategory.Q.map (s.inj i.as) :=
      e.hom.naturality (s.inj i.as)
    change ∀ i, DerivedCategory.Q.map (s.inj i) ≫ m = t.inj i at hm
    rw [← Category.assoc, hn, Category.assoc, hm]

instance derivedHasCoproducts : HasColimitsOfShape (Discrete I) (DerivedCategory C) where
  has_colimit G := by
    let F := DerivedCategory.Qh (C := C)
    let : F.EssSurj := Localization.essSurj F (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    let X (i : I) := F.objPreimage (G.obj ⟨i⟩)
    let e (i : I) := F.objObjPreimageIso (G.obj ⟨i⟩)
    let s : Cofan (fun i => F.obj (X i)) :=
      Cofan.mk (F.obj (∐ X)) (fun i => F.map (Sigma.ι X i))
    let h : IsColimit s := derivedHomotopyCofanIsColimit _ (colimit.isColimit _)
    let t : Cofan (fun i => G.obj ⟨i⟩) :=
      Cofan.mk s.pt (fun i => (e i).inv ≫ s.inj i)
    have ht : IsColimit t := by
      refine Cofan.IsColimit.mk _ (fun z => h.desc (Cofan.mk z.pt
        (fun i => (e i).hom ≫ z.inj i))) ?_ ?_
      · intro z i
        change ((e i).inv ≫ s.inj i) ≫ _ = _
        rw [Category.assoc, Cofan.IsColimit.inj_desc]
        exact Iso.inv_hom_id_assoc _ _
      · intro z m hm
        apply h.hom_ext
        intro i
        rw [IsColimit.fac]
        change s.inj i.as ≫ m = (e i.as).hom ≫ z.inj i.as
        rw [← hm i.as]
        change s.inj i.as ≫ m = (e i.as).hom ≫ ((e i.as).inv ≫ s.inj i.as) ≫ m
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
    let : HasColimit (Discrete.functor (fun i : I => G.obj ⟨i⟩)) := ⟨_, ht⟩
    exact hasColimit_of_iso (F := Discrete.functor (fun i : I => G.obj ⟨i⟩))
      (Discrete.natIso (fun i => Iso.refl (G.obj i)))

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_LocalizingRetracts
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace LittleFinitistic.DerivedSupport
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasColimitsOfShape (Discrete ℕ) C]
variable {X Y : C} (i : X ⟶ Y) (p : Y ⟶ X) (hip : i ≫ p = 𝟙 X)

def swindleA : (∐ fun _ : ℕ => Y) ⟶ (∐ fun _ : ℕ => Y) :=
  Sigma.desc fun n => (𝟙 Y - p ≫ i) ≫ Sigma.ι (fun _ : ℕ => Y) n +
    (p ≫ i) ≫ Sigma.ι (fun _ : ℕ => Y) (n+1)
def swindleC : (∐ fun _ : ℕ => Y) ⟶ (∐ fun _ : ℕ => Y) :=
  Sigma.desc fun n => match n with
    | 0 => (𝟙 Y - p ≫ i) ≫ Sigma.ι (fun _ : ℕ => Y) 0
    | n+1 => (p ≫ i) ≫ Sigma.ι (fun _ : ℕ => Y) n +
        (𝟙 Y - p ≫ i) ≫ Sigma.ι (fun _ : ℕ => Y) (n+1)
def swindleB : (∐ fun _ : ℕ => Y) ⟶ X :=
  Sigma.desc fun n => match n with
    | 0 => p
    | _+1 => 0
def swindleI : X ⟶ (∐ fun _ : ℕ => Y) := i ≫ Sigma.ι (fun _ : ℕ => Y) 0

include hip

lemma swindleAC : swindleA i p ≫ swindleC i p = 𝟙 _ := by
  apply Sigma.hom_ext
  intro n
  cases n <;>
    simp only [swindleA, swindleC, Sigma.ι_desc_assoc, Sigma.ι_desc,
      Preadditive.add_comp, Preadditive.comp_add, Preadditive.sub_comp,
      Preadditive.comp_sub, Category.assoc, reassoc_of% hip,
      Category.id_comp, Category.comp_id] <;> abel

lemma swindleAB : swindleA i p ≫ swindleB p = 0 := by
  apply Sigma.hom_ext
  intro n
  cases n <;> simp [swindleA, swindleB, Preadditive.add_comp, Preadditive.sub_comp,
    Category.assoc, hip]

lemma swindleIB : swindleI i ≫ swindleB p = 𝟙 _ := by
  simp [swindleI, swindleB, Category.assoc, hip]

lemma swindleIC : swindleI i ≫ swindleC i p = 0 := by
  simp [swindleI, swindleC, Category.assoc, Preadditive.comp_sub, reassoc_of% hip]

lemma swindleTotal : swindleC i p ≫ swindleA i p + swindleB p ≫ swindleI i = 𝟙 _ := by
  apply Sigma.hom_ext
  intro n
  cases n <;>
    simp only [swindleA, swindleC, swindleB, swindleI, Sigma.ι_desc_assoc,
      Sigma.ι_desc, Preadditive.add_comp, Preadditive.comp_add,
      Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc,
      reassoc_of% hip, Category.id_comp, Category.comp_id, zero_comp] <;> abel

variable [HasZeroObject C] [HasShift C ℤ]
  [∀ degree : ℤ, (shiftFunctor C degree).Additive] [Pretriangulated C]

def swindleIso : (∐ fun _ : ℕ => Y) ≅ (∐ fun _ : ℕ => Y) ⊞ X where
  hom := biprod.lift (swindleC i p) (swindleB p)
  inv := biprod.desc (swindleA i p) (swindleI i)
  hom_inv_id := by simpa using swindleTotal i p hip
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp [swindleAC i p hip, swindleAB i p hip,
      swindleIB i p hip, swindleIC i p hip]

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_ModuleGeneration
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.DerivedSupport
universe u w
variable {R : Type u} [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
variable (P : ObjectProperty (DerivedCategory (ModuleCat.{u} R)))
  [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
  [P.IsClosedUnderColimitsOfShape (Discrete ℕ)]

variable {S : Type u} [Ring S] (χ : R →+* S)
variable (hcop : ∀ I : Type u, P.IsClosedUnderColimitsOfShape (Discrete I))
include hcop

variable (J : Ideal R) [J.IsTwoSided] [IsSemisimpleRing (R ⧸ J)]

variable {k ι : Type u} [Field k] [Fintype ι] (ψ : R →+* (ι → k))

abbrev coordinateModule (j : ι) : ModuleCat R :=
  (ModuleCat.restrictScalars ((Pi.evalRingHom (fun _ : ι => k) j).comp ψ)).obj
    (ModuleCat.of k k)

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Nakayama_Modules
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

def Object (M : ModuleCat.{u} R) := Module.Dual k (M →ₗ[R] R)

end LittleFinitistic.Nakayama

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_ExactExtension
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.DerivedSupport
universe u v t t'
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type t} {ι' : Type t'} {c : ComplexShape ι} {c' : ComplexShape ι'}
variable (e : c.Embedding c') (S : ShortComplex (HomologicalComplex C c))

def extendEvalIso {j : ι} {j' : ι'} (hj : e.f j = j') :
    (S.map (e.extendFunctor C)).map (HomologicalComplex.eval C c' j') ≅
    S.map (HomologicalComplex.eval C c j) :=
  ShortComplex.isoMk (S.X₁.extendXIso e hj) (S.X₂.extendXIso e hj) (S.X₃.extendXIso e hj)
    (by
      change (S.X₁.extendXIso e hj).hom ≫ S.f.f j =
        (extendMap S.f e).f j' ≫ (S.X₂.extendXIso e hj).hom
      rw [extendMap_f _ e hj]
      simp)
    (by
      change (S.X₂.extendXIso e hj).hom ≫ S.g.f j =
        (extendMap S.g e).f j' ≫ (S.X₃.extendXIso e hj).hom
      rw [extendMap_f _ e hj]
      simp)

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_ModuleSums
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
namespace LittleFinitistic.DerivedSupport
universe u v
open HomologicalComplex
variable {R : Type u} [Ring R] {I : Type v}

def moduleSumComplex (K : I → CochainComplex (ModuleCat.{max u v} R) ℤ) :
    CochainComplex (ModuleCat R) ℤ where
  X j := ModuleCat.of R (Π₀ i, (K i).X j)
  d j k := ModuleCat.ofHom (DFinsupp.mapRange.linearMap (fun i => ((K i).d j k).hom))
  shape j k hjk := by
    ext x i
    change (K i).d j k (x i) = 0
    rw [(K i).shape j k hjk]
    rfl
  d_comp_d' j k l hjk hkl := by
    ext x i
    change ((K i).d k l) (((K i).d j k) (x i)) = 0
    exact ConcreteCategory.congr_hom ((K i).d_comp_d j k l) (x i)

def moduleSumComplexInj (K : I → CochainComplex (ModuleCat.{max u v} R) ℤ) (i : I) :
    K i ⟶ moduleSumComplex K := by
  classical
  refine { f := fun j => ModuleCat.ofHom (DFinsupp.lsingle (R := R)
      (M := fun n => (K n).X j) i), comm' := ?_ }
  intro j k hjk
  ext x
  change DFinsupp.mapRange (fun i => ((K i).d j k).hom) (fun i => map_zero _) (DFinsupp.single i x) =
    DFinsupp.single i ((K i).d j k x)
  rw [DFinsupp.mapRange_single]

def moduleSumComplexCofan (K : I → CochainComplex (ModuleCat.{max u v} R) ℤ) : Cofan K :=
  Cofan.mk _ (moduleSumComplexInj K)

def moduleSumComplexIsColimit (K : I → CochainComplex (ModuleCat.{max u v} R) ℤ) :
    IsColimit (moduleSumComplexCofan K) := by
  classical
  refine Cofan.IsColimit.mk _ (fun s =>
    { f := fun j => ModuleCat.ofHom (DFinsupp.lsum ℤ (fun i => ((s.inj i).f j).hom))
      comm' := ?_ }) ?_ ?_
  · intro j k hjk
    apply ModuleCat.hom_ext
    apply DFinsupp.lhom_ext
    intro i x
    change s.pt.d j k (DFinsupp.lsum ℤ (fun i => ((s.inj i).f j).hom)
        (DFinsupp.single i x)) =
      DFinsupp.lsum ℤ (fun i => ((s.inj i).f k).hom)
        (DFinsupp.mapRange (fun i => ((K i).d j k).hom) (fun i => map_zero _) (DFinsupp.single i x))
    simp only [DFinsupp.mapRange_single, DFinsupp.lsum_single]
    exact ConcreteCategory.congr_hom ((s.inj i).comm j k) x
  · intro s i
    ext j x
    change DFinsupp.lsum ℤ (fun i => ((s.inj i).f j).hom) (DFinsupp.single i x) = _
    simp only [DFinsupp.lsum_single]
  · intro s m hm
    apply HomologicalComplex.Hom.ext
    funext j
    apply ModuleCat.hom_ext
    apply DFinsupp.lhom_ext
    intro i x
    change m.f j (DFinsupp.single i x) =
      DFinsupp.lsum ℤ (fun i => ((s.inj i).f j).hom) (DFinsupp.single i x)
    rw [DFinsupp.lsum_single]
    exact ConcreteCategory.congr_hom (congrArg (fun f => f.f j) (hm i)) x

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_Telescopes
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
namespace LittleFinitistic.DerivedSupport

section
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X : ℕ → C} (f : ∀ n, X n ⟶ X (n+1)) (s : Cofan X) (hs : IsColimit s)

def telescopeMap : s.pt ⟶ s.pt :=
  hs.desc (Cofan.mk s.pt (fun n => s.inj n - f n ≫ s.inj (n+1)))

@[reassoc (attr := simp)]
lemma telescopeMap_inj (n : ℕ) :
    s.inj n ≫ telescopeMap f s hs = s.inj n - f n ≫ s.inj (n+1) :=
  hs.fac _ (Discrete.mk n)

def telescopeπ (c : Cocone (Functor.ofSequence f)) : s.pt ⟶ c.pt :=
  hs.desc (Cofan.mk c.pt c.ι.app)

omit [Preadditive C] in
@[reassoc (attr := simp)]
lemma telescopeπ_inj (c : Cocone (Functor.ofSequence f)) (n : ℕ) :
    s.inj n ≫ telescopeπ f s hs c = c.ι.app n := hs.fac _ (Discrete.mk n)

lemma telescope_zero (c : Cocone (Functor.ofSequence f)) :
    telescopeMap f s hs ≫ telescopeπ f s hs c = 0 := by
  apply hs.hom_ext
  intro n
  change s.inj n.as ≫ _ = _
  rw [telescopeMap_inj_assoc, Preadditive.sub_comp, telescopeπ_inj,
    Category.assoc, telescopeπ_inj, comp_zero]
  have h := c.w (homOfLE (Nat.le_add_right n.as 1))
  simpa using! sub_eq_zero.mpr h.symm

def telescopeCokernel (c : Cocone (Functor.ofSequence f)) (hc : IsColimit c) :
    IsColimit (CokernelCofork.ofπ (telescopeπ f s hs c) (telescope_zero f s hs c)) := by
  let d {Y : C} (g : s.pt ⟶ Y) (hg : telescopeMap f s hs ≫ g = 0) :
      Cocone (Functor.ofSequence f) :=
    { pt := Y
      ι := NatTrans.ofSequence (F := Functor.ofSequence f) (G := (Functor.const ℕ).obj Y) (fun n => s.inj n ≫ g) (fun n => by
        have h := congrArg (fun t => s.inj n ≫ t) hg
        rw [telescopeMap_inj_assoc, Preadditive.sub_comp, comp_zero] at h
        dsimp only [Functor.const_obj_map]
        rw [Functor.ofSequence_map_homOfLE_succ]
        change f n ≫ (s.inj (n+1) ≫ g) = (s.inj n ≫ g) ≫ 𝟙 Y
        simpa only [Category.comp_id, Category.assoc] using (sub_eq_zero.mp h).symm) }
  refine CokernelCofork.IsColimit.ofπ _ _ (fun g hg => hc.desc (d g hg)) ?_ ?_
  · intro Y g hg
    apply hs.hom_ext
    intro n
    change s.inj n.as ≫ _ = _
    erw [telescopeπ_inj_assoc, hc.fac]
    rfl
  · intro Y g hg m hm
    apply hc.hom_ext
    intro n
    rw [hc.fac]
    change c.ι.app n ≫ m = s.inj n ≫ g
    rw [← hm, telescopeπ_inj_assoc]
    rfl

end

section
universe u
variable {R : Type u} [Ring R]
variable (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (f : ∀ n, K n ⟶ K (n+1))

abbrev moduleTelescopeMap := telescopeMap f _ (moduleSumComplexIsColimit K)

def moduleTelescopeLinear (j : ℤ) : (Π₀ n, (K n).X j) →ₗ[R] (Π₀ n, (K n).X j) :=
  ((moduleTelescopeMap K f).f j).hom

end

universe u w
variable {R : Type u} [Ring R]
variable (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (f : ∀ n, K n ⟶ K (n+1))
variable (c : Cocone (Functor.ofSequence f)) (hc : IsColimit c)

def moduleTelescopeShortComplex : ShortComplex (CochainComplex (ModuleCat R) ℤ) :=
  ShortComplex.mk (moduleTelescopeMap K f)
    (telescopeπ f _ (moduleSumComplexIsColimit K) c)
    (telescope_zero f _ (moduleSumComplexIsColimit K) c)

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_Truncations
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.leftModule _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.DerivedSupport
universe u
variable {R : Type u} [Ring R]

def cutSub (K : CochainComplex (ModuleCat.{u} R) ℤ) (a j : ℤ) : Submodule R (K.X j) :=
  if a ≤ j then ⊤ else ⊥

lemma mem_cutSub {K : CochainComplex (ModuleCat.{u} R) ℤ} {a j : ℤ} {x : K.X j} :
    x ∈ cutSub K a j ↔ a ≤ j ∨ x = 0 := by
  by_cases h : a ≤ j <;> simp [cutSub, h]

lemma cutSub_d {K : CochainComplex (ModuleCat.{u} R) ℤ} {a j k : ℤ}
    {x : K.X j} (hx : x ∈ cutSub K a j) : K.d j k x ∈ cutSub K a k := by
  rw [mem_cutSub] at hx ⊢
  by_cases h : (ComplexShape.up ℤ).Rel j k
  · change j + 1 = k at h
    rcases hx with hx | rfl
    · exact Or.inl (by omega)
    · exact Or.inr (map_zero _)
  · rw [K.shape j k h]
    exact Or.inr rfl

def cut (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    CochainComplex (ModuleCat R) ℤ where
  X j := ModuleCat.of R (cutSub K a j)
  d j k := ModuleCat.ofHom
    { toFun := fun x => ⟨K.d j k x, cutSub_d x.property⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun r x => Subtype.ext (map_smul _ _ _) }
  shape j k hjk := by
    ext x
    change K.d j k x = 0
    rw [K.shape j k hjk]
    rfl
  d_comp_d' j k l hjk hkl := by
    ext x
    exact ConcreteCategory.congr_hom (K.d_comp_d j k l) x

def cutι (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) : cut K a ⟶ K where
  f j := ModuleCat.ofHom (cutSub K a j).subtype
  comm' _ _ _ := rfl

instance cutι_mono (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) : Mono (cutι K a) := by
  apply HomologicalComplex.mono_of_mono_f
  intro j
  exact (ModuleCat.mono_iff_injective _).2 Subtype.val_injective

lemma cutSub_le (K : CochainComplex (ModuleCat.{u} R) ℤ) {a b : ℤ} (h : b ≤ a) (j : ℤ) :
    cutSub K a j ≤ cutSub K b j := by
  intro x hx
  rw [mem_cutSub] at hx ⊢
  exact hx.imp (le_trans h) id

def cutMap (K : CochainComplex (ModuleCat.{u} R) ℤ) {a b : ℤ} (h : b ≤ a) :
    cut K a ⟶ cut K b where
  f j := ModuleCat.ofHom (Submodule.inclusion (cutSub_le K h j))
  comm' _ _ _ := rfl

@[reassoc (attr := simp)]
lemma cutMap_ι (K : CochainComplex (ModuleCat.{u} R) ℤ) {a b : ℤ} (h : b ≤ a) :
    cutMap K h ≫ cutι K b = cutι K a := rfl

lemma cut_isZero_X (K : CochainComplex (ModuleCat.{u} R) ℤ) (a j : ℤ) (h : j < a) :
    IsZero ((cut K a).X j) := by
  apply ModuleCat.isZero_iff_subsingleton.2
  have : cutSub K a j = ⊥ := ite_eq_right (by omega)
  change Subsingleton (cutSub K a j)
  rw [this]
  infer_instance

lemma cutι_f_isIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (a j : ℤ) (h : a ≤ j) :
    IsIso ((cutι K a).f j) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨Subtype.val_injective, fun x => ?_⟩
  exact ⟨⟨x, mem_cutSub.mpr (Or.inl h)⟩, rfl⟩

def cutπ (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    cut K a ⟶ (HomologicalComplex.single (ModuleCat R) (ComplexShape.up ℤ) a).obj (K.X a) :=
  mkHomToSingle ((cutι K a).f a) (fun i hi => by
    have h : i < a := by change i + 1 = a at hi; omega
    exact (cut_isZero_X K a i h).eq_of_src _ _)

lemma cutMap_π (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    cutMap K (show a ≤ a+1 by omega) ≫ cutπ K a = 0 := by
  apply to_single_hom_ext
  apply (cut_isZero_X K (a+1) a (by omega)).eq_of_src

instance cutMap_mono (K : CochainComplex (ModuleCat.{u} R) ℤ) {a b : ℤ} (h : b ≤ a) :
    Mono (cutMap K h) := by
  have : Mono (cutMap K h ≫ cutι K b) := by
    rw [cutMap_ι]
    infer_instance
  exact mono_of_mono _ (cutι K b)

instance cutπ_f_self_isIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    IsIso ((cutπ K a).f a) := by
  dsimp only [cutπ]
  rw [mkHomToSingle_f]
  have := cutι_f_isIso K a a (le_refl a)
  infer_instance

instance cutπ_epi (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) : Epi (cutπ K a) := by
  apply HomologicalComplex.epi_of_epi_f
  intro j
  by_cases h : j = a
  · subst j; infer_instance
  · exact (isZero_single_obj_X (ComplexShape.up ℤ) a (K.X a) j h).epi _

def cutShortComplex (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    ShortComplex (CochainComplex (ModuleCat R) ℤ) :=
  ShortComplex.mk (cutMap K (show a ≤ a+1 by omega)) (cutπ K a) (cutMap_π K a)

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_BoundedGeneration
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.DerivedSupport

section
universe v w
variable {C : Type v} [Category.{w} C]

def eventuallyIsoCoconeIsColimit {F : ℕ ⥤ C} (c : Cocone F) (N : ℕ)
    (h : ∀ n, N ≤ n → IsIso (c.ι.app n)) : IsColimit c := by
  have := h N le_rfl
  refine { desc := fun s => inv (c.ι.app N) ≫ s.ι.app N, fac := ?_, uniq := ?_ }
  · intro s n
    let m := max n N
    have hm : N ≤ m := le_max_right _ _
    have := h m hm
    have he : inv (c.ι.app N) ≫ s.ι.app N = inv (c.ι.app m) ≫ s.ι.app m := by
      apply (cancel_epi (c.ι.app N)).1
      rw [IsIso.hom_inv_id_assoc, ← c.w (homOfLE hm)]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc, s.w]
    rw [he, ← c.w (homOfLE (le_max_left n N))]
    simp only [m, Category.assoc, IsIso.hom_inv_id_assoc, s.w]
  · intro s m hm
    apply (cancel_epi (c.ι.app N)).1
    rw [IsIso.hom_inv_id_assoc, hm]

end

section
universe u
variable {R : Type u} [Ring R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

def cutSequenceMap (n : ℕ) : cut K (-(n : ℤ)) ⟶ cut K (-(n+1 : ℤ)) :=
  cutMap K (by omega)

def cutSequenceCocone : Cocone (Functor.ofSequence (cutSequenceMap K)) where
  pt := K
  ι := NatTrans.ofSequence (fun n => cutι K (-(n : ℤ))) (fun n => by
    simp [cutSequenceMap]
    exact (cutMap_ι K _).trans (Category.comp_id _).symm)

def cutSequenceIsColimit : IsColimit (cutSequenceCocone K) := by
  apply HomologicalComplex.isColimitOfEval
  intro j
  apply eventuallyIsoCoconeIsColimit _ (-j).toNat
  intro n hn
  change IsIso ((cutι K (-(n : ℤ))).f j)
  exact cutι_f_isIso K _ _ (by omega)

end

universe u w

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_UpperTruncation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.leftModule _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.DerivedSupport

section
universe u
variable {R : Type u} [Ring R]

def upperSub (K : CochainComplex (ModuleCat.{u} R) ℤ) (a j : ℤ) : Submodule R (K.X j) :=
  if j < a then ⊤ else if j = a then LinearMap.ker (K.d j (j+1)).hom else ⊥

lemma mem_upperSub {K : CochainComplex (ModuleCat.{u} R) ℤ} {a j : ℤ} {x : K.X j} :
    x ∈ upperSub K a j ↔ j < a ∨ (j = a ∧ K.d j (j+1) x = 0) ∨ x = 0 := by
  by_cases h : j < a
  · simp [upperSub, h]
  · by_cases he : j = a
    · simp [upperSub, he, LinearMap.mem_ker]
      intro hx; subst x; exact map_zero _
    · simp [upperSub, h, he]

lemma upperSub_d {K : CochainComplex (ModuleCat.{u} R) ℤ} {a j k : ℤ}
    {x : K.X j} (hx : x ∈ upperSub K a j) : K.d j k x ∈ upperSub K a k := by
  rw [mem_upperSub] at hx ⊢
  by_cases h : (ComplexShape.up ℤ).Rel j k
  · change j + 1 = k at h
    rcases hx with hx | ⟨rfl, hx⟩ | rfl
    · by_cases hk : k < a
      · exact Or.inl hk
      · exact Or.inr (Or.inl ⟨by omega,
          ConcreteCategory.congr_hom (K.d_comp_d j k (k+1)) x⟩)
    · exact Or.inr (Or.inr (by rw [← h]; exact hx))
    · exact Or.inr (Or.inr (map_zero _))
  · rw [K.shape j k h]
    exact Or.inr (Or.inr rfl)

def upper (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    CochainComplex (ModuleCat R) ℤ where
  X j := ModuleCat.of R (upperSub K a j)
  d j k := ModuleCat.ofHom
    { toFun := fun x => ⟨K.d j k x, upperSub_d x.property⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun r x => Subtype.ext (map_smul _ _ _) }
  shape j k hjk := by
    ext x
    change K.d j k x = 0
    rw [K.shape j k hjk]
    rfl
  d_comp_d' j k l hjk hkl := by
    ext x
    exact ConcreteCategory.congr_hom (K.d_comp_d j k l) x

def upperι (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) : upper K a ⟶ K where
  f j := ModuleCat.ofHom (upperSub K a j).subtype
  comm' _ _ _ := rfl

lemma upper_le (K : CochainComplex (ModuleCat.{u} R) ℤ) {a b : ℤ} (h : a ≤ b) (j : ℤ) :
    upperSub K a j ≤ upperSub K b j := by
  intro x hx
  rw [mem_upperSub] at hx ⊢
  rcases hx with hx | ⟨rfl, hx⟩ | rfl
  · exact Or.inl (lt_of_lt_of_le hx h)
  · rcases lt_or_eq_of_le h with hh | rfl
    · exact Or.inl hh
    · exact Or.inr (Or.inl ⟨rfl, hx⟩)
  · exact Or.inr (Or.inr rfl)

def upperMap (K : CochainComplex (ModuleCat.{u} R) ℤ) {a b : ℤ} (h : a ≤ b) :
    upper K a ⟶ upper K b where
  f j := ModuleCat.ofHom (Submodule.inclusion (upper_le K h j))
  comm' _ _ _ := by ext; rfl

@[reassoc (attr := simp)]
lemma upperMap_ι (K : CochainComplex (ModuleCat.{u} R) ℤ) {a b : ℤ} (h : a ≤ b) :
    upperMap K h ≫ upperι K b = upperι K a := by ext; rfl

lemma upperι_f_isIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (a j : ℤ) (hj : j < a) :
    IsIso ((upperι K a).f j) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨Subtype.val_injective, fun x => ⟨⟨x, by simp [upperSub, hj]⟩, rfl⟩⟩

end

universe u w
variable {R : Type u} [Ring R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

def upperSequenceMap (n : ℕ) : upper K (n : ℤ) ⟶ upper K ((n+1 : ℕ) : ℤ) :=
  upperMap K (by omega)

def upperSequenceCocone : Cocone (Functor.ofSequence (upperSequenceMap K)) where
  pt := K
  ι := NatTrans.ofSequence (fun n => upperι K (n : ℤ)) (fun n => by
    simp [upperSequenceMap]
    exact (upperMap_ι K _).trans (Category.comp_id _).symm)

def upperSequenceIsColimit : IsColimit (upperSequenceCocone K) := by
  apply HomologicalComplex.isColimitOfEval
  intro j
  apply eventuallyIsoCoconeIsColimit _ (j.toNat + 1)
  intro n hn
  change IsIso ((upperι K (n : ℤ)).f j)
  exact upperι_f_isIso K _ _ (by omega)

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Triangular_Algebra
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

def OffDiagonal (_C _E U : Type v) := U

def offValue {C E U : Type v} (x : OffDiagonal C E U) : U := x

namespace OffDiagonal
variable [Ring C] [Ring E] [AddCommGroup U]

instance instAddCommGroup : AddCommGroup (OffDiagonal C E U) := inferInstanceAs (AddCommGroup U)

instance instModuleProd [Module E U] : Module (C × E) (OffDiagonal C E U) :=
  Module.compHom U (RingHom.snd C E)

instance instModuleMulOppositeProd [Module Cᵐᵒᵖ U] : Module (C × E)ᵐᵒᵖ (OffDiagonal C E U) :=
  Module.compHom U (RingHom.fst C E).op

instance instSMulCommClassProdMulOpposite [Module E U] [Module Cᵐᵒᵖ U] [SMulCommClass E Cᵐᵒᵖ U] :
    SMulCommClass (C × E) (C × E)ᵐᵒᵖ (OffDiagonal C E U) where
  smul_comm p q x := by
    change p.2 • (MulOpposite.op q.unop.1 • (offValue x)) =
      MulOpposite.op q.unop.1 • (p.2 • (offValue x))
    exact smul_comm _ _ _

variable (k : Type v) [Field k] [_root_.Algebra k C] [_root_.Algebra k E] [Module k U]

instance instModule : Module k (OffDiagonal C E U) := inferInstanceAs (Module k U)

instance instIsScalarTowerProd [Module E U] [IsScalarTower k E U] :
    IsScalarTower k (C × E) (OffDiagonal C E U) where
  smul_assoc r p x := by
    change (r • p.2) • (offValue x) = r • (p.2 • (offValue x))
    exact smul_assoc _ _ _

instance instIsScalarTowerMulOppositeProd [Module Cᵐᵒᵖ U] [IsScalarTower k Cᵐᵒᵖ U] :
    IsScalarTower k (C × E)ᵐᵒᵖ (OffDiagonal C E U) where
  smul_assoc r p x := by
    change (r • MulOpposite.op p.unop.1) • (offValue x) =
      r • (MulOpposite.op p.unop.1 • (offValue x))
    exact smul_assoc _ _ _

end OffDiagonal

abbrev Algebra := TrivSqZeroExt (C × E) (OffDiagonal C E U)

end TriangularConstruction

end LittleFinitistic
end
end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Triangular_Socle
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instModule _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
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
namespace CummingsConstruction
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]

abbrev NewCorner (k ι : Type u) := ι → DualNumber k

instance instFiniteDimensionalNewCornerOfFinite [Finite ι] : FiniteDimensional k (NewCorner k ι) := by
  let : FiniteDimensional k (DualNumber k) := inferInstanceAs (FiniteDimensional k (k × k))
  exact inferInstanceAs (FiniteDimensional k (ι → DualNumber k))

def newAugmentation : NewCorner k ι →ₐ[k] (ι → k) :=
  AlgHom.pi fun i => (TrivSqZeroExt.fstHom k k k).comp (Pi.evalAlgHom k (fun _ : ι => DualNumber k) i)

def SimpleSum (_χ : C →ₐ[k] (ι → k)) := ι → k

namespace SimpleSum
def value {χ : C →ₐ[k] (ι → k)} (x : SimpleSum χ) : ι → k := x
variable (χ : C →ₐ[k] (ι → k))
instance instAddCommGroup : AddCommGroup (SimpleSum χ) := inferInstanceAs (AddCommGroup (ι → k))
instance instModule : Module k (SimpleSum χ) := inferInstanceAs (Module k (ι → k))
instance instFiniteDimensionalOfFinite [Finite ι] : FiniteDimensional k (SimpleSum χ) := inferInstanceAs (FiniteDimensional k (ι → k))
instance instModuleNewCorner : Module (NewCorner k ι) (SimpleSum χ) :=
  Module.compHom (ι → k) (newAugmentation (k := k) (ι := ι)).toRingHom

def rightCharacter : Cᵐᵒᵖ →+* (ι → k) where
  toFun c := χ c.unop
  map_one' := map_one χ
  map_zero' := map_zero χ
  map_add' x y := map_add χ x.unop y.unop
  map_mul' x y := by simp [map_mul, mul_comm]

instance instModuleMulOpposite : Module Cᵐᵒᵖ (SimpleSum χ) := Module.compHom (ι → k) (rightCharacter χ)

instance instSMulCommClassNewCornerMulOpposite : SMulCommClass (NewCorner k ι) Cᵐᵒᵖ (SimpleSum χ) where
  smul_comm e c x := by
    change newAugmentation e * (rightCharacter χ c * value x) =
      rightCharacter χ c * (newAugmentation e * value x)
    exact mul_left_comm _ _ _

instance instIsScalarTowerNewCorner : IsScalarTower k (NewCorner k ι) (SimpleSum χ) where
  smul_assoc r e x := by
    change newAugmentation (r • e) * value x = r • (newAugmentation e * value x)
    rw [map_smul, smul_mul_assoc]

instance instIsScalarTowerMulOpposite : IsScalarTower k Cᵐᵒᵖ (SimpleSum χ) where
  smul_assoc r c x := by
    change χ (r • c.unop) * value x = r • (χ c.unop * value x)
    rw [map_smul, smul_mul_assoc]
end SimpleSum

variable (χ : C →ₐ[k] (ι → k))
abbrev T := TriangularConstruction.Algebra C (NewCorner k ι) (SimpleSum χ)

instance instAlgebraT : Algebra k (T χ) := inferInstance

def augmentation : T χ →ₐ[k] (Sum ι ι → k) where
  toFun x := Sum.elim (χ x.fst.1) (newAugmentation x.fst.2)
  map_one' := by ext i; cases i <;> simp [newAugmentation]
  map_zero' := by ext i; cases i <;> simp [newAugmentation]
  map_add' x y := by ext i; cases i <;> simp [newAugmentation, map_add]
  map_mul' x y := by ext i; cases i <;> simp [newAugmentation, map_mul]
  commutes' r := by ext i; cases i <;> simp [newAugmentation, Algebra.algebraMap_eq_smul_one]

variable [DecidableEq ι]

def socle : Sum ι ι → T χ
  | .inl i => (0, Pi.single i 1)
  | .inr i => ((0, Pi.single i DualNumber.eps), 0)

lemma socle_mul (i : Sum ι ι) (x : T χ) :
    socle χ i * x = augmentation χ x i • socle χ i := by
  cases i with
  | inl i =>
    apply TrivSqZeroExt.ext
    · change (0 : C × NewCorner k ι) * x.fst = _ • 0
      simp
    · change newAugmentation (0 : NewCorner k ι) * (SimpleSum.value (TriangularConstruction.offValue x.snd)) +
        SimpleSum.rightCharacter χ (MulOpposite.op x.fst.1) * (Pi.single i 1 : ι → k) =
        χ x.fst.1 i • (Pi.single i 1 : ι → k)
      ext j
      by_cases h : j = i
      · subst j; simp [SimpleSum.rightCharacter]
      · simp [h]
  | inr i =>
    apply TrivSqZeroExt.ext
    · apply Prod.ext
      · change (0 : C) * x.fst.1 = _ • 0
        simp
      · change (Pi.single i DualNumber.eps : ι → DualNumber k) * x.fst.2 =
          (x.fst.2 i).fst • (Pi.single i DualNumber.eps : ι → DualNumber k)
        ext j : 1
        by_cases h : j = i
        · subst j
          simp only [Pi.mul_apply, Pi.smul_apply, Pi.single_eq_same]
          apply TrivSqZeroExt.ext <;> simp
        · simp [h]
    · apply funext
      intro j
      change (newAugmentation (Pi.single i (DualNumber.eps : DualNumber k))) j *
        (SimpleSum.value (TriangularConstruction.offValue x.snd)) j + χ x.fst.1 j * 0 =
        (x.fst.2 i).fst * 0
      have he : newAugmentation (Pi.single i (DualNumber.eps : DualNumber k)) = (0 : ι → k) := by
        ext j
        by_cases h : j = i
        · subst j; simp [newAugmentation]
        · simp [newAugmentation, h]
      simp [he]

end CummingsConstruction
end LittleFinitistic
end
end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Kasch_Radical
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
namespace Kasch

universe v w
variable {R : Type u} [Ring R]

abbrev radicalPart (J : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    Submodule R M := J • (⊤ : Submodule R M)

end Kasch
end LittleFinitistic
end
end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Triangular_Augmentation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
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
namespace CummingsConstruction
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]
variable (χ : C →ₐ[k] (ι → k))

def pureOldRadical : Ideal (T χ) where
  carrier := {x | x.fst.2 = 0 ∧ (SimpleSum.value (TriangularConstruction.offValue x.snd)) = 0 ∧ χ x.fst.1 = 0}
  zero_mem' := ⟨rfl, rfl, map_zero χ⟩
  add_mem' := by
    rintro x y ⟨hxe, hxu, hxc⟩ ⟨hye, hyu, hyc⟩
    change x.fst.2 + y.fst.2 = 0 ∧
      SimpleSum.value (TriangularConstruction.offValue x.snd) + SimpleSum.value (TriangularConstruction.offValue y.snd) = 0 ∧ χ (x.fst.1 + y.fst.1) = 0
    simp [hxe, hye, hxu, hyu, hxc, hyc, map_add]
  smul_mem' := by
    rintro r x ⟨hxe, hxu, hxc⟩
    change r.fst.2 * x.fst.2 = 0 ∧
      newAugmentation r.fst.2 * SimpleSum.value (TriangularConstruction.offValue x.snd) +
        χ x.fst.1 * SimpleSum.value (TriangularConstruction.offValue r.snd) = 0 ∧ χ (r.fst.1 * x.fst.1) = 0
    simp [hxe, hxu, hxc, map_mul]

end CummingsConstruction
end LittleFinitistic

end
end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Triangular_InjectiveCorners
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory
namespace LittleFinitistic.CummingsConstruction

section
universe u
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]
variable (χ : C →ₐ[k] (ι → k)) (i : ι)

def cval (r : T χ) : k := χ r.fst.1 i
def ehead (r : T χ) : k := (r.fst.2 i).fst
def etail (r : T χ) : k := (r.fst.2 i).snd
def oval (r : T χ) : k := (SimpleSum.value (TriangularConstruction.offValue r.snd)) i

@[simp] lemma cval_mul (r s : T χ) : cval χ i (r*s) = cval χ i r * cval χ i s := by
  change χ (r.fst.1 * s.fst.1) i = _
  simp [cval]
@[simp] lemma ehead_mul (r s : T χ) : ehead χ i (r*s) = ehead χ i r * ehead χ i s := rfl
@[simp] lemma etail_mul (r s : T χ) : etail χ i (r*s) = ehead χ i r * etail χ i s + ehead χ i s * etail χ i r := by
  change _ * _ + _ * _ = _
  change (r.fst.2 i).fst * (s.fst.2 i).snd + (r.fst.2 i).snd * (s.fst.2 i).fst = _
  dsimp only [ehead, etail]
  ring
@[simp] lemma oval_mul (r s : T χ) : oval χ i (r*s) = ehead χ i r * oval χ i s + cval χ i s * oval χ i r := rfl

def NewInjective (_χ : C →ₐ[k] (ι → k)) (_i : ι) := k × (k × k)
namespace NewInjective

def value (x : NewInjective χ i) : k × (k × k) := x

@[ext] lemma ext {x y : NewInjective χ i}
    (h₁ : (value χ i x).1 = (value χ i y).1)
    (h₂ : (value χ i x).2.1 = (value χ i y).2.1)
    (h₃ : (value χ i x).2.2 = (value χ i y).2.2) : x = y :=
  Prod.ext h₁ (Prod.ext h₂ h₃)
instance instAddCommGroup : AddCommGroup (NewInjective χ i) := inferInstanceAs (AddCommGroup (k × (k × k)))

def act (r : T χ) (x : NewInjective χ i) : NewInjective χ i :=
  (cval χ i r * (value χ i x).1,
    ehead χ i r * (value χ i x).2.1,
    oval χ i r * (value χ i x).1 + etail χ i r * (value χ i x).2.1 + ehead χ i r * (value χ i x).2.2)

instance instSMulT : SMul (T χ) (NewInjective χ i) := ⟨act χ i⟩

instance instModuleT : Module (T χ) (NewInjective χ i) where
  one_smul x := by
    change (χ 1 i * _, (1 * _, 0 * _ + 0 * _ + 1 * _)) = value χ i x
    simp
  mul_smul r s x := by
    change act χ i (r*s) x = act χ i r (act χ i s x)
    simp only [act, value, cval_mul, ehead_mul, etail_mul, oval_mul]
    apply ext <;> dsimp [value, NewInjective] <;> ring
  smul_zero r := by
    change act χ i r (0,0,0) = (0,0,0)
    simp only [act, value, mul_zero, add_zero]
    rfl
  smul_add r x y := by
    apply ext
    · change cval χ i r * (x.1 + y.1) = cval χ i r*x.1 + cval χ i r*y.1
      ring
    · change ehead χ i r * (x.2.1 + y.2.1) = ehead χ i r*x.2.1 + ehead χ i r*y.2.1
      ring
    · change oval χ i r * (x.1+y.1) + etail χ i r * (x.2.1+y.2.1) +
        ehead χ i r * (x.2.2+y.2.2) =
        (oval χ i r*x.1 + etail χ i r*x.2.1 + ehead χ i r*x.2.2) +
        (oval χ i r*y.1 + etail χ i r*y.2.1 + ehead χ i r*y.2.2)
      ring
  add_smul r s x := by
    apply ext
    · change χ (r.fst.1+s.fst.1) i * x.1 = χ r.fst.1 i*x.1 + χ s.fst.1 i*x.1
      simp [map_add, add_mul]
    · change ((r.fst.2 i).fst + (s.fst.2 i).fst)*x.2.1 =
        (r.fst.2 i).fst*x.2.1 + (s.fst.2 i).fst*x.2.1
      ring
    · change (oval χ i r + oval χ i s)*x.1 +
        (etail χ i r + etail χ i s)*x.2.1 +
        (ehead χ i r + ehead χ i s)*x.2.2 =
        (oval χ i r*x.1 + etail χ i r*x.2.1 + ehead χ i r*x.2.2) +
        (oval χ i s*x.1 + etail χ i s*x.2.1 + ehead χ i s*x.2.2)
      ring
  zero_smul x := by
    change (χ 0 i * _, (0 * _, 0 * _ + 0 * _ + 0 * _)) = (0,0,0)
    simp

end NewInjective
end

section
open CategoryTheory
universe u
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]
variable (χ : C →ₐ[k] (ι → k)) (i : ι) [DecidableEq ι]

def newIdem : T χ := ((0, Pi.single i 1), 0)

lemma newIdem_mul (r : T χ) : newIdem χ i * r =
    oval χ i r • socle χ (.inl i) + etail χ i r • socle χ (.inr i) +
    ehead χ i r • newIdem χ i := by
  apply TrivSqZeroExt.ext
  · apply Prod.ext
    · change (0 : C) * r.fst.1 = _
      change 0 * r.fst.1 = (oval χ i r) • (0 : C) + (etail χ i r) • 0 + (ehead χ i r) • 0
      simp
    · change (Pi.single i 1 : ι → DualNumber k) * r.fst.2 =
        (oval χ i r) • (0 : ι → DualNumber k) +
        (etail χ i r) • (Pi.single i (DualNumber.eps : DualNumber k) : ι → DualNumber k) +
        (ehead χ i r) • (Pi.single i (1 : DualNumber k) : ι → DualNumber k)
      ext j : 1
      by_cases hj : j = i
      · subst j
        apply TrivSqZeroExt.ext <;>
          simp [etail, ehead]
      · apply TrivSqZeroExt.ext <;>
          simp [hj]
  · change (newAugmentation (Pi.single i 1 : ι → DualNumber k) *
      SimpleSum.value (TriangularConstruction.offValue r.snd) +
      SimpleSum.rightCharacter χ (MulOpposite.op r.fst.1) * 0) = _
    change (newAugmentation (Pi.single i 1 : ι → DualNumber k) *
      SimpleSum.value (TriangularConstruction.offValue r.snd) +
      SimpleSum.rightCharacter χ (MulOpposite.op r.fst.1) * 0) =
      (oval χ i r) • (Pi.single i (1 : k) : ι → k) + (etail χ i r) • 0 + (ehead χ i r) • 0
    ext j
    by_cases hj : j = i
    · subst j
      simp [oval, newAugmentation]
    · simp [oval, newAugmentation, hj]

abbrev coindField := (ModuleCat.coextendScalars (algebraMap k (T χ))).obj (ModuleCat.of k k)

omit [DecidableEq ι] in
lemma coindField_smul_eval
    (h : (ModuleCat.restrictScalars (algebraMap k (T χ))).obj
      (ModuleCat.of (T χ) (T χ)) →ₗ[k] k) (a : k) (r : T χ) :
    h (a • r) = a • h r := by
  have scalar_eq := h.map_smul a r
  change h (algebraMap k (T χ) a * r) = a • h r at scalar_eq
  calc
    h (a • r) = h (algebraMap k (T χ) a * r) := congrArg h (Algebra.smul_def a r)
    _ = a • h r := scalar_eq

omit [DecidableEq ι] in
lemma coindField_add_eval
    (h : (ModuleCat.restrictScalars (algebraMap k (T χ))).obj
      (ModuleCat.of (T χ) (T χ)) →ₗ[k] k) (r s : T χ) :
    h (r+s) = h r + h s := h.map_add r s

def newInjectiveRetraction : coindField χ ⟶ ModuleCat.of (T χ) (NewInjective χ i) :=
  ModuleCat.ofHom {
    toFun := fun h => (h (socle χ (.inl i)), h (socle χ (.inr i)), h (newIdem χ i))
    map_add' := fun _ _ => rfl
    map_smul' := fun r h => by
      apply NewInjective.ext
      · change h (socle χ (.inl i) * r) = cval χ i r * h (socle χ (.inl i))
        rw [socle_mul, coindField_smul_eval]
        rfl
      · change h (socle χ (.inr i) * r) = ehead χ i r * h (socle χ (.inr i))
        rw [socle_mul, coindField_smul_eval]
        rfl
      · change h (newIdem χ i * r) = oval χ i r * h (socle χ (.inl i)) +
          etail χ i r * h (socle χ (.inr i)) + ehead χ i r * h (newIdem χ i)
        rw [newIdem_mul, coindField_add_eval, coindField_add_eval, coindField_smul_eval,
          coindField_smul_eval, coindField_smul_eval]
        rfl }

end

open CategoryTheory
universe u
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]
variable (χ : C →ₐ[k] (ι → k)) (i : ι) [DecidableEq ι]

def lastCoordinate : (ModuleCat.restrictScalars (algebraMap k (T χ))).obj
    (ModuleCat.of (T χ) (NewInjective χ i)) ⟶ ModuleCat.of k k := ModuleCat.ofHom
  (X := (ModuleCat.restrictScalars (algebraMap k (T χ))).obj
    (ModuleCat.of (T χ) (NewInjective χ i))) (Y := ModuleCat.of k k)
  (show (ModuleCat.restrictScalars (algebraMap k (T χ))).obj
    (ModuleCat.of (T χ) (NewInjective χ i)) →ₗ[k] k from {
  toFun := fun x => (NewInjective.value χ i x).2.2
  map_add' := fun _ _ => rfl
  map_smul' := fun a x => by
    change (NewInjective.act χ i ((algebraMap k (T χ)) a) x).2.2 = a * x.2.2
    change (0 * x.1 + 0 * x.2.1 + a * x.2.2) = a * x.2.2
    simp })

def newInjectiveInclusion : ModuleCat.of (T χ) (NewInjective χ i) ⟶ coindField χ :=
  ModuleCat.RestrictionCoextensionAdj.HomEquiv.fromRestriction _ (lastCoordinate χ i)

end LittleFinitistic.CummingsConstruction

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Triangular_InjectiveResolution
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory
namespace LittleFinitistic.CummingsConstruction
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]
variable (χ : C →ₐ[k] (ι → k)) (i : ι)

def oldCharacter : T χ →+* k :=
  (Pi.evalRingHom (fun _ : Sum ι ι => k) (.inl i)).comp (augmentation χ).toRingHom

def newCharacter : T χ →+* k :=
  (Pi.evalRingHom (fun _ : Sum ι ι => k) (.inr i)).comp (augmentation χ).toRingHom

def newProjection : T χ →+* DualNumber k where
  toFun r := r.fst.2 i
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

abbrev oldSimple := (ModuleCat.restrictScalars (oldCharacter χ i)).obj (ModuleCat.of k k)
abbrev newSimple := (ModuleCat.restrictScalars (newCharacter χ i)).obj (ModuleCat.of k k)
abbrev newRegular := (ModuleCat.restrictScalars (newProjection χ i)).obj (ModuleCat.of (DualNumber k) (DualNumber k))
abbrev newInjectiveObj := ModuleCat.of (T χ) (NewInjective χ i)

def newRegularι : newRegular χ i ⟶ newInjectiveObj χ i := ModuleCat.ofHom
  (X := newRegular χ i) (Y := newInjectiveObj χ i) (show
    newRegular χ i →ₗ[T χ] newInjectiveObj χ i from {
  toFun := fun x => (0,x.fst,x.snd)
  map_add' := fun x y => by
    apply NewInjective.ext (χ := χ) (i := i)
    · exact (zero_add (0 : k)).symm
    · rfl
    · rfl
  map_smul' := fun r x => by
    apply NewInjective.ext (χ := χ) (i := i)
    · change (0 : k) = cval χ i r * 0
      simp
    · rfl
    · change ehead χ i r*x.snd + etail χ i r*x.fst =
        oval χ i r*0 + etail χ i r*x.fst + ehead χ i r*x.snd
      ring })

def newInjectiveπ : newInjectiveObj χ i ⟶ oldSimple χ i := ModuleCat.ofHom
  (X := newInjectiveObj χ i) (Y := oldSimple χ i) (show
    newInjectiveObj χ i →ₗ[T χ] oldSimple χ i from {
  toFun := fun x => x.1
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl })

def newRegularπ : newRegular χ i ⟶ newSimple χ i := ModuleCat.ofHom
  (X := newRegular χ i) (Y := newSimple χ i) (show
    newRegular χ i →ₗ[T χ] newSimple χ i from {
  toFun := fun x => x.fst
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl })

def newSimpleι : newSimple χ i ⟶ newRegular χ i := ModuleCat.ofHom
  (X := newSimple χ i) (Y := newRegular χ i) (show
    newSimple χ i →ₗ[T χ] newRegular χ i from {
  toFun := fun a => (0,a)
  map_add' := fun a b => by
    apply TrivSqZeroExt.ext
    · exact (zero_add (0 : k)).symm
    · rfl
  map_smul' := fun r a => by
    apply TrivSqZeroExt.ext
    · change (0 : k) = ehead χ i r * 0
      simp
    · change ehead χ i r*(show k from a) = ehead χ i r*(show k from a) + etail χ i r*0
      simp })

def newDifferential : newInjectiveObj χ i ⟶ newInjectiveObj χ i := ModuleCat.ofHom
  (X := newInjectiveObj χ i) (Y := newInjectiveObj χ i) (show
    newInjectiveObj χ i →ₗ[T χ] newInjectiveObj χ i from {
  toFun := fun x => (0,0,x.2.1)
  map_add' := fun x y => by
    apply NewInjective.ext (χ := χ) (i := i)
    · exact (zero_add (0 : k)).symm
    · exact (zero_add (0 : k)).symm
    · rfl
  map_smul' := fun r x => by
    apply NewInjective.ext (χ := χ) (i := i)
    · change (0 : k) = cval χ i r * 0
      simp
    · change (0 : k) = ehead χ i r * 0
      simp
    · change ehead χ i r*x.2.1 = oval χ i r*0 + etail χ i r*0 + ehead χ i r*x.2.1
      simp })

def epsDifferential : newRegular χ i ⟶ newRegular χ i := newRegularπ χ i ≫ newSimpleι χ i

@[simp] lemma newDifferential_sq : newDifferential χ i ≫ newDifferential χ i = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

@[simp] lemma epsDifferential_sq : epsDifferential χ i ≫ epsDifferential χ i = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

lemma newRegularι_comm : newRegularι χ i ≫ newDifferential χ i =
    epsDifferential χ i ≫ newRegularι χ i := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

lemma newInjectiveπ_comm : newDifferential χ i ≫ newInjectiveπ χ i = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

lemma newRegularι_π : newRegularι χ i ≫ newInjectiveπ χ i = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

def periodicInjective : ChainComplex (ModuleCat (T χ)) ℕ :=
  ChainComplex.of (fun _ => newInjectiveObj χ i) (fun _ => newDifferential χ i)
    (fun _ => newDifferential_sq χ i)

def periodicRegular : ChainComplex (ModuleCat (T χ)) ℕ :=
  ChainComplex.of (fun _ => newRegular χ i) (fun _ => epsDifferential χ i)
    (fun _ => epsDifferential_sq χ i)

def periodicOld : ChainComplex (ModuleCat (T χ)) ℕ :=
  ChainComplex.of (fun _ => oldSimple χ i) (fun _ => 0) (fun _ => by simp)

def periodicι : periodicRegular χ i ⟶ periodicInjective χ i :=
  ChainComplex.ofHom (fun _ => newRegularι χ i) (fun n => by
    simpa [periodicInjective, periodicRegular] using newRegularι_comm χ i)

def periodicπ : periodicInjective χ i ⟶ periodicOld χ i :=
  ChainComplex.ofHom (fun _ => newInjectiveπ χ i) (fun n => by
    simpa [periodicInjective, periodicOld] using (newInjectiveπ_comm χ i).symm)

lemma periodicι_π : periodicι χ i ≫ periodicπ χ i = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  exact newRegularι_π χ i

lemma epsDifferential_π : epsDifferential χ i ≫ newRegularπ χ i = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

lemma epsDifferential_exact :
    (ShortComplex.mk (epsDifferential χ i) (epsDifferential χ i)
      (epsDifferential_sq χ i)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : x.fst = 0 := congrArg TrivSqZeroExt.snd hx
  refine ⟨(x.snd,0), ?_⟩
  apply TrivSqZeroExt.ext
  · exact hx'.symm
  · rfl

lemma epsDifferential_π_exact :
    (ShortComplex.mk (epsDifferential χ i) (newRegularπ χ i)
      (epsDifferential_π χ i)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  refine ⟨(x.snd,0), ?_⟩
  apply TrivSqZeroExt.ext
  · exact hx.symm
  · rfl

instance newRegularπ_epi : Epi (newRegularπ χ i) := by
  rw [ModuleCat.epi_iff_surjective]
  intro a
  exact ⟨(a,0), rfl⟩

def periodicAug : periodicRegular χ i ⟶ (ChainComplex.single₀ (ModuleCat (T χ))).obj
    (newSimple χ i) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨newRegularπ χ i, epsDifferential_π χ i⟩

instance periodicAug_quasiIso : QuasiIso (periodicAug χ i) := ⟨fun n => by
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · exact ⟨epsDifferential_π_exact χ i, newRegularπ_epi χ i⟩
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
      have hd : ChainComplex.of.d (fun _ : ℕ => newRegular χ i)
          (fun _ : ℕ => epsDifferential χ i) (n+2) (n+1) = epsDifferential χ i :=
        ChainComplex.of_d _ _ (n+1)
      simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
        periodicRegular, hd, ChainComplex.of_d] using epsDifferential_exact χ i
    · apply ChainComplex.exactAt_succ_single_obj⟩

end LittleFinitistic.CummingsConstruction

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Triangular_Generation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
namespace LittleFinitistic.CummingsConstruction
universe u w
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]
variable (χ : C →ₐ[k] (ι → k)) (i : ι)

lemma periodicOld_d (m n : ℕ) : (periodicOld χ i).d m n = 0 := by
  by_cases h : m = n+1
  · subst m
    simp [periodicOld]
    rfl
  · exact (periodicOld χ i).shape m n (by simpa [ComplexShape.down_Rel, eq_comm] using h)

def oldSingleι (n : ℕ) : (HomologicalComplex.single (ModuleCat (T χ)) (.down ℕ) n).obj
    (oldSimple χ i) ⟶ periodicOld χ i :=
  mkHomFromSingle (𝟙 _) (fun j hj => by simp [periodicOld_d]; exact Category.id_comp _)

def oldSingleπ (n : ℕ) : periodicOld χ i ⟶
    (HomologicalComplex.single (ModuleCat (T χ)) (.down ℕ) n).obj (oldSimple χ i) :=
  mkHomToSingle (𝟙 _) (fun j hj => by simp [periodicOld_d]; exact Category.comp_id _)

abbrev extendedInjective := (periodicInjective χ i).extend ComplexShape.embeddingDownNat
abbrev extendedRegular := (periodicRegular χ i).extend ComplexShape.embeddingDownNat

variable [HasDerivedCategory.{w} (ModuleCat.{u} (T χ))]

def regularDerivedIso : DerivedCategory.Q.obj (extendedRegular χ i) ≅
    (DerivedCategory.singleFunctor (ModuleCat (T χ)) 0).obj (newSimple χ i) :=
  asIso (DerivedCategory.Q.map (extendMap (periodicAug χ i) ComplexShape.embeddingDownNat)) ≪≫
    DerivedCategory.Q.mapIso (extendSingleIso ComplexShape.embeddingDownNat (newSimple χ i) 0 0 rfl) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat (T χ)) 0).app (newSimple χ i)).symm

def oldSingleDerivedIso (n : ℕ) :
    DerivedCategory.Q.obj (((HomologicalComplex.single (ModuleCat (T χ)) (.down ℕ) n).obj
      (oldSimple χ i)).extend ComplexShape.embeddingDownNat) ≅
    (DerivedCategory.singleFunctor (ModuleCat (T χ)) (-(n : ℤ))).obj (oldSimple χ i) :=
  DerivedCategory.Q.mapIso (extendSingleIso ComplexShape.embeddingDownNat (oldSimple χ i) n (-(n : ℤ)) rfl) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat (T χ)) (-n)).app (oldSimple χ i)).symm

end LittleFinitistic.CummingsConstruction

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Asymmetry
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open CategoryTheory
namespace LittleFinitistic.AsymmetryConstruction
universe u
variable {k A ι : Type u} [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [Nontrivial A] [Fintype ι]
variable (χ : Aᵐᵒᵖ →ₐ[k] (ι → k))
abbrev Lambda := (CummingsConstruction.T χ)ᵐᵒᵖ

end LittleFinitistic.AsymmetryConstruction

end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Augmentation_Directed
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
abbrev Vertices := {i : Fin n // D.e i ≠ 0}
def coefficient (a : A) (i : D.Vertices) : k := (D.diagonal i a).choose
lemma coefficient_spec (a : A) (i : D.Vertices) :
    D.e i * a * D.e i = D.coefficient a i • D.e i := (D.diagonal i a).choose_spec
lemma coefficient_eq_iff (a : A) (i : D.Vertices) (c : k) :
    D.coefficient a i = c ↔ D.e i * a * D.e i = c • D.e i := by
  rw [D.coefficient_spec]
  exact (smul_left_injective k i.property).eq_iff.symm

lemma corner_mul (a b : A) (i j : Fin n) :
    D.e i * (a * b) * D.e j = ∑ l, (D.e i * a * D.e l) * (D.e l * b * D.e j) := by
  conv_rhs => arg 2; ext l; rw [mul_assoc, ← mul_assoc (D.e l), ← mul_assoc (D.e l), D.idem]
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, D.complete]
  simp [mul_assoc]

lemma diagonal_mul (a b : A) (i : Fin n) :
    D.e i * (a * b) * D.e i = (D.e i * a * D.e i) * (D.e i * b * D.e i) := by
  rw [D.corner_mul, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hji | hij
    · rw [D.directed i j hji b, mul_zero]
    · rw [D.directed j i hij a, zero_mul]
  · simp

end DirectedSystem
end LittleFinitistic.DirectedBound

end
end

end OAI
end

section
-- module Solutions.Q221_FA.Finitistic_Localization_ConcreteTensorEvaluation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorLinear _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.commute _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.towerLeft _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TensorComplex.scalarTower
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.Free.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.Free.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimap_comp _root_.OAI.LittleFinitistic.BalancedTensor.bimap_mk _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_left _root_.OAI.LittleFinitistic.BalancedTensor.bimap_zero_right _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRightTo_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.smul_mk _root_.OAI.LittleFinitistic.BimoduleTotal.coefficient_at _root_.OAI.LittleFinitistic.BimoduleTotal.insertion_same _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_apply _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_comp _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_mk _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_left _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_right _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_id _root_.OAI.LittleFinitistic.ComplexTensor.column_d _root_.OAI.LittleFinitistic.ComplexTensor.finiteTotalMap_apply _root_.OAI.LittleFinitistic.ComplexTensor.inputMap_comp _root_.OAI.LittleFinitistic.ComplexTensor.inputMap_id _root_.OAI.LittleFinitistic.ComplexTensor.map_comp _root_.OAI.LittleFinitistic.ComplexTensor.map_id_left _root_.OAI.LittleFinitistic.ComplexTensor.map_zero_left _root_.OAI.LittleFinitistic.ComplexTensor.map_zero_right _root_.OAI.LittleFinitistic.ComplexTensor.matrix_apply _root_.OAI.LittleFinitistic.CornerProjection.projection_apply _root_.OAI.LittleFinitistic.PDBarQuotient.forward_mk _root_.OAI.LittleFinitistic.PDBarQuotient.inverse_quotient _root_.OAI.LittleFinitistic.PDResidueAssociativity.inner_mk _root_.OAI.LittleFinitistic.PDResidueAssociativity.inverse_mk _root_.OAI.LittleFinitistic.PDTensor.mapRight_mk _root_.OAI.LittleFinitistic.PDTensor.residueEval_mk _root_.OAI.LittleFinitistic.PDTensor.residueInverse_mk _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.ofModule_generator _root_.OAI.LittleFinitistic.QuadraticEncoding.actionArrow_zero _root_.OAI.LittleFinitistic.QuotientAction.quotientAction_generator _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis _root_.OAI.LittleFinitistic.TensorArrowSum.insertion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits Category
namespace LittleFinitistic.ConcreteTensorEvaluation
open QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type u} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

section TensorCongr
variable {A : Type u} [Ring A] [Algebra k A]
variable {M M' N : Type u} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N]
variable [Module k M] [Module k M'] [Module k N]
variable [Module Aᵐᵒᵖ M] [Module Aᵐᵒᵖ M'] [Module A N]
variable [IsScalarTower k Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M']

/-- Balanced tensor respects actual right-module equivalences. -/
def tensorCongr (e : M ≃ₗ[Aᵐᵒᵖ] M') :
    BalancedTensor.Tensor k A M N ≃ₗ[k] BalancedTensor.Tensor k A M' N where
  __ := BalancedTensor.mapLeft (k := k) N e.toLinearMap
  invFun := BalancedTensor.mapLeft (k := k) N e.symm.toLinearMap
  left_inv z := by
    change BalancedTensor.mapLeft (k := k) N e.symm.toLinearMap
      (BalancedTensor.mapLeft (k := k) N e.toLinearMap z) = z
    induction z using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => simp
    | ha a b ha hb =>
      simp only [map_add]
      exact congrArg₂ (· + ·) ha hb
  right_inv z := by
    change BalancedTensor.mapLeft (k := k) N e.toLinearMap
      (BalancedTensor.mapLeft (k := k) N e.symm.toLinearMap z) = z
    induction z using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => simp
    | ha a b ha hb =>
      simp only [map_add]
      exact congrArg₂ (· + ·) ha hb
end TensorCongr

/-- Actual tensor evaluation on projectives. -/
abbrev moduleEvaluation : SourceVerdier.Proj P ⥤ ModuleCat.{u} k :=
  (ProjectiveComplexes.finiteProjective (B P)).ι ⋙
    BalancedTensor.tensorFunctor k (B P) X.Evaluation

/-- The exact natural vertex identification E_i tensor_B M(Y) = Y. -/
def vertexIso (i : Fin 3) : (moduleEvaluation X).obj (SourceVerdier.E P i) ≅ ModuleCat.of k Y :=
  ((@tensorCongr k _ (B P) _ _
    (BalancedTensor.ScalarModule k (B P) (SourceVerdier.E P i).obj)
    (IdempotentTensor.rightIdeal (SourceVerdier.vertex P i)) X.Evaluation
    _ _ _ (BalancedTensor.ScalarModule k (B P) (SourceVerdier.E P i).obj).isModule _ _
    _ _ _ (vertexScalarTower (P := P) i) inferInstance
    (idealEquiv (SourceVerdier.vertex P i) (SourceVerdier.vertex_idem P i))).trans
      (X.vertexTensorEquiv i)).toModuleIso

@[simp] theorem vertexIso_mk (i : Fin 3)
    (m : BalancedTensor.ScalarModule k (B P) (SourceVerdier.E P i).obj) (y : X.Evaluation) :
    (vertexIso X i).hom.hom
      (BalancedTensor.mk k (B P) _ X.Evaluation m y) = X.projection i (m.val.unop • y) := rfl

end LittleFinitistic.ConcreteTensorEvaluation

end

end OAI
end

section
-- module Solutions.Q221_FA.Finitistic_Rectification_ExternalTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.ExternalTensor.columnInclusion_apply _root_.OAI.LittleFinitistic.TensorComplex.mapRight_tmul _root_.OAI.LittleFinitistic.TensorProjection.mem_fixed _root_.OAI.LittleFinitistic.TensorProjection.rightMap_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped TensorProduct


noncomputable section
namespace ExternalTensor

variable (k B M N : Type*) [Field k] [Ring B] [Algebra k B]
  [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]
  [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N] [IsScalarTower k Bᵐᵒᵖ N]

attribute [local instance] bimodule rightModule

variable {k B M N}
variable {M' N' : Type*}
  [AddCommGroup M'] [Module k M'] [Module B M'] [IsScalarTower k B M']
  [AddCommGroup N'] [Module k N'] [Module Bᵐᵒᵖ N'] [IsScalarTower k Bᵐᵒᵖ N']

variable {M'' N'' : Type*}
  [AddCommGroup M''] [Module k M''] [Module B M''] [IsScalarTower k B M'']
  [AddCommGroup N''] [Module k N''] [Module Bᵐᵒᵖ N''] [IsScalarTower k Bᵐᵒᵖ N'']

/-- The same tensor map as a map of right B-modules. -/
def rightMap (f : M →ₗ[B] M') (g : N →ₗ[Bᵐᵒᵖ] N') :
    (M ⊗[k] N) →ₗ[Bᵐᵒᵖ] (M' ⊗[k] N') where
  __ := (map (k := k) f g).toAddMonoidHom
  map_smul' c x := by
    change map (k := k) f g (c • x) = c • map (k := k) f g x
    rw [right_eq_enveloping, right_eq_enveloping, LinearMap.map_smul]

@[simp] theorem rightMap_tmul (f : M →ₗ[B] M') (g : N →ₗ[Bᵐᵒᵖ] N') (m : M) (n : N) :
    rightMap (k := k) f g (m ⊗ₜ[k] n) = f m ⊗ₜ[k] g n := rfl
end ExternalTensor

end

end OAI
end


