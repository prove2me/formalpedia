-- Prove2me | Definitions.Def_OAIQ032L023
-- name    : OAIQ032L023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:02:56.945825+00:00
-- url     : https://prove2.me/theorems/ec9b5bf6-4102-4fde-ad2d-4169fd45b5bf
-- title:
--   Definitions bundle OAIQ032L023 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 86 declarations of OpenAI's Lean: 39 definitions, 13 instances and 34 theorems. The definitions and types are `OAI.Lech.ReesRoot.renamedModule`, `OAI.Lech.RestrictedPolynomialCech.termEquiv`, `OAI.Lech.RestrictedPolynomialImageCech.cochains`, `OAI.Lech.RestrictedPolynomialImageCech.d`, `OAI.Lech.RootTower.normalizedLength`, `OAI.Lech.RootTower.perfectAlgEquiv`, `OAI.Lech.RootTower.perfectAlgHom`, `OAI.Lech.RootTower.perfectBasis`, `OAI.Lech.RootTower.regularTower`, `OAI.Lech.RootTower.restrictRootShift`, `OAI.Lech.RootTower.rootEquiv`, `OAI.Lech.RootTower.rootShiftEquiv`, `OAI.Lech.SignedCech.augmented`, `OAI.Lech.SignedCech.bicRowHomotopy`, `OAI.Lech.SignedCech.cochainHomotopy`, `OAI.Lech.SignedCech.cochainMultiply`, `OAI.Lech.SignedCech.cochainPiIso`, `OAI.Lech.SignedCech.complex`, `OAI.Lech.SignedCech.inclusion`, `OAI.Lech.SignedCech.multiply`, `OAI.Lech.SignedCech.positive`, `OAI.Lech.SignedCech.positiveInclusion`, `OAI.Lech.SignedCech.positiveMultiply`, `OAI.Lech.SignedCech.positiveRowHomotopy`, `OAI.Lech.SignedCech.positiveXIso`, `OAI.Lech.SignedCech.twistStep`, `OAI.Lech.SourceGraded.augmentedThickeningZeroIso`, `OAI.Lech.SourceGraded.thickeningComparison`, `OAI.Lech.SourceGraded.thickeningTensorBottomIso`, `OAI.Lech.TensorIdeal.fibreKernelEquiv`, `OAI.Lech.TensorTotal.singleRingHomologyIso`, `OAI.Lech.TensorTotal.splitting`, `OAI.Lech.TotalGhost.imageLift`, `OAI.Lech.TraceConductor.perfectOrder`, `OAI.Lech.TraceConductor.perfectOrderAt`, `OAI.Lech.scalarHomologyCokernelEmbedding`, `OAI.Lech.scalarQuotientCokernelIso`, `OAI.Lech.scalarQuotientShortComplex`, `OAI.Lech.scalarQuotientTransport`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_BicomplexImageLift`, `Multiplicity_CompleteResidueExtension`, `Multiplicity_FibreSquare`, `Multiplicity_FilteredCechAugmentationRing`, `Multiplicity_FiniteComplexTopInclusion`, `Multiplicity_FrobeniusIntermediatePowerMap`, `Multiplicity_GradedChartCochains`, `Multiplicity_LechCokernelComp`, `Multiplicity_NormalizedLengthTrivialRelation`, `Multiplicity_ReesExceptionalRing`, `Multiplicity_ReesExceptionalSquare`, `Multiplicity_RootTowerLengthEq`, `Multiplicity_RootTowerNormalizedLength`, `Multiplicity_RootTowerRemainderExponent`, `Multiplicity_ScalarHomologyError`, `Multiplicity_ScalarQuotientTransport`, `Multiplicity_SignedCechBicRow`, `Multiplicity_SourceGradedCechHomology`, `Multiplicity_TensorPushout`, `Multiplicity_TraceConductorPerfectOrder`.
--
--   **Imports.** It imports the bundles `OAIQ032L011`, `OAIQ032L012`, `OAIQ032L014`, `OAIQ032L015`, `OAIQ032L016` and `OAIQ032L017` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ032L027`; the statements `OAI.Lech.FrobeniusIntermediate.normalizedLength_intermediate_tensor`, `OAI.Lech.PerfectDomainStages.frobenius_module_length_tendsto`, `OAI.Lech.PerfectDomainStages.normalizedLength_actual_stage_quotient`, `OAI.Lech.PerfectDomainStages.normalizedLength_scalar_stage_quotient`, `OAI.Lech.PerfectDomainStages.normalizedLength_stage_homology`, `OAI.Lech.PerfectDomainStages.normalizedLength_stage_scalar_quotient_homology`, `OAI.Lech.PerfectDomainStages.stage_tensor_length_tendsto`, `OAI.Lech.RootTower.normalizedLength_eq_zero_of_root_annihilated`, `OAI.Lech.SeparableOrder.exists_normalization_frobenius_module_limit`, `OAI.Lech.SeparableOrder.normalizedLength_coordinate_power_koszul` and `OAI.Lech.SeparableOrder.normalizedLength_perfection_shortComplex_homology`; the proofs of `OAI.Lech.CharP.exists_length_with_module_limit`, `OAI.Lech.CharP.normalized_perfection_module_finite`, `OAI.Lech.FilteredCech.positive_homology_powerTorsion`, `OAI.Lech.FiniteModuleCech.tensorEuler_copies`, `OAI.Lech.FiniteModuleCech.tensor_euler_rank_zero`, `OAI.Lech.FrobeniusIntermediate.normalizedLength_intermediate_tensor`, `OAI.Lech.PerfectDomainStages.frobenius_homology_conductor_bound`, `OAI.Lech.PerfectDomainStages.frobenius_module_length_tendsto`, `OAI.Lech.PerfectDomainStages.normalizedLength_actual_stage_quotient`, `OAI.Lech.PerfectDomainStages.normalizedLength_scalar_stage_quotient`, `OAI.Lech.PerfectDomainStages.normalizedLength_stage_homology`, `OAI.Lech.PerfectDomainStages.normalizedLength_stage_scalar_quotient_homology`, `OAI.Lech.PerfectDomainStages.stage_tensor_length_tendsto`, `OAI.Lech.PowerSeries.maximal_power_colength`, `OAI.Lech.RootTower.normalizedLength_eq_zero_of_root_annihilated`, `OAI.Lech.SeparableOrder.exists_normalization_frobenius_module_limit`, `OAI.Lech.SeparableOrder.normalizedLength_coordinate_power_koszul`, `OAI.Lech.SeparableOrder.normalizedLength_perfection_shortComplex_homology`, `OAI.Lech.TensorIdeal.fibreMap_kernel_zero` and `OAI.Lech.exists_scalar_extension_homology_bound`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L011
import Definitions.Def_OAIQ032L012
import Definitions.Def_OAIQ032L014
import Definitions.Def_OAIQ032L015
import Definitions.Def_OAIQ032L016
import Definitions.Def_OAIQ032L017

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteComplexTopInclusion
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
namespace Lech

section

section
universe u
variable {R : Type u} [CommRing R]


instance powerTorsion_serre (I : Ideal R) : (powerTorsion I).IsSerreClass where
  exists_zero := ⟨0, isZero_zero _, powerTorsion_zero I (isZero_zero _)⟩
  prop_of_mono f _ h := powerTorsion_mono I f h
  prop_of_epi f _ h := powerTorsion_epi I f h
  prop_X₂_of_shortExact h h₁ h₃ := powerTorsion_extension I h.exact h₁ h₃


end


universe u v
end


universe u
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_GradedChartCochains
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.RestrictedPolynomialCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
attribute [local instance] MvPolynomial.gradedAlgebra


def termEquiv (h : ℕ) (s : Finset (Fin h)) (t : ℕ) :
    GradedChart.term (grade R S h) MvPolynomial.X s t ≃ₗ[R]
      GradedChart.term (MvPolynomial.homogeneousSubmodule (Fin h) S) MvPolynomial.X s t :=
  (LinearEquiv.ofEq _ _ (TwistedLocalization.piece_restrictScalars (R := R)
    (MvPolynomial.homogeneousSubmodule (Fin h) S) t)).trans
    ((Submodule.restrictScalarsEquiv R S _ _).restrictScalars R)

lemma termEquiv_naturality {h : ℕ} {s v : Finset (Fin h)} (hsv : s ⊆ v) (t : ℕ)
    (x : GradedChart.term (grade R S h) MvPolynomial.X s t) :
    termEquiv R S h v t (GradedChart.restrict (grade R S h) MvPolynomial.X
      (MvPolynomial.isHomogeneous_X S) hsv t x) =
    GradedChart.restrict (MvPolynomial.homogeneousSubmodule (Fin h) S) MvPolynomial.X
      (MvPolynomial.isHomogeneous_X S) hsv t (termEquiv R S h s t x) := by
  apply Subtype.ext
  rfl

end Lech.RestrictedPolynomialCech


namespace Lech.RestrictedPolynomialImageCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
  {h : ℕ} (H : ℕ → Submodule R B) [GradedAlgebra H]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (g : (RestrictedPolynomialCech.grade R S h) →+*ᵍ H)
  (hg : ∀ (r : R) (a : MvPolynomial (Fin h) S), g (r • a) = r • g a)

abbrev cochains (n t : ℕ) := ImageCech.cochains _ H g MvPolynomial.X n t

def d (n t : ℕ) : cochains H g n t →ₗ[R] cochains H g (n+1) t :=
  ImageCech.d _ H g MvPolynomial.X (MvPolynomial.isHomogeneous_X S) n t

end Lech.RestrictedPolynomialImageCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechCokernelComp
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]


variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
  {F G H : CochainComplex (ModuleCat.{u} R) ℤ}



@[reassoc (attr := simp)] lemma ι_degreeMap (a : ∀ j, F.X j ⟶ G.X j)
    (p q i : ℤ) (hpq : p+q=i) :
    ιMapBifunctor F K (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq ≫ degreeMap K a i =
      ((curriedTensor (ModuleCat.{u} R)).map (a p)).app (K.X q) ≫
        ιMapBifunctor G K (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq := by
  apply ι_mapBifunctorDesc

lemma degreeMap_id (i : ℤ) : degreeMap K (fun j => 𝟙 (F.X j)) i = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  change _ = ιMapBifunctor F K (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq ≫
    𝟙 ((mapBifunctor F K (curriedTensor (ModuleCat.{u} R)) (.up ℤ)).X i)
  simp

lemma degreeMap_comp (a : ∀ j, F.X j ⟶ G.X j) (b : ∀ j, G.X j ⟶ H.X j) (i : ℤ) :
    degreeMap K (fun j => a j ≫ b j) i=degreeMap K a i ≫ degreeMap K b i := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  refine (ι_degreeMap K (fun j => a j ≫ b j) p q i hpq).trans ?_
  simp only [Functor.map_comp, NatTrans.comp_app]
  exact (Category.assoc _ _ _).trans
    ((congrArg (((curriedTensor (ModuleCat.{u} R)).map (a p)).app (K.X q) ≫ ·)
      (ι_degreeMap K b p q i hpq).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ degreeMap K b i) (ι_degreeMap K a p q i hpq).symm).trans
            (Category.assoc _ _ _))))

lemma degreeMap_add (a b : ∀ j, F.X j ⟶ G.X j) (i : ℤ) :
    degreeMap K (fun j => a j+b j) i=degreeMap K a i+degreeMap K b i := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  refine (ι_degreeMap K (fun j => a j + b j) p q i hpq).trans ?_
  simp only [Functor.map_add, NatTrans.app_add]
  exact (Preadditive.add_comp _ _ _ _ _ _).trans
    ((congrArg₂ (· + ·) (ι_degreeMap K a p q i hpq).symm
      (ι_degreeMap K b p q i hpq).symm).trans (Preadditive.comp_add _ _ _ _ _ _).symm)

lemma map_f (f : F ⟶ G) (i : ℤ) :
    ((functor K).map f).f i=degreeMap K f.f i := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  simp only [functor]
  refine (ι_mapBifunctorMap f (𝟙 K) (curriedTensor (ModuleCat.{u} R)) (.up ℤ)
    p q i hpq).trans ?_
  exact (congrArg (fun t => ((curriedTensor (ModuleCat.{u} R)).map (f.f p)).app (K.X q) ≫
    t ≫ ιMapBifunctor G K (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq)
      (((curriedTensor (ModuleCat.{u} R)).obj (G.X p)).map_id (K.X q))).trans
    ((congrArg (((curriedTensor (ModuleCat.{u} R)).map (f.f p)).app (K.X q) ≫ ·)
      (Category.id_comp _)).trans (ι_degreeMap K f.f p q i hpq).symm)

instance instAdditiveCochainComplexModuleCatIntFunctor : (functor K).Additive where
  map_add {F G} f g := by
    apply HomologicalComplex.Hom.ext
    funext i
    change ((functor K).map (f+g)).f i=((functor K).map f).f i+((functor K).map g).f i
    simp only [map_f]
    exact degreeMap_add K f.f g.f i

 

def splitting (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (s : ∀ j, (S.map (eval (ModuleCat.{u} R) (.up ℤ) j)).Splitting) (i : ℤ) :
    ((S.map (functor K)).map (eval (ModuleCat.{u} R) (.up ℤ) i)).Splitting where
  r := degreeMap K (fun j => (s j).r) i
  s := degreeMap K (fun j => (s j).s) i
  f_r := by
    change ((functor K).map S.f).f i ≫ degreeMap K (fun j => (s j).r) i = 𝟙 (((functor K).obj S.X₁).X i)
    erw [map_f,←degreeMap_comp]
    erw [show (fun j => S.f.f j ≫ (s j).r)=(fun j => 𝟙 (S.X₁.X j)) from
      funext (fun j => (s j).f_r),degreeMap_id]
  s_g := by
    change degreeMap K (fun j => (s j).s) i ≫ ((functor K).map S.g).f i = 𝟙 (((functor K).obj S.X₃).X i)
    erw [map_f,←degreeMap_comp]
    erw [show (fun j => (s j).s ≫ S.g.f j)=(fun j => 𝟙 (S.X₃.X j)) from
      funext (fun j => (s j).s_g),degreeMap_id]
  id := by
    change degreeMap K (fun j => (s j).r) i ≫ ((functor K).map S.f).f i + ((functor K).map S.g).f i ≫ degreeMap K (fun j => (s j).s) i = 𝟙 (((functor K).obj S.X₂).X i)
    erw [map_f,map_f,←degreeMap_comp,←degreeMap_comp,←degreeMap_add]
    erw [show (fun j => (show S.X₂.X j ⟶ S.X₁.X j from (s j).r) ≫ S.f.f j + S.g.f j ≫ (show S.X₃.X j ⟶ S.X₂.X j from (s j).s))=
      (fun j => 𝟙 (S.X₂.X j)) from funext (fun j => (s j).id),degreeMap_id]

 

def singleRingHomologyIso (j i : ℤ) :
    ((functor K).obj ((single (ModuleCat.{u} R) (.up ℤ) j).obj (ModuleCat.of R R))).homology i ≅
      K.homology (i-j) := by
  let U := (single (ModuleCat.{u} R) (.up ℤ) 0).obj (ModuleCat.of R R)
  let e : U⟦-j⟧ ≅ (single (ModuleCat.{u} R) (.up ℤ) j).obj (ModuleCat.of R R) :=
    ((CochainComplex.singleFunctors (ModuleCat.{u} R)).shiftIso (-j) j 0 (by omega)).app _
  let e' : (functor K).obj ((single (ModuleCat.{u} R) (.up ℤ) j).obj (ModuleCat.of R R)) ≅ K⟦-j⟧ :=
    (functor K).mapIso e.symm ≪≫
      CochainComplex.mapBifunctorShift₁Iso U K (curriedTensor (ModuleCat.{u} R)) (-j) ≪≫
      (shiftFunctor _ (-j)).mapIso (HomologicalComplex.leftUnitor K)
  exact (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso e' ≪≫
    ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftIso (-j) i (i-j) (by omega)).app K
end Lech.TensorTotal
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredCechAugmentationRing
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)

noncomputable def augmentedThickeningZeroIso (M : ℕ) :
    (augmentedThickening I z hz M).X 0 ≅ ModuleCat.of R (R ⧸ I^M) :=
  (finiteThickening I z hz 0 M).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl ≪≫
    finiteThickeningZeroIso I z hz M



variable (F : CochainComplex (ModuleCat.{u} R) ℤ)

noncomputable def thickeningTensorBottomIso (M : ℕ) :
    (TensorTotal.Right.functor F).obj ((single (ModuleCat.{u} R) (.up ℤ) 0).obj
      ((augmentedThickening I z hz M).X 0)) ≅ (complexQuotient (I^M) (.up ℤ)).obj F :=
  (TensorTotal.Right.functor F).mapIso
    ((single (ModuleCat.{u} R) (.up ℤ) 0).mapIso (augmentedThickeningZeroIso I z hz M)) ≪≫
    TensorTotal.tensorSingleQuotientIso (I^M) F

 

noncomputable def thickeningComparison (M : ℕ) (i : ℤ) :
    ((complexQuotient (I^M) (.up ℤ)).obj F).homology i ⟶
      ((TensorTotal.Right.functor F).obj (thickeningCech I z hz M)).homology (i+1) :=
  ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso (thickeningTensorBottomIso I z hz F M)).inv ≫
    TensorTotal.bottomComparison F (augmentedThickening I z hz M)
      (augmentedThickening_boundedBelow I z hz M) i

end Lech.SourceGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SourceGradedCechHomology
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators


namespace Lech.SignedCech
section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

def complex (t : ℤ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  LocalizationCech.complex z (term I z t) (restriction_mem I z hz t)

def inclusion {s t : ℤ} (hst : s ≤ t) : complex I z hz t ⟶ complex I z hz s :=
  LocalizationCech.inclusion z _ _ _ _ (fun _ => SignedFraction.antitone I _ _ hst)

instance inclusion_mono {s t : ℤ} (hst : s ≤ t) : Mono (inclusion I z hz hst) := by
  apply mono_of_mono_f
  intro n
  apply (ModuleCat.mono_iff_injective _).mpr
  exact LocalizationCech.inclusionLinear_injective z (term I z t) (term I z s)
    (fun _ => SignedFraction.antitone I _ _ hst) n

end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

def augmented (t : ℤ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (complex I z hz t).extend ComplexShape.embeddingUpNat

lemma augmented_boundedBelow (t : ℤ) :
    ∀ i, i < (0 : ℤ) → IsZero ((augmented I z hz t).X i) := by
  intro i hi
  apply (complex I z hz t).isZero_extend_X
  intro n hn
  change (n : ℤ)=i at hn
  omega

 

def positive (t : ℤ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  FiniteComplex.dropBottom (augmented I z hz t) 0 (augmented_boundedBelow I z hz t)

lemma positive_boundedBelow (t : ℤ) :
    ∀ q, q≤(0 : ℤ) → IsZero ((positive I z hz t).X q) := by
  intro q hq
  exact FiniteComplex.dropBottom_boundedBelow _ _ _ q (by omega)

def positiveInclusion {s t : ℤ} (hst : s ≤ t) : positive I z hz t ⟶ positive I z hz s :=
  FiniteComplex.dropBottomMap (augmented I z hz t) 0 (augmented_boundedBelow I z hz t)
    (augmented_boundedBelow I z hz s) (extendMap (inclusion I z hz hst) ComplexShape.embeddingUpNat)

def positiveXIso (t : ℤ) (n : ℕ) (hn : 0<n) :
    (positive I z hz t).X (n : ℤ) ≅ (complex I z hz t).X n :=
  FiniteComplex.dropBottomXIso _ _ _ (n : ℤ) (by omega) ≪≫
    (complex I z hz t).extendXIso ComplexShape.embeddingUpNat (i := n) rfl

@[reassoc] lemma positiveXIso_inclusion {s t : ℤ} (hst : s ≤ t) (n : ℕ) (hn : 0<n) :
    (positiveXIso I z hz t n hn).hom ≫ (inclusion I z hz hst).f n =
      (positiveInclusion I z hz hst).f (n : ℤ) ≫ (positiveXIso I z hz s n hn).hom := by
  have he := congrArg (fun f => f.f (n : ℤ))
    (FiniteComplex.dropBottomMap_ι (augmented I z hz t) 0 (augmented_boundedBelow I z hz t)
      (augmented_boundedBelow I z hz s) (extendMap (inclusion I z hz hst) ComplexShape.embeddingUpNat))
  dsimp only [positiveXIso,Iso.trans_hom,FiniteComplex.dropBottomXIso,asIso_hom,positiveInclusion]
  exact component_iso_square_p1
    ((complex I z hz t).extendXIso ComplexShape.embeddingUpNat (i := n) rfl)
    ((complex I z hz s).extendXIso ComplexShape.embeddingUpNat (i := n) rfl)
    _ _ _ _ _
    (extendMap_f (inclusion I z hz hst) ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)) he

end Lech.SignedCech


namespace Lech.SignedCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Lech.TensorTotal
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℕ)
  (H : ∀ i, Homotopy (z i ^ m • 𝟙 F) 0)



def cochainPiIso (t : ℤ) (n : ℕ) :
    (complex I z hz t).X n ≅ TensorPi.modulePi (fun a : Fin n → Fin h =>
      ModuleCat.of R (term I z t (ActualCech.intersection a))) := Iso.refl _

lemma cochainPiIso_inclusion {s t : ℤ} (hst : s≤t) (n : ℕ) :
    (cochainPiIso I z hz t n).hom ≫ TensorPi.piMap (fun a : Fin n → Fin h =>
      ModuleCat.ofHom (Submodule.inclusion (SignedFraction.antitone I
        (GradedChart.denominator z (ActualCech.intersection a))
        (ActualCech.intersection a).card hst))) =
      (inclusion I z hz hst).f n ≫ (cochainPiIso I z hz s n).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

def cochainHomotopy (t : ℤ) (n : ℕ) (hn : 0<n) :
    Homotopy (termTensorMap F ((complex I z hz (t+(m:ℤ))).X n)
      ((inclusion I z hz (by omega : t ≤ t+(m:ℤ))).f n)) 0 := by
  let Q : (Fin n → Fin h) → ModuleCat.{u} R := fun a =>
    ModuleCat.of R (term I z (t+(m:ℤ)) (ActualCech.intersection a))
  let Q' : (Fin n → Fin h) → ModuleCat.{u} R := fun a =>
    ModuleCat.of R (term I z t (ActualCech.intersection a))
  let inc : ∀ a, Q a ⟶ Q' a := fun _ =>
    ModuleCat.ofHom (Submodule.inclusion (SignedFraction.antitone I _ _ (by omega : t ≤ t+(m:ℤ))))
  have HH := TensorPi.homotopy (Q := Q) (Q' := Q') F inc
    (intersectionHomotopy I z hz F m H t n hn)
  exact coefficientHomotopyOfIso F (cochainPiIso I z hz (t+(m:ℤ)) n) (cochainPiIso I z hz t n)
    _ _ (cochainPiIso_inclusion I z hz (by omega : t ≤ t+(m:ℤ)) n) HH

 

def positiveRowHomotopy (t : ℤ) (q : ℤ) :
    Homotopy (termTensorMap F ((positive I z hz (t+(m:ℤ))).X q)
      ((positiveInclusion I z hz (by omega : t ≤ t+(m:ℤ))).f q)) 0 := by
  by_cases hq : q ≤ 0
  · have hf : (positiveInclusion I z hz (by omega : t ≤ t+(m:ℤ))).f q=0 :=
      (positive_boundedBelow I z hz (t+(m:ℤ)) q hq).eq_of_src _ _
    rw [hf,termTensorMap_zero]
  · have hn : 0<q.toNat := by omega
    have heq : (q.toNat:ℤ)=q := by omega
    have HH := coefficientHomotopyOfIso F (positiveXIso I z hz (t+(m:ℤ)) q.toNat hn)
      (positiveXIso I z hz t q.toNat hn) _ _ (positiveXIso_inclusion I z hz _ q.toNat hn)
      (cochainHomotopy I z hz F m H t q.toNat hn)
    rw [heq] at HH
    exact HH
end Lech.SignedCech
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SignedCechBicRow
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
namespace Lech.SignedCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Lech.FilteredCech (tensorBic )
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℕ)
  (H : ∀ i, Homotopy (z i ^ m • 𝟙 F) 0)

def bicRowHomotopy (t : ℤ) :
    TotalGhost.RowHomotopy ((tensorBic F).map
      (positiveInclusion I z hz (by omega : t ≤ t+(m:ℤ)))) :=
  TotalGhost.RowHomotopy.ofRows (positiveRowHomotopy I z hz F m H t)


def twistStep (t : ℤ) (n : ℕ) :
    positive I z hz (twistIndex t m (n+1)) ⟶ positive I z hz (twistIndex t m n) :=
  positiveInclusion I z hz (by dsimp only [twistIndex]; omega)

end Lech.SignedCech


namespace Lech.SignedCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i∈I)

instance inclusion_f_mono {s t : ℤ} (hst : s ≤ t) (n : ℕ) :
    Mono ((inclusion I z hz hst).f n) :=
  (ModuleCat.mono_iff_injective _).mpr
    (LocalizationCech.inclusionLinear_injective z (term I z t) (term I z s)
      (fun _ => SignedFraction.antitone I _ _ hst) n)

 

def cochainMultiply (t : ℤ) (M : ℕ) (a : R) (ha : a∈I^M) (n : ℕ) :
    (complex I z hz t).X n ⟶ (complex I z hz (t+(M:ℤ))).X n :=
  ModuleCat.ofHom
    { toFun x b := SignedFraction.multiply I _ _
        (FilteredCech.denominator_mem I z hz (ActualCech.intersection b)) t M a ha (x b)
      map_add' x y := by funext b; exact map_add _ _ _
      map_smul' r x := by
        funext b
        exact map_smul (SignedFraction.multiply I _ _
          (FilteredCech.denominator_mem I z hz (ActualCech.intersection b)) t M a ha) r (x b) }

lemma cochainMultiply_inclusion (t : ℤ) (M : ℕ) (a : R) (ha : a∈I^M) (n : ℕ) :
    cochainMultiply I z hz t M a ha n ≫
      (inclusion I z hz (by omega : t ≤ t+(M:ℤ))).f n = a • 𝟙 ((complex I z hz t).X n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

def multiply (t : ℤ) (M : ℕ) (a : R) (ha : a∈I^M) :
    complex I z hz t ⟶ complex I z hz (t+(M:ℤ)) :=
  ComplexLift.lift (inclusion I z hz (by omega : t ≤ t+(M:ℤ))) (a • 𝟙 _)
    (cochainMultiply I z hz t M a ha) (cochainMultiply_inclusion I z hz t M a ha)

@[reassoc] lemma multiply_inclusion (t : ℤ) (M : ℕ) (a : R) (ha : a∈I^M) :
    multiply I z hz t M a ha ≫ inclusion I z hz (by omega : t ≤ t+(M:ℤ)) =
      a • 𝟙 (complex I z hz t) := ComplexLift.lift_comp _ _ _ _

 
def positiveMultiply (t : ℤ) (M : ℕ) (a : R) (ha : a∈I^M) :
    positive I z hz t ⟶ positive I z hz (t+(M:ℤ)) :=
  FiniteComplex.dropBottomMap (augmented I z hz t) 0 (augmented_boundedBelow I z hz t)
    (augmented_boundedBelow I z hz (t+(M:ℤ)))
    (extendMap (multiply I z hz t M a ha) ComplexShape.embeddingUpNat)

end Lech.SignedCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_BicomplexImageLift
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.TotalGhost
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R] {K L M : Bic (R:=R)}
  (f : K ⟶ L) (hf : ∀ p q,Function.Injective ((f.f p).f q).hom) (g : M ⟶ L)
  (hr : ∀ p q,((g.f p).f q).hom.range≤((f.f p).f q).hom.range)
def imageLift : M ⟶ K := by
  letI : ∀ p, Mono (f.f p) := fun p =>
    mono_of_mono_f _ (fun q => (ModuleCat.mono_iff_injective _).mpr (hf p q))
  exact ComplexLift.factor f g (imageRowLift f hf g hr) (imageRowLift_comp f hf g hr)
end Lech.TotalGhost

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerRemainderExponent
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical

open scoped TensorProduct
open IsLocalRing

open MvPowerSeries IsLocalRing


namespace Lech.RootTower
variable (A : Type*) [CommRing A] [IsReduced A] (p : ℕ) [Fact p.Prime] [CharP A p]


lemma rootRing_mono : Monotone (rootRing A p) := by
  intro n m h x hx
  obtain ⟨a, rfl⟩ := hx
  exact ⟨iterateFrobenius A p (m-n) a, rootMap_transition A p n m h a⟩

def rootEquiv (n : ℕ) : A ≃+* rootRing A p n :=
  RingEquiv.ofBijective (rootMap A p n).rangeRestrict
    ⟨fun _ _ h => rootMap_injective A p n (congrArg Subtype.val h),
      (rootMap A p n).rangeRestrict_surjective⟩

lemma rootEquiv_apply (n : ℕ) (a : A) :
    (rootEquiv A p n a : PerfectClosure A p) = rootMap A p n a := rfl

lemma rootRing_exhaustive (x : PerfectClosure A p) : ∃ n, x ∈ rootRing A p n := by
  obtain ⟨⟨n,a⟩, rfl⟩ := PerfectClosure.mk_surjective A p x
  exact ⟨n, a, rfl⟩

instance rootRing_local [IsLocalRing A] (n : ℕ) : IsLocalRing (rootRing A p n) :=
  (rootEquiv A p n).isLocalRing

instance rootRing_noetherian [IsNoetherianRing A] (n : ℕ) :
    IsNoetherianRing (rootRing A p n) :=
  isNoetherianRing_of_ringEquiv A (rootEquiv A p n)

lemma root_inclusion_eq (n m : ℕ) (h : n ≤ m) :
    Subring.inclusion (rootRing_mono A p h) =
      (rootEquiv A p m).toRingHom.comp
        ((iterateFrobenius A p (m-n)).comp (rootEquiv A p n).symm.toRingHom) := by
  ext x
  change (x : PerfectClosure A p) = rootMap A p m
    (iterateFrobenius A p (m-n) ((rootEquiv A p n).symm x))
  rw [rootMap_transition A p n m h]
  exact congrArg Subtype.val ((rootEquiv A p n).apply_symm_apply x).symm

lemma root_inclusion_flat (hflat : ∀ j, (iterateFrobenius A p j).Flat)
    (n m : ℕ) (h : n ≤ m) : (Subring.inclusion (rootRing_mono A p h)).Flat := by
  rw [root_inclusion_eq A p n m h]
  exact ((RingHom.Flat.of_bijective (rootEquiv A p n).symm.bijective).comp
    (hflat (m-n))).comp (RingHom.Flat.of_bijective (rootEquiv A p m).bijective)

lemma root_inclusion_local [IsLocalRing A] (n m : ℕ) (h : n ≤ m) :
    IsLocalHom (Subring.inclusion (rootRing_mono A p h)) := by
  rw [root_inclusion_eq A p n m h]
  let := iterateFrobenius_local A p (m-n)
  let : IsLocalHom (rootEquiv A p m).toRingHom :=
    ⟨fun x hx => by simpa using hx.map (rootEquiv A p m).symm.toMonoidHom⟩
  let : IsLocalHom (rootEquiv A p n).symm.toRingHom :=
    ⟨fun x hx => by simpa using hx.map (rootEquiv A p n).toMonoidHom⟩
  infer_instance

end Lech.RootTower


namespace Lech.RootTower



open IsLocalRing
variable (A : Type*) [CommRing A] [IsReduced A] [IsLocalRing A]
  (p : ℕ) [Fact p.Prime] [CharP A p]

omit [IsLocalRing A] in
lemma root_inclusion_comp_equiv (n m : ℕ) (h : n ≤ m) :
    (Subring.inclusion (rootRing_mono A p h)).comp (rootEquiv A p n).toRingHom =
      (rootEquiv A p m).toRingHom.comp (iterateFrobenius A p (m-n)) := by
  rw [root_inclusion_eq A p n m h]
  ext a
  simp

lemma root_fiber_ideal (n m : ℕ) (h : n ≤ m) :
    (maximalIdeal (rootRing A p n)).map (Subring.inclusion (rootRing_mono A p h)) =
      ((maximalIdeal A).map (iterateFrobenius A p (m-n))).map (rootEquiv A p m) := by
  calc
    _ = ((maximalIdeal A).map (rootEquiv A p n).toRingHom).map
        (Subring.inclusion (rootRing_mono A p h)) :=
      congrArg (Ideal.map (Subring.inclusion (rootRing_mono A p h)))
        (map_ringEquiv_maximalIdeal (rootEquiv A p n)).symm
    _ = (maximalIdeal A).map ((Subring.inclusion (rootRing_mono A p h)).comp
        (rootEquiv A p n).toRingHom) :=
      (maximalIdeal A).map_map _ _
    _ = (maximalIdeal A).map ((rootEquiv A p m).toRingHom.comp
        (iterateFrobenius A p (m-n))) :=
      congrArg (fun f => (maximalIdeal A).map f) (root_inclusion_comp_equiv A p n m h)
    _ = _ := (Ideal.map_map (I := maximalIdeal A) (iterateFrobenius A p (m-n))
      (rootEquiv A p m).toRingHom).symm

lemma root_fiber_length (n m : ℕ) (h : n ≤ m) :
    Module.length (rootRing A p m) ((rootRing A p m) ⧸
      (maximalIdeal (rootRing A p n)).map (Subring.inclusion (rootRing_mono A p h))) =
      Module.length A (A ⧸ (maximalIdeal A).map (iterateFrobenius A p (m-n))) :=
  (quotient_length_ringEquiv (rootEquiv A p m) _ _ (root_fiber_ideal A p n m h)).symm

end Lech.RootTower
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_NormalizedLengthTrivialRelation
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum

open TensorProduct


namespace Lech.RootTower
open scoped ENNReal
variable (σ k : Type*) [Fintype σ] [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p] [PerfectRing k p]

 
def regularTower : Lech.NormalizedLength.Tower (PerfectClosure (MvPowerSeries σ k) p) where
  ring := rootRing (MvPowerSeries σ k) p
  mono := rootRing_mono (MvPowerSeries σ k) p
  localRing := fun n => rootRing_local (MvPowerSeries σ k) p n
  noetherian := fun n => rootRing_noetherian (MvPowerSeries σ k) p n
  exhaustive := rootRing_exhaustive (MvPowerSeries σ k) p
  weight n := ((p : ℝ≥0∞) ^ (n * Fintype.card σ))⁻¹
  weight_ne_zero n := by simp
  weight_ne_top n := by
    apply ENNReal.inv_ne_top.mpr
    exact pow_ne_zero _ (by exact_mod_cast (Nat.Prime.ne_zero (Fact.out : p.Prime)))
  local_inclusion := root_inclusion_local (MvPowerSeries σ k) p
  flat n m h := (root_inclusion_flat (MvPowerSeries σ k) p
    (fun j => iterateFrobenius_flat (σ := σ) (R := k) p j) n m h)
  weight_mul_fiber n m h := by
    dsimp only
    rw [root_fiber_length (MvPowerSeries σ k) p n m h]
    have hf := frobenius_fiber_length (σ := σ) (k := k) p (m-n)
    change Module.length (MvPowerSeries σ k)
      ((MvPowerSeries σ k) ⧸ (IsLocalRing.maximalIdeal (MvPowerSeries σ k)).map
        (iterateFrobenius (MvPowerSeries σ k) p (m-n))) = _ at hf
    rw [hf]
    simpa using root_weight_mul p (Fintype.card σ) n m (Nat.Prime.pos Fact.out) h

end Lech.RootTower


namespace Lech.RootTower
open scoped ENNReal TensorProduct
variable (σ k : Type*) [Fintype σ] [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p] [PerfectRing k p]

 
def normalizedLength (M : Type*) [AddCommGroup M]
    [Module (PerfectClosure (MvPowerSeries σ k) p) M] : ℝ≥0∞ :=
  (regularTower σ k p).length M

end Lech.RootTower


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerLengthEq
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct


namespace Lech.RootTower
variable {A B : Type*} [CommRing A] [IsReduced A] [CommRing B] [IsReduced B]
variable (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

lemma perfectMap_injective (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (perfectMap p f) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨⟨n,a⟩,rfl⟩ := PerfectClosure.mk_surjective A p x
  change perfectMap p f (rootMap A p n a) = 0 at hx
  rw [perfectMap_root, ← (rootMap B p n).map_zero] at hx
  have ha : a = 0 := hf ((rootMap_injective B p n hx).trans f.map_zero.symm)
  change rootMap A p n a = 0
  rw [ha, map_zero]

end Lech.RootTower


namespace Lech.RootTower
variable (A : Type*) [CommRing A] [IsDomain A] (p : ℕ) [Fact p.Prime] [CharP A p]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] [CharP K p]

instance perfectDomain : IsDomain (PerfectClosure A p) :=
  Function.Injective.isDomain (perfectMap p (algebraMap A (FractionRing A)))
    (perfectMap_injective p _ (IsFractionRing.injective _ _))

instance perfectFraction : IsFractionRing (PerfectClosure A p) (PerfectClosure K p) := by
  let : FaithfulSMul (PerfectClosure A p) (PerfectClosure K p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (perfectMap_injective p _ (IsFractionRing.injective _ _))
  apply IsFractionRing.of_field
  intro z
  obtain ⟨⟨n,x⟩,rfl⟩ := PerfectClosure.mk_surjective K p z
  obtain ⟨a,b,hb,rfl⟩ := IsFractionRing.div_surjective A x
  refine ⟨rootMap A p n a, rootMap A p n b, ?_⟩
  change rootMap K p n (algebraMap A K a / algebraMap A K b) =
    perfectMap p (algebraMap A K) _ / perfectMap p (algebraMap A K) _
  rw [perfectMap_root, perfectMap_root, map_div₀]

instance perfectNormal [IsIntegrallyClosed A] : IsIntegrallyClosed (PerfectClosure A p) := by
  let K := FractionRing A
  let Q := PerfectClosure K p
  let : Algebra A Q := ((PerfectClosure.of K p).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K Q := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A (PerfectClosure A p) Q := IsScalarTower.of_algebraMap_eq' (by
    exact (PerfectRing.lift_comp _ _ _).symm)
  apply (isIntegrallyClosed_iff Q).mpr
  intro x hx
  have hxA : IsIntegral A x := isIntegral_trans x hx
  obtain ⟨n,y,hy⟩ := IsPRadical.pow_mem (PerfectClosure.of K p) p x
  have hyi : IsIntegral A y := by
    apply IsIntegral.tower_bot (R := A) (PerfectClosure.of K p).injective
    change IsIntegral A (PerfectClosure.of K p y)
    rw [hy]
    exact hxA.pow _
  obtain ⟨a,ha⟩ := (isIntegrallyClosed_iff K).mp (inferInstance : IsIntegrallyClosed A) hyi
  refine ⟨rootMap A p n a, ?_⟩
  apply (injective_frobenius Q p).iterate n
  rw [iterate_frobenius, iterate_frobenius, ← map_pow, rootMap_pow]
  change perfectMap p (algebraMap A K) (PerfectClosure.of A p a) = x^(p^n)
  rw [show perfectMap p (algebraMap A K) (PerfectClosure.of A p a) =
      PerfectClosure.of K p (algebraMap A K a) from PerfectRing.lift_comp_apply _ _ _ _]
  rw [ha, hy]

end Lech.RootTower


namespace Lech.RootTower
open Module
variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p]

instance perfectExtensionTower : IsScalarTower K (PerfectClosure K p) (PerfectClosure L p) :=
  IsScalarTower.of_algebraMap_eq' (PerfectRing.lift_comp _ _ _).symm

lemma perfect_span [FiniteDimensional K L] :
    Submodule.span (PerfectClosure K p) (Set.range (PerfectClosure.of L p)) = ⊤ := by
  let f := perfectOf K L p
  let S := Algebra.adjoin (PerfectClosure K p) (f.range : Set (PerfectClosure L p))
  let b := (Module.Free.chooseBasis K L).map (AlgEquiv.ofInjective f f.injective).toLinearEquiv
  have hS : S.toSubmodule.FG := by
    rw [show S.toSubmodule = Submodule.span (PerfectClosure K p)
      (Set.range fun i => ((b i : f.range) : PerfectClosure L p)) from
      f.range.adjoin_eq_span_basis _ b]
    exact Submodule.fg_span (Set.finite_range _)
  have : FiniteDimensional (PerfectClosure K p) S :=
    (Submodule.fg_iff_finiteDimensional S.toSubmodule).mp hS
  let E := Algebra.IsAlgebraic.toIntermediateField S
  have : FiniteDimensional (PerfectClosure K p) E := ‹FiniteDimensional (PerfectClosure K p) S›
  let : PerfectField E := Algebra.IsAlgebraic.perfectField (PerfectClosure K p)
  have hE : ∀ x : PerfectClosure L p, x ∈ E := by
    intro x
    obtain ⟨⟨n,a⟩,rfl⟩ := PerfectClosure.mk_surjective L p x
    have ha : PerfectClosure.of L p a ∈ E := Algebra.subset_adjoin ⟨a,rfl⟩
    obtain ⟨y,hy⟩ := (surjective_frobenius E p).iterate n ⟨_,ha⟩
    have hp : (y : PerfectClosure L p)^(p^n) = PerfectClosure.of L p a := by
      exact congrArg Subtype.val (by simpa only [iterate_frobenius] using hy)
    have heq : (y : PerfectClosure L p) = rootMap L p n a := by
      apply (injective_frobenius (PerfectClosure L p) p).iterate n
      rw [iterate_frobenius, iterate_frobenius, hp, rootMap_pow]
    change rootMap L p n a ∈ E
    rw [← heq]
    exact y.property
  apply top_unique
  intro x _
  have hx : x ∈ S.toSubmodule := hE x
  rw [show S.toSubmodule = Submodule.span (PerfectClosure K p)
    (Set.range fun i => ((b i : f.range) : PerfectClosure L p)) from
    f.range.adjoin_eq_span_basis _ b] at hx
  apply (Submodule.span_mono (s := Set.range fun i => ((b i : f.range) : PerfectClosure L p)) (t := Set.range (PerfectClosure.of L p)) ?_) hx
  rintro x ⟨i,rfl⟩
  exact (b i).property

lemma perfect_basis_independent [Algebra.IsSeparable K L] {ι : Type*} (b : Basis ι K L) :
    LinearIndependent (PerfectClosure K p) (fun i => PerfectClosure.of L p (b i)) := by
  let : IsPurelyInseparable K (PerfectClosure K p) :=
    (isPurelyInseparable_iff_pow_mem K p).mpr (by
      intro x
      change ∃ n, x ^ p ^ n ∈ (PerfectClosure.of K p).range
      exact IsPRadical.pow_mem (PerfectClosure.of K p) p x)
  apply LinearIndependent.map_of_isPurelyInseparable_of_isSeparable (F := K)
  · intro i
    exact (Algebra.IsSeparable.isSeparable K (b i)).map (perfectOf K L p) (perfectOf K L p).injective
  · exact b.linearIndependent.map' (perfectOf K L p).toLinearMap
      (LinearMap.ker_eq_bot.mpr (perfectOf K L p).injective)




lemma perfect_basis_span [FiniteDimensional K L] {ι : Type*} [Fintype ι] (b : Basis ι K L) :
    Submodule.span (PerfectClosure K p) (Set.range fun i => PerfectClosure.of L p (b i)) = ⊤ := by
  apply top_unique
  rw [← perfect_span K L p]
  apply Submodule.span_le.mpr
  rintro x ⟨l,rfl⟩
  rw [← b.sum_repr l, map_sum]
  apply Submodule.sum_mem
  intro i _
  change (perfectOf K L p) ((b.repr l i) • b i) ∈ _
  rw [map_smul]
  rw [← IsScalarTower.algebraMap_smul (PerfectClosure K p)]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

noncomputable def perfectBasis [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ι : Type*} [Fintype ι] (b : Basis ι K L) : Basis ι (PerfectClosure K p) (PerfectClosure L p) :=
  Basis.mk (perfect_basis_independent K L p b) (le_of_eq (perfect_basis_span K L p b).symm)

instance perfectExtensionFinite [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    FiniteDimensional (PerfectClosure K p) (PerfectClosure L p) :=
  Module.Finite.of_basis (perfectBasis K L p (Module.Free.chooseBasis K L))

end Lech.RootTower


namespace Lech.RootTower
variable (A : Type*) [CommRing A] [IsDomain A] (L : Type*) [Field L] [Algebra A L]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP L p]

instance perfectOriginalRootTower : IsScalarTower A (PerfectClosure A p) (PerfectClosure L p) :=
  IsScalarTower.of_algebraMap_eq' (PerfectRing.lift_comp _ _ _).symm

variable (K : Type*) [Field K] [CharP K p] [Algebra A K] [Algebra K L] [IsScalarTower A K L]
instance perfectScalarTower :
    IsScalarTower (PerfectClosure A p) (PerfectClosure K p) (PerfectClosure L p) := by
  apply IsScalarTower.of_algebraMap_eq'
  change perfectMap p (algebraMap A L) =
    (perfectMap p (algebraMap K L)).comp (perfectMap p (algebraMap A K))
  rw [perfectMap_comp,← IsScalarTower.algebraMap_eq]

end Lech.RootTower


namespace Lech.TraceConductor
open Lech.RootTower
variable (A D K L : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing D] [IsDomain D] [Field K] [Field L]
  [Algebra A D] [Algebra A K] [IsFractionRing A K]
  [Algebra A L] [Algebra D L] [IsFractionRing D L] [IsScalarTower A D L]
  [Algebra K L] [IsScalarTower A K L] [Algebra.IsIntegral A D]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP D p] [CharP K p] [CharP L p]

 
def perfectOrder : Subalgebra (PerfectClosure A p) (PerfectClosure L p) :=
  Algebra.adjoin (PerfectClosure A p) (Set.range ((PerfectClosure.of L p).comp (algebraMap D L)))

end Lech.TraceConductor
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TraceConductorPerfectOrder
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
namespace Lech.TraceConductor
open Lech.RootTower
variable (A D L : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Field L] [Algebra A L] [Algebra D L]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP L p]

 
def perfectOrderAt (n : ℕ) : Subalgebra (PerfectClosure A p) (PerfectClosure L p) :=
  Algebra.adjoin (PerfectClosure A p) (Set.range ((rootMap L p n).comp (algebraMap D L)))

end Lech.TraceConductor

open scoped TensorProduct nonZeroDivisors
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusIntermediatePowerMap
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct


namespace Lech.RootTower
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
open scoped ENNReal Classical
variable (A : Type*) [CommRing A] [IsReduced A] (p : ℕ) [Fact p.Prime] [CharP A p]

noncomputable def rootShiftEquiv (n d : ℕ) : rootRing A p n ≃+* rootRing A p (n+d) :=
  (rootEquiv A p n).symm.trans (rootEquiv A p (n+d))

lemma rootShiftEquiv_val (n d : ℕ) (x : rootRing A p n) :
    (rootShiftEquiv A p n d x : PerfectClosure A p) =
      (iterateFrobeniusEquiv (PerfectClosure A p) p d).symm (x : PerfectClosure A p) := by
  obtain ⟨a,rfl⟩ := (rootEquiv A p n).surjective x
  change rootMap A p (n+d) ((rootEquiv A p n).symm (rootEquiv A p n a)) = _
  rw [RingEquiv.symm_apply_apply,rootMap_shift,rootEquiv_apply]

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module (PerfectClosure A p) M] [Module (PerfectClosure A p) N]
noncomputable def restrictRootShift (d : ℕ)
    (E : LinearEquiv (σ' := ((iterateFrobeniusEquiv (PerfectClosure A p) p d) : PerfectClosure A p →+* PerfectClosure A p))
      ((iterateFrobeniusEquiv (PerfectClosure A p) p d).symm : PerfectClosure A p →+* PerfectClosure A p) M N) (n : ℕ) :
    LinearEquiv (σ' := ((rootShiftEquiv A p n d).symm : rootRing A p (n+d) →+* rootRing A p n))
      (rootShiftEquiv A p n d : rootRing A p n →+* rootRing A p (n+d)) M N where
  toAddEquiv := E.toAddEquiv
  map_smul' a x := by
    change E ((a : PerfectClosure A p) • x) =
      (rootShiftEquiv A p n d a : PerfectClosure A p) • E x
    rw [E.map_smulₛₗ,rootShiftEquiv_val]
    rfl

end Lech.RootTower


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerNormalizedLength
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct


namespace Lech.RootTower
variable {A B : Type*} [CommRing A] [IsReduced A] [CommRing B] [IsReduced B]
variable (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

 
lemma perfectMap_surjective (f : A →+* B)
    (h : ∃ n : ℕ, ∀ b : B, ∃ a : A, f a = b^(p^n)) :
    Function.Surjective (perfectMap p f) := by
  obtain ⟨n,hn⟩ := h
  intro z
  obtain ⟨⟨m,b⟩,rfl⟩ := PerfectClosure.mk_surjective B p z
  obtain ⟨a,ha⟩ := hn b
  refine ⟨rootMap A p (m+n) a,?_⟩
  rw [perfectMap_root,ha]
  change rootMap B p (m+n) (b^(p^n)) = rootMap B p m b
  simpa only [Nat.add_sub_cancel_left,iterateFrobenius_def] using
    rootMap_transition B p m (m+n) (Nat.le_add_right m n) b

end Lech.RootTower


namespace Lech.RootTower
open Lech.PerfectDomainStages
variable {A B D : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [CommRing D] [IsDomain D] [Algebra A B] [Algebra A D]
    (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p] [CharP D p]

def perfectAlgHom (f : B →ₐ[A] D) :
    PerfectClosure B p →ₐ[PerfectClosure A p] PerfectClosure D p where
  __ := perfectMap p f.toRingHom
  commutes' a := by
    change perfectMap p f.toRingHom (perfectMap p (algebraMap A B) a) =
      perfectMap p (algebraMap A D) a
    have hf : f.toRingHom.comp (algebraMap A B) = algebraMap A D := f.comp_algebraMap
    rw [← RingHom.comp_apply,perfectMap_comp,hf]

noncomputable def perfectAlgEquiv (f : B →ₐ[A] D) (hi : Function.Injective f)
    (he : ∃ e : ℕ, ∀ x : D, ∃ b : B, f b = x^(p^e)) :
    PerfectClosure B p ≃ₐ[PerfectClosure A p] PerfectClosure D p :=
  AlgEquiv.ofBijective (perfectAlgHom p f)
    ⟨perfectMap_injective p f.toRingHom hi, perfectMap_surjective p f.toRingHom he⟩

end Lech.RootTower


open scoped Classical Pointwise
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CompleteResidueExtension
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open IsLocalRing TensorProduct
namespace Lech.ResidueCompletion
variable {T K : Type*} [CommRing T] [IsLocalRing T] [Field K]

lemma noetherian (fg : (maximalIdeal T).FG) (φ : K →+* T)
    (hφ : Function.Surjective ((residue T).comp φ)) :
    IsNoetherianRing (AdicCompletion (maximalIdeal T) T) := by
  let := AdicCompletion.isLocalRing_of_fg fg
  let := AdicCompletion.isAdicComplete_of_fg fg
  apply Lech.CompleteLocal.noetherian_of_coefficient_and_fg (coefficient φ)
    (coefficient_surjective fg φ hφ)
  rw [AdicCompletion.maximalIdeal_eq_map_of_fg fg]
  exact fg.map _

end Lech.ResidueCompletion

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FibreSquare
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory
open scoped TensorProduct
universe u

section Square
variable {R A B C D : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [AddCommGroup C] [Module A C] [Module R C] [IsScalarTower R A C]
  [AddCommGroup D] [Module A D] [Module R D] [IsScalarTower R A D]
  (I : Ideal R) (a : A →ₗ[A] C) (b : B →ₗ[A] D) (g : C →ₗ[A] D)
  (ha : Function.Surjective a) (hb : Function.Surjective b)
  (hka : (a.restrictScalars R).ker = I • (⊤ : Submodule R A))
  (hkb : (b.restrictScalars R).ker = I • (⊤ : Submodule R B))
  (hsq : b 1=g (a 1))
  (V : Type u) [AddCommGroup V] [Module A V] [Module R V] [IsScalarTower R A V]

include hsq in
lemma fibre_square (x : V ⧸ (I • (⊤ : Submodule R V))) :
    quotientTensorEquiv I b hb hkb V (fibreMap I (A:=A) (B:=B) V x) =
      g.rTensor V (quotientUnitTensorEquiv I a ha hka V x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ v =>
    rw [fibreMap,idealQuotientMap_mk,quotientUnitTensorEquiv_mk]
    change quotientTensorEquiv I b hb hkb V (Submodule.Quotient.mk (1 ⊗ₜ[A] v)) = _
    rw [quotientTensorEquiv_mk,hsq]
    rfl

def fibreKernelEquiv : (fibreMap I (A:=A) (B:=B) V).ker ≃ₗ[R]
    ((g.rTensor V).restrictScalars R).ker :=
  kernelSquareEquiv (fibreMap I (A:=A) (B:=B) V) ((g.rTensor V).restrictScalars R)
    (quotientUnitTensorEquiv I a ha hka V) (quotientTensorEquiv I b hb hkb V)
      (fibre_square I a b g ha hb hka hkb hsq V)

end Square
end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesExceptionalRing
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.FilteredFraction
open HomogeneousLocalization IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {w : R} {d : ℕ} (hw : w ∈ I^d)
attribute [local instance] Homogeneous.awayAddCommGroup
attribute [local irreducible] quotientGraded Homogeneous.awayMap TwistedLocalization.piece TwistedLocalization.pieceMap TwistedLocalization.gradedMap

attribute [local instance] OAI.Lech.FilteredFraction.reesChartCommRing
attribute [local instance] OAI.Lech.FilteredFraction.reesChartModule
local instance reesChartTower : IsScalarTower R R (ReesChart I hw) :=
  ⟨fun a b c => mul_smul a b c⟩

attribute [local irreducible] TwistedLocalization.ambientMap

end Lech.FilteredFraction

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesExceptionalSquare
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open MvPolynomial HomogeneousLocalization IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

local instance renamedModule (s : Finset (Fin (n+1))) :
    Module R (FilteredFraction.ReesChart I (product_mem I z hz s)) :=
  Homogeneous.module (reesGrade I) (Submonoid.powers (FilteredFraction.reesDenominator I (product_mem I z hz s)))

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorPushout
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open TensorProduct

namespace Lech.TensorConductor
variable {D R M N X : Type*} [CommRing D] [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup X]
  [Module D M] [Module D N] [Module D X]
  [Module R M] [Module R N] [SMulCommClass D R M] [SMulCommClass D R N]
@[simp] lemma congrLeft_tmul (e : M ≃ₗ[D] N) (he : ∀ (r : R) x, e (r • x) = r • e x)
    (m : M) (x : X) : congrLeft e he (m ⊗ₜ[D] x) = e m ⊗ₜ[D] x := rfl
end Lech.TensorConductor

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarHomologyError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped Pointwise
namespace Lech
universe u
variable {R : Type u} [CommRing R]

lemma scalar_comp_quotientπ (g : R) (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    (g • 𝟙 F) ≫ complexQuotientπ (Ideal.span {g}) F = 0 := by
  ext i : 1
  apply ModuleCat.hom_ext
  ext x
  change (Ideal.span {g} • (⊤ : Submodule R (F.X i))).mkQ (g • x) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [← scalar_range_eq]
  exact ⟨x,rfl⟩

def scalarQuotientShortComplex (g : R) (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (g • 𝟙 F) (complexQuotientπ (Ideal.span {g}) F) (scalar_comp_quotientπ g F)

lemma scalarQuotientShortExact (g : R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hg : ∀ j,Function.Injective (fun x : F.X j => g • x)) :
    (scalarQuotientShortComplex g F).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro j
  refine {exact := ?_,mono_f := ?_,epi_g := ?_}
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    change (Ideal.span {g} • (⊤ : Submodule R (F.X j))).mkQ x = 0 at hx
    have hm := (Submodule.Quotient.mk_eq_zero _).mp hx
    rw [← scalar_range_eq] at hm
    exact hm
  · exact (ModuleCat.mono_iff_injective _).mpr (hg j)
  · exact (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

lemma scalarHomologyKer (g : R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hg : ∀ j,Function.Injective (fun x : F.X j => g • x)) (i : ℤ) :
    (homologyMap (complexQuotientπ (Ideal.span {g}) F) i).hom.ker =
      (LinearMap.lsmul R (F.homology i) g).range := by
  have he := (scalarQuotientShortExact g F hg).homology_exact₂ i
  have hm := (ShortComplex.moduleCat_exact_iff _).mp he
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := hm x hx
    refine ⟨y,?_⟩
    change homologyMap (g • 𝟙 F) i y = x at hy
    rw [Koszul.homologyMap_smul,homologyMap_id] at hy
    exact hy
  · rintro ⟨y,rfl⟩
    have heq := congrArg (fun f => homologyMap f i) (scalar_comp_quotientπ g F)
    rw [homologyMap_comp,Koszul.homologyMap_smul,homologyMap_id,homologyMap_zero] at heq
    exact congrArg (fun f => f y) heq

def scalarHomologyCokernelEmbedding (g : R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hg : ∀ j,Function.Injective (fun x : F.X j => g • x)) (i : ℤ) :
    (F.homology i) ⧸ (LinearMap.lsmul R (F.homology i) g).range →ₗ[R]
      (((complexQuotient (Ideal.span {g}) (.up ℤ)).obj F).homology i) :=
  let f := (homologyMap (complexQuotientπ (Ideal.span {g}) F) i).hom
  let e := (Submodule.quotEquivOfEq _ _ (scalarHomologyKer g F hg i).symm).trans
    f.quotKerEquivRange
  f.range.subtype.comp e.toLinearMap

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarQuotientTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def scalarQuotientCokernelIso (g : R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hg : ∀ j,Function.Injective (fun x : F.X j => g • x)) :
    ((complexQuotient (Ideal.span {g}) (.up ℤ)).obj F) ≅ cokernel (g • 𝟙 F) :=
  (scalarQuotientShortExact g F hg).gIsCokernel.coconePointUniqueUpToIso
    (colimit.isColimit (parallelPair (g • 𝟙 F) 0))

def scalarQuotientTransport
    (E : CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} S) ℤ)
    [E.PreservesZeroMorphisms] [PreservesFiniteColimits E]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (g : R) (a : S)
    (hmap : E.map (g • 𝟙 F) = a • 𝟙 (E.obj F))
    (hg : ∀ j,Function.Injective (fun x : F.X j => g • x))
    (ha : ∀ j,Function.Injective (fun x : (E.obj F).X j => a • x)) :
    E.obj ((complexQuotient (Ideal.span {g}) (.up ℤ)).obj F) ≅
      ((complexQuotient (Ideal.span {a}) (.up ℤ)).obj (E.obj F)) :=
  E.mapIso (scalarQuotientCokernelIso g F hg) ≪≫
    PreservesCokernel.iso E _ ≪≫ cokernelIsoOfEq hmap ≪≫
    (scalarQuotientCokernelIso a (E.obj F) ha).symm

end Lech

end

end OAI
end


