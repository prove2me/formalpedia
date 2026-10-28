-- Prove2me | Definitions.Def_OAIQ65Sa021
-- name    : OAIQ65Sa021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T04:35:13.311606+00:00
-- url     : https://prove2.me/theorems/80e1f706-132f-45a3-a84d-d8c9ef0ebf94
-- title:
--   Definitions bundle OAIQ65Sa021 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 75 declarations of OpenAI's Lean: 35 definitions, 11 instances and 29 theorems. The definitions and types are `OAI.SimpleAmenable.PolygonObject.LabelledStage.chainCoordinates`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.coefficientDifferential`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.negativeProjection`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.reindexCoefficients`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.rowCoordinateIso`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.signedLabelEquiv`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.stringCoefficientIso`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.trajectoryChainIso`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.trajectoryE2Iso`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.trajectoryRow`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.translateCoefficients`, `OAI.SimpleAmenable.PolygonObject.standardCastIso`, `OAI.SimpleAmenable.PolygonObject.standardSuccessorIso`, `OAI.SimpleAmenable.PolygonObject.standardTensorIso`, `OAI.SimpleAmenable.PolygonTracks.fiberSuccessorIso`, `OAI.SimpleAmenable.PolygonTracks.fiberToStage`, `OAI.SimpleAmenable.PolygonTracks.fiberToStageGlobal`, `OAI.SimpleAmenable.PolygonTracks.fixedToStage`, `OAI.SimpleAmenable.PolygonTracks.fixedToStageGlobal`, `OAI.SimpleAmenable.PolygonTracks.mixedImage`, `OAI.SimpleAmenable.PolygonTracks.representativeGeneratorIso`, `OAI.SimpleAmenable.PolygonTracks.representativeSuccessorIso`, `OAI.SimpleAmenable.PolygonTracks.stageTranslate`, `OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion`, `OAI.SimpleAmenable.PolygonTracks.standardHomologyIso`, `OAI.SimpleAmenable.SymmetricConfiguration.fiberSuccessorIso`, `OAI.SimpleAmenable.SymmetricConfiguration.generator`, `OAI.SimpleAmenable.SymmetricConfiguration.representativeGeneratorIso`, `OAI.SimpleAmenable.SymmetricConfiguration.representativeSuccessorIso`, `OAI.SimpleAmenable.SymmetricConfiguration.standardCastIso`, `OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion`, `OAI.SimpleAmenable.SymmetricConfiguration.standardHomologyIso`, `OAI.SimpleAmenable.SymmetricConfiguration.standardNerveInclusion`, `OAI.SimpleAmenable.SymmetricConfiguration.standardSuccessorIso`, `OAI.SimpleAmenable.SymmetricConfiguration.standardTensorIso`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: [`SimpleAmenable_Configurations_FiberBinary`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/FiberBinary.lean), [`SimpleAmenable_Configurations_PolygonComponentStable`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/PolygonComponentStable.lean), [`SimpleAmenable_Configurations_StageBinary`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/StageBinary.lean), [`SimpleAmenable_Configurations_SymmetricComponents`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/SymmetricComponents.lean), [`SimpleAmenable_Configurations_TrajectoryCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/TrajectoryCoordinates.lean), [`SimpleAmenable_Homology_TrajectoryDifferential`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Homology/TrajectoryDifferential.lean), [`SimpleAmenable_Homology_TrajectoryTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Homology/TrajectoryTensor.lean), [`SimpleAmenable_Homology_TranslationCoefficients`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Homology/TranslationCoefficients.lean), [`SimpleAmenable_Simplicial_ReindexHomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Simplicial/ReindexHomology.lean), [`SimpleAmenable_Simplicial_TrajectoryFinite`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Simplicial/TrajectoryFinite.lean), [`SimpleAmenable_Simplicial_TripleBarMaps`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Simplicial/TripleBarMaps.lean).
--
--   **Imports.** It imports the bundles `OAIQ65Sa019` and `OAIQ65Sa020` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ65Sa025` and `OAIQ65Sa026`; the statement `OAI.SimpleAmenable.PolygonTracks.binaryD_quotient_zero`; the proofs of `OAI.SimpleAmenable.PolygonTracks.binaryD_quotient_zero`, `OAI.SimpleAmenable.PolygonTracks.fullH1_finite_of_bar`, `OAI.SimpleAmenable.PolygonTracks.stableH2_finite_of_bar`, `OAI.SimpleAmenable.SymmetricConfiguration.componentStableH1_finite`, `OAI.SimpleAmenable.SymmetricConfiguration.componentStableH2_finite`, `OAI.SimpleAmenable.SymmetricConfiguration.triple_homology_finite`, `OAI.SimpleAmenable.main` and `OAI.SimpleAmenable.polygon_bar_homology_finite`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ65Sa019
import Definitions.Def_OAIQ65Sa020

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TripleBarMaps
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instBraidedStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.reindexStringMonoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalPropertyInverse _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject

variable {a n : ℕ}
noncomputable instance instMonoidalStringGroupoidStringEval : (stringEval (a:=a) (n:=n)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso _ _ := Iso.refl _
    μIso_hom_natural_left := by intros; simp; rfl
    μIso_hom_natural_right := by intros; simp; rfl
    associativity := by
      intro first second third
      change (𝟙 _ ▷ _ ≫ 𝟙 _ ≫ (α_ _ _ _).hom) =
        ((α_ _ _ _).hom ≫ _ ◁ 𝟙 _ ≫ 𝟙 _)
      simp
    left_unitality := by
      intro object
      change (λ_ _).hom = 𝟙 _ ▷ _ ≫ 𝟙 _ ≫ (λ_ _).hom
      simp
    right_unitality := by
      intro object
      change (ρ_ _).hom = _ ◁ 𝟙 _ ≫ 𝟙 _ ≫ (ρ_ _).hom
      simp }
noncomputable instance instBraidedStringGroupoidStringEval : (stringEval (a:=a) (n:=n)).Braided where
  braided _ _ := by
    change sumSwap _ _ ≫ 𝟙 _ = 𝟙 _ ≫ sumSwap _ _
    simp
end SimpleAmenable.PolygonObject

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonComponentStable
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.translationEvaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instBraidedStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.reindexStringMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.emptyPointIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.pointEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalPropertyInverse _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.StableBarOne.linearπ_epi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation GroupoidComponentHomology

attribute [local instance 1200] Rep.hV2
@[simp] lemma standardNerveInclusion_obj (a n:ℕ) (x:SingleObj (polygonFullGroup a n)) :
    (standardNerveInclusion a n).obj x=PolygonObject.standard a n := rfl
@[simp] lemma standardNerveInclusion_map (a n:ℕ) {x y:SingleObj (polygonFullGroup a n)} (f:x⟶y) :
    (standardNerveInclusion a n).map f=PolygonObject.fullGroupArrow f := rfl
noncomputable def standardFiberInclusion (a n:ℕ) :
    SingleObj (polygonFullGroup a n) ⥤ Fiber (componentGenerator a^n) :=
  (property (componentGenerator a^n)).lift (standardNerveInclusion a n)
    (fun _=>PolygonObject.component_standard_pow n)
noncomputable def standardHomologyIso (a n q:ℕ) :
    groupHomology (Rep.trivial ℤ (polygonFullGroup a n) ℤ) q ≅
      (nerve (Fiber (componentGenerator a^n))).homology Z q := by
  haveI:=TrivialHomology.isIso_equiv (PolygonObject.standardAutEquiv a n).symm q
  exact asIso (TrivialHomology.map (PolygonObject.standardAutEquiv a n).symm.toMonoidHom q) ≪≫
    fiberIsoHomology (standardFiber a n) q
end SimpleAmenable.PolygonTracks
namespace SimpleAmenable.PolygonObject
open SimpleAmenable SimpleAmenable.PolygonTracks

variable {a:ℕ}
lemma eqToHom_coord {U V:PolygonObject a} (h:U=V) (x:U.Point) :
    (((eqToHom h:U⟶V).toEquiv x).val.1.val,((eqToHom h:U⟶V).toEquiv x).val.2)=
      (x.val.1.val,x.val.2) := by subst V; rfl
lemma standardTensor_map (k n:ℕ) (f:polygonFullGroup a n) :
    (tensorLeft (standard a k)).map (fullGroupArrow f) ≫ eqToHom (sum_standard k n) =
      eqToHom (sum_standard k n) ≫ fullGroupArrow (stabilize a k n f) := by
  apply Arrow.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    obtain ⟨y,rfl⟩ := (sumPointEquiv (standard a k) (standard a n)).surjective x
    cases y with
    | inl y =>
      have hx:=congrArg (fun z : ℕ × GenericSquare a => z.1) (eqToHom_coord (sum_standard k n) (sumPointEquiv (standard a k) (standard a n) (.inl y)))
      simp only [arrow_comp_apply]
      change ((eqToHom (sum_standard k n)).toEquiv
        ((sumArrow (𝟙 _) (fullGroupArrow f)).toEquiv _)).val.1.val = _
      rw [sumArrow_inl,arrow_id_apply]
      rw [show ((eqToHom (sum_standard k n)).toEquiv _).val.1.val = y.val.1.val from hx]
      change _=((stabilize a k n f).val ((eqToHom (sum_standard k n)).toEquiv _).val).1.val
      have hp : ((eqToHom (sum_standard k n)).toEquiv
          (sumPointEquiv (standard a k) (standard a n) (.inl y))).val=(y.val.1.castAdd n,y.val.2) := by
        apply Prod.ext
        · apply Fin.ext; exact hx
        · exact congrArg (fun z : ℕ × GenericSquare a => z.2) (eqToHom_coord (sum_standard k n) _)
      erw [hp,stabilize_left]
      rfl
    | inr y =>
      have hp (z:(standard a n).Point) : ((eqToHom (sum_standard k n)).toEquiv
          (sumPointEquiv (standard a k) (standard a n) (.inr z))).val=(z.val.1.natAdd k,z.val.2) := by
        apply Prod.ext
        · apply Fin.ext; exact congrArg (fun z : ℕ × GenericSquare a => z.1) (eqToHom_coord (sum_standard k n) _)
        · exact congrArg (fun z : ℕ × GenericSquare a => z.2) (eqToHom_coord (sum_standard k n) _)
      simp only [arrow_comp_apply]
      change ((eqToHom (sum_standard k n)).toEquiv
        ((sumArrow (𝟙 _) (fullGroupArrow f)).toEquiv _)).val.1.val =
          ((stabilize a k n f).val ((eqToHom (sum_standard k n)).toEquiv _).val).1.val
      erw [sumArrow_inr,hp,hp,stabilize_right]
      rfl
  · obtain ⟨y,rfl⟩ := (sumPointEquiv (standard a k) (standard a n)).surjective x
    cases y with
    | inl y =>
      have hp : ((eqToHom (sum_standard k n)).toEquiv
          (sumPointEquiv (standard a k) (standard a n) (.inl y))).val=(y.val.1.castAdd n,y.val.2) := by
        apply Prod.ext
        · apply Fin.ext; exact congrArg (fun z : ℕ × GenericSquare a => z.1) (eqToHom_coord (sum_standard k n) _)
        · exact congrArg (fun z : ℕ × GenericSquare a => z.2) (eqToHom_coord (sum_standard k n) _)
      simp only [arrow_comp_apply]
      change ((eqToHom (sum_standard k n)).toEquiv
        ((sumArrow (𝟙 _) (fullGroupArrow f)).toEquiv _)).val.2 =
          ((stabilize a k n f).val ((eqToHom (sum_standard k n)).toEquiv _).val).2
      erw [sumArrow_inl,arrow_id_apply,hp,stabilize_left]
    | inr y =>
      have hp (z:(standard a n).Point) : ((eqToHom (sum_standard k n)).toEquiv
          (sumPointEquiv (standard a k) (standard a n) (.inr z))).val=(z.val.1.natAdd k,z.val.2) := by
        apply Prod.ext
        · apply Fin.ext; exact congrArg (fun z : ℕ × GenericSquare a => z.1) (eqToHom_coord (sum_standard k n) _)
        · exact congrArg (fun z : ℕ × GenericSquare a => z.2) (eqToHom_coord (sum_standard k n) _)
      simp only [arrow_comp_apply]
      change ((eqToHom (sum_standard k n)).toEquiv
        ((sumArrow (𝟙 _) (fullGroupArrow f)).toEquiv _)).val.2 =
          ((stabilize a k n f).val ((eqToHom (sum_standard k n)).toEquiv _).val).2
      erw [sumArrow_inr,hp,hp,stabilize_right]
      rfl
noncomputable def standardTensorIso (k n:ℕ) :
    standardNerveInclusion a n ⋙ tensorLeft (standard a k) ≅
      (stabilize a k n).toFunctor ⋙ standardNerveInclusion a (k+n) :=
  NatIso.ofComponents (fun _=>eqToIso (sum_standard k n)) (by
    intro x y f
    exact standardTensor_map k n f)
noncomputable def standardCastIso {m n:ℕ} (h:m=n) : standardNerveInclusion a m ≅
    (castFull a h).toMonoidHom.toFunctor ⋙ standardNerveInclusion a n := by
  subst n
  exact NatIso.ofComponents (fun _=>Iso.refl _) (by intro x y f; simp; rfl)
noncomputable def standardSuccessorIso (n:ℕ) :
    standardNerveInclusion a n ⋙ tensorLeft (standard a 1) ≅
      (successorStabilize a n).toFunctor ⋙ standardNerveInclusion a (n+1) :=
  standardTensorIso 1 n ≪≫
    Functor.isoWhiskerLeft (stabilize a 1 n).toFunctor (standardCastIso (Nat.add_comm 1 n)) ≪≫
      (Functor.associator _ _ _).symm
end SimpleAmenable.PolygonObject
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation GroupoidComponentHomology

instance standardFiberInclusion_faithful (a n:ℕ) : (standardFiberInclusion a n).Faithful where
  map_injective h := PolygonObject.fullGroupArrow_injective
    (congrArg (fun f : (standardFiberInclusion a n).obj _ ⟶ (standardFiberInclusion a n).obj _ => f.hom) h)
noncomputable instance standardFiberInclusion_full (a n:ℕ) : (standardFiberInclusion a n).Full where
  map_surjective f := ⟨PolygonObject.fullGroupOfArrow f.hom,by
    apply ObjectProperty.hom_ext
    exact PolygonObject.arrow_fullGroup f.hom⟩
instance standardFiberInclusion_essSurj (a n:ℕ) : (standardFiberInclusion a n).EssSurj where
  mem_essImage V := ⟨SingleObj.star _,⟨fiberIso _ (standardFiber a n) V⟩⟩
noncomputable instance standardFiberInclusion_isEquivalence (a n:ℕ) :
    (standardFiberInclusion a n).IsEquivalence := ⟨inferInstance,inferInstance,inferInstance⟩
noncomputable def representativeGeneratorIso (a:ℕ) :
    repr (componentGenerator a) ≅ PolygonObject.standard a 1 := Skeleton.isoOfEq (repr_component _)
noncomputable def representativeSuccessorIso (a n:ℕ) :
    standardNerveInclusion a n ⋙ tensorLeft (repr (componentGenerator a)) ≅
      (successorStabilize a n).toFunctor ⋙ standardNerveInclusion a (n+1) :=
  Functor.isoWhiskerLeft (standardNerveInclusion a n)
    ((tensoringLeft (PolygonObject a)).mapIso (representativeGeneratorIso a)) ≪≫
      PolygonObject.standardSuccessorIso n
noncomputable def fiberSuccessorIso (a n:ℕ) :
    standardFiberInclusion a n ⋙
      ComponentTranslation.translate (componentGenerator a) (componentGenerator a^n) (componentGenerator a^(n+1)) (pow_succ' _ _).symm ≅
        (successorStabilize a n).toFunctor ⋙ standardFiberInclusion a (n+1) :=
  NatIso.ofComponents (fun x=>ObjectProperty.isoMk _ ((representativeSuccessorIso a n).app x)) (by
    intro x y f
    apply ObjectProperty.hom_ext
    exact (representativeSuccessorIso a n).hom.naturality f)
end SimpleAmenable.PolygonTracks

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TranslationCoefficients
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.reindexBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.reindexMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.reindexStringMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Classical
namespace SimpleAmenable.PolygonObject.LabelledStage

variable {a n : ℕ} {K : Type} [AddCommGroup K]
@[simp] lemma stepTranslate_apply (u : CutRing × CutRing) (f : BooleanStep a K) (p : GenericSquare a) :
    (stepTranslate (K:=K) u f).val p = f.val (SimpleAmenable.translate a (-u) p) := rfl
variable (d : (Fin n → CutRing × CutRing) → CutRing × CutRing)
noncomputable def translateCoefficients : Coefficients a n K →ₗ[ℤ] Coefficients a n K :=
  Finsupp.lsum ℤ (fun l : ReducedLabel n => (Finsupp.lsingle l).comp (stepTranslate (d l.val)))
@[simp] lemma translateCoefficients_single (l : ReducedLabel n) (s : BooleanStep a K) :
    translateCoefficients (K:=K) d (Finsupp.single l s)=
      Finsupp.single l (stepTranslate (K:=K) (d l.val) s) := Finsupp.lsum_single _ _ _ _
lemma translateCoefficients_at (f : Coefficients a n K) (l : ReducedLabel n) :
    translateCoefficients (K:=K) d f l=stepTranslate (K:=K) (d l.val) (f l) := by
  induction f using Finsupp.induction with
  | zero => simp
  | single_add k s f hk hs ih =>
    simp only [map_add,Finsupp.add_apply,ih]
    congr 1
    rw [translateCoefficients_single]
    by_cases h:k=l
    · subst l; simp only [Finsupp.single_eq_same]
    · simp only [Finsupp.single_eq_of_ne (Ne.symm h),map_zero]
end SimpleAmenable.PolygonObject.LabelledStage

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Classical
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar.Diagram BarFinitePower FreeChains Labelled

variable {a n : ℕ}
variable (d : (Fin n → CutRing × CutRing) → CutRing × CutRing)
lemma translation_evaluation_homology (j : ℕ)
    (c : GenericSquare a × (Fin n → CutRing × CutRing)) :
    SSet.homologyMap (bar₃Map (translateFunctor d ⋙ PointFiber.evaluation ⋙ project _ c)) Z j =
    SSet.homologyMap (bar₃Map (PointFiber.evaluation ⋙ project _ (SimpleAmenable.translate a (-d c.2) c.1,c.2))) Z j :=
  (bar₃Map_eq_of_monoidalNatTrans (PointFiber.translationEvaluationIso d c).hom j).symm
lemma homologyCoefficientIso_translate_point (j : ℕ) (hj : 0<j) (hj5 : j≤5)
    (c : GenericSquare a × ReducedLabel n) :
    SSet.homologyMap (bar₃Map (translateFunctor d)) Z j ≫
      (homologyCoefficientIso (a:=a) (n:=n) j hj hj5).hom ≫ ModuleCat.ofHom (pointValue c) =
    (homologyCoefficientIso (a:=a) (n:=n) j hj hj5).hom ≫
      ModuleCat.ofHom (pointValue (SimpleAmenable.translate a (-d c.2.val) c.1,c.2)) := by
  rw [homologyCoefficientIso_point,homologyCoefficientIso_point,
    ←SSet.homologyMap_comp,←bar₃Map_comp]
  exact translation_evaluation_homology d j (c.1,c.2.val)
lemma homologyCoefficientIso_translate (j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    SSet.homologyMap (bar₃Map (translateFunctor d)) Z j ≫
      (homologyCoefficientIso (a:=a) (n:=n) j hj hj5).hom =
    (homologyCoefficientIso (a:=a) (n:=n) j hj hj5).hom ≫
      ModuleCat.ofHom (translateCoefficients (a:=a) (K:=K j) d) := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
  apply Finsupp.ext; intro l
  apply Subtype.ext; funext p
  have h := congrArg (fun k : (bar₃ (C:=Labelled a n)).homology Z j ⟶ K j => k x)
    (homologyCoefficientIso_translate_point d j hj hj5 (p,l))
  change _ = (translateCoefficients (a:=a) (K:=K j) d ((homologyCoefficientIso j hj hj5).hom x) l).val p
  rw [translateCoefficients_at,stepTranslate_apply]
  exact h
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TrajectoryTensor
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory
open scoped TensorProduct
namespace SimpleAmenable.PolygonObject.LabelledStage

variable {a : ℕ} {K : Type} [AddCommGroup K]
lemma tensorEquiv_translation (u : CutRing × CutRing) (v : SquareStep a ⊗[ℤ] K) :
    (BooleanStep.tensorEquiv (a:=a) (K:=K))
      ((SquareStep.coefficientRep a K).ρ (SquareStep.orbitProjection (Multiplicative.ofAdd u)) v) =
      stepTranslate (K:=K) u ((BooleanStep.tensorEquiv (a:=a) (K:=K)) v) := by
  induction v using OAI.tensorInductionOn with
  | add left right left_eq right_eq =>
    let action : (SquareStep a ⊗[ℤ] K) →ₗ[ℤ] (SquareStep a ⊗[ℤ] K) :=
      (SquareStep.coefficientRep a K).ρ (SquareStep.orbitProjection (Multiplicative.ofAdd u))
    change BooleanStep.tensorEquiv (a:=a) (K:=K) (action (left + right)) = _
    change BooleanStep.tensorEquiv (a:=a) (K:=K) (action left) = _ at left_eq
    change BooleanStep.tensorEquiv (a:=a) (K:=K) (action right) = _ at right_eq
    simp only [map_add,left_eq,right_eq]
  | tmul f k =>
    change (BooleanStep.tensorMap (a:=a) (K:=K))
      (SquareStep.orbitRepresentation a (SquareStep.orbitProjection (Multiplicative.ofAdd u)) f ⊗ₜ[ℤ] k) = _
    rw [←SquareStep.representation_reduce]
    apply Subtype.ext
    funext p
    rfl
lemma tensorEquiv_symm_translation (u : CutRing × CutRing) (v : BooleanStep a K) :
    (BooleanStep.tensorEquiv (a:=a) (K:=K)).symm (stepTranslate (K:=K) u v) =
    (SquareStep.coefficientRep a K).ρ (SquareStep.orbitProjection (Multiplicative.ofAdd u))
      ((BooleanStep.tensorEquiv (a:=a) (K:=K)).symm v) := by
  apply (BooleanStep.tensorEquiv (a:=a) (K:=K)).injective
  rw [LinearEquiv.apply_symm_apply,tensorEquiv_translation,LinearEquiv.apply_symm_apply]
@[simp] lemma stepTranslate_zero (v : BooleanStep a K) : stepTranslate (K:=K) 0 v=v := by
  apply Subtype.ext
  funext p
  change v.val (SimpleAmenable.translate a (-0) p)=v.val p
  simp
end SimpleAmenable.PolygonObject.LabelledStage

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_ReindexHomology
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalPropertyInverse _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_full _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_isEquivalence _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory
namespace SimpleAmenable.PolygonObject
noncomputable instance stringReindex_braided {a n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) :
    (stringReindex (a:=a) u).Braided where
  braided _ _ := by
    apply WideSubcategory.hom_ext
    ext i
    change 𝟙 _ ≫ (β_ _ _).hom = (β_ _ _).hom ≫ 𝟙 _
    simp
end SimpleAmenable.PolygonObject
namespace SimpleAmenable.PolygonObject.LabelledStage
open IntervalBar.Diagram BarFinitePower FreeChains Labelled

variable {a n m : ℕ} {K : Type} [AddCommGroup K]
noncomputable def reindexCoefficients (u : Fin (m+1) ⥤ Fin (n+1)) :
    Coefficients a n K →ₗ[ℤ] Coefficients a m K :=
  (relabelCoefficients (reindexLabel u) (reindexLabel_reduced u)).comp
    (translateCoefficients (initialDisplacement u))
lemma reindexCoefficients_single (u : Fin (m+1) ⥤ Fin (n+1))
    (l : ReducedLabel n) (s : BooleanStep a K) :
    reindexCoefficients (K:=K) u (Finsupp.single l s) =
      Finsupp.single (labelMap (reindexLabel u) (reindexLabel_reduced u) l)
        (stepTranslate (K:=K) (initialDisplacement u l.val) s) := by
  simp only [reindexCoefficients,LinearMap.comp_apply,translateCoefficients_single,
    relabelCoefficients_single]
namespace Stage
lemma homologyCoefficientIso_reindex (u : Fin (m+1) ⥤ Fin (n+1))
    (j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    SSet.homologyMap (bar₃Map (reindexFunctor (a:=a) u)) Z j ≫
      (homologyCoefficientIso (a:=a) (n:=m) j hj hj5).hom =
    (homologyCoefficientIso (a:=a) (n:=n) j hj hj5).hom ≫
      ModuleCat.ofHom (reindexCoefficients (a:=a) (K:=Stage.K j) u) := by
  change SSet.homologyMap (bar₃Map (translateFunctor (initialDisplacement u) ⋙
      relabel (reindexLabel u) (reindexLabel_reduced u))) Z j ≫ _ = _
  rw [bar₃Map_comp,SSet.homologyMap_comp,Category.assoc,homologyCoefficientIso_relabel,
    ←Category.assoc,homologyCoefficientIso_translate,Category.assoc]
  rfl
end Stage
noncomputable def stringCoefficientIso (a n j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    (bar₃ (C:=StringGroupoid a n)).homology Z j ≅
      ModuleCat.of ℤ (Coefficients a n (Stage.K j)) := by
  haveI := Labelled.tripleBar_homology_isIso (a:=a) (n:=n) j
  exact (asIso (SSet.homologyMap (bar₃Map (toStrings (a:=a) (n:=n))) Z j)).symm ≪≫
    Stage.homologyCoefficientIso j hj hj5
lemma toStrings_stringCoefficientIso (j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    SSet.homologyMap (bar₃Map (toStrings (a:=a) (n:=n))) Z j ≫
      (stringCoefficientIso a n j hj hj5).hom =
    (Stage.homologyCoefficientIso j hj hj5).hom := by
  have tripleBarIso := Labelled.tripleBar_homology_isIso (a:=a) (n:=n) j
  change _ ≫ inv _ ≫ _ = _
  rw [IsIso.hom_inv_id_assoc]
lemma toStrings_reindex_homology (u : Fin (m+1) ⥤ Fin (n+1)) (j : ℕ) :
    SSet.homologyMap (bar₃Map (reindexFunctor (a:=a) u)) Z j ≫
      SSet.homologyMap (bar₃Map toStrings) Z j =
    SSet.homologyMap (bar₃Map toStrings) Z j ≫
      SSet.homologyMap (bar₃Map (stringReindex u)) Z j := by
  rw [←SSet.homologyMap_comp,←bar₃Map_comp,←SSet.homologyMap_comp,←bar₃Map_comp]
  exact bar₃Map_eq_of_monoidalNatTrans (reindexStringIso u).hom j
lemma stringCoefficientIso_reindex (u : Fin (m+1) ⥤ Fin (n+1))
    (j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    SSet.homologyMap (bar₃Map (stringReindex (a:=a) u)) Z j ≫
      (stringCoefficientIso a m j hj hj5).hom =
    (stringCoefficientIso a n j hj hj5).hom ≫
      ModuleCat.ofHom (reindexCoefficients (a:=a) (K:=Stage.K j) u) := by
  have tripleBarIso := Labelled.tripleBar_homology_isIso (a:=a) (n:=n) j
  apply (cancel_epi (SSet.homologyMap (bar₃Map (toStrings (a:=a) (n:=n))) Z j)).mp
  rw [←Category.assoc,toStrings_reindex_homology u j |>.symm,Category.assoc,
    toStrings_stringCoefficientIso,←Category.assoc,toStrings_stringCoefficientIso]
  exact Stage.homologyCoefficientIso_reindex u j hj hj5
end SimpleAmenable.PolygonObject.LabelledStage

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_TrajectoryCoordinates
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory
open scoped TensorProduct
namespace SimpleAmenable.PolygonObject.LabelledStage
open Labelled

variable {a n : ℕ} {K : Type} [AddCommGroup K]
noncomputable def negativeProjection (u : CutRing × CutRing) : RankTwo :=
  (SquareStep.orbitProjection (Multiplicative.ofAdd u))⁻¹
lemma negativeProjection_add (u v : CutRing × CutRing) :
    negativeProjection (u+v)=negativeProjection u*negativeProjection v := by
  change (SquareStep.orbitProjection (Multiplicative.ofAdd u*Multiplicative.ofAdd v))⁻¹ = _
  rw [map_mul,mul_inv_rev,mul_comm]
  rfl

noncomputable def signedLabelEquiv (n : ℕ) : ReducedLabel n ≃ (Fin n → RankTwo) :=
  (reducedLabelEquiv n).trans (Equiv.piCongrRight (fun _ => Equiv.inv RankTwo))
lemma signedLabelEquiv_apply (l : ReducedLabel n) (i : Fin n) :
    signedLabelEquiv n l i=negativeProjection (l.val i) := rfl
lemma signedLabel_zero_face (l : ReducedLabel (n+1)) :
    signedLabelEquiv n (labelMap (reindexLabel (faceFunctor 0))
      (reindexLabel_reduced (faceFunctor 0)) l)=Fin.tail (signedLabelEquiv (n+1) l) := by
  change (fun i => negativeProjection (reindexLabel (faceFunctor 0) l.val i)) = _
  rw [reindexLabel_zero_face]
  rfl
lemma signedLabel_succ_face (l : ReducedLabel (n+1)) (i : Fin (n+1)) :
    signedLabelEquiv n (labelMap (reindexLabel (faceFunctor i.succ))
      (reindexLabel_reduced (faceFunctor i.succ)) l)=i.contractNth (·*·) (signedLabelEquiv (n+1) l) := by
  change (fun k => negativeProjection (reindexLabel (faceFunctor i.succ) l.val k)) = _
  rw [reindexLabel_succ_face]
  exact Fin.comp_contractNth (·+·) (·*·) negativeProjection_add i l.val
noncomputable def chainCoordinates (a n : ℕ) (K : Type) [AddCommGroup K] :
    Coefficients a n K ≃ₗ[ℤ] ((Fin n → RankTwo) →₀ (SquareStep a ⊗[ℤ] K)) :=
  (Finsupp.mapRange.linearEquiv (BooleanStep.tensorEquiv (a:=a) (K:=K)).symm).trans
    (Finsupp.domLCongr (signedLabelEquiv n))
lemma chainCoordinates_single (l : ReducedLabel n) (v : BooleanStep a K) :
    chainCoordinates a n K (Finsupp.single l v)=
      Finsupp.single (signedLabelEquiv n l) ((BooleanStep.tensorEquiv (a:=a) (K:=K)).symm v) := by
  simp [chainCoordinates]
lemma chainCoordinates_zero_face (l : ReducedLabel (n+1)) (v : BooleanStep a K) :
    chainCoordinates a n K (reindexCoefficients (K:=K) (faceFunctor 0) (Finsupp.single l v)) =
      Finsupp.single (Fin.tail (signedLabelEquiv (n+1) l))
        ((SquareStep.coefficientRep a K).ρ ((signedLabelEquiv (n+1) l 0)⁻¹)
          ((BooleanStep.tensorEquiv (a:=a) (K:=K)).symm v)) := by
  rw [reindexCoefficients_single,chainCoordinates_single,signedLabel_zero_face,
    initialDisplacement_zero_face,tensorEquiv_symm_translation]
  simp only [signedLabelEquiv_apply,negativeProjection,inv_inv]
  rfl
lemma chainCoordinates_succ_face (l : ReducedLabel (n+1)) (v : BooleanStep a K) (i : Fin (n+1)) :
    chainCoordinates a n K (reindexCoefficients (K:=K) (faceFunctor i.succ) (Finsupp.single l v)) =
      Finsupp.single (i.contractNth (·*·) (signedLabelEquiv (n+1) l))
        ((BooleanStep.tensorEquiv (a:=a) (K:=K)).symm v) := by
  rw [reindexCoefficients_single,chainCoordinates_single,signedLabel_succ_face,
    initialDisplacement_succ_face,stepTranslate_zero]
end SimpleAmenable.PolygonObject.LabelledStage

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TrajectoryDifferential
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_full _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_isEquivalence _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory AlgebraicTopology
open scoped BigOperators TensorProduct
namespace SimpleAmenable.PolygonObject.LabelledStage
open Labelled IntervalBar.Diagram FreeChains

attribute [local instance 1200] Rep.hV2 Representation.instModuleAsModule TensorProduct.instModule
variable {a n : ℕ} {K : Type} [AddCommGroup K]
noncomputable def coefficientDifferential (a n : ℕ) (K : Type) [AddCommGroup K] :
    Coefficients a (n+1) K →ₗ[ℤ] Coefficients a n K :=
  ∑ i : Fin (n+2), (-1:ℤ)^(i:ℕ) • reindexCoefficients (a:=a) (K:=K) (faceFunctor i)
lemma chainCoordinates_d :
    (chainCoordinates a n K).toLinearMap.comp (coefficientDifferential a n K) =
      (groupHomology.inhomogeneousChains.d (SquareStep.coefficientRep a K) n).hom.comp
        (chainCoordinates a (n+1) K).toLinearMap := by
  classical
  apply Finsupp.lhom_ext'
  intro l
  apply LinearMap.ext
  intro v
  change chainCoordinates a n K (coefficientDifferential a n K (Finsupp.single l v)) =
    groupHomology.inhomogeneousChains.d (SquareStep.coefficientRep a K) n
      (chainCoordinates a (n+1) K (Finsupp.single l v))
  simp only [coefficientDifferential,LinearMap.sum_apply,LinearMap.smul_apply,
    map_sum,map_smul,chainCoordinates_single]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,chainCoordinates_zero_face,Fin.val_succ,
    chainCoordinates_succ_face]
  erw [one_smul]
  exact (groupHomology.inhomogeneousChains.d_single (A:=SquareStep.coefficientRep a K)
    n (signedLabelEquiv (n+1) l) ((BooleanStep.tensorEquiv (a:=a) (K:=K)).symm v)).symm
noncomputable def trajectoryRow (a j : ℕ) : SimplicialObject (ModuleCat ℤ) :=
  RestrictedNerve.stringBarRows (positionalProperty a) ⋙ SSet.homologyFunctor Z j
noncomputable def rowCoordinateIso (a n j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    (trajectoryRow a j).obj (Opposite.op (SimplexCategory.mk n)) ≅
      (groupHomology.inhomogeneousChains (trajectoryRep a j)).X n := by
  refine stringCoefficientIso a n j hj hj5 ≪≫ ?_
  exact (chainCoordinates a n (Stage.K j)).toModuleIso
lemma trajectoryRow_d (a n j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    (AlternatingFaceMapComplex.obj (trajectoryRow a j)).d (n+1) n ≫
      (stringCoefficientIso a n j hj hj5).hom =
    (stringCoefficientIso a (n+1) j hj hj5).hom ≫
      ModuleCat.ofHom (coefficientDifferential a n (Stage.K j)) := by
  rw [AlternatingFaceMapComplex.obj_d_eq]
  change (∑ index : Fin (n+2), (-1:ℤ)^(index:ℕ) •
      SSet.homologyMap (bar₃Map (stringReindex (a:=a) (faceFunctor index))) Z j) ≫
      (stringCoefficientIso a n j hj hj5).hom =
    (stringCoefficientIso a (n+1) j hj hj5).hom ≫
      ModuleCat.ofHom (coefficientDifferential a n (Stage.K j))
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,
    stringCoefficientIso_reindex]
  apply ModuleCat.hom_ext
  ext x
  simp only [coefficientDifferential,ModuleCat.hom_sum,ModuleCat.hom_zsmul,
    ModuleCat.hom_comp,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,ModuleCat.hom_ofHom]
noncomputable def trajectoryChainIso (a j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    AlternatingFaceMapComplex.obj (trajectoryRow a j) ≅
      groupHomology.inhomogeneousChains (trajectoryRep a j) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n => rowCoordinateIso a n j hj hj5) ?_
  rintro n m rfl
  symm
  change _ ≫ (stringCoefficientIso a m j hj hj5).hom ≫
      ModuleCat.ofHom (chainCoordinates a m (Stage.K j)).toLinearMap =
    ((stringCoefficientIso a (m+1) j hj hj5).hom ≫
      ModuleCat.ofHom (chainCoordinates a (m+1) (Stage.K j)).toLinearMap) ≫ _
  erw [←Category.assoc,trajectoryRow_d,Category.assoc,groupHomology.inhomogeneousChains.d_def]
  apply ModuleCat.hom_ext
  exact congrArg
    (fun linear => LinearMap.comp linear (stringCoefficientIso a (m+1) j hj hj5).hom.hom)
    (chainCoordinates_d (a:=a) (n:=m) (K:=Stage.K j))
end SimpleAmenable.PolygonObject.LabelledStage

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TrajectoryFinite
attribute [-instance] _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_full _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_isEquivalence _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Opposite AlgebraicTopology HomologicalComplex
namespace SimpleAmenable.PolygonObject.LabelledStage
open Labelled IntervalBar.Diagram FreeChains

attribute [local instance 1200] Rep.hV2 Representation.instModuleAsModule TensorProduct.instModule
noncomputable def trajectoryE2Iso (a p q : ℕ) (hq : 0<q) (hq5 : q≤5) :
    (TotalFiniteness.row (EilenbergZilber.twoComplex
      (SimplicialDiagonal.uncurry (RestrictedNerve.stringBarRows (positionalProperty a)))) q).homology p ≅
      groupHomology (trajectoryRep a q) p :=
by
  refine SimplicialDiagonal.homologyRowHomologyIso
    (RestrictedNerve.stringBarRows (positionalProperty a)) p q ≪≫ ?_
  exact (homologyFunctor A c p).mapIso (trajectoryChainIso a q hq hq5)
end SimpleAmenable.PolygonObject.LabelledStage

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_StageBinary
attribute [-instance] _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation ComponentStable

attribute [local instance 1200] Rep.hV2 Submodule.module
noncomputable def stageTranslate (a m:ℕ) (hm:32 ≤ m) :
    Fiber (componentGenerator a^32) ⥤ Fiber (componentGenerator a^m) :=
  ComponentTranslation.translate (componentGenerator a^(m-32)) _ _
    (by rw [←pow_add,Nat.sub_add_cancel hm])
noncomputable def fixedToStage (a m:ℕ) (hm:32 ≤ m) :
    SingleObj (polygonFullGroup a 32) ⥤ SingleObj (polygonFullGroup a m) :=
  standardFiberInclusion a 32 ⋙ stageTranslate a m hm ⋙ (standardFiberInclusion a m).asEquivalence.inverse
noncomputable def fixedToStageGlobal (a m:ℕ) (hm:32 ≤ m) :
    fixedToStage a m hm ⋙ standardNerveInclusion a m ≅
      standardNerveInclusion a 32 ⋙ tensorLeft (repr (componentGenerator a^(m-32))) := by
  let e := (standardFiberInclusion a m).asEquivalence
  let α := Functor.isoWhiskerLeft (standardFiberInclusion a 32 ⋙ stageTranslate a m hm) e.counitIso
  exact Functor.isoWhiskerRight α (property (componentGenerator a^m)).ι
noncomputable def mixedImage (a:ℕ) : Submodule ℤ (object (C:=PolygonObject a) 2) :=
  LinearMap.range ((pullD (nerveMap (standardNerveInclusion a 32))
    (nerveMap (standardNerveInclusion a 32)) 2).hom.comp
      (LinearMap.ker (ConnectedProduct.projection (nerve (SingleObj (polygonFullGroup a 32)))
        (nerve (SingleObj (polygonFullGroup a 32))) 2).hom).subtype)
end SimpleAmenable.PolygonTracks

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_FiberBinary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation ComponentStable

attribute [local instance 1200] Rep.hV2 Submodule.module Submodule.Quotient.module
noncomputable def fiberToStage (a:ℕ) (p:Skeleton (PolygonObject a)) (n:ℕ)
    (r:Skeleton (PolygonObject a)) (h:r*p=componentGenerator a^n) :
    Fiber p ⥤ SingleObj (polygonFullGroup a n) :=
  ComponentTranslation.translate r p (componentGenerator a^n) h ⋙
    (standardFiberInclusion a n).asEquivalence.inverse
noncomputable def fiberToStageGlobal (a:ℕ) (p:Skeleton (PolygonObject a)) (n:ℕ)
    (r:Skeleton (PolygonObject a)) (h:r*p=componentGenerator a^n) :
    fiberToStage a p n r h ⋙ standardNerveInclusion a n ≅
      (property p).ι ⋙ tensorLeft (repr r) := by
  exact Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (ComponentTranslation.translate r p _ h)
      (standardFiberInclusion a n).asEquivalence.counitIso) (property (componentGenerator a^n)).ι
end SimpleAmenable.PolygonTracks

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SymmetricComponents
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.SymmetricConfiguration
open FreeChains ComponentTranslation GroupoidComponentHomology PolygonObject

attribute [local instance 1200] Rep.hV2
noncomputable abbrev generator : Skeleton FiniteSetGroupoid := toSkeleton ⟨1⟩
lemma component_pow (n:ℕ) : toSkeleton (⟨n⟩:FiniteSetGroupoid)=generator^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ,←ih]
    exact Skeleton.toSkeleton_tensorObj (⟨n⟩:FiniteSetGroupoid) ⟨1⟩
noncomputable def standardNerveInclusion (n:ℕ) : SingleObj (G n) ⥤ FiniteSetGroupoid where
  obj _ := ⟨n⟩
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl
noncomputable def standardFiberInclusion (n:ℕ) : SingleObj (G n) ⥤ Fiber (generator^n) :=
  (property (generator^n)).lift (standardNerveInclusion n) (fun _=>component_pow n)
instance standardFiberInclusion_faithful (n:ℕ) : (standardFiberInclusion n).Faithful where
  map_injective h := congrArg (fun f : (standardFiberInclusion n).obj _ ⟶ (standardFiberInclusion n).obj _=>f.hom) h
noncomputable instance standardFiberInclusion_full (n:ℕ) : (standardFiberInclusion n).Full where
  map_surjective f := ⟨f.hom,rfl⟩
instance standardFiberInclusion_essSurj (n:ℕ) : (standardFiberInclusion n).EssSurj where
  mem_essImage V := ⟨SingleObj.star _,⟨fiberIso _ ((standardFiberInclusion n).obj (SingleObj.star _)) V⟩⟩
noncomputable instance standardFiberInclusion_isEquivalence (n:ℕ) : (standardFiberInclusion n).IsEquivalence :=
  ⟨inferInstance,inferInstance,inferInstance⟩
noncomputable def standardHomologyIso (n q:ℕ) :
    groupHomology (Rep.trivial ℤ (G n) ℤ) q ≅ (nerve (Fiber (generator^n))).homology Z q := by
  haveI:=NerveHomotopy.homologyMap_isIso (standardFiberInclusion n) Z q
  exact (GroupNerveCoordinates.homologyIso (G n) q).symm ≪≫
    asIso (SSet.homologyMap (nerveMap (standardFiberInclusion n)) Z q)
lemma tensor_stabilize (k n:ℕ) (f:G n) :
    (tensorLeft (⟨k⟩:FiniteSetGroupoid)).map (show (⟨n⟩:FiniteSetGroupoid) ⟶ ⟨n⟩ from f)=
      (show (⟨k+n⟩:FiniteSetGroupoid) ⟶ ⟨k+n⟩ from stabilize k n f) := by
  apply Equiv.ext
  intro x
  obtain ⟨y,rfl⟩:=finSumFinEquiv.surjective x
  cases y with
  | inl i =>
    change FiniteSetGroupoid.sumHom (Equiv.refl (Fin k)) f (FiniteSetGroupoid.sumEquiv ⟨k⟩ ⟨n⟩ (.inl i))=stabilize k n f (Fin.castAdd n i)
    rw [FiniteSetGroupoid.sumHom_inl,stabilize_apply_head]
    rfl
  | inr i =>
    change FiniteSetGroupoid.sumHom (Equiv.refl (Fin k)) f (FiniteSetGroupoid.sumEquiv ⟨k⟩ ⟨n⟩ (.inr i))=stabilize k n f (Fin.natAdd k i)
    rw [FiniteSetGroupoid.sumHom_inr,stabilize_apply_tail]
    rfl
noncomputable def standardTensorIso (k n:ℕ) :
    standardNerveInclusion n ⋙ tensorLeft (⟨k⟩:FiniteSetGroupoid) ≅
      (stabilize k n).toFunctor ⋙ standardNerveInclusion (k+n) :=
  NatIso.ofComponents (fun _=>Iso.refl _) (by
    intro X Y f
    change FiniteSetGroupoid.sumHom (Equiv.refl (Fin k)) f = stabilize k n f
    exact tensor_stabilize k n f)
noncomputable def standardCastIso {m n:ℕ} (h:m=n) : standardNerveInclusion m ≅
    (castGroup h).toMonoidHom.toFunctor ⋙ standardNerveInclusion n := by
  subst n
  exact Iso.refl _
noncomputable def standardSuccessorIso (n:ℕ) :
    standardNerveInclusion n ⋙ tensorLeft (⟨1⟩:FiniteSetGroupoid) ≅
      (successorStabilize n).toFunctor ⋙ standardNerveInclusion (n+1) :=
  standardTensorIso 1 n ≪≫
    Functor.isoWhiskerLeft (stabilize 1 n).toFunctor (standardCastIso (Nat.add_comm 1 n)) ≪≫
      (Functor.associator _ _ _).symm
end SimpleAmenable.SymmetricConfiguration

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.SymmetricConfiguration
open FreeChains ComponentTranslation GroupoidComponentHomology PolygonObject

attribute [local instance 1200] Rep.hV2
noncomputable def representativeGeneratorIso : repr generator ≅ (⟨1⟩:FiniteSetGroupoid) :=
  Skeleton.isoOfEq (repr_component _)
noncomputable def representativeSuccessorIso (n:ℕ) :
    standardNerveInclusion n ⋙ tensorLeft (repr generator) ≅
      (successorStabilize n).toFunctor ⋙ standardNerveInclusion (n+1) :=
  Functor.isoWhiskerLeft (standardNerveInclusion n)
    ((tensoringLeft FiniteSetGroupoid).mapIso representativeGeneratorIso) ≪≫ standardSuccessorIso n
noncomputable def fiberSuccessorIso (n:ℕ) :
    standardFiberInclusion n ⋙
      ComponentTranslation.translate generator (generator^n) (generator^(n+1)) (pow_succ' _ _).symm ≅
        (successorStabilize n).toFunctor ⋙ standardFiberInclusion (n+1) :=
  NatIso.ofComponents (fun x=>ObjectProperty.isoMk _ ((representativeSuccessorIso n).app x)) (by
    intro x y f
    apply ObjectProperty.hom_ext
    exact (representativeSuccessorIso n).hom.naturality f)
end SimpleAmenable.SymmetricConfiguration

end

end OAI
end


