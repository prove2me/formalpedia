-- Prove2me | Definitions.Def_OAIQ65Sa019
-- name    : OAIQ65Sa019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T04:29:14.349657+00:00
-- url     : https://prove2.me/theorems/1552f7e6-88aa-451d-a4c0-9f46fceb4686
-- title:
--   Definitions bundle OAIQ65Sa019 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 71 declarations of OpenAI's Lean: 26 definitions, 9 instances and 36 theorems. The definitions and types are `OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.backPoint`, `OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.translateFiber`, `OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.translationEvaluationIso`, `OAI.SimpleAmenable.PolygonObject.Labelled.initialCore`, `OAI.SimpleAmenable.PolygonObject.Labelled.initialIso`, `OAI.SimpleAmenable.PolygonObject.Labelled.reindexFunctor`, `OAI.SimpleAmenable.PolygonObject.Labelled.reindexInitial`, `OAI.SimpleAmenable.PolygonObject.Labelled.reindexLadder`, `OAI.SimpleAmenable.PolygonObject.Labelled.reindexStringIso`, `OAI.SimpleAmenable.PolygonObject.Labelled.stringsCore`, `OAI.SimpleAmenable.PolygonObject.Labelled.vertexArrow`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.degreeBarHomologyIsColimit`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.degreeHomologyIsColimit`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.emptyPointIso`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.homologyCoefficientIso`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.homologyCoordinateIso`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.middleBarHomologyIsColimit`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.pointEvaluationIso`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.pointFiber`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.tripleBarHomologyIsColimit`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.labelMap`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.pointValue`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.relabelCoefficients`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.stepTranslate`, `OAI.SimpleAmenable.PolygonObject.stringEval`, `OAI.SimpleAmenable.PolygonTracks.standardNerveInclusion`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `SimpleAmenable_Configurations_CellFiber`, `SimpleAmenable_Configurations_LabelledStringEquiv`, `SimpleAmenable_Configurations_PolygonComponentStable`, `SimpleAmenable_Configurations_TranslationFiber`, `SimpleAmenable_Homology_PointFiberHomology`, `SimpleAmenable_Homology_RelabelCoefficients`, `SimpleAmenable_Homology_StageHomologyCoordinates`, `SimpleAmenable_Homology_StageRefinementHomology`, `SimpleAmenable_Homology_TranslationCoefficients`, `SimpleAmenable_Simplicial_StageCoordinateMaps`, `SimpleAmenable_Simplicial_StageSimplicialColimit`, `SimpleAmenable_Simplicial_TrajectoryReindexLabels`, `SimpleAmenable_Simplicial_TranslationFiberMonoidal`, `SimpleAmenable_Simplicial_TripleBarMaps`.
--
--   **Imports.** It imports the bundles `OAIQ65Sa012` and `OAIQ65Sa017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ65Sa021` and `OAIQ65Sa023`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ65Sa012
import Definitions.Def_OAIQ65Sa017

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TripleBarMaps
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.positionalPropertyInverse _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject

variable {a n : ℕ}
noncomputable def stringEval : StringGroupoid a n ⥤ PolygonObject a where
  obj F := F.obj.obj 0
  map f := f.hom.app 0
  map_id _ := rfl
  map_comp _ _ := rfl
instance instFaithfulStringGroupoidStringEval : (stringEval (a:=a) (n:=n)).Faithful where
  map_injective h := by apply WideSubcategory.hom_ext; exact ladder_ext h
namespace Labelled
noncomputable def initialIso : forget (a:=a) (n:=n) ≅ toStrings ⋙ stringEval :=
  NatIso.ofComponents (fun U =>
    @asIso (PolygonObject a) _ _ _ (initial U) (IsIso.of_groupoid (C := PolygonObject a) _)) (by
    intro U V f
    change f.arrow ≫ initial V = initial U ≫ (ladder f).hom.app 0
    rw [ladder_zero]
    simp [initialArrow])
end Labelled
end SimpleAmenable.PolygonObject

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_CellFiber
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.newLabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.refineEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonObject.positionalPropertyInverse _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open UniformObject BarFinitePower

variable {a n : ℕ} (S : Stage a n)
variable (b : Fin S.partition.size × Fin S.support.card)
    (c : GenericSquare a × (Fin n → CutRing × CutRing))
    (hp : S.partition.color c.1=b.1) (hl : S.L b.2=c.2)

noncomputable def pointFiber (U : S.Obj) :
    UniformObject.Fiber U b ≃ Labelled.PointFiber.Fiber U.obj c where
  toFun x := ⟨⟨(x.val.val.1,c.1),
    (U.uniform x.val.val.1 x.val.val.2 c.1 (by
      rw [x.property.1,S.partition.color_point,hp])).mp x.val.property⟩,rfl,
    x.property.2.trans hl⟩
  invFun y := ⟨⟨(y.val.val.1,S.partition.point b.1),
    (U.uniform y.val.val.1 y.val.val.2 (S.partition.point b.1) (by
      rw [y.property.1,hp,S.partition.color_point])).mp y.val.property⟩,rfl,
    y.property.2.trans hl.symm⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl x.property.1.symm
  right_inv y := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl y.property.1.symm

lemma pointFiber_natural {U V : S.Obj} (f : U ⟶ V) (x : Fiber U b) :
    pointFiber S b c hp hl V (fiberMap f b x)=
      Labelled.PointFiber.fiberMap f.arrow c (pointFiber S b c hp hl U x) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact f.uniform x.val (pointFiber S b c hp hl U x).val rfl (by
      change S.partition.color x.val.val.2=S.partition.color c.1
      rw [x.property.1,S.partition.color_point,hp])
  · exact (f.arrow.positional (pointFiber S b c hp hl U x).val).symm

noncomputable def pointEvaluationIso :
    evaluation (P:=S.partition) (L:=S.L) ⋙ project _ b ≅
      S.forget ⋙ Labelled.PointFiber.evaluation ⋙ project _ c :=
  NatIso.ofComponents (fun U => asIso (X := UniformObject.E.obj U b)
    (Y := Labelled.PointFiber.E.obj U.obj c)
    ((enumerate U b).symm.trans ((pointFiber S b c hp hl U).trans
      (Labelled.PointFiber.enumerate U.obj c)))) (by
      intro U V f
      apply Equiv.ext
      intro x
      obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
      dsimp only [Functor.comp_map,Pi.eval,project,asIso_hom,Equiv.trans_apply,Equiv.symm_apply_apply]
      change Labelled.PointFiber.enumerate V.obj c (pointFiber S b c hp hl V
          ((enumerate V b).symm (UniformObject.E.map f b (enumerate U b x)))) =
        Labelled.PointFiber.E.map f.arrow c (Labelled.PointFiber.enumerate U.obj c
          (pointFiber S b c hp hl U ((enumerate U b).symm (enumerate U b x))))
      rw [E_map_enum,Equiv.symm_apply_apply,Equiv.symm_apply_apply,
        Labelled.PointFiber.E_map_enum,pointFiber_natural])

lemma pointFiber_sum_inl (U V : S.Obj) (x : Fiber U b) :
    pointFiber S b c hp hl (UniformObject.sum U V) (fiberSum U V b (.inl x)) =
      Labelled.PointFiber.fiberSum U.obj V.obj c (.inl (pointFiber S b c hp hl U x)) := rfl
lemma pointFiber_sum_inr (U V : S.Obj) (x : Fiber V b) :
    pointFiber S b c hp hl (UniformObject.sum U V) (fiberSum U V b (.inr x)) =
      Labelled.PointFiber.fiberSum U.obj V.obj c (.inr (pointFiber S b c hp hl V x)) := rfl
lemma pointEvaluationIso_enum (U : S.Obj) (x : Fiber U b) :
    (pointEvaluationIso S b c hp hl).hom.app U (enumerate U b x) =
      Labelled.PointFiber.enumerate U.obj c (pointFiber S b c hp hl U x) := by
  change Labelled.PointFiber.enumerate U.obj c (pointFiber S b c hp hl U
    ((enumerate U b).symm (enumerate U b x)))=_
  rw [Equiv.symm_apply_apply]

instance pointEvaluationIso_monoidal : NatTrans.IsMonoidal (pointEvaluationIso S b c hp hl).hom where
  unit := by apply Equiv.ext; intro x; exact Fin.elim0 x
  tensor U V := by
    change ((𝟙 _ ≫ mu U V b) ≫ _) = (_ ≫ (𝟙 _ ≫ Labelled.PointFiber.mu U.obj V.obj c) ≫
      (Labelled.PointFiber.E.map (𝟙 (U.obj ⊗ V.obj))) c)
    rw [CategoryTheory.Functor.map_id]
    simp only [Category.id_comp]
    apply Equiv.ext
    intro x
    change (pointEvaluationIso S b c hp hl).hom.app (UniformObject.sum U V) (mu U V b x) =
      Labelled.PointFiber.mu U.obj V.obj c
        (FiniteSetGroupoid.sumHom ((pointEvaluationIso S b c hp hl).hom.app U)
          ((pointEvaluationIso S b c hp hl).hom.app V) x)
    obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (UniformObject.E.obj U b) (UniformObject.E.obj V b)).surjective x
    cases x with
    | inl x =>
      obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
      erw [mu_inl,pointEvaluationIso_enum,pointFiber_sum_inl,FiniteSetGroupoid.sumHom_inl,
        pointEvaluationIso_enum,Labelled.PointFiber.mu_inl]
    | inr x =>
      obtain ⟨x,rfl⟩ := (enumerate V b).surjective x
      erw [mu_inr,pointEvaluationIso_enum,pointFiber_sum_inr,FiniteSetGroupoid.sumHom_inr,
        pointEvaluationIso_enum,Labelled.PointFiber.mu_inr]

variable {S b hp hl}
lemma point_new_label_size (hc : ∀j,S.L j ≠ c.2) (U : S.Obj) :
    (Labelled.PointFiber.E.obj U.obj c).size=0 := by
  have := pointFiber_empty_of_new_label c hc U
  exact Fintype.card_eq_zero
noncomputable def emptyPointIso (hc : ∀j,S.L j ≠ c.2) :
    FiniteSetGroupoid.terminal ⋙ FiniteSetGroupoid.emptyFunctor ≅
      S.forget ⋙ Labelled.PointFiber.evaluation ⋙ project _ c :=
  NatIso.ofComponents (fun U => asIso (X := FiniteSetGroupoid.empty)
    (Y := Labelled.PointFiber.E.obj U.obj c) (finCongr (point_new_label_size c hc U).symm)) (by
      intros; apply Equiv.ext; intro x; exact Fin.elim0 x)
noncomputable instance emptyPointIsoMonoidal (hc : ∀j,S.L j ≠ c.2) :
    NatTrans.IsMonoidal (emptyPointIso c hc).hom where
  unit := by apply Equiv.ext; intro x; exact Fin.elim0 x
  tensor _ _ := by apply Equiv.ext; intro x; exact Fin.elim0 x

end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_LabelledStringEquiv
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.emptyPointIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.pointEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.positionalPropertyInverse _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled

variable {a n : ℕ}
noncomputable def initialCore : (toStrings (a:=a) (n:=n) ⋙ stringEval).CoreMonoidal :=
  Functor.Monoidal.coreMonoidalTransport initialIso
lemma initialCore_unit : (initialCore (a:=a) (n:=n)).εIso.hom=initial (𝟙_ _) := by
  change 𝟙 _ ≫ initial (𝟙_ _) = _
  exact Category.id_comp _
lemma initialCore_tensor (U V : Labelled a n) :
    (initialCore.μIso U V).hom=tensorInitial U V := by
  change (inv (initial U) ⊗ₘ inv (initial V)) ≫ 𝟙 _ ≫ initial (U⊗V) =
    inv (sumArrow (initial U) (initial V)) ≫ initial (U⊗V)
  simp only [Category.id_comp]
  congr 1
  apply (cancel_epi (sumArrow (initial U) (initial V))).mp
  change (initial U ⊗ₘ initial V) ≫ (inv (initial U) ⊗ₘ inv (initial V)) = _
  rw [tensorHom_comp_tensorHom]
  simp
  rfl
noncomputable def stringsCore : (toStrings (a:=a) (n:=n)).CoreMonoidal where
  εIso := @asIso (StringGroupoid a n) _ _ _ unitLadder
    (IsIso.of_groupoid (C := StringGroupoid a n) _)
  μIso U V := @asIso (StringGroupoid a n) _ _ _ (tensorLadder U V)
    (IsIso.of_groupoid (C := StringGroupoid a n) _)
  μIso_hom_natural_left := by
    intro U V f W
    apply (stringEval (a:=a) (n:=n)).map_injective
    change sumArrow ((ladder f).hom.app 0) (𝟙 _) ≫ (tensorLadder V W).hom.app 0 =
      (tensorLadder U W).hom.app 0 ≫ (ladder (f ▷ W)).hom.app 0
    rw [tensorLadder_zero,tensorLadder_zero,←initialCore_tensor,←initialCore_tensor]
    exact initialCore.μIso_hom_natural_left f W
  μIso_hom_natural_right := by
    intro U V W f
    apply (stringEval (a:=a) (n:=n)).map_injective
    change sumArrow (𝟙 _) ((ladder f).hom.app 0) ≫ (tensorLadder W V).hom.app 0 =
      (tensorLadder W U).hom.app 0 ≫ (ladder (W ◁ f)).hom.app 0
    rw [tensorLadder_zero,tensorLadder_zero,←initialCore_tensor,←initialCore_tensor]
    exact initialCore.μIso_hom_natural_right W f
  associativity := by
    intro U V W
    apply (stringEval (a:=a) (n:=n)).map_injective
    change sumArrow ((tensorLadder U V).hom.app 0) (𝟙 _) ≫
      (tensorLadder (U⊗V) W).hom.app 0 ≫ (ladder (α_ U V W).hom).hom.app 0 =
      sumAssoc _ _ _ ≫ sumArrow (𝟙 _) ((tensorLadder V W).hom.app 0) ≫
        (tensorLadder U (V⊗W)).hom.app 0
    simp only [tensorLadder_zero,←initialCore_tensor]
    exact initialCore.associativity U V W
  left_unitality := by
    intro U
    apply (stringEval (a:=a) (n:=n)).map_injective
    change leftUnit _ = sumArrow (unitLadder.hom.app 0) (𝟙 _) ≫
      (tensorLadder (𝟙_ _) U).hom.app 0 ≫ (ladder (λ_ U).hom).hom.app 0
    rw [unitLadder_zero,tensorLadder_zero,←initialCore_unit,←initialCore_tensor]
    exact initialCore.left_unitality U
  right_unitality := by
    intro U
    apply (stringEval (a:=a) (n:=n)).map_injective
    change rightUnit _ = sumArrow (𝟙 _) (unitLadder.hom.app 0) ≫
      (tensorLadder U (𝟙_ _)).hom.app 0 ≫ (ladder (ρ_ U).hom).hom.app 0
    rw [unitLadder_zero,tensorLadder_zero,←initialCore_unit,←initialCore_tensor]
    exact initialCore.right_unitality U
noncomputable instance instMonoidalStringGroupoidToStrings : (toStrings (a:=a) (n:=n)).Monoidal := stringsCore.toMonoidal
noncomputable instance instBraidedStringGroupoidToStrings : (toStrings (a:=a) (n:=n)).Braided where
  braided U V := by
    apply (stringEval (a:=a) (n:=n)).map_injective
    change (tensorLadder U V).hom.app 0 ≫ (ladder (β_ U V).hom).hom.app 0 =
      sumSwap _ _ ≫ (tensorLadder V U).hom.app 0
    rw [tensorLadder_zero,tensorLadder_zero,ladder_zero]
    change (inv (sumArrow (initial U) (initial V)) ≫ initial (U⊗V)) ≫
        (inv (initial (U⊗V)) ≫ sumSwap _ _ ≫ initial (V⊗U)) =
      sumSwap _ _ ≫ inv (sumArrow (initial V) (initial U)) ≫ initial (V⊗U)
    simp only [Category.assoc,IsIso.hom_inv_id_assoc]
    apply (cancel_epi (sumArrow (initial U) (initial V))).mp
    simp only [IsIso.hom_inv_id_assoc]
    have h := BraidedCategory.braiding_naturality (initial U) (initial V)
    change sumArrow (initial U) (initial V) ≫ sumSwap _ _ =
      sumSwap _ _ ≫ sumArrow (initial V) (initial U) at h
    rw [←Category.assoc (sumArrow (initial U) (initial V)),h]
    simp

lemma tripleBar_homology_isIso (j : ℕ) :
    IsIso (SSet.homologyMap (IntervalBar.Diagram.bar₃Map (toStrings (a:=a) (n:=n)))
      DiagonalResolution.Z j) :=
  IntervalBar.Diagram.bar₃Map_homology_isIso toStrings j
end SimpleAmenable.PolygonObject.Labelled

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_StageRefinementHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.emptyFunctorMonoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.instBraidedTerminalEmptyFunctor _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.emptyPointIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.newLabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.pointEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar.Diagram BarFinitePower UniformObject

variable {a n : ℕ} {S T : Stage a n} (h : S≤T)
variable (b : Fin S.partition.size × Fin S.support.card)
    (c : Fin T.partition.size × Fin T.support.card)
    (hp : S.partition.color (T.partition.point c.1)=b.1)
    (hl : S.L b.2=T.L c.2)
include hp hl

lemma refinement_coordinate_homology (j:ℕ) :
    SSet.homologyMap (bar₃Map (evaluation (P:=S.partition) (L:=S.L) ⋙ project _ b))
        DiagonalResolution.Z j =
    SSet.homologyMap (bar₃Map (inclusion h ⋙ evaluation (P:=T.partition) (L:=T.L) ⋙ project _ c))
        DiagonalResolution.Z j :=
  bar₃Map_eq_of_monoidalNatTrans (refineEvaluationIso h b c hp hl).hom j
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StageCoordinateMaps
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.emptyPointIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.pointEvaluationIso_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar.Diagram BarFinitePower UniformObject

variable {a n:ℕ} {S T:Stage a n} (h:S≤T)
    (c:Fin T.partition.size × Fin T.support.card)
variable (S)
variable {S}
lemma refinement_coordinate
    (b:Fin S.partition.size × Fin S.support.card)
    (hp:S.partition.color (T.partition.point c.1)=b.1)
    (hl:S.L b.2=T.L c.2) (j:ℕ) :
    SSet.homologyMap (S.finiteProductComparison ≫ evaluate _ _ b) DiagonalResolution.Z j =
      SSet.homologyMap (bar₃Map (inclusion h) ≫ T.finiteProductComparison ≫ evaluate _ _ c)
        DiagonalResolution.Z j := by
  rw [finiteProductComparison_coordinate,finiteProductComparison_coordinate,←bar₃Map_comp]
  exact refinement_coordinate_homology h b c hp hl j
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonComponentStable
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instBraidedStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.positionalPropertyInverse _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions
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
noncomputable def standardNerveInclusion (a n:ℕ) :
    SingleObj (polygonFullGroup a n) ⥤ PolygonObject a :=
  (PolygonObject.standardAutEquiv a n).symm.toMonoidHom.toFunctor ⋙
    GroupoidComponentHomology.inclusion (PolygonObject.standard a n)
end SimpleAmenable.PolygonTracks

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_TranslationFiber
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.emptyFunctorMonoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.instBraidedTerminalEmptyFunctor _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instBraidedStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.emptyPointIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.newLabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.pointEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.refineEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonObject.positionalPropertyInverse _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Classical
namespace SimpleAmenable.PolygonObject.Labelled.PointFiber

variable {a n : ℕ} (d : (Fin n → CutRing × CutRing) → CutRing × CutRing)
variable (c : GenericSquare a × (Fin n → CutRing × CutRing))
noncomputable def backPoint : GenericSquare a × (Fin n → CutRing × CutRing) :=
  (SimpleAmenable.translate a (-d c.2) c.1,c.2)
lemma translated_predicate (U : Labelled a n) (x : U.polygon.Point) :
    (x.val.2=(backPoint d c).1 ∧ U.label x.val.1=(backPoint d c).2) ↔
      (((translateArrow d U).toEquiv x).val.2=c.1 ∧
        (translateObj d U).label ((translateArrow d U).toEquiv x).val.1=c.2) := by
  change (x.val.2=SimpleAmenable.translate a (-d c.2) c.1 ∧ U.label x.val.1=c.2) ↔
    (SimpleAmenable.translate a (d (U.label x.val.1)) x.val.2=c.1 ∧ U.label x.val.1=c.2)
  constructor
  · rintro ⟨hp,hl⟩
    refine ⟨?_,hl⟩
    rw [hl,hp,←SimpleAmenable.translate_add,add_neg_cancel,SimpleAmenable.translate_zero]
  · rintro ⟨hp,hl⟩
    refine ⟨?_,hl⟩
    rw [hl] at hp
    apply (translation a (d c.2)).injective
    change SimpleAmenable.translate a (d c.2) x.val.2 = _
    rw [hp]
    change _ = SimpleAmenable.translate a (d c.2) (SimpleAmenable.translate a (-d c.2) c.1)
    rw [←SimpleAmenable.translate_add,add_neg_cancel,SimpleAmenable.translate_zero]
noncomputable def translateFiber (U : Labelled a n) :
    Fiber U (backPoint d c) ≃ Fiber (translateObj d U) c :=
  (translateArrow d U).toEquiv.subtypeEquiv (translated_predicate d c U)
@[simp] lemma translateFiber_val (U : Labelled a n) (x : Fiber U (backPoint d c)) :
    (translateFiber d c U x).val=(translateArrow d U).toEquiv x.val := rfl
lemma translateFiber_natural {U V : Labelled a n} (f : U ⟶ V)
    (x : Fiber U (backPoint d c)) :
    translateFiber d c V (fiberMap f (backPoint d c) x) =
      fiberMap (translateHom d f) c (translateFiber d c U x) := by
  apply Subtype.ext
  change (translateArrow d V).toEquiv (f.arrow.toEquiv x.val) =
    (inv (translateArrow d U) ≫ f.arrow ≫ translateArrow d V).toEquiv
      ((translateArrow d U).toEquiv x.val)
  simp only [arrow_comp_apply,inv_arrow_apply,Equiv.symm_apply_apply]
noncomputable def translationEvaluationIso :
    evaluation ⋙ BarFinitePower.project _ (backPoint d c) ≅
      translateFunctor d ⋙ evaluation ⋙ BarFinitePower.project _ c :=
  NatIso.ofComponents (fun U => asIso (X := E.obj U (backPoint d c))
    (Y := E.obj (translateObj d U) c)
    ((enumerate U (backPoint d c)).symm.trans ((translateFiber d c U).trans
      (enumerate (translateObj d U) c)))) (by
    intro U V f
    apply Equiv.ext; intro x
    obtain ⟨x,rfl⟩ := (enumerate U (backPoint d c)).surjective x
    change enumerate (translateObj d V) c (translateFiber d c V
      ((enumerate V (backPoint d c)).symm (E.map f (backPoint d c)
        (enumerate U (backPoint d c) x)))) = E.map (translateHom d f) c
      (enumerate (translateObj d U) c (translateFiber d c U
        ((enumerate U (backPoint d c)).symm (enumerate U (backPoint d c) x))))
    rw [E_map_enum,Equiv.symm_apply_apply,Equiv.symm_apply_apply,E_map_enum,translateFiber_natural])
@[simp] lemma translationEvaluationIso_enum (U : Labelled a n) (x : Fiber U (backPoint d c)) :
    (translationEvaluationIso d c).hom.app U (enumerate U (backPoint d c) x) =
      enumerate (translateObj d U) c (translateFiber d c U x) := by
  change enumerate (translateObj d U) c (translateFiber d c U
    ((enumerate U (backPoint d c)).symm (enumerate U (backPoint d c) x))) = _
  rw [Equiv.symm_apply_apply]
end SimpleAmenable.PolygonObject.Labelled.PointFiber

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StageSimplicialColimit
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.IntervalBar.Diagram.reindex_map_monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.diagramPropertyBraided _root_.OAI.RestrictedNerve.diagramPropertyInverse _root_.OAI.RestrictedNerve.diagramPropertyMonoidal _root_.OAI.RestrictedNerve.diagramProperty_multiplicative _root_.OAI.RestrictedNerve.instIsEquivalenceDiagramStringsPosDiagramsDiagramPropertyTransposeDiagram _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.posDiagramBraided _root_.OAI.RestrictedNerve.posDiagramInclusionBraided _root_.OAI.RestrictedNerve.posDiagramInclusionEquivalence _root_.OAI.RestrictedNerve.posDiagramInclusionEssSurj _root_.OAI.RestrictedNerve.posDiagramInclusionMonoidal _root_.OAI.RestrictedNerve.posDiagramIsIso _root_.OAI.RestrictedNerve.posDiagramMonoidal _root_.OAI.RestrictedNerve.posDiagramSymmetric _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.posReindex_inclusion_monoidal _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.RestrictedNerve.transposeBraided _root_.OAI.RestrictedNerve.transposeMonoidal _root_.OAI.RestrictedNerve.transpose_evaluation_monoidal _root_.OAI.RestrictedNerve.transpose_reindex_monoidal _root_.OAI.RestrictedNerve.triplePosInclusionEquivalence _root_.OAI.RestrictedNerve.tripleTransposeEquivalence _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instBraidedStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.emptyPointIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.newLabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.pointEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.refineEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar IntervalBar.Diagram ColimitTransfer

variable {a n : ℕ} (p q : ℕ)
noncomputable def degreeHomologyIsColimit (r : SimplexCategoryᵒᵖ) (k:ℕ) :
    IsColimit (((evaluation SimplexCategoryᵒᵖ Cat).obj r ⋙ H k).mapCocone
      (degreeRowsCocone (a:=a) (n:=n) p q)) := by
  let u : degreeRowsStage (a:=a) (n:=n) p q ⋙ (evaluation SimplexCategoryᵒᵖ Cat).obj r ⋙ H k ≅
      tripleHomologyStage r.unop.len q p k :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro S T h
      simp only [Iso.refl_hom]
      exact (tripleHomologyStage_map r.unop.len q p k h).symm)
  let pointIso : (((evaluation SimplexCategoryᵒᵖ Cat).obj r ⋙ H k).mapCocone
      (degreeRowsCocone (a:=a) (n:=n) p q)).pt ≅
      (tripleHomologyCocone r.unop.len q p k).pt := Iso.refl _
  apply ofIsos _ (tripleHomologyCocone r.unop.len q p k) u.hom pointIso.hom _
    (tripleHomologyIsColimit r.unop.len q p k)
  intro S
  change (H k).map (Diagram.map (I:=Fin (r.unop.len+1))
    (Diagram.map (I:=Fin (q+1)) (Diagram.map (I:=Fin (p+1)) S.forget))).toCatHom ≫ 𝟙 _ =
      (𝟙 _) ≫ (tripleHomologyCocone r.unop.len q p k).ι.app S
  rw [Category.comp_id,Category.id_comp]
  exact (tripleHomologyCocone_ι r.unop.len q p k S).symm
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar IntervalBar.Diagram ColimitTransfer SimplicialDiagonal

variable {a n : ℕ}
noncomputable def degreeBarHomologyIsColimit (p q k:ℕ) :
    IsColimit ((nerveDiagonal ⋙ SSet.homologyFunctor DiagonalResolution.Z k).mapCocone
      (degreeRowsCocone (a:=a) (n:=n) p q)) := by
  exact diagonalHomologyIsColimit
    (((Functor.whiskeringRight I Cat SSet).obj nerveFunctor).mapCocone (degreeRowsCocone p q))
    (fun r j => degreeHomologyIsColimit p q r j) k
noncomputable def middleBarHomologyIsColimit (p k:ℕ) :
    IsColimit ((diagonal ⋙ SSet.homologyFunctor DiagonalResolution.Z k).mapCocone
      (middleRowsCocone (a:=a) (n:=n) p)) := by
  apply diagonalHomologyIsColimit
  intro q j
  exact degreeBarHomologyIsColimit p q.unop.len j

noncomputable def tripleBarHomologyIsColimit (k:ℕ) :
    IsColimit ((diagonal ⋙ SSet.homologyFunctor DiagonalResolution.Z k).mapCocone
      (topRowsCocone (a:=a) (n:=n))) := by
  apply diagonalHomologyIsColimit
  intro p j
  exact middleBarHomologyIsColimit p.unop.len j
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_StageHomologyCoordinates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.emptyPointIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.pointEvaluationIso_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar.Diagram BarFinitePower FreeChains

attribute [local instance 1200] Pi.module Prod.instModule
variable {a n:ℕ}
lemma homologyCoordinates_refinement {S T:Stage a n} (h:S≤T) (j:ℕ) (hj:0<j) :
    SSet.homologyMap (bar₃Map (inclusion h)) Z j ≫ T.homologyCoordinates j =
      S.homologyCoordinates j ≫ (coefficientDiagram (a:=a) (n:=n) (K j)).map (homOfLE h) := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; funext c
  change T.homologyCoordinates j (SSet.homologyMap (bar₃Map (inclusion h)) Z j x) c =
    (S.realize (K:=K j) (S.homologyCoordinates j x) (T.label c.2)).val (T.partition.point c.1)
  rw [homologyCoordinates_at]
  change (SSet.homologyMap (bar₃Map (inclusion h)) Z j ≫
    SSet.homologyMap (T.finiteProductComparison ≫ evaluate _ E c) Z j) x = _
  rw [←SSet.homologyMap_comp]
  by_cases hl:T.label c.2∈S.support
  · obtain ⟨b,hb⟩ := (S.label_range (T.label c.2)).mpr hl
    let d : Fin S.partition.size × Fin S.support.card := (S.partition.color (T.partition.point c.1),b)
    have hh : S.L b=T.L c.2 := congrArg Subtype.val hb
    rw [←refinement_coordinate h c d rfl hh j,←homologyCoordinates_at,←hb]
    erw [S.realize_at_label,BooleanStep.inflate_apply]
  · rw [refinement_new_label_zero h c (fun b hb => hl ((S.label_range (T.label c.2)).mp ⟨b,Subtype.ext hb⟩)) j hj]
    erw [S.realize_outside _ _ hl]
    rfl
noncomputable def homologyCoordinateIso (j:ℕ) (hj:0<j) (hj5:j≤5) :
    topRowsStage (a:=a) (n:=n) ⋙ SimplicialDiagonal.diagonal ⋙ SSet.homologyFunctor Z j ≅
      coefficientDiagram (a:=a) (n:=n) (K j) :=
  NatIso.ofComponents (fun S => by
    haveI := S.homologyCoordinates_isIso j hj hj5
    exact asIso (C := ModuleCat ℤ) (X := (bar₃ (C:=S.Obj)).homology Z j)
      (Y := (coefficientDiagram (a:=a) (n:=n) (K j)).obj S)
      (S.homologyCoordinates j)) (fun h => homologyCoordinates_refinement (leOfHom h) j hj)

noncomputable def homologyCoefficientIso (j:ℕ) (hj:0<j) (hj5:j≤5) :
    (bar₃ (C:=Labelled a n)).homology Z j ≅
      ModuleCat.of ℤ (Coefficients a n (K j)) :=
  (tripleBarHomologyIsColimit (a:=a) (n:=n) j).coconePointsIsoOfNatIso
    (coefficientIsColimit (a:=a) (n:=n) (K j)) (homologyCoordinateIso j hj hj5)
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PointFiberHomology
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage
open IntervalBar.Diagram BarFinitePower FreeChains

variable {a n : ℕ} {K : Type} [AddCommGroup K]
variable {modK : Module ℤ K}
noncomputable def pointValue (c : GenericSquare a × ReducedLabel n) :
    Coefficients a n K →ₗ[ℤ] K where
  toFun f := (f c.2).val c.1
  map_add' _ _ := rfl
  map_smul' r f := by
    let h : Coefficients a n K →+ K := {
      toFun f := (f c.2).val c.1
      map_zero' := rfl
      map_add' _ _ := rfl }
    exact map_intCast_smul h ℤ ℤ r f
namespace Stage
variable (S : Stage a n)
lemma homologyCoefficientIso_stage (j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    SSet.homologyMap (bar₃Map S.forget) Z j ≫ (homologyCoefficientIso (a:=a) (n:=n) j hj hj5).hom =
      S.homologyCoordinates j ≫ ModuleCat.ofHom (S.realize (K:=Stage.K j)) :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom
    (tripleBarHomologyIsColimit j) (coefficientIsColimit (Stage.K j))
    (homologyCoordinateIso j hj hj5) S
lemma homologyCoefficientIso_point (j : ℕ) (hj : 0<j) (hj5 : j≤5)
    (c : GenericSquare a × ReducedLabel n) :
    (homologyCoefficientIso (a:=a) (n:=n) j hj hj5).hom ≫
      ModuleCat.ofHom (pointValue (K:=Stage.K j) c) =
    SSet.homologyMap (bar₃Map (Labelled.PointFiber.evaluation ⋙ project _ (c.1,c.2.val))) Z j := by
  apply (tripleBarHomologyIsColimit (a:=a) (n:=n) j).hom_ext
  intro S
  change SSet.homologyMap (bar₃Map S.forget) Z j ≫
      ((homologyCoefficientIso j hj hj5).hom ≫ ModuleCat.ofHom (pointValue c)) =
    SSet.homologyMap (bar₃Map S.forget) Z j ≫
      SSet.homologyMap (bar₃Map (Labelled.PointFiber.evaluation ⋙ project _ (c.1,c.2.val))) Z j
  rw [←Category.assoc,homologyCoefficientIso_stage,←SSet.homologyMap_comp,←bar₃Map_comp]
  by_cases hc : c.2∈S.support
  · obtain ⟨k,hk⟩ := (S.label_range c.2).mpr hc
    let b : Fin S.partition.size × Fin S.support.card := (S.partition.color c.1,k)
    have hl : S.L b.2 = c.2.val := congrArg Subtype.val hk
    rw [←bar₃Map_eq_of_monoidalNatTrans
      (pointEvaluationIso S b (c.1,c.2.val) rfl hl).hom j]
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
    change (S.realize (K:=Stage.K j) (S.homologyCoordinates j x) c.2).val c.1 = _
    rw [←hk]
    erw [S.realize_at_label,BooleanStep.inflate_apply]
    rw [←S.finiteProductComparison_coordinate b,←S.homologyCoordinates_at]
  · rw [←bar₃Map_eq_of_monoidalNatTrans
      (emptyPointIso (c.1,c.2.val) (fun k hk => hc
        ((S.label_range c.2).mp ⟨k,Subtype.ext hk⟩))).hom j,
      bar₃Map_comp,SSet.homologyMap_comp]
    have hz := bar₃_acyclic (C:=FiniteSetGroupoid.Terminal)
      (fun x y => ⟨eqToHom (Subsingleton.elim x y)⟩) j hj
    rw [hz.eq_of_src (SSet.homologyMap (bar₃Map FiniteSetGroupoid.emptyFunctor) Z j) 0,comp_zero]
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
    change (S.realize (K:=Stage.K j) (S.homologyCoordinates j x) c.2).val c.1 = 0
    erw [S.realize_outside _ _ hc]
    rfl
end Stage
end SimpleAmenable.PolygonObject.LabelledStage

end

namespace SimpleAmenable.PolygonObject.Labelled.Cell

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Classical
open IntervalBar.Diagram BarFinitePower FreeChains LabelledStage

variable {a n : ℕ} (P : polygonAlgebra a) (l : ReducedLabel n)
lemma homology_coefficient (j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    SSet.homologyMap (bar₃Map (functor P l)) Z j ≫
      (Stage.homologyCoefficientIso (a:=a) (n:=n) j hj hj5).hom =
    ModuleCat.ofHom (coefficient (K:=Stage.K j) P l) := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
  apply Finsupp.ext; intro k
  apply Subtype.ext; funext p
  have h := congrArg (fun f : Stage.K j ⟶ Stage.K j => f x)
    (congrArg (fun f => SSet.homologyMap (bar₃Map (functor P l)) Z j ≫ f)
      (Stage.homologyCoefficientIso_point (a:=a) (n:=n) j hj hj5 (p,k)))
  rw [←SSet.homologyMap_comp,←bar₃Map_comp,homology_point P l j hj (p,k)] at h
  change _ = (Finsupp.single l (step P x) k).val p
  refine h.trans ?_
  by_cases hl:l=k
  · subst k
    simp only [and_true,Finsupp.single_eq_same,step_apply]
    split_ifs <;> rfl
  · simp only [hl,and_false,ite_false,Finsupp.single_eq_of_ne (Ne.symm hl)]
    rfl
end SimpleAmenable.PolygonObject.Labelled.Cell

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RelabelCoefficients
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Classical
namespace SimpleAmenable.PolygonObject.LabelledStage

variable {a n m : ℕ} {K : Type} [AddCommGroup K]
def labelMap (f : (Fin n → CutRing × CutRing) → (Fin m → CutRing × CutRing))
    (hf : ∀g,Labelled.Reduced g → Labelled.Reduced (f g)) : ReducedLabel n → ReducedLabel m :=
  fun l => ⟨f l.val,hf l.val l.property⟩
variable (f : (Fin n → CutRing × CutRing) → (Fin m → CutRing × CutRing))
  (hf : ∀g,Labelled.Reduced g → Labelled.Reduced (f g))
noncomputable def relabelCoefficients : Coefficients a n K →ₗ[ℤ] Coefficients a m K where
  toFun := Finsupp.mapDomain (labelMap f hf)
  map_add' _ _ := Finsupp.mapDomain_add
  map_smul' r x := by
    let h : Coefficients a n K →+ Coefficients a m K := {
      toFun := Finsupp.mapDomain (labelMap f hf)
      map_zero' := Finsupp.mapDomain_zero
      map_add' _ _ := Finsupp.mapDomain_add }
    exact map_intCast_smul h ℤ ℤ r x
@[simp] lemma relabelCoefficients_single (l : ReducedLabel n) (s : BooleanStep a K) :
    relabelCoefficients (a:=a) (K:=K) f hf (Finsupp.single l s)=Finsupp.single (labelMap f hf l) s :=
  Finsupp.mapDomain_single
end SimpleAmenable.PolygonObject.LabelledStage

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Classical
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar.Diagram BarFinitePower FreeChains Labelled

variable {a n m : ℕ}
variable (f : (Fin n → CutRing × CutRing) → (Fin m → CutRing × CutRing))
  (hf : ∀g, Reduced g → Reduced (f g))
lemma homologyCoefficientIso_relabel (j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    SSet.homologyMap (bar₃Map (relabel (a:=a) f hf)) Z j ≫
      (homologyCoefficientIso (a:=a) (n:=m) j hj hj5).hom =
    (homologyCoefficientIso (a:=a) (n:=n) j hj hj5).hom ≫
      ModuleCat.ofHom (relabelCoefficients (a:=a) (K:=K j) f hf) := by
  apply (cancel_epi (homologyCoefficientIso (a:=a) (n:=n) j hj hj5).inv).mp
  rw [Iso.inv_hom_id_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply Cell.coefficient_ext
  intro P l x
  have he := congrArg (fun k : K j ⟶ ModuleCat.of ℤ (Coefficients a n (K j)) => k x)
    (Cell.homology_coefficient P l j hj hj5)
  change (SSet.homologyMap (bar₃Map (Cell.functor P l)) Z j ≫
    (homologyCoefficientIso j hj hj5).hom) x = Finsupp.single l (Cell.step P x) at he
  change ((homologyCoefficientIso j hj hj5).inv ≫
    SSet.homologyMap (bar₃Map (relabel f hf)) Z j ≫ (homologyCoefficientIso j hj hj5).hom)
      (Finsupp.single l (Cell.step P x)) = _
  conv_lhs => rw [←he]
  change (SSet.homologyMap (bar₃Map (Cell.functor P l)) Z j ≫
    (homologyCoefficientIso j hj hj5).hom ≫ (homologyCoefficientIso j hj hj5).inv ≫
    SSet.homologyMap (bar₃Map (relabel f hf)) Z j ≫
    (homologyCoefficientIso j hj hj5).hom) x = _
  rw [Iso.hom_inv_id_assoc,←Category.assoc,←SSet.homologyMap_comp,←bar₃Map_comp,
    bar₃Map_eq_of_monoidalNatTrans (Cell.relabelIso f hf P l).hom j]
  erw [Cell.homology_coefficient P (labelMap f hf l) j hj hj5]
  exact (relabelCoefficients_single f hf l (Cell.step P x)).symm
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TranslationFiberMonoidal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.emptyFunctorMonoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.instBraidedTerminalEmptyFunctor _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instBraidedStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.emptyPointIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.newLabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.pointEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.refineEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonObject.positionalPropertyInverse _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Classical
namespace SimpleAmenable.PolygonObject.Labelled.PointFiber

variable {a n : ℕ} (d : (Fin n → CutRing × CutRing) → CutRing × CutRing)
variable (c : GenericSquare a × (Fin n → CutRing × CutRing))
lemma translationFiber_sum_left (U V : Labelled a n) (x : Fiber U (backPoint d c)) :
    fiberMap (translationTensor d U V) c
      (fiberSum (translateObj d U) (translateObj d V) c (.inl (translateFiber d c U x))) =
    translateFiber d c (U⊗V) (fiberSum U V (backPoint d c) (.inl x)) := by
  apply Subtype.ext
  change (inv (sumArrow (translateArrow d U) (translateArrow d V)) ≫ translateArrow d (U⊗V)).toEquiv
    (sumPointEquiv _ _ (.inl ((translateArrow d U).toEquiv x.val))) = _
  rw [←sumArrow_inl,arrow_comp_apply,inv_arrow_apply,Equiv.symm_apply_apply]
  rfl
lemma translationFiber_sum_right (U V : Labelled a n) (x : Fiber V (backPoint d c)) :
    fiberMap (translationTensor d U V) c
      (fiberSum (translateObj d U) (translateObj d V) c (.inr (translateFiber d c V x))) =
    translateFiber d c (U⊗V) (fiberSum U V (backPoint d c) (.inr x)) := by
  apply Subtype.ext
  change (inv (sumArrow (translateArrow d U) (translateArrow d V)) ≫ translateArrow d (U⊗V)).toEquiv
    (sumPointEquiv _ _ (.inr ((translateArrow d V).toEquiv x.val))) = _
  rw [←sumArrow_inr,arrow_comp_apply,inv_arrow_apply,Equiv.symm_apply_apply]
  rfl
lemma translationEvaluation_tensor_left (U V : Labelled a n) (x : Fin (E.obj U (backPoint d c)).size) :
    (translationEvaluationIso d c).hom.app (U⊗V)
      (mu U V (backPoint d c) (FiniteSetGroupoid.sumEquiv _ _ (.inl x))) =
      E.map (translationTensor d U V) c (mu (translateObj d U) (translateObj d V) c
        (FiniteSetGroupoid.sumHom ((translationEvaluationIso d c).hom.app U)
          ((translationEvaluationIso d c).hom.app V) (FiniteSetGroupoid.sumEquiv _ _ (.inl x)))) := by
  obtain ⟨x,rfl⟩ := (enumerate U (backPoint d c)).surjective x
  erw [mu_inl,translationEvaluationIso_enum,FiniteSetGroupoid.sumHom_inl,
    translationEvaluationIso_enum,mu_inl,E_map_enum,translationFiber_sum_left]
  rfl
lemma translationEvaluation_tensor_right (U V : Labelled a n) (x : Fin (E.obj V (backPoint d c)).size) :
    (translationEvaluationIso d c).hom.app (U⊗V)
      (mu U V (backPoint d c) (FiniteSetGroupoid.sumEquiv _ _ (.inr x))) =
      E.map (translationTensor d U V) c (mu (translateObj d U) (translateObj d V) c
        (FiniteSetGroupoid.sumHom ((translationEvaluationIso d c).hom.app U)
          ((translationEvaluationIso d c).hom.app V) (FiniteSetGroupoid.sumEquiv _ _ (.inr x)))) := by
  obtain ⟨x,rfl⟩ := (enumerate V (backPoint d c)).surjective x
  erw [mu_inr,translationEvaluationIso_enum,FiniteSetGroupoid.sumHom_inr,
    translationEvaluationIso_enum,mu_inr,E_map_enum,translationFiber_sum_right]
  rfl
noncomputable instance translationEvaluationIsoMonoidal :
    NatTrans.IsMonoidal (translationEvaluationIso d c).hom where
  unit := by apply Equiv.ext; intro x; exact Fin.elim0 x
  tensor U V := by
    apply Equiv.ext; intro x
    change (translationEvaluationIso d c).hom.app (U⊗V) (mu U V (backPoint d c) x) =
      E.map (translationTensor d U V) c (mu (translateObj d U) (translateObj d V) c
        (FiniteSetGroupoid.sumHom ((translationEvaluationIso d c).hom.app U)
          ((translationEvaluationIso d c).hom.app V) x))
    obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (E.obj U (backPoint d c))
      (E.obj V (backPoint d c))).surjective x
    cases x with
    | inl x => exact translationEvaluation_tensor_left d c U V x
    | inr x => exact translationEvaluation_tensor_right d c U V x
end SimpleAmenable.PolygonObject.Labelled.PointFiber

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TranslationCoefficients
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Classical
namespace SimpleAmenable.PolygonObject.LabelledStage

variable {a n : ℕ} {K : Type} [AddCommGroup K]
noncomputable def stepTranslate (u : CutRing × CutRing) : BooleanStep a K →ₗ[ℤ] BooleanStep a K where
  toFun f := ⟨fun p => f.val (SimpleAmenable.translate a (-u) p),
    squareArrangement_translate f.property (-u)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end SimpleAmenable.PolygonObject.LabelledStage

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TrajectoryReindexLabels
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.translationEvaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.emptyPointIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.newLabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.pointEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.refineEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonObject.positionalPropertyInverse _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled
section

variable {a n m:ℕ}
noncomputable abbrev vertexArrow (U:Labelled a n) (i:Fin (n+1)) :
    U.polygon ⟶ (string U).obj.obj i :=
  shiftArrow U.polygon (fun k => Fin.partialSum (U.label k) i)
lemma initial_baseArrow (U:Labelled a n) (i:Fin (n+1)) :
    initial U ≫ baseArrow (string U).obj i=vertexArrow U i := by
  change initial U ≫ (inv (initial U) ≫ vertexArrow U i) = _
  simp
lemma vertexArrow_ladder {U V:Labelled a n} (f:U⟶V) (i:Fin (n+1)) :
    vertexArrow U i ≫ (ladder f).hom.app i = f.arrow ≫ vertexArrow V i := by
  rw [←initial_baseArrow,Category.assoc]
  have h := (ladder f).hom.naturality (homOfLE (Fin.zero_le i))
  change baseArrow _ i ≫ (ladder f).hom.app i = (ladder f).hom.app 0 ≫ baseArrow _ i at h
  rw [h,ladder_zero]
  simp only [initialArrow,Category.assoc,IsIso.hom_inv_id_assoc,←initial_baseArrow]
lemma ladder_app {U V:Labelled a n} (f:U⟶V) (i:Fin (n+1)) :
    (ladder f).hom.app i = inv (vertexArrow U i) ≫ f.arrow ≫ vertexArrow V i := by
  apply (cancel_epi (vertexArrow U i)).mp
  rw [vertexArrow_ladder]
  simp
lemma trajectoryShift_vertex (U:Labelled a n) (x:U.polygon.Point) (i:Fin (n+1)) :
    trajectoryShift (string U).obj ((initial U).toEquiv x) i = Fin.partialSum (U.label x.val.1) i := by
  change trajectoryShift (translationString U.polygon (fun j k => Fin.partialSum (U.label k) j))
    ((shiftArrow U.polygon (fun k => Fin.partialSum (U.label k) 0)).toEquiv x) i = _
  rw [trajectoryShift_translationString]
  simp only [Fin.partialSum_zero,sub_zero]
  exact representative_partialSum _ (U.reduced _) i
lemma increments_vertex_reindex (U:Labelled a n) (u : Fin (m+1) ⥤ Fin (n+1))
    (x:U.polygon.Point) :
    increments (u ⋙ (string U).obj) ((vertexArrow U (u.obj 0)).toEquiv x) =
      reindexLabel u (U.label x.val.1) := by
  funext i
  rw [←initial_baseArrow,arrow_comp_apply,increments_reindex,
    trajectoryShift_vertex,trajectoryShift_vertex]
  rfl
end

section
variable {a n m:ℕ} (u:Fin (m+1) ⥤ Fin (n+1))
noncomputable def reindexFunctor : Labelled a n ⥤ Labelled a m :=
  translateFunctor (initialDisplacement u) ⋙ relabel (reindexLabel u) (reindexLabel_reduced u)
lemma reindexFunctor_arrow {U V:Labelled a n} (f: U⟶V) :
    ((reindexFunctor u).map f).arrow =
      inv (vertexArrow U (u.obj 0)) ≫ f.arrow ≫ vertexArrow V (u.obj 0) := rfl
noncomputable abbrev reindexInitial (U:Labelled a n) :
    (string ((reindexFunctor u).obj U)).obj.obj 0 ⟶ (string U).obj.obj (u.obj 0) :=
  inv (X := ((reindexFunctor u).obj U).polygon)
    (Y := (string ((reindexFunctor u).obj U)).obj.obj 0) (initial ((reindexFunctor u).obj U))
lemma reindexInitial_positional (U:Labelled a n) : Positional (reindexInitial u U) :=
  positional_inv (incrementInitial_positional _ _)
lemma reindexInitial_labels (U:Labelled a n)
    (x:((string ((reindexFunctor u).obj U)).obj.obj 0).Point) :
    increments (u ⋙ (string U).obj) ((reindexInitial u U).toEquiv x) =
      increments (string ((reindexFunctor u).obj U)).obj x := by
  obtain ⟨y,rfl⟩ := (initial ((reindexFunctor u).obj U)).toEquiv.surjective x
  rw [incrementString_spec_reduced _ _ ((reindexFunctor u).obj U).reduced]
  have h : (reindexInitial u U).toEquiv ((initial ((reindexFunctor u).obj U)).toEquiv y)=y := by
    erw [inv_arrow_apply]
    exact Equiv.symm_apply_apply _ _
  rw [h]
  obtain ⟨z,rfl⟩ := (vertexArrow U (u.obj 0)).toEquiv.surjective y
  exact increments_vertex_reindex U u z
noncomputable def reindexLadder (U:Labelled a n) :
    string ((reindexFunctor u).obj U) ⟶ (stringReindex u).obj (string U) :=
  ⟨extendLadder (reindexInitial u U),extendLadder_positional_of_increments _
    (reindexInitial_positional u U) (reindexInitial_labels u U)⟩
@[simp] lemma reindexLadder_zero (U:Labelled a n) :
    (reindexLadder u U).hom.app 0=reindexInitial u U := extendLadder_zero _

noncomputable def reindexStringIso : reindexFunctor (a:=a) u ⋙ toStrings ≅
    toStrings ⋙ stringReindex u :=
  NatIso.ofComponents (fun U => @asIso (StringGroupoid a m) _ _ _ (reindexLadder u U)
    (IsIso.of_groupoid (C := StringGroupoid a m) _)) (by
    intro U V f
    apply WideSubcategory.hom_ext
    apply ladder_ext
    change (ladder ((reindexFunctor u).map f)).hom.app 0 ≫ (reindexLadder u V).hom.app 0 =
      (reindexLadder u U).hom.app 0 ≫ (ladder f).hom.app (u.obj 0)
    rw [reindexLadder_zero,reindexLadder_zero,ladder_zero,ladder_app]
    simp only [initialArrow,reindexInitial,reindexFunctor_arrow]
    exact @comp_inv_last _ _ _ _ _ _ _ _ _
      (IsIso.of_groupoid (C := PolygonObject a) _))
end

variable {a n m:ℕ}
lemma tensorLadder_vertex (U V:Labelled a n) (i:Fin (n+1)) :
    sumArrow (vertexArrow U i) (vertexArrow V i) ≫ (tensorLadder U V).hom.app i =
      vertexArrow (U⊗V) i := by
  have h := (tensorLadder U V).hom.naturality (homOfLE (Fin.zero_le i))
  change sumArrow (baseArrow (string U).obj i) (baseArrow (string V).obj i) ≫
    (tensorLadder U V).hom.app i = (tensorLadder U V).hom.app 0 ≫ baseArrow (string (U⊗V)).obj i at h
  rw [tensorLadder_zero] at h
  erw [←initial_baseArrow,←initial_baseArrow,sumArrow_comp,Category.assoc,h]
  change sumArrow (initial U) (initial V) ≫
    (inv (sumArrow (initial U) (initial V)) ≫ initial (U⊗V)) ≫ baseArrow _ i = _
  simp only [Category.assoc,IsIso.hom_inv_id_assoc]
  exact initial_baseArrow _ _
lemma tensorLadder_app (U V:Labelled a n) (i:Fin (n+1)) :
    (tensorLadder U V).hom.app i =
      inv (sumArrow (vertexArrow U i) (vertexArrow V i)) ≫ vertexArrow (U⊗V) i := by
  apply (cancel_epi (sumArrow (vertexArrow U i) (vertexArrow V i))).mp
  rw [tensorLadder_vertex,IsIso.hom_inv_id_assoc]
variable (u:Fin (m+1) ⥤ Fin (n+1))
noncomputable instance reindexMonoidal : (reindexFunctor (a:=a) u).Monoidal := by
  unfold reindexFunctor; infer_instance
noncomputable instance reindexBraided : (reindexFunctor (a:=a) u).Braided := by
  unfold reindexFunctor; infer_instance
lemma reindex_μ_arrow (U V:Labelled a n) :
    (Functor.LaxMonoidal.μ (reindexFunctor u) U V).arrow =
      inv (sumArrow (vertexArrow U (u.obj 0)) (vertexArrow V (u.obj 0))) ≫ vertexArrow (U⊗V) (u.obj 0) := by
  change (Functor.LaxMonoidal.μ
    (translateFunctor (initialDisplacement u) ⋙ relabel (reindexLabel u) (reindexLabel_reduced u)) U V).arrow = _
  rw [Functor.LaxMonoidal.comp_μ]
  change (𝟙 _) ≫ (translationTensor (initialDisplacement u) U V).arrow = _
  rw [Category.id_comp]
  rfl
noncomputable instance reindexStringMonoidal : NatTrans.IsMonoidal (reindexStringIso (a:=a) u).hom where
  unit := by
    apply WideSubcategory.hom_ext
    apply ladder_ext
    apply Arrow.ext
    apply Equiv.ext
    intro x
    change Point PolygonObject.empty at x
    exact isEmptyElim x
  tensor U V := by
    apply WideSubcategory.hom_ext
    apply ladder_ext
    change ((Functor.LaxMonoidal.μ (reindexFunctor u ⋙ toStrings) U V).hom.app 0) ≫
      (reindexLadder u (U⊗V)).hom.app 0 =
      sumArrow ((reindexLadder u U).hom.app 0) ((reindexLadder u V).hom.app 0) ≫
        ((Functor.LaxMonoidal.μ (toStrings ⋙ stringReindex u) U V).hom.app 0)
    rw [Functor.LaxMonoidal.comp_μ,Functor.LaxMonoidal.comp_μ]
    change (tensorLadder ((reindexFunctor u).obj U) ((reindexFunctor u).obj V)).hom.app 0 ≫
      (ladder (Functor.LaxMonoidal.μ (reindexFunctor u) U V)).hom.app 0 ≫
      (reindexLadder u (U⊗V)).hom.app 0 =
      sumArrow ((reindexLadder u U).hom.app 0) ((reindexLadder u V).hom.app 0) ≫
        (𝟙 _ ≫ (tensorLadder U V).hom.app (u.obj 0))
    erw [tensorLadder_zero,ladder_zero,reindexLadder_zero,reindexLadder_zero,reindexLadder_zero,
      Category.id_comp,tensorLadder_app]
    simp only [tensorInitial,initialArrow,reindexInitial,Category.assoc,reindex_μ_arrow]
    congr 1
    · apply (cancel_epi (sumArrow (initial ((reindexFunctor u).obj U)) (initial ((reindexFunctor u).obj V)))).mp
      erw [IsIso.hom_inv_id]
      change 𝟙 _ = (_ ⊗ₘ _) ≫ (_ ⊗ₘ _)
      rw [tensorHom_comp_tensorHom]
      simp
    · exact @cancel_two_inverses _ _ _ _ _ _ _ _ _
        (IsIso.of_groupoid (C := PolygonObject a) _)
        (IsIso.of_groupoid (C := PolygonObject a) _)
end SimpleAmenable.PolygonObject.Labelled

end OAI
end


