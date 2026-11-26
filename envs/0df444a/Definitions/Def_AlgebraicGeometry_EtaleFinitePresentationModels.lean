-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleFinitePresentationModels
-- name    : AlgebraicGeometry_EtaleFinitePresentationModels
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T00:06:55.195493+00:00
-- url     : https://prove2.me/theorems/f1348e55-67ca-4a0a-a812-8366c1a5f350
-- title:
--   Finite presentations of annihilated étale coefficient sheaves
-- statement:
--   A sheaf killed by an integer is a filtered colimit of sheafifications of finite module presheaf presentations.
-- source:
--   Stacks Project, 59.73.2 (https://stacks.math.columbia.edu/tag/03SA) and 59.74.4 (https://stacks.math.columbia.edu/tag/09Z7).

import Definitions.Def_AlgebraicGeometry_FiniteModulePresheafPresentations
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.LinearAlgebra.Finsupp.Pi

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleBoundedFiniteModelReduction (boundedFiniteModel)
open PhilipponEtaleFiniteConstantColimits (finiteConstant finiteCoefficients)
open PhilipponEtaleFiniteFieldModels (finiteFieldModel affineChart_finiteFieldModel)
open PhilipponEtaleRelativeCoefficients (boundedTorsionModule boundedTorsionModule_forget)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponFiniteModulePresheafPresentation (finitePresentations ind_finitePresentations)
open PhilipponFreeYonedaMaps (mapFreeYoneda ι_mapFreeYoneda_app ι_mapFreeYoneda_app_assoc
  homEquiv_mapFreeYoneda_comp)
open PhilipponFreeEtaleSplitChart (splitChart exists_finite_constant_of_split)


namespace PhilipponEtaleFinitePresentations

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev SmallAffine (X : Scheme.{u}) := SmallModel.{u} X.AffineEtale

abbrev smallTopology (X : Scheme.{u}) :=
  (equivSmallModel.{u} X.AffineEtale).inverse.inducedTopology (Scheme.AffineEtale.topology X)

def restrictEquivalence (X : Scheme.{u}) :
    Ab X ≌ Sheaf (smallTopology X) AddCommGrpCat.{u} :=
  ((Scheme.AffineEtale.Spec X).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Scheme.AffineEtale.topology X) X.smallEtaleTopology).asEquivalence.trans
      ((equivSmallModel.{u} X.AffineEtale).sheafCongr (Scheme.AffineEtale.topology X)
        (smallTopology X) AddCommGrpCat.{u})

private abbrev R (N : ℕ) := ULift.{u} (ZMod N)

abbrev forgetCoefficients (X : Scheme.{u}) (N : ℕ) :
    ((SmallAffine X)ᵒᵖ ⥤ ModuleCat.{u} (R.{u} N)) ⥤ ((SmallAffine X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u} (R.{u} N)) AddCommGrpCat.{u})

def modelSheaf (X : Scheme.{u}) (N : ℕ) :
    ((SmallAffine X)ᵒᵖ ⥤ ModuleCat.{u} (R.{u} N)) ⥤ Ab X :=
  forgetCoefficients X N ⋙ presheafToSheaf (smallTopology X) AddCommGrpCat.{u} ⋙
    (restrictEquivalence X).inverse

abbrev affineChartFunctor (X : Scheme.{u}) : SmallAffine X ⥤ X.Etale :=
  (equivSmallModel.{u} X.AffineEtale).inverse ⋙ Scheme.AffineEtale.Spec X

private abbrev affineChart (X : Scheme.{u}) (U : SmallAffine X) : X.Etale :=
  (affineChartFunctor X).obj U

abbrev abCoefficients (N : ℕ) :=
  forget₂ (ModuleCat.{u} (R.{u} N)) AddCommGrpCat.{u}

/-- The underlying abelian group of the free rank-one coefficient module. -/
abbrev generatorCoefficients (N : ℕ) : AddCommGrpCat.{u} :=
  (abCoefficients N).obj ((ModuleCat.free.{u} (R.{u} N)).obj PUnit.{u + 1})

theorem generatorCoefficients_finite (N : ℕ) (hN : N ≠ 0) :
    finiteCoefficients N (generatorCoefficients.{u} N) := by
  let : NeZero N := ⟨hN⟩
  refine ⟨Finite.of_injective _ (Finsupp.uniqueLinearEquiv (R.{u} N) (R.{u} N)
    (PUnit.unit : PUnit.{u + 1})).injective, ?_⟩
  apply ConcreteCategory.hom_ext
  intro a
  let a' : PUnit.{u + 1} →₀ R.{u} N := a
  have h : N • a' = 0 := by
    have hz : (N : R.{u} N) = 0 := by
      apply ULift.ext
      exact ZMod.natCast_self N
    rw [← Nat.cast_smul_eq_nsmul (R.{u} N) N a', hz, zero_smul]
  exact h

private def forgetFreeYonedaIso (X : Scheme.{u}) (N : ℕ) (U : SmallAffine X)
    (M : ModuleCat.{u} (R.{u} N)) :
    Presheaf.freeYoneda U ((abCoefficients N).obj M) ≅
      (forgetCoefficients X N).obj (Presheaf.freeYoneda U M) := by
  let G := abCoefficients N
  let c (V : (SmallAffine X)ᵒᵖ) :=
    sigmaComparison G (fun _ : (yoneda.obj U).obj V => M)
  refine NatIso.ofComponents (fun V => asIso (c V)) ?_
  intro V W f
  apply Sigma.hom_ext
  intro b
  change Sigma.ι _ b ≫ Sigma.map' ((yoneda.obj U).map f) (fun _ => 𝟙 (G.obj M)) ≫ c W =
    Sigma.ι _ b ≫ c V ≫ G.map (Sigma.map' ((yoneda.obj U).map f) (fun _ => 𝟙 M))
  simp only [c, Sigma.ι_comp_map'_assoc, Category.id_comp, ι_comp_sigmaComparison_assoc,
    ι_comp_sigmaComparison, ← G.map_comp, Sigma.ι_comp_map']

private theorem forgetFreeYonedaIso_naturality (X : Scheme.{u}) (N : ℕ)
    {U V : SmallAffine X} {M P : ModuleCat.{u} (R.{u} N)} (a : U ⟶ V) (m : M ⟶ P) :
    mapFreeYoneda a ((abCoefficients N).map m) ≫ (forgetFreeYonedaIso X N V P).hom =
      (forgetFreeYonedaIso X N U M).hom ≫ (forgetCoefficients X N).map (mapFreeYoneda a m) := by
  apply NatTrans.ext
  funext W
  obtain ⟨W⟩ := W
  apply Sigma.hom_ext
  intro b
  let G := abCoefficients N
  let c (T : SmallAffine X) (Q : ModuleCat.{u} (R.{u} N)) :=
    sigmaComparison G (fun _ : (yoneda.obj T).obj (op W) => Q)
  change Sigma.ι (fun _ : (yoneda.obj U).obj (op W) => G.obj M) b ≫
    (mapFreeYoneda a (G.map m)).app (op W) ≫ c V P =
    Sigma.ι (fun _ : (yoneda.obj U).obj (op W) => G.obj M) b ≫
      c U M ≫ G.map ((mapFreeYoneda a m).app (op W))
  simp only [c, ι_mapFreeYoneda_app_assoc, ι_comp_sigmaComparison_assoc, ι_comp_sigmaComparison,
    ← G.map_comp, ι_mapFreeYoneda_app]

private def modelSheafHomEquiv (X : Scheme.{u}) (N : ℕ)
    (P : (SmallAffine X)ᵒᵖ ⥤ ModuleCat.{u} (R.{u} N)) (F : Ab X) :
    ((modelSheaf X N).obj P ⟶ F) ≃ ((forgetCoefficients X N).obj P ⟶
      ((restrictEquivalence X).functor.obj F).obj) :=
  let Q := (forgetCoefficients X N).obj P
  let A := (restrictEquivalence X).symm.toAdjunction
  let L := presheafToSheaf (smallTopology X) AddCommGrpCat.{u}
  let B := sheafificationAdjunction (smallTopology X) AddCommGrpCat.{u}
  (A.homEquiv (L.obj Q) F).trans (B.homEquiv Q ((restrictEquivalence X).functor.obj F))

private def modelSheafFreeYonedaHomEquiv (X : Scheme.{u}) (N : ℕ) (U : SmallAffine X)
    (M : ModuleCat.{u} (R.{u} N)) (F : Ab X) :
    ((modelSheaf X N).obj (Presheaf.freeYoneda U M) ⟶ F) ≃
      ((abCoefficients N).obj M ⟶ F.obj.obj (op (affineChart X U))) :=
  ((modelSheafHomEquiv X N (Presheaf.freeYoneda U M) F).trans
    (Iso.homCongr (forgetFreeYonedaIso X N U M).symm (Iso.refl _))).trans
      Presheaf.freeYonedaHomEquiv

private theorem modelSheafFreeYonedaHomEquiv_comp (X : Scheme.{u}) (N : ℕ)
    (U : SmallAffine X) (M : ModuleCat.{u} (R.{u} N)) {F H : Ab X}
    (k : (modelSheaf X N).obj (Presheaf.freeYoneda U M) ⟶ F) (a : F ⟶ H) :
    modelSheafFreeYonedaHomEquiv X N U M H (k ≫ a) =
      modelSheafFreeYonedaHomEquiv X N U M F k ≫ a.hom.app (op (affineChart X U)) := by
  let E := restrictEquivalence X
  let A := E.symm.toAdjunction
  let B := sheafificationAdjunction (smallTopology X) AddCommGrpCat.{u}
  let ψ (G : Ab X) := modelSheafHomEquiv X N (Presheaf.freeYoneda U M) G
  have hp : ψ H (k ≫ a) = ψ F k ≫ (E.functor.map a).hom := by
    dsimp only [ψ, modelSheafHomEquiv, Equiv.trans_apply]
    erw [A.homEquiv_naturality_right k a, B.homEquiv_naturality_right _ (E.functor.map a)]
    rfl
  let b := (forgetFreeYonedaIso X N U M).hom
  change Presheaf.freeYonedaHomEquiv (b ≫ ψ H (k ≫ a) ≫ 𝟙 _) =
    Presheaf.freeYonedaHomEquiv (b ≫ ψ F k ≫ 𝟙 _) ≫ (E.functor.map a).hom.app (op U)
  rw [Category.comp_id, Category.comp_id, hp, ← Category.assoc]
  exact Presheaf.freeYonedaHomEquiv_comp _ _

def modelSheafFreeYonedaIso (X : Scheme.{u}) (N : ℕ) (U : SmallAffine X)
    (M : ModuleCat.{u} (R.{u} N)) :
    (modelSheaf X N).obj (Presheaf.freeYoneda U M) ≅
      PhilipponFreeEtaleSheaf.freeSheaf (affineChart X U) ((abCoefficients N).obj M) := by
  let P := (modelSheaf X N).obj (Presheaf.freeYoneda U M)
  let V := affineChart X U
  let T := (abCoefficients N).obj M
  let Q := PhilipponFreeEtaleSheaf.freeSheaf V T
  let α := modelSheafFreeYonedaHomEquiv X N U M
  let β := PhilipponFreeEtaleSheaf.homEquiv V T
  let u : P ⟶ Q := (α Q).symm (β Q (𝟙 Q))
  let v : Q ⟶ P := (β P).symm (α P (𝟙 P))
  have hu : α Q u = β Q (𝟙 Q) := Equiv.apply_symm_apply _ _
  have hv : β P v = α P (𝟙 P) := Equiv.apply_symm_apply _ _
  refine ⟨u, v, (α P).injective ?_, (β Q).injective ?_⟩
  · change modelSheafFreeYonedaHomEquiv X N U M P (u ≫ v) = α P (𝟙 P)
    rw [modelSheafFreeYonedaHomEquiv_comp, show modelSheafFreeYonedaHomEquiv X N U M Q u = _ from hu]
    exact (PhilipponFreeEtaleSheaf.homEquiv_comp V T (𝟙 Q) v).symm.trans
      ((congrArg (β P) (Category.id_comp v)).trans hv)
  · change PhilipponFreeEtaleSheaf.homEquiv V T Q (v ≫ u) = β Q (𝟙 Q)
    rw [PhilipponFreeEtaleSheaf.homEquiv_comp, show PhilipponFreeEtaleSheaf.homEquiv V T P v = _ from hv]
    exact (modelSheafFreeYonedaHomEquiv_comp X N U M (𝟙 P) u).symm.trans
      ((congrArg (α Q) (Category.id_comp u)).trans hu)

private theorem modelSheafFreeYonedaHomEquiv_precomp (X : Scheme.{u}) (N : ℕ)
    {U V : SmallAffine X} {M P : ModuleCat.{u} (R.{u} N)} (a : U ⟶ V) (m : M ⟶ P)
    {F : Ab X} (k : (modelSheaf X N).obj (Presheaf.freeYoneda V P) ⟶ F) :
    modelSheafFreeYonedaHomEquiv X N U M F ((modelSheaf X N).map (mapFreeYoneda a m) ≫ k) =
      (abCoefficients N).map m ≫ modelSheafFreeYonedaHomEquiv X N V P F k ≫
        F.obj.map (((equivSmallModel.{u} X.AffineEtale).inverse ⋙ Scheme.AffineEtale.Spec X).map a).op := by
  let E := restrictEquivalence X
  let A := E.symm.toAdjunction
  let B := sheafificationAdjunction (smallTopology X) AddCommGrpCat.{u}
  let L := presheafToSheaf (smallTopology X) AddCommGrpCat.{u}
  let φ := mapFreeYoneda a m
  let ψ {G : (SmallAffine X)ᵒᵖ ⥤ ModuleCat.{u} (R.{u} N)} := modelSheafHomEquiv X N G F
  have hp : ψ ((modelSheaf X N).map φ ≫ k) = (forgetCoefficients X N).map φ ≫ ψ k := by
    dsimp only [ψ, modelSheafHomEquiv, Equiv.trans_apply]
    change B.homEquiv _ _ (A.homEquiv _ _
        (E.symm.functor.map (L.map ((forgetCoefficients X N).map φ)) ≫ k)) = _
    erw [A.homEquiv_naturality_left (L.map ((forgetCoefficients X N).map φ)) k,
      B.homEquiv_naturality_left]
    rfl
  let u := (forgetFreeYonedaIso X N U M).hom
  let v := (forgetFreeYonedaIso X N V P).hom
  let g := mapFreeYoneda a ((abCoefficients N).map m)
  have hcv : g ≫ v = u ≫ (forgetCoefficients X N).map φ :=
    forgetFreeYonedaIso_naturality X N a m
  change Presheaf.freeYonedaHomEquiv (u ≫ ψ ((modelSheaf X N).map φ ≫ k) ≫ 𝟙 _) =
    (abCoefficients N).map m ≫ Presheaf.freeYonedaHomEquiv (v ≫ ψ k ≫ 𝟙 _) ≫ _
  rw [Category.comp_id, Category.comp_id, hp, ← Category.assoc u, ← hcv, Category.assoc]
  exact homEquiv_mapFreeYoneda_comp a _ _

private theorem modelSheafFreeYonedaHomEquiv_iso_comp (X : Scheme.{u}) (N : ℕ)
    (U : SmallAffine X) (M : ModuleCat.{u} (R.{u} N)) {F : Ab X}
    (k : PhilipponFreeEtaleSheaf.freeSheaf (affineChart X U) ((abCoefficients N).obj M) ⟶ F) :
    modelSheafFreeYonedaHomEquiv X N U M F ((modelSheafFreeYonedaIso X N U M).hom ≫ k) =
      PhilipponFreeEtaleSheaf.homEquiv (affineChart X U) ((abCoefficients N).obj M) F k := by
  rw [modelSheafFreeYonedaHomEquiv_comp]
  change modelSheafFreeYonedaHomEquiv X N U M _
      ((modelSheafFreeYonedaHomEquiv X N U M _).symm
        (PhilipponFreeEtaleSheaf.homEquiv _ _ _ (𝟙 _))) ≫ k.hom.app _ = _
  rw [Equiv.apply_symm_apply, ← PhilipponFreeEtaleSheaf.homEquiv_comp, Category.id_comp]

theorem modelSheafFreeYonedaIso_naturality (X : Scheme.{u}) (N : ℕ)
    {U V : SmallAffine X} {M P : ModuleCat.{u} (R.{u} N)} (a : U ⟶ V) (m : M ⟶ P) :
    (modelSheaf X N).map (mapFreeYoneda a m) ≫ (modelSheafFreeYonedaIso X N V P).hom =
      (modelSheafFreeYonedaIso X N U M).hom ≫ PhilipponFreeEtaleSheaf.mapFreeSheaf
        (((equivSmallModel.{u} X.AffineEtale).inverse ⋙ Scheme.AffineEtale.Spec X).map a)
        ((abCoefficients N).map m) := by
  apply (modelSheafFreeYonedaHomEquiv X N U M _).injective
  rw [modelSheafFreeYonedaHomEquiv_precomp, modelSheafFreeYonedaHomEquiv_iso_comp,
    ← Category.comp_id (modelSheafFreeYonedaIso X N V P).hom, modelSheafFreeYonedaHomEquiv_iso_comp]
  rw [← Category.comp_id (PhilipponFreeEtaleSheaf.mapFreeSheaf _ _),
    PhilipponFreeEtaleSheaf.homEquiv_mapFreeSheaf_comp]

/-- Sheafifications of the finite-colimit closure of free affine étale
representables with coefficient ring ℤ/Nℤ, viewed as abelian sheaves. -/
def finiteEtalePresentations (X : Scheme.{u}) (N : ℕ) : ObjectProperty (Ab X) :=
  (finitePresentations (R.{u} N) (SmallAffine X)).map (modelSheaf X N)

/-- A property closed under finite colimits and containing the free affine
étale generators contains every sheafified finite presentation. -/
theorem finiteEtalePresentations_le (X : Scheme.{u}) (N : ℕ) (Q : ObjectProperty (Ab X))
    [Q.IsClosedUnderIsomorphisms]
    (hQ : ∀ (J : Type u) [SmallCategory J] [Finite J], Q.IsClosedUnderColimitsOfShape J)
    (hGen : ∀ U : SmallModel.{u} X.AffineEtale,
      Q (PhilipponFreeEtaleSheaf.freeSheaf (affineChart X U) (generatorCoefficients N))) :
    finiteEtalePresentations X N ≤ Q := by
  let G := modelSheaf X N
  have h : finitePresentations (R.{u} N) (SmallAffine X) ≤ Q.inverseImage G := by
    unfold finitePresentations
    apply ObjectProperty.colimitsCardinalClosure_le
    · intro J _ hj
      let : Finite (Arrow J) := (hasCardinalLT_aleph0_iff _).mp hj
      let : Finite J := Finite.of_injective (fun j : J => Arrow.mk (𝟙 j))
        (fun _ _ hEq => congrArg Arrow.left hEq)
      let : Q.IsClosedUnderColimitsOfShape J := hQ J
      let : PreservesColimitsOfShape J G := by
        unfold G modelSheaf
        infer_instance
      apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
      rintro _ ⟨F, hF⟩
      exact Q.prop_of_isColimit (isColimitOfPreserves G (colimit.isColimit F)) hF
    · rintro _ ⟨U⟩
      exact Q.prop_of_iso (modelSheafFreeYonedaIso X N U _).symm (hGen U)
  rintro _ ⟨P, hP, ⟨e⟩⟩
  exact Q.prop_of_iso e (h P hP)

/-- An affine étale chart splits after pullback if it becomes a finite
disjoint union of copies of the new base. -/
def chartSplits {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.AffineEtale) : Prop :=
  ∃ (I : Type u) (_ : Finite I),
    Nonempty (splitChart Y I ≅ (baseChange f).obj ((Scheme.AffineEtale.Spec X).obj U))

/-- Every bounded finite presentation has finitely many affine étale charts
whose simultaneous splitting suffices to make the sheaf finite constant. -/
theorem exists_trivializing_charts (X : Scheme.{u}) (N : ℕ) (hN : N ≠ 0) (F : Ab X)
    (hF : finiteEtalePresentations X N F) :
    ∃ s : Finset X.AffineEtale, ∀ (Y : Scheme.{u}) [PreconnectedSpace Y] [Nonempty Y]
      (f : Y ⟶ X), (∀ U ∈ s, chartSplits f U) →
      finiteConstant Y N ((pullbackSheaves f).obj F) := by
  classical
  let Q : ObjectProperty (Ab X) := fun G =>
    ∃ s : Finset X.AffineEtale, ∀ (Y : Scheme.{u}) [PreconnectedSpace Y] [Nonempty Y]
      (f : Y ⟶ X), (∀ U ∈ s, chartSplits f U) →
      finiteConstant Y N ((pullbackSheaves f).obj G)
  let : Q.IsClosedUnderIsomorphisms :=
    ⟨fun e ⟨s, hs⟩ => ⟨s, fun Y _ _ f h =>
      (finiteConstant Y N).prop_of_iso ((pullbackSheaves f).mapIso e) (hs Y f h)⟩⟩
  refine finiteEtalePresentations_le X N Q ?_ ?_ F hF
  · intro J _ _
    let : Fintype J := Fintype.ofFinite J
    apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
    rintro _ ⟨D, hD⟩
    choose s hs using hD
    refine ⟨Finset.univ.biUnion s, fun Y _ _ f h => ?_⟩
    let P := pullbackSheaves f
    let : P.IsLeftAdjoint := (pullbackAdjunction f).isLeftAdjoint
    apply (finiteConstant Y N).prop_of_isColimit (c := P.mapCocone (colimit.cocone D))
      (isColimitOfPreserves P (colimit.isColimit D))
    intro j
    exact hs j Y f fun U hU => h U (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hU⟩)
  · intro U
    let V := (equivSmallModel.{u} X.AffineEtale).inverse.obj U
    refine ⟨{V}, fun Y _ _ f h => ?_⟩
    obtain ⟨I, hI, ⟨e⟩⟩ := h V (Finset.mem_singleton_self V)
    let M := generatorCoefficients.{u} N
    let : Finite M := (generatorCoefficients_finite N hN).1
    let a := PhilipponFreeEtaleSheaf.pullbackFreeSheafIso f (affineChart X U) M
    let b := PhilipponFreeEtaleSheaf.freeSheafIsoOfChartIso e M
    obtain ⟨K, hK, hNK, ⟨c⟩⟩ := exists_finite_constant_of_split Y I M N
      (generatorCoefficients_finite N hN).2
    exact ⟨K, ⟨hK, hNK⟩, ⟨c.symm ≪≫ b ≪≫ a.symm⟩⟩

/-- The restriction of a finite presentation on an affine scheme to a
field-valued point becomes finite constant over a finite separable extension. -/
theorem finiteFieldModel_pullback (X : Scheme.{u}) [IsAffine X] (K : Type u) [Field K]
    (f : Spec (.of K) ⟶ X) (N : ℕ) (hN : N ≠ 0) (F : Ab X)
    (hF : finiteEtalePresentations X N F) :
    finiteFieldModel K N ((pullbackSheaves f).obj F) := by
  let G := pullbackSheaves f
  let P := finiteFieldModel K N
  let : G.IsLeftAdjoint := (pullbackAdjunction f).isLeftAdjoint
  refine finiteEtalePresentations_le X N (P.inverseImage G) ?_ ?_ F hF
  · intro J _ _
    let : P.IsClosedUnderColimitsOfShape J :=
      inferInstanceAs ((finiteFieldModel K N).IsClosedUnderColimitsOfShape J)
    apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
    rintro _ ⟨D, hD⟩
    change P (G.obj (colimit D))
    exact P.prop_of_isColimit (c := G.mapCocone (colimit.cocone D))
      (isColimitOfPreserves G (colimit.isColimit D)) hD
  · intro U
    let V := affineChart X U
    let T := generatorCoefficients.{u} N
    let : Finite T := (generatorCoefficients_finite N hN).1
    have hV : IsAffine V.left := inferInstanceAs (IsAffine (Spec _))
    let : IsAffine ((baseChange f).obj V).left :=
      @Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine V.left (Spec (.of K)) X
        V.hom f hV inferInstance ‹IsAffine X›
    exact P.prop_of_iso (PhilipponFreeEtaleSheaf.pullbackFreeSheafIso f V T).symm
      (affineChart_finiteFieldModel K ((baseChange f).obj V) T N (generatorCoefficients_finite N hN).2)

/-- A bounded-torsion sheaf on the small étale site is a filtered colimit
of the corresponding sheafifications of finite presheaf presentations. -/
theorem ind_finiteEtalePresentations (X : Scheme.{u}) (N : ℕ) (F : Ab X)
    (h : N • 𝟙 F = 0) :
    ObjectProperty.ind.{u} (finiteEtalePresentations X N) F := by
  let P := boundedTorsionModule N F h
  let a := (equivSmallModel.{u} X.AffineEtale).inverse ⋙ Scheme.AffineEtale.Spec X
  let r : R.{u} N →+* ZMod N := ULift.ringEquiv.toRingHom
  let Q := a.op ⋙ P.obj ⋙ ModuleCat.restrictScalars.{u} r
  let F₀ := (restrictEquivalence X).functor.obj F
  have hQ : (forgetCoefficients X N).obj Q = F₀.obj := by
    change a.op ⋙ (P.obj ⋙ forget₂ (ModuleCat.{u} (ZMod N)) AddCommGrpCat.{u}) = a.op ⋙ F.obj
    rw [boundedTorsionModule_forget]
  let L := presheafToSheaf (smallTopology X) AddCommGrpCat.{u}
  let e : (modelSheaf X N).obj Q ≅ F :=
    (restrictEquivalence X).inverse.mapIso (L.mapIso (eqToIso hQ) ≪≫ (sheafificationIso F₀).symm) ≪≫
      (restrictEquivalence X).unitIso.symm.app F
  obtain ⟨J, _, _, p, hp⟩ := ind_finitePresentations (R.{u} N) (SmallAffine X) Q
  let : PreservesColimitsOfShape J (modelSheaf X N) := by
    unfold modelSheaf
    infer_instance
  exact ⟨J, inferInstance, inferInstance, (p.map (modelSheaf X N)).ofIso e,
    fun i => (finitePresentations (R.{u} N) (SmallAffine X)).prop_map_obj (modelSheaf X N) (hp i)⟩

/-- It suffices to embed the sheafified finite presentations in finite
constant direct images to obtain a bounded model presentation of every
sheaf annihilated by the coefficient bound. -/
theorem ind_boundedFiniteModel_of_finitePresentations (X : Scheme.{u}) (N : ℕ) (F : Ab X)
    (h : N • 𝟙 F = 0) (hModel : finiteEtalePresentations X N ≤ boundedFiniteModel X N) :
    ObjectProperty.ind.{u} (boundedFiniteModel X N) F := by
  obtain ⟨J, _, _, p, hp⟩ := ind_finiteEtalePresentations X N F h
  exact ⟨J, inferInstance, inferInstance, p, fun i => hModel _ (hp i)⟩

end PhilipponEtaleFinitePresentations

end

end


