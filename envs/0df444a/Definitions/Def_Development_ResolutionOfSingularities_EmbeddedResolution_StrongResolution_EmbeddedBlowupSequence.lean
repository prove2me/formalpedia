-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedBlowupSequence
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedBlowupSequence
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T12:55:16.542799+00:00
-- url     : https://prove2.me/theorems/fc875e02-cb79-49aa-bf08-7fd262795192
-- title:
--   Embedded Blowup Sequence
-- statement:
--   Definitions and structural lemmas for Embedded Blowup Sequence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/EmbeddedBlowupSequence.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_RemoveIsoBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_EmbeddedResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FunctorialPrincipalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedStrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Theorems.Thm_FunctorialResolution_Blowup_comap_le_strictTransform

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
structure EmbeddedBlowupSequence (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [AlgebraicGeometry.IsAffine Y] (pY : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pY] : Type (u + 1) where
  ambient : Scheme.{u}
  ambientStruct : ambient ⟶ Spec (CommRingCat.of k)
  isAffine_ambient : AlgebraicGeometry.IsAffine ambient
  smooth_ambientStruct : AlgebraicGeometry.Smooth ambientStruct
  locallyOfFiniteType_ambientStruct : AlgebraicGeometry.LocallyOfFiniteType ambientStruct
  quasiCompact_ambientStruct : AlgebraicGeometry.QuasiCompact ambientStruct
  emb : Y ⟶ ambient
  isClosedImmersion_emb : AlgebraicGeometry.IsClosedImmersion emb
  emb_comp : emb ≫ ambientStruct = pY
  ambientSeq : SequenceOfBlowups ambient
namespace EmbeddedBlowupSequence
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
instance instIsAffineAmbient (T : EmbeddedBlowupSequence k Y pY) :
    AlgebraicGeometry.IsAffine T.ambient := T.isAffine_ambient
instance instSmoothAmbientStruct (T : EmbeddedBlowupSequence k Y pY) :
    AlgebraicGeometry.Smooth T.ambientStruct := T.smooth_ambientStruct
instance instLocallyOfFiniteTypeAmbientStruct (T : EmbeddedBlowupSequence k Y pY) :
    AlgebraicGeometry.LocallyOfFiniteType T.ambientStruct :=
  T.locallyOfFiniteType_ambientStruct
instance instQuasiCompactAmbientStruct (T : EmbeddedBlowupSequence k Y pY) :
    AlgebraicGeometry.QuasiCompact T.ambientStruct := T.quasiCompact_ambientStruct
instance instIsClosedImmersionEmb (T : EmbeddedBlowupSequence k Y pY) :
    AlgebraicGeometry.IsClosedImmersion T.emb := T.isClosedImmersion_emb
variable (T : EmbeddedBlowupSequence k Y pY)
abbrev length : ℕ := T.ambientSeq.length
abbrev schemeAt (i : ℕ) : Scheme.{u} := T.ambientSeq.schemeAt i
abbrev blowdown (i : ℕ) : T.schemeAt (i + 1) ⟶ T.schemeAt i := T.ambientSeq.transitionMapSucc i
abbrev ambientCenter (i : ℕ) : (T.schemeAt i).IdealSheafData := T.ambientSeq.center i
def strictTransformIdeal (i : ℕ) : (T.schemeAt i).IdealSheafData :=
  Nat.rec (motive := fun j => (T.schemeAt j).IdealSheafData)
    (Scheme.Hom.ker (T.emb ≫ T.ambientSeq.isoZero.inv))
    (fun j ih => Blowup.strictTransform (T.blowdown j) (T.ambientCenter j) ih) i
abbrev strictTransform (i : ℕ) : Scheme.{u} := (T.strictTransformIdeal i).subscheme
abbrev strictTransformι (i : ℕ) : T.strictTransform i ⟶ T.schemeAt i := (T.strictTransformIdeal i).subschemeι
theorem comap_strictTransformIdeal_le (i : ℕ) :
    (T.strictTransformIdeal i).comap (T.blowdown i) ≤ T.strictTransformIdeal (i + 1) :=
  Blowup.comap_le_strictTransform _ _ _
theorem exists_strictTransformMap (i : ℕ) :
    ∃ f : T.strictTransform (i + 1) ⟶ T.strictTransform i,
      f ≫ T.strictTransformι i = T.strictTransformι (i + 1) ≫ T.blowdown i := by
  have hle : T.strictTransformIdeal i ≤ (T.strictTransformIdeal (i + 1)).map (T.blowdown i) :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr (T.comap_strictTransformIdeal_le i)
  exact ⟨(T.strictTransformIdeal (i + 1)).subschemeMap (T.strictTransformIdeal i) (T.blowdown i) hle,
    Scheme.IdealSheafData.subschemeMap_subschemeι (T.strictTransformIdeal (i + 1)) (T.strictTransformIdeal i)
      (T.blowdown i) hle⟩
def strictTransformMap (i : ℕ) : T.strictTransform (i + 1) ⟶ T.strictTransform i := (T.exists_strictTransformMap i).choose
def detachedComponents (i : ℕ) : Set (Set ↥(T.strictTransform i)) :=
  {C | C ∈ irreducibleComponents ↥(T.strictTransform i) ∧
    (T.strictTransformι i).base '' C ⊆ ((T.ambientCenter i).support : Set ↥(T.schemeAt i))}
def detachedLocus (i : ℕ) : Set ↥(T.strictTransform i) := ⋃₀ (T.detachedComponents i)
def detachedClosure (i : ℕ) : TopologicalSpace.Closeds ↥(T.strictTransform i) :=
  ⟨closure (T.detachedLocus i), isClosed_closure⟩
def detachedIdeal (i : ℕ) : (T.strictTransform i).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (T.detachedClosure i)
abbrev detachedScheme (i : ℕ) : Scheme.{u} := (T.detachedIdeal i).subscheme
abbrev detachedι (i : ℕ) : T.detachedScheme i ⟶ T.strictTransform i := (T.detachedIdeal i).subschemeι
def detachedClosureCompl (i : ℕ) : (T.strictTransform i).Opens := (T.detachedClosure i).compl
def comapAmbientCenter (i : ℕ) : (T.strictTransform i).IdealSheafData :=
  (T.ambientCenter i).comap (T.strictTransformι i)
def centerOffDetached (i : ℕ) : (T.strictTransform i).IdealSheafData :=
  Scheme.Hom.ker
    (((T.comapAmbientCenter i).comap (T.detachedClosureCompl i).ι).subschemeι ≫ (T.detachedClosureCompl i).ι)
def detachedCoprod (i : ℕ) : Scheme.{u} :=
  Nat.rec (motive := fun _ => Scheme.{u}) (⊥_ Scheme.{u})
    (fun j ih => ih ⨿ T.detachedScheme j) i
abbrev totalSpace (i : ℕ) : Scheme.{u} := T.strictTransform i ⨿ T.detachedCoprod i
def totalTransition (i : ℕ) : T.totalSpace (i + 1) ⟶ T.totalSpace i :=
  coprod.desc (T.strictTransformMap i ≫ coprod.inl)
    (coprod.desc (coprod.inr : T.detachedCoprod i ⟶ T.totalSpace i)
        (T.detachedι i ≫ coprod.inl) :
      T.detachedCoprod i ⨿ T.detachedScheme i ⟶ T.totalSpace i)
def totalCenter (i : ℕ) : (T.totalSpace i).IdealSheafData :=
  Scheme.Hom.ker
    ((T.centerOffDetached i).subschemeι ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i))
theorem exists_kerSubschemeIso_of_isClosedImmersion {X Z : Scheme.{u}} (g : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion g] :
    ∃ u : (Scheme.Hom.ker g).subscheme ≅ Z, u.hom ≫ g = (Scheme.Hom.ker g).subschemeι :=
  ⟨(asIso g.toImage).symm, by
    rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]⟩
theorem exists_coprodIso_of_isInitial {A B Z : Scheme.{u}}
    (hB : IsInitial B) (u : A ≅ Z) :
    ∃ e : (A ⨿ B) ≅ Z, (coprod.inl : A ⟶ A ⨿ B) ≫ e.hom = u.hom := by
  refine ⟨⟨coprod.desc u.hom (hB.to Z), u.inv ≫ coprod.inl, ?_, ?_⟩, coprod.inl_desc _ _⟩
  · refine coprod.hom_ext ?_ ?_
    · calc (coprod.inl : A ⟶ A ⨿ B) ≫ (coprod.desc u.hom (hB.to Z) ≫ (u.inv ≫ coprod.inl))
          = ((coprod.inl : A ⟶ A ⨿ B) ≫ coprod.desc u.hom (hB.to Z)) ≫
              (u.inv ≫ (coprod.inl : A ⟶ A ⨿ B)) := (Category.assoc _ _ _).symm
        _ = u.hom ≫ (u.inv ≫ (coprod.inl : A ⟶ A ⨿ B)) :=
            congrArg (fun t => t ≫ (u.inv ≫ (coprod.inl : A ⟶ A ⨿ B))) (coprod.inl_desc _ _)
        _ = (u.hom ≫ u.inv) ≫ (coprod.inl : A ⟶ A ⨿ B) := (Category.assoc _ _ _).symm
        _ = 𝟙 A ≫ (coprod.inl : A ⟶ A ⨿ B) :=
            congrArg (fun t => t ≫ (coprod.inl : A ⟶ A ⨿ B)) u.hom_inv_id
        _ = (coprod.inl : A ⟶ A ⨿ B) := Category.id_comp _
        _ = (coprod.inl : A ⟶ A ⨿ B) ≫ 𝟙 (A ⨿ B) := (Category.comp_id _).symm
    · exact hB.hom_ext _ _
  · calc (u.inv ≫ (coprod.inl : A ⟶ A ⨿ B)) ≫ coprod.desc u.hom (hB.to Z)
        = u.inv ≫ ((coprod.inl : A ⟶ A ⨿ B) ≫ coprod.desc u.hom (hB.to Z)) :=
          Category.assoc _ _ _
      _ = u.inv ≫ u.hom := congrArg (fun t => u.inv ≫ t) (coprod.inl_desc _ _)
      _ = 𝟙 Z := u.inv_hom_id
theorem exists_totalSpaceZeroIso :
    ∃ e : T.totalSpace 0 ≅ Y,
      (coprod.inl : T.strictTransform 0 ⟶ T.totalSpace 0) ≫ e.hom ≫
          (T.emb ≫ T.ambientSeq.isoZero.inv) = T.strictTransformι 0 := by
  have : AlgebraicGeometry.IsClosedImmersion (T.emb ≫ T.ambientSeq.isoZero.inv) := inferInstance
  obtain ⟨u, hu⟩ := exists_kerSubschemeIso_of_isClosedImmersion
    (T.emb ≫ T.ambientSeq.isoZero.inv)
  have hB : IsInitial (T.detachedCoprod 0) := initialIsInitial
  obtain ⟨e, he⟩ :=
    exists_coprodIso_of_isInitial (A := T.strictTransform 0) (B := T.detachedCoprod 0) (Z := Y) hB u
  refine ⟨e, ?_⟩
  refine Eq.trans ?_ hu
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun t => t ≫ (T.emb ≫ T.ambientSeq.isoZero.inv)) he
def totalSpaceZeroIso : T.totalSpace 0 ≅ Y := T.exists_totalSpaceZeroIso.choose
def totalTower : ℕᵒᵖ ⥤ Scheme.{u} :=
  (Functor.ofSequence (fun i => (T.totalTransition i).op)).leftOp
def TransitionsAreBlowups : Prop :=
  ∀ i, i < T.length → Blowup.IsBlowupAlongIdealSheaf (T.totalTower.map (homOfLE (Nat.le_succ i)).op) (T.totalCenter i)
def inducedBlowups (h : T.TransitionsAreBlowups) : SequenceOfBlowups Y where
  length := T.length
  tower := T.totalTower
  isoZero := T.totalSpaceZeroIso
  center := T.totalCenter
  isBlowup := h
def inducedBlowupsWithoutIso (h : T.TransitionsAreBlowups) : SequenceOfBlowups Y := (T.inducedBlowups h).withoutIsoBlowups
end EmbeddedBlowupSequence
theorem locallyOfFiniteType_affineSpaceIndexedByToSpec_ulift (k : Type u) [Field k] (n : ℕ) :
    AlgebraicGeometry.LocallyOfFiniteType (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n))) := by
  unfold affineSpaceIndexedByToSpec
  infer_instance
theorem quasiCompact_affineSpaceIndexedByToSpec_ulift (k : Type u) [Field k] (n : ℕ) :
    AlgebraicGeometry.QuasiCompact (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n))) := by
  unfold affineSpaceIndexedByToSpec
  infer_instance
namespace AffineSpacePrincipalizationData
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
def toEmbeddedBlowupSequence (S : AffineSpacePrincipalizationData k Y pY) : EmbeddedBlowupSequence k Y pY where
  ambient := S.ambient
  ambientStruct := S.ambientToSpec
  isAffine_ambient := inferInstance
  smooth_ambientStruct := S.ambient_smooth
  locallyOfFiniteType_ambientStruct := locallyOfFiniteType_affineSpaceIndexedByToSpec_ulift k S.dim
  quasiCompact_ambientStruct := quasiCompact_affineSpaceIndexedByToSpec_ulift k S.dim
  emb := S.emb
  isClosedImmersion_emb := S.emb_closedImmersion
  emb_comp := S.emb_comp
  ambientSeq := S.ambientBlowups
theorem toEmbeddedBlowupSequence_transitionsAreBlowups_iff (S : AffineSpacePrincipalizationData k Y pY) :
    S.toEmbeddedBlowupSequence.TransitionsAreBlowups ↔ S.TransitionsAreBlowups := Iff.rfl
end AffineSpacePrincipalizationData
namespace EmbeddingDatum
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
def toEmbeddedBlowupSequence (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) : EmbeddedBlowupSequence k Y pY where
  ambient := D.ambient
  ambientStruct := D.ambientStruct
  isAffine_ambient := D.isAffine_ambient
  smooth_ambientStruct := D.smooth_ambientStruct
  locallyOfFiniteType_ambientStruct := D.locallyOfFiniteType_ambientStruct
  quasiCompact_ambientStruct := D.quasiCompact_ambientStruct
  emb := D.emb
  isClosedImmersion_emb := D.isClosedImmersion_emb
  emb_comp := D.comp_eq
  ambientSeq :=
    (A k D.ambient D.ambientStruct (Scheme.Hom.ker D.emb) D.nonzeroOnComponents_ker
      ([] : List D.ambient.IdealSheafData) D.sncEmpty).toSequenceOfBlowups
end EmbeddingDatum
def TransitionsAreBlowupsForEmbeddings (A : PrincipalizationAlgorithm.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (D : EmbeddingDatum k Y pY),
    (D.toEmbeddedBlowupSequence A).TransitionsAreBlowups
def embeddedResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u}) (h : TransitionsAreBlowupsForEmbeddings A) : EmbeddedResolutionRule.{u} := by
  intro k _ _ Y pY _ _ _ _ D
  exact (D.toEmbeddedBlowupSequence A).inducedBlowupsWithoutIso (h k Y pY D)
def affineSpaceEmbeddingDatum (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY] :
    EmbeddingDatum k Y pY where
  ambient := affineSpaceIndexedBy k (ULift.{u} (Fin (hemb k Y pY).choose))
  ambientStruct := affineSpaceIndexedByToSpec k (ULift.{u} (Fin (hemb k Y pY).choose))
  emb := (hemb k Y pY).choose_spec.choose
  isAffine_ambient := inferInstance
  smooth_ambientStruct := hsm k ((hemb k Y pY).choose)
  locallyOfFiniteType_ambientStruct :=
    locallyOfFiniteType_affineSpaceIndexedByToSpec_ulift k ((hemb k Y pY).choose)
  quasiCompact_ambientStruct :=
    quasiCompact_affineSpaceIndexedByToSpec_ulift k ((hemb k Y pY).choose)
  isClosedImmersion_emb := (hemb k Y pY).choose_spec.choose_spec.1
  nonzeroOnComponents_ker := (hemb k Y pY).choose_spec.choose_spec.2.1
  comp_eq := (hemb k Y pY).choose_spec.choose_spec.2.2
  sncEmpty := hsnc k ((hemb k Y pY).choose)
def affineSpaceEmbeddingChoice (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    EmbeddingChoice.{u} := by
  intro k _ _ Y pY _ _ _ _
  exact affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY
end FunctorialResolution.EmbeddedResolution
end


