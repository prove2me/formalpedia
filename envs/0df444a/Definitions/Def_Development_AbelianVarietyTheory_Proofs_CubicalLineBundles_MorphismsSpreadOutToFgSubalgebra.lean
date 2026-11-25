-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
-- name    : Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T14:12:35.168837+00:00
-- url     : https://prove2.me/theorems/bf0194b9-8380-403c-be89-54c84a951324
-- title:
--   Morphisms Spread Out To Fg Subalgebra
-- statement:
--   Definitions and structural lemmas for Morphisms Spread Out To Fg Subalgebra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MorphismsSpreadOutToFgSubalgebra.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.Spread
section General
variable {k : Type} [CommRing k] {B Z : Scheme.{0}} (pB : B ⟶ Sp k)
theorem spMap_algHom_comp {R A : Type} [CommRing R] [CommRing A] [Algebra k R] [Algebra k A]
    (f : R →ₐ[k] A) : spMap f.toRingHom ≫ spMap (algebraMap k R) = spMap (algebraMap k A) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact f.comp_algebraMap
def bcMap {R A : Type} [CommRing R] [CommRing A] [Algebra k R] [Algebra k A] (f : R →ₐ[k] A) :
    pullback pB (spMap (algebraMap k A)) ⟶ pullback pB (spMap (algebraMap k R)) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap f.toRingHom)
    (by rw [Category.assoc, spMap_algHom_comp, pullback.condition])
section
variable {R R' A : Type} [CommRing R] [CommRing R'] [CommRing A] [Algebra k R] [Algebra k R']
  [Algebra k A]
@[reassoc (attr := simp)]
theorem bcMap_fst (f : R →ₐ[k] A) : bcMap pB f ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _
@[reassoc (attr := simp)]
theorem bcMap_snd (f : R →ₐ[k] A) :
    bcMap pB f ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap f.toRingHom :=
  pullback.lift_snd _ _ _
@[reassoc]
theorem bcMap_comp (f : R →ₐ[k] R') (g : R' →ₐ[k] A) :
    bcMap pB g ≫ bcMap pB f = bcMap pB (g.comp f) := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcMap_fst, bcMap_fst, bcMap_fst]
  · rw [Category.assoc, bcMap_snd, bcMap_snd_assoc, bcMap_snd, ← Spec.map_comp]
    rfl
@[reassoc]
theorem bcMap_comp_of_eq (f : R →ₐ[k] R') (g : R' →ₐ[k] A) (h : R →ₐ[k] A) (e : ∀ x, g (f x) = h x) :
    bcMap pB g ≫ bcMap pB f = bcMap pB h := by
  rw [bcMap_comp, show g.comp f = h from AlgHom.ext e]
theorem bcMap_eq_id (f : R →ₐ[k] R) (e : ∀ x, f x = x) : bcMap pB f = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [bcMap_fst, Category.id_comp]
  · rw [bcMap_snd, Category.id_comp, show f = AlgHom.id k R from AlgHom.ext e]
    exact (congrArg _ (Spec.map_id _)).trans (Category.comp_id _)
theorem isPullback_bcMap (f : R →ₐ[k] A) :
    IsPullback (bcMap pB f) (pullback.snd _ _) (pullback.snd _ _) (spMap f.toRingHom) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst pB _) (v₁₃ := pB)
    (h₂₂ := spMap (algebraMap k R)) ?_ (bcMap_snd _ _) (.of_hasPullback _ _)
  rw [spMap_algHom_comp, bcMap_fst]
  exact .of_hasPullback _ _
instance isAffineHom_bcMap (f : R →ₐ[k] A) : IsAffineHom (bcMap pB f) :=
  MorphismProperty.of_isPullback (isPullback_bcMap pB f).flip inferInstance
end
variable (A : Type) [CommRing A] [Algebra k A]
def ringDiagram (k : Type) [CommRing k] (A : Type) [CommRing A] [Algebra k A] :
    Finset A ⥤ CommRingCat.{0} where
  obj s := .of (Algebra.adjoin k (s : Set A))
  map {s t} h := CommRingCat.ofHom
    (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h.le))).toRingHom
def ringCocone (k : Type) [CommRing k] (A : Type) [CommRing A] [Algebra k A] :
    Cocone (ringDiagram k A) where
  pt := .of A
  ι := { app s := CommRingCat.ofHom (Algebra.adjoin k (s : Set A)).val.toRingHom }
def isColimitRingCocone (k : Type) [CommRing k] (A : Type) [CommRing A] [Algebra k A] :
    IsColimit (ringCocone k A) := by
  classical
  have : ReflectsFilteredColimits (forget CommRingCat.{0}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  exact isColimitOfReflects (forget _)
    (Types.FilteredColimit.isColimitOf' _ _
      (fun x ↦ by
        let x' : A := x
        exact ⟨({x'} : Finset A), (⟨x', Algebra.subset_adjoin (by simp)⟩ :
          Algebra.adjoin k (({x'} : Finset A) : Set A)), rfl⟩)
      (fun i x y hxy ↦ ⟨i, 𝟙 i, congrArg _ (Subtype.ext hxy)⟩))
def bcDiagram : (Finset A)ᵒᵖ ⥤ Scheme.{0} where
  obj s := pullback pB (spMap (algebraMap k (Algebra.adjoin k (s.unop : Set A))))
  map {s t} h := bcMap pB
    (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h.unop.le)))
  map_id s := bcMap_eq_id pB _ fun _ ↦ rfl
  map_comp f g := (bcMap_comp_of_eq pB _ _ _ fun _ ↦ rfl).symm
def bcCone : Cone (bcDiagram pB A) where
  pt := pullback pB (spMap (algebraMap k A))
  π :=
    { app s := bcMap pB (Algebra.adjoin k (s.unop : Set A)).val
      naturality s t f := (Category.id_comp _).trans (bcMap_comp_of_eq pB _ _ _ fun _ ↦ rfl).symm }
def isLimitBcCone : IsLimit (bcCone pB A) := by
  classical
  let α : bcDiagram pB A ⟶ (ringDiagram k A).op ⋙ Scheme.Spec :=
    { app s := pullback.snd pB _
      naturality s t f := bcMap_snd pB _ }
  exact isLimitOfIsPullbackOfIsConnected α (bcCone pB A)
    (Scheme.Spec.mapCone (ringCocone k A).op)
    { hom := pullback.snd pB _, w s := (bcMap_snd pB _).symm }
    (fun s ↦ isPullback_bcMap pB _)
    (isLimitOfPreserves Scheme.Spec (isColimitRingCocone k A).op)
instance {s t : (Finset A)ᵒᵖ} (f : s ⟶ t) : IsAffineHom ((bcDiagram pB A).map f) :=
  isAffineHom_bcMap pB _
theorem compactSpace_bc [QuasiCompact pB] {T : Scheme.{0}} [CompactSpace T] (g : T ⟶ Sp k) :
    CompactSpace ↥(pullback pB g) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.snd pB g)
instance [QuasiCompact pB] (s : (Finset A)ᵒᵖ) : CompactSpace ((bcDiagram pB A).obj s) :=
  compactSpace_bc pB _
instance [QuasiSeparated pB] (s : (Finset A)ᵒᵖ) : QuasiSeparatedSpace ((bcDiagram pB A).obj s) :=
  (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd pB _)).mp inferInstance
def bcStr : bcDiagram pB A ⟶ (Functor.const _).obj (Sp k) where
  app s := pullback.fst pB _ ≫ pB
  naturality s t f := by
    change bcMap pB _ ≫ pullback.fst pB _ ≫ pB = (pullback.fst pB _ ≫ pB) ≫ 𝟙 _
    rw [bcMap_fst_assoc, Category.comp_id]
variable {A} (pZ : Z ⟶ Sp k)
open Chart
end General
section Field
variable {k A : Type} [Field k] [CommRing A] [Algebra k A] {B Z : Scheme.{0}} (pB : B ⟶ Sp k)
end Field
end GlobalTheory.Spread
namespace GlobalTheory
end GlobalTheory


