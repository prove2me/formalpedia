-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.exists_coequifibered_iso_glued_comp_toBase_eq_of_isAffineHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/6840d3f8-7c8f-50cd-a1dd-1e3188b7d99d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_coequifibered_iso_glued_comp_toBase_eq_of_isAffineHom

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry"

noncomputable section

namespace FormalGAGAFiniteAffDescAux

p2m_open "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.AffineZariskiSite"

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

abbrev α : (toOpensFunctor Y).op ⋙ Y.presheaf ⟶ (toOpensFunctor Y).op ⋙ f.base _* X.presheaf :=
  (toOpensFunctor Y).op.whiskerLeft f.c

set_option backward.isDefEq.respectTransparency false in

lemma coequifibered [QuasiCompact f] [QuasiSeparated f] : (α f).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r ↦ ?_
  let inst : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  have : IsLocalization.Away (f.app U.1 r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) := by
    let : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, X.basicOpen (f.app _ r)) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le _)).op).hom.toAlgebra
    dsimp +instances [inst]
    rw! (castMode := .all) [f.preimage_basicOpen r]
    exact isLocalization_basicOpen_of_qcqs (f.isCompact_preimage U.2.isCompact)
        (f.isQuasiSeparated_preimage U.2.isQuasiSeparated) (f.app _ r)
  exact this

variable [IsAffineHom f]

def D : (directedCover Y).RelativeGluingData := relativeGluingData (coequifibered f)

scoped instance : ((D f).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

lemma D_cover_f (U : Y.AffineZariskiSite) : (D f).cover.f U = colimit.ι (D f).functor U := by
  simp [D]

abbrev chart (U : Y.AffineZariskiSite) : pullback f U.1.ι ⟶ (D f).glued :=
  (pullbackRestrictIsoRestrict f _).hom ≫ (f ⁻¹ᵁ U.1).toSpecΓ ≫ (D f).cover.f U

set_option backward.isDefEq.respectTransparency false in
lemma chart_compat {U V : Y.AffineZariskiSite} (i : U ⟶ V) :
    Cover.trans ((directedCover Y).pullback₁ f) i ≫ chart f V = chart f U := by
  have : (pullbackRestrictIsoRestrict f U.1).inv ≫
      Cover.trans ((directedCover Y).pullback₁ f) i ≫
      (pullbackRestrictIsoRestrict f V.1).hom = X.homOfLE
        (f.preimage_mono (toOpens_mono i.1.1)) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp +instances [Cover.trans, Cover.locallyDirectedPullbackCover]
  rw [chart, chart, ← Iso.inv_comp_eq, reassoc_of% this,
    ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]
  simp only [D_cover_f]
  rw [← colimit.w (D f).functor i]
  rfl

def toGlued : X ⟶ (D f).glued :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected ((directedCover Y).pullback₁ f)
    (chart f) (fun i ↦ chart_compat f i)

@[reassoc]
lemma ι_toGlued (U : Y.AffineZariskiSite) :
    (f ⁻¹ᵁ U.1).ι ≫ toGlued f = (f ⁻¹ᵁ U.1).toSpecΓ ≫ (D f).cover.f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict f U.1).hom, ← Category.assoc]
  trans ((directedCover Y).pullback₁ f).f U ≫ toGlued f
  · congr 1; simp; rfl
  exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected ((directedCover Y).pullback₁ f)
    (chart f) (fun i ↦ chart_compat f i) U

lemma ι_toBase (U : Y.AffineZariskiSite) :
    (D f).cover.f U ≫ (D f).toBase = Spec.map (f.app U.1) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

lemma toBase_preimage (U : Y.AffineZariskiSite) :
    (D f).toBase ⁻¹ᵁ U.1 = ((D f).cover.f U).opensRange := by
  have h := (D f).toBase_preimage_eq_opensRange_ι U
  simp only [Scheme.AffineZariskiSite.directedCover_f, Scheme.Opens.opensRange_ι] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma toGlued_toBase : toGlued f ≫ (D f).toBase = f := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.1)) _ _ fun U ↦ ?_
  refine (ι_toGlued_assoc f ⟨U.1, U.2⟩ _).trans ?_
  rw [ι_toBase]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f.app _) ≫ U.2.fromSpec = (f ⁻¹ᵁ U.1).ι ≫ _
  simp

lemma toGlued_preimage (U : Y.AffineZariskiSite) :
    toGlued f ⁻¹ᵁ ((D f).cover.f U).opensRange = f ⁻¹ᵁ U.1 := by
  rw [← toBase_preimage, ← Scheme.Hom.comp_preimage, toGlued_toBase]

set_option backward.isDefEq.respectTransparency false in
scoped instance isIso_toGlued : IsIso (toGlued f) := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
    (D f).cover).mpr fun U ↦ ?_
  let e := IsOpenImmersion.isoOfRangeEq (pullback.fst (toGlued f) ((D f).cover.f U))
    (f ⁻¹ᵁ U.1).ι (by
      rw [Pullback.range_fst, Opens.range_ι, ← Hom.coe_opensRange, ← Scheme.Hom.coe_preimage,
        toGlued_preimage])
  rw [← MorphismProperty.cancel_left_of_respectsIso (.isomorphisms _) e.inv]
  have heq : e.inv ≫ pullback.snd (toGlued f) ((D f).cover.f U) = (f ⁻¹ᵁ U.1).toSpecΓ := by
    rw [← cancel_mono ((D f).cover.f U), Category.assoc, ← pullback.condition,
      ← Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac, ι_toGlued]
  change IsIso (e.inv ≫ pullback.snd (toGlued f) ((D f).cover.f U))
  rw [heq, ← IsAffineOpen.isoSpec_hom (U.2.preimage f)]
  infer_instance

def isoGlued : X ≅ (D f).glued := asIso (toGlued f)

end FormalGAGAFiniteAffDescAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_coequifibered_iso_glued_comp_toBase_eq_of_isAffineHom.FormalGAGAFiniteAffDescAux"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_coequifibered_iso_glued_comp_toBase_eq_of_isAffineHom.FormalGAGAFiniteAffDescAux"

open FormalGAGAFiniteAffDescAux in
theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    ∃ (H : ((Scheme.AffineZariskiSite.toOpensFunctor Y).op.whiskerLeft f.c).Coequifibered)
      (e : X ≅ (Scheme.AffineZariskiSite.relativeGluingData H).glued),
      e.hom ≫ (Scheme.AffineZariskiSite.relativeGluingData H).toBase = f ∧
      ∀ U : Y.AffineZariskiSite, (f ⁻¹ᵁ U.1).ι ≫ e.hom =
        (f ⁻¹ᵁ U.1).toSpecΓ ≫ (Scheme.AffineZariskiSite.relativeGluingData H).cover.f U :=
  ⟨coequifibered f, isoGlued f, toGlued_toBase f, fun U ↦ ι_toGlued f U⟩

end S_AlgebraicGeometry_Scheme_Hom_exists_coequifibered_iso_glued_comp_toBase_eq_of_isAffineHom
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_coequifibered_iso_glued_comp_toBase_eq_of_isAffineHom (solution)
