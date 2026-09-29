-- Prove2me | solution 1 for AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/6760894f-10d9-56b9-bce9-b6cad40e38d6

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MFPb6

def HasModels (A₀ : Type u) [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (CommRingCat.of A)) : Prop :=
  ∀ SS : Finset A, ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑SS : Set A) ⊆ T ∧
    Set.range (algebraMap A₀ A) ⊆ T ∧
    ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : Y ⟶ X₀),
      LocallyOfFinitePresentation f₀ ∧ QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
      IsPullback π h f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A)))

variable {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]

theorem hasModels_of_iso {Y Y' : Scheme.{u}} {h : Y ⟶ Spec (CommRingCat.of A)}
    (hh : HasModels A₀ h) (e : Y' ≅ Y) {h' : Y' ⟶ Spec (CommRingCat.of A)} (w : e.hom ≫ h = h') :
    HasModels A₀ h' := by
  intro SS
  obtain ⟨T, hT, hs, hr, X₀, f₀, π, h1, h2, h3, hpb⟩ := hh SS
  refine ⟨T, hT, hs, hr, X₀, f₀, e.hom ≫ π, h1, h2, h3, ?_⟩
  subst w
  exact hpb.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

theorem hasModels_of_isAffine {Y : Scheme.{u}} [IsAffine Y] (h : Y ⟶ Spec (CommRingCat.of A))
    [LocallyOfFinitePresentation h] : HasModels A₀ h := by
  intro SS
  obtain ⟨T, hT, hs, hr, X₀, f₀, π, -, h1, h2, h3, hpb⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation
      (A₀ := A₀) (R := A₀) (A := A) h SS
  exact ⟨T, hT, hs, hr, X₀, f₀, π, h1, h2, h3, hpb⟩

theorem hasModels_of_sup {Z : Scheme.{u}} (gZ : Z ⟶ Spec (CommRingCat.of A))
    [QuasiCompact gZ] [QuasiSeparated gZ] [LocallyOfFinitePresentation gZ]
    (U V : Z.Opens) (hUV : U ⊔ V = ⊤) (hUc : IsCompact (U : Set Z)) (hVc : IsCompact (V : Set Z))
    (hU : HasModels A₀ (U.ι ≫ gZ)) (hV : HasModels A₀ (V.ι ≫ gZ)) : HasModels A₀ gZ := by
  intro SS
  exact AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation
    (A₀ := A₀) (R := A₀) (A := A) gZ U V hUV hUc hVc hU hV SS

theorem isCompact_preimage_ι {X : Scheme.{u}} {S V : X.Opens} (hSV : S ≤ V)
    (hS : IsCompact (S : Set X)) :
    IsCompact ((V.ι ⁻¹ᵁ S : V.toScheme.Opens) : Set V) := by
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  haveI : CompactSpace ↥(V.ι ⁻¹ᵁ S) :=
    QuasiCompact.compactSpace_of_compactSpace (Scheme.Opens.isoOfLE hSV).hom
  exact isCompact_iff_compactSpace.mpr ‹_›

theorem main {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact g]
    [QuasiSeparated g] [LocallyOfFinitePresentation g] : HasModels A₀ g := by
  have key : ∀ S : X.Opens, IsCompact (S : Set X) → HasModels A₀ (S.ι ≫ g) := by
    intro S hS
    refine compact_open_induction_on (P := fun S : X.Opens => HasModels A₀ (S.ι ≫ g)) S hS ?_ ?_
    · haveI : IsAffine ((⊥ : X.Opens) : Scheme.{u}) := isAffineOpen_bot X
      exact hasModels_of_isAffine _
    · intro S hS U hPS
      have hS' : IsCompact (S : Set X) := hS
      have hPS' : HasModels A₀ (S.ι ≫ g) := hPS
      show HasModels A₀ ((S ⊔ ↑U).ι ≫ g)
      haveI : CompactSpace ↥((S ⊔ ↑U : X.Opens) : Scheme.{u}) :=
        isCompact_iff_compactSpace.mp (hS'.union U.2.isCompact)
      haveI : IsAffine ((U : X.Opens) : Scheme.{u}) := U.2
      refine hasModels_of_sup ((S ⊔ ↑U).ι ≫ g) ((S ⊔ ↑U).ι ⁻¹ᵁ S) ((S ⊔ ↑U).ι ⁻¹ᵁ ↑U)
        (by rw [← Scheme.Hom.preimage_sup, Scheme.Opens.ι_preimage_self])
        (isCompact_preimage_ι le_sup_left hS') (isCompact_preimage_ι le_sup_right U.2.isCompact)
        ?_ ?_
      · exact hasModels_of_iso hPS' (Scheme.Opens.isoOfLE (le_sup_left : S ≤ S ⊔ ↑U))
          (by rw [← Category.assoc, Scheme.Opens.isoOfLE_hom_ι, Category.assoc])
      · exact hasModels_of_iso (hasModels_of_isAffine ((U : X.Opens).ι ≫ g))
          (Scheme.Opens.isoOfLE (le_sup_right : (U : X.Opens) ≤ S ⊔ ↑U))
          (by rw [← Category.assoc, Scheme.Opens.isoOfLE_hom_ι, Category.assoc])
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  have htop : HasModels A₀ ((⊤ : X.Opens).ι ≫ g) :=
    key ⊤ (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)
  exact hasModels_of_iso htop X.topIso.symm
    (by rw [Iso.symm_hom, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp])

end MFPb6

theorem solution {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact g] [QuasiSeparated g]
    [LocallyOfFinitePresentation g] (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : X ⟶ X₀),
        LocallyOfFinitePresentation f₀ ∧ QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
        IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) := by
  obtain ⟨T, hT, hs, -, X₀, f₀, π, h1, h2, h3, hpb⟩ := MFPb6.main (A₀ := A₀) g s
  exact ⟨T, hT, hs, X₀, f₀, π, h1, h2, h3, hpb⟩

end S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
end P2MW
export P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation (solution)
