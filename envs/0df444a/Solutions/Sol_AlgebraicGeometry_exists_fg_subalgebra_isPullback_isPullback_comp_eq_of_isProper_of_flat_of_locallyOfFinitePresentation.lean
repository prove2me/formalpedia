-- Prove2me | solution 1 for AlgebraicGeometry.exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3a429098-246c-5615-81a7-7e9a679966d0

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq"

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace P2mWs41DescTriple

lemma isPullback_lift_of_fac {X X₁ Y B B' : Scheme.{u}} {π : X ⟶ X₁} {g : X ⟶ Y} {f : X₁ ⟶ B} {ι : Y ⟶ B}
    (sq : IsPullback π g f ι) (κ : B' ⟶ B) (ι' : Y ⟶ B') (hι : ι' ≫ κ = ι)
    (w : π ≫ f = (g ≫ ι') ≫ κ) :
    IsPullback (pullback.lift π (g ≫ ι') w) g (pullback.snd f κ) ι' := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f κ) (v₁₃ := f) (h₂₂ := κ) ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback f κ)
  rw [pullback.lift_fst, hι]
  exact sq

lemma specMap_algebraMap_comp {T : Type u} [CommRing T] {A : Type u} [CommRing A] [Algebra T A]
    (T' : Subalgebra T A) :
    Spec.map (CommRingCat.ofHom (algebraMap ↥T' A)) ≫ Spec.map (CommRingCat.ofHom (algebraMap T ↥T')) =
      Spec.map (CommRingCat.ofHom (algebraMap T A)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

lemma package {A₀ B A : Type} [CommRing A₀] [CommRing B] [CommRing A] [Algebra A₀ B] [Algebra B A] [Algebra A₀ A]
    [IsScalarTower A₀ B A] [Algebra.FiniteType A₀ B]
    (T₃ : Subalgebra B A) (hT₃ : T₃.FG)
    {X Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (q : X ⟶ Spec (CommRingCat.of A)) (h : Z ⟶ X)
    (Z₀ X₀ : Scheme.{0}) (p₀ : Z₀ ⟶ Spec (CommRingCat.of ↥T₃)) (q₀ : X₀ ⟶ Spec (CommRingCat.of ↥T₃)) (h₀ : Z₀ ⟶ X₀)
    (πZ : Z ⟶ Z₀) (πX : X ⟶ X₀)
    (H : h₀ ≫ q₀ = p₀ ∧ IsProper p₀ ∧ Flat p₀ ∧ LocallyOfFinitePresentation p₀ ∧
        IsProper q₀ ∧ Flat q₀ ∧ LocallyOfFinitePresentation q₀ ∧
        IsPullback πZ p p₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T₃ A))) ∧
        IsPullback πX q q₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T₃ A))) ∧
        h ≫ πX = πZ ≫ h₀) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧
      ∃ (Z₀ X₀ : Scheme.{0}) (p₀ : Z₀ ⟶ Spec (CommRingCat.of ↥T)) (q₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (h₀ : Z₀ ⟶ X₀)
        (πZ : Z ⟶ Z₀) (πX : X ⟶ X₀),
        h₀ ≫ q₀ = p₀ ∧ IsProper p₀ ∧ Flat p₀ ∧ LocallyOfFinitePresentation p₀ ∧
        IsProper q₀ ∧ Flat q₀ ∧ LocallyOfFinitePresentation q₀ ∧
        IsPullback πZ p p₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) ∧
        IsPullback πX q q₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) ∧
        h ≫ πX = πZ ≫ h₀ := by
  haveI : Algebra.FiniteType B ↥T₃ := (Subalgebra.fg_iff_finiteType _).mp hT₃
  have hFT : Algebra.FiniteType A₀ ↥T₃ := Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  exact ⟨T₃.restrictScalars A₀, (Subalgebra.fg_iff_finiteType _).mpr hFT, Z₀, X₀, p₀, q₀, h₀, πZ, πX, H⟩

theorem descend_triple
    {A₀ : Type} [CommRing A₀] [IsNoetherianRing A₀] {A : Type} [CommRing A] [Algebra A₀ A] {X Z : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of A)) (q : X ⟶ Spec (CommRingCat.of A)) (h : Z ⟶ X) (w : h ≫ q = p)
    [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [IsProper q] [Flat q] [LocallyOfFinitePresentation q] :
    ∃ (T : Subalgebra A₀ A), T.FG ∧
      ∃ (Z₀ X₀ : Scheme.{0}) (p₀ : Z₀ ⟶ Spec (CommRingCat.of ↥T)) (q₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (h₀ : Z₀ ⟶ X₀)
        (πZ : Z ⟶ Z₀) (πX : X ⟶ X₀),
        h₀ ≫ q₀ = p₀ ∧ IsProper p₀ ∧ Flat p₀ ∧ LocallyOfFinitePresentation p₀ ∧
        IsProper q₀ ∧ Flat q₀ ∧ LocallyOfFinitePresentation q₀ ∧
        IsPullback πZ p p₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) ∧
        IsPullback πX q q₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) ∧
        h ≫ πX = πZ ≫ h₀ := by
  classical

  obtain ⟨T₁, hT₁, -, X₁, f₁, πX₁, hprop₁, hflat₁, sqX₁⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation
      (A₀ := A₀) q (∅ : Finset A)
  haveI : Algebra.FiniteType A₀ ↥T₁ := (Subalgebra.fg_iff_finiteType _).mp hT₁
  haveI : IsNoetherianRing ↥T₁ := Algebra.FiniteType.isNoetherianRing A₀ ↥T₁
  haveI := hprop₁
  haveI := hflat₁

  obtain ⟨T₂, hT₂, -, Z₂, p₂, πZ₂, hprop₂, hflat₂, sqZ₂⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation
      (A₀ := ↥T₁) p (∅ : Finset A)
  haveI : Algebra.FiniteType ↥T₁ ↥T₂ := (Subalgebra.fg_iff_finiteType _).mp hT₂
  haveI : Algebra.FiniteType A₀ ↥T₂ := Algebra.FiniteType.trans (S := ↥T₁) inferInstance inferInstance
  haveI : IsNoetherianRing ↥T₂ := Algebra.FiniteType.isNoetherianRing A₀ ↥T₂
  haveI := hprop₂
  haveI := hflat₂

  let κ₁₂ : Spec (CommRingCat.of ↥T₂) ⟶ Spec (CommRingCat.of ↥T₁) := Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))
  let f₂ := pullback.snd f₁ κ₁₂
  have wX₂ : πX₁ ≫ f₁ = (q ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T₂ A))) ≫ κ₁₂ := by
    rw [Category.assoc, specMap_algebraMap_comp T₂]; exact sqX₁.w
  let πX₂ : X ⟶ pullback f₁ κ₁₂ := pullback.lift πX₁ (q ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T₂ A))) wX₂
  have sqX₂ : IsPullback πX₂ q f₂ (Spec.map (CommRingCat.ofHom (algebraMap ↥T₂ A))) :=
    isPullback_lift_of_fac sqX₁ κ₁₂ _ (specMap_algebraMap_comp T₂) wX₂
  haveI : IsProper f₂ := MorphismProperty.pullback_snd (P := @IsProper) _ _ hprop₁
  haveI : Flat f₂ := MorphismProperty.pullback_snd (P := @Flat) _ _ hflat₁
  haveI : LocallyOfFinitePresentation f₁ := inferInstance
  haveI : LocallyOfFinitePresentation f₂ :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
  haveI : LocallyOfFinitePresentation p₂ := inferInstance

  let σ₂ : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of ↥T₂) := Spec.map (CommRingCat.ofHom (algebraMap ↥T₂ A))
  let eZ : Z ≅ pullback p₂ σ₂ := sqZ₂.isoPullback
  let eX : X ≅ pullback f₂ σ₂ := sqX₂.isoPullback
  let g : pullback p₂ σ₂ ⟶ pullback f₂ σ₂ := eZ.inv ≫ h ≫ eX.hom
  have hg : g ≫ pullback.snd f₂ σ₂ = pullback.snd p₂ σ₂ := by
    simp only [g, eZ, eX, σ₂, Category.assoc, IsPullback.isoPullback_hom_snd, w, IsPullback.isoPullback_inv_snd]
  obtain ⟨T₃, hT₃, -, g₀, hg₀, hcompat⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      (A₀ := ↥T₂) p₂ f₂ g hg (∅ : Finset A)

  let τ : Spec (CommRingCat.of ↥T₃) ⟶ Spec (CommRingCat.of ↥T₂) := Spec.map (CommRingCat.ofHom (algebraMap ↥T₂ ↥T₃))
  let σ₃ : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of ↥T₃) := Spec.map (CommRingCat.ofHom (algebraMap ↥T₃ A))
  have hσ : σ₃ ≫ τ = σ₂ := specMap_algebraMap_comp T₃
  have wZ : πZ₂ ≫ p₂ = (p ≫ σ₃) ≫ τ := by rw [Category.assoc, hσ]; exact sqZ₂.w
  have wX : πX₂ ≫ f₂ = (q ≫ σ₃) ≫ τ := by rw [Category.assoc, hσ]; exact sqX₂.w
  let πZ : Z ⟶ pullback p₂ τ := pullback.lift πZ₂ (p ≫ σ₃) wZ
  let πX : X ⟶ pullback f₂ τ := pullback.lift πX₂ (q ≫ σ₃) wX
  have sqZ : IsPullback πZ p (pullback.snd p₂ τ) σ₃ := isPullback_lift_of_fac sqZ₂ τ σ₃ hσ wZ
  have sqX : IsPullback πX q (pullback.snd f₂ τ) σ₃ := isPullback_lift_of_fac sqX₂ τ σ₃ hσ wX

  have hval : (T₃.val.toRingHom : ↥T₃ →+* A) = algebraMap ↥T₃ A := RingHom.ext fun _ => rfl
  have hcomm : h ≫ πX = πZ ≫ g₀ := by
    have key := hcompat (eZ.inv ≫ πZ) (eX.inv ≫ πX)
      (by simp only [Category.assoc, πZ, τ, pullback.lift_fst, eZ, σ₂, IsPullback.isoPullback_inv_fst])
      (by rw [hval]; simp only [Category.assoc, πZ, τ, pullback.lift_snd, eZ, σ₂, σ₃, IsPullback.isoPullback_inv_snd_assoc])
      (by simp only [Category.assoc, πX, τ, pullback.lift_fst, eX, σ₂, IsPullback.isoPullback_inv_fst])
      (by rw [hval]; simp only [Category.assoc, πX, τ, pullback.lift_snd, eX, σ₂, σ₃, IsPullback.isoPullback_inv_snd_assoc])

    have key' := congrArg (fun k => eZ.hom ≫ k) key
    simp only [g, Category.assoc, Iso.hom_inv_id_assoc] at key'
    exact key'.symm

  exact package (A₀ := A₀) (B := ↥T₂) T₃ hT₃ p q h (pullback p₂ τ) (pullback f₂ τ) (pullback.snd p₂ τ) (pullback.snd f₂ τ) g₀ πZ πX
    ⟨hg₀,
     MorphismProperty.pullback_snd (P := @IsProper) _ _ hprop₂,
     MorphismProperty.pullback_snd (P := @Flat) _ _ hflat₂,
     MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance,
     MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance,
     MorphismProperty.pullback_snd (P := @Flat) _ _ inferInstance,
     MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance,
     sqZ, sqX, hcomm⟩

end P2mWs41DescTriple

theorem solution
    {A : Type} [CommRing A] {X Z : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of A)) (q : X ⟶ Spec (CommRingCat.of A)) (h : Z ⟶ X) (w : h ≫ q = p)
    [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [IsProper q] [Flat q] [LocallyOfFinitePresentation q] :
    ∃ (T : Subalgebra ℤ A), T.FG ∧
      ∃ (Z₀ X₀ : Scheme.{0}) (p₀ : Z₀ ⟶ Spec (CommRingCat.of ↥T)) (q₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (h₀ : Z₀ ⟶ X₀)
        (πZ : Z ⟶ Z₀) (πX : X ⟶ X₀),
        h₀ ≫ q₀ = p₀ ∧ IsProper p₀ ∧ Flat p₀ ∧ LocallyOfFinitePresentation p₀ ∧
        IsProper q₀ ∧ Flat q₀ ∧ LocallyOfFinitePresentation q₀ ∧
        IsPullback πZ p p₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) ∧
        IsPullback πX q q₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) ∧
        h ≫ πX = πZ ≫ h₀ :=
  P2mWs41DescTriple.descend_triple (A₀ := ℤ) p q h w

end S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation
end P2MW
export P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation (solution)
