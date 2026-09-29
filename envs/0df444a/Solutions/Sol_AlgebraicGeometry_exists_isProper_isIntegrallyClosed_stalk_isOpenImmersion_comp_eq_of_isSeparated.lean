-- Prove2me | solution 1 for AlgebraicGeometry.exists_isProper_isIntegrallyClosed_stalk_isOpenImmersion_comp_eq_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1f0321d8-9e9c-5b29-8f92-b5ff737362a0

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral
import Theorems.Thm_AlgebraicGeometry_exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isProper_isIntegrallyClosed_stalk_isOpenImmersion_comp_eq_of_isSeparated
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isProper_isIntegrallyClosed_stalk_isOpenImmersion_comp_eq_of_isSeparated.AlgebraicGeometry TopologicalSpace"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsProper morphismRestrict_ι Scheme.Hom QuasiCompact LocallyOfFiniteType Spec IsIntegral Scheme.Hom.stalkMap_comp Scheme IsOpenImmersion IsSeparated Scheme.homOfLE_ι_assoc Scheme.Hom.isoImage_hom_ι Scheme.Hom.isoOpensRange_hom_ι exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral"
namespace B1aReduce
p2m_open "AlgebraicGeometry"

theorem isIso_stalkMap_of_isIso_morphismRestrict {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens)
    [IsIso (g ∣_ U)] (x : X) (hx : g.base x ∈ U) : IsIso (g.stalkMap x) := by
  haveI : IsOpenImmersion ((g ⁻¹ᵁ U).ι ≫ g) := by
    rw [← morphismRestrict_ι]; infer_instance
  obtain ⟨x', rfl⟩ : ∃ x' : ↥((g ⁻¹ᵁ U : X.Opens) : Scheme.{u}), (g ⁻¹ᵁ U).ι x' = x :=
    ⟨⟨x, hx⟩, rfl⟩
  have h := Scheme.Hom.stalkMap_comp (g ⁻¹ᵁ U).ι g x'
  haveI i1 : IsIso (((g ⁻¹ᵁ U).ι ≫ g).stalkMap x') := inferInstance
  haveI i2 : IsIso ((g ⁻¹ᵁ U).ι.stalkMap x') := inferInstance
  rw [h] at i1
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ i2 i1

end AlgebraicGeometry.B1aReduce

open AlgebraicGeometry.B1aReduce in
theorem solution
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∃ (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of k)) (D : P.Opens)
      (τ : (D : Scheme.{u}) ⟶ X) (V : X.Opens) (ι : (V : Scheme.{u}) ⟶ (D : Scheme.{u})),
      IsProper p ∧ IsIntegral P ∧ (∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y)) ∧
      IsProper τ ∧ τ ≫ f = D.ι ≫ p ∧
      Nonempty (V : Scheme.{u}) ∧ IsOpenImmersion ι ∧ ι ≫ τ = V.ι := by

  obtain ⟨X', Pt, π, j, q, hπ, -, hj, hq, hjq, hX', hPt, U, hU, hiso⟩ :=
    AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral f
  haveI := hπ; haveI := hj; haveI := hq; haveI := hX'; haveI := hPt; haveI := hiso

  obtain ⟨P, ν, hPint, hPn, hνfin, -, -, hνiso⟩ :=
    AlgebraicGeometry.exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral k q
  haveI := hPint; haveI := hνfin

  let U₀ : Pt.Opens := j.opensRange
  let D : P.Opens := ν ⁻¹ᵁ U₀
  let τ : (D : Scheme.{u}) ⟶ X := (ν ∣_ U₀) ≫ j.isoOpensRange.inv ≫ π

  let U₁ : Pt.Opens := j ''ᵁ (π ⁻¹ᵁ U)
  have hU₁ : ∀ z ∈ U₁, IsIntegrallyClosed (Pt.presheaf.stalk z) := by
    rintro _ ⟨y, hy, rfl⟩
    haveI : IsIso (π.stalkMap y) := isIso_stalkMap_of_isIso_morphismRestrict π U y hy
    haveI : IsIntegrallyClosed (X'.presheaf.stalk y) := by
      haveI := hX (π.base y)
      exact IsIntegrallyClosed.of_equiv (asIso (π.stalkMap y)).commRingCatIsoToRingEquiv
    exact IsIntegrallyClosed.of_equiv (asIso (j.stalkMap y)).symm.commRingCatIsoToRingEquiv
  haveI hνU₁ : IsIso (ν ∣_ U₁) := hνiso U₁ hU₁
  have hle : ν ⁻¹ᵁ U₁ ≤ D := by
    intro z hz
    show ν.base z ∈ U₀
    obtain ⟨y, -, hy⟩ := hz
    exact ⟨y, hy⟩

  let ι : (U : Scheme.{u}) ⟶ (D : Scheme.{u}) :=
    inv (π ∣_ U) ≫ (j.isoImage (π ⁻¹ᵁ U)).hom ≫ inv (ν ∣_ U₁) ≫ P.homOfLE hle
  refine ⟨P, ν ≫ q, D, τ, U, ι, inferInstance, hPint, hPn, inferInstance, ?_, ?_, inferInstance, ?_⟩
  ·
    simp only [τ, Category.assoc]
    rw [← hjq, j.isoOpensRange_inv_comp_assoc, ← Category.assoc, morphismRestrict_ι, Category.assoc]
  ·
    have : (U : Set X).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hU (TopologicalSpace.Opens.ext (h.trans TopologicalSpace.Opens.coe_bot.symm))
    obtain ⟨x, hx⟩ := this
    exact ⟨⟨x, hx⟩⟩
  ·
    rw [← cancel_epi (π ∣_ U)]
    have hm : (j.isoImage (π ⁻¹ᵁ U)).hom ≫ inv (ν ∣_ U₁) ≫ P.homOfLE hle ≫ (ν ∣_ U₀) =
        (π ⁻¹ᵁ U).ι ≫ j.isoOpensRange.hom := by
      rw [← cancel_mono U₀.ι]
      simp only [Category.assoc, morphismRestrict_ι]
      rw [Scheme.homOfLE_ι_assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
        Scheme.Hom.isoImage_hom_ι]
      simp only [U₀, Scheme.Hom.isoOpensRange_hom_ι]
    simp only [ι, τ, Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← Category.assoc (j.isoImage _).hom, ← Category.assoc ((j.isoImage _).hom ≫ _),
      ← Category.assoc (((j.isoImage _).hom ≫ _) ≫ _)]
    simp only [Category.assoc] at hm ⊢
    rw [reassoc_of% hm, Iso.hom_inv_id_assoc, morphismRestrict_ι]

end S_AlgebraicGeometry_exists_isProper_isIntegrallyClosed_stalk_isOpenImmersion_comp_eq_of_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isProper_isIntegrallyClosed_stalk_isOpenImmersion_comp_eq_of_isSeparated (solution)
