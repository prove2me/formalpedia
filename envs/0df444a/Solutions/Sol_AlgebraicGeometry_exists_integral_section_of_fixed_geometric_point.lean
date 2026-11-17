-- Prove2me | solution 1 for AlgebraicGeometry.exists_integral_section_of_fixed_geometric_point
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:12.851096+00:00
-- url     : https://prove2.me/submissions/29c79ddd-61e1-47e9-9b95-ff8e88b27967

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry

/-- A rational geometric point on a proper model over the integers localized at
a prime extends to a section of that same model. The comparison is an equality
of geometric morphisms, retaining the chosen model and its original point. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime]
    {B : Scheme.{0}}
    (f : B ⟶ Spec (CommRingCat.of (GaloisRep.ratLocalizedAt p))) [IsProper f]
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom
      (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) f)
    (hx : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.1 = x.1) :
    ∃ s : SchemeHomOver (𝟙 (Spec (CommRingCat.of (GaloisRep.ratLocalizedAt p)))) f,
      Spec.map (CommRingCat.ofHom
        (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) ≫ s.1 = x.1 := by
  letI : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
    { isAlgClosed := AlgebraicClosure.isAlgClosed ℚ
      isAlgebraic := ⟨fun z => by
        have hz : _root_.IsIntegral ℚ z := by
          convert ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z).isIntegral
          all_goals rfl
        exact hz.isAlgebraic⟩ }
  letI : IsGalois ℚ (AlgebraicClosure ℚ) :=
    { to_isSeparable := IsAlgClosure.separable ℚ (AlgebraicClosure ℚ)
      to_normal := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) }
  have hd := Scheme.exists_specMap_fixedField_comp_eq_of_forall_comp_eq
    (⊤ : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) x.1 (fun σ _ => hx σ)
  rw [InfiniteGalois.fixedField_bot] at hd
  obtain ⟨y, hy⟩ := hd
  let e := IntermediateField.botEquiv ℚ (AlgebraicClosure ℚ)
  let yQ := Spec.map (CommRingCat.ofHom e.toRingHom) ≫ y
  let b := Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))
  have hyQ : b ≫ yQ = x.1 := by
    dsimp [yQ, b]
    rw [← Category.assoc, ← Spec.map_comp]
    convert hy using 2
    congr 1
    apply CommRingCat.hom_ext
    ext a
    exact congrArg Subtype.val (e.symm_apply_apply a)
  let j := Spec.map (CommRingCat.ofHom (algebraMap (GaloisRep.ratLocalizedAt p) ℚ))
  have hbj : b ≫ j = Spec.map (CommRingCat.ofHom
      (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) := by
    dsimp [b, j]
    rw [← Spec.map_comp]
    congr 1
  letI : Epi b := Flat.epi_of_flat_of_surjective b
  have hyover : yQ ≫ f = j := by
    apply (cancel_epi b).mp
    rw [← Category.assoc, hyQ, hbj]
    exact x.2
  letI := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p (Fact.out : p.Prime)
  letI := GaloisRep.isFractionRing_ratLocalizedAt p
  have hv : ValuativeCriterion f := by
    have h : IsProper f := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  let square : ValuativeCommSq f :=
    { R := GaloisRep.ratLocalizedAt p
      K := ℚ
      i₁ := yQ
      i₂ := 𝟙 _
      commSq := ⟨by simpa [j] using hyover⟩ }
  obtain ⟨s, hs, hf⟩ := (hv.existence square).exists_lift
  refine ⟨⟨s, hf⟩, ?_⟩
  calc
    Spec.map (CommRingCat.ofHom
        (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) ≫ s =
        (b ≫ j) ≫ s := congrArg (fun z => z ≫ s) hbj.symm
    _ = b ≫ (j ≫ s) := Category.assoc _ _ _
    _ = b ≫ yQ := congrArg (fun z => b ≫ z) hs
    _ = x.1 := hyQ

end AlgebraicGeometry
