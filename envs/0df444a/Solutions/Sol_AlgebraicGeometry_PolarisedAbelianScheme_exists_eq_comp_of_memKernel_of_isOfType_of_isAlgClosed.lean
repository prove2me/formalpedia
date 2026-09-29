-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.exists_eq_comp_of_memKernel_of_isOfType_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/2a4a4701-a5d5-5137-9d2d-3fdc7a75af76

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Theorems.Thm_Module_FaithfullyFlat_exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_eq_comp_of_memKernel_of_isOfType_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
p2m_open_scoped "BigOperators CategoryTheory.MonoidalCategory"

set_option maxHeartbeats 3200000 in
theorem solution
    {g d n : ℕ} (δ : Fin g → ℕ) {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    (hu : PolarisedAbelianScheme.IsOfType δ u)
    {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S))
    (x : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → SchemeHomOver t u.f)
    (hxK : ∀ y : SchemeHomOver t u.f, Polarisation.MemKernel u.f u.L u.pol t y →
      ∃ h : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), y = x h)
    {L : Type} [Field L] (ψ : K →+* L)
    (y : SchemeHomOver (Spec.map (CommRingCat.ofHom ψ) ≫ t) u.f)
    (hy : Polarisation.MemKernel u.f u.L u.pol (Spec.map (CommRingCat.ofHom ψ) ≫ t) y) :
    ∃ h : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), y.1 = Spec.map (CommRingCat.ofHom ψ) ≫ (x h).1 := by
  classical
  obtain ⟨φ', rfl⟩ := Spec.map_surjective t
  obtain ⟨S', _, _, _, _, x', -, -, hmem⟩ := hu
  haveI : Algebra.FiniteType S S' := inferInstance
  obtain ⟨sk, hsk⟩ := Module.FaithfullyFlat.exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed S' K φ'.hom

  have transp : ∀ {R : Type} [CommRing R] {t₁ t₂ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)} (e : t₁ = t₂)
      (z : SchemeHomOver t₁ u.f), Polarisation.MemKernel u.f u.L u.pol t₁ z →
        Polarisation.MemKernel u.f u.L u.pol t₂ ⟨z.1, e ▸ z.2⟩ := by
    intro R _ t₁ t₂ e z hz; subst e; exact hz

  letI algL : Algebra S' L := (ψ.comp sk).toAlgebra
  have eL : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map φ' = Spec.map (CommRingCat.ofHom ((algebraMap S' L).comp (algebraMap S S'))) := by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_assoc, hsk, ← Spec.map_comp]
    rfl
  obtain ⟨m, r, hr, hloc⟩ := (hmem L ⟨y.1, eL ▸ y.2⟩).mp (transp eL y hy)
  have hj : ∃ j, r j ≠ 0 := by
    by_contra h0
    push_neg at h0
    have hbot : Ideal.span (Set.range r) = ⊥ := Ideal.span_eq_bot.mpr (by rintro _ ⟨j, rfl⟩; exact h0 j)
    exact bot_ne_top (hbot.symm.trans hr)
  obtain ⟨j, hj⟩ := hj
  obtain ⟨h, hh⟩ := hloc j

  let gj : Localization.Away (r j) →+* L := IsLocalization.Away.lift (r j) (g := RingHom.id L) (isUnit_iff_ne_zero.mpr hj)
  have hgj : gj.comp (algebraMap L (Localization.Away (r j))) = RingHom.id L := IsLocalization.Away.lift_comp (r j) _
  have hyL : y.1 = Spec.map (CommRingCat.ofHom (algebraMap S' L)) ≫ (x' h).1 := by
    have := congrArg (fun q => Spec.map (CommRingCat.ofHom gj) ≫ q) hh
    simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at this
    rw [← RingHom.comp_assoc, hgj, RingHom.id_comp] at this
    simpa using this

  letI algK : Algebra S' K := sk.toAlgebra
  let z₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap S' K).comp (algebraMap S S')))) u.f :=
    ⟨Spec.map (CommRingCat.ofHom sk) ≫ (x' h).1, by
      rw [Category.assoc, (x' h).2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩
  have hz₁ : Polarisation.MemKernel u.f u.L u.pol _ z₁ := by
    refine (hmem K z₁).mpr ⟨1, fun _ => 1, ?_, fun j => ⟨h, ?_⟩⟩
    · simp
    · show Spec.map _ ≫ (Spec.map (CommRingCat.ofHom sk) ≫ (x' h).1) = _
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have eK : Spec.map (CommRingCat.ofHom ((algebraMap S' K).comp (algebraMap S S'))) = Spec.map φ' := by
    rw [RingHom.algebraMap_toAlgebra, hsk]; rfl
  obtain ⟨h', hh'⟩ := hxK ⟨z₁.1, eK ▸ z₁.2⟩ (transp eK z₁ hz₁)
  have hzK : Spec.map (CommRingCat.ofHom sk) ≫ (x' h).1 = (x h').1 := congrArg Subtype.val hh'
  refine ⟨h', ?_⟩
  rw [hyL, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hzK]

end S_AlgebraicGeometry_PolarisedAbelianScheme_exists_eq_comp_of_memKernel_of_isOfType_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_eq_comp_of_memKernel_of_isOfType_of_isAlgClosed (solution)
