-- Prove2me | solution 1 for AlgebraicGeometry.valuation_sub_counit_lt_one_of_isClosedImmersion_of_specMap_comp_eq_zeroSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ad4fdebf-732a-56bf-bcc2-4ccd729c2459

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_valuation_sub_counit_lt_one_of_isClosedImmersion_of_specMap_comp_eq_zeroSection

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open CategoryTheory AlgebraicGeometry NeronModelInfra

theorem solution
    (A : Type) [CommRing A] [Algebra A (AlgebraicClosure ℚ)]

    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (zero : Spec (CommRingCat.of A) ⟶ X) (hzero : zero ≫ f = 𝟙 _)
    (B : Type) [CommRing B] [Bialgebra A B]
    (c : Spec (CommRingCat.of B) ⟶ X) [IsClosedImmersion c]
    (hc : c ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (hunit : Spec.map (CommRingCat.ofHom ((Bialgebra.counitAlgHom A B : B →ₐ[A] A) : B →+* A)) ≫ c = zero)

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (k : Type) [Field k] [Algebra A k] (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)
    (hπk : RingHom.ker πk = IsLocalRing.maximalIdeal ↥Pl)

    (g : B →ₐ[A] AlgebraicClosure ℚ) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) f)
    (hz : Spec.map (CommRingCat.ofHom ((g : B →ₐ[A] AlgebraicClosure ℚ) : B →+* AlgebraicClosure ℚ)) ≫ c =
      Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1)
    (hred : Spec.map (CommRingCat.ofHom πk) ≫ z.1 = Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ zero) :
    ∀ b : B, Pl.valuation (g b - algebraMap A (AlgebraicClosure ℚ) (Coalgebra.counit (R := A) b)) < 1 := by
  intro b
  classical

  let q := Limits.pullback.snd c z.1
  let w := Limits.pullback.lift (Spec.map (CommRingCat.ofHom ((g : B →ₐ[A] AlgebraicClosure ℚ) : B →+* AlgebraicClosure ℚ)))
    (Spec.map (CommRingCat.ofHom Pl.subtype)) hz
  have hwq : w ≫ q = Spec.map (CommRingCat.ofHom Pl.subtype) := Limits.pullback.lift_snd _ _ _
  have hker : Scheme.Hom.ker (Spec.map (CommRingCat.ofHom Pl.subtype)) = ⊥ := by
    rw [Scheme.ker_of_isAffine]
    have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom Pl.subtype)
    have heq : (Spec.map (CommRingCat.ofHom Pl.subtype)).appTop =
        (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom Pl.subtype ≫ (Scheme.ΓSpecIso _).inv := by
      rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hbot : RingHom.ker (Spec.map (CommRingCat.ofHom Pl.subtype)).appTop.hom = ⊥ := by
      rw [RingHom.ker_eq_bot_iff_eq_zero]
      intro x hx
      rw [heq] at hx
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at hx
      have h1 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).hom.hom hx
      rw [map_zero, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply] at h1
      have h2 : (Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).hom.hom x = 0 := Subtype.ext h1
      have h3 := congrArg (Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv.hom h2
      rwa [map_zero, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at h3
    rw [hbot]
    exact Scheme.IdealSheafData.ext (funext fun U => by
      rw [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_bot]; rfl)
  have hqker : Scheme.Hom.ker q = ⊥ := by
    rw [← le_bot_iff, ← hker, ← hwq]
    exact Scheme.Hom.le_ker_comp w q
  haveI : IsIso q := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hqker
  let w' : Spec (CommRingCat.of ↥Pl) ⟶ Spec (CommRingCat.of B) := inv q ≫ Limits.pullback.fst c z.1
  have hw' : w' ≫ c = z.1 := by
    change (inv q ≫ Limits.pullback.fst c z.1) ≫ c = z.1
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

  let gt : CommRingCat.of B ⟶ CommRingCat.of ↥Pl := Spec.preimage w'
  have hgt : Spec.map gt = w' := Spec.map_preimage w'

  have h1 : gt ≫ CommRingCat.ofHom Pl.subtype =
      CommRingCat.ofHom ((g : B →ₐ[A] AlgebraicClosure ℚ) : B →+* AlgebraicClosure ℚ) := by
    rw [← Spec.map_inj, Spec.map_comp, ← cancel_mono c, Category.assoc, hgt, hw', hz]

  have h2 : gt ≫ CommRingCat.ofHom πk =
      CommRingCat.ofHom ((Bialgebra.counitAlgHom A B : B →ₐ[A] A) : B →+* A) ≫ CommRingCat.ofHom (algebraMap A k) := by
    rw [← Spec.map_inj, Spec.map_comp, Spec.map_comp, ← cancel_mono c]
    simp only [Category.assoc]
    rw [hgt, hw', hred, hunit]

  have hsub : ((gt.hom b : ↥Pl) : AlgebraicClosure ℚ) = g b := by
    have := congrArg (fun φ : CommRingCat.of B ⟶ CommRingCat.of (AlgebraicClosure ℚ) => φ.hom b) h1
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
    exact this
  have hπ : πk (gt.hom b) = algebraMap A k (Coalgebra.counit (R := A) b) := by
    have := congrArg (fun φ : CommRingCat.of B ⟶ CommRingCat.of k => φ.hom b) h2
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
    exact this
  have hmem : gt.hom b - ρ (Coalgebra.counit (R := A) b) ∈ IsLocalRing.maximalIdeal ↥Pl := by
    rw [← hπk, RingHom.mem_ker, map_sub, hπ, hAlgk, RingHom.comp_apply, sub_self]
  have hval := (ValuationSubring.valuation_lt_one_iff Pl _).1 hmem
  have hcoe : g b - algebraMap A (AlgebraicClosure ℚ) (Coalgebra.counit (R := A) b) =
      ((gt.hom b - ρ (Coalgebra.counit (R := A) b) : ↥Pl) : AlgebraicClosure ℚ) := by
    rw [← hρ, RingHom.comp_apply, ← hsub]
    rfl
  rw [hcoe]
  exact hval

end S_AlgebraicGeometry_valuation_sub_counit_lt_one_of_isClosedImmersion_of_specMap_comp_eq_zeroSection
end P2MW
export P2MW.S_AlgebraicGeometry_valuation_sub_counit_lt_one_of_isClosedImmersion_of_specMap_comp_eq_zeroSection (solution)
