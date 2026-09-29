-- Prove2me | solution 1 for AlgebraicGeometry.flat_of_forall_flat_pullback_snd_specMap_quotient_maximalIdeal_pow_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a834c7ca-8fa5-5e9b-a255-ba597f8be592

import Mathlib
import Theorems.Thm_Module_Flat_of_forall_flat_quotient_pow_tensor_of_map_le_jacobson
import Theorems.Thm_AlgebraicGeometry_flat_quotient_tensor_stalk_of_flat_pullback_snd_specMap_quotientMk
import Theorems.Thm_AlgebraicGeometry_Flat_of_forall_isClosed_flat_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_flat_of_forall_flat_pullback_snd_specMap_quotient_maximalIdeal_pow_of_isProper

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (hflat : ∀ n : ℕ,
      Flat (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))))) :
    Flat f := by
  classical
  haveI : CompactSpace ↥Z := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
  refine AlgebraicGeometry.Flat.of_forall_isClosed_flat_stalk f fun x hx => ?_
  letI alg : Algebra R ↑(Z.presheaf.stalk x) :=
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ Z.presheaf.germ ⊤ x trivial).hom).toAlgebra

  have hSpec : Z.fromSpecStalk x ≫ f =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ Z.presheaf.germ ⊤ x trivial) := by
    rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

  have hfx : (f x).asIdeal = (IsLocalRing.maximalIdeal ↑(Z.presheaf.stalk x)).comap (algebraMap R ↑(Z.presheaf.stalk x)) := by
    have h1 : f x = (Z.fromSpecStalk x ≫ f) (IsLocalRing.closedPoint ↑(Z.presheaf.stalk x)) := by
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint]
    rw [h1, hSpec, Spec.map_apply]
    rfl

  have hmax : (f x).asIdeal = IsLocalRing.maximalIdeal R := by
    apply IsLocalRing.eq_maximalIdeal
    rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    have := f.isClosedMap _ hx
    rwa [Set.image_singleton] at this
  haveI : IsNoetherianRing ↑(Z.presheaf.stalk x) := inferInstance
  refine Module.Flat.of_forall_flat_quotient_pow_tensor_of_map_le_jacobson (IsLocalRing.maximalIdeal R) ?_ ?_
  ·
    refine le_trans ?_ (IsLocalRing.maximalIdeal_le_jacobson _)
    rw [Ideal.map_le_iff_le_comap, ← hfx, hmax]
  · intro n
    cases n with
    | zero =>
      haveI : Subsingleton (R ⧸ IsLocalRing.maximalIdeal R ^ 0) :=
        Ideal.Quotient.subsingleton_iff.mpr ((pow_zero _).trans Ideal.one_eq_top)
      haveI := Module.subsingleton (R ⧸ IsLocalRing.maximalIdeal R ^ 0)
        ((R ⧸ IsLocalRing.maximalIdeal R ^ 0) ⊗[R] ↑(Z.presheaf.stalk x))
      infer_instance
    | succ n =>
      haveI := hflat n
      exact AlgebraicGeometry.flat_quotient_tensor_stalk_of_flat_pullback_snd_specMap_quotientMk
        (IsLocalRing.maximalIdeal R ^ (n + 1)) f x

end S_AlgebraicGeometry_flat_of_forall_flat_pullback_snd_specMap_quotient_maximalIdeal_pow_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_flat_of_forall_flat_pullback_snd_specMap_quotient_maximalIdeal_pow_of_isProper (solution)
