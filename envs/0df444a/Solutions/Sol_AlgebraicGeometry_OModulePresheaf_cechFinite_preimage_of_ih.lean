-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.cechFinite_preimage_of_ih
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/91efaf28-cfa1-555f-b359-590fc005fa6f

import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.Finiteness.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_preimage_of_ih

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_preimage_of_ih.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.map_appLE Scheme.IdealSheafData.coe_support_vanishingIdeal Scheme.Hom Scheme.preimage_basicOpen Spec Scheme.IdealSheafData.range_subschemeι Scheme Scheme.IdealSheafData.vanishingIdeal IsClosedImmersion Scheme.IdealSheafData Scheme.Hom.appLE_eq_app OModulePresheaf OModulePresheaf.cechFinite_pushforward_iff"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "pushforward Hom CechFinite IsCoherent IsQuasicoherent SupportedIn res res_smul res_refl obj res_comp moduleSections cechFinite_pushforward_iff"
namespace Descend
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

variable {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (i : Z ⟶ V) [IsClosedImmersion i]
variable (F : OModulePresheaf (i ≫ π))

theorem isCoherent_pushforward (hFc : F.IsCoherent) : (pushforward π i F).IsCoherent := fun U => by
  letI : Module Γ(V, U.1) (F.obj (i ⁻¹ᵁ U.1)) := (pushforward π i F).moduleSections U.1
  letI : Algebra Γ(V, U.1) Γ(Z, i ⁻¹ᵁ U.1) := (i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  haveI : IsScalarTower Γ(V, U.1) Γ(Z, i ⁻¹ᵁ U.1) (F.obj (i ⁻¹ᵁ U.1)) :=
    ⟨fun a b x => by show ((i.appLE U.1 _ le_rfl).hom a * b) • x = _; rw [mul_smul]; rfl⟩
  haveI : Module.Finite Γ(V, U.1) Γ(Z, i ⁻¹ᵁ U.1) :=
    Module.Finite.of_surjective (Algebra.linearMap _ _) fun x => by
      obtain ⟨a, ha⟩ := i.app_surjective U.1 U.2 x
      exact ⟨a, show (i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl).hom a = x by rw [Scheme.Hom.appLE_eq_app]; exact ha⟩
  haveI := hFc ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩
  exact Module.Finite.trans (R := Γ(V, U.1)) Γ(Z, i ⁻¹ᵁ U.1) (F.obj (i ⁻¹ᵁ U.1))

theorem isQuasicoherent_pushforward (hFq : F.IsQuasicoherent) : (pushforward π i F).IsQuasicoherent := fun U f => by
  letI : Module Γ(V, U.1) (F.obj (i ⁻¹ᵁ U.1)) := (pushforward π i F).moduleSections U.1
  set g : Γ(Z, i ⁻¹ᵁ U.1) := (i.app U.1).hom f with hg_def
  have hbo : i ⁻¹ᵁ V.basicOpen f = Z.basicOpen g := Scheme.preimage_basicOpen i f
  obtain ⟨hs, ha⟩ := hFq ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ g
  have hpow : ∀ n (y : F.obj (i ⁻¹ᵁ U.1)),
      (f ^ n : Γ(V, U.1)) • y = (g ^ n : Γ(Z, i ⁻¹ᵁ U.1)) • y := fun n y => by
    show (i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl).hom (f ^ n) • y = _
    rw [map_pow, Scheme.Hom.appLE_eq_app]
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨n, y, hny⟩ := hs (F.res hbo.ge (show F.obj (i ⁻¹ᵁ V.basicOpen f) from x))
    refine ⟨n, y, ?_⟩
    have key := congrArg (F.res hbo.le) hny
    rw [← LinearMap.comp_apply, ← F.res_comp, F.res_smul,
      ← LinearMap.comp_apply (g := F.res hbo.ge), ← F.res_comp,
      LinearMap.congr_fun (F.res_refl _) x] at key
    show F.res _ y = (i.appLE (V.basicOpen f) (i ⁻¹ᵁ V.basicOpen f) le_rfl).hom
        ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n))
      • (show F.obj (i ⁻¹ᵁ V.basicOpen f) from x)
    refine key.trans ?_
    congr 1
    rw [← CommRingCat.comp_apply (f := V.presheaf.map _), Scheme.Hom.map_appLE,
      ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp, map_pow, map_pow]
    congr 1
  · refine (ha y ?_).imp fun n hn => (hpow n y).trans hn
    refine (LinearMap.congr_fun (F.res_comp hbo.ge ((Opens.map i.base).monotone (V.basicOpen_le f))) y).trans ?_
    exact (congrArg (F.res hbo.ge)
      (show F.res ((Opens.map i.base).monotone (V.basicOpen_le f)) y = 0 from hy)).trans (map_zero _)

theorem supportedIn_pushforward_image {Y' : Closeds Z} (hFs : F.SupportedIn Y') :
    (pushforward π i F).SupportedIn ⟨i.base '' Y', i.isClosedEmbedding.isClosedMap _ Y'.2⟩ := fun U hU =>
  hFs ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ (by
    refine Set.eq_empty_of_forall_notMem fun x ⟨hxU, hxY'⟩ => ?_
    exact Set.eq_empty_iff_forall_notMem.mp hU (i.base x) ⟨hxU, ⟨x, hxY', rfl⟩⟩)

end AlgebraicGeometry.OModulePresheaf.Descend

open AlgebraicGeometry.OModulePresheaf.Descend in

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (K : V.OrderedAffineCover)
    {Z₀ : TopologicalSpace.Closeds V}
    (ih : ∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' → G.CechFinite K)
    (F : OModulePresheaf ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ≫ π))
    (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent)
    (Y' : TopologicalSpace.Closeds (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme) (hY' : Y' < ⊤)
    (hFs : F.SupportedIn Y') :
    F.CechFinite (K.preimage (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι) := by
  have hrange : Set.range (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.base = (Z₀ : Set V) :=
    (Scheme.IdealSheafData.range_subschemeι _).trans (Scheme.IdealSheafData.coe_support_vanishingIdeal Z₀)
  let Y'' : Closeds V := ⟨(Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.base '' Y', (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.isClosedEmbedding.isClosedMap _ Y'.2⟩
  have hY''_lt : Y'' < Z₀ := by
    refine lt_of_le_of_ne (fun v ⟨_, _, hvx⟩ => show v ∈ (Z₀ : Set V) from hvx ▸ hrange ▸ Set.mem_range_self _)
      (fun heq => hY'.ne (SetLike.coe_injective (Set.eq_univ_of_forall fun x => ?_)))
    have hx : (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.base x ∈ (Y'' : Set V) :=
      heq.symm ▸ (show (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.base x ∈ (Z₀ : Set V) from hrange ▸ Set.mem_range_self x)
    obtain ⟨x', hx', hxx'⟩ := hx
    exact (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.isClosedEmbedding.injective hxx' ▸ hx'
  exact (AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_iff (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι F K).mp
    (ih Y'' hY''_lt _ (isCoherent_pushforward π _ F hFc) (isQuasicoherent_pushforward π _ F hFq)
      (supportedIn_pushforward_image π _ F hFs))

end S_AlgebraicGeometry_OModulePresheaf_cechFinite_preimage_of_ih
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_preimage_of_ih (solution)
