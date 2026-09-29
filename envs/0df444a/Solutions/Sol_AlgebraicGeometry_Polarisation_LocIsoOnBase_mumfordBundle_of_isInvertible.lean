-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.LocIsoOnBase.mumfordBundle_of_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/c8d2f05e-b05b-5f2e-b3be-3c7e05921552

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_mumfordBundle_of_isInvertible
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u v

namespace R2LocIso

variable {S : Type u} [CommRing S]

theorem locIsoOnBase_of_iso {S' : Type u} [CommRing S'] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S'))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

noncomputable def dualIso {X : Scheme.{u}} {M M' : X.Modules} (e : M ≅ M') :
    Scheme.Modules.dual M ≅ Scheme.Modules.dual M' :=
  ((MonoidalClosed.internalHom (C := X.Modules)).mapIso e.op.symm).app (𝟙_ X.Modules)

theorem locIsoOnBase_dual {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) {𝓛 𝓛' : A.Modules}
    (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓛' : Scheme.Modules.IsInvertible 𝓛') (h : LocIsoOnBase f 𝓛 𝓛') :
    LocIsoOnBase f (Scheme.Modules.dual 𝓛) (Scheme.Modules.dual 𝓛') := by
  intro s
  obtain ⟨U, hsU, ⟨e⟩⟩ := h s
  obtain ⟨d⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 (f ⁻¹ᵁ U).ι h𝓛
  obtain ⟨d'⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 (f ⁻¹ᵁ U).ι h𝓛'
  exact ⟨U, hsU, ⟨d ≪≫ dualIso e ≪≫ d'.symm⟩⟩

theorem locIsoOnBase_mumfordBundle {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {𝓛 𝓛' : A.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (h : LocIsoOnBase f 𝓛 𝓛') :
    LocIsoOnBase (pullback.fst f f ≫ f) (mumfordBundle f L 𝓛) (mumfordBundle f L 𝓛') := by
  have hd := locIsoOnBase_dual f h𝓛 h𝓛' h
  have h1 : LocIsoOnBase (pullback.fst f f ≫ f) ((Scheme.Modules.pullback (addMor f L)).obj 𝓛)
      ((Scheme.Modules.pullback (addMor f L)).obj 𝓛') :=
    LocIsoOnBase.pullback_of_comp_eq (pullback.fst f f ≫ f) (addMor f L) (𝟙 _)
      (by rw [Category.comp_id]; exact addMor_over f L) h
  have h2 : LocIsoOnBase (pullback.fst f f ≫ f) ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual 𝓛))
      ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual 𝓛')) :=
    LocIsoOnBase.pullback_of_comp_eq (pullback.fst f f ≫ f) (pullback.fst f f) (𝟙 _)
      (by rw [Category.comp_id]) hd
  have h3 : LocIsoOnBase (pullback.fst f f ≫ f) ((Scheme.Modules.pullback (pullback.snd f f)).obj (Scheme.Modules.dual 𝓛))
      ((Scheme.Modules.pullback (pullback.snd f f)).obj (Scheme.Modules.dual 𝓛')) :=
    LocIsoOnBase.pullback_of_comp_eq (pullback.fst f f ≫ f) (pullback.snd f f) (𝟙 _)
      (by rw [Category.comp_id]; exact pullback.condition.symm) hd
  exact LocIsoOnBase.tensor h1 (LocIsoOnBase.tensor h2 h3)

theorem geomFibreH0Finrank_eq_of_locIsoOnBase {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) {𝓛 𝓛' : A.Modules}
    (h : LocIsoOnBase f 𝓛 𝓛') (k : Type u) [Field k] (sk : S →+* k) :
    Scheme.Modules.geomFibreH0Finrank f 𝓛 k sk = Scheme.Modules.geomFibreH0Finrank f 𝓛' k sk := by
  classical

  let s : ↥(Spec (CommRingCat.of S)) := (⟨RingHom.ker sk, RingHom.ker_isPrime sk⟩ : PrimeSpectrum S)
  obtain ⟨U, hsU, ⟨e⟩⟩ := h s

  obtain ⟨V, ⟨r, rfl⟩, hsV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1
    (PrimeSpectrum.isBasis_basic_opens (R := S))) hsU
  have hr : sk r ≠ 0 := by
    have : r ∉ RingHom.ker sk := (PrimeSpectrum.mem_basicOpen r s).1 hsV
    rwa [RingHom.mem_ker] at this

  let S' : Type u := Localization.Away r
  let φ : S →+* S' := algebraMap S S'
  let ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom φ)
  let c := pullback.fst f ψ
  let f' := pullback.snd f ψ
  have hc : IsPullback c f' f ψ := IsPullback.of_hasPullback f ψ

  have hunit : IsUnit (sk r) := isUnit_iff_ne_zero.2 hr
  let sK : S' →+* k := IsLocalization.Away.lift r hunit
  have hsK : sK.comp φ = sk := IsLocalization.Away.lift_comp r hunit

  have hrange : Set.range (c : ↥(pullback f ψ) → ↥A) ⊆ Set.range ((f ⁻¹ᵁ U).ι : ↥(f ⁻¹ᵁ U) → ↥A) := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨a, rfl⟩
    show f.base (c.base a) ∈ U
    have h1 : f.base (c.base a) = ψ.base (f'.base a) := by
      exact congrArg (fun g => g.base a) (pullback.condition (f := f) (g := ψ))
    rw [h1]
    apply hVU
    rw [show ψ.base (f'.base a) = PrimeSpectrum.comap φ (f'.base a) by simp [ψ, Spec.map_base]; rfl]
    rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    intro hmem
    exact (f'.base a).2.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
      (IsLocalization.Away.algebraMap_isUnit r))
  let c' := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι c hrange
  have hc' : c' ≫ (f ⁻¹ᵁ U).ι = c := IsOpenImmersion.lift_fac _ _ _

  have ec : (Scheme.Modules.pullback c).obj 𝓛 ≅ (Scheme.Modules.pullback c).obj 𝓛' :=
    (Scheme.Modules.pullbackCongr hc'.symm).app 𝓛 ≪≫ ((Scheme.Modules.pullbackComp c' (f ⁻¹ᵁ U).ι).app 𝓛).symm ≪≫
      (Scheme.Modules.pullback c').mapIso e ≪≫ (Scheme.Modules.pullbackComp c' (f ⁻¹ᵁ U).ι).app 𝓛' ≪≫
      (Scheme.Modules.pullbackCongr hc').app 𝓛'
  have h1 := AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback φ f f' c hc 𝓛
    ((Scheme.Modules.pullback c).obj 𝓛') ec k sK
  have h2 := AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback φ f f' c hc 𝓛'
    ((Scheme.Modules.pullback c).obj 𝓛') (Iso.refl _) k sK
  rw [hsK] at h1 h2
  rw [← h1, h2]

end R2LocIso

open R2LocIso in
theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {𝓛 𝓛' : A.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (h : LocIsoOnBase f 𝓛 𝓛') :
    LocIsoOnBase (pullback.fst f f ≫ f) (mumfordBundle f L 𝓛) (mumfordBundle f L 𝓛') :=
  locIsoOnBase_mumfordBundle f L h𝓛 h𝓛' h

end S_AlgebraicGeometry_Polarisation_LocIsoOnBase_mumfordBundle_of_isInvertible
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_mumfordBundle_of_isInvertible (solution)
