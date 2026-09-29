-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_of_locIsoOnBase_of_kernelIsTwoTorsion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/cd2f58a7-482b-55a1-8326-434e5d08cf0d

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_iff_and_kernelTrivial_iff_of_iso
import Theorems.Thm_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_baseChange_of_isInvertible
import Theorems.Thm_AlgebraicGeometry_Polarisation_KernelIsTwoTorsion_of_forall_away_of_isInvertible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_of_locIsoOnBase_of_kernelIsTwoTorsion
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

noncomputable section

namespace K2TRoot

theorem baseChange_mul_comp_fst {S S' : Type} [CommRing S] [CommRing S'] (ι : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' (pullback.snd f ι))
    (hP : (P.1 ≫ pullback.fst f ι) ≫ f = t' ≫ ι) (hQ : (Q.1 ≫ pullback.fst f ι) ≫ f = t' ≫ ι) :
    ((L.baseChange ι).mul t' P Q).1 ≫ pullback.fst f ι = (L.mul (t' ≫ ι) ⟨P.1 ≫ pullback.fst f ι, hP⟩ ⟨Q.1 ≫ pullback.fst f ι, hQ⟩).1 :=
  congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul ι L t' P Q)

section brick

variable {S' : Type} [CommRing S'] {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of S')) (L' : RelativeGroupLaw S' f')

theorem mem_basicOpen_of_away (r : S') (y : ↥(Spec (CommRingCat.of (Localization.Away r)))) :
    (Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away r)))).base y ∈ PrimeSpectrum.basicOpen r := by
  have h : Set.range (Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away r)))).base =
      ((PrimeSpectrum.basicOpen r : TopologicalSpace.Opens (PrimeSpectrum S')) : Set (PrimeSpectrum S')) :=
    (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r :)
  have hy : (Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away r)))).base y ∈
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away r)))).base := ⟨y, rfl⟩
  rw [h] at hy
  exact hy

theorem range_fst_subset (r : S') (U : (Spec (CommRingCat.of S')).Opens)
    (hrU : ∀ x : ↥(Spec (CommRingCat.of S')), x ∈ PrimeSpectrum.basicOpen r → x ∈ U) :
    Set.range (pullback.fst f' (Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away r))))).base ⊆
      Set.range (f' ⁻¹ᵁ U).ι.base := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  change f'.base ((pullback.fst f' _).base x) ∈ U
  apply hrU
  have hx : f'.base ((pullback.fst f' (Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away r))))).base x) =
      (Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away r)))).base
        ((pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away r))))).base x) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  rw [hx]
  exact mem_basicOpen_of_away r _

theorem nonempty_iso_pullback_fst_of_iso_restrict (r : S') (U : (Spec (CommRingCat.of S')).Opens)
    (hrU : ∀ x : ↥(Spec (CommRingCat.of S')), x ∈ PrimeSpectrum.basicOpen r → x ∈ U) (M N : A'.Modules)
    (e : (Scheme.Modules.pullback (f' ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (f' ⁻¹ᵁ U).ι).obj N) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst f' (Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away r)))))).obj M ≅
      (Scheme.Modules.pullback (pullback.fst f' (Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away r)))))).obj N) := by
  let g := pullback.fst f' (Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away r))))
  let l := IsOpenImmersion.lift (f' ⁻¹ᵁ U).ι g (range_fst_subset f' r U hrU)
  have hl : l ≫ (f' ⁻¹ᵁ U).ι = g := IsOpenImmersion.lift_fac _ _ _
  exact ⟨((Scheme.Modules.pullbackCongr hl).app M).symm ≪≫ ((Scheme.Modules.pullbackComp l _).app M).symm ≪≫
    (Scheme.Modules.pullback l).mapIso e ≪≫ (Scheme.Modules.pullbackComp l _).app N ≪≫ (Scheme.Modules.pullbackCongr hl).app N⟩

theorem kernelIsTwoTorsion_of_locIsoOnBase (M N : A'.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hN : Scheme.Modules.IsInvertible N) (h : LocIsoOnBase f' M N) (hK : KernelIsTwoTorsion f' L' N) :
    KernelIsTwoTorsion f' L' M := by
  classical

  have key : ∀ s : PrimeSpectrum S', ∃ r : S', s ∈ PrimeSpectrum.basicOpen r ∧
      ∃ U : (Spec (CommRingCat.of S')).Opens, (∀ x : ↥(Spec (CommRingCat.of S')), x ∈ PrimeSpectrum.basicOpen r → x ∈ U) ∧
        Nonempty ((Scheme.Modules.pullback (f' ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (f' ⁻¹ᵁ U).ι).obj N) := by
    intro s
    obtain ⟨U, hs, e⟩ := h s
    obtain ⟨_, ⟨r, rfl⟩, hsr, hrU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (show s ∈ (U : Set ↥(Spec (CommRingCat.of S'))) from hs) U.isOpen
    exact ⟨r, hsr, U, fun x hx => hrU hx, e⟩
  choose r hr U hrU e using key

  obtain ⟨t, ht⟩ := (isCompact_univ (X := PrimeSpectrum S')).elim_finite_subcover
    (fun s : PrimeSpectrum S' => ((PrimeSpectrum.basicOpen (r s) : TopologicalSpace.Opens (PrimeSpectrum S')) : Set (PrimeSpectrum S')))
    (fun s => (PrimeSpectrum.basicOpen (r s)).isOpen) (fun s _ => Set.mem_iUnion.2 ⟨s, hr s⟩)
  let ι : Fin t.card → PrimeSpectrum S' := fun i => (t.equivFin.symm i).1
  let r' : Fin t.card → S' := fun i => r (ι i)
  have hspan : Ideal.span (Set.range r') = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    refine top_le_iff.1 fun s _ => ?_
    obtain ⟨s₀, hs₀, hss₀⟩ : ∃ s₀ ∈ t, s ∈ ((PrimeSpectrum.basicOpen (r s₀) : TopologicalSpace.Opens (PrimeSpectrum S')) : Set (PrimeSpectrum S')) := by
      simpa only [Set.mem_iUnion, exists_prop] using ht (Set.mem_univ s)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨t.equivFin ⟨s₀, hs₀⟩, ?_⟩
    change s ∈ PrimeSpectrum.basicOpen (r (t.equivFin.symm (t.equivFin ⟨s₀, hs₀⟩)).1)
    rw [Equiv.symm_apply_apply]
    exact hss₀

  refine KernelIsTwoTorsion.of_forall_away_of_isInvertible f' L' r' hspan
    (fun i => pullback f' (Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away (r' i))))))
    (fun i => pullback.snd f' _) (fun i => pullback.fst f' _) (fun i => IsPullback.of_hasPullback _ _)
    (fun i => L'.baseChange _) (fun i {T} t' x y => baseChange_mul_comp_fst _ L' t' x y _ _) M hM fun i => ?_
  have hNi := kernelIsTwoTorsion_baseChange_of_isInvertible
    (Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away (r' i))))) f' L' N hN hK
  obtain ⟨ei⟩ := nonempty_iso_pullback_fst_of_iso_restrict f' (r' i) (U (ι i)) (hrU (ι i)) M N (e (ι i)).some
  exact (kernelIsTwoTorsion_iff_and_kernelTrivial_iff_of_iso (L'.baseChange _) _ _ ei).1.2 hNi

end brick

end K2TRoot

open K2TRoot in
theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (𝓛 𝓜 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (hloc : LocIsoOnBase f 𝓛 𝓜) (h : KernelIsTwoTorsion f L 𝓜) :
    KernelIsTwoTorsion f L 𝓛 :=
  K2TRoot.kernelIsTwoTorsion_of_locIsoOnBase f L 𝓛 𝓜 h𝓛 h𝓜 hloc h

end
end S_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_of_locIsoOnBase_of_kernelIsTwoTorsion
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_of_locIsoOnBase_of_kernelIsTwoTorsion (solution)
