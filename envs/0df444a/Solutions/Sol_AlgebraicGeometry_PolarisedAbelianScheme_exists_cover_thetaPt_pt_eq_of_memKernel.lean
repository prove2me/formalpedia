-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.exists_cover_thetaPt_pt_eq_of_memKernel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/e0460a38-8b57-5e1a-b602-f1206d73cd1c

import Mathlib
import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Theorems.Thm_AlgebraicGeometry_Polarisation_isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit_of_commRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_cover_thetaPt_pt_eq_of_memKernel
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

namespace ThetaKer

open AlgebraicGeometry.Scheme.Modules

theorem not_mem_specMap_away {R : Type} [CommRing R] (r : R) (x : Spec (CommRingCat.of (Localization.Away r))) :
    r ∉ ((Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))).base x).asIdeal := by
  show r ∉ Ideal.comap (algebraMap R (Localization.Away r)) x.asIdeal
  intro h
  exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit r))

theorem exists_finset_span_eq_top {R : Type} [CommRing R] (rr : PrimeSpectrum R → R) (hrr : ∀ p, rr p ∉ p.asIdeal) :
    ∃ T : Finset R, (↑T : Set R) ⊆ Set.range rr ∧ Ideal.span (↑T : Set R) = ⊤ := by
  classical
  have htop : Ideal.span (Set.range rr) = ⊤ := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    exact hrr ⟨M, hM.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  have h1 : (1 : R) ∈ Ideal.span (Set.range rr) := by rw [htop]; trivial
  obtain ⟨T, hT, h1T⟩ := Submodule.mem_span_finite_of_mem_span h1
  exact ⟨T, hT, (Ideal.eq_top_iff_one _).2 h1T⟩

theorem exists_cover_of_locallyIsoOver {X : Scheme.{0}} {R : Type} [CommRing R] (q : X ⟶ Spec (CommRingCat.of R))
    (M M' : X.Modules) (h : Scheme.Modules.LocallyIsoOver q M M') :
    ∃ (m : ℕ) (r : Fin m → R), Ideal.span (Set.range r) = ⊤ ∧ ∀ j, ∃ U : (Spec (CommRingCat.of R)).Opens,
      (∀ x : Spec (CommRingCat.of R), r j ∉ x.asIdeal → x ∈ U) ∧
      Nonempty ((Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M') := by
  classical
  have hbasic : ∀ τ : Spec (CommRingCat.of R), ∃ (U : (Spec (CommRingCat.of R)).Opens) (r : R),
      r ∉ τ.asIdeal ∧ (∀ x : Spec (CommRingCat.of R), r ∉ x.asIdeal → x ∈ U) ∧
      Nonempty ((Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M') := by
    intro τ
    obtain ⟨U, hτU, hiso⟩ := h τ
    obtain ⟨V, ⟨r, rfl⟩, hV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens) hτU
    exact ⟨U, r, hV, fun x hx => hVU hx, hiso⟩
  choose Uτ rτ hrτ hrU hisoτ using hbasic
  obtain ⟨T, hT, hTtop⟩ := exists_finset_span_eq_top rτ hrτ
  have hpre : ∀ j : Fin T.card, ∃ τ, rτ τ = (T.equivFin.symm j).1 := fun j => hT (T.equivFin.symm j).2
  choose τj hτj using hpre
  refine ⟨T.card, fun j => (T.equivFin.symm j).1, ?_, fun j => ⟨Uτ (τj j), fun x hx => hrU (τj j) x (by rw [hτj j]; exact hx), hisoτ (τj j)⟩⟩
  have : Set.range (fun j : Fin T.card => (T.equivFin.symm j).1) = (↑T : Set R) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩; exact (T.equivFin.symm j).2
    · intro hx; exact ⟨T.equivFin ⟨x, hx⟩, by simp⟩
  rw [this, hTtop]

theorem nonempty_iso_pullback_of_forall_mem {X Y T : Scheme.{0}} (q : X ⟶ T) (U : T.Opens) {M M' : X.Modules}
    (e : (Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M')
    (g : Y ⟶ X) (hg : ∀ y : Y, q.base (g.base y) ∈ U) :
    Nonempty ((Scheme.Modules.pullback g).obj M ≅ (Scheme.Modules.pullback g).obj M') := by
  have hsub : Set.range g.base ⊆ Set.range (q ⁻¹ᵁ U).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hg y
  let g' := IsOpenImmersion.lift (q ⁻¹ᵁ U).ι g hsub
  have hg' : g' ≫ (q ⁻¹ᵁ U).ι = g := IsOpenImmersion.lift_fac _ _ _
  exact ⟨((pullbackCongr hg').app M).symm ≪≫ ((pullbackComp g' (q ⁻¹ᵁ U).ι).app M).symm ≪≫
    (Scheme.Modules.pullback g').mapIso e ≪≫ (pullbackComp g' (q ⁻¹ᵁ U).ι).app M' ≪≫ (pullbackCongr hg').app M'⟩

end ThetaKer

open ThetaKer AlgebraicGeometry.Scheme.Modules in
theorem solution
    {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (y : SchemeHomOver t u.f) (hy : Polarisation.MemKernel u.f u.L u.pol t y) :
    ∃ (m : ℕ) (r : Fin m → R), Ideal.span (Set.range r) = ⊤ ∧
      ∀ j : Fin m, ∃ θ : ThetaPt u.f u.L u.pol
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (r j)))) ≫ t),
        (θ.pt).1 = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (r j)))) ≫ y.1 := by
  classical
  have hstab : Scheme.Modules.LocallyIsoOver (pullback.snd u.f t)
      ((Scheme.Modules.pullback (u.L.mulRight t y)).obj u.pol) ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol) :=
    (AlgebraicGeometry.Polarisation.isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit_of_commRing
      S u.f u.L u.pol u.pol_isInvertible R t y).mpr hy
  obtain ⟨m, r, hspan, hU⟩ := exists_cover_of_locallyIsoOver _ _ _ hstab
  refine ⟨m, r, hspan, fun j => ?_⟩
  obtain ⟨U, hrU, ⟨e⟩⟩ := hU j

  let loc := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (r j))))
  let tr := loc ≫ t
  let yr : SchemeHomOver tr u.f := schemeHomOverComp loc rfl y
  let φ : pullback u.f tr ⟶ pullback u.f t :=
    pullback.lift (pullback.fst u.f tr) (pullback.snd u.f tr ≫ loc) (by rw [pullback.condition, Category.assoc])
  have hφ1 : φ ≫ pullback.fst u.f t = pullback.fst u.f tr := pullback.lift_fst _ _ _
  have hφ2 : φ ≫ pullback.snd u.f t = pullback.snd u.f tr ≫ loc := pullback.lift_snd _ _ _
  have hφU : ∀ a : ↥(pullback u.f tr), (pullback.snd u.f t).base (φ.base a) ∈ U := by
    intro a
    have : a ∈ (φ ≫ pullback.snd u.f t) ⁻¹ᵁ U := by
      rw [hφ2]
      exact hrU _ (not_mem_specMap_away (r j) _)
    exact this
  obtain ⟨E1⟩ := nonempty_iso_pullback_of_forall_mem (pullback.snd u.f t) U e φ hφU

  have hφt : φ ≫ (pullback.snd u.f t ≫ t) = pullback.snd u.f tr ≫ tr := by
    rw [← Category.assoc, hφ2, Category.assoc]
  have hmr : u.L.mulRight tr yr = φ ≫ u.L.mulRight t y := by
    have hnat := u.L.mul_natural (pullback.snd u.f t ≫ t) (pullback.snd u.f tr ≫ tr) φ hφt (u.L.fstPoint t) (u.L.sndPoint t y)
    have h1 : schemeHomOverComp φ hφt (u.L.fstPoint t) = u.L.fstPoint tr := Subtype.ext hφ1
    have h2 : schemeHomOverComp φ hφt (u.L.sndPoint t y) = u.L.sndPoint tr yr :=
      Subtype.ext (by
        show φ ≫ pullback.snd u.f t ≫ y.1 = pullback.snd u.f tr ≫ (loc ≫ y.1)
        rw [← Category.assoc, hφ2, Category.assoc])
    rw [h1, h2] at hnat
    exact (congrArg Subtype.val hnat).symm
  have htrans : translate u.f u.L tr yr ≫ pullback.fst u.f tr = u.L.mulRight tr yr := pullback.lift_fst _ _ _

  refine ⟨⟨yr, ?_⟩, rfl⟩
  exact (pullbackComp (translate u.f u.L tr yr) (pullback.fst u.f tr)).app u.pol ≪≫
    (pullbackCongr (htrans.trans hmr)).app u.pol ≪≫
    ((pullbackComp φ (u.L.mulRight t y)).app u.pol).symm ≪≫ E1 ≪≫
    (pullbackComp φ (pullback.fst u.f t)).app u.pol ≪≫ (pullbackCongr hφ1).app u.pol

end S_AlgebraicGeometry_PolarisedAbelianScheme_exists_cover_thetaPt_pt_eq_of_memKernel
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_cover_thetaPt_pt_eq_of_memKernel (solution)
