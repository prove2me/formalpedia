-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.closedImmersionBySections_of_affine_openCover
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-07T19:33:07.16081+00:00
-- url     : https://prove2.me/submissions/d7801031-3561-4805-8bba-42003ea118bb

import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_closedImmersionBySections_of_forall_isPullback_away

universe u v

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory TopologicalSpace


namespace PhilipponFinitePrincipalRefinement

/-- A finite principal cover refining the actual given open cover of an
affine spectrum. The unit-ideal condition is derived from the cover. -/
theorem exists_refinement {R : Type u} [CommRing R]
    (𝒰 : Scheme.OpenCover.{v} (Spec (CommRingCat.of R))) :
    ∃ (k : ℕ) (r : Fin k → R) (idx : Fin k → 𝒰.I₀),
      Ideal.span (Set.range r) = ⊤ ∧
      ∀ j, PrimeSpectrum.basicOpen (r j) ≤ (𝒰.f (idx j)).opensRange := by
  classical
  have hx (x : Spec (CommRingCat.of R)) :
      ∃ r : R, x ∈ PrimeSpectrum.basicOpen r ∧
        PrimeSpectrum.basicOpen r ≤ (𝒰.f (𝒰.idx x)).opensRange := by
    obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hmem, hle⟩ := PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (𝒰.covers x) (𝒰.f (𝒰.idx x)).opensRange.isOpen
    exact ⟨r, hmem, hle⟩
  choose r hmem hle using hx
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover
    (fun x => (PrimeSpectrum.basicOpen (r x)).carrier)
    (fun x => (PrimeSpectrum.basicOpen (r x)).isOpen.mem_nhds (hmem x))
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  refine ⟨Fintype.card t, fun j => r (e j), fun j => 𝒰.idx (e j), ?_, fun j => hle (e j)⟩
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
  apply top_unique
  intro x _
  have hx : x ∈ ⋃ y ∈ t, (PrimeSpectrum.basicOpen (r y)).carrier := by
    rw [ht]
    trivial
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
  apply Opens.mem_iSup.mpr
  refine ⟨(Fintype.equivFin t) ⟨y, hy⟩, ?_⟩
  simp only [e, Equiv.symm_apply_apply]
  exact hxy

end PhilipponFinitePrincipalRefinement

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponProjectivePresentationBaseChange

theorem of_moduleIso {R : Type u} [CommRing R] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of R)} {M N : X.Modules} (e : M ≅ N)
    (h : Scheme.Modules.ClosedImmersionBySections M f) :
    Scheme.Modules.ClosedImmersionBySections N f := by
  obtain ⟨n, P, hP⟩ := h
  obtain ⟨Q, hQ, -⟩ := P.exists_of_iso e
  exact ⟨n, Q, hQ.symm ▸ hP⟩

theorem of_isPullback {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {X X' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    {f' : X' ⟶ Spec (CommRingCat.of A)} {p : X' ⟶ X}
    (sq : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    (M : X.Modules) (h : Scheme.Modules.ClosedImmersionBySections M f) :
    Scheme.Modules.ClosedImmersionBySections ((Scheme.Modules.pullback p).obj M) f' := by
  obtain ⟨n, P, hP⟩ := h
  obtain ⟨Q, -, -, hQ⟩ := P.exists_baseChange_of_isPullback sq
  exact ⟨n, Q, MorphismProperty.of_isPullback (P := @IsClosedImmersion) hQ hP⟩

def pullbackRestrictIso {X U V : Scheme.{u}} (M : X.Modules)
    (iU : U ⟶ X) (iV : V ⟶ X) (p : V ⟶ U)
    [IsOpenImmersion iU] [IsOpenImmersion iV] [IsOpenImmersion p]
    (hp : p ≫ iU = iV) :
    (Scheme.Modules.pullback p).obj (M.restrict iU) ≅ M.restrict iV :=
  ((Scheme.Modules.restrictFunctorIsoPullback p).app (M.restrict iU)).symm ≪≫
    ((Scheme.Modules.restrictFunctorComp p iU).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr hp).app M

end PhilipponProjectivePresentationBaseChange

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponProjectivePresentationBaseChange


namespace PhilipponProjectiveAtlasDescent

theorem on_affine_refinement {S D : Type u} [CommRing S] [CommRing D]
    {X U V : Scheme.{u}} [IsAffine U]
    {f : X ⟶ Spec (CommRingCat.of S)} (iU : U ⟶ Spec (CommRingCat.of S))
    (iV : V ⟶ X) (fV : V ⟶ U) [IsOpenImmersion iU] [IsOpenImmersion iV]
    (sq : IsPullback iV fV f iU) (M : X.Modules)
    (h : Scheme.Modules.ClosedImmersionBySections (M.restrict iV) (fV ≫ U.toSpecΓ))
    (r : Spec (CommRingCat.of D) ⟶ Spec (CommRingCat.of S)) [IsOpenImmersion r]
    (hr : Set.range r ⊆ Set.range iU) :
    Scheme.Modules.ClosedImmersionBySections (M.restrict (pullback.fst f r)) (pullback.snd f r) := by
  let t := IsOpenImmersion.lift iU r hr
  have ht : t ≫ iU = r := IsOpenImmersion.lift_fac iU r hr
  let p : pullback f r ⟶ V := sq.lift (pullback.fst f r) (pullback.snd f r ≫ t)
    (by rw [Category.assoc, ht, pullback.condition])
  have hp : p ≫ iV = pullback.fst f r := sq.lift_fst _ _ _
  have hpf : p ≫ fV = pullback.snd f r ≫ t := sq.lift_snd _ _ _
  have hsq : IsPullback p (pullback.snd f r) fV t := by
    have houter : IsPullback (p ≫ iV) (pullback.snd f r) f (t ≫ iU) := by
      rw [hp, ht]
      exact IsPullback.of_hasPullback f r
    exact houter.of_right hpf sq
  haveI : IsOpenImmersion (p ≫ iV) := hp.symm ▸ inferInstance
  haveI : IsOpenImmersion p := IsOpenImmersion.of_comp p iV
  let φ : Γ(U, ⊤) ⟶ CommRingCat.of D := Spec.preimage (t ≫ U.toSpecΓ)
  letI : Algebra Γ(U, ⊤) D := φ.hom.toAlgebra
  have hΓ : IsPullback p (pullback.snd f r) (fV ≫ U.toSpecΓ)
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(U, ⊤) D))) := by
    change IsPullback p (pullback.snd f r) (fV ≫ U.toSpecΓ) (Spec.map φ)
    dsimp only [φ]
    rw [Spec.map_preimage]
    exact hsq.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso U.toSpecΓ)
      (by simp) (by simp) (by simp) (by simp)
  exact of_moduleIso (pullbackRestrictIso M iV (pullback.fst f r) p hp)
    (of_isPullback hΓ (M.restrict iV) h)

/-- Descent of closed presentations of one invertible module from an
arbitrary affine open atlas of an affine base. All finite principal
localization data are constructed from that atlas. -/
theorem of_openCover {S : Type u} [CommRing S] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of S)) (hf : IsProper f)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (𝒰 : Scheme.OpenCover.{v} (Spec (CommRingCat.of S))) [∀ i, IsAffine (𝒰.X i)]
    (V : 𝒰.I₀ → Scheme.{u}) (iV : ∀ i, V i ⟶ X) (fV : ∀ i, V i ⟶ 𝒰.X i)
    [∀ i, IsOpenImmersion (iV i)]
    (sq : ∀ i, IsPullback (iV i) (fV i) f (𝒰.f i))
    (h : ∀ i, Scheme.Modules.ClosedImmersionBySections (M.restrict (iV i))
      (fV i ≫ (𝒰.X i).toSpecΓ)) : Scheme.Modules.ClosedImmersionBySections M f := by
  obtain ⟨k, r, idx, hr, hidx⟩ := PhilipponFinitePrincipalRefinement.exists_refinement 𝒰
  let B (j : Fin k) := Localization.Away (r j)
  let ρ (j : Fin k) : Spec (CommRingCat.of (B j)) ⟶ Spec (CommRingCat.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap S (B j)))
  have hρ (j : Fin k) : Set.range (ρ j) ⊆ Set.range (𝒰.f (idx j)) := by
    change Set.range (PrimeSpectrum.comap (algebraMap S (B j))) ⊆ _
    rw [PrimeSpectrum.localization_away_comap_range (B j) (r j)]
    exact hidx j
  have hlocal (j : Fin k) :
      Scheme.Modules.ClosedImmersionBySections (M.restrict (pullback.fst f (ρ j)))
        (pullback.snd f (ρ j)) :=
    on_affine_refinement (𝒰.f (idx j)) (iV (idx j)) (fV (idx j)) (sq (idx j)) M
      (h (idx j)) (ρ j) (hρ j)
  exact Scheme.Modules.closedImmersionBySections_of_forall_isPullback_away r hr B f
    (fun j => pullback.snd f (ρ j)) (fun j => pullback.fst f (ρ j))
    (fun j => IsPullback.of_hasPullback f (ρ j)) hf M hM
    (fun j => M.restrict (pullback.fst f (ρ j)))
    (fun j => ((Scheme.Modules.restrictFunctorIsoPullback (pullback.fst f (ρ j))).app M).symm)
    hlocal

end PhilipponProjectiveAtlasDescent

end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem solution {S : Type u} [CommRing S] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of S)) (hf : IsProper f)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (𝒰 : Scheme.OpenCover.{v} (Spec (CommRingCat.of S))) [∀ i, IsAffine (𝒰.X i)]
    (V : 𝒰.I₀ → Scheme.{u}) (iV : ∀ i, V i ⟶ X) (fV : ∀ i, V i ⟶ 𝒰.X i)
    [∀ i, IsOpenImmersion (iV i)]
    (sq : ∀ i, IsPullback (iV i) (fV i) f (𝒰.f i))
    (h : ∀ i, Scheme.Modules.ClosedImmersionBySections (M.restrict (iV i))
      (fV i ≫ (𝒰.X i).toSpecΓ)) : Scheme.Modules.ClosedImmersionBySections M f := by
  exact PhilipponProjectiveAtlasDescent.of_openCover f hf M hM 𝒰 V iV fV sq h
