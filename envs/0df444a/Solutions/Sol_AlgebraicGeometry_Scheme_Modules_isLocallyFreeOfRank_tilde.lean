-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_tilde
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/81ee1ad7-32e7-5ea6-b08d-ba9d0a9ac5bc

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_ModulesTildePullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_tilde

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_tilde.AlgebraicGeometry Opposite TensorProduct"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsOpenImmersion.isoOfRangeEq_inv_fac Scheme.Modules.pullback Spec Spec.map Scheme tildeFinsupp pullbackSpecIso basicOpenIsoSpecAway IsOpenImmersion Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId tilde.functor Scheme.Modules tilde Scheme.Modules.pullbackComp Scheme.Modules.IsLocallyFreeOfRank tilde.pullbackSpecIso"
p2m_open "AlgebraicGeometry"

theorem free_finite_finrank_of_algebra_eq {A S : Type u} [CommRing A] [CommRing S]
    (M : Type u) [AddCommGroup M] [Module A M] (n : ℕ) (i₁ i₂ : Algebra A S) (h : i₁ = i₂)
    (H : letI := i₁;
      Module.Free S (S ⊗[A] M) ∧ Module.Finite S (S ⊗[A] M) ∧ Module.finrank S (S ⊗[A] M) = n) :
    letI := i₂;
      Module.Free S (S ⊗[A] M) ∧ Module.Finite S (S ⊗[A] M) ∧ Module.finrank S (S ⊗[A] M) = n := by
  subst h; exact H

theorem free_finite_finrank_baseChange_away {R : Type u} [CommRing R] (P : Type u)
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P] (n : ℕ)
    (hrk : ∀ (K : Type u) [Field K] [Algebra R K], Module.finrank K (K ⊗[R] P) = n)
    (r : R) (p : PrimeSpectrum R) (hr : r ∈ p.asIdeal.primeCompl)
    (hfree : Module.Free (Localization (.powers r)) (LocalizedModule (.powers r) P)) :
    Module.Free (Localization.Away r) (Localization.Away r ⊗[R] P) ∧
      Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] P) ∧
      Module.finrank (Localization.Away r) (Localization.Away r ⊗[R] P) = n := by
  have hF : Module.Free (Localization.Away r) (Localization.Away r ⊗[R] P) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (.powers r) P)
  refine ⟨hF, inferInstance, ?_⟩

  have hp : p ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) :=
    show r ∉ p.asIdeal from hr
  rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r] at hp
  obtain ⟨q, hq⟩ := hp
  have h1 : Module.rankAtStalk (Localization.Away r ⊗[R] P) q =
      Module.finrank (Localization.Away r) (Localization.Away r ⊗[R] P) := by
    simpa using congrFun (Module.rankAtStalk_eq_finrank_of_free
      (R := Localization.Away r) (M := Localization.Away r ⊗[R] P)) q
  rw [← h1, Module.rankAtStalk_baseChange, hq, Module.rankAtStalk_eq]
  exact hrk _

noncomputable def tildeIsoFreeOfFinrankEq {S : CommRingCat.{u}} [Nontrivial S] (N : ModuleCat.{u} S)
    [Module.Free S N] [Module.Finite S N] {n : ℕ} (hn : Module.finrank S N = n) :
    tilde N ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n)) :=
  (tilde.functor S).mapIso
      (((Module.finBasisOfFinrankEq S N hn).reindex Equiv.ulift.{u, 0}.symm).repr.toModuleIso) ≪≫
    tildeFinsupp (ULift.{u} (Fin n))

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback basicOpen Modules.pullbackCongr Modules.pullbackId Modules Opens Modules.pullbackComp Modules.IsLocallyFreeOfRank" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback pullbackCongr pullbackId pullbackComp IsLocallyFreeOfRank" end Scheme.Modules
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in

theorem Scheme.Modules.opensMap_final'' {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in

noncomputable def Scheme.Modules.pullbackObjFreeIso' {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.free.{u} I) ≅ SheafOfModules.free.{u} I :=
  haveI := Scheme.Modules.opensMap_final'' f
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in

noncomputable def Scheme.Modules.isoFreeOfIsoPullback {U Y : Scheme.{u}} (e : Y ≅ U) (M : U.Modules)
    (I : Type u) (h : (Scheme.Modules.pullback e.hom).obj M ≅ SheafOfModules.free.{u} I) :
    M ≅ SheafOfModules.free.{u} I :=
  (Scheme.Modules.pullbackId U).symm.app M ≪≫
    (Scheme.Modules.pullbackCongr (show 𝟙 U = e.inv ≫ e.hom by simp)).app M ≪≫
    (Scheme.Modules.pullbackComp e.inv e.hom).symm.app M ≪≫
    (Scheme.Modules.pullback e.inv).mapIso h ≪≫
    Scheme.Modules.pullbackObjFreeIso' e.inv I

set_option backward.isDefEq.respectTransparency false in

theorem _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_tilde.solution {R : CommRingCat.{u}} (P : ModuleCat.{u} R)
    [Module.Finite R P] [Module.Projective R P] (n : ℕ)
    (hrk : ∀ (K : Type u) [Field K] [Algebra R K], Module.finrank K (K ⊗[R] P) = n) :
    Scheme.Modules.IsLocallyFreeOfRank n (tilde P) := by
  classical
  haveI : Module.FinitePresentation R P := Module.finitePresentation_of_projective R P
  refine ⟨fun p => ?_⟩

  haveI : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl P) := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P)
    (Localization.AtPrime p.asIdeal)
  haveI : Nontrivial (Localization.Away (r : R)) :=
    (IsLocalization.map (M := .powers r) (T := p.asIdeal.primeCompl) (Localization.AtPrime p.asIdeal)
      (RingHom.id _) (Submonoid.powers_le.mpr hr)).domain_nontrivial
  obtain ⟨hF, hFin, hrank⟩ := free_finite_finrank_baseChange_away P n hrk r p hr hfree

  let S : CommRingCat.{u} := .of (Localization.Away (r : R))
  let φ : R ⟶ S := CommRingCat.ofHom (algebraMap R (Localization.Away (r : R)))
  obtain ⟨hF', hFin', hrank'⟩ := free_finite_finrank_of_algebra_eq (A := R) (S := Localization.Away (r : R))
    P n inferInstance φ.hom.toAlgebra (Algebra.algebra_ext _ _ fun _ => rfl) ⟨hF, hFin, hrank⟩
  haveI : Module.Free S ((ModuleCat.extendScalars φ.hom).obj P) := hF'
  haveI : Module.Finite S ((ModuleCat.extendScalars φ.hom).obj P) := hFin'
  have hn : Module.finrank S ((ModuleCat.extendScalars φ.hom).obj P) = n := hrank'
  haveI : Nontrivial S := inferInstanceAs (Nontrivial (Localization.Away (r : R)))
  refine ⟨PrimeSpectrum.basicOpen r, (show r ∉ p.asIdeal from hr), ⟨?_⟩⟩
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let e : (U : Scheme.{u}) ≅ Spec S := basicOpenIsoSpecAway (R := R) r
  have he : e.inv ≫ U.ι = Spec.map φ := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  refine Scheme.Modules.isoFreeOfIsoPullback e.symm _ _ ?_
  exact (Scheme.Modules.pullbackComp e.inv U.ι).app (tilde P) ≪≫
    (Scheme.Modules.pullbackCongr he).app (tilde P) ≪≫
    tilde.pullbackSpecIso φ P ≪≫
    tildeIsoFreeOfFinrankEq ((ModuleCat.extendScalars φ.hom).obj P) hn

#print axioms solution

end AlgebraicGeometry

end S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_tilde
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_tilde (solution)
