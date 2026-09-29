-- Prove2me | solution 1 for AlgebraicGeometry.isReduced_pullback_of_etale_of_forall_isReduced_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/877fc573-51a2-5b96-bd10-998ba855ea06

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isReduced_pullback_of_etale_of_forall_isReduced_pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace TorsorSmoothAux

variable {κ : Type u} [Field κ] [IsAlgClosed κ]

theorem locallyQuasiFinite_of_etale {E : Scheme.{u}} (fE : E ⟶ Spec (CommRingCat.of κ)) [Etale fE] :
    LocallyQuasiFinite fE := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have hEt : RingHom.Etale (fE.appLE U V e).hom := HasRingHomProperty.appLE (P := @Etale) fE inferInstance U V e
  algebraize [(fE.appLE U V e).hom]
  have : Algebra.Etale Γ(Spec (CommRingCat.of κ), U) Γ(E, V) := hEt
  change Algebra.QuasiFinite _ _
  infer_instance

theorem exists_openImmersion_specPoint {E : Scheme.{u}} (fE : E ⟶ Spec (CommRingCat.of κ)) [Etale fE] (e : E) :
    ∃ (y : Spec (CommRingCat.of κ) ⟶ E), IsOpenImmersion y ∧ y ≫ fE = 𝟙 _ ∧ e ∈ Set.range y.base := by
  classical
  haveI := locallyQuasiFinite_of_etale fE

  have hdisc : _root_.IsDiscrete (Set.univ : Set E) := by
    have h1 := fE.isDiscrete_preimage_singleton (IsLocalRing.closedPoint κ)
    have hS : fE.base ⁻¹' {IsLocalRing.closedPoint κ} = Set.univ :=
      Set.eq_univ_of_forall fun x => Subsingleton.elim _ _
    exact (congrArg _root_.IsDiscrete hS).mp h1
  haveI : DiscreteTopology E := isDiscrete_univ_iff.1 hdisc

  have hopen : IsOpen ({e} : Set E) := isOpen_discrete _
  obtain ⟨R, ι, hι, he, hsub⟩ := AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset
    (U := ⟨{e}, hopen⟩) (x := e) rfl
  haveI : IsOpenImmersion ι := hι
  have hrange : Set.range ι.base = {e} := Set.Subset.antisymm hsub (Set.singleton_subset_iff.2 he)

  have hsub1 : Subsingleton (Spec (CommRingCat.of R)) := by
    refine ⟨fun a b => ι.isOpenEmbedding.injective ?_⟩
    have ha : ι.base a ∈ ({e} : Set E) := hrange ▸ ⟨a, rfl⟩
    have hb : ι.base b ∈ ({e} : Set E) := hrange ▸ ⟨b, rfl⟩
    rw [Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
  obtain ⟨a₀, ha₀⟩ := he
  haveI : IsLocalRing R := by
    refine IsLocalRing.of_unique_max_ideal ⟨(a₀ : PrimeSpectrum R).asIdeal, ?_, ?_⟩
    ·
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (a₀ : PrimeSpectrum R).isPrime.ne_top
      have : (⟨M, hM.isPrime⟩ : PrimeSpectrum R) = a₀ := Subsingleton.elim (α := Spec (CommRingCat.of R)) _ _
      rw [← this]; exact hM
    · intro I hI
      have : (⟨I, hI.isPrime⟩ : PrimeSpectrum R) = a₀ := Subsingleton.elim (α := Spec (CommRingCat.of R)) _ _
      exact congrArg PrimeSpectrum.asIdeal this

  set ρ : CommRingCat.of κ ⟶ CommRingCat.of R := Spec.preimage (ι ≫ fE) with hρdef
  have hρ : Spec.map ρ = ι ≫ fE := Spec.map_preimage _
  have hρet : RingHom.Etale ρ.hom := by
    have : Etale (Spec.map ρ) := by rw [hρ]; infer_instance
    exact HasRingHomProperty.Spec_iff.mp this
  algebraize [ρ.hom]
  have : Algebra.Etale κ R := hρet
  have hbij : Function.Bijective (algebraMap κ R) :=
    Algebra.FormallyUnramified.bijective_of_isAlgClosed_of_isLocalRing κ R
  let eρ : κ ≃+* R := RingEquiv.ofBijective (algebraMap κ R) hbij
  let σ : CommRingCat.of R ⟶ CommRingCat.of κ := CommRingCat.ofHom eρ.symm.toRingHom
  have hρσ : ρ ≫ σ = 𝟙 _ := by
    apply CommRingCat.hom_ext; apply RingHom.ext; intro a
    change eρ.symm (algebraMap κ R a) = a
    exact eρ.symm_apply_apply a
  haveI : IsIso σ := by
    refine ⟨⟨ρ, ?_, hρσ⟩⟩
    apply CommRingCat.hom_ext; apply RingHom.ext; intro b
    change algebraMap κ R (eρ.symm b) = b
    exact eρ.apply_symm_apply b
  refine ⟨Spec.map σ ≫ ι, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, ← hρ, ← Spec.map_comp, hρσ, Spec.map_id]
  · refine ⟨(inv (Spec.map σ)).base a₀, ?_⟩
    change ((inv (Spec.map σ)) ≫ (Spec.map σ ≫ ι)).base a₀ = e
    rw [IsIso.inv_hom_id_assoc]
    exact ha₀

end TorsorSmoothAux

theorem solution
    {κ : Type u} [Field κ] [IsAlgClosed κ] {X Y E : Scheme.{u}}
    (f : X ⟶ Y) (g : E ⟶ Y) (fE : E ⟶ Spec (CommRingCat.of κ)) [Etale fE]
    (h : ∀ y : Spec (CommRingCat.of κ) ⟶ E, y ≫ fE = 𝟙 _ → IsReduced (pullback f (y ≫ g))) :
    IsReduced (pullback f g) := by
  classical
  choose y hyo hyf hye using TorsorSmoothAux.exists_openImmersion_specPoint fE

  let 𝒰 : E.OpenCover := Scheme.Cover.mkOfCovers E (fun _ => Spec (CommRingCat.of κ)) y
    (fun x => by obtain ⟨a, ha⟩ := hye x; exact ⟨x, a, ha⟩) (fun e => hyo e)
  haveI : ∀ i, IsReduced ((Scheme.Pullback.openCoverOfRight 𝒰 f g).X i) := fun i => h (y i) (hyf i)
  exact IsReduced.of_openCover (X := pullback f g) (Scheme.Pullback.openCoverOfRight 𝒰 f g)

end S_AlgebraicGeometry_isReduced_pullback_of_etale_of_forall_isReduced_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_isReduced_pullback_of_etale_of_forall_isReduced_pullback (solution)
