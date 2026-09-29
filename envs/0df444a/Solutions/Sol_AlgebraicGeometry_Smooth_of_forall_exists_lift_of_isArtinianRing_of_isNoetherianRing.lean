-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f3347e35-ee3d-53d3-a505-9a7409bc74a5

import Mathlib
import Theorems.Thm_MvPolynomial_formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem
import Theorems.Thm_AlgebraicGeometry_Scheme_forall_exists_algHom_lift_of_forall_exists_lift_of_isOpenImmersion_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_chart_formallySmooth_stalkMap_of_formallySmooth_localization
import Theorems.Thm_MvPolynomial_exists_faithfullyFlat_algHom_lift_family_of_forall_isArtinianRing_exists_algHom_lift_of_isNoetherianRing
import Theorems.Thm_MvPolynomial_mem_mul_of_forall_pderiv_mem_of_forall_exists_algHom_lift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_of_forall_exists_lift_of_isArtinianRing_of_isNoetherianRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TopologicalSpace

namespace SmoothArtinNoethAux

theorem piece
    {R : Type} [CommRing R] [IsNoetherianRing R] {M : Scheme.{0}} (ϖ : M ⟶ Spec (CommRingCat.of R))
    (h : ∀ (T' T : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
      [CommRing T] [Nontrivial T] (p : T' →+* T), Function.Surjective p → RingHom.ker p * maximalIdeal T' = ⊥ →
      ∀ (s : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of R)) (m : Spec (CommRingCat.of T) ⟶ M),
        m ≫ ϖ = Spec.map (CommRingCat.ofHom p) ≫ s →
        ∃ m' : Spec (CommRingCat.of T') ⟶ M, m' ≫ ϖ = s ∧ Spec.map (CommRingCat.ofHom p) ≫ m' = m)
    {V : Scheme.{0}} (j : V ⟶ M) [IsOpenImmersion j] [CompactSpace ↥V]
    (g : V ⟶ Spec (CommRingCat.of R)) (hg : j ≫ ϖ = g) [LocallyOfFinitePresentation g] :
    Smooth g := by
  classical
  haveI : LocallyOfFiniteType g := inferInstance
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  by_contra hne

  have hZ : IsClosed ((g.smoothLocus : Set ↥V)ᶜ) := g.smoothLocus.isOpen.isClosed_compl
  have hZne : ((g.smoothLocus : Set ↥V)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro htop
    exact hne (TopologicalSpace.Opens.ext htop)

  obtain ⟨W, hWZ, hWne, hWcl, hWmin⟩ := hZ.exists_minimal_nonempty_closed_subset hZne
  obtain ⟨x, rfl⟩ := minimal_nonempty_closed_eq_singleton hWcl hWne hWmin
  have hx : IsClosed ({x} : Set ↥V) := hWcl
  have hxZ : x ∉ g.smoothLocus := fun hmem => hWZ (Set.mem_singleton x) hmem
  apply hxZ
  rw [Scheme.Hom.mem_smoothLocus]

  obtain ⟨n, I, J, hIJ, hJ, hJI, ι, hιopen, hι, -, himp⟩ :=
    AlgebraicGeometry.Scheme.exists_chart_formallySmooth_stalkMap_of_formallySmooth_localization g x hx
  apply himp
  haveI := hιopen
  haveI := hJ

  have hιM : (ι ≫ j) ≫ ϖ = Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ I))) := by
    rw [Category.assoc, hg, hι]
  have hlift := AlgebraicGeometry.Scheme.forall_exists_algHom_lift_of_forall_exists_lift_of_isOpenImmersion_of_isAlgClosed
    ϖ I (ι ≫ j) hιM h
  obtain ⟨D, iR, iA, iC, iT, iF, σ, hσ⟩ :=
    MvPolynomial.exists_faithfullyFlat_algHom_lift_family_of_forall_isArtinianRing_exists_algHom_lift_of_isNoetherianRing
      R I J hIJ hJ hlift
  letI := iR; letI := iA; letI := iC; haveI := iT; haveI := iF

  exact MvPolynomial.formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem R I J hIJ
    (fun v hv hdv => MvPolynomial.mem_mul_of_forall_pderiv_mem_of_forall_exists_algHom_lift R I J hIJ hJ D σ hσ v hv hdv)

end SmoothArtinNoethAux

theorem solution
    {R : Type} [CommRing R] [IsNoetherianRing R] {M : Scheme.{0}} (ϖ : M ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation ϖ]
    (h : ∀ (T' T : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
      [CommRing T] [Nontrivial T] (p : T' →+* T), Function.Surjective p → RingHom.ker p * maximalIdeal T' = ⊥ →
      ∀ (s : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of R)) (m : Spec (CommRingCat.of T) ⟶ M),
        m ≫ ϖ = Spec.map (CommRingCat.ofHom p) ≫ s →
        ∃ m' : Spec (CommRingCat.of T') ⟶ M, m' ≫ ϖ = s ∧ Spec.map (CommRingCat.ofHom p) ≫ m' = m) :
    Smooth ϖ := by
  classical
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) M.affineCover).mpr (fun i => ?_)
  haveI : IsAffine (M.affineCover.X i) := inferInstance
  haveI : CompactSpace ↥(M.affineCover.X i) := inferInstance
  exact SmoothArtinNoethAux.piece ϖ h (M.affineCover.f i) (M.affineCover.f i ≫ ϖ) rfl

end S_AlgebraicGeometry_Smooth_of_forall_exists_lift_of_isArtinianRing_of_isNoetherianRing
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_of_forall_exists_lift_of_isArtinianRing_of_isNoetherianRing (solution)
