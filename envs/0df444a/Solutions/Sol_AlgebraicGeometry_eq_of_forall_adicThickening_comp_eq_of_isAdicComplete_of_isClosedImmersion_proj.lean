-- Prove2me | solution 1 for AlgebraicGeometry.eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/ccd4f8a9-8bbb-5c06-bce4-6b85a6b76166

import Mathlib
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_isIso_of_forall_isIso_adicThickening_of_isAdicComplete_of_isClosedImmersion_proj
import Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_iff_comp_eq_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2mWs49FormalMorUniq

theorem isPullback_adicThickening {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (I : Ideal R) (n : ℕ) :
    IsPullback (adicThickeningι f I n) (adicThickeningToBase f I n) f (adicThickeningBase I n) :=
  IsPullback.of_hasPullback f (adicThickeningBase I n)

end P2mWs49FormalMorUniq

open P2mWs49FormalMorUniq in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ιX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hιX : IsClosedImmersion ιX)
    (hιXf : ιX ≫ ProjSpace.π R N = f)
    (N' : ℕ) (ιY : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)) (hιY : IsClosedImmersion ιY)
    (hιYg : ιY ≫ ProjSpace.π R N' = g)
    (ψ ψ' : X ⟶ Y) (hψ : ψ ≫ g = f) (hψ' : ψ' ≫ g = f)
    (h : ∀ n : ℕ, adicThickeningι f I n ≫ ψ = adicThickeningι f I n ≫ ψ') :
    ψ = ψ' := by
  haveI := hιX
  haveI := hιY
  haveI : IsSeparated g := by rw [← hιYg]; infer_instance

  obtain ⟨E, j, hj, hE⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_iff_comp_eq_of_isSeparated g f ψ ψ' hψ hψ'
  haveI := hj

  have hs : ∀ n : ℕ, ∃ s : adicThickening f I n ⟶ E, s ≫ j = adicThickeningι f I n :=
    fun n => (hE (adicThickeningι f I n)).mp (h n)
  choose s hs using hs

  have hPX : ∀ n : ℕ, IsPullback (adicThickeningι f I n) (adicThickeningToBase f I n) f (adicThickeningBase I n) :=
    fun n => isPullback_adicThickening f I n
  have hPE : ∀ n : ℕ, IsPullback (adicThickeningι (j ≫ f) I n) (adicThickeningToBase (j ≫ f) I n) (j ≫ f)
      (adicThickeningBase I n) :=
    fun n => isPullback_adicThickening (j ≫ f) I n

  have hw : ∀ n : ℕ, (adicThickeningι (j ≫ f) I n ≫ j) ≫ f =
      adicThickeningToBase (j ≫ f) I n ≫ adicThickeningBase I n := fun n => by
    rw [Category.assoc]; exact (hPE n).w
  let jn : ∀ n : ℕ, adicThickening (j ≫ f) I n ⟶ adicThickening f I n := fun n =>
    (hPX n).lift (adicThickeningι (j ≫ f) I n ≫ j) (adicThickeningToBase (j ≫ f) I n) (hw n)
  have hjn : ∀ n : ℕ, jn n ≫ adicThickeningι f I n = adicThickeningι (j ≫ f) I n ≫ j := fun n =>
    (hPX n).lift_fst _ _ _
  have hjn' : ∀ n : ℕ, jn n ≫ adicThickeningToBase f I n = adicThickeningToBase (j ≫ f) I n := fun n =>
    (hPX n).lift_snd _ _ _

  have hiso : ∀ n : ℕ, IsIso (jn n) := fun n => by
    haveI : Mono (jn n) := mono_of_mono_fac (hjn n)
    have hσw : s n ≫ (j ≫ f) = adicThickeningToBase f I n ≫ adicThickeningBase I n := by
      rw [← Category.assoc, hs, (hPX n).w]
    let σ : adicThickening f I n ⟶ adicThickening (j ≫ f) I n :=
      (hPE n).lift (s n) (adicThickeningToBase f I n) hσw
    have hσ₁ : σ ≫ adicThickeningι (j ≫ f) I n = s n := (hPE n).lift_fst _ _ _
    have hσ₂ : σ ≫ adicThickeningToBase (j ≫ f) I n = adicThickeningToBase f I n := (hPE n).lift_snd _ _ _
    have hsec : σ ≫ jn n = 𝟙 _ := by
      apply (hPX n).hom_ext
      · rw [Category.assoc, hjn, ← Category.assoc, hσ₁, hs, Category.id_comp]
      · rw [Category.assoc, hjn', hσ₂, Category.id_comp]
    haveI : IsSplitEpi (jn n) := IsSplitEpi.mk' ⟨σ, hsec⟩
    exact isIso_of_mono_of_isSplitEpi (jn n)

  haveI : IsIso j :=
    AlgebraicGeometry.isIso_of_forall_isIso_adicThickening_of_isAdicComplete_of_isClosedImmersion_proj
      I (j ≫ f) f N (j ≫ ιX) inferInstance (by rw [Category.assoc, hιXf]) N ιX hιX hιXf j rfl jn hjn hjn' hiso

  have hEq : j ≫ ψ = j ≫ ψ' := (hE j).mpr ⟨𝟙 E, Category.id_comp j⟩
  exact (cancel_epi j).mp hEq

end S_AlgebraicGeometry_eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
end P2MW
export P2MW.S_AlgebraicGeometry_eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj (solution)
