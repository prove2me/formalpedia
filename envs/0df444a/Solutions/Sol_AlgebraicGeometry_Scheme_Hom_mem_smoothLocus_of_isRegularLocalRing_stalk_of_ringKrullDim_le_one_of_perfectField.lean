-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.mem_smoothLocus_of_isRegularLocalRing_stalk_of_ringKrullDim_le_one_of_perfectField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a19654df-3048-54fc-830d-c912704069b6

import Mathlib
import Theorems.Thm_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_perfectField
import Theorems.Thm_IsRegularLocalRing_isDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_mem_smoothLocus_of_isRegularLocalRing_stalk_of_ringKrullDim_le_one_of_perfectField

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false in

theorem solution
    {K : Type u} [Field K] [PerfectField K] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFinitePresentation g]
    (y : ↥Y) (hreg : IsRegularLocalRing (Y.presheaf.stalk y))
    (hdim : ringKrullDim (Y.presheaf.stalk y) ≤ 1) :
    y ∈ g.smoothLocus := by
  have hft := LocallyOfFiniteType.stalkMap g y
  rw [Scheme.Hom.mem_smoothLocus]
  algebraize [(g.stalkMap y).hom]

  let K' := (Spec.structureSheaf K).presheaf.stalk (g y)
  let e : K ≃ₐ[K] K' := IsLocalization.atUnits _ (g y).asIdeal.primeCompl
      (fun x hx ↦ by aesop (add simp IsUnit.mem_submonoid_iff))
  have : Algebra.IsAlgebraic K K' :=
    .of_injective e.symm.toAlgHom e.symm.injective
  let iF : Field K' := (e.toRingEquiv.symm.isField (Field.toIsField K)).toField
  let iF' : Field ((Spec (.of K)).presheaf.stalk (g y)) := iF
  have : PerfectField ((Spec (.of K)).presheaf.stalk (g y)) :=
    Algebra.IsAlgebraic.perfectField (K := K)
      (L := (Spec.structureSheaf K).presheaf.stalk (g y))
  show Algebra.FormallySmooth ((Spec (.of K)).presheaf.stalk (g y)) (Y.presheaf.stalk y)

  haveI := hreg
  haveI : IsDomain ↥(Y.presheaf.stalk y) := IsRegularLocalRing.isDomain _
  have hfg : (IsLocalRing.maximalIdeal ↥(Y.presheaf.stalk y)).FG := IsNoetherian.noetherian _
  have hle : ((IsLocalRing.maximalIdeal ↥(Y.presheaf.stalk y)).spanFinrank : WithBot ℕ∞) ≤ 1 := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal]; exact hdim
  have hle' : (IsLocalRing.maximalIdeal ↥(Y.presheaf.stalk y)).spanFinrank ≤ 1 := by
    exact_mod_cast hle
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle' with h0 | h1
  ·
    have hbot : IsLocalRing.maximalIdeal ↥(Y.presheaf.stalk y) = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mp h0
    let _ : Field ↥(Y.presheaf.stalk y) :=
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr hbot).toField
    exact Algebra.FormallySmooth.of_perfectField
  ·
    obtain ⟨s, hs, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
    rw [h1, Finset.card_eq_one] at hs
    obtain ⟨u, rfl⟩ := hs
    rw [Finset.coe_singleton] at hspan
    have hu0 : u ≠ 0 := by
      rintro rfl
      have : (IsLocalRing.maximalIdeal ↥(Y.presheaf.stalk y)).spanFinrank = 0 := by
        rw [← hspan]; simp
      omega
    exact Algebra.FormallySmooth.of_maximalIdeal_eq_span_of_perfectField _ _ u hu0 hspan.symm

end S_AlgebraicGeometry_Scheme_Hom_mem_smoothLocus_of_isRegularLocalRing_stalk_of_ringKrullDim_le_one_of_perfectField
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_mem_smoothLocus_of_isRegularLocalRing_stalk_of_ringKrullDim_le_one_of_perfectField (solution)
