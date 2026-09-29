-- Prove2me | solution 1 for AlgebraicGeometry.exists_comp_fromSpecResidueField_eq_of_range_subset_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/34f6195b-1f4f-5c46-b39a-acc61c2556f7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_comp_fromSpecResidueField_eq_of_range_subset_singleton

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_comp_fromSpecResidueField_eq_of_range_subset_singleton.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.IdealSheafData.radical_ideal Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal Scheme.IdealSheafData.vanishingIdeal_antimono Scheme.Hom Scheme.range_fromSpecResidueField QuasiCompact Scheme.Hom.support_ker Spec Scheme Scheme.IdealSheafData.vanishingIdeal IsClosedImmersion IsReduced IsClosedImmersion.lift IsClosedImmersion.lift_fac Scheme.Hom.ker_apply Scheme.IdealSheafData.vanishingIdeal_support Scheme.IdealSheafData"
p2m_open "AlgebraicGeometry"

theorem isClosedImmersion_fromSpecResidueField {S : Scheme.{u}} (s : S) (hs : IsClosed ({s} : Set S)) :
    IsClosedImmersion (S.fromSpecResidueField s) :=
  .of_isPreimmersion _ (by rw [Scheme.range_fromSpecResidueField]; exact hs)

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "fromSpecResidueField IdealSheafData.radical_ideal IdealSheafData.le_support_iff_le_vanishingIdeal IdealSheafData.vanishingIdeal_antimono Hom range_fromSpecResidueField Hom.support_ker IdealSheafData.vanishingIdeal residueField Hom.ker_apply residue IdealSheafData.vanishingIdeal_support IdealSheafData" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "support_ker ker ker_apply" end Scheme.Hom
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem Scheme.Hom.radical_ker_of_isReduced {Z S : Scheme.{u}} (g : Z ⟶ S) [QuasiCompact g] [IsReduced Z] :
    g.ker.radical = g.ker := by
  ext U : 2
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  refine le_antisymm (fun x ⟨n, hn⟩ => ?_) Ideal.le_radical
  rw [RingHom.mem_ker] at hn ⊢
  rw [map_pow] at hn
  exact IsReduced.eq_zero _ ⟨n, hn⟩

theorem exists_eq_comp_fromSpecResidueField_of_range_subset_aux {Z S : Scheme.{u}} [IsReduced Z] (g : Z ⟶ S) [QuasiCompact g]
    (s : S) (hs : IsClosed ({s} : Set S)) (hg : Set.range g.base ⊆ {s}) :
    ∃ t : Z ⟶ Spec (S.residueField s), t ≫ S.fromSpecResidueField s = g := by
  haveI := isClosedImmersion_fromSpecResidueField s hs
  refine ⟨IsClosedImmersion.lift (S.fromSpecResidueField s) g ?_, IsClosedImmersion.lift_fac _ _ _⟩

  have h1 : (S.fromSpecResidueField s).ker ≤ Scheme.IdealSheafData.vanishingIdeal ⟨{s}, hs⟩ := by
    rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    intro x hx
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField]
    exact subset_closure hx
  have h2 : Scheme.IdealSheafData.vanishingIdeal ⟨{s}, hs⟩ ≤ Scheme.IdealSheafData.vanishingIdeal g.ker.support := by
    apply Scheme.IdealSheafData.vanishingIdeal_antimono
    intro x hx
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker] at hx
    exact hs.closure_subset_iff.mpr hg hx
  rw [Scheme.IdealSheafData.vanishingIdeal_support, Scheme.Hom.radical_ker_of_isReduced] at h2
  exact h1.trans h2

end AlgebraicGeometry

theorem solution
    {Z S : Scheme.{u}} [IsReduced Z] (g : Z ⟶ S) [QuasiCompact g]
    (s : S) (hs : IsClosed ({s} : Set S)) (hg : Set.range g.base ⊆ {s}) :
    ∃ t : Z ⟶ Spec (S.residueField s), t ≫ S.fromSpecResidueField s = g :=
  AlgebraicGeometry.exists_eq_comp_fromSpecResidueField_of_range_subset_aux g s hs hg

end S_AlgebraicGeometry_exists_comp_fromSpecResidueField_eq_of_range_subset_singleton
end P2MW
export P2MW.S_AlgebraicGeometry_exists_comp_fromSpecResidueField_eq_of_range_subset_singleton (solution)
