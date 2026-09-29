-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.eq_of_forall_comap_openCover_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/f7f7cbd3-37f0-5423-a1c0-346943304146

import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Cover.Open
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme Scheme.IdealSheafData"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "OpenCover affineOpens isBasis_affineOpens Opens IdealSheafData Cover"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "ideal ext_of_iSup_eq_top comap ideal_comap_of_isOpenImmersion"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem eq_of_forall_comap_openCover_eq_aux
    {X : Scheme.{u}} (𝒰 : X.OpenCover) {I J : X.IdealSheafData}
    (h : ∀ i, I.comap (𝒰.f i) = J.comap (𝒰.f i)) : I = J := by
  refine ext_of_iSup_eq_top
    (fun p : Σ i, (𝒰.X i).affineOpens => ⟨𝒰.f p.1 ''ᵁ (p.2 : (𝒰.X p.1).Opens),
      p.2.2.image_of_isOpenImmersion _⟩) ?_ ?_
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨y, hy⟩ := 𝒰.covers x
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
      (𝒰.X (𝒰.idx x)).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨𝒰.idx x, ⟨W, hW⟩⟩, ⟨y, hyW, hy⟩⟩
  · rintro ⟨i, W⟩
    have hW := congrArg (fun K : (𝒰.X i).IdealSheafData => K.ideal W) (h i)
    simp only [ideal_comap_of_isOpenImmersion] at hW
    exact Ideal.comap_injective_of_surjective _
      (ConcreteCategory.bijective_of_isIso ((𝒰.f i).appIso (W : (𝒰.X i).Opens)).inv).2 hW

end AlgebraicGeometry.Scheme.IdealSheafData

theorem solution
    {X : Scheme.{u}} (𝒰 : X.OpenCover) {I J : X.IdealSheafData}
    (h : ∀ i, I.comap (𝒰.f i) = J.comap (𝒰.f i)) : I = J :=
  AlgebraicGeometry.Scheme.IdealSheafData.eq_of_forall_comap_openCover_eq_aux 𝒰 h

end S_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq (solution)
