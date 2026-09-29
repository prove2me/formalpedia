-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_comp_linMap_of_sigma_eq_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/fbbb700e-5698-542a-87e6-ae8a46e92550

import Definitions.Def_AlgebraicGeometry_ProjSpaceLinMap
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_sigma_eq_sum_smul_toProj_eq_comp_linMap
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_forall_sections_eq_univ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_comp_linMap_of_sigma_eq_sum_smul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N : ℕ}
    (𝔓 𝔔 : M.ProjPresentation f N) (U : Matrix (Fin (N + 1)) (Fin (N + 1)) R) (hU : IsUnit U)
    (h : ∀ i, 𝔔.σ i = ∑ j, ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of R)).inv.hom (U i j))) • 𝔓.σ j) :
    𝔔.toProj = 𝔓.toProj ≫ ProjSpace.linMap R N U hU  := by
  obtain ⟨𝔓', hσ, hto⟩ :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_sigma_eq_sum_smul_toProj_eq_comp_linMap 𝔓 U hU
  have h𝔔 : 𝔔.toProj = 𝔓'.toProj :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_of_forall_sections_eq_univ 𝔔 𝔓'
      (fun i => by rw [h i, hσ i])
  rw [h𝔔, hto]

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_comp_linMap_of_sigma_eq_sum_smul
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_comp_linMap_of_sigma_eq_sum_smul (solution)
