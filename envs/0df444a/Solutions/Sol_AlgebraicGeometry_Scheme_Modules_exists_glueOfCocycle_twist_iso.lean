-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_glueOfCocycle_twist_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/2c1eaa3c-6d76-5f2c-9e08-bb3c2c42bf87

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_glueOfCocycle_twist_iso
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

p2m_open "CategoryTheory Opposite TopologicalSpace CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_glueOfCocycle_twist_iso.AlgebraicGeometry"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme Scheme.Modules.Hom.id_app Scheme.Modules Scheme.Modules.map_smul Scheme.Modules.UnitCocycle Scheme.Modules.glueOfCocycle Scheme.Modules.glueFrame"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.id_app Hom Γ Modules.Hom.comp_app Modules.Hom Modules.Hom.id_app Hom.comp_app Modules Opens Modules.map_smul Modules.UnitCocycle Modules.glueOfCocycle Modules.glueFrame"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf Hom.comp_app Hom Hom.id_app map_smul IsFrameOn UnitCocycle glueOfCocycle glueFrame isFrameOn_glueFrame map_glueFrame_eq_smul exists_iso_glueOfCocycle_app_eq_glueFrame"
namespace GlueT2
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.Modules.GlueOfCocycle"

variable {X : Scheme.{u}} {M : X.Modules}

theorem map_smul' {A B : X.Opens} (hBA : B ≤ A) (r : Γ(X, A)) (m : Γ(M, A)) :
    M.presheaf.map (homOfLE hBA).op (r • m) = X.presheaf.map (homOfLE hBA).op r • M.presheaf.map (homOfLE hBA).op m :=
  Scheme.Modules.map_smul M _ r m

theorem map_refl {A : X.Opens} (m : Γ(M, A)) : M.presheaf.map (homOfLE (le_refl A)).op m = m := by
  rw [Subsingleton.elim (homOfLE (le_refl A)) (𝟙 A), op_id, M.presheaf.map_id]; rfl

theorem isFrameOn_unit_smul {A : X.Opens} {s : Γ(M, A)} (hs : IsFrameOn s A) (g : Γ(X, A)) (hg : IsUnit g) :
    IsFrameOn (g • s) A := by
  intro W hWA _
  obtain ⟨v, hv⟩ := hg.map (X.presheaf.map (homOfLE hWA).op).hom
  have hb := hs hWA hWA
  have hcomp : (fun a : Γ(X, W) => a • M.presheaf.map (homOfLE hWA).op (g • s)) =
      (fun a : Γ(X, W) => a • M.presheaf.map (homOfLE hWA).op s) ∘ (fun a => a * ↑v) := by
    funext a
    simp only [Function.comp_apply, map_smul', smul_smul, ← hv]
  rw [hcomp]
  exact hb.comp (Units.mulRight_bijective v)

lemma iso_hom_inv_app_apply {N N' : X.Modules} (e : N ≅ N') (A : X.Opens) (x : Γ(N, A)) :
    e.inv.app A (e.hom.app A x) = x := by
  rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
  rfl

end AlgebraicGeometry.Scheme.Modules.GlueT2

open _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_glueOfCocycle_twist_iso.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueT2 AlgebraicGeometry.Scheme.Modules.GlueOfCocycle in

theorem solution
    {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤) (c : Scheme.Modules.UnitCocycle U)
    (h : ∀ i, Γ(X, U i)ˣ) :
    ∃ φ : Scheme.Modules.glueOfCocycle (c.twist h) ≅ Scheme.Modules.glueOfCocycle c,
      ∀ i, φ.hom.app (U i) (Scheme.Modules.glueFrame (c.twist h) i) =
        (↑(h i)⁻¹ : Γ(X, U i)) • Scheme.Modules.glueFrame c i := by

  let f : ∀ i, Γ(glueOfCocycle c, U i) := fun i => (↑(h i)⁻¹ : Γ(X, U i)) • glueFrame c i
  have hf : ∀ i, IsFrameOn (f i) (U i) :=
    fun i => isFrameOn_unit_smul (isFrameOn_glueFrame c i) _ (h i)⁻¹.isUnit

  have htrans : ∀ i j,
      (glueOfCocycle c).presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (f j) =
        (c.twist h).u i j • (glueOfCocycle c).presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (f i) := by
    intro i j
    simp only [f]
    rw [map_smul', map_smul', map_glueFrame_eq_smul c i j, smul_smul, smul_smul]
    congr 1
    change rO inf_le_right (↑(h j)⁻¹ : Γ(X, U j)) * c.u i j =
      (rO inf_le_left (h i : Γ(X, U i)) * c.u i j * rO inf_le_right (↑(h j)⁻¹ : Γ(X, U j))) *
        rO inf_le_left (↑(h i)⁻¹ : Γ(X, U i))
    have hunit : rO (inf_le_left : U i ⊓ U j ≤ U i) (h i : Γ(X, U i)) * rO inf_le_left (↑(h i)⁻¹ : Γ(X, U i)) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    linear_combination (-(c.u i j * rO (inf_le_right : U i ⊓ U j ≤ U j) (↑(h j)⁻¹ : Γ(X, U j)))) * hunit
  obtain ⟨φ, hφ⟩ := exists_iso_glueOfCocycle_app_eq_glueFrame hU (c.twist h) f hf htrans
  refine ⟨φ.symm, fun i => ?_⟩
  change φ.inv.app (U i) (glueFrame (c.twist h) i) = f i
  rw [← hφ i]
  exact iso_hom_inv_app_apply φ (U i) (f i)

end S_AlgebraicGeometry_Scheme_Modules_exists_glueOfCocycle_twist_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_glueOfCocycle_twist_iso (solution)
