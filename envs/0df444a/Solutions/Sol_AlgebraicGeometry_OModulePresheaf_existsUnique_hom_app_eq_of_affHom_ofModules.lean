-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.existsUnique_hom_app_eq_of_affHom_ofModules
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/68a9fe6f-5f38-5be0-8a1e-bccd068aafc0

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_hom_app_eq_of_affHom_ofModules

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace ExtAff

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)} {M N : X.Modules}
  (Φ : OModulePresheaf.AffHom (OModulePresheaf.ofModules π M) (OModulePresheaf.ofModules π N))

abbrev B (X : Scheme.{u}) : X.affineOpens → X.Opens := fun U => U.1

theorem isBasis_range_B (X : Scheme.{u}) : Opens.IsBasis (Set.range (B X)) := by
  rw [show Set.range (B X) = X.affineOpens from Subtype.range_coe]
  exact X.isBasis_affineOpens

noncomputable def α₀ : (inducedFunctor (B X)).op ⋙ M.presheaf ⟶ (inducedFunctor (B X)).op ⋙ N.presheaf where
  app U := AddCommGrpCat.ofHom (Φ.app U.unop).toAddMonoidHom
  naturality {U V} i := by
    ext x
    change Φ.app V.unop (M.presheaf.map (i.unop.hom).op x) = N.presheaf.map (i.unop.hom).op (Φ.app U.unop x)
    have h := Φ.naturality_apply (U := V.unop) (U' := U.unop) (i.unop.hom).le x
    rw [Subsingleton.elim i.unop.hom (homOfLE (i.unop.hom).le)]
    exact h

noncomputable def αAb : M.presheaf ⟶ N.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom M.presheaf ((SheafOfModules.toSheaf _).obj N) (isBasis_range_B X) (α₀ Φ)

theorem αAb_app_affine (U : X.affineOpens) (s : Γ(M, U.1)) :
    (αAb Φ).app (op U.1) s = Φ.app U s := by
  have := TopCat.Sheaf.extend_hom_app M.presheaf ((SheafOfModules.toSheaf _).obj N) (isBasis_range_B X) (α₀ Φ) U
  change (TopCat.Sheaf.restrictHomEquivHom M.presheaf ((SheafOfModules.toSheaf _).obj N) (isBasis_range_B X)
    (α₀ Φ)).app (op (B X U)) s = _
  rw [this]
  rfl

theorem αAb_naturality_apply {U V : X.Opens} (h : V ≤ U) (s : Γ(M, U)) :
    (αAb Φ).app (op V) (M.presheaf.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op ((αAb Φ).app (op U) s) := by
  have := (αAb Φ).naturality (homOfLE h).op
  exact congrFun (congrArg (fun f => (ConcreteCategory.hom f : _ → _)) this) s

theorem αAb_smul (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, U)) :
    (αAb Φ).app (op U) (r • m) = r • (αAb Φ).app (op U) m := by

  let ι : Type u := {V : X.affineOpens // V.1 ≤ U}
  have hcov : U ≤ ⨆ i : ι, i.1.1 := by
    intro x hx
    obtain ⟨W, ⟨V, hV, rfl⟩, hxV, hVU⟩ := (X.isBasis_affineOpens).exists_subset_of_mem_open hx U.isOpen
    exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hxV⟩
  refine (AlgebraicGeometry.Scheme.Modules.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible N
    (fun i : ι => i.1.1) U (fun i => i.2) hcov).1 _ _ (fun i => ?_)
  rw [← αAb_naturality_apply, Scheme.Modules.map_smul, Scheme.Modules.map_smul, ← αAb_naturality_apply,
    αAb_app_affine, αAb_app_affine]
  exact Φ.app_smul i.1 _ _

private noncomputable def _root_.ExtAff.hom : M ⟶ N :=
  ⟨PresheafOfModules.homMk (αAb Φ) (fun U r m => by obtain ⟨U⟩ := U; exact αAb_smul Φ U r m)⟩

p2m_export "ExtAff" "hom"
theorem hom_app_affine (U : X.affineOpens) (s : Γ(M, U.1)) : (hom Φ).app U.1 s = Φ.app U s :=
  αAb_app_affine Φ U s

theorem eq_of_forall_app_affine (β γ : M ⟶ N) (h : ∀ (U : X.affineOpens) (s : Γ(M, U.1)), β.app U.1 s = γ.app U.1 s) :
    β = γ := by
  apply (Scheme.Modules.toPresheaf X).map_injective
  refine TopCat.Sheaf.hom_ext M.presheaf ((SheafOfModules.toSheaf _).obj N) (isBasis_range_B X) (fun U => ?_)
  ext s
  exact h U s

end ExtAff

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M N : X.Modules)
    (Φ : OModulePresheaf.AffHom (OModulePresheaf.ofModules f M) (OModulePresheaf.ofModules f N)) :
    ∃! α : M ⟶ N, ∀ (U : X.affineOpens) (s : Γ(M, U.1)), α.app U.1 s = Φ.app U s :=
  ⟨ExtAff.hom Φ, fun U s => ExtAff.hom_app_affine Φ U s,
    fun β hβ => ExtAff.eq_of_forall_app_affine β (ExtAff.hom Φ)
      (fun U s => (hβ U s).trans (ExtAff.hom_app_affine Φ U s).symm)⟩

end S_AlgebraicGeometry_OModulePresheaf_existsUnique_hom_app_eq_of_affHom_ofModules
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_hom_app_eq_of_affHom_ofModules (solution)
