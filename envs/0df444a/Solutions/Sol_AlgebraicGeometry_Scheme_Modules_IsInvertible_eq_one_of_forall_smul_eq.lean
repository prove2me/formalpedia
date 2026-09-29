-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.eq_one_of_forall_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/7dcb651c-0f7f-574e-a6f5-00d09414f192

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_one_of_forall_smul_eq

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

theorem solution
    {T : Scheme.{u}} {N : T.Modules} (hN : Scheme.Modules.IsInvertible N) (v : Γ(T, ⊤))
    (h : ∀ (U : T.Opens) (s : Γ(N, U)), T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op v • s = s) :
    v = 1 := by
  classical

  have loc : ∀ x : T, ∃ U : T.Opens, x ∈ U ∧ T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op v = 1 := by
    intro x
    obtain ⟨U, hxU, -, ⟨τ⟩⟩ := hN.exists_restrict_iso (V := ⊤) (x := x) trivial
    refine ⟨U.1, hxU, ?_⟩

    let W : T.Opens := U.1.ι ''ᵁ ⊤
    let v' : Γ(T, W) := T.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op v

    let one' : Γ(𝟙_ (U.1 : Scheme.{u}).Modules, ⊤) := Scheme.Modules.toUnitSection ⊤ 1
    let m : Γ(N.restrict U.1.ι, ⊤) := τ.inv.app ⊤ one'
    have hm : τ.hom.app ⊤ m = one' := by
      change (τ.inv.app ⊤ ≫ τ.hom.app ⊤) one' = one'
      rw [← Scheme.Modules.Hom.comp_app, τ.inv_hom_id, Scheme.Modules.Hom.id_app]
      rfl

    let r : Γ(U.1, ⊤) := (U.1.ι.appIso ⊤).hom v'
    have hr : (U.1.ι.appIso ⊤).inv r = v' := by
      change ((U.1.ι.appIso ⊤).hom ≫ (U.1.ι.appIso ⊤).inv) v' = v'
      rw [Iso.hom_inv_id]; rfl
    have h1 : r • m = m := by
      have h0 : v' • (show Γ(N, W) from m) = (show Γ(N, W) from m) := h W m
      rw [← hr] at h0
      exact h0

    have h2 : r • one' = one' := by
      rw [← hm, ← Scheme.Modules.Hom.app_smul, h1]
    have hr1 : r = 1 := by
      have := congrArg (Scheme.Modules.ofUnitSection ⊤) h2
      rw [Scheme.Modules.ofUnitSection_smul] at this
      simpa [one', Scheme.Modules.ofUnitSection_toUnitSection] using this

    have hv' : v' = 1 := by rw [← hr, hr1, map_one]
    have hWU : W = U.1 := U.1.ι_image_top
    have : T.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op v =
        T.presheaf.map (eqToHom hWU.symm).op v' := by
      change _ = (T.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫ T.presheaf.map (eqToHom hWU.symm).op) v
      rw [← Functor.map_comp, ← op_comp,
        show eqToHom hWU.symm ≫ homOfLE (le_top : W ≤ ⊤) = homOfLE (le_top : U.1 ≤ ⊤) from Subsingleton.elim _ _]
    rw [this, hv', map_one]

  choose U hU hU1 using loc
  refine T.sheaf.eq_of_locally_eq' U ⊤ (fun x => homOfLE le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x⟩) v 1 ?_
  intro x
  rw [map_one]
  exact hU1 x

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_one_of_forall_smul_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_one_of_forall_smul_eq (solution)
