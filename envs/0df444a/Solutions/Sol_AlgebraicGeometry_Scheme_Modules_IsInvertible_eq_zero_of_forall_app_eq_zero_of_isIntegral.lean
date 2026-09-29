-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.eq_zero_of_forall_app_eq_zero_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/79ccb7df-c28e-5870-8bed-bacbf61eda77

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_zero_of_forall_app_eq_zero_of_isIntegral

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace P2mWs30LBExtZero

variable {X : Scheme.{u}}

theorem res_injective [IsIntegral X] {V W : X.Opens} (i : W ≤ V) (hW : Nonempty W) :
    Function.Injective (X.presheaf.map (homOfLE i).op) := by
  obtain ⟨⟨x, hx⟩⟩ := hW
  intro a b h
  have ha := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE i) x hx a
  have hb := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE i) x hx b
  apply germ_injective_of_isIntegral X x (i hx)
  rw [← ha, ← hb, h]

theorem restrict_map_apply {N : X.Modules} (U : X.Opens) {W W' : (U : Scheme.{u}).Opens} (i : W' ≤ W)
    (n : Γ(N.restrict U.ι, W)) :
    (N.restrict U.ι).presheaf.map (homOfLE i).op n =
      N.presheaf.map (homOfLE (Scheme.Hom.image_mono U.ι i)).op (show Γ(N, U.ι ''ᵁ W) from n) := rfl

end P2mWs30LBExtZero

open P2mWs30LBExtZero in
theorem solution
    {X : Scheme.{u}} [IsIntegral X] {M N : X.Modules} (hN : Scheme.Modules.IsInvertible N) (f : M ⟶ N)
    (U : X.Opens) (hU : Nonempty U) (h : ∀ V : X.Opens, V ≤ U → f.app V = 0) : f = 0 := by
  apply Scheme.Modules.hom_ext
  intro W
  ext m
  change f.app W m = 0
  set n : Γ(N, W) := f.app W m with hn

  have key : ∀ y ∈ W, ∃ V : X.Opens, V ≤ W ∧ y ∈ V ∧
      ∀ (hV : V ≤ W), N.presheaf.map (homOfLE hV).op n = 0 := by
    intro y hyW
    obtain ⟨Uy, hyU, ⟨eU⟩⟩ := hN.exists_trivialization y
    let e : N.restrict Uy.ι ≅ SheafOfModules.unit (Uy : Scheme.{u}).ringCatSheaf :=
      (Scheme.Modules.restrictFunctorIsoPullback Uy.ι).app N ≪≫ eU
    let W' : (Uy : Scheme.{u}).Opens := Uy.ι ⁻¹ᵁ W
    let W'' : (Uy : Scheme.{u}).Opens := Uy.ι ⁻¹ᵁ (W ⊓ U)
    have hW''W' : W'' ≤ W' := fun z hz => hz.1
    have himW' : Uy.ι ''ᵁ W' ≤ W := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact inf_le_right
    have himW'' : Uy.ι ''ᵁ W'' ≤ U := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact fun z hz => hz.2.2
    have hyim : y ∈ Uy.ι ''ᵁ W' := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact ⟨hyU, hyW⟩

    have hne : Nonempty (Uy.ι ''ᵁ W'') := by
      have h1 : ((Uy ⊓ W : X.Opens) : Set X).Nonempty := ⟨y, hyU, hyW⟩
      obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (Uy ⊓ W).isOpen U.isOpen h1
        (hU.elim fun u => ⟨u.1, u.2⟩)
      refine ⟨⟨z, ?_⟩⟩
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact ⟨hz.1.1, hz.1.2, hz.2⟩
    refine ⟨Uy.ι ''ᵁ W', himW', hyim, fun hV => ?_⟩

    set n' : Γ(N.restrict Uy.ι, W') := N.presheaf.map (homOfLE hV).op n with hn'

    have hn'' : (N.restrict Uy.ι).presheaf.map (homOfLE hW''W').op n' = 0 := by
      rw [restrict_map_apply, hn', hn]
      change (N.presheaf.map (homOfLE hV).op ≫ N.presheaf.map _) (f.app W m) = 0
      rw [← N.presheaf.map_comp, ← op_comp]
      have nat := ConcreteCategory.congr_hom
        (f.mapPresheaf.naturality (homOfLE (Scheme.Hom.image_mono Uy.ι hW''W') ≫ homOfLE hV).op) m
      simp only [Scheme.Modules.mapPresheaf_app] at nat
      change (f.app W ≫ N.presheaf.map _) m = 0
      rw [← nat]
      change f.app (Uy.ι ''ᵁ W'') (M.presheaf.map _ m) = 0
      rw [h _ himW'']
      rfl

    set g := e.hom.app W' n' with hg
    have hgres : (Scheme.Modules.presheaf (SheafOfModules.unit (Uy : Scheme.{u}).ringCatSheaf)).map
        (homOfLE hW''W').op g = 0 := by
      have nat := ConcreteCategory.congr_hom (e.hom.mapPresheaf.naturality (homOfLE hW''W').op) n'
      simp only [Scheme.Modules.mapPresheaf_app] at nat
      rw [hg]
      change ((e.hom.app W') ≫ (Scheme.Modules.presheaf (SheafOfModules.unit (Uy : Scheme.{u}).ringCatSheaf)).map (homOfLE hW''W').op) n' = 0
      rw [← nat]
      change e.hom.app W'' ((N.restrict Uy.ι).presheaf.map (homOfLE hW''W').op n') = 0
      rw [hn'', map_zero]
    have hg0 : g = 0 := by
      haveI := hne
      apply res_injective (X := X) (Scheme.Hom.image_mono Uy.ι hW''W') hne
      change X.presheaf.map (homOfLE (Scheme.Hom.image_mono Uy.ι hW''W')).op g =
        X.presheaf.map (homOfLE (Scheme.Hom.image_mono Uy.ι hW''W')).op (0 : Γ(X, Uy.ι ''ᵁ W'))
      rw [map_zero]
      exact hgres
    have hn'0 : n' = 0 := by
      have : n' = e.inv.app W' (e.hom.app W' n') := by
        change n' = (e.hom ≫ e.inv).app W' n'
        rw [Iso.hom_inv_id]
        rfl
      rw [this, ← hg, hg0, map_zero]
    exact hn'0

  choose V hVW hyV hzero using key
  let ι := {y : X // y ∈ W}
  let Vc : ι → X.Opens := fun y => V y.1 y.2
  have hcov : W ≤ iSup Vc := fun y hy => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyV y hy⟩
  exact TopCat.Sheaf.eq_of_locally_eq' (C := Ab) ⟨N.presheaf, N.isSheaf⟩ Vc W
    (fun y => homOfLE (hVW y.1 y.2)) hcov n 0
    (fun y => by rw [map_zero]; exact hzero y.1 y.2 (hVW y.1 y.2))

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_zero_of_forall_app_eq_zero_of_isIntegral
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_zero_of_forall_app_eq_zero_of_isIntegral (solution)
