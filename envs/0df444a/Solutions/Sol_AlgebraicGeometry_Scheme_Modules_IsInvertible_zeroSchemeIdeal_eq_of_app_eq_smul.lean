-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.zeroSchemeIdeal_eq_of_app_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1ddc03ba-be37-5eac-b1d3-62243cd46443

import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_app_eq_smul

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite"

namespace ZSWs13

variable {X : Scheme.{u}} {M : X.Modules}

theorem map_app_unit (φ : 𝟙_ X.Modules ⟶ M) {U V : X.Opens} (i : U ⟶ V)
    (m : Γ(𝟙_ X.Modules, V)) :
    M.presheaf.map i.op (φ.app V m) = φ.app U ((𝟙_ X.Modules).presheaf.map i.op m) := by
  have h := (Scheme.Modules.Hom.mapPresheaf φ).naturality i.op
  have h2 := ConcreteCategory.congr_hom h m
  simp only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] at h2
  exact h2.symm

theorem map_toUnitSection_one {U V : X.Opens} (i : U ⟶ V) :
    (𝟙_ X.Modules).presheaf.map i.op (Scheme.Modules.toUnitSection V 1) =
      Scheme.Modules.toUnitSection U 1 := by
  apply Scheme.Modules.ofUnitSection_injective
  rw [Scheme.Modules.ofUnitSection_map, Scheme.Modules.ofUnitSection_toUnitSection,
    Scheme.Modules.ofUnitSection_toUnitSection, map_one]

theorem app_one_eq_map (φ : 𝟙_ X.Modules ⟶ M) (U : X.Opens) :
    φ.app U (Scheme.Modules.toUnitSection U 1) =
      M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (φ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) := by
  rw [map_app_unit, map_toUnitSection_one]

end ZSWs13

open ZSWs13 in
theorem solution
    {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s₁ s₂ : 𝟙_ X.Modules ⟶ M) (u : Γ(X, ⊤)) (hu : IsUnit u)
    (h : s₂.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = u • s₁.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) :
    Scheme.Modules.zeroSchemeIdeal s₁ = Scheme.Modules.zeroSchemeIdeal s₂ := by
  classical

  have hcov : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ Nonempty (M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules) := by
    intro x
    obtain ⟨U, hxU, -, hτ⟩ := hM.exists_restrict_iso (V := ⊤) (x := x) trivial
    exact ⟨U, hxU, hτ⟩
  choose U hxU hτ using hcov
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top U
    (top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩) fun x => ?_
  obtain ⟨τ⟩ := hτ x
  obtain ⟨-, h1⟩ := Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq hM s₁
  obtain ⟨-, h2⟩ := Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq hM s₂
  rw [(h1 (U x) τ).1, (h2 (U x) τ).1]

  set W : X.Opens := (U x).1.ι ''ᵁ ⊤ with hW
  have hres : s₂.app W (Scheme.Modules.toUnitSection W 1) =
      X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op u • s₁.app W (Scheme.Modules.toUnitSection W 1) := by
    rw [app_one_eq_map s₂ W, app_one_eq_map s₁ W, h, Scheme.Modules.map_smul]

  set r : Γ(((U x).1 : Scheme.{u}), ⊤) := ((U x).1.ι.appIso ⊤).hom (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op u) with hr
  have hr' : ((U x).1.ι.appIso ⊤).inv r = X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op u := by
    rw [hr, Iso.hom_inv_id_apply]
  have hres' : Scheme.Modules.restrictSection s₂ (U x).1 = r • Scheme.Modules.restrictSection s₁ (U x).1 := by
    change s₂.app W (Scheme.Modules.toUnitSection W 1) =
      ((U x).1.ι.appIso ⊤).inv r • s₁.app W (Scheme.Modules.toUnitSection W 1)
    rw [hr']
    exact hres
  have hru : IsUnit r := (hu.map _).map _
  have key : Scheme.Modules.coeff s₂ (U x).1 τ.hom = (U x).1.topIso.hom r * Scheme.Modules.coeff s₁ (U x).1 τ.hom := by
    show (U x).1.topIso.hom (Scheme.Modules.ofUnitSection ⊤ (τ.hom.app ⊤ (Scheme.Modules.restrictSection s₂ (U x).1))) = _
    rw [hres', Scheme.Modules.Hom.app_smul, Scheme.Modules.ofUnitSection_smul, map_mul]
    rfl
  rw [key]
  exact (Ideal.span_singleton_mul_left_unit (hru.map _) _).symm

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_app_eq_smul
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_app_eq_smul (solution)
