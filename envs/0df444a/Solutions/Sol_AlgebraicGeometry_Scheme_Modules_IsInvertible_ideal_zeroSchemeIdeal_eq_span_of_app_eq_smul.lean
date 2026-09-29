-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/d644f93f-adcb-5ca9-a670-1b85d6138552

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Surjective Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme Scheme.Modules.Hom.id_app Scheme.Opens.topIso_hom Scheme.Modules Scheme.Opens Scheme.Modules.map_smul Scheme.Modules.IsInvertible Scheme.Modules.IsFrameOn Scheme.Modules.toUnitSection Scheme.Modules.ofUnitSection Scheme.Modules.ofUnitSection_toUnitSection Scheme.Modules.ofUnitSection_injective Scheme.Modules.ofUnitSection_map Scheme.Modules.ofUnitSection_smul Scheme.Modules.restrictSection Scheme.Modules.coeff Scheme.Modules.zeroSchemeIdeal Scheme.Modules.restrictIsoOfLE Scheme.Modules.restrict_smul_eq"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul Hom.id_app Hom Γ Modules.Hom.comp_app topIso_hom Modules.Hom topIso Modules.Hom.id_app Opens.topIso_hom affineOpens Hom.comp_app Modules Opens Modules.map_smul restrict Modules.IsInvertible Modules.IsFrameOn Modules.toUnitSection Modules.ofUnitSection Modules.ofUnitSection_toUnitSection Modules.ofUnitSection_injective Modules.ofUnitSection_map Modules.ofUnitSection_smul Modules.restrictSection Modules.coeff Modules.zeroSchemeIdeal Modules.restrictIsoOfLE Modules.restrict_smul_eq"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul presheaf Hom.comp_app Hom Hom.id_app restrict map_smul IsInvertible IsFrameOn toUnitSection ofUnitSection ofUnitSection_toUnitSection ofUnitSection_injective ofUnitSection_map ofUnitSection_smul restrictSection coeff zeroSchemeIdeal restrictIsoOfLE restrict_smul_eq"
namespace ZFrameAux
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

lemma app_map {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ⟶ U) (x : Γ(M, U)) :
    φ.app V (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app U x) := by
  simpa using ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) x

lemma map_toUnitSection_one {U V : X.Opens} (i : V ⟶ U) :
    (𝟙_ X.Modules).presheaf.map i.op (Scheme.Modules.toUnitSection U 1) = Scheme.Modules.toUnitSection V 1 := by
  apply Scheme.Modules.ofUnitSection_injective
  rw [Scheme.Modules.ofUnitSection_map, Scheme.Modules.ofUnitSection_toUnitSection,
    Scheme.Modules.ofUnitSection_toUnitSection, map_one]

lemma presheaf_map_map {A B C : X.Opens} (f : B ⟶ A) (g : C ⟶ B) (k : C ⟶ A) (x : Γ(X, A)) :
    X.presheaf.map g.op (X.presheaf.map f.op x) = X.presheaf.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (g ≫ f) k]

end AlgebraicGeometry.Scheme.Modules.ZFrameAux

open AlgebraicGeometry.Scheme.Modules.ZFrameAux in
theorem solution
    {X : Scheme.{u}} {N : X.Modules} (hN : Scheme.Modules.IsInvertible N)
    {V : X.Opens} (Ω : Γ(N, V)) (hΩ : Scheme.Modules.IsFrameOn Ω V)
    (σ : 𝟙_ X.Modules ⟶ N) (c : Γ(X, V))
    (hσ : σ.app V (Scheme.Modules.toUnitSection V 1) = c • Ω)
    (U : X.affineOpens) (hUV : U.1 ≤ V) :
    (Scheme.Modules.zeroSchemeIdeal σ).ideal U = Ideal.span {X.presheaf.map (homOfLE hUV).op c} := by

  obtain ⟨e⟩ := hΩ.nonempty_pullback_iso_unit U.1 hUV hUV
  let τ : N.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules := Scheme.Modules.restrictIsoOfLE le_rfl e
  rw [((hN.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq σ).2 U τ).1]

  have hi : U.1.ι ''ᵁ ⊤ ≤ V := (le_of_eq U.1.ι_image_top).trans hUV
  let c' : Γ((U.1 : Scheme.{u}), ⊤) := (X.presheaf.map (homOfLE hi).op c : Γ(X, U.1.ι ''ᵁ ⊤))
  let Ω' : Γ(N.restrict U.1.ι, ⊤) := (N.presheaf.map (homOfLE hi).op Ω : Γ(N, U.1.ι ''ᵁ ⊤))
  have hres : Scheme.Modules.restrictSection σ U.1 = c' • Ω' := by
    refine Eq.trans ?_ (Scheme.Modules.restrict_smul_eq ⊤ c' Ω').symm
    change σ.app (U.1.ι ''ᵁ ⊤) (Scheme.Modules.toUnitSection _ 1) =
      X.presheaf.map (homOfLE hi).op c • N.presheaf.map (homOfLE hi).op Ω
    rw [← map_toUnitSection_one (homOfLE hi), app_map, hσ, Scheme.Modules.map_smul]

  have htt_smul : ∀ (g : Γ((U.1 : Scheme.{u}), ⊤)) (y : Γ(N.restrict U.1.ι, ⊤)),
      τ.hom.app ⊤ (g • y) = g • τ.hom.app ⊤ y := fun g y => Scheme.Modules.Hom.app_smul τ.hom g y
  have htt_surj : Function.Surjective (τ.hom.app ⊤) := fun z => ⟨τ.inv.app ⊤ z, by
    change (τ.inv.app ⊤ ≫ τ.hom.app ⊤) z = z
    rw [← Scheme.Modules.Hom.comp_app, τ.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl⟩

  have hΩ' : Scheme.Modules.IsFrameOn (N.presheaf.map (homOfLE hi).op Ω) (U.1.ι ''ᵁ ⊤) :=
    (hΩ.map (homOfLE hi)).mono hi
  let u : Γ((U.1 : Scheme.{u}), ⊤) := Scheme.Modules.ofUnitSection ⊤ (τ.hom.app ⊤ Ω')
  have hu : IsUnit u := by
    obtain ⟨y, hy⟩ := htt_surj (Scheme.Modules.toUnitSection ⊤ 1)
    obtain ⟨g, hg⟩ := (hΩ' le_rfl le_rfl).2 (show Γ(N, U.1.ι ''ᵁ ⊤) from y)

    have hg' : (show Γ((U.1 : Scheme.{u}), ⊤) from g) • Ω' = y := by
      rw [Scheme.Modules.restrict_smul_eq]
      simp at hg
      exact hg
    refine isUnit_iff_exists_inv'.mpr ⟨g, ?_⟩
    have h1 := congrArg (fun m => Scheme.Modules.ofUnitSection ⊤ (τ.hom.app ⊤ m)) hg'
    simp only at h1
    rw [htt_smul, Scheme.Modules.ofUnitSection_smul, hy, Scheme.Modules.ofUnitSection_toUnitSection] at h1
    exact h1

  have hcoeff : Scheme.Modules.coeff σ U.1 τ.hom = U.1.topIso.hom (c' * u) := by
    unfold Scheme.Modules.coeff
    rw [hres, htt_smul, Scheme.Modules.ofUnitSection_smul]
  rw [hcoeff, map_mul, Ideal.span_singleton_mul_right_unit (hu.map _)]

  congr 2
  change U.1.topIso.hom (X.presheaf.map (homOfLE hi).op c) = _
  rw [Scheme.Opens.topIso_hom]
  exact presheaf_map_map (homOfLE hi) _ (homOfLE hUV) c

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul (solution)
