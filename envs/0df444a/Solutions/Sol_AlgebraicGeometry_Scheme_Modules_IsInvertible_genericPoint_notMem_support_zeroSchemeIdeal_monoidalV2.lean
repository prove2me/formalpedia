-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.genericPoint_notMem_support_zeroSchemeIdeal_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/0808c9fc-bef7-5e54-b04f-02dc920385e5

import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_genericPoint_notMem_support_zeroSchemeIdeal_monoidalV2

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Scheme.Modules.Hom.app_smul Scheme.Modules.Hom.mapPresheaf Scheme.Modules.Hom.zero_app Scheme.IdealSheafData.mem_support_iff basicOpen_eq_bot_iff Scheme.Modules.Hom.comp_app Scheme.Modules.Hom IsIntegral Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app Scheme.Modules Scheme.Opens Scheme.Opens.ι_image_top Scheme.IdealSheafData Scheme.Modules.toUnitSection Scheme.Modules.ofUnitSection Scheme.Modules.ofUnitSection_toUnitSection Scheme.Modules.ofUnitSection_injective Scheme.Modules.ofUnitSection_map Scheme.Modules.ofUnitSection_smul Scheme.Modules.restrictSection Scheme.Modules.coeff Scheme.Modules.zeroSchemeIdeal Scheme.Modules.IsInvertible Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Modules.hom_ext Modules.Hom.app_smul Modules.Hom.mapPresheaf Modules.Hom.zero_app IdealSheafData.mem_support_iff Hom.id_app Hom Γ Modules.Hom.comp_app Modules.Hom topIso Modules.mapPresheaf_app Modules.Hom.id_app mem_zeroLocus_iff affineOpens Hom.comp_app basicOpen Modules Opens Opens.ι_image_top restrict IdealSheafData Modules.toUnitSection Modules.ofUnitSection Modules.ofUnitSection_toUnitSection Modules.ofUnitSection_injective Modules.ofUnitSection_map Modules.ofUnitSection_smul Modules.restrictSection Modules.coeff Modules.zeroSchemeIdeal Modules.IsInvertible Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext Hom.app_smul Hom.mapPresheaf Hom.zero_app presheaf Hom.comp_app Hom mapPresheaf_app Hom.id_app isSheaf restrict toUnitSection ofUnitSection ofUnitSection_toUnitSection ofUnitSection_injective ofUnitSection_map ofUnitSection_smul restrictSection coeff zeroSchemeIdeal IsInvertible IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2" namespace IsInvertible p2m_export "AlgebraicGeometry.Scheme.Modules.IsInvertible" "exists_restrict_iso coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2" end AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.IsInvertible" in
alias AlgebraicGeometry.Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq := AlgebraicGeometry.Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_genericPoint_notMem_support_zeroSchemeIdeal_monoidalV2.AlgebraicGeometry TopologicalSpace Opposite"

namespace S3ZD

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

theorem eq_smul_toUnitSection_one {U : X.Opens} (m : Γ(𝟙_ X.Modules, U)) :
    m = Scheme.Modules.ofUnitSection U m • Scheme.Modules.toUnitSection U 1 := by
  apply Scheme.Modules.ofUnitSection_injective
  rw [Scheme.Modules.ofUnitSection_smul, Scheme.Modules.ofUnitSection_toUnitSection, mul_one]

theorem eq_zero_of_forall_app_one (φ : 𝟙_ X.Modules ⟶ M)
    (h : ∀ U : X.Opens, φ.app U (Scheme.Modules.toUnitSection U 1) = 0) : φ = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  rw [Scheme.Modules.Hom.zero_app]
  ext m
  rw [eq_smul_toUnitSection_one m, Scheme.Modules.Hom.app_smul, h U, smul_zero]
  rfl

theorem restrictSection_eq_zero (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (U : X.affineOpens) (τ : M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules)
    (hU : (Scheme.Modules.zeroSchemeIdeal s).ideal U = ⊥) :
    Scheme.Modules.restrictSection s U.1 = 0 := by
  obtain ⟨-, hloc⟩ := Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq hM s
  obtain ⟨hspan, -⟩ := hloc U τ
  have hc : Scheme.Modules.coeff s U.1 τ.hom = 0 := by
    have hmem : Scheme.Modules.coeff s U.1 τ.hom ∈ (Scheme.Modules.zeroSchemeIdeal s).ideal U := by
      rw [hspan]; exact Ideal.mem_span_singleton_self _
    rw [hU] at hmem
    exact (Submodule.mem_bot _).mp hmem
  have h3 : τ.hom.app ⊤ (Scheme.Modules.restrictSection s U.1) = 0 := by
    have hinj : Function.Injective (U.1.topIso.hom) :=
      U.1.topIso.commRingCatIsoToRingEquiv.injective
    have h4 : U.1.topIso.hom (Scheme.Modules.ofUnitSection ⊤
        (τ.hom.app ⊤ (Scheme.Modules.restrictSection s U.1))) = U.1.topIso.hom 0 := by
      rw [map_zero]; exact hc
    exact hinj h4
  have h5 : τ.inv.app ⊤ (τ.hom.app ⊤ (Scheme.Modules.restrictSection s U.1)) =
      Scheme.Modules.restrictSection s U.1 := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
      Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]
  rw [← h5, h3, map_zero]

end S3ZD

open S3ZD in
theorem solution
    {X : Scheme.{u}} [IsIntegral X] {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M) (hs : s ≠ 0) :
    genericPoint X ∉ (Scheme.Modules.zeroSchemeIdeal s).support := by
  intro hη
  apply hs

  have hA : ∀ U : X.affineOpens, (Scheme.Modules.zeroSchemeIdeal s).ideal U = ⊥ := by
    intro U
    refine (Submodule.eq_bot_iff _).mpr fun g hg => ?_
    have h1 := (Scheme.IdealSheafData.mem_support_iff.mp hη) U
    have h2 : genericPoint X ∉ X.basicOpen g := (X.mem_zeroLocus_iff _ _).mp h1 g hg
    by_contra hg0
    apply h2
    have hne : ((X.basicOpen g : X.Opens) : Set X).Nonempty := by
      rw [Set.nonempty_iff_ne_empty, Ne, Opens.coe_eq_empty, basicOpen_eq_bot_iff]
      exact hg0
    exact ((genericPoint_spec X).mem_open_set_iff (X.basicOpen g).isOpen).mpr (by simpa using hne)

  apply eq_zero_of_forall_app_one
  intro V
  have hcov : ∀ x : V, ∃ U : X.affineOpens, (x : X) ∈ U.1 ∧ U.1 ≤ V ∧
      Nonempty (M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules) :=
    fun x => hM.exists_restrict_iso x.2
  choose U hxU hUV hτ using hcov
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  refine TopCat.Sheaf.eq_of_locally_eq' F (fun x : V => (U x).1) V (fun x => homOfLE (hUV x))
    (fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxU ⟨y, hy⟩⟩) _ _ fun x => ?_
  rw [map_zero]
  change M.presheaf.map (homOfLE (hUV x)).op (s.app V (Scheme.Modules.toUnitSection V 1)) = 0
  rw [map_app_unit, map_toUnitSection_one]
  have hB := restrictSection_eq_zero hM s (U x) (hτ x).some (hA (U x))
  change s.app ((U x).1.ι ''ᵁ ⊤) (Scheme.Modules.toUnitSection ((U x).1.ι ''ᵁ ⊤) 1) = 0 at hB
  rw [Scheme.Opens.ι_image_top] at hB
  exact hB

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_genericPoint_notMem_support_zeroSchemeIdeal_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_genericPoint_notMem_support_zeroSchemeIdeal_monoidalV2 (solution)
