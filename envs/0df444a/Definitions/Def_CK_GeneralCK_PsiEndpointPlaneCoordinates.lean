-- Prove2me | Definitions.Def_CK_GeneralCK_PsiEndpointPlaneCoordinates
-- name    : CK_GeneralCK_PsiEndpointPlaneCoordinates
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T12:09:05.733826+00:00
-- url     : https://prove2.me/theorems/12030e88-0232-4890-912b-80b12496522c
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiEndpointPlaneCoordinates` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiEndpointPlaneCoordinates` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiEndpointPlaneCoordinates` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiEndpointPlaneCoordinates (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiEndpointPlaneCoordinates.lean)

import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneQuotientDefs
import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneGraph

-- ===== source module GeneralCK.PsiEndpointPlaneCoordinates =====
section

/-!
# Original-coordinate stationary-contact uniqueness

The change of variables `r=x/y`, `s=(1-y)/(1-x)` bijects the strict ordered
triangle with the open unit square. The logarithmic contact equations in
the original coordinates are exactly the level functions whose uniqueness
was proved using the explicit graph and positive Jacobian.
-/

namespace GeneralCK.PsiEndpointPlane

open Set

theorem contact_ratios_mem {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    x / y ∈ Ioo 0 1 ∧ (1 - y) / (1 - x) ∈ Ioo 0 1 := by
  have hy0 : 0 < y := hx.trans hxy
  have hx1 : 0 < 1 - x := by linarith
  exact ⟨⟨div_pos hx hy0, (div_lt_one hy0).mpr hxy⟩,
    ⟨div_pos (sub_pos.mpr hy) hx1, (div_lt_one hx1).mpr (by linarith)⟩⟩

theorem contact_reconstruct_right {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    (1 - (1 - y) / (1 - x)) / (1 - (x / y) * ((1 - y) / (1 - x))) = y := by
  have hh := contact_ratios_mem hx hxy hy
  have hden := (sub_pos.mpr (product_lt_one hh.1 hh.2)).ne'
  have hyne := (hx.trans hxy).ne'
  have hxne : 1 - x ≠ 0 := by linarith
  apply (div_eq_iff hden).mpr
  field_simp [hyne, hxne]
  ring

theorem contact_reconstruct_left {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    (x / y) *
      ((1 - (1 - y) / (1 - x)) / (1 - (x / y) * ((1 - y) / (1 - x)))) = x := by
  rw [contact_reconstruct_right hx hxy hy, div_mul_cancel₀ _ (hx.trans hxy).ne']

theorem contact_reconstruct_left_complement {x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    (1 - x / y) / (1 - (x / y) * ((1 - y) / (1 - x))) = 1 - x := by
  have hh := contact_ratios_mem hx hxy hy
  have hden := (sub_pos.mpr (product_lt_one hh.1 hh.2)).ne'
  have hyne := (hx.trans hxy).ne'
  have hxne : 1 - x ≠ 0 := by linarith
  apply (div_eq_iff hden).mpr
  field_simp [hyne, hxne]
  ring

theorem singularPart_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    singularPart (x / y) = (x - y) ^ 2 / (2 * x * y) := by
  unfold singularPart
  field_simp [hx.ne', hy.ne']
  ring

theorem contactLevel1_eq_level1 {A B x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    contactLevel1 A B x y = level1 A B (x / y) ((1 - y) / (1 - x)) := by
  unfold level1
  rw [contact_reconstruct_right hx hxy hy, singularPart_ratio hx (hx.trans hxy),
    Real.log_div hx.ne' (hx.trans hxy).ne']
  unfold contactLevel1
  ring

theorem contactLevel0_eq_level0 {A B x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    contactLevel0 A B x y = level0 A B (x / y) ((1 - y) / (1 - x)) := by
  have hy1 : 0 < 1 - y := sub_pos.mpr hy
  have hx1 : 0 < 1 - x := by linarith
  unfold level0
  rw [contact_reconstruct_left_complement hx hxy hy, singularPart_ratio hy1 hx1,
    Real.log_div hy1.ne' hx1.ne']
  unfold contactLevel0
  ring

/-- Uniqueness in the original `(x,y)` contact coordinates, for arbitrary
nonnegative target levels. -/
theorem original_contact_levels_unique {A B K1 K0 x y x' y' : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B) (hK1 : 0 ≤ K1) (hK0 : 0 ≤ K0)
    (hxy : (x, y) ∈ triangle) (hxy' : (x', y') ∈ triangle)
    (h1 : contactLevel1 A B x y = K1) (h0 : contactLevel0 A B x y = K0)
    (h1' : contactLevel1 A B x' y' = K1) (h0' : contactLevel0 A B x' y' = K0) :
    x = x' ∧ y = y' := by
  change 0 < x ∧ x < y ∧ y < 1 at hxy
  change 0 < x' ∧ x' < y' ∧ y' < 1 at hxy'
  have hrat := contact_ratios_mem hxy.1 hxy.2.1 hxy.2.2
  have hrat' := contact_ratios_mem hxy'.1 hxy'.2.1 hxy'.2.2
  have heq := stationary_level_system_unique hA hB hAB hK1 hK0
    hrat.1 hrat.2 hrat'.1 hrat'.2
    ((contactLevel1_eq_level1 hxy.1 hxy.2.1 hxy.2.2).symm.trans h1)
    ((contactLevel0_eq_level0 hxy.1 hxy.2.1 hxy.2.2).symm.trans h0)
    ((contactLevel1_eq_level1 hxy'.1 hxy'.2.1 hxy'.2.2).symm.trans h1')
    ((contactLevel0_eq_level0 hxy'.1 hxy'.2.1 hxy'.2.2).symm.trans h0')
  have hey : y = y' := by
    rw [← contact_reconstruct_right hxy.1 hxy.2.1 hxy.2.2,
      heq.1, heq.2, contact_reconstruct_right hxy'.1 hxy'.2.1 hxy'.2.2]
  have hex : x = x' := by
    rw [hey] at heq
    exact (div_left_inj' (hxy'.1.trans hxy'.2.1).ne').mp heq.1
  exact ⟨hex, hey⟩

/-- The zero-level stationary system used by the global supporting plane. -/
theorem original_contact_system_unique {A B x y x' y' : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B)
    (hxy : (x, y) ∈ triangle) (hxy' : (x', y') ∈ triangle)
    (h1 : contactLevel1 A B x y = 0) (h0 : contactLevel0 A B x y = 0)
    (h1' : contactLevel1 A B x' y' = 0) (h0' : contactLevel0 A B x' y' = 0) :
    x = x' ∧ y = y' :=
  original_contact_levels_unique hA hB hAB le_rfl le_rfl hxy hxy' h1 h0 h1' h0'

#print axioms contactLevel1_eq_level1
#print axioms contactLevel0_eq_level0
#print axioms original_contact_system_unique

end GeneralCK.PsiEndpointPlane

end


