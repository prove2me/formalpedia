-- Prove2me | Definitions.Def_CK_GeneralCK_PsiEndpointPlaneDifferential
-- name    : CK_GeneralCK_PsiEndpointPlaneDifferential
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:13:13.283857+00:00
-- url     : https://prove2.me/theorems/f5f78aa4-3096-4bbf-ae9a-9238e0c2ee61
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiEndpointPlaneDifferential` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiEndpointPlaneDifferential` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiEndpointPlaneDifferential` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiEndpointPlaneDifferential (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiEndpointPlaneDifferential.lean)

import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneNoFold

-- ===== source module GeneralCK.PsiEndpointPlaneDifferential =====
section

/-!
# Differential form of the endpoint no-fold argument

The concrete level functions have a strictly positive Jacobian determinant
at their nonnegative levels. Along any differentiable first-level curve,
the second level therefore has strictly positive derivative wherever it is
nonnegative. This file proves the derivatives from the logarithmic formulas.
-/

namespace GeneralCK.PsiEndpointPlane

open Set Filter

noncomputable def partial1r (A B r s : ℝ) : ℝ :=
  (r ^ 2 - 1) / (2 * r ^ 2) + A / r + (A + B) * s / (1 - r * s)

noncomputable def partial1s (A B r s : ℝ) : ℝ :=
  -(A + B) * (1 - r) / ((1 - s) * (1 - r * s))

noncomputable def partial0r (A B r s : ℝ) : ℝ :=
  -(A + B) * (1 - s) / ((1 - r) * (1 - r * s))

noncomputable def partial0s (A B r s : ℝ) : ℝ :=
  (s ^ 2 - 1) / (2 * s ^ 2) + B / s + (A + B) * r / (1 - r * s)

theorem product_lt_one {r s : ℝ} (hr : r ∈ Ioo 0 1) (hs : s ∈ Ioo 0 1) :
    r * s < 1 :=
  (mul_lt_mul_of_pos_right hr.2 hs.1).trans (by simpa using hs.2)

theorem hasDerivAt_singularPart {r : ℝ} (hr : 0 < r) :
    HasDerivAt singularPart ((r ^ 2 - 1) / (2 * r ^ 2)) r := by
  have hd := (((hasDerivAt_id r).const_sub 1).pow 2).div
    ((hasDerivAt_id r).const_mul 2) (by positivity : (2 : ℝ) * r ≠ 0)
  convert! hd using 1
  dsimp only [id_eq, Pi.pow_apply]
  field_simp [hr.ne']
  ring

theorem level1_eq_log_split {A B r s : ℝ}
    (hr : r ∈ Ioo 0 1) (hs : s ∈ Ioo 0 1) :
    level1 A B r s = singularPart r + A * Real.log r +
      (A + B) * (Real.log (1 - s) - Real.log (1 - r * s)) := by
  unfold level1
  rw [Real.log_div (by linarith [hs.2] : 1 - s ≠ 0)
    (by linarith [product_lt_one hr hs] : 1 - r * s ≠ 0)]

/-- The complete chain rule for the first level function. -/
theorem hasDerivAt_level1_along {A B p dx dy : ℝ} {x y : ℝ → ℝ}
    (hx : x p ∈ Ioo 0 1) (hy : y p ∈ Ioo 0 1)
    (hdx : HasDerivAt x dx p) (hdy : HasDerivAt y dy p) :
    HasDerivAt (fun z => level1 A B (x z) (y z))
      (partial1r A B (x p) (y p) * dx + partial1s A B (x p) (y p) * dy) p := by
  have h1y : 1 - y p ≠ 0 := by linarith [hy.2]
  have h1xy : 1 - x p * y p ≠ 0 := by linarith [product_lt_one hx hy]
  have hg := (hasDerivAt_singularPart hx.1).comp p hdx
  have hlx := (hdx.log hx.1.ne').const_mul A
  have hly := (hdy.const_sub 1).log h1y
  have hlxy := ((hdx.mul hdy).const_sub 1).log h1xy
  have hd := (hg.add hlx).add ((hly.sub hlxy).const_mul (A + B))
  have heq : (fun z => level1 A B (x z) (y z)) =ᶠ[nhds p]
      (fun z => singularPart (x z) + A * Real.log (x z) +
        (A + B) * (Real.log (1 - y z) - Real.log (1 - x z * y z))) := by
    filter_upwards [hdx.continuousAt (Ioo_mem_nhds hx.1 hx.2),
      hdy.continuousAt (Ioo_mem_nhds hy.1 hy.2)] with z hz hz'
    exact level1_eq_log_split hz hz'
  convert! hd.congr_of_eventuallyEq heq using 1
  dsimp only [partial1r, partial1s, Pi.mul_apply]
  field_simp [hx.1.ne', h1y, h1xy]
  ring

theorem level0_swap (A B r s : ℝ) : level0 A B r s = level1 B A s r := by
  simp only [level0, level1, add_comm A B, mul_comm r s]

/-- The complete chain rule for the second level function. -/
theorem hasDerivAt_level0_along {A B p dx dy : ℝ} {x y : ℝ → ℝ}
    (hx : x p ∈ Ioo 0 1) (hy : y p ∈ Ioo 0 1)
    (hdx : HasDerivAt x dx p) (hdy : HasDerivAt y dy p) :
    HasDerivAt (fun z => level0 A B (x z) (y z))
      (partial0r A B (x p) (y p) * dx + partial0s A B (x p) (y p) * dy) p := by
  have hd := hasDerivAt_level1_along (A := B) (B := A) hy hx hdy hdx
  convert! hd using 1
  · funext z
    exact level0_swap A B (x z) (y z)
  · simp only [partial0r, partial0s, partial1r, partial1s, mul_comm (x p) (y p),
      add_comm A B]
    ring

/-- Exact Jacobian numerator. All logarithms disappear after differentiation. -/
theorem level_jacobian_identity {A B r s : ℝ}
    (hr : r ∈ Ioo 0 1) (hs : s ∈ Ioo 0 1) :
    partial1r A B r s * partial0s A B r s -
      partial1s A B r s * partial0r A B r s =
        foldNumerator A B r s / (4 * r ^ 2 * s ^ 2) := by
  have hrn := hr.1.ne'
  have hsn := hs.1.ne'
  have h1r : 1 - r ≠ 0 := by linarith [hr.2]
  have h1s : 1 - s ≠ 0 := by linarith [hs.2]
  have h1rs : 1 - r * s ≠ 0 := by linarith [product_lt_one hr hs]
  unfold partial1r partial1s partial0r partial0s foldNumerator
  field_simp
  ring

theorem level_jacobian_pos {A B r s : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : r ∈ Ioo 0 1) (hs : s ∈ Ioo 0 1)
    (h1 : 0 ≤ level1 A B r s) (h0 : 0 ≤ level0 A B r s) :
    0 < partial1r A B r s * partial0s A B r s -
      partial1s A B r s * partial0r A B r s := by
  rw [level_jacobian_identity hr hs]
  exact div_pos (foldNumerator_pos_of_nonnegative_levels hA hB hr hs h1 h0)
    (by have := hr.1; have := hs.1; positivity)

theorem partial1s_neg {A B r s : ℝ}
    (hAB : 0 < A + B) (hr : r ∈ Ioo 0 1) (hs : s ∈ Ioo 0 1) :
    partial1s A B r s < 0 := by
  unfold partial1s
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_neg_of_pos (neg_neg_of_pos hAB) (sub_pos.mpr hr.2)
  · exact mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr (product_lt_one hr hs))

/-- Strict increase of the second level along a differentiable first-level
curve, whenever both levels are nonnegative. This is stronger than merely
excluding a fold at the point. -/
theorem level0_deriv_pos_along_level1 {A B r ds : ℝ} {curve : ℝ → ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B)
    (hr : r ∈ Ioo 0 1) (hs : curve r ∈ Ioo 0 1)
    (hc : HasDerivAt curve ds r)
    (hlevelDerivative : HasDerivAt (fun z => level1 A B z (curve z)) 0 r)
    (h1 : 0 ≤ level1 A B r (curve r)) (h0 : 0 ≤ level0 A B r (curve r)) :
    0 < deriv (fun z => level0 A B z (curve z)) r := by
  have hfirst := hasDerivAt_level1_along (A := A) (B := B) hr hs (hasDerivAt_id r) hc
  have hsecond := hasDerivAt_level0_along (A := A) (B := B) hr hs (hasDerivAt_id r) hc
  simp only [id_eq] at hfirst hsecond
  have hzero := hfirst.unique hlevelDerivative
  have hjac := level_jacobian_pos hA hB hr hs h1 h0
  have hnegative := partial1s_neg hAB hr hs
  rw [hsecond.deriv]
  simp only [mul_one] at hzero ⊢
  have hzeroMul := congrArg (fun z => z * partial0s A B r (curve r)) hzero
  have hproduct :
      (-partial1s A B r (curve r)) *
          (partial0r A B r (curve r) + partial0s A B r (curve r) * ds) =
        partial1r A B r (curve r) * partial0s A B r (curve r) -
          partial1s A B r (curve r) * partial0r A B r (curve r) := by
    nlinarith only [hzeroMul]
  have hp : 0 < (-partial1s A B r (curve r)) *
      (partial0r A B r (curve r) + partial0s A B r (curve r) * ds) := by
    rw [hproduct]
    exact hjac
  exact (mul_pos_iff_of_pos_left (neg_pos.mpr hnegative)).mp hp

#print axioms hasDerivAt_level1_along
#print axioms level_jacobian_identity
#print axioms level0_deriv_pos_along_level1

end GeneralCK.PsiEndpointPlane

end


