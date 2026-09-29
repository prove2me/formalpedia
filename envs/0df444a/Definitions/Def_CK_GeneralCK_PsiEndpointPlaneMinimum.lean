-- Prove2me | Definitions.Def_CK_GeneralCK_PsiEndpointPlaneMinimum
-- name    : CK_GeneralCK_PsiEndpointPlaneMinimum
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:20:33.853077+00:00
-- url     : https://prove2.me/theorems/9b4840d5-660b-4da6-bf20-27ac7fc30751
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiEndpointPlaneMinimum` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiEndpointPlaneMinimum` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiEndpointPlaneMinimum` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiEndpointPlaneMinimum (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiEndpointPlaneMinimum.lean)

import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneQuotientDefs
import Definitions.Def_CK_GeneralCK_ProfileDerivatives
import Mathlib.Topology.Order.Compact

-- ===== source module GeneralCK.PsiEndpointPlaneMinimum =====
section

/-!
# The endpoint quotient attains its minimum in the open triangle

Explicit entropy and log-ratio estimates place every fixed sublevel inside
a compact subset of the open triangle. No coercivity premise is assumed.
-/

namespace GeneralCK.PsiEndpointPlane
open Set

theorem quotient_log_decomposition {A B x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    quotient A B x y =
      (Real.log (y / x) + Real.log ((1 - x) / (1 - y))) / 2 +
        A * Real.binEntropy x / (y - x) + B * Real.binEntropy y / (y - x) := by
  have hx1 : x < 1 := hxy.trans hy
  have hy0 : 0 < y := hx.trans hxy
  unfold quotient naturalCost interiorCost J
  rw [Real.log_div (by linarith : 1 - x ≠ 0) hx.ne',
    Real.log_div (by linarith : 1 - y ≠ 0) hy0.ne',
    Real.log_div hy0.ne' hx.ne',
    Real.log_div (by linarith : 1 - x ≠ 0) (by linarith : 1 - y ≠ 0)]
  field_simp [log_two_pos.ne', sub_ne_zero.mpr hxy.ne']
  ring

theorem quotient_pos {A B x y : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hx : 0 < x) (hxy : x < y) (hy : y < 1) : 0 < quotient A B x y := by
  have hx1 := hxy.trans hy
  have hy0 := hx.trans hxy
  have hgap : 0 < y - x := sub_pos.mpr hxy
  have hlog₁ : 0 ≤ Real.log (y / x) :=
    Real.log_nonneg ((le_div_iff₀ hx).2 (by linarith))
  have hlog₂ : 0 ≤ Real.log ((1 - x) / (1 - y)) :=
    Real.log_nonneg ((le_div_iff₀ (by linarith : 0 < 1 - y)).2 (by linarith))
  have he₁ := Real.binEntropy_pos hx hx1
  have he₂ := Real.binEntropy_pos hy0 hy
  rw [quotient_log_decomposition hx hxy hy]
  positivity

private theorem entropy_terms {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    x * (-Real.log x) ≤ Real.binEntropy x ∧
    (1 - x) * (-Real.log (1 - x)) ≤ Real.binEntropy x ∧
    x * (1 - x) ≤ Real.binEntropy x := by
  have hlogx : 0 ≤ -Real.log x := neg_nonneg.mpr (Real.log_nonpos hx.le hx1.le)
  have hlogc : 0 ≤ -Real.log (1 - x) :=
    neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))
  have hlower : x ≤ -Real.log (1 - x) := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 - x)]
  have he : Real.binEntropy x = x * (-Real.log x) + (1 - x) * (-Real.log (1 - x)) := by
    simp only [Real.binEntropy, Real.log_inv]
  have hp := mul_nonneg hx.le hlogx
  have hq := mul_nonneg (show 0 ≤ 1 - x by linarith) hlogc
  have hr := mul_le_mul_of_nonneg_left hlower (show 0 ≤ 1 - x by linarith)
  rw [he]
  constructor
  · linarith
  constructor <;> nlinarith

/-- Four separate, nonnegative contributions cannot exceed the sublevel. -/
theorem sublevel_core_bounds {A B M x y : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hx : 0 < x) (hxy : x < y) (hy : y < 1) (hM : quotient A B x y ≤ M) :
    0 < M ∧ Real.log (y / x) ≤ 2 * M ∧
      Real.log ((1 - x) / (1 - y)) ≤ 2 * M ∧
      A * Real.binEntropy x ≤ M * (y - x) ∧
      B * Real.binEntropy y ≤ M * (y - x) := by
  have hM0 := (quotient_pos hA hB hx hxy hy).trans_le hM
  have hgap : 0 < y - x := sub_pos.mpr hxy
  have hlog₁ : 0 ≤ Real.log (y / x) :=
    Real.log_nonneg ((le_div_iff₀ hx).2 (by linarith))
  have hlog₂ : 0 ≤ Real.log ((1 - x) / (1 - y)) :=
    Real.log_nonneg ((le_div_iff₀ (by linarith : 0 < 1 - y)).2 (by linarith))
  have he₁ : 0 ≤ A * Real.binEntropy x / (y - x) := by
    exact div_nonneg (mul_nonneg hA.le (Real.binEntropy_nonneg hx.le (hxy.trans hy).le)) hgap.le
  have he₂ : 0 ≤ B * Real.binEntropy y / (y - x) := by
    exact div_nonneg (mul_nonneg hB.le (Real.binEntropy_nonneg (hx.trans hxy).le hy.le)) hgap.le
  rw [quotient_log_decomposition hx hxy hy] at hM
  refine ⟨hM0, by linarith, by linarith, ?_, ?_⟩
  · apply (div_le_iff₀ hgap).1
    linarith
  · apply (div_le_iff₀ hgap).1
    linarith

noncomputable def sublevelFloor (C M : ℝ) : ℝ := Real.exp (-M / C - 2 * M)

theorem sublevel_coordinates {A B M x y : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hx : 0 < x) (hxy : x < y) (hy : y < 1) (hM : quotient A B x y ≤ M) :
    sublevelFloor B M ≤ x ∧ sublevelFloor A M ≤ 1 - y := by
  obtain ⟨hM0, hlx, hly, hAx, hBy⟩ := sublevel_core_bounds hA hB hx hxy hy hM
  have hx1 := hxy.trans hy
  have hy0 := hx.trans hxy
  have hxc : 0 < 1 - x := by linarith
  have hyc : 0 < 1 - y := by linarith
  have hlogy : -M / B ≤ Real.log y := by
    have hent := mul_le_mul_of_nonneg_left (entropy_terms hy0 hy).1 hB.le
    have hden : B * (-Real.log y) ≤ M := by
      have hg := mul_le_mul_of_nonneg_left (show y - x ≤ y by linarith) hM0.le
      nlinarith
    apply (div_le_iff₀ hB).2
    nlinarith
  have hlogcx : -M / A ≤ Real.log (1 - x) := by
    have hent := mul_le_mul_of_nonneg_left (entropy_terms hx hx1).2.1 hA.le
    have hden : A * (-Real.log (1 - x)) ≤ M := by
      have hg := mul_le_mul_of_nonneg_left (show y - x ≤ 1 - x by linarith) hM0.le
      nlinarith
    apply (div_le_iff₀ hA).2
    nlinarith
  rw [Real.log_div hy0.ne' hx.ne'] at hlx
  rw [Real.log_div hxc.ne' hyc.ne'] at hly
  constructor
  · exact (Real.le_log_iff_exp_le hx).1 (by linarith)
  · exact (Real.le_log_iff_exp_le hyc).1 (by linarith)

/-- A positive separation from the diagonal follows from the entropy term. -/
theorem sublevel_gap {A B M x y : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hx : 0 < x) (hxy : x < y) (hy : y < 1) (hM : quotient A B x y ≤ M) :
    A * sublevelFloor B M * sublevelFloor A M / M ≤ y - x := by
  obtain ⟨hM0, _, _, hAx, _⟩ := sublevel_core_bounds hA hB hx hxy hy hM
  obtain ⟨hxl, hyl⟩ := sublevel_coordinates hA hB hx hxy hy hM
  have hfloorA : 0 ≤ sublevelFloor A M := (Real.exp_pos _).le
  have hfloorB : 0 ≤ sublevelFloor B M := (Real.exp_pos _).le
  have hprod : sublevelFloor B M * sublevelFloor A M ≤ x * (1 - x) := by
    exact mul_le_mul hxl (hyl.trans (by linarith)) hfloorA hx.le
  have hb := hprod.trans (entropy_terms hx (hxy.trans hy)).2.2
  have hh := (mul_le_mul_of_nonneg_left hb hA.le).trans hAx
  apply (div_le_iff₀ hM0).2
  nlinarith

noncomputable def sublevelBox (A B M : ℝ) : Set (ℝ × ℝ) :=
  (Icc (sublevelFloor B M) 1 ×ˢ Icc 0 (1 - sublevelFloor A M)) ∩
    {p | A * sublevelFloor B M * sublevelFloor A M / M ≤ p.2 - p.1}

theorem isCompact_sublevelBox (A B M : ℝ) : IsCompact (sublevelBox A B M) := by
  apply (isCompact_Icc.prod isCompact_Icc).inter_right
  exact isClosed_le continuous_const (continuous_snd.sub continuous_fst)

theorem sublevelBox_subset_triangle {A B M : ℝ} (hA : 0 < A) (hM : 0 < M) :
    sublevelBox A B M ⊆ triangle := by
  intro p hp
  have hfloorA : 0 < sublevelFloor A M := Real.exp_pos _
  have hfloorB : 0 < sublevelFloor B M := Real.exp_pos _
  have hgap : 0 < A * sublevelFloor B M * sublevelFloor A M / M := by positivity
  have hxp : sublevelFloor B M ≤ p.1 := hp.1.1.1
  have hyp : p.2 ≤ 1 - sublevelFloor A M := hp.1.2.2
  have hgp : A * sublevelFloor B M * sublevelFloor A M / M ≤ p.2 - p.1 := hp.2
  exact ⟨by linarith, by linarith, by linarith⟩

theorem mem_sublevelBox {A B M : ℝ} (hA : 0 < A) (hB : 0 < B)
    {p : ℝ × ℝ} (hp : p ∈ triangle) (hM : quotient A B p.1 p.2 ≤ M) :
    p ∈ sublevelBox A B M := by
  obtain ⟨hx, hxy, hy⟩ := hp
  obtain ⟨hlx, hly⟩ := sublevel_coordinates hA hB hx hxy hy hM
  have hgap := sublevel_gap hA hB hx hxy hy hM
  exact ⟨⟨⟨hlx, (hxy.trans hy).le⟩, ⟨(hx.trans hxy).le, by linarith⟩⟩, hgap⟩

theorem quotient_continuousOn_triangle (A B : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => quotient A B p.1 p.2) triangle := by
  intro p hp
  obtain ⟨hx, hxy, hy⟩ := hp
  have hJx : ContinuousWithinAt (fun z : ℝ × ℝ => J z.1) triangle p :=
    (hasDerivAt_J hx (hxy.trans hy)).continuousAt.comp_continuousWithinAt
      continuous_fst.continuousWithinAt
  have hJy : ContinuousWithinAt (fun z : ℝ × ℝ => J z.2) triangle p :=
    (hasDerivAt_J (hx.trans hxy) hy).continuousAt.comp_continuousWithinAt
      continuous_snd.continuousWithinAt
  have heX : ContinuousWithinAt (fun z : ℝ × ℝ => Real.binEntropy z.1) triangle p :=
    (Real.binEntropy_continuous.comp continuous_fst).continuousWithinAt
  have heY : ContinuousWithinAt (fun z : ℝ × ℝ => Real.binEntropy z.2) triangle p :=
    (Real.binEntropy_continuous.comp continuous_snd).continuousWithinAt
  have hgap : ContinuousWithinAt (fun z : ℝ × ℝ => z.2 - z.1) triangle p :=
    (continuous_snd.sub continuous_fst).continuousWithinAt
  have hcost := ((hgap.mul (hJx.sub hJy)).div_const 2).const_mul (Real.log 2)
  exact ((hcost.add (heX.const_mul A)).add (heY.const_mul B)).div hgap
    (sub_ne_zero.mpr hxy.ne')

/-- A positive-entropy-coefficient endpoint quotient attains its global
minimum strictly inside the open triangle. The compact set is explicitly
constructed from a fixed, finite interior sublevel. -/
theorem quotient_attains_minimum {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∃ p ∈ triangle, IsMinOn (fun z : ℝ × ℝ => quotient A B z.1 z.2) triangle p := by
  let p₀ : ℝ × ℝ := (1 / 4, 3 / 4)
  let M := quotient A B p₀.1 p₀.2
  have hp₀ : p₀ ∈ triangle := by norm_num [p₀, triangle]
  have hM : 0 < M := quotient_pos hA hB hp₀.1 hp₀.2.1 hp₀.2.2
  have hanchor : p₀ ∈ sublevelBox A B M := mem_sublevelBox hA hB hp₀ le_rfl
  have hsub := sublevelBox_subset_triangle (B := B) hA hM
  obtain ⟨p, hp, hmin⟩ := (isCompact_sublevelBox A B M).exists_isMinOn
    ⟨p₀, hanchor⟩ ((quotient_continuousOn_triangle A B).mono hsub)
  refine ⟨p, hsub hp, ?_⟩
  intro z hz
  by_cases hval : quotient A B z.1 z.2 ≤ M
  · exact hmin (mem_sublevelBox hA hB hz hval)
  · exact (hmin hanchor).trans (lt_of_not_ge hval).le

theorem isOpen_triangle : IsOpen triangle := by
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_snd).inter (isOpen_lt continuous_snd continuous_const))

theorem quotient_has_local_minimum {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∃ p ∈ triangle, IsLocalMin (fun z : ℝ × ℝ => quotient A B z.1 z.2) p := by
  obtain ⟨p, hp, hmin⟩ := quotient_attains_minimum hA hB
  exact ⟨p, hp, hmin.isLocalMin (isOpen_triangle.mem_nhds hp)⟩

#print axioms quotient_log_decomposition
#print axioms sublevel_core_bounds
#print axioms sublevel_coordinates
#print axioms sublevel_gap
#print axioms isCompact_sublevelBox
#print axioms quotient_continuousOn_triangle
#print axioms quotient_attains_minimum
#print axioms quotient_has_local_minimum

end GeneralCK.PsiEndpointPlane

end


