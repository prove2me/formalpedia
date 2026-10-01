-- Prove2me | Definitions.Def_CK_GeneralCK_FCSharp500
-- name    : CK_GeneralCK_FCSharp500
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:57:37.549223+00:00
-- url     : https://prove2.me/theorems/9633313d-fc7e-4138-938a-f4ae7b6672cd
-- title:
--   Courtade–Kumar proof module `GeneralCK.FCSharp500` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FCSharp500` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FCSharp500` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FCSharp500 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FCSharp500.lean)

import Definitions.Def_CK_GeneralCK_FCConst

-- ===== source module GeneralCK.FCSharp500 =====
section

/-!
# Lane F-C: the sharp eta decrement, and the high-ratio branch

Two pieces:

* `eta_decrement_fivehundredth` — the integrated form of `FCConst.neg_deriv_eta_sharp`,
  i.e. `eta x − eta y ≤ (17/10)·(log y − log x)` on `(0, 1/500]`.  The coefficient
  `17/10` is what buys the capped assembly its margin: the `21/10` valid on `(0,1/10]`
  leaves only 1% at the worst admissible point, and 1% is not a margin.

* `eta_decrement_caseB` — the branch `E/zm > 1/10` of the total decrement.  There the
  integration is done with `17/10` up to `1/500`, with `21/10` from `1/500` to `1/10`,
  and the last stretch is charged to the compiled numeric gap `eta (1/10) − eta (1/2)`.
  The activity hypothesis `2E < zm` caps `E/zm` below `1/2`, which is what makes the
  last step legal.

  Priced at the worst admissible point (`−log zm = 9.21`, `E/zm → 1/2`) BEFORE being
  written down: the bound is `(17/10)·(−log zm) + 4·(0.4·log 50 + 4.2)/4`, whose constant
  part is `(34/15)·log 2 + 21/5 ≤ 1.5867 + 4.2 = 5.7867 ≤ 29/5`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.FCSharp500

open GeneralCK

/-- `eta x − eta y ≤ (17/10)·(log y − log x)` on `(0, 1/500]`. -/
theorem eta_decrement_fivehundredth {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1 / 500) :
    eta x - eta y ≤ (17 / 10) * (Real.log y - Real.log x) := by
  rcases eq_or_lt_of_le hxy with heq | hlt
  · rw [heq]; simp
  · have hmono : MonotoneOn (fun t => eta t + (17 / 10) * Real.log t) (Set.Icc x y) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x y)
        (f' := fun t => deriv eta t + (17 / 10) * t⁻¹)
      · intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le hx ht.1
        have ht1 : t < 1 := by have := ht.2; linarith
        have hda := hasDerivAt_eta ht0 ht1
        have h1 : HasDerivAt eta (deriv eta t) t := by rwa [hda.deriv]
        have h2 : HasDerivAt (fun u : ℝ => (17 / 10) * Real.log u) ((17 / 10) * t⁻¹) t :=
          (Real.hasDerivAt_log ht0.ne').const_mul (17 / 10 : ℝ)
        exact (h1.add h2).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have ht0 : 0 < t := lt_trans hx ht.1
        have ht1 : t < 1 := by have := ht.2; linarith
        have hda := hasDerivAt_eta ht0 ht1
        have h1 : HasDerivAt eta (deriv eta t) t := by rwa [hda.deriv]
        have h2 : HasDerivAt (fun u : ℝ => (17 / 10) * Real.log u) ((17 / 10) * t⁻¹) t :=
          (Real.hasDerivAt_log ht0.ne').const_mul (17 / 10 : ℝ)
        exact (h1.add h2).hasDerivWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have ht0 : 0 < t := lt_trans hx ht.1
        have htle : t ≤ 1 / 500 := by have := ht.2; linarith
        have hb := FCConst.neg_deriv_eta_sharp ht0 htle
        have hinv : (17 / 10 : ℝ) * t⁻¹ = (17 / 10) / t := by field_simp
        linarith [hb, hinv]
    have hres := hmono (Set.left_mem_Icc.2 hxy) (Set.right_mem_Icc.2 hxy) hxy
    simp only at hres
    linarith

/-- **The high-ratio branch of the capped decrement.**  When `E/Z > 1/10` the direct
integration at `21/10` is too expensive; splitting the range at `1/500` and paying the
compiled numeric gap for the top stretch costs `29/5` but drops the slope to `17/10`. -/
theorem eta_decrement_caseB {E Z : ℝ} (hE : 0 < E) (hEsmall : E ≤ 1 / 500)
    (hZ : 0 < Z) (h2E : 2 * E < Z) (hcase : 1 / 10 < E / Z) :
    eta E - eta (E / Z) ≤ (17 / 10) * (-Real.log Z) + 29 / 5 := by
  have hl2pos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hl2ub := FCAnalytic.log_two_ub
  have hl2lb := FCAnalytic.log_two_lb
  have hT := FCRay.log_ten_upper
  have hratio_pos : 0 < E / Z := div_pos hE hZ
  have hratio_half : E / Z < 1 / 2 := by
    rw [div_lt_iff₀ hZ]; linarith
  -- the four steps of the chain
  have h1 := eta_decrement_fivehundredth hE hEsmall (le_refl (1 / 500 : ℝ))
  have h2 := FCSharp.eta_decrement_tenth (show (0 : ℝ) < 1 / 500 by norm_num)
      (show (1 : ℝ) / 500 ≤ 1 / 10 by norm_num) (le_refl (1 / 10 : ℝ))
  have h3 := FCSharp.eta_gap_sharp
  have h4 : eta (1 / 2 : ℝ) ≤ eta (E / Z) := by
    apply eta_antitoneOn
      (show (E / Z) ∈ Set.Ioc (0 : ℝ) 1 from ⟨hratio_pos, by linarith⟩)
      (show (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 by constructor <;> norm_num)
    linarith
  -- the logarithms of the two anchors
  have hlog500 : Real.log (1 / 500 : ℝ) = Real.log 2 - 3 * Real.log 10 := by
    rw [show (1 : ℝ) / 500 = 2 / (10 : ℝ) ^ (3 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  have hlog10 : Real.log (1 / 10 : ℝ) = -Real.log 10 := by
    rw [show (1 : ℝ) / 10 = (10 : ℝ)⁻¹ by norm_num, Real.log_inv]
  -- the case hypothesis, cleared of its denominator
  have hZ10E : Z < 10 * E := by
    have hZne : Z ≠ 0 := ne_of_gt hZ
    have hpos : (0 : ℝ) < E / Z - 1 / 10 := by linarith
    have hmulpos : 0 < (E / Z - 1 / 10) * Z := mul_pos hpos hZ
    have hdc : E / Z * Z = E := by field_simp
    have hid : (E / Z - 1 / 10) * Z = E / Z * Z - Z / 10 := by ring
    rw [hid, hdc] at hmulpos
    linarith
  have hlogZE : Real.log Z ≤ Real.log 10 + Real.log E := by
    have h := Real.log_le_log hZ hZ10E.le
    rwa [Real.log_mul (by norm_num) hE.ne'] at h
  linarith [h1, h2, h3, h4, hlog500, hlog10, hlogZE, hT, hl2ub, hl2lb]

#check @eta_decrement_fivehundredth
#check @eta_decrement_caseB
#print axioms eta_decrement_fivehundredth
#print axioms eta_decrement_caseB

end GeneralCK.FCSharp500

end


