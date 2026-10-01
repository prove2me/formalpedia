-- Prove2me | Definitions.Def_CK_GeneralCK_FCRay
-- name    : CK_GeneralCK_FCRay
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T01:29:08.25626+00:00
-- url     : https://prove2.me/theorems/edc267fd-de83-44d7-92df-96e57751f756
-- title:
--   Courtade–Kumar proof module `GeneralCK.FCRay` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FCRay` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FCRay` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FCRay (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FCRay.lean)

import Definitions.Def_CK_GeneralCK_FCActive
import Definitions.Def_CK_GeneralCK_EntropyRadialDerivatives

-- ===== source module GeneralCK.FCRay =====
section

/-!
# Lane F-C: the ray construction, supporting lemmas

* `H_small_upper` — `H q ≤ 1/500` for `0 < q ≤ 1/10000`, which is what turns the
  owner's `E ≤ (H a + H b)/2` into the `E ≤ 1/500` that the analytic layer needs;
* `deriv_eta_increment` — `eta' y − eta' x ≤ (2/x²)(y − x)`;
* `deriv_phi_sub` — `deriv (phi m) h = deriv eta h − deriv (F (1−2m)) h`;
* `deriv_F_entropy_ray` — the radial derivative depends on `(z,h)` only through
  `z/h`, so the two ray tangents have equal `F`-slopes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.FCRay

open GeneralCK

theorem log_ten_upper : Real.log 10 ≤ (10 / 3 : ℝ) * Real.log 2 := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 10 ^ (3 : ℕ))
    (by norm_num : (10 : ℝ) ^ (3 : ℕ) ≤ 2 ^ (10 : ℕ))
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

theorem H_ten_thousandth_upper : H (1 / 10000) ≤ 1 / 500 := by
  have hLpos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hL := FCAnalytic.log_two_lb
  have hlog4 : Real.log 10000 ≤ (40 / 3 : ℝ) * Real.log 2 := by
    rw [show (10000 : ℝ) = 10 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith [log_ten_upper]
  have hsecond : Real.log (10000 / 9999 : ℝ) ≤ 1 / 9999 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10000 / 9999)
    linarith
  have hHid : H (1 / 10000) * Real.log 2
      = (1 / 10000) * Real.log 10000 + (9999 / 10000) * Real.log (10000 / 9999) := by
    unfold H Real.binEntropy
    rw [div_mul_cancel₀ _ hLpos.ne']
    rw [show (1 : ℝ) - 1 / 10000 = 9999 / 10000 by norm_num]
    rw [show ((1 : ℝ) / 10000)⁻¹ = 10000 by norm_num,
      show ((9999 : ℝ) / 10000)⁻¹ = 10000 / 9999 by norm_num]
  have hfin : H (1 / 10000) * Real.log 2 ≤ (1 / 500 : ℝ) * Real.log 2 := by
    rw [hHid]
    nlinarith only [hlog4, hsecond, hL, hLpos]
  exact le_of_mul_le_mul_right hfin hLpos

theorem H_small_upper {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 10000) : H q ≤ 1 / 500 := by
  have hmono := H_strictMonoOn.monotoneOn
    (show q ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨hq, by linarith⟩)
    (show (1 / 10000 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) by constructor <;> norm_num) hq'
  exact hmono.trans H_ten_thousandth_upper

/-- `eta'` increments are controlled by the curvature bound. -/
theorem deriv_eta_increment {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1 / 500) :
    deriv eta y - deriv eta x ≤ (2 / x ^ 2) * (y - x) := by
  rcases eq_or_lt_of_le hxy with heq | hlt
  · rw [heq]
    simp
  · have hxpos : (0 : ℝ) < x := hx
    have hmono : MonotoneOn (fun t => (2 / x ^ 2) * t - deriv eta t) (Set.Icc x y) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x y)
        (f' := fun t => (2 / x ^ 2) - Scalar.etaCurvature t)
      · intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le hxpos ht.1
        have ht1 : t < 1 := by
          have := ht.2
          linarith
        have h1 : HasDerivAt (fun u : ℝ => (2 / x ^ 2) * u) (2 / x ^ 2) t := by
          simpa using (hasDerivAt_id t).const_mul (2 / x ^ 2)
        exact (h1.sub (Scalar.hasDerivAt_deriv_eta ht0 ht1)).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have ht0 : 0 < t := lt_trans hxpos ht.1
        have ht1 : t < 1 := by
          have := ht.2
          linarith
        have h1 : HasDerivAt (fun u : ℝ => (2 / x ^ 2) * u) (2 / x ^ 2) t := by
          simpa using (hasDerivAt_id t).const_mul (2 / x ^ 2)
        exact (h1.sub (Scalar.hasDerivAt_deriv_eta ht0 ht1)).hasDerivWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have ht0 : 0 < t := lt_trans hxpos ht.1
        have htle : t ≤ 1 / 500 := by
          have := ht.2
          linarith
        have hcurv := FCAnalytic.etaCurvature_upper ht0 htle
        have hxle : x ≤ t := ht.1.le
        have hmon : (2 : ℝ) / t ^ 2 ≤ 2 / x ^ 2 := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          nlinarith only [hxle, hxpos]
        linarith
    have hres := hmono (Set.left_mem_Icc.2 hxy) (Set.right_mem_Icc.2 hxy) hxy
    simp only at hres
    linarith

/-- `eta'` is monotone, from nonnegative curvature. -/
theorem deriv_eta_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) :
    deriv eta x ≤ deriv eta y := by
  rcases eq_or_lt_of_le hxy with heq | hlt
  · rw [heq]
  · have hmono : MonotoneOn (deriv eta) (Set.Icc x y) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x y)
        (f' := Scalar.etaCurvature)
      · intro t ht
        exact (Scalar.hasDerivAt_deriv_eta (lt_of_lt_of_le hx ht.1)
          (lt_of_le_of_lt ht.2 hy)).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (Scalar.hasDerivAt_deriv_eta (lt_trans hx ht.1)
          (lt_trans ht.2 hy)).hasDerivWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact Scalar.etaCurvature_nonneg (lt_trans hx ht.1) (lt_trans ht.2 hy)
    exact hmono (Set.left_mem_Icc.2 hxy) (Set.right_mem_Icc.2 hxy) hxy

theorem phi_eq_sub {m : ℝ} (hm : 0 < m) (hm2 : m < 1 / 2) :
    phi m = fun h => eta h - F (1 - 2 * m) h := by
  funext h
  unfold phi
  rw [abs_of_pos (by linarith : (0 : ℝ) < 1 - 2 * m)]

theorem deriv_phi_sub {m h : ℝ} (hm : 0 < m) (hm2 : m < 1 / 2) (hh : 0 < h) (hh1 : h < 1) :
    deriv (phi m) h = deriv eta h - deriv (F (1 - 2 * m)) h := by
  have hz : (0 : ℝ) < 1 - 2 * m := by linarith
  have hda := hasDerivAt_eta hh hh1
  have hdb := hasDerivAt_F_entropy hz hh
  have hphi : HasDerivAt (phi m) (deriv eta h - deriv (F (1 - 2 * m)) h) h := by
    rw [hda.deriv, hdb.deriv, phi_eq_sub hm hm2]
    exact hda.sub hdb
  exact hphi.deriv

/-- The `F`-slope in the entropy direction depends on `(z, h)` only through `z/h`.
This is why the two ray tangents have coinciding `F`-parts. -/
theorem deriv_F_entropy_ray {z w h k : ℝ} (hz : 0 < z) (hh : 0 < h)
    (hw : 0 < w) (hk : 0 < k) (hratio : z / h = w / k) :
    deriv (F z) h = deriv (F w) k := by
  rw [deriv_F_entropy hz hh, deriv_F_entropy hw hk, hratio]

#check @deriv_eta_mono
#check @H_small_upper
#check @deriv_eta_increment
#check @deriv_phi_sub
#check @deriv_F_entropy_ray
#print axioms deriv_eta_mono
#print axioms H_small_upper
#print axioms deriv_eta_increment
#print axioms deriv_phi_sub
#print axioms deriv_F_entropy_ray

end GeneralCK.FCRay

end


