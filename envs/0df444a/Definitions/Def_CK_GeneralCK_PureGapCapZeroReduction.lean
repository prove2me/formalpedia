-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapCapZeroReduction
-- name    : CK_GeneralCK_PureGapCapZeroReduction
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:58:25.90044+00:00
-- url     : https://prove2.me/theorems/10a65fae-ade6-451e-8ce3-25bbc79f80f8
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapCapZeroReduction` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapCapZeroReduction` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapCapZeroReduction` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapCapZeroReduction (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapCapZeroReduction.lean)

import Definitions.Def_CK_GeneralCK_PureGapCapAnalytic
import Definitions.Def_CK_GeneralCK_DeterministicCap
import Definitions.Def_CK_GeneralCK_ProfileLowerBounds
import Definitions.Def_CK_GeneralCK_PhiEntropyConvexity

-- ===== source module GeneralCK.PureGapCapZeroReduction =====
section

/-!
# Shared zero-cutoff cap reductions

At cutoff zero the two lower fiber endpoints are the same double-cap point.
The direct double-cap value is `interiorCost - phi` and admits a scalar
entropy-chord reduction. No cap sign certificate is assumed implicitly.
-/

namespace GeneralCK
open Set

theorem capFiberLower_zero {h fixedMean : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hm : 0 ≤ fixedMean) :
    capFiberLower 0 h fixedMean = entropyInverse h := by
  unfold capFiberLower
  exact max_eq_left (by linarith [(entropyInverse_spec hh hh1).1])

theorem phi_at_entropy_cap {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 2) :
    phi a (H a) = 0 := by
  rcases ha1.eq_or_lt with rfl | ha1
  · norm_num [phi, F, eta_one]
  · have hH : H a < 1 := by
      simpa only [H_half] using
        (H_strictMonoOn ⟨ha.le, ha1.le⟩ ⟨by norm_num, le_rfl⟩ ha1)
    simp [phi, eta, ne_of_lt hH, entropyInverse_H_lower ha.le ha1.le,
      abs_of_pos (show 0 < 1 - 2 * a by linarith), F,
      ne_of_gt (show 0 < 1 - 2 * a by linarith), radialContact_H_lower ha ha1]

theorem canonicalPureGap_doubleCap_eq {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    canonicalPureGap a b (H a) (H b) =
      interiorCost a b - phi ((a + b) / 2) ((H a + H b) / 2) := by
  rw [← pureGap_eq_canonicalPureGap hab hb]
  simp only [pureGap, fourMomentLowerBound, entropyCorrection, atomCorrection,
    entropyInverse_H_lower ha.le (hab.trans hb),
    entropyInverse_H_lower (ha.le.trans hab) hb, candidateGap,
    phi_at_entropy_cap ha (hab.trans hb), phi_at_entropy_cap (ha.trans_le hab) hb]
  ring

/-- The four distinct zero-cutoff obligations. Both lower endpoints consume
`doubleCap`; the three other fields keep their exact scalar domains. -/
structure CanonicalPureGapZeroCapOwners : Prop where
  doubleCap : ∀ e f, 0 < e → e < f → f ≤ 1 →
    0 ≤ canonicalPureGap (entropyInverse e) (entropyInverse f) e f
  leftUpper : ∀ e f, 0 < e → e < f → f ≤ 1 →
    0 ≤ canonicalPureGap (entropyInverse e) (1 / 2) e f
  leftStationary : ∀ e f c, 0 < e → e < f → f ≤ 1 →
    entropyInverse f < c → c < 1 / 2 →
    deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
    0 ≤ canonicalPureGap (entropyInverse e) c e f
  rightStationary : ∀ e f a, 0 < e → e < f → f ≤ 1 →
    entropyInverse e < a → a < entropyInverse f →
    deriv (fun x => canonicalPureGap x (entropyInverse f) e f) a = 0 →
    0 ≤ canonicalPureGap a (entropyInverse f) e f

theorem CanonicalPureGapZeroCapOwners.toExceptEqual
    (h : CanonicalPureGapZeroCapOwners) :
    CanonicalPureGapCapFiberOwnersExceptEqual 0 where
  leftLower := by
    intro e f he hef hf _
    rw [capFiberLower_zero (he.trans hef).le hf
      (entropyInverse_spec he.le (hef.le.trans hf)).1]
    exact h.doubleCap e f he hef hf
  leftUpper := by
    intro e f he hef hf _
    exact h.leftUpper e f he hef hf
  leftStationary := by
    intro e f c he hef hf hc hc1 hderiv
    rw [capFiberLower_zero (he.trans hef).le hf
      (entropyInverse_spec he.le (hef.le.trans hf)).1] at hc
    exact h.leftStationary e f c he hef hf hc hc1 hderiv
  rightLower := by
    intro e f he hef hf _
    rw [capFiberLower_zero he.le (hef.le.trans hf)
      (entropyInverse_spec (he.trans hef).le hf).1]
    exact h.doubleCap e f he hef hf
  rightStationary := by
    intro e f a he hef hf ha ha1 hderiv
    rw [capFiberLower_zero he.le (hef.le.trans hf)
      (entropyInverse_spec (he.trans hef).le hf).1] at ha
    exact h.rightStationary e f a he hef hf ha ha1 hderiv

theorem CanonicalPureGapCapFiberOwnersExceptEqual.toZeroCapOwners
    (h : CanonicalPureGapCapFiberOwnersExceptEqual 0) :
    CanonicalPureGapZeroCapOwners where
  doubleCap := by
    intro e f he hef hf
    have hmax := capFiberLower_zero (he.trans hef).le hf
      (entropyInverse_spec he.le (hef.le.trans hf)).1
    have hv := h.leftLower e f he hef hf (by
      rw [hmax]
      exact (entropyInverse_spec (he.trans hef).le hf).2.1)
    rwa [hmax] at hv
  leftUpper := by
    intro e f he hef hf
    apply h.leftUpper e f he hef hf
    rw [capFiberLower_zero (he.trans hef).le hf
      (entropyInverse_spec he.le (hef.le.trans hf)).1]
    exact (entropyInverse_spec (he.trans hef).le hf).2.1
  leftStationary := by
    intro e f c he hef hf hc hc1 hderiv
    apply h.leftStationary e f c he hef hf _ hc1 hderiv
    rwa [capFiberLower_zero (he.trans hef).le hf
      (entropyInverse_spec he.le (hef.le.trans hf)).1]
  rightStationary := by
    intro e f a he hef hf ha ha1 hderiv
    apply h.rightStationary e f a he hef hf _ ha1 hderiv
    rwa [capFiberLower_zero he.le (hef.le.trans hf)
      (entropyInverse_spec (he.trans hef).le hf).1]

theorem canonicalPureGapZeroCapOwners_iff :
    CanonicalPureGapZeroCapOwners ↔ CanonicalPureGapCapFiberOwnersExceptEqual 0 :=
  ⟨CanonicalPureGapZeroCapOwners.toExceptEqual,
    CanonicalPureGapCapFiberOwnersExceptEqual.toZeroCapOwners⟩

theorem H_concaveOn_unit : ConcaveOn ℝ (Icc 0 1) H := by
  convert! Real.strictConcave_binEntropy.concaveOn.smul
    (inv_nonneg.mpr log_two_pos.le) using 1
  funext p
  simp [H, div_eq_mul_inv, mul_comm]

theorem entropy_average_le_midpoint {a b : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    (H a + H b) / 2 ≤ H ((a + b) / 2) := by
  have h := H_concaveOn_unit.2 ⟨ha, ha1⟩ ⟨hb, hb1⟩
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  rw [show (1 / 2 : ℝ) * a + (1 / 2) * b = (a + b) / 2 by ring] at h
  linarith

/-- The global deterministic comparison `j ≥ 4 ΔH` follows directly from
the already-proved deterministic profile bound and the profile slope. -/
theorem four_entropyDrop_le_interiorCost {a b : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) :
    4 * (H ((a + b) / 2) - (H a + H b) / 2) ≤ interiorCost a b := by
  have hE : 0 < (H a + H b) / 2 := by linarith [H_pos ha ha1, H_pos hb hb1]
  have hD : 0 ≤ H ((a + b) / 2) - (H a + H b) / 2 :=
    sub_nonneg.mpr (entropy_average_le_midpoint ha.le ha1.le hb.le hb1.le)
  have hD1 : H ((a + b) / 2) - (H a + H b) / 2 < 1 := by
    linarith [H_le_one ((a + b) / 2)]
  exact (Scalar.four_mul_le_P hD hD1).trans (deterministic_cap_bound ha ha1 hb hb1)

/-- Convexity in entropy makes a single lower-entropy endpoint sufficient
for the full interval up to the deterministic cap. -/
theorem phi_le_four_entropyDeficit_of_endpoint {m e e₀ : ℝ}
    (hm : 0 < m) (hm1 : m ≤ 1 / 2) (he₀ : 0 < e₀)
    (he : e₀ ≤ e) (hecap : e ≤ H m)
    (hendpoint : phi m e₀ ≤ 4 * (H m - e₀)) :
    phi m e ≤ 4 * (H m - e) := by
  have hconvex : ConvexOn ℝ (Ioc 0 (H m))
      (fun t => phi m t + 4 * t - 4 * H m) := by
    have hphi := phi_entropy_convexOn hm (hm1.trans_lt (by norm_num))
    convert! (hphi.add ((convexOn_id (convex_Ioc (0 : ℝ) (H m))).smul
      (by norm_num : (0 : ℝ) ≤ 4))).add_const (-4 * H m) using 1
    funext t
    simp [Pi.add_apply, smul_eq_mul, sub_eq_add_neg]
  have hbound := hconvex.le_max_of_mem_Icc
    (show e₀ ∈ Ioc 0 (H m) from ⟨he₀, he.trans hecap⟩)
    (show H m ∈ Ioc 0 (H m) from ⟨H_pos hm (hm1.trans_lt (by norm_num)), le_rfl⟩)
    (show e ∈ Icc e₀ (H m) from ⟨he, hecap⟩)
  rw [phi_at_entropy_cap hm hm1] at hbound
  have hmax : max (phi m e₀ + 4 * e₀ - 4 * H m)
      (0 + 4 * H m - 4 * H m) ≤ 0 := max_le (by linarith) (by linarith)
  linarith

/-- Any scalar entropy floor and its endpoint sign give the double-cap
value. This theorem contains no finite-law or correction-sign premise. -/
theorem canonicalPureGap_doubleCap_nonneg_of_entropy_endpoint {a b e₀ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2)
    (he₀ : 0 < e₀) (hfloor : e₀ ≤ (H a + H b) / 2)
    (hendpoint : phi ((a + b) / 2) e₀ ≤
      4 * (H ((a + b) / 2) - e₀)) :
    0 ≤ canonicalPureGap a b (H a) (H b) := by
  have hb0 : 0 < b := ha.trans_le hab
  have ha1 : a < 1 := (hab.trans hb).trans_lt (by norm_num)
  have hb1 : b < 1 := hb.trans_lt (by norm_num)
  have hphi := phi_le_four_entropyDeficit_of_endpoint
    (show 0 < (a + b) / 2 by linarith) (show (a + b) / 2 ≤ 1 / 2 by linarith)
    he₀ hfloor (entropy_average_le_midpoint ha.le ha1.le hb0.le hb1.le) hendpoint
  rw [canonicalPureGap_doubleCap_eq ha hab hb]
  linarith [four_entropyDrop_le_interiorCost ha ha1 hb0 hb1]

theorem H_sum_ge_extreme_pair {a b l u : ℝ}
    (hl : 0 ≤ l) (hu : u ≤ 1) (hla : l ≤ a) (hau : a ≤ u)
    (hsum : a + b = l + u) : H l + H u ≤ H a + H b := by
  have hlu : l ≤ u := hla.trans hau
  rcases hlu.eq_or_lt with rfl | hlu
  · have ha : a = l := by linarith
    have hb : b = l := by linarith
    simp [ha, hb]
  · let t := (a - l) / (u - l)
    have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hla) (sub_nonneg.mpr hlu.le)
    have ht1 : t ≤ 1 := (div_le_one (sub_pos.mpr hlu)).mpr (by linarith)
    have hid : t * (u - l) = a - l := div_mul_cancel₀ _ (sub_pos.mpr hlu).ne'
    have hargA : (1 - t) * l + t * u = a := by nlinarith [hid]
    have hargB : t * l + (1 - t) * u = b := by nlinarith [hid]
    have hA := H_concaveOn_unit.2
      (show l ∈ Icc 0 1 from ⟨hl, hlu.le.trans hu⟩)
      (show u ∈ Icc 0 1 from ⟨hl.trans hlu.le, hu⟩)
      (show 0 ≤ 1 - t by linarith) ht (by ring : 1 - t + t = 1)
    have hB := H_concaveOn_unit.2
      (show l ∈ Icc 0 1 from ⟨hl, hlu.le.trans hu⟩)
      (show u ∈ Icc 0 1 from ⟨hl.trans hlu.le, hu⟩)
      ht (show 0 ≤ 1 - t by linarith) (by ring : t + (1 - t) = 1)
    simp only [smul_eq_mul, hargA, hargB] at hA hB
    linarith

/-- Least mean entropy for two lower-half means with midpoint `m`. -/
noncomputable def capEntropyFloor (m : ℝ) : ℝ :=
  if m ≤ 1 / 4 then H (2 * m) / 2 else (1 + H (2 * m - 1 / 2)) / 2

theorem capEntropyFloor_pos {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1 / 2) :
    0 < capEntropyFloor m := by
  unfold capEntropyFloor
  split_ifs with h
  · exact div_pos (H_pos (by linarith) (by linarith)) two_pos
  · have hp : 0 ≤ H (2 * m - 1 / 2) := H_nonneg (by linarith) (by linarith)
    linarith

theorem capEntropyFloor_le_average {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    capEntropyFloor ((a + b) / 2) ≤ (H a + H b) / 2 := by
  unfold capEntropyFloor
  rw [show 2 * ((a + b) / 2) = a + b by ring]
  split_ifs with h
  · have hsum := H_sum_ge_extreme_pair (a := a) (b := b) (l := 0) (u := a + b)
      le_rfl (by linarith) ha (by linarith) (by ring)
    rw [H_zero, zero_add] at hsum
    linarith
  · have hsum := H_sum_ge_extreme_pair (a := a) (b := b)
      (l := a + b - 1 / 2) (u := 1 / 2)
      (by linarith) (by norm_num) (by linarith) (hab.trans hb) (by ring)
    rw [H_half] at hsum
    linarith

/-- Two one-dimensional endpoint inequalities, joined at `m = 1/4`.
The domain includes the half-mean endpoint; its value is identically zero. -/
def CanonicalDoubleCapEntropyEndpoints : Prop :=
  ∀ m, 0 < m → m ≤ 1 / 2 →
    phi m (capEntropyFloor m) ≤ 4 * (H m - capEntropyFloor m)

theorem canonicalPureGap_doubleCap_nonneg_of_scalar_endpoints
    (h : CanonicalDoubleCapEntropyEndpoints) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    0 ≤ canonicalPureGap a b (H a) (H b) := by
  have hm : 0 < (a + b) / 2 := by linarith
  have hm1 : (a + b) / 2 ≤ 1 / 2 := by linarith
  exact canonicalPureGap_doubleCap_nonneg_of_entropy_endpoint ha hab hb
    (capEntropyFloor_pos hm hm1) (capEntropyFloor_le_average ha.le hab hb)
    (h _ hm hm1)

theorem canonicalPureGap_inverse_doubleCap_nonneg_of_scalar_endpoints
    (h : CanonicalDoubleCapEntropyEndpoints) {e f : ℝ}
    (he : 0 < e) (hef : e < f) (hf : f ≤ 1) :
    0 ≤ canonicalPureGap (entropyInverse e) (entropyInverse f) e f := by
  have hie := entropyInverse_spec he.le (hef.le.trans hf)
  have hif := entropyInverse_spec (he.trans hef).le hf
  have hn := canonicalPureGap_doubleCap_nonneg_of_scalar_endpoints h
    (entropyInverse_pos he (hef.le.trans hf))
    (entropyInverse_mono he.le hf hef.le) hif.2.1
  rwa [hie.2.2, hif.2.2] at hn

theorem capEntropyFloor_half : capEntropyFloor (1 / 2) = 1 := by
  norm_num [capEntropyFloor]

theorem canonicalDoubleCapEntropyEndpoints_of_strict
    (h : ∀ m, 0 < m → m < 1 / 2 →
      phi m (capEntropyFloor m) ≤ 4 * (H m - capEntropyFloor m)) :
    CanonicalDoubleCapEntropyEndpoints := by
  intro m hm hm1
  rcases hm1.eq_or_lt with rfl | hm1
  · norm_num [capEntropyFloor, phi, F, eta_one]
  · exact h m hm hm1

/-- The remaining non-double-cap obligations after using a zero cutoff.
The maximal-entropy left endpoint is double cap, and the maximal-entropy
left stationary domain is empty, so both left fields use `f < 1`. -/
structure CanonicalPureGapZeroCapResidualOwners : Prop where
  leftUpper : ∀ e f, 0 < e → e < f → f < 1 →
    0 ≤ canonicalPureGap (entropyInverse e) (1 / 2) e f
  leftStationary : ∀ e f c, 0 < e → e < f → f < 1 →
    entropyInverse f < c → c < 1 / 2 →
    deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
    0 ≤ canonicalPureGap (entropyInverse e) c e f
  rightStationary : ∀ e f a, 0 < e → e < f → f ≤ 1 →
    entropyInverse e < a → a < entropyInverse f →
    deriv (fun x => canonicalPureGap x (entropyInverse f) e f) a = 0 →
    0 ≤ canonicalPureGap a (entropyInverse f) e f

theorem CanonicalPureGapZeroCapResidualOwners.withDoubleCap
    (h : CanonicalPureGapZeroCapResidualOwners)
    (hd : ∀ e f, 0 < e → e < f → f ≤ 1 →
      0 ≤ canonicalPureGap (entropyInverse e) (entropyInverse f) e f) :
    CanonicalPureGapZeroCapOwners where
  doubleCap := hd
  leftUpper := by
    intro e f he hef hf
    rcases hf.eq_or_lt with rfl | hf
    · have hi : entropyInverse 1 = 1 / 2 := by
        simpa only [H_half] using entropyInverse_H_lower (by norm_num : (0 : ℝ) ≤ 1 / 2) le_rfl
      simpa only [hi] using hd e 1 he hef le_rfl
    · exact h.leftUpper e f he hef hf
  leftStationary := by
    intro e f c he hef hf hc hc1 hderiv
    rcases hf.eq_or_lt with rfl | hf
    · have hi : entropyInverse 1 = 1 / 2 := by
        simpa only [H_half] using entropyInverse_H_lower (by norm_num : (0 : ℝ) ≤ 1 / 2) le_rfl
      rw [hi] at hc
      linarith
    · exact h.leftStationary e f c he hef hf hc hc1 hderiv
  rightStationary := h.rightStationary

/-- Direct consumer for the final zero-cutoff assembly. Its only premises
are the scalar double-cap endpoint signs and the three residual owners. -/
theorem canonicalPureGapCapFiberOwnersExceptEqual_zero_of_scalar_endpoints
    (hscalar : CanonicalDoubleCapEntropyEndpoints)
    (hresidual : CanonicalPureGapZeroCapResidualOwners) :
    CanonicalPureGapCapFiberOwnersExceptEqual 0 :=
  (hresidual.withDoubleCap (fun _ _ he hef hf =>
    canonicalPureGap_inverse_doubleCap_nonneg_of_scalar_endpoints hscalar he hef hf)).toExceptEqual

#print axioms capFiberLower_zero
#print axioms phi_at_entropy_cap
#print axioms canonicalPureGap_doubleCap_eq
#print axioms canonicalPureGapZeroCapOwners_iff
#print axioms four_entropyDrop_le_interiorCost
#print axioms phi_le_four_entropyDeficit_of_endpoint
#print axioms canonicalPureGap_doubleCap_nonneg_of_entropy_endpoint
#print axioms capEntropyFloor_le_average
#print axioms canonicalPureGap_inverse_doubleCap_nonneg_of_scalar_endpoints
#print axioms canonicalDoubleCapEntropyEndpoints_of_strict
#print axioms CanonicalPureGapZeroCapResidualOwners.withDoubleCap
#print axioms canonicalPureGapCapFiberOwnersExceptEqual_zero_of_scalar_endpoints

end GeneralCK

end


