-- Prove2me | Definitions.Def_CK_CKLaneN4_EightKernel
-- name    : CK_CKLaneN4_EightKernel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:32:49.947997+00:00
-- url     : https://prove2.me/theorems/811f31cc-2b89-438c-8c72-b84149400bdf
-- title:
--   Courtade–Kumar proof module `CKLaneN4.EightKernel` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.EightKernel` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.EightKernel` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.EightKernel (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/EightKernel.lean)

import Definitions.Def_CK_CKLaneN4_ParentKernel
import Definitions.Def_CK_GeneralCK_PsiParentEntropyGain
import Definitions.Def_CK_GeneralCK_PsiSplitLossBound

-- ===== source module CKLaneN4.EightKernel =====
section

/-!
# Lane N4: the uniform parent correction of the global eight-ratio theorem

Archive: `reduction/eight_global/EIGHT_RATIO.py` (CK_GENERAL_COMPLETION), claim

  `E [eta(E) - eta(E + C(q))] / q^2 ≥ 7/10`  for `0 < E ≤ 11/200`, `0 ≤ q ≤ 8E`,

proved on the rational root `(E, y) ∈ [1/10000, 11/200] × [0, 8]`, `q = yE`, by an exact binary
partition with two acceptance tests, plus the analytic tail `E ≤ 1/10000`:

* (a) logarithmic test: `eta(E) - eta(E+c) ≥ 2c + β log(1 + c/E)` where
  `β ≤ h(-eta'(h) - 2)` on the entropy range, using
  `h(-eta'(h) - 2) ≥ (1 - 2v)(1 + 1/log((1-v)/v)) / (L (1-v))`, `v = H⁻¹(h)`;
  then `T_-[2E_- + β ℓ₀(U)] ≥ 7/10` with `T_- ≤ C(q)/q^2`, `ℓ₀(u) = log(1+u)/u` decreasing,
  `U ≥ C(q)/E`;
* (b) direct test: `(eta(E_+) - eta(E_+ + C(q_-))) · E_- / q_+^2 ≥ 7/10` by convexity.

`checkEY B c = true → SemEY B` with no other hypotheses.
-/

namespace CKLaneN4

open GeneralCK CKLaneD Set

/-! ## Analytic lemmas -/

/-- Sharp entropy-production slope: `h(-eta'(h) - 2) ≥ (1-2v)(1 + 1/ℓ)/(L(1-v))`,
`v = H⁻¹(h)`, `ℓ = log((1-v)/v)`. -/
theorem neg_deriv_eta_ge_beta {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    (1 - 2 * entropyInverse h) *
        (1 + 1 / Real.log ((1 - entropyInverse h) / entropyInverse h)) /
        (Real.log 2 * (1 - entropyInverse h)) ≤ h * (-deriv eta h - 2) := by
  have hv : 0 < entropyInverse h := entropyInverse_pos hh hh1.le
  have hvhalf : entropyInverse h < 1 / 2 := entropyInverse_lt_half hh.le hh1
  have hH : H (entropyInverse h) = h := (entropyInverse_spec hh.le hh1.le).2.2
  rw [deriv_eta hh hh1]
  generalize entropyInverse h = v at hv hvhalf hH ⊢
  have hvc : 0 < 1 - v := by linarith
  have hL : 0 < Real.log 2 := log_two_pos
  have hℓpos : 0 < Real.log ((1 - v) / v) := Real.log_pos (by rw [lt_div_iff₀ hv]; linarith)
  generalize hℓdef : Real.log ((1 - v) / v) = ℓ at hℓpos ⊢
  have hJ : J v = ℓ / Real.log 2 := by rw [← hℓdef]; rfl
  have hbin : Real.binEntropy v = v * ℓ - Real.log (1 - v) := by
    rw [Real.binEntropy, Real.log_inv, Real.log_inv, ← hℓdef, Real.log_div hvc.ne' hv.ne']
    ring
  have hLh : Real.log 2 * h = v * ℓ - Real.log (1 - v) := by
    rw [← hbin, ← hH]
    unfold H
    field_simp
  have hlog : v ≤ -Real.log (1 - v) := by linarith [Real.log_le_sub_one_of_pos hvc]
  rw [hJ]
  have hR : h * (-(-2 - (1 - 2 * v) / (Real.log 2 * v * (1 - v) * (ℓ / Real.log 2))) - 2) =
      (Real.log 2 * h) * (1 - 2 * v) / (Real.log 2 * v * (1 - v) * ℓ) := by
    field_simp
    ring
  have hLHS : (1 - 2 * v) * (1 + 1 / ℓ) / (Real.log 2 * (1 - v)) =
      (v * (ℓ + 1)) * (1 - 2 * v) / (Real.log 2 * v * (1 - v) * ℓ) := by
    field_simp
  rw [hR, hLHS]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [hLh]
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  linarith

/-- Integrated form: a derivative bound `-eta' ≥ 2 + β/h` on `(a, a+c)` gives
`eta a - eta (a + c) ≥ 2c + β log(1 + c/a)`. -/
theorem eta_increment_ge_beta_log {a c β : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hac : a + c ≤ 1)
    (hder : ∀ h, a < h → h < a + c → 2 + β / h ≤ -deriv eta h) :
    2 * c + β * Real.log (1 + c / a) ≤ eta a - eta (a + c) := by
  have hb : 0 < a + c := by linarith
  have hanti : AntitoneOn (fun h : ℝ => eta h + 2 * h + β * Real.log h) (Icc a (a + c)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a (a + c))
      (f' := fun h => deriv eta h + 2 + β / h)
    · apply ContinuousOn.add
      · exact (Scalar.eta_continuousOn.mono (fun h hh => ⟨ha.trans_le hh.1, hh.2.trans hac⟩)).add
          (continuous_const.mul continuous_id).continuousOn
      · exact continuousOn_const.mul (Real.continuousOn_log.mono
          (fun h hh => ne_of_gt (ha.trans_le hh.1)))
    · intro h hh
      have hi : h ∈ Ioo a (a + c) := by simpa only [interior_Icc] using hh
      have h0 : 0 < h := ha.trans hi.1
      have h1 : h < 1 := hi.2.trans_le hac
      have hd := ((hasDerivAt_eta h0 h1).add ((hasDerivAt_id h).const_mul 2)).add
        ((Real.hasDerivAt_log h0.ne').const_mul β)
      rw [← (hasDerivAt_eta h0 h1).deriv] at hd
      convert! hd.hasDerivWithinAt using 1
      field_simp
    · intro h hh
      have hi : h ∈ Ioo a (a + c) := by simpa only [interior_Icc] using hh
      have := hder h hi.1 hi.2
      linarith
  have hm := hanti ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  simp only at hm
  have he : 1 + c / a = (a + c) / a := by field_simp
  rw [he, Real.log_div hb.ne' ha.ne']
  nlinarith

/-- `log(1+u)/u` is antitone: `log(1+U)/U ≤ log(1+u)/u` for `0 < u ≤ U`. -/
theorem log_one_add_div_antitone {u U : ℝ} (hu : 0 < u) (huU : u ≤ U) :
    Real.log (1 + U) / U ≤ Real.log (1 + u) / u := by
  have hU : 0 < U := hu.trans_le huU
  have hh := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : ℝ) ∈ Ioi 0 by norm_num) (show 1 + U ∈ Ioi (0 : ℝ) by
      change (0 : ℝ) < 1 + U; linarith)
    (show 0 ≤ 1 - u / U by rw [sub_nonneg, div_le_one hU]; exact huU)
    (show 0 ≤ u / U by positivity) (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hh
  have he : (1 - u / U) * 1 + u / U * (1 + U) = 1 + u := by field_simp; ring
  rw [he] at hh
  rw [div_le_div_iff₀ hU hu]
  have := mul_le_mul_of_nonneg_left hh hU.le
  have he2 : U * (u / U * Real.log (1 + U)) = u * Real.log (1 + U) := by field_simp
  rw [he2] at this
  linarith

/-- Normalized parent capacity lower bounds. -/
theorem capacity_ratio_ge_half {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    1 / (2 * Real.log 2) ≤ (1 - H ((1 - q) / 2)) / q ^ 2 := by
  have h := SmallMean.Cn_ge_half_sq hq.le hq1
  unfold SmallMean.Cn at h
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [log_two_pos]

theorem capacity_ratio_mono {q0 q : ℝ} (hq0 : 0 < q0) (hqq : q0 ≤ q) (hq1 : q ≤ 1) :
    (1 - H ((1 - q0) / 2)) / q0 ^ 2 ≤ (1 - H ((1 - q) / 2)) / q ^ 2 := by
  have h := Cn_ratio_strictMonoOn.monotoneOn ⟨hq0, hqq.trans hq1⟩ ⟨hq0.trans_le hqq, hq1⟩ hqq
  simp only [SmallMean.Cn] at h
  have hL : 0 < Real.log 2 := log_two_pos
  rw [mul_div_assoc, mul_div_assoc] at h
  exact le_of_mul_le_mul_left h hL

theorem capacity_pos {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) : 0 < 1 - H ((1 - q) / 2) := by
  have h := SmallMean.Cn_ge_half_sq hq.le hq1
  unfold SmallMean.Cn at h
  have : 0 < Real.log 2 * (1 - H ((1 - q) / 2)) := by nlinarith
  exact pos_of_mul_pos_right this log_two_pos.le

/-- `ℓ = log((1-v)/v)` decreases in `v`. -/
theorem logit_anti {v w : ℝ} (hv : 0 < v) (hvw : v ≤ w) (hw : w < 1) :
    Real.log ((1 - w) / w) ≤ Real.log ((1 - v) / v) := by
  have hw0 : 0 < w := hv.trans_le hvw
  apply Real.log_le_log (div_pos (by linarith) hw0)
  rw [div_le_div_iff₀ hw0 hv]
  nlinarith

/-- Rational lower bound of the slope coefficient on an entropy range `[h0, h1]`
from brackets `H v0 ≤ h0`, `h1 ≤ H v1`. -/
theorem slope_coeff_lower {h v0 v1 ℓhi L1' : ℝ} (hh : 0 < h) (hh1 : h < 1) (hv0 : 0 < v0)
    (hv1pos : 0 < v1) (hv1 : 2 * v1 ≤ 1) (hv0h : H v0 ≤ h) (hv02 : 2 * v0 ≤ 1) (hhv1 : h ≤ H v1)
    (hℓ : Real.log ((1 - v0) / v0) ≤ ℓhi) (hL1 : Real.log 2 ≤ L1') :
    (1 - 2 * v1) / (1 - v1) * (1 + 1 / ℓhi) / L1' ≤ h * (-deriv eta h - 2) := by
  refine le_trans ?_ (neg_deriv_eta_ge_beta hh hh1)
  set v := entropyInverse h
  have hvl : v0 ≤ v := by
    have := entropyInverse_mono (H_nonneg hv0.le (by linarith)) hh1.le hv0h
    rwa [entropyInverse_H_lower hv0.le (by linarith)] at this
  have hvu : v ≤ v1 := by
    have h1' : H v1 ≤ 1 := H_le_one _
    have := entropyInverse_mono hh.le h1' hhv1
    rwa [entropyInverse_H_lower (by linarith) (by linarith)] at this
  have hv : 0 < v := hv0.trans_le hvl
  have hvh : v < 1 / 2 := entropyInverse_lt_half hh.le hh1
  have hL : 0 < Real.log 2 := log_two_pos
  have hℓv : 0 < Real.log ((1 - v) / v) := Real.log_pos (by rw [lt_div_iff₀ hv]; linarith)
  have hℓle : Real.log ((1 - v) / v) ≤ ℓhi :=
    (logit_anti hv0 hvl (by linarith)).trans hℓ
  have hℓhi : 0 < ℓhi := hℓv.trans_le hℓle
  have hf1 : (1 - 2 * v1) / (1 - v1) ≤ (1 - 2 * v) / (1 - v) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hf1n : 0 ≤ (1 - 2 * v1) / (1 - v1) := div_nonneg (by linarith) (by linarith)
  have hf2 : 1 + 1 / ℓhi ≤ 1 + 1 / Real.log ((1 - v) / v) := by
    have := one_div_le_one_div_of_le hℓv hℓle
    linarith
  have hf2n : 0 ≤ 1 + 1 / ℓhi := by have := one_div_pos.mpr hℓhi; linarith
  have hprod := mul_le_mul hf1 hf2 hf2n (div_nonneg (by linarith) (by linarith))
  have hL1pos : 0 < L1' := hL.trans_le hL1
  calc (1 - 2 * v1) / (1 - v1) * (1 + 1 / ℓhi) / L1'
      ≤ (1 - 2 * v) / (1 - v) * (1 + 1 / Real.log ((1 - v) / v)) / L1' :=
        div_le_div_of_nonneg_right hprod hL1pos.le
    _ ≤ (1 - 2 * v) / (1 - v) * (1 + 1 / Real.log ((1 - v) / v)) / Real.log 2 :=
        div_le_div_of_nonneg_left (mul_nonneg (div_nonneg (by linarith) (by linarith))
          (by have := one_div_pos.mpr hℓv; linarith)) hL hL1
    _ = (1 - 2 * v) * (1 + 1 / Real.log ((1 - v) / v)) / (Real.log 2 * (1 - v)) := by
        field_simp

/-! ## Boxes, certificates and the checker -/

/-- A rational box in `(E, y)`, `q = y E`. -/
structure EYBox where
  e0 : ℚ
  e1 : ℚ
  y0 : ℚ
  y1 : ℚ
  deriving Repr, DecidableEq

/-- The normalized parent correction `≥ 7/10` on every `(E, q)` with `(E, q/E)` in the box. -/
def SemEY (B : EYBox) : Prop :=
  ∀ E q : ℝ, (B.e0 : ℝ) ≤ E → E ≤ B.e1 → (B.y0 : ℝ) * E ≤ q → q ≤ (B.y1 : ℝ) * E → 0 ≤ q →
    (7 / 10) * (q ^ 2 / E) ≤ eta E - eta (E + (1 - H ((1 - q) / 2)))

/-- Untrusted certificate for one `(E, y)` box: the direct test (b) or the logarithmic test (a). -/
inductive PGCert where
  | direct (pM : PtCert) (xc : ℚ) (pxc : PtCert) (xa : ℚ) (pxa : PtCert)
  | logb (pM0 pM1 : PtCert) (v0 : ℚ) (pv0 : PtCert) (v1 : ℚ) (pv1 : PtCert) (cU : LogCert)
  deriving Repr, DecidableEq

def EYBox.q0 (B : EYBox) : ℚ := B.e0 * B.y0
def EYBox.q1 (B : EYBox) : ℚ := B.e1 * B.y1

/-- Box sanity shared by both tests (includes the physical bound `E + q^2 ≤ 1`). -/
def eyBoxOK (B : EYBox) : Bool :=
  decide (0 < B.e0 ∧ B.e0 ≤ B.e1 ∧ 0 ≤ B.y0 ∧ B.y0 ≤ B.y1 ∧ B.q1 < 1 ∧ B.e1 + B.q1 ^ 2 ≤ 1)

/-- Upper bound of the parent capacity `C(q_+)`. -/
def capHi (q1 : ℚ) (p : PtCert) : ℚ := 1 - Hlo ((1 - q1) / 2) p

/-- Lower bound of `C(q)/q^2` on the box. -/
def tLo (q0 : ℚ) (p : PtCert) : ℚ :=
  if q0 = 0 then 1 / (2 * L1) else max (1 / (2 * L1)) ((1 - Hhi ((1 - q0) / 2) p) / q0 ^ 2)

/-- Lower bound of the slope coefficient `β`. -/
def betaLo (v1 : ℚ) (pv0 : PtCert) : ℚ :=
  (1 - 2 * v1) / (1 - v1) * (1 + 1 / (pv0.cy.hi - pv0.cx.lo)) / L1

def checkEY (B : EYBox) : PGCert → Bool
  | .direct pM xc pxc xa pxa =>
      eyBoxOK B && decide (0 < B.q0) &&
      checkPt ((1 - B.q0) / 2) pM && checkPt xc pxc && checkPt xa pxa &&
      decide (0 ≤ 1 - Hhi ((1 - B.q0) / 2) pM) &&
      decide (B.e1 + (1 - Hhi ((1 - B.q0) / 2) pM) ≤ 1) &&
      decide (2 * xc ≤ 1 ∧ B.e1 ≤ Hlo xc pxc) &&
      decide (2 * xa ≤ 1 ∧ Hhi xa pxa ≤ B.e1 + (1 - Hhi ((1 - B.q0) / 2) pM)) &&
      decide (7 / 10 * (B.q1 ^ 2 / B.e0) ≤
        (1 - 2 * xc) * Jlo xc pxc - (1 - 2 * xa) * Jhi xa pxa)
  | .logb pM0 pM1 v0 pv0 v1 pv1 cU =>
      eyBoxOK B &&
      checkPt ((1 - B.q0) / 2) pM0 && checkPt ((1 - B.q1) / 2) pM1 &&
      checkPt v0 pv0 && checkPt v1 pv1 &&
      checkLogCert (1 + capHi B.q1 pM1 / B.e0) cU &&
      decide (0 < capHi B.q1 pM1) &&
      decide (B.e1 + capHi B.q1 pM1 < 1) &&
      decide (2 * v0 ≤ 1 ∧ Hhi v0 pv0 ≤ B.e0) &&
      decide (2 * v1 ≤ 1 ∧ B.e1 + capHi B.q1 pM1 ≤ Hlo v1 pv1) &&
      decide (0 < pv0.cy.hi - pv0.cx.lo) &&
      decide (0 ≤ cU.lo) &&
      decide (7 / 10 ≤ tLo B.q0 pM0 *
        (2 * B.e0 + betaLo v1 pv0 * (cU.lo / (capHi B.q1 pM1 / B.e0))))

theorem eyBoxOK_facts {B : EYBox} (h : eyBoxOK B = true) :
    (0 : ℝ) < B.e0 ∧ (B.e0 : ℝ) ≤ B.e1 ∧ (0 : ℝ) ≤ B.y0 ∧ (B.y0 : ℝ) ≤ B.y1 ∧
      ((B.q1 : ℚ) : ℝ) < 1 ∧ (B.e1 : ℝ) + ((B.q1 : ℚ) : ℝ) ^ 2 ≤ 1 := by
  unfold eyBoxOK at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3, by exact_mod_cast h4,
    by exact_mod_cast h5, by exact_mod_cast h6⟩

/-- Common point facts on an `(E, y)` box. -/
theorem ey_point {B : EYBox} (h : eyBoxOK B = true) {E q : ℝ} (he0 : (B.e0 : ℝ) ≤ E)
    (he1 : E ≤ B.e1) (hy0 : (B.y0 : ℝ) * E ≤ q) (hy1 : q ≤ (B.y1 : ℝ) * E) :
    0 < E ∧ ((B.q0 : ℚ) : ℝ) ≤ q ∧ q ≤ ((B.q1 : ℚ) : ℝ) ∧ q < 1 ∧
      E + (1 - H ((1 - q) / 2)) ≤ 1 := by
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := eyBoxOK_facts h
  have hE : 0 < E := r1.trans_le he0
  have eq0 : ((B.q0 : ℚ) : ℝ) = (B.e0 : ℝ) * B.y0 := by unfold EYBox.q0; push_cast; ring
  have eq1 : ((B.q1 : ℚ) : ℝ) = (B.e1 : ℝ) * B.y1 := by unfold EYBox.q1; push_cast; ring
  have hq0 : ((B.q0 : ℚ) : ℝ) ≤ q := by
    rw [eq0]; nlinarith [mul_le_mul_of_nonneg_right he0 r3]
  have hq1 : q ≤ ((B.q1 : ℚ) : ℝ) := by
    rw [eq1]; nlinarith [mul_le_mul_of_nonneg_left he1 (r3.trans r4)]
  have hq0' : 0 ≤ q := le_trans (by rw [eq0]; positivity) hq0
  refine ⟨hE, hq0, hq1, hq1.trans_lt r5, ?_⟩
  rcases hq0'.eq_or_lt with hz | hqpos
  · rw [← hz]; norm_num [H_half]; nlinarith [sq_nonneg ((B.q1 : ℚ) : ℝ)]
  · have hc := capacity_le_sq hqpos (hq1.trans_lt r5)
    have hsq : q ^ 2 ≤ ((B.q1 : ℚ) : ℝ) ^ 2 := by nlinarith
    linarith

theorem checkEY_direct_sound {B : EYBox} {pM : PtCert} {xc : ℚ} {pxc : PtCert} {xa : ℚ}
    {pxa : PtCert} (h : checkEY B (.direct pM xc pxc xa pxa) = true) : SemEY B := by
  intro E q he0 he1 hy0 hy1 hq
  unfold checkEY at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hbox, hq0pos⟩, hpM⟩, hpxc⟩, hpxa⟩, hcap0⟩, hEC⟩, ⟨hxc1, hxc2⟩⟩, ⟨hxa1, hxa2⟩⟩,
    hacc⟩ := h
  obtain ⟨hE, hqq0, hqq1, hq1', hphys⟩ := ey_point hbox he0 he1 hy0 hy1
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := eyBoxOK_facts hbox
  obtain ⟨_, _, _, hMu, _, _⟩ := checkPt_bounds hpM
  obtain ⟨hxc0, _, hxcHl, _, hxcJl, _⟩ := checkPt_bounds hpxc
  obtain ⟨hxa0, _, _, hxaHu, _, hxaJu⟩ := checkPt_bounds hpxa
  have rq0 : (0 : ℝ) < ((B.q0 : ℚ) : ℝ) := by exact_mod_cast hq0pos
  have hqpos : 0 < q := rq0.trans_le hqq0
  -- capacity lower bound
  have hM : (((1 - B.q0) / 2 : ℚ) : ℝ) = (1 - ((B.q0 : ℚ) : ℝ)) / 2 := by push_cast; ring
  rw [hM] at hMu
  have hHq : H ((1 - q) / 2) ≤ H ((1 - ((B.q0 : ℚ) : ℝ)) / 2) :=
    H_mono_left (by linarith) (by linarith) (by linarith)
  set cl : ℚ := 1 - Hhi ((1 - B.q0) / 2) pM with hcl
  have ecl : (cl : ℝ) = 1 - (Hhi ((1 - B.q0) / 2) pM : ℝ) := by rw [hcl]; push_cast; ring
  have rcl0 : (0 : ℝ) ≤ (cl : ℝ) := by exact_mod_cast hcap0
  have hclle : (cl : ℝ) ≤ 1 - H ((1 - q) / 2) := by rw [ecl]; linarith
  have rEC : (B.e1 : ℝ) + (cl : ℝ) ≤ 1 := by exact_mod_cast hEC
  have hgain := parent_gain_lower hE he1 rcl0 hclle hphys rEC
  have rxc0 : (0 : ℝ) < (xc : ℝ) := by exact_mod_cast hxc0
  have rxc1 : 2 * (xc : ℝ) ≤ 1 := by exact_mod_cast hxc1
  have rxc2 : (B.e1 : ℝ) ≤ (Hlo xc pxc : ℝ) := by exact_mod_cast hxc2
  have hetaLo : (1 - 2 * (xc : ℝ)) * J (xc : ℝ) ≤ eta (B.e1 : ℝ) :=
    eta_ge_bracket (r1.trans_le r2) (by linarith) rxc0 (by linarith) (rxc2.trans hxcHl)
  have rxa0 : (0 : ℝ) < (xa : ℝ) := by exact_mod_cast hxa0
  have rxa1 : 2 * (xa : ℝ) ≤ 1 := by exact_mod_cast hxa1
  have rxa2 : (Hhi xa pxa : ℝ) ≤ (B.e1 : ℝ) + (cl : ℝ) := by exact_mod_cast hxa2
  have hetaHi : eta ((B.e1 : ℝ) + (cl : ℝ)) ≤ (1 - 2 * (xa : ℝ)) * J (xa : ℝ) :=
    eta_le_bracket (by linarith [r1.trans_le r2]) rEC rxa0 (by linarith) (hxaHu.trans rxa2)
  have hJxc : (1 - 2 * (xc : ℝ)) * (Jlo xc pxc : ℝ) ≤ (1 - 2 * (xc : ℝ)) * J (xc : ℝ) :=
    mul_le_mul_of_nonneg_left hxcJl (by linarith)
  have hJxa : (1 - 2 * (xa : ℝ)) * J (xa : ℝ) ≤ (1 - 2 * (xa : ℝ)) * (Jhi xa pxa : ℝ) :=
    mul_le_mul_of_nonneg_left hxaJu (by linarith)
  have racc : (7 / 10 : ℝ) * (((B.q1 : ℚ) : ℝ) ^ 2 / (B.e0 : ℝ)) ≤
      (1 - 2 * (xc : ℝ)) * (Jlo xc pxc : ℝ) - (1 - 2 * (xa : ℝ)) * (Jhi xa pxa : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hacc
    push_cast at this
    linarith
  have hq0' : 0 ≤ q := hq
  have hsq : q ^ 2 ≤ ((B.q1 : ℚ) : ℝ) ^ 2 := pow_le_pow_left₀ hq0' hqq1 2
  have hnorm : q ^ 2 / E ≤ ((B.q1 : ℚ) : ℝ) ^ 2 / (B.e0 : ℝ) :=
    (div_le_div_of_nonneg_right hsq hE.le).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) r1 he0)
  linarith

theorem checkEY_logb_sound {B : EYBox} {pM0 pM1 : PtCert} {v0 : ℚ} {pv0 : PtCert} {v1 : ℚ}
    {pv1 : PtCert} {cU : LogCert} (h : checkEY B (.logb pM0 pM1 v0 pv0 v1 pv1 cU) = true) :
    SemEY B := by
  intro E q he0 he1 hy0 hy1 hq
  unfold checkEY at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hbox, hpM0⟩, hpM1⟩, hpv0⟩, hpv1⟩, hcU⟩, hcH0⟩, hh1⟩, ⟨hv02, hv0e⟩⟩,
    ⟨hv12, hv1h⟩⟩, hℓpos⟩, hcUlo⟩, hacc⟩ := h
  obtain ⟨hE, hqq0, hqq1, hq1', hphys⟩ := ey_point hbox he0 he1 hy0 hy1
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := eyBoxOK_facts hbox
  rcases hq.eq_or_lt with hz | hqpos
  · rw [← hz]; norm_num [H_half]
  -- point enclosures
  obtain ⟨_, _, _, hM0u, _, _⟩ := checkPt_bounds hpM0
  obtain ⟨_, _, hM1l, _, _, _⟩ := checkPt_bounds hpM1
  obtain ⟨hv00, _, _, hv0Hu, _, _⟩ := checkPt_bounds hpv0
  obtain ⟨hv10, _, hv1Hl, _, _, _⟩ := checkPt_bounds hpv1
  obtain ⟨hU1, hU2⟩ := checkLogCert_sound hcU
  have hlogv0 := checkLogCert_sound (show checkLogCert v0 pv0.cx = true by
    unfold checkPt at hpv0; rw [Bool.and_eq_true] at hpv0; exact hpv0.1)
  have hlog1v0 := checkLogCert_sound (show checkLogCert (1 - v0) pv0.cy = true by
    unfold checkPt at hpv0; rw [Bool.and_eq_true] at hpv0; exact hpv0.2)
  -- the capacity
  set c := 1 - H ((1 - q) / 2) with hcdef
  have hc0 : 0 < c := capacity_pos hqpos hq1'.le
  have hL := log2_bounds
  have hLpos : 0 < Real.log 2 := log_two_pos
  set cH : ℚ := capHi B.q1 pM1 with hcHdef
  have ecH : (cH : ℝ) = 1 - (Hlo ((1 - B.q1) / 2) pM1 : ℝ) := by
    rw [hcHdef]; unfold capHi; push_cast; ring
  have hM1 : (((1 - B.q1) / 2 : ℚ) : ℝ) = (1 - ((B.q1 : ℚ) : ℝ)) / 2 := by push_cast; ring
  rw [hM1] at hM1l
  have hcle : c ≤ (cH : ℝ) := by
    have := capacity_mono hqq1 r5.le hq
    rw [ecH]; linarith
  have rcH0 : (0 : ℝ) < (cH : ℝ) := by exact_mod_cast hcH0
  have rh1 : (B.e1 : ℝ) + (cH : ℝ) < 1 := by exact_mod_cast hh1
  -- the slope coefficient on [E, E + c]
  have rv0 : (0 : ℝ) < (v0 : ℝ) := by exact_mod_cast hv00
  have rv02 : 2 * (v0 : ℝ) ≤ 1 := by exact_mod_cast hv02
  have rv0e : (Hhi v0 pv0 : ℝ) ≤ (B.e0 : ℝ) := by exact_mod_cast hv0e
  have rv12 : 2 * (v1 : ℝ) ≤ 1 := by exact_mod_cast hv12
  have rv1h : (B.e1 : ℝ) + (cH : ℝ) ≤ (Hlo v1 pv1 : ℝ) := by exact_mod_cast hv1h
  have hℓ : Real.log ((1 - (v0 : ℝ)) / (v0 : ℝ)) ≤ ((pv0.cy.hi - pv0.cx.lo : ℚ) : ℝ) := by
    have hv0' : (v0 : ℝ) < 1 := by linarith
    rw [Real.log_div (by linarith) rv0.ne']
    push_cast at hlog1v0 ⊢
    linarith [hlog1v0.2, hlogv0.1]
  set β : ℚ := betaLo v1 pv0 with hβdef
  have eβ : (β : ℝ) = (1 - 2 * (v1 : ℝ)) / (1 - (v1 : ℝ)) *
      (1 + 1 / ((pv0.cy.hi - pv0.cx.lo : ℚ) : ℝ)) / (L1 : ℝ) := by
    rw [hβdef]; unfold betaLo; push_cast; ring
  have hder : ∀ h, E < h → h < E + c → 2 + (β : ℝ) / h ≤ -deriv eta h := by
    intro h hlo hhi
    have h0 : 0 < h := hE.trans hlo
    have hh1' : h < 1 := by linarith
    have rv1pos : (0 : ℝ) < (v1 : ℝ) := by exact_mod_cast hv10
    have hs := slope_coeff_lower h0 hh1' rv0 rv1pos rv12
      ((hv0Hu.trans rv0e).trans (he0.trans hlo.le)) rv02
      (by linarith [hv1Hl]) hℓ hL.2
    rw [← eβ] at hs
    have : (β : ℝ) / h ≤ -deriv eta h - 2 := by
      rw [div_le_iff₀ h0]; linarith
    linarith
  have hβ0 : (0 : ℝ) ≤ (β : ℝ) := by
    rw [eβ]
    have hL1 : (0 : ℝ) < (L1 : ℝ) := hLpos.trans_le hL.2
    have rℓ : (0 : ℝ) < ((pv0.cy.hi - pv0.cx.lo : ℚ) : ℝ) := by exact_mod_cast hℓpos
    have : (0 : ℝ) ≤ 1 - 2 * (v1 : ℝ) := by linarith
    have : (0 : ℝ) < 1 - (v1 : ℝ) := by linarith
    positivity
  have hgain := eta_increment_ge_beta_log hE hc0.le hphys hder
  -- logarithmic factor
  set U : ℚ := cH / B.e0 with hUdef
  have eU : (U : ℝ) = (cH : ℝ) / (B.e0 : ℝ) := by rw [hUdef]; push_cast; ring
  have hcE : c / E ≤ (U : ℝ) := by
    rw [eU]
    exact (div_le_div_of_nonneg_right hcle hE.le).trans
      (div_le_div_of_nonneg_left rcH0.le r1 he0)
  have hcEpos : 0 < c / E := div_pos hc0 hE
  have hUpos : (0 : ℝ) < (U : ℝ) := hcEpos.trans_le hcE
  have hl0 := log_one_add_div_antitone hcEpos hcE
  have eU1 : ((1 + cH / B.e0 : ℚ) : ℝ) = 1 + (U : ℝ) := by rw [eU]; push_cast; ring
  rw [eU1] at hU1
  have rcUlo : (0 : ℝ) ≤ (cU.lo : ℝ) := by exact_mod_cast hcUlo
  have hl0' : (cU.lo : ℝ) / (U : ℝ) ≤ Real.log (1 + c / E) / (c / E) :=
    (div_le_div_of_nonneg_right hU1 hUpos.le).trans hl0
  -- capacity ratio
  have hT : ((tLo B.q0 pM0 : ℚ) : ℝ) ≤ c / q ^ 2 := by
    unfold tLo
    have hhalf : (((1 / (2 * L1)) : ℚ) : ℝ) ≤ c / q ^ 2 := by
      have := capacity_ratio_ge_half hqpos hq1'.le
      push_cast
      refine le_trans ?_ this
      exact one_div_le_one_div_of_le (by positivity) (by linarith [hL.2])
    split_ifs with hq0z
    · exact hhalf
    · push_cast
      apply max_le
      · simpa using hhalf
      · have rq0 : (0 : ℝ) < ((B.q0 : ℚ) : ℝ) := by
          have h0 : (0 : ℚ) ≤ B.q0 := by unfold EYBox.q0; exact mul_nonneg (by exact_mod_cast r1.le) (by exact_mod_cast r3)
          exact_mod_cast lt_of_le_of_ne h0 (Ne.symm hq0z)
        have hM0 : (((1 - B.q0) / 2 : ℚ) : ℝ) = (1 - ((B.q0 : ℚ) : ℝ)) / 2 := by push_cast; ring
        rw [hM0] at hM0u
        have hmono := capacity_ratio_mono rq0 hqq0 hq1'.le
        refine le_trans ?_ hmono
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        linarith
  have hTpos : (0 : ℝ) < ((tLo B.q0 pM0 : ℚ) : ℝ) := by
    unfold tLo
    have hL1 : (0 : ℝ) < (L1 : ℝ) := hLpos.trans_le hL.2
    split_ifs
    · push_cast; positivity
    · push_cast
      exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  -- assemble
  have racc : (7 / 10 : ℝ) ≤ ((tLo B.q0 pM0 : ℚ) : ℝ) *
      (2 * (B.e0 : ℝ) + (β : ℝ) * ((cU.lo : ℝ) / (U : ℝ))) := by
    have := (Rat.cast_le (K := ℝ)).mpr hacc
    push_cast at this
    linarith
  have hlogeq : Real.log (1 + c / E) = (c / E) * (Real.log (1 + c / E) / (c / E)) := by
    field_simp
  have hkey : ((tLo B.q0 pM0 : ℚ) : ℝ) * (2 * (B.e0 : ℝ) + (β : ℝ) * ((cU.lo : ℝ) / (U : ℝ))) ≤
      (c / q ^ 2) * (2 * E + (β : ℝ) * (Real.log (1 + c / E) / (c / E))) := by
    apply mul_le_mul hT _ (by positivity) (by positivity)
    have := mul_le_mul_of_nonneg_left hl0' hβ0
    linarith
  have hfinal : (c / q ^ 2) * (2 * E + (β : ℝ) * (Real.log (1 + c / E) / (c / E))) * (q ^ 2 / E) =
      2 * c + (β : ℝ) * Real.log (1 + c / E) := by
    rw [hlogeq]
    field_simp
  have hqE : 0 ≤ q ^ 2 / E := by positivity
  calc (7 / 10) * (q ^ 2 / E)
      ≤ (c / q ^ 2) * (2 * E + (β : ℝ) * (Real.log (1 + c / E) / (c / E))) * (q ^ 2 / E) :=
        mul_le_mul_of_nonneg_right (racc.trans hkey) hqE
    _ = 2 * c + (β : ℝ) * Real.log (1 + c / E) := hfinal
    _ ≤ eta E - eta (E + c) := hgain

theorem checkEY_sound {B : EYBox} {c : PGCert} (h : checkEY B c = true) : SemEY B := by
  cases c with
  | direct pM xc pxc xa pxa => exact checkEY_direct_sound h
  | logb pM0 pM1 v0 pv0 v1 pv1 cU => exact checkEY_logb_sound h

/-! ## Trees -/

def EYBox.lower (B : EYBox) : ℕ → EYBox
  | 0 => { B with e1 := (B.e0 + B.e1) / 2 }
  | _ => { B with y1 := (B.y0 + B.y1) / 2 }

def EYBox.upper (B : EYBox) : ℕ → EYBox
  | 0 => { B with e0 := (B.e0 + B.e1) / 2 }
  | _ => { B with y0 := (B.y0 + B.y1) / 2 }

def checkTreeEY : EYBox → CTree PGCert → Bool
  | B, .leaf c => checkEY B c
  | B, .node ax l r => decide (ax ≤ 1) && checkTreeEY (B.lower ax) l && checkTreeEY (B.upper ax) r

theorem semEY_of_halves {B : EYBox} {ax : ℕ} (hax : ax ≤ 1) (hl : SemEY (B.lower ax))
    (hr : SemEY (B.upper ax)) : SemEY B := by
  intro E q he0 he1 hy0 hy1 hq
  obtain rfl | rfl : ax = 0 ∨ ax = 1 := by omega
  · by_cases hm : E ≤ (((B.e0 + B.e1) / 2 : ℚ) : ℝ)
    · exact hl E q he0 hm hy0 hy1 hq
    · exact hr E q (le_of_not_ge hm) he1 hy0 hy1 hq
  · by_cases hm : q ≤ (((B.y0 + B.y1) / 2 : ℚ) : ℝ) * E
    · exact hl E q he0 he1 hy0 hm hq
    · exact hr E q he0 he1 (le_of_not_ge hm) hy1 hq

theorem checkTreeEY_sound : ∀ (T : CTree PGCert) (B : EYBox), checkTreeEY B T = true → SemEY B
  | .leaf c, B, h => checkEY_sound h
  | .node ax l r, B, h => by
    unfold checkTreeEY at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact semEY_of_halves h.1.1 (checkTreeEY_sound l _ h.1.2) (checkTreeEY_sound r _ h.2)

/-! ## The analytic tail `E ≤ 1/10000` -/

theorem parent_gain_tail {E q : ℝ} (hE : 0 < E) (hEt : E ≤ 1 / 10000) (hq : 0 ≤ q)
    (hqE : q ≤ 8 * E) :
    (7 / 10) * (q ^ 2 / E) ≤ eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  rcases hq.eq_or_lt with hz | hqpos
  · rw [← hz]; norm_num [H_half]
  set L := Real.log 2
  set c := 1 - H ((1 - q) / 2)
  set c₀ := q ^ 2 / (2 * L)
  have hL : 0 < L := log_two_pos
  have hLcap : L ≤ 7 / 10 := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    exact h.trans (by norm_num)
  have hq1 : q < 1 := by linarith
  have hc0 : 0 ≤ c₀ := by positivity
  have hcle : c₀ ≤ c := by
    have h := SmallMean.Cn_ge_half_sq hq hq1.le
    unfold SmallMean.Cn at h
    change q ^ 2 / (2 * L) ≤ c
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hc : 0 ≤ c := hc0.trans hcle
  have hcq := capacity_le_sq hqpos hq1
  have hphys : E + c ≤ 1 := by nlinarith
  have hgain := eta_increment_ge_rational hE hc hphys
  have hmono : c₀ / (L * (E + c₀)) ≤ c / (L * (E + c)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h := mul_le_mul_of_nonneg_left hcle (mul_nonneg hL.le hE.le)
    nlinarith
  have heq : c₀ / (L * (E + c₀)) = q ^ 2 / (L * (2 * L * E + q ^ 2)) := by
    simp only [c₀]
    field_simp
  have hqSq : q ^ 2 ≤ 64 * E ^ 2 := by nlinarith
  have hden : (7 / 10) * (L * (2 * L * E + q ^ 2)) ≤ E := by
    have hLsq : L ^ 2 ≤ 49 / 100 := by nlinarith
    have h1 : (7 / 10) * L * q ^ 2 ≤ (7 / 10) * (7 / 10) * (64 * E ^ 2) := by
      have := mul_le_mul hLcap hqSq (sq_nonneg q) (by norm_num)
      nlinarith
    nlinarith
  have hb : (7 / 10) * (q ^ 2 / E) ≤ q ^ 2 / (L * (2 * L * E + q ^ 2)) := by
    rw [mul_div_assoc', div_le_div_iff₀ hE (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hden (sq_nonneg q)]
  rw [heq] at hmono
  exact hb.trans (hmono.trans hgain)

end CKLaneN4

end


