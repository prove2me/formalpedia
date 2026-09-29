-- Prove2me | Definitions.Def_CK_CKLaneP_EvalTheta
-- name    : CK_CKLaneP_EvalTheta
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:07:13.594112+00:00
-- url     : https://prove2.me/theorems/cc870696-6bf8-4eea-9499-1a1af3cdabef
-- title:
--   Courtade–Kumar proof module `CKLaneP.EvalTheta` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.EvalTheta` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.EvalTheta` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.EvalTheta (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/EvalTheta.lean)

import Definitions.Def_CK_CKLaneP_EvalBase
import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryThetaBracketBridge

-- ===== source module CKLaneP.EvalTheta =====
section
/-
Lane P — certified rational bounds for `H`, `J`, `radialSlope`, `Θ = e8Theta` and `Θ'`,
driven by rational *contact points* `v`.

For a rational `v ∈ (0, 1/2]` the log data `a1 ≤ -log v ≤ b1`, `a2 ≤ -log(1-v) ≤ b2` (from
`logQ`, kernel-evaluated) give enclosures of
* `hn v = v·L1 + (1-v)·L2`, `H v = hn v / log 2`, `J v = (L1 - L2)/log 2`,
* `radialSlope v = J v + (1-2v)·hn v / (log 2 · v(1-v) · (L1+L2))`,
where `L1 = -log v`, `L2 = -log(1-v)`.
Θ bounds use the corpus bracket bridge (`ZeroCapLeftStationaryThetaBracket`):
* if `1 - 2v ≤ 2·x·Hlo(v)` then `Slo(v) ≤ Θ(x)`;
* if `2·x·Hhi(v) ≤ 1 - 2v` then `Θ(x) ≤ Shi(v)`.
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed

/-- Short dyadic bounds of `log 2` (scale `2^64`), used by all kernel evaluations below. -/
def L2loD : ℚ := 12786308645202655659 / 18446744073709551616
/-- Upper companion of `L2loD`. -/
def L2hiD : ℚ := 12786308645202655660 / 18446744073709551616

theorem log2D_bounds : ((L2loD : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((L2hiD : ℚ) : ℝ) := by
  have h := log2_bounds
  have h1 : L2loD ≤ L2lo := by unfold L2loD L2lo; decide +kernel
  have h2 : L2hi ≤ L2hiD := by unfold L2hiD L2hi; decide +kernel
  have h1' : ((L2loD : ℚ) : ℝ) ≤ ((L2lo : ℚ) : ℝ) := by exact_mod_cast h1
  have h2' : ((L2hi : ℚ) : ℝ) ≤ ((L2hiD : ℚ) : ℝ) := by exact_mod_cast h2
  exact ⟨h1'.trans h.1, h.2.trans h2'⟩

/-- Rational log data at a contact point. -/
structure VD where
  v : ℚ
  a1 : ℚ
  b1 : ℚ
  a2 : ℚ
  b2 : ℚ
deriving Repr

namespace VD

theorem cast_le_half {q : ℚ} (h : q ≤ 1 / 2) : (q : ℝ) ≤ 1 / 2 := by
  have h' : ((q : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr h
  rw [show ((1 / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h'
  exact h'

theorem cast_lt_half {q : ℚ} (h : q < 1 / 2) : (q : ℝ) < 1 / 2 := by
  have h' : ((q : ℚ) : ℝ) < ((1 / 2 : ℚ) : ℝ) := Rat.cast_lt.mpr h
  rw [show ((1 / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h'
  exact h'

/-- Semantic soundness of the log data. -/
def Sound (d : VD) : Prop :=
  0 < d.v ∧ d.v ≤ 1 / 2 ∧
  (d.a1 : ℝ) ≤ -Real.log (d.v : ℝ) ∧ -Real.log (d.v : ℝ) ≤ (d.b1 : ℝ) ∧
  (d.a2 : ℝ) ≤ -Real.log (1 - (d.v : ℝ)) ∧ -Real.log (1 - (d.v : ℝ)) ≤ (d.b2 : ℝ)

/-- Kernel-computed log data. -/
def ofQ (P n : ℕ) (v : ℚ) : VD :=
  ⟨v, -(logQ P n v).hi, -(logQ P n v).lo, -(logQ P n (1 - v)).hi, -(logQ P n (1 - v)).lo⟩

/-- Decidable precondition for `mk` to be sound. -/
def ok (P : ℕ) (v : ℚ) : Bool :=
  decide (0 < v ∧ v ≤ 1 / 2 ∧ 0 < rdn P v ∧ 0 < rdn P (1 - v))

theorem ofQ_sound {P n : ℕ} {v : ℚ} (h : ok P v = true) : (ofQ P n v).Sound := by
  unfold ok at h
  obtain ⟨h0, h1, h2, h3⟩ := of_decide_eq_true h
  have hv := logQ_sound (P := P) (n := n) h0 h2
  have h1v : (0 : ℚ) < 1 - v := by linarith
  have hw := logQ_sound (P := P) (n := n) h1v h3
  have ecast : ((1 - v : ℚ) : ℝ) = 1 - (v : ℝ) := by push_cast; ring
  rw [ecast] at hw
  obtain ⟨hv1, hv2⟩ := hv
  obtain ⟨hw1, hw2⟩ := hw
  refine ⟨h0, h1, ?_, ?_, ?_, ?_⟩
  all_goals (simp only [ofQ]; push_cast; try linarith)

/-! ### Elementary identities -/

theorem hn_eq_logs (v : ℝ) :
    hn v = v * (-Real.log v) + (1 - v) * (-Real.log (1 - v)) := by
  unfold hn; ring

theorem J_eq_logs {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    J v = ((-Real.log v) - (-Real.log (1 - v))) / Real.log 2 := by
  unfold J
  rw [Real.log_div (by linarith) hv.ne']
  ring_nf

theorem kap_eq_logs {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    kap v = ((-Real.log v) + (-Real.log (1 - v))) / 2 := by
  unfold kap
  rw [Real.log_mul hv.ne' (by linarith)]
  ring

theorem H_eq_hn (v : ℝ) : H v = hn v / Real.log 2 := by
  rw [hn_eq_H_mul_log, mul_div_assoc, div_self log_two_pos.ne', mul_one]

theorem neg_log_nonneg {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) : 0 ≤ -Real.log v := by
  have := Real.log_nonpos hv.le hv1
  linarith

/-! ### Enclosures -/

/-- Lower bound of `hn v`. -/
def hnLo (d : VD) : ℚ := max 0 (d.v * d.a1 + (1 - d.v) * d.a2)
/-- Upper bound of `hn v`. -/
def hnHi (d : VD) : ℚ := d.v * d.b1 + (1 - d.v) * d.b2

theorem hn_nonneg' {v : ℝ} (hv : 0 < v) (hv1 : v < 1) : 0 ≤ hn v := by
  rw [hn_eq_logs]
  have h1 := neg_log_nonneg hv hv1.le
  have h2 := neg_log_nonneg (show (0 : ℝ) < 1 - v by linarith) (by linarith)
  have : 0 ≤ 1 - v := by linarith
  positivity

theorem hnLo_le {d : VD} (hd : d.Sound) : ((d.hnLo : ℚ) : ℝ) ≤ hn (d.v : ℝ) := by
  obtain ⟨h0, h1, ha1, _, ha2, _⟩ := hd
  have hv0 : (0 : ℝ) < d.v := by exact_mod_cast h0
  have hv1 : (d.v : ℝ) ≤ 1 / 2 := cast_le_half h1
  have hnn := hn_nonneg' hv0 (by linarith)
  rw [hn_eq_logs]
  unfold hnLo
  push_cast
  apply max_le
  · rw [← hn_eq_logs]; exact hnn
  · have e1 := mul_le_mul_of_nonneg_left ha1 hv0.le
    have e2 := mul_le_mul_of_nonneg_left ha2 (show (0 : ℝ) ≤ 1 - d.v by linarith)
    linarith

theorem le_hnHi {d : VD} (hd : d.Sound) : hn (d.v : ℝ) ≤ ((d.hnHi : ℚ) : ℝ) := by
  obtain ⟨h0, h1, _, hb1, _, hb2⟩ := hd
  have hv0 : (0 : ℝ) < d.v := by exact_mod_cast h0
  have hv1 : (d.v : ℝ) ≤ 1 / 2 := cast_le_half h1
  rw [hn_eq_logs]
  unfold hnHi
  push_cast
  have e1 := mul_le_mul_of_nonneg_left hb1 hv0.le
  have e2 := mul_le_mul_of_nonneg_left hb2 (show (0 : ℝ) ≤ 1 - d.v by linarith)
  linarith

/-- Lower bound of `H v`. -/
def Hlo (d : VD) : ℚ := d.hnLo / L2hiD
/-- Upper bound of `H v`. -/
def Hhi (d : VD) : ℚ := d.hnHi / L2loD

theorem L2lo_pos : (0 : ℝ) < (L2loD : ℝ) := by
  have h : (0 : ℚ) < L2loD := by unfold L2loD; norm_num
  exact_mod_cast h

theorem Hlo_le {d : VD} (hd : d.Sound) : ((d.Hlo : ℚ) : ℝ) ≤ H (d.v : ℝ) := by
  have hL := log2D_bounds
  have hlo := hnLo_le hd
  have h0 : (0 : ℝ) ≤ ((d.hnLo : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ d.hnLo := le_max_left _ _
    exact_mod_cast this
  have hl2 : 0 < Real.log 2 := log_two_pos
  unfold Hlo
  push_cast
  rw [H_eq_hn]
  calc ((d.hnLo : ℚ) : ℝ) / (L2hiD : ℝ) ≤ ((d.hnLo : ℚ) : ℝ) / Real.log 2 :=
        div_le_div_of_nonneg_left h0 hl2 hL.2
    _ ≤ hn (d.v : ℝ) / Real.log 2 := div_le_div_of_nonneg_right hlo hl2.le

theorem le_Hhi {d : VD} (hd : d.Sound) : H (d.v : ℝ) ≤ ((d.Hhi : ℚ) : ℝ) := by
  have hL := log2D_bounds
  have hhi := le_hnHi hd
  obtain ⟨h0, h1, _⟩ := hd
  have hv0 : (0 : ℝ) < d.v := by exact_mod_cast h0
  have hv1 : (d.v : ℝ) ≤ 1 / 2 := cast_le_half h1
  have hnn := hn_nonneg' hv0 (by linarith)
  have hl2 : 0 < Real.log 2 := log_two_pos
  unfold Hhi
  push_cast
  rw [H_eq_hn]
  calc hn (d.v : ℝ) / Real.log 2 ≤ ((d.hnHi : ℚ) : ℝ) / Real.log 2 :=
        div_le_div_of_nonneg_right hhi hl2.le
    _ ≤ ((d.hnHi : ℚ) : ℝ) / (L2loD : ℝ) :=
        div_le_div_of_nonneg_left (hnn.trans hhi) L2lo_pos hL.1

/-- Lower bound of `J v`. -/
def Jlo (d : VD) : ℚ := max 0 (d.a1 - d.b2) / L2hiD
/-- Upper bound of `J v` (needs `0 ≤ b1 - a2`, automatic when sound). -/
def Jhi (d : VD) : ℚ := (d.b1 - d.a2) / L2loD

theorem logs_order {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1 / 2) :
    -Real.log (1 - v) ≤ -Real.log v := by
  have : Real.log v ≤ Real.log (1 - v) := Real.log_le_log hv (by linarith)
  linarith

theorem Jlo_le {d : VD} (hd : d.Sound) : ((d.Jlo : ℚ) : ℝ) ≤ J (d.v : ℝ) := by
  have hL := log2D_bounds
  obtain ⟨h0, h1, ha1, _, _, hb2⟩ := hd
  have hv0 : (0 : ℝ) < d.v := by exact_mod_cast h0
  have hv1 : (d.v : ℝ) ≤ 1 / 2 := cast_le_half h1
  have hord := logs_order hv0 hv1
  have hl2 : 0 < Real.log 2 := log_two_pos
  rw [J_eq_logs hv0 (by linarith)]
  unfold Jlo
  push_cast
  have hm0 : (0 : ℝ) ≤ max 0 ((d.a1 : ℝ) - (d.b2 : ℝ)) := le_max_left _ _
  have hm : max 0 ((d.a1 : ℝ) - (d.b2 : ℝ)) ≤ -Real.log (d.v : ℝ) - -Real.log (1 - (d.v : ℝ)) :=
    max_le (by linarith) (by linarith)
  calc max 0 ((d.a1 : ℝ) - (d.b2 : ℝ)) / (L2hiD : ℝ)
      ≤ max 0 ((d.a1 : ℝ) - (d.b2 : ℝ)) / Real.log 2 := div_le_div_of_nonneg_left hm0 hl2 hL.2
    _ ≤ _ := div_le_div_of_nonneg_right hm hl2.le

theorem le_Jhi {d : VD} (hd : d.Sound) : J (d.v : ℝ) ≤ ((d.Jhi : ℚ) : ℝ) := by
  have hL := log2D_bounds
  obtain ⟨h0, h1, _, hb1, ha2, _⟩ := hd
  have hv0 : (0 : ℝ) < d.v := by exact_mod_cast h0
  have hv1 : (d.v : ℝ) ≤ 1 / 2 := cast_le_half h1
  have hord := logs_order hv0 hv1
  have hl2 : 0 < Real.log 2 := log_two_pos
  rw [J_eq_logs hv0 (by linarith)]
  unfold Jhi
  push_cast
  have hn0 : 0 ≤ -Real.log (d.v : ℝ) - -Real.log (1 - (d.v : ℝ)) := by linarith
  have hm : -Real.log (d.v : ℝ) - -Real.log (1 - (d.v : ℝ)) ≤ (d.b1 : ℝ) - (d.a2 : ℝ) := by
    linarith
  calc (-Real.log (d.v : ℝ) - -Real.log (1 - (d.v : ℝ))) / Real.log 2
      ≤ ((d.b1 : ℝ) - (d.a2 : ℝ)) / Real.log 2 := div_le_div_of_nonneg_right hm hl2.le
    _ ≤ ((d.b1 : ℝ) - (d.a2 : ℝ)) / (L2loD : ℝ) :=
        div_le_div_of_nonneg_left (hn0.trans hm) L2lo_pos hL.1

/-- `radialSlope` in log form. -/
theorem radialSlope_eq_logs {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    radialSlope v = J v + (1 - 2 * v) * hn v /
      (Real.log 2 * (v * (1 - v)) * ((-Real.log v) + (-Real.log (1 - v)))) := by
  unfold radialSlope
  rw [kap_eq_logs hv hv1]
  congr 1
  congr 1
  ring

/-- Lower bound of `radialSlope v`. -/
def Slo (d : VD) : ℚ :=
  d.Jlo + (1 - 2 * d.v) * d.hnLo / (L2hiD * (d.v * (1 - d.v)) * (d.b1 + d.b2))
/-- Upper bound of `radialSlope v` (valid when `0 < a1 + a2`). -/
def Shi (d : VD) : ℚ :=
  d.Jhi + (1 - 2 * d.v) * d.hnHi / (L2loD * (d.v * (1 - d.v)) * (d.a1 + d.a2))

theorem Slo_le {d : VD} (hd : d.Sound) : ((d.Slo : ℚ) : ℝ) ≤ radialSlope (d.v : ℝ) := by
  have hL := log2D_bounds
  have hJ := Jlo_le hd
  have hhn := hnLo_le hd
  obtain ⟨h0, h1, _, hb1, _, hb2⟩ := hd
  have hv0 : (0 : ℝ) < d.v := by exact_mod_cast h0
  have hv1 : (d.v : ℝ) ≤ 1 / 2 := cast_le_half h1
  have hl2 : 0 < Real.log 2 := log_two_pos
  have hL1 := neg_log_nonneg hv0 (by linarith)
  have hL1pos : 0 < -Real.log (d.v : ℝ) := by
    have : Real.log (d.v : ℝ) < 0 := Real.log_neg hv0 (by linarith)
    linarith
  have hL2 := neg_log_nonneg (show (0 : ℝ) < 1 - d.v by linarith) (by linarith)
  have hvv : 0 < (d.v : ℝ) * (1 - d.v) := mul_pos hv0 (by linarith)
  have hr : (0 : ℝ) ≤ 1 - 2 * d.v := by linarith
  have hlo0 : (0 : ℝ) ≤ ((d.hnLo : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ d.hnLo := le_max_left _ _
    exact_mod_cast this
  rw [radialSlope_eq_logs hv0 (by linarith)]
  unfold Slo
  push_cast
  apply add_le_add hJ
  -- second term: numerator down, denominator up
  have hK : 0 < -Real.log (d.v : ℝ) + -Real.log (1 - (d.v : ℝ)) := by linarith
  have hDen1 : 0 < Real.log 2 * ((d.v : ℝ) * (1 - d.v)) *
      (-Real.log (d.v : ℝ) + -Real.log (1 - (d.v : ℝ))) := by positivity
  have hDenLe : Real.log 2 * ((d.v : ℝ) * (1 - d.v)) *
      (-Real.log (d.v : ℝ) + -Real.log (1 - (d.v : ℝ))) ≤
      (L2hiD : ℝ) * ((d.v : ℝ) * (1 - d.v)) * ((d.b1 : ℝ) + (d.b2 : ℝ)) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_right hL.2 hvv.le) (by linarith) hK.le
    exact mul_nonneg (by linarith [hL.1, L2lo_pos]) hvv.le
  have hnum : (1 - 2 * (d.v : ℝ)) * ((d.hnLo : ℚ) : ℝ) ≤ (1 - 2 * (d.v : ℝ)) * hn (d.v : ℝ) :=
    mul_le_mul_of_nonneg_left hhn hr
  calc (1 - 2 * (d.v : ℝ)) * ((d.hnLo : ℚ) : ℝ) /
        ((L2hiD : ℝ) * ((d.v : ℝ) * (1 - d.v)) * ((d.b1 : ℝ) + (d.b2 : ℝ)))
      ≤ (1 - 2 * (d.v : ℝ)) * ((d.hnLo : ℚ) : ℝ) / (Real.log 2 * ((d.v : ℝ) * (1 - d.v)) *
          (-Real.log (d.v : ℝ) + -Real.log (1 - (d.v : ℝ)))) :=
        div_le_div_of_nonneg_left (mul_nonneg hr hlo0) hDen1 hDenLe
    _ ≤ _ := div_le_div_of_nonneg_right hnum hDen1.le

theorem le_Shi {d : VD} (hd : d.Sound) (hpos : 0 < d.a1 + d.a2) :
    radialSlope (d.v : ℝ) ≤ ((d.Shi : ℚ) : ℝ) := by
  have hL := log2D_bounds
  have hJ := le_Jhi hd
  have hhn := le_hnHi hd
  obtain ⟨h0, h1, ha1, _, ha2, _⟩ := hd
  have hv0 : (0 : ℝ) < d.v := by exact_mod_cast h0
  have hv1 : (d.v : ℝ) ≤ 1 / 2 := cast_le_half h1
  have hl2 : 0 < Real.log 2 := log_two_pos
  have hvv : 0 < (d.v : ℝ) * (1 - d.v) := mul_pos hv0 (by linarith)
  have hr : (0 : ℝ) ≤ 1 - 2 * d.v := by linarith
  have hapos : (0 : ℝ) < (d.a1 : ℝ) + (d.a2 : ℝ) := by exact_mod_cast hpos
  have hnn := hn_nonneg' hv0 (by linarith)
  rw [radialSlope_eq_logs hv0 (by linarith)]
  unfold Shi
  push_cast
  apply add_le_add hJ
  have hDen2 : 0 < (L2loD : ℝ) * ((d.v : ℝ) * (1 - d.v)) * ((d.a1 : ℝ) + (d.a2 : ℝ)) := by
    have := L2lo_pos; positivity
  have hDenLe : (L2loD : ℝ) * ((d.v : ℝ) * (1 - d.v)) * ((d.a1 : ℝ) + (d.a2 : ℝ)) ≤
      Real.log 2 * ((d.v : ℝ) * (1 - d.v)) *
        (-Real.log (d.v : ℝ) + -Real.log (1 - (d.v : ℝ))) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_right hL.1 hvv.le) (by linarith) hapos.le
    exact mul_nonneg hl2.le hvv.le
  have hnum : (1 - 2 * (d.v : ℝ)) * hn (d.v : ℝ) ≤ (1 - 2 * (d.v : ℝ)) * ((d.hnHi : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_left hhn hr
  calc (1 - 2 * (d.v : ℝ)) * hn (d.v : ℝ) / (Real.log 2 * ((d.v : ℝ) * (1 - d.v)) *
        (-Real.log (d.v : ℝ) + -Real.log (1 - (d.v : ℝ))))
      ≤ (1 - 2 * (d.v : ℝ)) * hn (d.v : ℝ) /
          ((L2loD : ℝ) * ((d.v : ℝ) * (1 - d.v)) * ((d.a1 : ℝ) + (d.a2 : ℝ))) :=
        div_le_div_of_nonneg_left (mul_nonneg hr hnn) hDen2 hDenLe
    _ ≤ _ := div_le_div_of_nonneg_right hnum hDen2.le

end VD

/-! ### Θ bounds from contact brackets -/

open ZeroCapLeftStationaryThetaBracket in
/-- Lower bound of `Θ(x)` at any real `x ≥ xq` from a contact point `v` with
`1 - 2v ≤ 2·xq·Hlo(v)`. -/
theorem theta_ge_Slo {d : VD} (hd : d.Sound) (hv : d.v < 1 / 2) {xq : ℚ} {x : ℝ}
    (hxq0 : 0 < xq) (hxq : (xq : ℝ) ≤ x) (hc : 1 - 2 * d.v ≤ 2 * xq * d.Hlo) :
    ((d.Slo : ℚ) : ℝ) ≤ e8Theta x := by
  have hv0 : (0 : ℝ) < d.v := by exact_mod_cast hd.1
  have hvh : (d.v : ℝ) < 1 / 2 := VD.cast_lt_half hv
  have hxq0R : (0 : ℝ) < xq := by exact_mod_cast hxq0
  have hx : 0 < x := lt_of_lt_of_le hxq0R hxq
  have hHlo := VD.Hlo_le hd
  have hHlo0 : (0 : ℝ) ≤ ((d.Hlo : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ d.Hlo := by
      unfold VD.Hlo
      apply div_nonneg (le_max_left _ _)
      unfold L2hiD; norm_num
    exact_mod_cast this
  have hcR : 1 - 2 * (d.v : ℝ) ≤ 2 * (xq : ℝ) * ((d.Hlo : ℚ) : ℝ) := by exact_mod_cast hc
  have hres : 1 - 2 * (d.v : ℝ) ≤ 2 * x * ((d.Hlo : ℚ) : ℝ) := by
    have := mul_le_mul_of_nonneg_right hxq hHlo0
    nlinarith
  have hcont := contact_upper_of_entropy_lower hx hv0.le hvh.le hHlo hres
  exact le_trans (VD.Slo_le hd) (e8Theta_lower_of_contact_upper hx hv0 hvh hcont)

open ZeroCapLeftStationaryThetaBracket in
/-- Upper bound of `Θ(x)` at any real `0 < x ≤ xq` from a contact point `v` with
`2·xq·Hhi(v) ≤ 1 - 2v`. -/
theorem theta_le_Shi {d : VD} (hd : d.Sound) (hv : d.v < 1 / 2) (hpos : 0 < d.a1 + d.a2)
    {xq : ℚ} {x : ℝ} (hx : 0 < x) (hxq : x ≤ (xq : ℝ)) (hc : 2 * xq * d.Hhi ≤ 1 - 2 * d.v) :
    e8Theta x ≤ ((d.Shi : ℚ) : ℝ) := by
  have hv0 : (0 : ℝ) < d.v := by exact_mod_cast hd.1
  have hvh : (d.v : ℝ) < 1 / 2 := VD.cast_lt_half hv
  have hHhi := VD.le_Hhi hd
  have hH0 : 0 ≤ H (d.v : ℝ) := H_nonneg hv0.le (by linarith)
  have hcR : 2 * (xq : ℝ) * ((d.Hhi : ℚ) : ℝ) ≤ 1 - 2 * (d.v : ℝ) := by exact_mod_cast hc
  have hres : 2 * x * ((d.Hhi : ℚ) : ℝ) ≤ 1 - 2 * (d.v : ℝ) := by
    have h1 : x * ((d.Hhi : ℚ) : ℝ) ≤ (xq : ℝ) * ((d.Hhi : ℚ) : ℝ) :=
      mul_le_mul_of_nonneg_right hxq (hH0.trans hHhi)
    linarith
  have hcont := contact_lower_of_entropy_upper hx hv0.le hvh.le hHhi hres
  exact le_trans (e8Theta_upper_of_contact_lower hx hv0 hvh hcont) (VD.le_Shi hd hpos)

/-! ### Kernel pilot -/

/-- Pilot contact point `v = 1/10`: data, and a Θ lower bound at `x = 2`. -/
def pilotVD : VD := VD.ofQ 64 20 (1 / 10)

theorem pilotVD_ok : VD.ok 64 (1 / 10) = true := by decide +kernel

theorem pilotVD_numbers :
    1 - 2 * pilotVD.v ≤ 2 * 2 * pilotVD.Hlo ∧ 0 < pilotVD.a1 + pilotVD.a2 ∧
      (49 / 10 : ℚ) ≤ pilotVD.Slo ∧ pilotVD.Shi ≤ 491 / 100 := by
  decide +kernel

/-- Pilot: `4.9 ≤ Θ(2)` (true value `Θ(2) = 6.4577...`). -/
theorem pilot_theta_two : (49 / 10 : ℝ) ≤ e8Theta 2 := by
  have hd : pilotVD.Sound := VD.ofQ_sound pilotVD_ok
  have hn := pilotVD_numbers
  have hv : pilotVD.v < 1 / 2 := by decide +kernel
  have h := theta_ge_Slo hd hv (xq := 2) (x := 2) (by norm_num) (by norm_num) hn.1
  have h2 : ((49 / 10 : ℚ) : ℝ) ≤ ((pilotVD.Slo : ℚ) : ℝ) := by exact_mod_cast hn.2.2.1
  have e : ((49 / 10 : ℚ) : ℝ) = 49 / 10 := by norm_num
  linarith

end CKLaneP

end


