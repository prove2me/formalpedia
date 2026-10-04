-- Prove2me | Definitions.Def_CK_CKLaneN1_R3Q
-- name    : CK_CKLaneN1_R3Q
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T12:58:54.841982+00:00
-- url     : https://prove2.me/theorems/18a9c990-98c4-45b6-9f7d-50a5cb099fe9
-- title:
--   Courtade–Kumar proof module `CKLaneN1.R3Q` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.R3Q` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.R3Q` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.R3Q (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/R3Q.lean)

import Definitions.Def_CK_CKLaneN1_R3Leaf
import Definitions.Def_CK_CKLaneN1_EdgeCheck

-- ===== source module CKLaneN1.R3Q =====
section

/-!
# Lane N1 — CE-stat row 3: the sharpened leaf checker `leafOK2`

Same semantics `Sem` as `leafOK`, sharper bound (M07's frozen lemmas reused read-only):

`gapLB (H a) (H b) c ≥ y² · P(z)`,  `P(z) = α(1−z²) + β z² − T₃ z² − (1−z)(2κK₄(1−z) + z(K₄/2 + E₄))`,

* `α, β, κ` as in M07's `r3BoxOK` (`alphaQ, betaQ, kappaQ`), but `z` kept exact;
* Jensen penalty `T₃ z²` with `T₃ = slopeHi q · 2 JHn / J_M` (`JH ≤ (zy)² JHn`);
* log-form outer penalty: `Υ(q) − Υ(t_C) ≤ K (log t_C − log q) ≤ K((t_C − M)/M_lo + (M − q)/q_lo)` with
  `K ≥ sup w|Υ'(w)|` on `[q_lo, c_hi]` (`H(w)/w` antitone by concavity; `(2κ−s)/κ²` antitone), and
  `K₄ = K/M_lo`, `E₄ = K b₁c₁ JHn/(J_M q_lo)`;
* positivity of the quadratic `P` on `[z₀, z₁]` by N1's `qposOK` (proved sound in `EdgeCheck`).
-/

set_option autoImplicit false

namespace CKLaneN1.R3

open GeneralCK GeneralCK.Certificates.Mixed CKLaneN1 CKLaneE.FP CKLaneN1.Capital Set
open CKLaneM07.CE CKLaneM07.CE.R3

/-! ## Real lemmas -/

/-- `H(w)/w` is antitone: `H w · q ≤ H q · w` for `0 < q ≤ w ≤ 1` (concavity, `H 0 = 0`). -/
theorem r3q_H_mul_le {q w : ℝ} (hq : 0 < q) (hqw : q ≤ w) (hw : w ≤ 1) : H w * q ≤ H q * w := by
  have hw0 : 0 < w := hq.trans_le hqw
  have h := H_concaveOn_unit.2 (show w ∈ Icc (0 : ℝ) 1 from ⟨hw0.le, hw⟩)
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
    (div_nonneg hq.le hw0.le) (sub_nonneg.mpr ((div_le_one hw0).mpr hqw)) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, H_zero] at h
  rw [div_mul_cancel₀ q hw0.ne', div_mul_eq_mul_div, div_le_iff₀ hw0] at h
  linarith

/-- `(2κ − s)/κ²` is antitone in `κ ≥ k₀` when `0 ≤ s ≤ k₀`. -/
theorem r3q_kap_ratio {s k0 k : ℝ} (_hs : 0 ≤ s) (hsk : s ≤ k0) (hk0 : 0 < k0) (hk : k0 ≤ k) :
    (2 * k - s) / k ^ 2 ≤ (2 * k0 - s) / k0 ^ 2 := by
  have hk' : 0 < k := hk0.trans_le hk
  rw [div_le_div_iff₀ (pow_pos hk' 2) (pow_pos hk0 2)]
  have h1 : 0 ≤ k - k0 := by linarith
  have h2 : 0 ≤ k * (2 * k0 - s) - s * k0 := by
    nlinarith [mul_nonneg h1 (by linarith : (0 : ℝ) ≤ 2 * k0 - s),
      mul_nonneg hk0.le (by linarith : (0 : ℝ) ≤ k0 - s)]
  nlinarith [mul_nonneg h1 h2]

/-- log-form increment bound for the decreasing `Υ = radialSlope`. -/
theorem r3q_ups_log {u v K : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v < 1 / 2)
    (hK : ∀ w ∈ Icc u v, w * dUps w ≤ K) :
    radialSlope u - radialSlope v ≤ K * (Real.log v - Real.log u) := by
  have hg : ∀ w ∈ Icc u v, HasDerivAt (fun x => radialSlope x + K * Real.log x)
      (-dUps w + K * w⁻¹) w := by
    intro w hw
    have hw0 : 0 < w := hu.trans_le hw.1
    exact (hasDerivAt_ups hw0 (lt_of_le_of_lt hw.2 hv)).add
      ((Real.hasDerivAt_log hw0.ne').const_mul K)
  have hmono : MonotoneOn (fun x => radialSlope x + K * Real.log x) (Icc u v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc u v)
    · intro w hw; exact (hg w hw).continuousAt.continuousWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      exact (hg w ⟨hw.1.le, hw.2.le⟩).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      have hw' : w ∈ Icc u v := ⟨hw.1.le, hw.2.le⟩
      rw [(hg w hw').deriv]
      have hw0 : 0 < w := hu.trans hw.1
      have h1 : dUps w * w ≤ K := by linarith [hK w hw', mul_comm w (dUps w)]
      have h2 : dUps w ≤ K * w⁻¹ := by
        calc dUps w = dUps w * w * w⁻¹ := by field_simp
          _ ≤ K * w⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hw0.le)
      linarith
  have := hmono ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ huv
  simp only at this
  linarith

/-- `w · |Υ'(w)|` on `[q, c]` is bounded by a rational-friendly expression. -/
theorem r3q_wdUps {q c w k0 N L : ℝ} (hq : 0 < q) (hqw : q ≤ w) (hwc : w ≤ c) (hc : c < 1 / 2)
    (hk0 : 0 < k0) (hk0c : k0 ≤ kap c) (hs : (1 - 2 * c) ^ 2 ≤ k0) (hN : hn q ≤ N)
    (hL : 0 < L) (hLl : L ≤ Real.log 2) :
    w * dUps w ≤ N / q * ((2 * k0 - (1 - 2 * c) ^ 2) / k0 ^ 2) / (4 * L * (1 - c) ^ 2) := by
  have hw0 : 0 < w := hq.trans_le hqw
  have hw2 : w < 1 / 2 := lt_of_le_of_lt hwc hc
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkw : kap c ≤ kap w := kap_anti hw0 hwc hc.le
  have hkw0 : k0 ≤ kap w := hk0c.trans hkw
  have hkwpos : 0 < kap w := hk0.trans_le hkw0
  have hgap : 0 < 2 * kap w - (1 - 2 * w) ^ 2 := kap_sq_gap_pos hw0 hw2
  have hs' : (1 - 2 * c) ^ 2 ≤ (1 - 2 * w) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hratio := r3q_kap_ratio (sq_nonneg (1 - 2 * c)) hs hk0 hkw0
  have hHw : H w * q ≤ H q * w := r3q_H_mul_le hq hqw (by linarith)
  have hhn : hn w * q ≤ hn q * w := by
    rw [hn_eq_H_mul_log, hn_eq_H_mul_log]
    have k := mul_le_mul_of_nonneg_right hHw hL2.le
    linarith
  have hnw0 : 0 < hn w := by
    rw [hn_eq_H_mul_log]; exact mul_pos (H_pos hw0 (by linarith)) hL2
  have hnq : hn w / w ≤ N / q := by
    rw [div_le_div_iff₀ hw0 hq]
    have := mul_le_mul_of_nonneg_right hN hw0.le
    linarith
  have h1w : (1 - w) ≠ 0 := by linarith
  have e : w * dUps w = (hn w / w) * ((2 * kap w - (1 - 2 * w) ^ 2) / kap w ^ 2) /
      (4 * Real.log 2 * (1 - w) ^ 2) := by
    unfold dUps
    field_simp
  rw [e]
  have f1 : (2 * kap w - (1 - 2 * w) ^ 2) / kap w ^ 2 ≤ (2 * k0 - (1 - 2 * c) ^ 2) / k0 ^ 2 :=
    (div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)).trans hratio
  have f2 : 4 * L * (1 - c) ^ 2 ≤ 4 * Real.log 2 * (1 - w) ^ 2 := by
    have h1 : (1 - c) ^ 2 ≤ (1 - w) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have k := mul_le_mul hLl h1 (sq_nonneg _) hL2.le
    nlinarith [k]
  have p1 : 0 ≤ hn w / w := div_nonneg hnw0.le hw0.le
  have p2 : 0 ≤ (2 * kap w - (1 - 2 * w) ^ 2) / kap w ^ 2 := div_nonneg hgap.le (sq_nonneg _)
  have p3 : 0 < 4 * L * (1 - c) ^ 2 := by
    have : 0 < 1 - c := by linarith
    positivity
  have num : hn w / w * ((2 * kap w - (1 - 2 * w) ^ 2) / kap w ^ 2) ≤
      N / q * ((2 * k0 - (1 - 2 * c) ^ 2) / k0 ^ 2) :=
    mul_le_mul hnq f1 p2 (p1.trans hnq)
  have hnum0 : 0 ≤ N / q * ((2 * k0 - (1 - 2 * c) ^ 2) / k0 ^ 2) := (mul_nonneg p1 p2).trans num
  exact div_le_div₀ hnum0 num p3 f2

/-! ## The checker -/

section box

variable (B : B3)

/-- rational upper bound of `sup w |Υ'(w)|` over `[q, c_hi]` -/
def Kq (q : ℚ) : ℚ :=
  HnumHi q / q * ((2 * kapLoQ (cHi B) - (1 - 2 * cHi B) ^ 2) / kapLoQ (cHi B) ^ 2) /
    (4 * LqLo * (1 - cHi B) ^ 2)

def K4a (q : ℚ) : ℚ := Kq B q / MLo B
def E4 (q : ℚ) : ℚ := Kq B q * (B.b1 * B.c1 * JHn B) / (JMq B * q)
def T3n (q : ℚ) : ℚ := slopeHi q * 2 * JHn B / JMq B

def Pq0 (w : RWit) : ℚ := alphaQ B w - 2 * kappaQ B * K4a B w.q
def Pq1 (w : RWit) : ℚ := 4 * kappaQ B * K4a B w.q - K4a B w.q / 2 - E4 B w.q
def Pq2 (w : RWit) : ℚ :=
  -alphaQ B w + betaQ B - T3n B w.q - 2 * kappaQ B * K4a B w.q + K4a B w.q / 2 + E4 B w.q

def okK : Bool := decide ((1 - 2 * cHi B) ^ 2 ≤ kapLoQ (cHi B))

def bound2OK (w : RWit) : Bool :=
  okH B && okC B && okTheta B w && okQ B w && okRho B && okK B &&
    CKLaneN1.Edge.qposOK (Pq0 B w) (Pq1 B w) (Pq2 B w) B.b0 B.b1

/-- the sharpened row-3 leaf predicate -/
def leafOK2 (w : RWit) : Bool :=
  retVac B || tcVac B || (geomOK B && (vacOK B || bound2OK B w))

end box

theorem Kq_cast (B : B3) (q : ℚ) : ((Kq B q : ℚ) : ℝ) =
    ((HnumHi q : ℚ) : ℝ) / (q : ℝ) * ((2 * ((kapLoQ (cHi B) : ℚ) : ℝ) -
      (1 - 2 * ((cHi B : ℚ) : ℝ)) ^ 2) / ((kapLoQ (cHi B) : ℚ) : ℝ) ^ 2) /
      (4 * ((LqLo : ℚ) : ℝ) * (1 - ((cHi B : ℚ) : ℝ)) ^ 2) := by
  unfold Kq; push_cast; ring

theorem P_cast (B : B3) (w : RWit) (z : ℝ) :
    ((Pq0 B w : ℚ) : ℝ) + ((Pq1 B w : ℚ) : ℝ) * z + ((Pq2 B w : ℚ) : ℝ) * z ^ 2 =
      ((alphaQ B w : ℚ) : ℝ) * (1 - z ^ 2) + ((betaQ B : ℚ) : ℝ) * z ^ 2 -
        z ^ 2 * ((T3n B w.q : ℚ) : ℝ) -
        (1 - z) * (2 * ((kappaQ B : ℚ) : ℝ) * ((K4a B w.q : ℚ) : ℝ) * (1 - z) +
          z * (((K4a B w.q : ℚ) : ℝ) / 2 + ((E4 B w.q : ℚ) : ℝ))) := by
  unfold Pq0 Pq1 Pq2; push_cast; ring

/-! ## Pointwise bounds on a box -/

section pt

variable {B : B3} {a z y : ℝ}

/-- `T₁ + T₂` with `z` exact -/
theorem ptT12z (P : PtBox B a z y) (hH : okH B = true) (hC : okC B = true) {w : RWit}
    (hT : okTheta B w = true) :
    (a + y - a) / (2 * ((H a + H (a + z * y)) / 2)) ≤ ((Xq B : ℚ) : ℝ) ∧
    y ^ 2 * (((alphaQ B w : ℚ) : ℝ) * (1 - z ^ 2) + ((betaQ B : ℚ) : ℝ) * z ^ 2) ≤
      e8Theta ((Xq B : ℚ) : ℝ) / ((Xq B : ℚ) : ℝ) * ((a + y - a) ^ 2 - (a + z * y - a) ^ 2) /
          (4 * ((H a + H (a + z * y)) / 2)) +
        (a + z * y - a) ^ 2 / ((a + (a + z * y)) * Real.log 2) := by
  simp only [okH, Bool.and_eq_true, decide_eq_true_eq] at hH
  obtain ⟨⟨⟨⟨⟨hhLo, -⟩, -⟩, -⟩, -⟩, -⟩ := hH
  simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at hC
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hc1⟩ := hC
  simp only [okTheta, Bool.and_eq_true, decide_eq_true_eq] at hT
  obtain ⟨⟨hvok, hv0⟩, hres⟩ := hT
  have hhLoR : (0 : ℝ) < ((hLo B : ℚ) : ℝ) := by exact_mod_cast hhLo
  have hc1R : (0 : ℝ) < ((B.c1 : ℚ) : ℝ) := by exact_mod_cast hc1
  have hh_lo : ((hLo B : ℚ) : ℝ) ≤ (H a + H (a + z * y)) / 2 := by
    rw [hLo_cast]; linarith [P.Ha_lo, P.Hb_lo]
  have hh_hi : (H a + H (a + z * y)) / 2 ≤ ((hHi B : ℚ) : ℝ) := by
    rw [hHi_cast]; linarith [P.Ha_hi, P.Hb_hi]
  have hh0 : 0 < (H a + H (a + z * y)) / 2 := hhLoR.trans_le hh_lo
  have hX0 : (0 : ℝ) < ((Xq B : ℚ) : ℝ) := by
    rw [Xq_cast]; exact div_pos hc1R (by linarith)
  have hX : (a + y - a) / (2 * ((H a + H (a + z * y)) / 2)) ≤ ((Xq B : ℚ) : ℝ) := by
    rw [Xq_cast, show a + y - a = y by ring]
    exact div_le_div₀ hc1R.le P.y1 (by linarith) (by linarith)
  refine ⟨hX, ?_⟩
  have hresR : 1 - 2 * ((w.v : ℚ) : ℝ) ≤ 2 * ((Xq B : ℚ) : ℝ) * ((Hlo w.v : ℚ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hres; push_cast at this; linarith
  have hth := theta_ge hX0 hvok hresR
  have hv0R : (0 : ℝ) ≤ ((slopeLo w.v : ℚ) : ℝ) := by exact_mod_cast hv0
  have e1 : (a + y - a) ^ 2 - (a + z * y - a) ^ 2 = y ^ 2 * (1 - z ^ 2) := by ring
  have hz2 : z ^ 2 ≤ 1 := by nlinarith [P.hz0, P.hz1]
  have T1 : y ^ 2 * (((alphaQ B w : ℚ) : ℝ) * (1 - z ^ 2)) ≤
      e8Theta ((Xq B : ℚ) : ℝ) / ((Xq B : ℚ) : ℝ) * ((a + y - a) ^ 2 - (a + z * y - a) ^ 2) /
        (4 * ((H a + H (a + z * y)) / 2)) := by
    rw [e1, alphaQ_cast]
    have k1 : ((slopeLo w.v : ℚ) : ℝ) / ((Xq B : ℚ) : ℝ) ≤
        e8Theta ((Xq B : ℚ) : ℝ) / ((Xq B : ℚ) : ℝ) :=
      div_le_div_of_nonneg_right hth hX0.le
    have k2 : (1 - z ^ 2) * y ^ 2 / (4 * ((hHi B : ℚ) : ℝ)) ≤
        (1 - z ^ 2) * y ^ 2 / (4 * ((H a + H (a + z * y)) / 2)) :=
      div_le_div_of_nonneg_left (mul_nonneg (by linarith) (sq_nonneg _)) (by linarith) (by linarith)
    have k3 : 0 ≤ (1 - z ^ 2) * y ^ 2 / (4 * ((hHi B : ℚ) : ℝ)) :=
      div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by linarith)
    have k4 : 0 ≤ e8Theta ((Xq B : ℚ) : ℝ) / ((Xq B : ℚ) : ℝ) := div_nonneg (hv0R.trans hth) hX0.le
    have k := mul_le_mul k1 k2 k3 k4
    have eL : y ^ 2 * (((slopeLo w.v : ℚ) : ℝ) / ((Xq B : ℚ) : ℝ) / (4 * ((hHi B : ℚ) : ℝ)) *
        (1 - z ^ 2)) = ((slopeLo w.v : ℚ) : ℝ) / ((Xq B : ℚ) : ℝ) *
        ((1 - z ^ 2) * y ^ 2 / (4 * ((hHi B : ℚ) : ℝ))) := by ring
    have eR : e8Theta ((Xq B : ℚ) : ℝ) / ((Xq B : ℚ) : ℝ) * (y ^ 2 * (1 - z ^ 2)) /
        (4 * ((H a + H (a + z * y)) / 2)) = e8Theta ((Xq B : ℚ) : ℝ) / ((Xq B : ℚ) : ℝ) *
        ((1 - z ^ 2) * y ^ 2 / (4 * ((H a + H (a + z * y)) / 2))) := by ring
    rw [eL, eR]; exact k
  have T2 : y ^ 2 * (((betaQ B : ℚ) : ℝ) * z ^ 2) ≤
      (a + z * y - a) ^ 2 / ((a + (a + z * y)) * Real.log 2) := by
    rw [betaQ_cast, show a + z * y - a = z * y by ring]
    have hden0 : 0 < (a + (a + z * y)) * Real.log 2 :=
      mul_pos (by linarith [P.ha, P.hzy]) log2_pos
    have hden : (a + (a + z * y)) * Real.log 2 ≤
        (2 * ((B.a1 : ℚ) : ℝ) + ((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ)) * ((LqHi : ℚ) : ℝ) :=
      mul_le_mul (by linarith [P.a1, P.zy_hi]) LqHi_ge' log2_pos.le
        (by linarith [P.pa0, P.a0, P.a1, P.hzy, P.zy_hi])
    have k := div_le_div_of_nonneg_left (sq_nonneg (z * y)) hden0 hden
    have e : y ^ 2 * (1 / ((2 * ((B.a1 : ℚ) : ℝ) + ((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ)) *
        ((LqHi : ℚ) : ℝ)) * z ^ 2) = (z * y) ^ 2 /
        ((2 * ((B.a1 : ℚ) : ℝ) + ((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ)) * ((LqHi : ℚ) : ℝ)) := by
      ring
    rw [e]; exact k
  nlinarith [T1, T2]

/-- Jensen penalty with `z` exact -/
theorem ptT3z (P : PtBox B a z y) (hH : okH B = true) (hR : okRho B = true) {w : RWit}
    (hQ : okQ B w = true) :
    radialSlope (entropyInverse ((H a + H (a + z * y)) / 2)) *
        (a + (a + z * y) - 2 * entropyInverse ((H a + H (a + z * y)) / 2)) ≤
      y ^ 2 * (z ^ 2 * ((T3n B w.q : ℚ) : ℝ)) := by
  obtain ⟨hq0, hq, hqs⟩ := P.q_le hH hR hQ
  have h := P.cfg.T3 hq0 hq
  have hqs' := hqs
  simp only [slopeHiOk, Bool.and_eq_true, decide_eq_true_eq] at hqs'
  obtain ⟨⟨-, hqh⟩, -⟩ := hqs'
  have hqhR : (w.q : ℝ) < 1 / 2 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hqh
    push_cast at this
    linarith
  have hU0 : 0 < radialSlope (w.q : ℝ) := ups_pos hq0 hqhR
  have hU1 : radialSlope (w.q : ℝ) ≤ ((slopeHi w.q : ℚ) : ℝ) := le_slopeHi hqs
  obtain ⟨hJM0, hJM⟩ := P.JM hH
  obtain ⟨hn, hn0⟩ := P.JH_n hH hR
  have hJH0 := P.JH_nonneg
  have hJpos : 0 < J ((a + (a + z * y)) / 2) := hJM0.trans_le hJM
  have hsl0 : 0 ≤ ((slopeHi w.q : ℚ) : ℝ) := hU0.le.trans hU1
  have hR0 : 0 ≤ (H ((a + (a + z * y)) / 2) - (H a + H (a + z * y)) / 2) /
      J ((a + (a + z * y)) / 2) := div_nonneg hJH0 hJpos.le
  have key : radialSlope (entropyInverse ((H a + H (a + z * y)) / 2)) *
        (a + (a + z * y) - 2 * entropyInverse ((H a + H (a + z * y)) / 2)) ≤
      ((slopeHi w.q : ℚ) : ℝ) * (2 * ((H ((a + (a + z * y)) / 2) - (H a + H (a + z * y)) / 2) /
        J ((a + (a + z * y)) / 2))) :=
    h.trans (mul_le_mul_of_nonneg_right hU1 (by linarith))
  have bn : (H ((a + (a + z * y)) / 2) - (H a + H (a + z * y)) / 2) / J ((a + (a + z * y)) / 2) ≤
      y ^ 2 * (z ^ 2 * ((JHn B : ℚ) : ℝ)) / ((JMq B : ℚ) : ℝ) := by
    have e1 : H ((a + (a + z * y)) / 2) - (H a + H (a + z * y)) / 2 ≤
        y ^ 2 * (z ^ 2 * ((JHn B : ℚ) : ℝ)) := by
      have e : (z * y) ^ 2 * ((JHn B : ℚ) : ℝ) = y ^ 2 * (z ^ 2 * ((JHn B : ℚ) : ℝ)) := by ring
      linarith
    have hnum0 : 0 ≤ y ^ 2 * (z ^ 2 * ((JHn B : ℚ) : ℝ)) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hn0)
    exact (div_le_div_of_nonneg_right e1 hJpos.le).trans (div_le_div_of_nonneg_left hnum0 hJM0 hJM)
  have k := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left bn (by norm_num : (0 : ℝ) ≤ 2)) hsl0
  have e : ((slopeHi w.q : ℚ) : ℝ) * (2 * (y ^ 2 * (z ^ 2 * ((JHn B : ℚ) : ℝ)) /
      ((JMq B : ℚ) : ℝ))) = y ^ 2 * (z ^ 2 * ((T3n B w.q : ℚ) : ℝ)) := by
    unfold T3n; push_cast; ring
  linarith

/-- log-form outer penalty -/
theorem ptT4log (P : PtBox B a z y) (hH : okH B = true) (hC : okC B = true) (hR : okRho B = true)
    {w : RWit} (hQ : okQ B w = true) (hK : okK B = true) :
    (radialSlope (entropyInverse ((H a + H (a + z * y)) / 2)) -
        radialSlope (radialContact (1 - 2 * (a + y)) (H (a + z * y)))) * (a + y - (a + z * y)) ≤
      y ^ 2 * ((1 - z) * (2 * ((kappaQ B : ℚ) : ℝ) * ((K4a B w.q : ℚ) : ℝ) * (1 - z) +
        z * (((K4a B w.q : ℚ) : ℝ) / 2 + ((E4 B w.q : ℚ) : ℝ)))) := by
  obtain ⟨hq0, hq, hqs⟩ := P.q_le hH hR hQ
  obtain ⟨-, j2, j3⟩ := P.cfg.jensen
  obtain ⟨t1, t2⟩ := P.cfg.contact
  obtain ⟨hκ, hκ0⟩ := P.kappa hC
  obtain ⟨hn', hn0⟩ := P.JH_n hH hR
  obtain ⟨hJM0, hJM⟩ := P.JM hH
  have hJH0 := P.JH_nonneg
  have hH' := hH
  simp only [okH, Bool.and_eq_true, decide_eq_true_eq] at hH'
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hMLo⟩, -⟩ := hH'
  have hMLoR : (0 : ℝ) < ((MLo B : ℚ) : ℝ) := by exact_mod_cast hMLo
  have hC' := hC
  simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at hC'
  obtain ⟨⟨⟨⟨hcpt, -⟩, hkap⟩, -⟩, -⟩ := hC'
  have hkapR : (0 : ℝ) < ((kapLoQ (cHi B) : ℚ) : ℝ) := by exact_mod_cast hkap
  have hqs' := hqs
  simp only [slopeHiOk, Bool.and_eq_true, decide_eq_true_eq] at hqs'
  obtain ⟨⟨hqpt, -⟩, -⟩ := hqs'
  simp only [okK, decide_eq_true_eq] at hK
  have hsR : (1 - 2 * ((cHi B : ℚ) : ℝ)) ^ 2 ≤ ((kapLoQ (cHi B) : ℚ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hK
    push_cast at this
    linarith
  have hcHi := P.hcHi
  have hcle := P.c_le
  have hMlo := P.M_lo
  -- names
  set q := entropyInverse ((H a + H (a + z * y)) / 2) with hq_def
  set tC := radialContact (1 - 2 * (a + y)) (H (a + z * y)) with htC_def
  have hzy := P.hzy
  have hMpos : 0 < (a + (a + z * y)) / 2 := by linarith [P.ha]
  have hMb : (a + (a + z * y)) / 2 < a + z * y := by linarith
  have hqpos : 0 < q := hq0.trans_le hq
  have htpos : 0 < tC := by linarith
  have htC_lt : tC < ((cHi B : ℚ) : ℝ) := lt_of_lt_of_le t2 hcle
  have hqt : q ≤ tC := by linarith
  -- K bound on [q, tC]
  have hKb : ∀ v ∈ Icc q tC, v * dUps v ≤ ((Kq B w.q : ℚ) : ℝ) := by
    intro v hv
    rw [Kq_cast]
    exact r3q_wdUps hq0 (hq.trans hv.1) (hv.2.trans htC_lt.le) hcHi hkapR (kap_bounds hcpt).1 hsR
      (hn_bounds hqpt).2 LqLo_pos LqLo_le'
  have hlog := r3q_ups_log hqpos hqt (by linarith) hKb
  have hK0 : 0 ≤ ((Kq B w.q : ℚ) : ℝ) := by
    have h0 := hKb q ⟨le_rfl, hqt⟩
    have hd : 0 ≤ q * dUps q := by
      have hq2 : q < 1 / 2 := by linarith
      unfold dUps
      have h1 := hn_pos' hqpos (by linarith)
      have h2 := kap_sq_gap_pos hqpos hq2
      have h3 := kap_pos hqpos hq2
      have h4 := log2_pos
      have h5 : 0 < 1 - q := by linarith
      positivity
    linarith
  -- log increments
  have l1 : Real.log tC - Real.log ((a + (a + z * y)) / 2) ≤
      (tC - (a + (a + z * y)) / 2) / ((a + (a + z * y)) / 2) := by
    have h := Real.log_le_sub_one_of_pos (div_pos htpos hMpos)
    rw [Real.log_div htpos.ne' hMpos.ne'] at h
    have e : tC / ((a + (a + z * y)) / 2) - 1 =
        (tC - (a + (a + z * y)) / 2) / ((a + (a + z * y)) / 2) := by
      rw [sub_div, div_self hMpos.ne']
    linarith
  have l2 : Real.log ((a + (a + z * y)) / 2) - Real.log q ≤ ((a + (a + z * y)) / 2 - q) / q := by
    have h := Real.log_le_sub_one_of_pos (div_pos hMpos hqpos)
    rw [Real.log_div hMpos.ne' hqpos.ne'] at h
    have e : (a + (a + z * y)) / 2 / q - 1 = ((a + (a + z * y)) / 2 - q) / q := by
      rw [sub_div, div_self hqpos.ne']
    linarith
  have l1' : (tC - (a + (a + z * y)) / 2) / ((a + (a + z * y)) / 2) ≤
      (tC - (a + (a + z * y)) / 2) / ((MLo B : ℚ) : ℝ) :=
    div_le_div_of_nonneg_left (by linarith) hMLoR hMlo
  have l2' : ((a + (a + z * y)) / 2 - q) / q ≤ ((a + (a + z * y)) / 2 - q) / (w.q : ℝ) :=
    div_le_div_of_nonneg_left (by linarith) hq0 hq
  -- contact step and Jensen gap
  have hstep := contact_step P.cfg.hb0 P.cfg.hbc P.cfg.hc
  have ecb : a + y - (a + z * y) = (1 - z) * y := by ring
  have hcb0 : 0 ≤ (1 - z) * y := mul_nonneg (by linarith [P.hz1]) P.hy.le
  have htM : tC - (a + (a + z * y)) / 2 ≤
      2 * ((1 - z) * y) * ((kappaQ B : ℚ) : ℝ) + z * y / 2 := by
    have k1 : 2 * (a + y - (a + z * y)) * (H (a + y) / ((1 - 2 * (a + y)) * J (a + y) +
        2 * H (a + z * y))) ≤ 2 * (a + y - (a + z * y)) * ((kappaQ B : ℚ) : ℝ) :=
      mul_le_mul_of_nonneg_left hκ (by rw [ecb]; linarith)
    rw [ecb] at k1
    linarith
  have hMq : (a + (a + z * y)) / 2 - q ≤ (z * y) ^ 2 * ((JHn B : ℚ) : ℝ) / ((JMq B : ℚ) : ℝ) := by
    have hJpos : 0 < J ((a + (a + z * y)) / 2) := hJM0.trans_le hJM
    have hnum0 : 0 ≤ (z * y) ^ 2 * ((JHn B : ℚ) : ℝ) := mul_nonneg (sq_nonneg _) hn0
    have k := (div_le_div_of_nonneg_right hn' hJpos.le).trans
      (div_le_div_of_nonneg_left hnum0 hJM0 hJM)
    linarith
  -- assemble the increment bound
  set Kr := ((Kq B w.q : ℚ) : ℝ) with hKr
  set Mlo := ((MLo B : ℚ) : ℝ) with hMloD
  set qw := (w.q : ℝ) with hqwD
  set κr := ((kappaQ B : ℚ) : ℝ) with hκr
  set Jn := ((JHn B : ℚ) : ℝ) with hJn
  set Jm := ((JMq B : ℚ) : ℝ) with hJm
  have hX1 : (tC - (a + (a + z * y)) / 2) / Mlo ≤ (2 * ((1 - z) * y) * κr + z * y / 2) / Mlo :=
    div_le_div_of_nonneg_right htM hMLoR.le
  have hX2 : ((a + (a + z * y)) / 2 - q) / qw ≤ (z * y) ^ 2 * Jn / Jm / qw :=
    div_le_div_of_nonneg_right hMq hq0.le
  have hinc : radialSlope q - radialSlope tC ≤
      Kr * ((2 * ((1 - z) * y) * κr + z * y / 2) / Mlo + (z * y) ^ 2 * Jn / Jm / qw) := by
    have hsum : Real.log tC - Real.log q ≤
        (2 * ((1 - z) * y) * κr + z * y / 2) / Mlo + (z * y) ^ 2 * Jn / Jm / qw := by
      linarith
    exact hlog.trans (mul_le_mul_of_nonneg_left hsum hK0)
  have hmul := mul_le_mul_of_nonneg_right hinc hcb0
  rw [ecb]
  -- the E4 step: z y ≤ b1 c1
  have hzyb : z * y ≤ ((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ) := P.zy_hi
  have hfac0 : 0 ≤ Kr * (1 - z) * y * (z * y) * Jn / Jm / qw := by
    have h1 : 0 ≤ Kr * (1 - z) * y * (z * y) * Jn := by
      have := mul_nonneg (mul_nonneg (mul_nonneg hK0 (by linarith [P.hz1] : (0 : ℝ) ≤ 1 - z))
        P.hy.le) hzy.le
      exact mul_nonneg this hn0
    exact div_nonneg (div_nonneg h1 hJM0.le) hq0.le
  have hE : Kr * (1 - z) * y * (z * y) * Jn / Jm / qw * (z * y) ≤
      Kr * (1 - z) * y * (z * y) * Jn / Jm / qw * (((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hzyb hfac0
  have eK4 : ((K4a B w.q : ℚ) : ℝ) = Kr / Mlo := by unfold K4a; push_cast; ring
  have eE4 : ((E4 B w.q : ℚ) : ℝ) = Kr * (((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ) * Jn) / (Jm * qw) := by
    unfold E4; push_cast; ring
  rw [eK4, eE4]
  have e1 : Kr * ((2 * ((1 - z) * y) * κr + z * y / 2) / Mlo + (z * y) ^ 2 * Jn / Jm / qw) *
      ((1 - z) * y) = y ^ 2 * ((1 - z) * (2 * κr * (Kr / Mlo) * (1 - z) + z * ((Kr / Mlo) / 2))) +
      Kr * (1 - z) * y * (z * y) * Jn / Jm / qw * (z * y) := by
    field_simp
  have e2 : Kr * (1 - z) * y * (z * y) * Jn / Jm / qw * (((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ)) =
      y ^ 2 * ((1 - z) * (z * (Kr * (((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ) * Jn) / (Jm * qw)))) := by
    field_simp
  have e3 : y ^ 2 * ((1 - z) * (2 * κr * (Kr / Mlo) * (1 - z) +
      z * (Kr / Mlo / 2 + Kr * (((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ) * Jn) / (Jm * qw)))) =
      y ^ 2 * ((1 - z) * (2 * κr * (Kr / Mlo) * (1 - z) + z * ((Kr / Mlo) / 2))) +
      y ^ 2 * ((1 - z) * (z * (Kr * (((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ) * Jn) / (Jm * qw)))) := by
    ring
  rw [e3]
  linarith [hmul, hE, e1, e2]

/-- the sharpened bound case: `gapLB ≥ y² · P(z) > 0` -/
theorem ptBound2 (P : PtBox B a z y) {w : RWit} (hb : bound2OK B w = true) :
    0 < gapLB (H a) (H (a + z * y)) (a + y) := by
  simp only [bound2OK, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨⟨hH, hC⟩, hT⟩, hQ⟩, hR⟩, hK⟩, hqp⟩ := hb
  obtain ⟨hX, h12⟩ := ptT12z P hH hC hT
  have h3 := ptT3z P hH hR hQ
  have h4 := ptT4log P hH hC hR hQ hK
  have hG := P.cfg.gapLB_ge hX h3 h4
  have hP := CKLaneN1.Edge.qposOK_sound hqp P.z0 P.z1
  rw [P_cast] at hP
  have hy2 : 0 < y ^ 2 := pow_pos P.hy 2
  have k := mul_pos hy2 hP
  nlinarith [k, h12, hG]

end pt

/-- **Soundness of `leafOK2`.** -/
theorem leafOK2_sound {B : B3} {w : RWit} (h : leafOK2 B w = true) : Sem B := by
  intro a z y hm hz0 hz1 hy hA hret htc
  simp only [leafOK2, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (hr | ht) | ⟨hg, hv | hb⟩
  · exact leafOK_sound (w := w) (by simp [leafOK, hr]) a z y hm hz0 hz1 hy hA hret htc
  · exact leafOK_sound (w := w) (by simp [leafOK, ht]) a z y hm hz0 hz1 hy hA hret htc
  · exfalso
    have P := PtBox.of_geom hg hm hz0 hz1 hy
    simp only [vacOK, decide_eq_true_eq] at hv
    have hvR : ((Ha1 B : ℚ) : ℝ) + ((Hb1 B : ℚ) : ℝ) < 20 * ((B.c0 : ℚ) : ℝ) := by
      exact_mod_cast hv
    linarith [P.Ha_hi, P.Hb_hi, P.y0]
  · exact (ptBound2 (PtBox.of_geom hg hm hz0 hz1 hy) hb).le

/-- either leaf predicate -/
def leafAny (B : B3) (w : RWit) : Bool := leafOK B w || leafOK2 B w

theorem leafAny_sound {B : B3} {w : RWit} (h : leafAny B w = true) : Sem B := by
  simp only [leafAny, Bool.or_eq_true] at h
  rcases h with h | h
  · exact leafOK_sound h
  · exact leafOK2_sound h

/-- a partition tree of `R` whose leaves all pass `leafAny` proves `Sem R` -/
theorem sem_of_treeAny (R : B3) (T : PT RWit)
    (h : T.allLeaves (fun p w => leafAny (R.ofPath p) w) = true) : Sem R := by
  intro a z y hm
  obtain ⟨q, hq, hmq⟩ := PT.cover R T hm
  exact leafAny_sound (PT.allLeaves_sound h q hq) a z y hmq

end CKLaneN1.R3

end


