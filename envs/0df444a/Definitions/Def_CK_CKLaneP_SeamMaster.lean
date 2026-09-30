-- Prove2me | Definitions.Def_CK_CKLaneP_SeamMaster
-- name    : CK_CKLaneP_SeamMaster
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:40:49.940987+00:00
-- url     : https://prove2.me/theorems/e74e7718-9cfd-4dd3-b2a3-0c33529ba0f3
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamMaster` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamMaster` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamMaster` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamMaster (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamMaster.lean)

import Definitions.Def_CK_CKLaneP_SeamBase
import Definitions.Def_CK_CKLaneP_SeamAux

-- ===== source module CKLaneP.SeamMaster =====
section
/-
Lane P — master inequalities for the seam field (real-number form).

`seam_master_A` (case A, `q ≤ S/2`, base point `y = 0`) and `seam_master_B` (case B, `q > S/2`,
base point `y_lo = 2q − S`) turn real-valued certificate data into `0 ≤ s(y*)` for a stationary
seam point `y*`:

    s(y*) ≥ DC + [∫ right fiber] + [bulk] − M (y* − y_lo)²/(2E) ≥ 0.

All data are hypotheses; the rational checkers discharge them.
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

/-- Case A master inequality (normalized by `β²`). -/
theorem seam_master_A {S p q ys DCn c1n c2 Bn M Y : ℝ}
    (hS0 : 0 < S) (hS : S ≤ 1 / 10000) (hp : 0 < p) (hpq : p < q) (hqS : q ≤ S / 2)
    (hys0 : 0 < ys) (hysS : ys < S - 2 * p)
    (hstat : seamD S (H p) (H q) ys = 0)
    (hDC : (q - p) ^ 2 * DCn ≤ canonicalPureGap p q (H p) (H q))
    (hR : ∀ t ∈ Ioo p q, c1n * (q - p) - c2 * (q - t) ≤ rightD q (H p) (H q) t)
    (hB : ∀ m ∈ Icc q (S / 2), (q - p) ^ 2 * Bn ≤ (S / 2 - q) * jdef (H p) (H q) m)
    (hM : ∀ t ∈ Ioo 0 ys, e8Theta (ys / (H p + H q)) - e8Theta (t / (H p + H q)) ≤
      M * ((ys - t) / (H p + H q)))
    (hM0 : 0 ≤ M) (hY : ys ≤ (q - p) * Y)
    (hcheck : 0 ≤ DCn + c1n - c2 / 2 + Bn - M * Y ^ 2 / (2 * (H p + H q))) :
    0 ≤ seamCurve S (H p) (H q) ys := by
  have hq12 : q < 1 / 2 := by linarith
  have hHp : 0 < H p := H_pos hp (by linarith)
  have hHpq : H p ≤ H q := H_strictMonoOn.monotoneOn ⟨hp.le, by linarith⟩ ⟨(hp.trans hpq).le, by linarith⟩ hpq.le
  have hHq : 0 < H q := lt_of_lt_of_le hHp hHpq
  have hE : 0 < H p + H q := by linarith
  set β := q - p with hβ
  have hβ0 : 0 < β := by rw [hβ]; linarith
  -- dip
  have hdip := seam_dip_M (S := S) (y0 := 0) hS0.le hHp hHq le_rfl hys0 (by linarith) hstat hM
  -- base: seamCurve 0 = emLine (S/2)
  rw [seamCurve_zero] at hdip
  -- bulk: emLine (S/2) ≥ emLine q + (S/2 - q) * ℓ with ℓ = β² Bn/(S/2 - q) (if S/2 > q)
  have hbulk : emLine (H p) (H q) q + β ^ 2 * Bn ≤ emLine (H p) (H q) (S / 2) := by
    rcases eq_or_lt_of_le hqS with heq | hlt
    · -- q = S/2: Bn term must be ≤ 0 by hB at m = q
      have h := hB q ⟨le_rfl, hqS⟩
      rw [heq, sub_self, zero_mul] at h
      rw [heq]
      linarith
    · have hpos : 0 < S / 2 - q := by linarith
      have hmvt := emLine_mvt (ℓ := β ^ 2 * Bn / (S / 2 - q)) hHp hHq hlt.le (by linarith)
        (fun t ht => by
          have h := hB t ht
          rw [div_le_iff₀ hpos]
          linarith)
      have e : β ^ 2 * Bn / (S / 2 - q) * (S / 2 - q) = β ^ 2 * Bn :=
        div_mul_cancel₀ _ hpos.ne'
      linarith
  -- right fiber from p to q (b = q)
  have hright : canonicalPureGap p q (H p) (H q) + c1n * β * (q - p) -
      c2 * ((q - p) ^ 2 - (q - q) ^ 2) / 2 ≤ canonicalPureGap q q (H p) (H q) := by
    apply rightFiber_affine hp le_rfl hpq.le le_rfl (by linarith)
    intro t ht
    have := hR t ht
    rw [hβ]; linarith
  have hem : emLine (H p) (H q) q = canonicalPureGap q q (H p) (H q) := rfl
  -- assemble
  have hY2 : ys ^ 2 ≤ (β * Y) ^ 2 := pow_le_pow_left₀ hys0.le hY 2
  have hdip2 : M * (ys - 0) ^ 2 / (2 * (H p + H q)) ≤ M * (β * Y) ^ 2 / (2 * (H p + H q)) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [sub_zero]
    exact mul_le_mul_of_nonneg_left hY2 hM0
  have hfin : 0 ≤ β ^ 2 * (DCn + c1n - c2 / 2 + Bn - M * Y ^ 2 / (2 * (H p + H q))) :=
    mul_nonneg (sq_nonneg _) hcheck
  have e1 : β ^ 2 * (DCn + c1n - c2 / 2 + Bn - M * Y ^ 2 / (2 * (H p + H q))) =
      β ^ 2 * DCn + c1n * β * β - c2 * (β ^ 2 - 0) / 2 + β ^ 2 * Bn -
        M * (β * Y) ^ 2 / (2 * (H p + H q)) := by ring
  rw [e1] at hfin
  have hsq : (q - q) ^ 2 = (0 : ℝ) := by ring
  rw [hsq, ← hβ] at hright
  linarith

/-- Case B master inequality (normalized by `β²`), base point `y_lo = 2q − S`. -/
theorem seam_master_B {S p q ys DCn c1n c2 M Y : ℝ}
    (hS0 : 0 < S) (hS : S ≤ 1 / 10000) (hp : 0 < p) (hpq : p < q) (hqS : S / 2 < q)
    (hpqS : p + q < S)
    (hys0 : 2 * q - S < ys) (hysS : ys < S - 2 * p)
    (hstat : seamD S (H p) (H q) ys = 0)
    (hDC : (q - p) ^ 2 * DCn ≤ canonicalPureGap p q (H p) (H q))
    (hR : ∀ t ∈ Ioo p (S - q), c1n * (q - p) - c2 * (q - t) ≤ rightD q (H p) (H q) t)
    (hM : ∀ t ∈ Ioo (2 * q - S) ys, e8Theta (ys / (H p + H q)) - e8Theta (t / (H p + H q)) ≤
      M * ((ys - t) / (H p + H q)))
    (hM0 : 0 ≤ M) (hY : ys - (2 * q - S) ≤ (q - p) * Y)
    (hcheck : 0 ≤ (q - p) ^ 2 * DCn + (c1n * (q - p) * (S - q - p) -
        c2 * ((q - p) ^ 2 - (2 * q - S) ^ 2) / 2) - M * ((q - p) * Y) ^ 2 / (2 * (H p + H q))) :
    0 ≤ seamCurve S (H p) (H q) ys := by
  have hq12 : q < 1 / 2 := by linarith
  have hHp : 0 < H p := H_pos hp (by linarith)
  have hHpq : H p ≤ H q := H_strictMonoOn.monotoneOn ⟨hp.le, by linarith⟩ ⟨(hp.trans hpq).le, by linarith⟩ hpq.le
  have hHq : 0 < H q := lt_of_lt_of_le hHp hHpq
  have hE : 0 < H p + H q := by linarith
  have hylo0 : 0 ≤ 2 * q - S := by linarith
  have hdip := seam_dip_M (S := S) hS0.le hHp hHq hylo0 hys0 (by linarith) hstat hM
  rw [seamCurve_ylo] at hdip
  -- right fiber from p to S - q
  have hright := rightFiber_affine (a := p) (b := q) (t1 := p) (t2 := S - q) (c1 := c1n * (q - p))
    (c2 := c2) hp le_rfl (by linarith) (by linarith) (by linarith) (fun t ht => hR t ht)
  have e2 : (q - (S - q)) = 2 * q - S := by ring
  rw [e2] at hright
  have hY2 : (ys - (2 * q - S)) ^ 2 ≤ ((q - p) * Y) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hY 2
  have hdip2 : M * (ys - (2 * q - S)) ^ 2 / (2 * (H p + H q)) ≤
      M * ((q - p) * Y) ^ 2 / (2 * (H p + H q)) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hY2 hM0
  linarith

end CKLaneP

end


