-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_R3Combine
-- name    : CK_CKLaneM07_CE_R3Combine
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:13:20.371649+00:00
-- url     : https://prove2.me/theorems/e4680459-03b2-499c-9791-72994d4fa77a
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.R3Combine` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.R3Combine` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.R3Combine` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.R3Combine (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/R3Combine.lean)

import Definitions.Def_CK_CKLaneM07_CE_R3Bound

-- ===== source module CKLaneM07.CE.R3Combine =====
section

/-!
# Lane M07 / CE-stat row 3: the pointwise box bound for `gapLB`

`gapLB (H a) (H b) c ≥ T1 + T2 − T3 − T4` with
* `T1 = Θ(X)/X · ((c−a)² − (b−a)²)/(4h)` for any `X ≥ (c−a)/(2h)`,
* `T2 = (b−a)²/((a+b) log 2)`,
* `T3 = Υ(q_lo) · 2 JH / J(M)`, `JH = H(M) − h`, `M = (a+b)/2`, any `0 < q_lo ≤ ι h`,
* `T4 = D (c−b) (2κ(c−b) + (b−a)/2 + JH/J(M))` for `D ≥ |Υ'|` on `[q_lo, c]`,
  `κ ≥ H(c)/((1−2c)J(c) + 2H(b))`,
  or `T4' = (Υ(q_lo) − Υ(t_hi)) (c − b)` for any `t_C ≤ t_hi < 1/2`.
-/

set_option autoImplicit false

namespace CKLaneM07.CE.R3

open GeneralCK GeneralCK.Certificates.Mixed Set CKLaneN1.Edge CKLaneM07.CE

theorem gapLB_eq {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1 / 2) :
    gapLB (H a) (H b) c =
      F (c - a) ((H a + H b) / 2) - F (b - a) ((H a + H b) / 2) + interiorCost a b +
        radialSlope (entropyInverse ((H a + H b) / 2)) *
          (2 * entropyInverse ((H a + H b) / 2) - a - c) +
        radialSlope (radialContact (1 - 2 * c) (H b)) * (c - b) := by
  unfold gapLB interiorCost
  rw [entropyInverse_H_lower ha.le (by linarith), entropyInverse_H_lower (ha.trans hab).le hb]

/-- common facts at a configuration -/
structure Cfg (a b c : ℝ) : Prop where
  ha : 0 < a
  hab : a < b
  hbc : b < c
  hc : c < 1 / 2

section cfg

variable {a b c : ℝ} (P : Cfg a b c)
include P

theorem Cfg.hb : b < 1 / 2 := by linarith [P.hbc, P.hc]
theorem Cfg.hb0 : 0 < b := P.ha.trans P.hab
theorem Cfg.hh : 0 < (H a + H b) / 2 := by
  have h1 := H_pos P.ha (by linarith [P.hb, P.hab])
  have h2 := H_pos P.hb0 (by linarith [P.hb])
  linarith
theorem Cfg.hM : 0 < (a + b) / 2 ∧ (a + b) / 2 < 1 / 2 := by
  constructor <;> linarith [P.ha, P.hab, P.hb]

/-- the Jensen facts for `q = ι h` -/
theorem Cfg.jensen :
    a ≤ entropyInverse ((H a + H b) / 2) ∧
    entropyInverse ((H a + H b) / 2) ≤ (a + b) / 2 ∧
    (a + b) / 2 - entropyInverse ((H a + H b) / 2) ≤
      (H ((a + b) / 2) - (H a + H b) / 2) / J ((a + b) / 2) := by
  obtain ⟨h1, h2, h3, -⟩ := q_facts P.ha P.hab.le P.hb
  have hJ := J_pos P.hM.1 P.hM.2
  refine ⟨h1, h2, ?_⟩
  rw [le_div_iff₀ hJ]
  linarith

theorem Cfg.contact :
    b < radialContact (1 - 2 * c) (H b) ∧ radialContact (1 - 2 * c) (H b) < c := by
  refine ⟨?_, contact_lt P.hb0 P.hbc P.hc⟩
  have hf := H_pos P.hb0 (by linarith [P.hb])
  have h := radialContact_strictAnti_radius (show (0 : ℝ) < 1 - 2 * c by linarith [P.hc])
    (show 1 - 2 * c < 1 - 2 * b by linarith [P.hbc]) hf
  rwa [cap_contact_H P.hb0 P.hb] at h

/-- the two first pieces -/
theorem Cfg.T12 {X : ℝ} (hX : (c - a) / (2 * ((H a + H b) / 2)) ≤ X) :
    e8Theta X / X * ((c - a) ^ 2 - (b - a) ^ 2) / (4 * ((H a + H b) / 2)) +
      (b - a) ^ 2 / ((a + b) * Real.log 2) ≤
    F (c - a) ((H a + H b) / 2) - F (b - a) ((H a + H b) / 2) + interiorCost a b := by
  have h1 := F_sub_ge_ratio P.hh (sub_pos.mpr P.hab) (by linarith [P.hbc]) hX
  have h2 := interiorCost_ge P.ha P.hab (by linarith [P.hb])
  linarith

/-- the Jensen penalty -/
theorem Cfg.T3 {qlo : ℝ} (hq0 : 0 < qlo) (hq : qlo ≤ entropyInverse ((H a + H b) / 2)) :
    radialSlope (entropyInverse ((H a + H b) / 2)) *
        (a + b - 2 * entropyInverse ((H a + H b) / 2)) ≤
      radialSlope qlo * (2 * ((H ((a + b) / 2) - (H a + H b) / 2) / J ((a + b) / 2))) := by
  obtain ⟨j1, j2, j3⟩ := P.jensen
  set q := entropyInverse ((H a + H b) / 2)
  have hq1 : q < 1 / 2 := lt_of_le_of_lt j2 P.hM.2
  have hU0 : 0 < radialSlope q := ups_pos (hq0.trans_le hq) hq1
  have hU1 : radialSlope q ≤ radialSlope qlo := ups_anti hq0 hq hq1
  have e : a + b - 2 * q = 2 * ((a + b) / 2 - q) := by ring
  rw [e]
  have hMq : 0 ≤ (a + b) / 2 - q := by linarith
  have := mul_le_mul hU1 (mul_le_mul_of_nonneg_left j3 (by norm_num : (0 : ℝ) ≤ 2))
    (by positivity) (hU0.le.trans hU1)
  linarith

/-- the outer tangent penalty, mean-value form -/
theorem Cfg.T4 {qlo D κ : ℝ} (hq0 : 0 < qlo) (hq : qlo ≤ entropyInverse ((H a + H b) / 2))
    (hD : ∀ w ∈ Icc qlo c, dUps w ≤ D)
    (hκ : H c / ((1 - 2 * c) * J c + 2 * H b) ≤ κ) :
    (radialSlope (entropyInverse ((H a + H b) / 2)) - radialSlope (radialContact (1 - 2 * c) (H b))) *
        (c - b) ≤
      D * (c - b) * (2 * κ * (c - b) + (b - a) / 2 +
        (H ((a + b) / 2) - (H a + H b) / 2) / J ((a + b) / 2)) := by
  obtain ⟨j1, j2, j3⟩ := P.jensen
  obtain ⟨t1, t2⟩ := P.contact
  set q := entropyInverse ((H a + H b) / 2)
  set tC := radialContact (1 - 2 * c) (H b)
  have hqt : q ≤ tC := by linarith [P.hab]
  have hq0' : 0 < q := hq0.trans_le hq
  have htC : tC < 1 / 2 := by linarith [P.hc]
  have hmv := ups_sub_le hq0' hqt htC (fun w hw => hD w ⟨hq.trans hw.1, hw.2.trans t2.le⟩)
  have hstep := contact_step P.hb0 P.hbc P.hc
  have hcb : 0 < c - b := by linarith [P.hbc]
  have hD0 : 0 ≤ D := by
    have hd := hD qlo ⟨le_rfl, by linarith [j1, P.hab, P.hbc]⟩
    have : 0 ≤ dUps qlo := by
      unfold dUps
      have hql : qlo < 1 / 2 := by linarith [hq.trans j2, P.hM.2]
      have := hn_pos' hq0 (by linarith)
      have := kap_sq_gap_pos hq0 hql
      have := kap_pos hq0 hql
      have := log2_pos
      have : 0 < 1 - qlo := by linarith
      positivity
    linarith
  have hK : 2 * (c - b) * (H c / ((1 - 2 * c) * J c + 2 * H b)) ≤ 2 * κ * (c - b) := by
    nlinarith
  have hdist : tC - q ≤ 2 * κ * (c - b) + (b - a) / 2 +
      (H ((a + b) / 2) - (H a + H b) / 2) / J ((a + b) / 2) := by
    linarith
  calc (radialSlope q - radialSlope tC) * (c - b) ≤ (D * (tC - q)) * (c - b) :=
        mul_le_mul_of_nonneg_right hmv hcb.le
    _ ≤ (D * (2 * κ * (c - b) + (b - a) / 2 +
          (H ((a + b) / 2) - (H a + H b) / 2) / J ((a + b) / 2))) * (c - b) := by
        apply mul_le_mul_of_nonneg_right _ hcb.le
        exact mul_le_mul_of_nonneg_left hdist hD0
    _ = _ := by ring

/-- the outer tangent penalty, direct form -/
theorem Cfg.T4' {qlo thi : ℝ} (hq0 : 0 < qlo) (hq : qlo ≤ entropyInverse ((H a + H b) / 2))
    (ht : radialContact (1 - 2 * c) (H b) ≤ thi) (hthi : thi < 1 / 2) :
    (radialSlope (entropyInverse ((H a + H b) / 2)) - radialSlope (radialContact (1 - 2 * c) (H b))) *
        (c - b) ≤ (radialSlope qlo - radialSlope thi) * (c - b) := by
  obtain ⟨j1, j2, -⟩ := P.jensen
  obtain ⟨t1, t2⟩ := P.contact
  have hq1 : entropyInverse ((H a + H b) / 2) < 1 / 2 := lt_of_le_of_lt j2 P.hM.2
  have hU1 := ups_anti hq0 hq hq1
  have htC0 : 0 < radialContact (1 - 2 * c) (H b) := P.hb0.trans t1
  have hU2 := ups_anti htC0 ht hthi
  have hcb : 0 ≤ c - b := by linarith [P.hbc]
  exact mul_le_mul_of_nonneg_right (by linarith) hcb

/-- the box bound (abstract penalties) -/
theorem Cfg.gapLB_ge {X U3 U4 : ℝ} (hX : (c - a) / (2 * ((H a + H b) / 2)) ≤ X)
    (h3 : radialSlope (entropyInverse ((H a + H b) / 2)) *
        (a + b - 2 * entropyInverse ((H a + H b) / 2)) ≤ U3)
    (h4 : (radialSlope (entropyInverse ((H a + H b) / 2)) -
        radialSlope (radialContact (1 - 2 * c) (H b))) * (c - b) ≤ U4) :
    e8Theta X / X * ((c - a) ^ 2 - (b - a) ^ 2) / (4 * ((H a + H b) / 2)) +
      (b - a) ^ 2 / ((a + b) * Real.log 2) - U3 - U4 ≤ gapLB (H a) (H b) c := by
  rw [gapLB_eq P.ha P.hab P.hb.le]
  have h12 := P.T12 hX
  have e : radialSlope (entropyInverse ((H a + H b) / 2)) *
        (2 * entropyInverse ((H a + H b) / 2) - a - c) +
      radialSlope (radialContact (1 - 2 * c) (H b)) * (c - b) =
      -(radialSlope (entropyInverse ((H a + H b) / 2)) *
        (a + b - 2 * entropyInverse ((H a + H b) / 2))) -
      (radialSlope (entropyInverse ((H a + H b) / 2)) -
        radialSlope (radialContact (1 - 2 * c) (H b))) * (c - b) := by ring
  linarith

end cfg

end CKLaneM07.CE.R3

end


