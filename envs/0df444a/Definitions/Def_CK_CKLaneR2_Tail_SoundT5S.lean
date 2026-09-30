-- Prove2me | Definitions.Def_CK_CKLaneR2_Tail_SoundT5S
-- name    : CK_CKLaneR2_Tail_SoundT5S
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:54:06.74611+00:00
-- url     : https://prove2.me/theorems/6f15db62-3ca6-4c51-a501-9b995266a90e
-- title:
--   Courtade–Kumar proof module `CKLaneR2.Tail.SoundT5S` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneR2.Tail.SoundT5S` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneR2.Tail.SoundT5S` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneR2.Tail.SoundT5S (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneR2/Tail/SoundT5S.lean)

import Definitions.Def_CK_CKLaneR2_Tail_SoundT5Final

-- ===== source module CKLaneR2.Tail.SoundT5S =====
section

/-!
# Lane R2 — tail checker soundness, part 7b: mode S (universal bound for the fifth block)
-/

namespace CKLaneR2.Tail

open CKLaneR2.TM3 CKLaneR2.Cell GeneralCK

noncomputable def rawT5S (t u b s3 lam cq gg : ℝ) : ℝ :=
  let omega := (1 - lam * cq) * (lam * gg + 1)⁻¹
  let TU := t * u
  let aa := ((2 : ℤ) : ℝ) * ((TU * u) * (b - u)⁻¹)
  let bb := ((4 : ℤ) : ℝ) * (TU * omega)
  let cc := s3 * (omega * omega)
  let UB1 := ((4 : ℤ) : ℝ) * (((aa + bb) + cc) * (1 / Real.log 2))
  let UB2 := (((2 : ℤ) : ℝ) * (s3 * lam)) * (1 / Real.log 2 * (1 - u)⁻¹)
  show ℝ from -((UB1 + UB2) / 2)

section Bounds

variable {L u v a c1 av cv s3 t b : ℝ}

set_option maxHeartbeats 2000000 in
theorem QA_le (hL : 0 < L) (hv : 0 < v) (hv1 : v < 1 / 2) (hs3 : 0 < s3)
    (hH : 0 < u * a + (1 - u) * c1) (hh : 0 < v * av + (1 - v) * cv) (hk : 0 < av + cv)
    (hkd : (1 - 2 * v) ^ 2 ≤ av + cv) (hRv : v * av + (1 - v) * cv ≤ 2 * v * (1 - v) * (av + cv))
    (hcontact : s3 * (v * av + (1 - v) * cv) = (1 - 2 * v) * (u * a + (1 - u) * c1)) :
    QA L u v a c1 av cv s3 t ≤ 4 * ((2 * (t * u) + s3 * (u * (a - c1) / (u * a + (1 - u) * c1))) ^ 2 / s3) / L := by
  set q := 2 * (t * u) + s3 * (u * (a - c1) / (u * a + (1 - u) * c1)) with hq
  set h := v * av + (1 - v) * cv with hhdef
  set k := av + cv with hkdef
  set HuL := u * a + (1 - u) * c1 with hHuLdef
  have h12 : 0 < 1 - 2 * v := by linarith
  have hv1' : 0 < 1 - v := by linarith
  have hHuL' : HuL = s3 * h / (1 - 2 * v) := by rw [eq_div_iff h12.ne']; linarith
  have hD : 0 < v ^ 2 * (1 - v) ^ 2 * k ^ 3 := by positivity
  have e : QA L u v a c1 av cv s3 t = q ^ 2 * (h ^ 2 * ((1 - 2 * v) * (k - (1 - 2 * v) ^ 2))) / (L * s3 * (v ^ 2 * (1 - v) ^ 2 * k ^ 3)) := by
    unfold QA
    rw [← hq, ← hhdef, ← hkdef, ← hHuLdef, hHuL']
    field_simp
    try ring
  have hW : h ^ 2 * ((1 - 2 * v) * (k - (1 - 2 * v) ^ 2)) ≤ 4 * (v ^ 2 * (1 - v) ^ 2 * k ^ 3) := by
    have h2 : h ^ 2 ≤ (2 * v * (1 - v) * k) ^ 2 := pow_le_pow_left₀ hh.le hRv 2
    have h3 : (1 - 2 * v) * (k - (1 - 2 * v) ^ 2) ≤ k := by nlinarith
    have h4 : 0 ≤ (1 - 2 * v) * (k - (1 - 2 * v) ^ 2) := mul_nonneg h12.le (by linarith)
    calc h ^ 2 * ((1 - 2 * v) * (k - (1 - 2 * v) ^ 2)) ≤ (2 * v * (1 - v) * k) ^ 2 * k :=
          mul_le_mul h2 h3 h4 (by positivity)
      _ = 4 * (v ^ 2 * (1 - v) ^ 2 * k ^ 3) := by ring
  rw [e]
  calc q ^ 2 * (h ^ 2 * ((1 - 2 * v) * (k - (1 - 2 * v) ^ 2))) / (L * s3 * (v ^ 2 * (1 - v) ^ 2 * k ^ 3))
      ≤ q ^ 2 * (4 * (v ^ 2 * (1 - v) ^ 2 * k ^ 3)) / (L * s3 * (v ^ 2 * (1 - v) ^ 2 * k ^ 3)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hW (sq_nonneg q)
    _ = 4 * (q ^ 2 / s3) / L := by field_simp

set_option maxHeartbeats 2000000 in
theorem QB_le (hL : 0 < L) (hu : 0 < u) (hu1 : u < 1) (hv : 0 < v) (hv1 : v < 1 / 2) (hs3 : 0 < s3)
    (ha : 0 < a) (hc1 : 0 ≤ c1) (hh : 0 < v * av + (1 - v) * cv) (hk : 0 < av + cv)
    (hRv : v * av + (1 - v) * cv ≤ 2 * v * (1 - v) * (av + cv)) :
    QB L u v a c1 av cv s3 ≤ 2 * s3 * a⁻¹ / (L * (1 - u)) := by
  unfold QB
  set h := v * av + (1 - v) * cv with hhdef
  set k := av + cv with hkdef
  have hv1' : 0 < 1 - v := by linarith
  have hu1' : 0 < 1 - u := by linarith
  have h12 : 0 ≤ 1 - 2 * v := by linarith
  have hHuL : 0 < u * a + (1 - u) * c1 := by nlinarith
  -- QB = s3 (1-2v) h u / (v k L (1-u)(1-v) HuL) ≤ 2 s3 u/(L (1-u) HuL) ≤ 2 s3/(a L (1-u))
  have step1 : s3 * (1 - 2 * v) * h * u / (2 * v * (k / 2) * L * (1 - u) * (1 - v) * (u * a + (1 - u) * c1))
      ≤ 2 * s3 * u / (L * (1 - u) * (u * a + (1 - u) * c1)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hRv' : h ≤ 2 * v * (1 - v) * k := hRv
    have hpos : 0 ≤ s3 * u * (L * (1 - u) * (u * a + (1 - u) * c1)) := by positivity
    have key : (1 - 2 * v) * h ≤ 2 * v * (1 - v) * k := by nlinarith [hRv', h12, hh]
    calc s3 * (1 - 2 * v) * h * u * (L * (1 - u) * (u * a + (1 - u) * c1))
        = (s3 * u * (L * (1 - u) * (u * a + (1 - u) * c1))) * ((1 - 2 * v) * h) := by ring
      _ ≤ (s3 * u * (L * (1 - u) * (u * a + (1 - u) * c1))) * (2 * v * (1 - v) * k) :=
          mul_le_mul_of_nonneg_left key hpos
      _ = 2 * s3 * u * (2 * v * (k / 2) * L * (1 - u) * (1 - v) * (u * a + (1 - u) * c1)) := by ring
  have step2 : 2 * s3 * u / (L * (1 - u) * (u * a + (1 - u) * c1)) ≤ 2 * s3 * a⁻¹ / (L * (1 - u)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hua : u * a ≤ u * a + (1 - u) * c1 := by nlinarith
    have hinv : a⁻¹ * a = 1 := inv_mul_cancel₀ ha.ne'
    have : u ≤ a⁻¹ * (u * a + (1 - u) * c1) := by
      calc u = a⁻¹ * (u * a) := by field_simp
        _ ≤ a⁻¹ * (u * a + (1 - u) * c1) := mul_le_mul_of_nonneg_left hua (inv_nonneg.mpr ha.le)
    have hp : 0 ≤ 2 * s3 * (L * (1 - u)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hp]
  exact step1.trans step2

theorem q2_le (hs3 : 0 < s3) (hd : 0 < b - u) (ht : 0 ≤ t) (h2td : 2 * t * (b - u) ≤ s3) (ω : ℝ) :
    (2 * (t * u) + s3 * ω) ^ 2 / s3 ≤ 2 * ((t * u * u) * (b - u)⁻¹) + 4 * (t * u * ω) + s3 * (ω * ω) := by
  rw [div_le_iff₀ hs3]
  have key : 4 * t ^ 2 * u ^ 2 ≤ 2 * ((t * u * u) * (b - u)⁻¹) * s3 := by
    have e : 2 * ((t * u * u) * (b - u)⁻¹) * s3 = 2 * t * u ^ 2 * (s3 / (b - u)) := by field_simp
    rw [e]
    have h1 : 2 * t ≤ s3 / (b - u) := by rw [le_div_iff₀ hd]; linarith
    have h2 : 0 ≤ 2 * t * u ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg ht (sq_nonneg u))]
  nlinarith [key]

end Bounds

end CKLaneR2.Tail

end


