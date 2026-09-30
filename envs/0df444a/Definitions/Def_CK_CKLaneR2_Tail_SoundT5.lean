-- Prove2me | Definitions.Def_CK_CKLaneR2_Tail_SoundT5
-- name    : CK_CKLaneR2_Tail_SoundT5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:34:20.797949+00:00
-- url     : https://prove2.me/theorems/d8f0f991-3b15-417e-891a-0f97f3b17ed8
-- title:
--   Courtade–Kumar proof module `CKLaneR2.Tail.SoundT5` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneR2.Tail.SoundT5` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneR2.Tail.SoundT5` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneR2.Tail.SoundT5 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneR2/Tail/SoundT5.lean)

import Definitions.Def_CK_CKLaneR2_Tail_SoundG1

-- ===== source module CKLaneR2.Tail.SoundT5 =====
section

/-!
# Lane R2 — tail checker soundness, part 3: the fifth raySec block in the ρ = v/u representation

* `residR_eq`: the implicit residual equals `(ln2 · Λ/u) · (s3 H(uρ) - (1-2uρ) H(u))`.
* `t5_bracket`: residual signs at `ρm ≤ ρp` ⇒ `u ρm ≤ radialContact (s3/H u) 1 ≤ u ρp`.
* `t5_algebra_A`, `t5_algebra_B`: the closed-form identities (atoms: logs as free variables, contact equation).
-/

namespace CKLaneR2.Tail

open CKLaneR2.TM3 CKLaneR2.Cell GeneralCK

theorem log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- `ln2 · H x = x (ln(1/x) + g1 x)` for `0 < x < 1`. -/
theorem H_g1 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : Real.log 2 * H x = x * (-Real.log x + g1 x) := by
  unfold H g1
  rw [if_neg h0.ne', Real.binEntropy, Real.log_inv, Real.log_inv]
  have hL := log2_pos.ne'
  field_simp
  try ring

theorem H_logs {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    H x = (x * (-Real.log x) + (1 - x) * (-Real.log (1 - x))) / Real.log 2 := by
  unfold H
  rw [Real.binEntropy, Real.log_inv, Real.log_inv]

/-! ## The implicit residual -/

/-- Raw residual (mirror of `t5Resid`). -/
noncomputable def residR (s3 u lam gg rho : ℝ) : ℝ :=
  s3 * rho * ((lam * g1 (u * rho) - lam * Real.log rho) + 1) - (-2 * (u * rho) + 1) * (lam * gg + 1)

theorem residR_eq {s3 u lam rho : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hlam : lam * (-Real.log u) = 1)
    (hr0 : 0 < rho) (hr1 : u * rho < 1) :
    residR s3 u lam (g1 u) rho = (Real.log 2 * lam / u) * (s3 * H (u * rho) - (1 - 2 * (u * rho)) * H u) := by
  have hv0 : 0 < u * rho := mul_pos hu0 hr0
  have h1 := H_g1 hv0 hr1
  have h2 := H_g1 hu0 hu1
  have hlr : Real.log rho = Real.log (u * rho) - Real.log u := by
    rw [Real.log_mul hu0.ne' hr0.ne']; ring
  unfold residR
  rw [hlr]
  have hL := log2_pos
  have e1 : Real.log 2 * lam / u * (s3 * H (u * rho) - (1 - 2 * (u * rho)) * H u)
      = lam / u * (s3 * (Real.log 2 * H (u * rho)) - (1 - 2 * (u * rho)) * (Real.log 2 * H u)) := by
    field_simp
  rw [e1, h1, h2]
  field_simp
  have hlam' : lam * Real.log u = -1 := by linarith
  linear_combination (s3 * rho + 2 * rho * u - 1) * hlam'

/-- Residual signs certify the contact bracket. -/
theorem t5_bracket {s3 u lam rm rp : ℝ} (hs3 : 0 < s3) (hu0 : 0 < u) (hu1 : u < 1 / 2)
    (hlam : lam * (-Real.log u) = 1) (hrm : 0 < rm) (hmp : rm ≤ rp) (hp1 : u * rp < 1)
    (hRm : residR s3 u lam (g1 u) rm < 0) (hRp : 0 < residR s3 u lam (g1 u) rp) :
    u * rm ≤ radialContact (s3 / H u) 1 ∧ radialContact (s3 / H u) 1 ≤ u * rp := by
  have hrp : 0 < rp := lt_of_lt_of_le hrm hmp
  have hm1 : u * rm < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hmp hu0.le) hp1
  have hHu : 0 < H u := H_pos hu0 (by linarith)
  have hlog : 0 < -Real.log u := by
    have := Real.log_neg hu0 (by linarith : u < 1); linarith
  have hlam0 : 0 < lam := by
    by_contra h; push_neg at h; nlinarith
  have hk : 0 < Real.log 2 * lam / u := div_pos (mul_pos log2_pos hlam0) hu0
  have hz : 0 < s3 / H u := div_pos hs3 hHu
  rw [residR_eq hu0 (by linarith) hlam hrm hm1] at hRm
  rw [residR_eq hu0 (by linarith) hlam hrp hp1] at hRp
  have hm : s3 * H (u * rm) - (1 - 2 * (u * rm)) * H u < 0 := by
    by_contra h; push_neg at h; nlinarith
  have hp : 0 < s3 * H (u * rp) - (1 - 2 * (u * rp)) * H u := by
    by_contra h; push_neg at h; nlinarith
  have hzm : s3 / H u * H (u * rm) < 1 * (1 - 2 * (u * rm)) := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hHu]; linarith
  have hzp : 1 * (1 - 2 * (u * rp)) < s3 / H u * H (u * rp) := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hHu]; linarith
  constructor
  · have hvm0 : 0 ≤ u * rm := (mul_pos hu0 hrm).le
    by_cases hh : u * rm ≤ 1 / 2
    · exact (le_radialContact_iff hz one_pos hvm0 hh).2 hzm.le
    · push_neg at hh
      exfalso
      have hH0 : 0 ≤ H (u * rm) := H_nonneg hvm0 (by linarith)
      have : 0 ≤ s3 / H u * H (u * rm) := mul_nonneg hz.le hH0
      linarith
  · have hvp0 : 0 ≤ u * rp := (mul_pos hu0 hrp).le
    by_cases hh : u * rp ≤ 1 / 2
    · exact (radialContact_le_iff hz one_pos hvp0 hh).2 hzp.le
    · push_neg at hh
      have := radialContact_lt_half hz one_pos
      linarith

/-! ## The closed-form identities (atoms) -/

section Atoms

variable {L u v a c1 av cv s3 t : ℝ}

/-- `u (2t + z J u) = 2tu + s3 ω` with `ω = u(a - c1)/(ua + (1-u)c1)`. -/
theorem t5_q (hL : 0 < L) (hHu : 0 < u * a + (1 - u) * c1) :
    u * (2 * t - s3 / ((u * a + (1 - u) * c1) / L) * (-((a - c1) / L)))
      = 2 * (t * u) + s3 * (u * (a - c1) / (u * a + (1 - u) * c1)) := by
  field_simp
  ring

/-- The contact equation gives `z cJ + 2 = (av + cv)/h`. -/
theorem t5_zcJ (hL : 0 < L) (hHu : 0 < u * a + (1 - u) * c1) (hHv : 0 < v * av + (1 - v) * cv)
    (hcontact : s3 * (v * av + (1 - v) * cv) = (1 - 2 * v) * (u * a + (1 - u) * c1)) :
    s3 / ((u * a + (1 - u) * c1) / L) * ((av - cv) / L) + 2 = (av + cv) / (v * av + (1 - v) * cv) := by
  have hs3 : s3 = (1 - 2 * v) * (u * a + (1 - u) * c1) / (v * av + (1 - v) * cv) := by
    field_simp; linarith
  rw [hs3]
  field_simp
  ring

/-- `(1/Hu) · F''(z)` in closed form. -/
theorem t5_F2 (hL : 0 < L) (hv : 0 < v) (hv1 : v < 1) (hHu : 0 < u * a + (1 - u) * c1)
    (hHv : 0 < v * av + (1 - v) * cv) (hk : 0 < av + cv)
    (hcontact : s3 * (v * av + (1 - v) * cv) = (1 - 2 * v) * (u * a + (1 - u) * c1)) :
    1 / ((u * a + (1 - u) * c1) / L) *
      (4 * ((v * av + (1 - v) * cv) * (v * av + (1 - v) * cv) * (2 * ((av + cv) / 2) - (1 - 2 * v) * (1 - 2 * v)) *
        ((4 * v * (1 - v))⁻¹ * (4 * v * (1 - v))⁻¹ * (((av + cv) / 2)⁻¹ * ((av + cv) / 2)⁻¹) *
          (s3 / ((u * a + (1 - u) * c1) / L) * ((av - cv) / L) + 2)⁻¹) * (1 / L * (1 / L))))
      = (v * av + (1 - v) * cv) ^ 3 * ((av + cv) - (1 - 2 * v) ^ 2)
        / (L * (u * a + (1 - u) * c1) * (v ^ 2 * (1 - v) ^ 2 * (av + cv) ^ 3)) := by
  rw [t5_zcJ hL hHu hHv hcontact]
  have hv1' : 0 < 1 - v := by linarith
  field_simp
  ring

/-- Part A: the quadratic-form term. -/
theorem t5_partA (hL : 0 < L) (hu : 0 < u) (hv : 0 < v) (hv1 : v < 1) (hHu : 0 < u * a + (1 - u) * c1)
    (hHv : 0 < v * av + (1 - v) * cv) (hk : 0 < av + cv)
    (hcontact : s3 * (v * av + (1 - v) * cv) = (1 - 2 * v) * (u * a + (1 - u) * c1)) :
    u ^ 2 * ((2 * t - s3 / ((u * a + (1 - u) * c1) / L) * (-((a - c1) / L)))
        * (2 * t - s3 / ((u * a + (1 - u) * c1) / L) * (-((a - c1) / L)))
        * (1 / ((u * a + (1 - u) * c1) / L))
        * (4 * ((v * av + (1 - v) * cv) * (v * av + (1 - v) * cv) * (2 * ((av + cv) / 2) - (1 - 2 * v) * (1 - 2 * v)) *
          ((4 * v * (1 - v))⁻¹ * (4 * v * (1 - v))⁻¹ * (((av + cv) / 2)⁻¹ * ((av + cv) / 2)⁻¹) *
            (s3 / ((u * a + (1 - u) * c1) / L) * ((av - cv) / L) + 2)⁻¹) * (1 / L * (1 / L)))))
      = (2 * (t * u) + s3 * (u * (a - c1) / (u * a + (1 - u) * c1))) ^ 2
        * ((v * av + (1 - v) * cv) ^ 3 * ((av + cv) - (1 - 2 * v) ^ 2)
          / (L * (u * a + (1 - u) * c1) * (v ^ 2 * (1 - v) ^ 2 * (av + cv) ^ 3))) := by
  rw [← t5_F2 hL hv hv1 hHu hHv hk hcontact, ← t5_q (t := t) (s3 := s3) hL hHu]
  ring

/-- Part B: the `dde` terms (no contact equation needed). -/
theorem t5_partB (hL : 0 < L) (hu : 0 < u) (hu1 : u < 1) (hv : 0 < v) (hv1 : v < 1)
    (hHu : 0 < u * a + (1 - u) * c1) (hk : 0 < av + cv) :
    u ^ 2 * (-(s3 / ((u * a + (1 - u) * c1) / L) * (-1 / (L * u * (1 - u)))
        * ((av - cv) / L + 2 * ((1 - 2 * v) * (v * av + (1 - v) * cv) * ((4 * v * (1 - v))⁻¹ * ((av + cv) / 2)⁻¹)
          * (1 / L))))
      + (-1 / (L * u * (1 - u))) * (s3 / ((u * a + (1 - u) * c1) / L) * ((av - cv) / L)))
      = s3 * (1 - 2 * v) * (v * av + (1 - v) * cv) * u
        / (2 * v * ((av + cv) / 2) * L * (1 - u) * (1 - v) * (u * a + (1 - u) * c1)) := by
  have hv1' : 0 < 1 - v := by linarith
  have hu1' : 0 < 1 - u := by linarith
  field_simp
  ring

end Atoms

end CKLaneR2.Tail

end


