-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionHessianPSD
-- name    : CK_GeneralCK_CorrectionHessianPSD
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:39:48.920299+00:00
-- url     : https://prove2.me/theorems/e7d10ae5-63da-4142-b0ad-e8af20d96a80
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionHessianPSD` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionHessianPSD` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionHessianPSD` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionHessianPSD (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionHessianPSD.lean)

import Definitions.Def_CK_GeneralCK_CorrectionHessian
import Definitions.Def_GeneralCK_correction_minors

namespace GeneralCK.Correction








noncomputable def Mquadratic (e f a b : ℝ) : ℝ :=
  Mleft e f*a^2+2*Mcross e f*a*b+Mright e f*b^2
noncomputable def hessianQuadratic (e f a b : ℝ) : ℝ :=
  deriv (deriv (fun t => entropyCorrection t f)) e*a^2+
  2*deriv (fun t => deriv (fun x => entropyCorrection x t) e) f*a*b+
  deriv (deriv (entropyCorrection e)) f*b^2
noncomputable def entropyScale (e : ℝ) : ℝ := J (entropyInverse e)*q e

theorem entropyScale_pos {e : ℝ} (he : 0 < e) (he' : e < 1) :
    0 < entropyScale e := by
  have hv := entropyInverse_pos he he'.le
  have hv' := entropyInverse_lt_half he.le he'
  have hJ := J_pos hv hv'
  unfold entropyScale q
  have : 0 < 1-entropyInverse e := by linarith
  positivity

theorem quadratic_nonneg_of_minor {A B C x y : ℝ}
    (hA : 0 < A) (hd : 0 ≤ A*C-B^2) : 0 ≤ A*x^2+2*B*x*y+C*y^2 := by
  have hid : A*(A*x^2+2*B*x*y+C*y^2) = (A*x+B*y)^2+(A*C-B^2)*y^2 := by ring
  have hp : 0 ≤ A*(A*x^2+2*B*x*y+C*y^2) := by
    rw [hid]
    positivity
  exact nonneg_of_mul_nonneg_right hp hA

theorem quadratic_pos_of_minor {A B C x y : ℝ}
    (hA : 0 < A) (hd : 0 < A*C-B^2) (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < A*x^2+2*B*x*y+C*y^2 := by
  have hid : A*(A*x^2+2*B*x*y+C*y^2) = (A*x+B*y)^2+(A*C-B^2)*y^2 := by ring
  have hp : 0 < A*(A*x^2+2*B*x*y+C*y^2) := by
    rw [hid]
    by_cases hy : y = 0
    · have hx : x ≠ 0 := hxy.resolve_right (not_not_intro hy)
      simpa [hy] using sq_pos_of_ne_zero (mul_ne_zero hA.ne' hx)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hd (sq_pos_of_ne_zero hy))
  exact pos_of_mul_pos_right hp hA.le

theorem Mquadratic_nonneg {e f : ℝ} (hleft : 0 < Mleft e f) (hdet : 0 ≤ Mdet e f)
    (a b : ℝ) : 0 ≤ Mquadratic e f a b :=
  quadratic_nonneg_of_minor hleft hdet

theorem Mquadratic_pos {e f a b : ℝ} (hleft : 0 < Mleft e f)
    (hdet : 0 < Mdet e f) (hab : a ≠ 0 ∨ b ≠ 0) : 0 < Mquadratic e f a b :=
  quadratic_pos_of_minor hleft hdet hab

/-- Inverse diagonal congruence recovers the actual entropy-coordinate quadratic form. -/
theorem Mquadratic_unscale {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1)
    (a b : ℝ) : Mquadratic e f (a/entropyScale e) (b/entropyScale f) =
      2*Real.log 2*hessianQuadratic e f a b := by
  obtain ⟨hl, hc, hr⟩ := entropyCorrection_scaled_hessian he hef hf
  change _ = Mleft e f at hl
  change _ = Mcross e f at hc
  change _ = Mright e f at hr
  have hse := (entropyScale_pos he (hef.trans hf)).ne'
  have hsf := (entropyScale_pos (he.trans hef) hf).ne'
  unfold Mquadratic
  rw [← hl, ← hc, ← hr]
  change 2*Real.log 2*(entropyScale e)^2*_*_+2*(2*Real.log 2*entropyScale e*entropyScale f*_)*_*_+
    2*Real.log 2*(entropyScale f)^2*_*_ = _
  unfold hessianQuadratic
  field_simp [hse, hsf]

/-- Pointwise certificate criterion; no global sign hypothesis is hidden here. -/
theorem hessianQuadratic_nonneg {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1)
    (hleft : 0 < Mleft e f) (hdet : 0 ≤ Mdet e f) (a b : ℝ) :
    0 ≤ hessianQuadratic e f a b := by
  have hp := Mquadratic_nonneg hleft hdet (a/entropyScale e) (b/entropyScale f)
  rw [Mquadratic_unscale he hef hf] at hp
  exact nonneg_of_mul_nonneg_right hp (by positivity : 0 < 2*Real.log 2)

theorem hessianQuadratic_pos {e f a b : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1)
    (hleft : 0 < Mleft e f) (hdet : 0 < Mdet e f) (hab : a ≠ 0 ∨ b ≠ 0) :
    0 < hessianQuadratic e f a b := by
  have hse := (entropyScale_pos he (hef.trans hf)).ne'
  have hsf := (entropyScale_pos (he.trans hef) hf).ne'
  have hxy : a/entropyScale e ≠ 0 ∨ b/entropyScale f ≠ 0 :=
    hab.imp (fun ha => div_ne_zero ha hse) (fun hb => div_ne_zero hb hsf)
  have hp := Mquadratic_pos hleft hdet hxy
  rw [Mquadratic_unscale he hef hf] at hp
  exact pos_of_mul_pos_right hp (by positivity : 0 ≤ 2*Real.log 2)

end GeneralCK.Correction


