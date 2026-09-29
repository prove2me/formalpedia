-- Prove2me | Definitions.Def_CK_CKLaneA1_Identities
-- name    : CK_CKLaneA1_Identities
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:55:28.979277+00:00
-- url     : https://prove2.me/theorems/cebb69a9-6b26-4678-94bc-9d65bdeaa3fc
-- title:
--   Courtade–Kumar proof module `CKLaneA1.Identities` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.Identities` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.Identities` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.Identities (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/Identities.lean)

import Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerDetGapFactor
import Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerRegularContact

/-!
# CKLaneA1.Identities — algebraic identities for the scaled correction kernel

Lane A1 (correction arm `u < 1/50`).  Pure algebra: the scaled gap coefficient
`(1/J) * detGapCoefficient` and `m11` expressed in "atom" variables that the interval
checker encloses.  No numerical facts are assumed here.
-/

set_option autoImplicit false

namespace CKLaneA1

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU

/-- Scaled gap-coefficient formula in atoms (`t = 1/J`, `ku = q*J`, `hh = 1-2u`). -/
noncomputable def feTcoef (t qu ku Jw qw s S R W hh : ℝ) : ℝ :=
  let qj := (qu*Jw - ku)/s
  let tj := (t*Jw - 1)/s
  let A1 := qj + 2*qu*R - 1
  let U := t*A1 + s
  let tJV := 2*t*Jw + A1*t*tj - (hh - s)*(tj + 2*(t*R))
  let Z := hh - s - (ku + qw*Jw)/S
  let z := -qu - s*ku/S
  let m := qu + qw + s*U - W*(z*z)
  let tJw := t*Jw
  m*(tJV - tJw*W*(Z*Z)) - tJw*((U - W*z*Z)*(U - W*z*Z))

set_option maxHeartbeats 4000000 in
/-- Abstract algebraic form of the scaling identity. -/
theorem detGap_scaled (d q h J j R W S : ℝ) (hJ : J ≠ 0) (hJ' : J + d*j ≠ 0) (hS : S ≠ 0)
    (hd : d ≠ 0) :
    (1/J) * detGapCoefficient d q h J j R W S =
      feTcoef (1/J) q (q*J) (J + d*j) (q + h*d - d^2) d S R W h := by
  unfold detGapCoefficient feTcoef
  simp only []
  field_simp
  ring

/-- The scaled gap coefficient in natural atoms. -/
theorem tcoef_identity {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1/2) :
    (1 / jn u) * actualDetGapCoefficient u w =
      feTcoef (1 / jn u) (qp u) (qp u * jn u) (jn w) (qp w) (w - u) (entropySum u w)
        (regularFsGap u w) (regularWeight u w) (1 - 2*u) := by
  have huJ := natural_jn_nonzero hu (huw.trans hw)
  have hwJ := natural_jn_nonzero (hu.trans huw) hw
  have hS : entropySum u w ≠ 0 := by
    apply ne_of_gt
    unfold entropySum
    rw [Certificates.Mixed.hn_eq_H_mul_log, Certificates.Mixed.hn_eq_H_mul_log]
    exact add_pos (mul_pos (H_pos hu (by linarith)) log_two_pos)
      (mul_pos (H_pos (hu.trans huw) (by linarith)) log_two_pos)
  have hd : w - u ≠ 0 := sub_ne_zero.mpr (ne_of_gt huw)
  have hjs : jn u + (w - u) * dslope jn u w = jn w := by
    have h := sub_smul_dslope jn u w
    simp only [smul_eq_mul] at h
    linarith
  have hq : qp u + (1 - 2*u)*(w - u) - (w - u)^2 = qp w := by
    unfold qp; ring
  have h := detGap_scaled (w - u) (qp u) (1 - 2*u) (jn u) (dslope jn u w)
    (regularFsGap u w) (regularWeight u w) (entropySum u w) huJ (by rw [hjs]; exact hwJ) hS hd
  rw [hjs, hq] at h
  exact h

/-- The left minor in atoms. -/
noncomputable def feM11 (t qu ku Jw s S F W hh : ℝ) : ℝ :=
  let z := -qu - s*ku/S
  qu*(1 + t*(Jw + 2*F)) + s*(hh - t) - W*(z*z)

theorem m11_identity {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1/2) :
    m11 u w = feM11 (1 / jn u) (qp u) (qp u * jn u) (jn w) (w - u) (entropySum u w)
      (Fs (contact u w)) (weight u w) (1 - 2*u) := by
  have huJ := natural_jn_nonzero hu (huw.trans hw)
  unfold m11 au zu feM11
  simp only []
  field_simp
  ring

#print axioms detGap_scaled
#print axioms tcoef_identity
#print axioms m11_identity

end CKLaneA1


