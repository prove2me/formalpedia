-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreRationalLogCertificate
-- name    : row23_rh_supp_RHLegendreRationalLogCertificate
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:16:22.773197+00:00
-- url     : https://prove2.me/theorems/58416541-130d-411b-b629-57740901a3a2
-- title:
--   Row 23 RH support: RHLegendreRationalLogCertificate
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreRationalLogScaling
set_option autoImplicit false
namespace DusartLegendreSmoothing.RationalLog
 def certificate (q : ℚ) (k : ℕ) (L U : ℚ) : Prop :=
  1 ≤ reduce q k ∧ L ≤ lower q k 30 ∧ upper q k 30 ≤ U
 theorem verified_bounds (q : ℚ) (k : ℕ) (L U : ℚ) (h : certificate q k L U) :
    (L:ℝ) ≤ Real.log (q:ℝ) ∧ Real.log (q:ℝ) ≤ (U:ℝ) := by
  have hb := bounds q k 30 h.1
  exact ⟨(Rat.cast_mono (K:=ℝ) h.2.1).trans hb.1,
    hb.2.trans (Rat.cast_mono (K:=ℝ) h.2.2)⟩
end DusartLegendreSmoothing.RationalLog
#print axioms DusartLegendreSmoothing.RationalLog.verified_bounds


