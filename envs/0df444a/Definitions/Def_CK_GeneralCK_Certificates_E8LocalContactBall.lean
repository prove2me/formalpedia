-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8LocalContactBall
-- name    : CK_GeneralCK_Certificates_E8LocalContactBall
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:50:12.118316+00:00
-- url     : https://prove2.me/theorems/3761d3b4-c080-44ca-b8fb-5270b7887b2b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8LocalContactBall` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8LocalContactBall` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8LocalContactBall` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8LocalContactBall (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8LocalContactBall.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8LocalContactContraction
import Definitions.Def_CK_GeneralCK_Certificates_E8CoupledTauCBox

-- ===== source module GeneralCK.Certificates.E8LocalContactBall =====
section

/-! Proof-producing locally centered contact balls for E8 tau cells. -/

namespace GeneralCK.Certificates.E8LocalContactBall

open E8GaussianRatBall E8CoupledTauCBox E8LocalContactContraction
open Reflection.ComplexEntropy Reflection.ComplexGlobalAnalytic
open Reflection.ComplexDiscElementary

def localResidual (tauBall : RatBall) (z : GaussianRat) : RatBall :=
  (fixedPointImageBox tauBall (RatBall.point z.re z.im) logTwoBall).sub
    (RatBall.point z.re z.im)

def localContactBall (tauBall : RatBall) (z : GaussianRat) : RatBall :=
  { center := z
    radius := (25 / 21) *
      ((localResidual tauBall z).center.l1 + (localResidual tauBall z).radius) }

theorem localContactBall_sound_norm {tau : ℂ} {tauBall : RatBall} {z : GaussianRat}
    (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) (htauBall : tauBall.Holds tau)
    (hzNorm : ‖z.val‖ ≤ (1 / 3 : ℝ)) :
    (localContactBall tauBall z).Holds (fixedPointOnDisc tau) := by
  have hzMem : z.val ∈ Metric.closedBall (0 : ℂ) (1 / 3 : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hzNorm
  have hzContact : ‖z.val‖ ≤ (1103 / 2500 : ℝ) := hzNorm.trans (by norm_num)
  have hpoint : (RatBall.point z.re z.im).Holds z.val := by
    simpa [GaussianRat.val] using holds_point z.re z.im
  have hE := entropyBox_sound hpoint hzContact logTwoBall_holds
  have himage := holds_mul htauBall hE
  have hres : (localResidual tauBall z).Holds
      (contactMap entropyExt tau z.val - z.val) := by
    simpa [localResidual, fixedPointImageBox, contactMap, GaussianRat.val]
      using holds_sub himage hpoint
  have hresNorm : ‖contactMap entropyExt tau z.val - z.val‖ ≤
      (((localResidual tauBall z).center.l1 +
        (localResidual tauBall z).radius : ℚ) : ℝ) := by
    unfold RatBall.Holds E8ComplexBallKernel.InBall at hres
    calc
      ‖contactMap entropyExt tau z.val - z.val‖ ≤
          ‖(localResidual tauBall z).center.val‖ +
            ‖(contactMap entropyExt tau z.val - z.val) -
              (localResidual tauBall z).center.val‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ ((localResidual tauBall z).center.l1 : ℝ) +
          (localResidual tauBall z).radius :=
        add_le_add (norm_val_le_l1 _) hres
      _ = _ := by norm_cast
  have hresDist : dist (contactMap entropyExt tau z.val) z.val ≤
      (((localResidual tauBall z).center.l1 +
        (localResidual tauBall z).radius : ℚ) : ℝ) := by
    simpa [dist_eq_norm] using hresNorm
  have hdist := fixedPointOnDisc_dist_le_residual htau hzMem
  unfold localContactBall RatBall.Holds E8ComplexBallKernel.InBall
  rw [dist_eq_norm] at hdist
  exact hdist.trans (by
    rw [show (((25 / 21 : ℚ) *
      ((localResidual tauBall z).center.l1 +
        (localResidual tauBall z).radius) : ℚ) : ℝ) =
      (25 / 21 : ℝ) * (((localResidual tauBall z).center.l1 +
        (localResidual tauBall z).radius : ℚ) : ℝ) by
          push_cast
          norm_num]
    exact mul_le_mul_of_nonneg_left hresDist (by norm_num))

theorem localContactBall_sound_sq {tau : ℂ} {tauBall : RatBall} {z : GaussianRat}
    (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) (htauBall : tauBall.Holds tau)
    (hz : (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 ≤ (1 / 9 : ℝ)) :
    (localContactBall tauBall z).Holds (fixedPointOnDisc tau) := by
  apply localContactBall_sound_norm htau htauBall
  have hsquare : ‖z.val‖ ^ 2 = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  nlinarith [norm_nonneg z.val]

theorem localContactBall_sound {tau : ℂ} {tauBall : RatBall} {z : GaussianRat}
    (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) (htauBall : tauBall.Holds tau)
    (hz : (z.l1 : ℝ) ≤ (1 / 3 : ℝ)) :
    (localContactBall tauBall z).Holds (fixedPointOnDisc tau) :=
  localContactBall_sound_norm htau htauBall ((norm_val_le_l1 z).trans hz)

end GeneralCK.Certificates.E8LocalContactBall

end


