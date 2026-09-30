-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema
-- name    : CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:59:28.343025+00:00
-- url     : https://prove2.me/theorems/fe24076a-225d-43cd-ba9a-6473f0638067
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8QuadraticCellCertificateSchema` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8QuadraticCellCertificateSchema` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8QuadraticCellCertificateSchema` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8QuadraticCellCertificateSchema (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8QuadraticCellCertificateSchema.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticBallAcceptance
import Definitions.Def_CK_GeneralCK_Certificates_E8LocalContactBall

-- ===== source module GeneralCK.Certificates.E8QuadraticCellCertificateSchema =====
section

/-! Production leaf schema using the sound squared-Euclidean output test. -/

namespace GeneralCK.Certificates.E8QuadraticCellCertificateSchema

open E8GaussianRatBall E8LocalContactBall E8RoundedDerivativeEvaluator
open E8CoupledTauCBox E8QuadraticBallAcceptance

def precision : ℕ := 2^40

structure CellCertificate where
  tauBall : RatBall
  contactCenter : GaussianRat
  contactBall : RatBall
  work : RoundedTauEval
  center_sq : (contactCenter.re : ℝ) ^ 2 + (contactCenter.im : ℝ) ^ 2 ≤
    (1/9 : ℝ)
  contact_eq : localContactBall tauBall contactCenter = contactBall
  work_eq : evalTau precision tauBall contactBall logTwoBall = work
  theta_ok : work.theta.ok = true
  jac_ok : work.jac.invOK = true
  accepted : acceptsUnitSq work.out = true

theorem CellCertificate.sound (cell : CellCertificate) {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ)) (hcell : cell.tauBall.Holds tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  have hc : cell.contactBall.Holds
      (Reflection.ComplexGlobalAnalytic.fixedPointOnDisc tau) := by
    rw [← cell.contact_eq]
    exact localContactBall_sound_sq htau hcell cell.center_sq
  have hthetaWork : (evalTau precision cell.tauBall cell.contactBall
      logTwoBall).theta.ok = true := by rw [cell.work_eq]; exact cell.theta_ok
  have htheta : (evalTheta precision cell.contactBall logTwoBall).ok = true := by
    simpa [evalTau] using hthetaWork
  have hjac : (evalTau precision cell.tauBall cell.contactBall
      logTwoBall).jac.invOK = true := by rw [cell.work_eq]; exact cell.jac_ok
  have hout := evalTau_out_sound (D := precision) (by norm_num [precision])
    htau hcell hc logTwoBall_holds htheta hjac
  apply acceptsUnitSq_sound (b := cell.work.out) cell.accepted
  rwa [← cell.work_eq]

def CoveredBy (cells : List CellCertificate) (tau : ℂ) : Prop :=
  ∃ cell ∈ cells, cell.tauBall.Holds tau

theorem sound_of_covered (cells : List CellCertificate) {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ)) (hcover : CoveredBy cells tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases hcover with ⟨cell, _, hcell⟩
  exact cell.sound htau hcell

end GeneralCK.Certificates.E8QuadraticCellCertificateSchema

end


