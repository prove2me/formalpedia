-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ThetaTauDerivativeFormula
-- name    : CK_GeneralCK_Certificates_E8ThetaTauDerivativeFormula
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:17:40.208702+00:00
-- url     : https://prove2.me/theorems/f9ad420d-006e-4c71-9e6c-4cfde88a2faf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ThetaTauDerivativeFormula` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ThetaTauDerivativeFormula` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ThetaTauDerivativeFormula` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ThetaTauDerivativeFormula (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ThetaTauDerivativeFormula.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ThetaTauAnalytic

-- ===== source module GeneralCK.Certificates.E8ThetaTauDerivativeFormula =====
section

/-!
# Derivative handoff for the final E8 quantitative inverse bound

This removes the derivative of the implicit contact branch.  The only
derivative left in the displayed expression is that of the explicit
elementary function `thetaParam`, the target for a complex interval checker.
-/

namespace GeneralCK.Certificates.E8ThetaTauDerivativeFormula

open E8AnalyticGerm
open Reflection.ComplexEntropy
open Reflection.ComplexGlobalAnalytic
open E8TauInverseContraction
open E8ThetaTauAnalytic

noncomputable def thetaTauDerivExpr (tau : ℂ) : ℂ :=
  let c := fixedPointOnDisc tau
  deriv thetaParam c *
    (entropyExt c / (1 - tau * entropyDeriv c))

theorem hasDerivAt_thetaOfTau_expr {tau : ℂ}
    (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) :
    HasDerivAt thetaOfTau (thetaTauDerivExpr tau) tau := by
  have htau' : ‖tau‖ < (7 / 10 : ℝ) := htau.trans_lt (by norm_num)
  have hc := norm_fixedPointOnDisc_le htau
  have houter := (analyticAt_thetaParam_on_disc hc).differentiableAt.hasDerivAt
  have hinner := hasDerivAt_fixedPointOnDisc htau'
  change HasDerivAt (thetaParam ∘ fixedPointOnDisc) _ tau
  simpa only [thetaTauDerivExpr] using houter.comp tau hinner

theorem deriv_thetaTauRemainder_eq {tau : ℂ}
    (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) :
    deriv thetaTauRemainder tau = thetaTauDerivExpr tau - 4 := by
  have htheta := hasDerivAt_thetaOfTau_expr htau
  have hlinear : HasDerivAt (fun z : ℂ => 4 * z) 4 tau := by
    simpa using (hasDerivAt_id (𝕜 := ℂ) tau).const_mul 4
  have h := htheta.sub hlinear
  change deriv (thetaOfTau - fun z : ℂ => 4 * z) tau = _
  exact h.deriv

theorem final_derivative_bound_of_expr_bound
    (hExpr : ∀ tau : ℂ, ‖tau‖ ≤ (2 / 5 : ℝ) →
      ‖thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ)) :
    ∀ tau : ℂ, ‖tau‖ ≤ (2 / 5 : ℝ) →
      ‖deriv thetaTauRemainder tau‖ ≤ (1 : ℝ) := by
  intro tau htau
  rw [deriv_thetaTauRemainder_eq htau]
  exact hExpr tau htau

end GeneralCK.Certificates.E8ThetaTauDerivativeFormula

end


