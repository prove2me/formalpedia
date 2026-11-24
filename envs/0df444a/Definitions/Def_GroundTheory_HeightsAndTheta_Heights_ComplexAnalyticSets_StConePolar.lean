-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConePolar
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConePolar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:26.307855+00:00
-- url     : https://prove2.me/theorems/4240d53f-fca3-4200-8ee9-bc6318326e04
-- title:
--   St Cone Polar
-- statement:
--   Definitions and structural lemmas for St Cone Polar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StConePolar.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
def ConePolar.Statement : Prop :=
  ∀ e : ℕ, ∃ κ : ℝ, ∀ (n : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (g : (Fin n → ℂ) → ℝ),
    IsProjPrime J → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) →
    linForm ℓ ∉ J → (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → g (t • x) = g x) →
    ContinuousOn g {x | x ≠ 0} →
      coneIntegral h J e g =
        κ * varInt (J ⊔ Ideal.span {linForm ℓ - 1}) e g (fun _ x => Real.log (h.dualNorm x))
end
end GroundTheory.Heights₂.Heights


