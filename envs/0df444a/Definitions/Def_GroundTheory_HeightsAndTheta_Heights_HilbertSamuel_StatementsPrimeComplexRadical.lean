-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPrimeComplexRadical
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPrimeComplexRadical
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:29.074888+00:00
-- url     : https://prove2.me/theorems/288eeac8-297f-42ea-9bbf-711176cb5d48
-- title:
--   Statements Prime Complex Radical
-- statement:
--   Definitions and structural lemmas for Statements Prime Complex Radical, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsPrimeComplexRadical.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial
noncomputable section
def PrimeComplexRadical.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℤ)), P.IsPrime →
    (P.map (MvPolynomial.map (Int.castRingHom ℂ))).IsRadical
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


