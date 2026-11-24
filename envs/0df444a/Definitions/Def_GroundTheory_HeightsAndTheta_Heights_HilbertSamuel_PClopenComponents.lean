-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PClopenComponents
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PClopenComponents
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:24.039805+00:00
-- url     : https://prove2.me/theorems/33752a79-9701-4c53-9021-df7d8bf2cf54
-- title:
--   PClopen Components
-- statement:
--   Definitions and structural lemmas for PClopen Components, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PClopenComponents.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsClopenComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsIrreducibleConnected
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (ι) in

def multiIrrelevantIdeal : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  Ideal.span (Set.range fun i : (∀ k, ι k) => ∏ k, (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℂ))
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


