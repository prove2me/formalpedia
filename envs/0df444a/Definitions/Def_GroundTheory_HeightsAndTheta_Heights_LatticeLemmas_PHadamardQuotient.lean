-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardQuotient
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardQuotient
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T09:32:23.330195+00:00
-- url     : https://prove2.me/theorems/4af1997f-e52b-5d52-90f6-f3d2057973c5
-- title:
--   PHadamard Quotient
-- statement:
--   Definitions and structural lemmas for PHadamard Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamardQuotient.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Module Submodule
open GroundTheory.Heights₂.Heights
universe u v w
noncomputable section
namespace HadamardQuotient
variable {K : Type*} [Field K] [NumberField K]
end HadamardQuotient
end
end GroundTheory.Heights₂.Heights.LatticeLemmas


