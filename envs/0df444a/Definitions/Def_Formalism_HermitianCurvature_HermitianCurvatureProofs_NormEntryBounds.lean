-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormEntryBounds
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_NormEntryBounds
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T17:34:22.069987+00:00
-- url     : https://prove2.me/theorems/cedc82d1-376e-45bf-b376-1cfd49beb9d7
-- title:
--   Norm Entry Bounds
-- statement:
--   Definitions and structural lemmas for Norm Entry Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormEntryBounds.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryMinorBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZhatSectionExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P
open C2x2 C2x5 HermitianXiVector UnipotentSums EntryMinorBounds
namespace NormEntryBounds
variable {k r : ℕ}
end NormEntryBounds
open NormEntryBounds
end Formalism.FourierDecayAlt.P


