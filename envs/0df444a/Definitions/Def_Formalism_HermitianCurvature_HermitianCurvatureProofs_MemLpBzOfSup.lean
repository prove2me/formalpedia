-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemLpBzOfSup
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_MemLpBzOfSup
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:59:01.420317+00:00
-- url     : https://prove2.me/theorems/5523d9bd-e555-52d9-964a-eba721a8139c
-- title:
--   Mem Lp Bz Of Sup
-- statement:
--   Definitions and structural lemmas for Mem Lp Bz Of Sup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemLpBzOfSup.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroNotMemPreimagePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace ENNReal
noncomputable section
open Classical
section ss2
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
end ss2
end
end Formalism.FourierDecayAlt.P.PBK


