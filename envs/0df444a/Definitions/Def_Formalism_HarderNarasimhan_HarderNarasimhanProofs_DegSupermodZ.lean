-- Prove2me | Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
-- name    : Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:09:15.717702+00:00
-- url     : https://prove2.me/theorems/1061f0ae-8a32-410a-9cf1-20688c0cd3a8
-- title:
--   Deg Supermod Z
-- statement:
--   Definitions and structural lemmas for Deg Supermod Z, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DegSupermodZ.lean

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
namespace Formalism.RankSupermodularCovolume
open Formalism.F
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
end
end Formalism.RankSupermodularCovolume
namespace Formalism.HN
open Formalism.F Formalism.RankSupermodularCovolume
end Formalism.HN


