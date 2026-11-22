-- Prove2me | Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeIneq
-- name    : Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeIneq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:21.127016+00:00
-- url     : https://prove2.me/theorems/8b2e890d-c68a-40c3-807d-dd744d0883c7
-- title:
--   Size Ineq
-- statement:
--   Definitions and structural lemmas for Size Ineq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SizeIneq.lean

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Lemmata_GeneralBFactSecondTail_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
namespace Formalism.HN
section SlopeTestRemainingChoices
variable {K : Type*} [Field K] [NumberField K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {W : Type*} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
end SlopeTestRemainingChoices
end Formalism.HN


