-- Prove2me | Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
-- name    : Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:51.516274+00:00
-- url     : https://prove2.me/theorems/ba2e2e19-87d2-43ae-9d38-a7bd75e0caf5
-- title:
--   Good Bad Cut
-- statement:
--   Definitions and structural lemmas for Good Bad Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/GoodBadCut.lean

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
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
namespace Formalism.ExtensionFiltration
open Formalism.HN
namespace HermitianIdempotentFrameLemmas
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
section Mod
variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end Mod
end HermitianIdempotentFrameLemmas
end Formalism.ExtensionFiltration


