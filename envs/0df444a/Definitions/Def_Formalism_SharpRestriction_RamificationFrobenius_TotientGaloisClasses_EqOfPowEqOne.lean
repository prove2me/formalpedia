-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_EqOfPowEqOne
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_EqOfPowEqOne
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T19:25:36.696783+00:00
-- url     : https://prove2.me/theorems/7f711f1a-049c-47a9-86ac-893c215b700a
-- title:
--   Eq Of Pow Eq One
-- statement:
--   Definitions and structural lemmas for Eq Of Pow Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/EqOfPowEqOne.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
namespace Formalism.HC.D7
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {e q d : ℕ} (hH : HostHyp q d) {L : Type} [Field L] [NumberField L] {ζ a b : L}
  (h : IsLayer (e + 2) q d ζ a b)
include hH h
end Formalism.HC.D7
end


