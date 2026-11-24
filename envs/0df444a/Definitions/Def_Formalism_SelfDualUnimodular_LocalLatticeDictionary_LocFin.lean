-- Prove2me | Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_LocFin
-- name    : Formalism_SelfDualUnimodular_LocalLatticeDictionary_LocFin
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T14:24:36.75122+00:00
-- url     : https://prove2.me/theorems/088391df-3c2d-4700-b398-f8cd7cfad3d1
-- title:
--   Loc Fin
-- statement:
--   Definitions and structural lemmas for Loc Fin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/LocFin.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Lemmata_Denominators_Denom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.LF
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
end Formalism.L2.SG.Pf.LatDictZ.Z0.LF


