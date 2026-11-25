-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RegulatorLeSumSmallIdealsInClass
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_RegulatorLeSumSmallIdealsInClass
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T05:22:38.732043+00:00
-- url     : https://prove2.me/theorems/86eff40e-6f98-497e-ad44-3458995b91f2
-- title:
--   Regulator Le Sum Small Ideals In Class
-- statement:
--   Definitions and structural lemmas for Regulator Le Sum Small Ideals In Class, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RegulatorLeSumSmallIdealsInClass.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CovolumeLeSumVolumeOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_VolumePosSimplexLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory NumberField Finset
namespace GlobalTheory.RegulatorClassBound
open NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem Module
open scoped nonZeroDivisors
end GlobalTheory.RegulatorClassBound


