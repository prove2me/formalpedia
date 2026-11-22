-- Prove2me | Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
-- name    : Formalism_ThickAverageLoss_ThickAverageProofs_Balance
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:42:01.051805+00:00
-- url     : https://prove2.me/theorems/4b3062ee-7e1a-4202-b321-f8484b929b39
-- title:
--   Balance
-- statement:
--   Definitions and structural lemmas for Balance, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/Balance.lean

import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
namespace Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
namespace Bal
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
end
end Bal
end Formalism.D5


