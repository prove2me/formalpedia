-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_GoodRecipPf
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_GoodRecipPf
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:07:48.533771+00:00
-- url     : https://prove2.me/theorems/d05557de-6b93-402d-9ca7-34fe03790028
-- title:
--   Good Recip Pf
-- statement:
--   Definitions and structural lemmas for Good Recip Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/GoodRecipPf.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
namespace Formalism.L2.SG.Pf.GoodRecipPf
section Rev
variable {K : Type*} [Field K]
end Rev
section Inv
variable {L : Type*} [Field L]
end Inv
section Recip
variable {g : ℕ} [Fact g.Prime]
end Recip
end Formalism.L2.SG.Pf.GoodRecipPf
namespace Formalism.L2.SG.Pf.RowDictPf
open Formalism.L2.SG.Pf.GoodRecipPf
end Formalism.L2.SG.Pf.RowDictPf


