-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsGA
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsGA
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:37:13.51657+00:00
-- url     : https://prove2.me/theorems/4f61ef8f-17cf-47d4-8230-0deba3ecbdb0
-- title:
--   All Rows GA
-- statement:
--   Definitions and structural lemmas for All Rows GA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/AllRowsGA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MonoidAlgebra
namespace Formalism.L2.SG.Pf.AllRowsGA
variable {G : Type} [Group G] [Fintype G]
def conjA (a : MonoidAlgebra ℂ G) : MonoidAlgebra ℂ G :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g => star (a.coeff g⁻¹))
end Formalism.L2.SG.Pf.AllRowsGA


