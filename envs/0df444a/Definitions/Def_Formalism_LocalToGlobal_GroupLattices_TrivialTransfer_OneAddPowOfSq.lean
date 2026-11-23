-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_OneAddPowOfSq
-- name    : Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_OneAddPowOfSq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:40:19.332378+00:00
-- url     : https://prove2.me/theorems/646c7931-8069-4009-be41-c734acd85ff3
-- title:
--   One Add Pow Of Sq
-- statement:
--   Definitions and structural lemmas for One Add Pow Of Sq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/OneAddPowOfSq.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ClosureUpperUni
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddPowOfMulSelfEqZero
import Definitions.Def_Lemmata_GeneralBFactLeftTail_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
namespace Formalism.L2.G.Triv
section Helpers
end Helpers
section Ring
variable {R : Type} [CommRing R] {k : ℕ}
end Ring
section Place
variable {F : Type} [Field F] [NumberField F] {k : ℕ}
end Place
end Formalism.L2.G.Triv
end


