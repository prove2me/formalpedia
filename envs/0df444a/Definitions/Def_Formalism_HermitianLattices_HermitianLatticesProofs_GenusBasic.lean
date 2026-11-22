-- Prove2me | Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
-- name    : Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:58:01.526111+00:00
-- url     : https://prove2.me/theorems/e81faf0d-5298-47a4-806d-7ac4d66fcff2
-- title:
--   Genus Basic
-- statement:
--   Definitions and structural lemmas for Genus Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusBasic.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HermitianLatticesTheory
section SlopeTestRemainingChoices
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
end SlopeTestRemainingChoices
end Formalism.HermitianLatticesTheory


