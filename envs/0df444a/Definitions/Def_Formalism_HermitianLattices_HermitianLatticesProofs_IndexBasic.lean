-- Prove2me | Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
-- name    : Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:58:24.412836+00:00
-- url     : https://prove2.me/theorems/786c73d7-6ec0-43d9-8b80-beb911ababd5
-- title:
--   Index Basic
-- statement:
--   Definitions and structural lemmas for Index Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/IndexBasic.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
namespace Formalism.HermitianLatticesTheory
section Fin
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
end Fin
section K
variable {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
end K
end Formalism.HermitianLatticesTheory


