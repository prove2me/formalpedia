-- Prove2me | Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajBasic
-- name    : Formalism_HermitianLattices_HermitianLatticesProofs_MajBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:33.39288+00:00
-- url     : https://prove2.me/theorems/dfa5a506-cdb5-4473-b626-be4096319a9a
-- title:
--   Maj Basic
-- statement:
--   Definitions and structural lemmas for Maj Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajBasic.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_OpBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
noncomputable section
namespace Formalism.HermitianLatticesTheory
section MajBasicAux
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
end MajBasicAux
end Formalism.HermitianLatticesTheory


