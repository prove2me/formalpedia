-- Prove2me | Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
-- name    : Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:01:43.372589+00:00
-- url     : https://prove2.me/theorems/803aecf7-1c2e-4290-b908-c6a78e7449c8
-- title:
--   Trace Real
-- statement:
--   Definitions and structural lemmas for Trace Real, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/TraceReal.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable
import Definitions.Def_Lemmata_GeneralBFactSecondSide_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
namespace Formalism.HermitianLatticesTheory
section TR
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
variable [Module (NumberField.RingOfIntegers K) V]
  [IsScalarTower (NumberField.RingOfIntegers K) K V]
variable [FiniteDimensional K V]
end TR
end Formalism.HermitianLatticesTheory


