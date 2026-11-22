-- Prove2me | Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_AutFinite
-- name    : Formalism_HermitianLattices_HermitianLatticesProofs_AutFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:02:29.406604+00:00
-- url     : https://prove2.me/theorems/24f807d4-0b3d-4c65-81ae-0a129f4e60f0
-- title:
--   Aut Finite
-- statement:
--   Definitions and structural lemmas for Aut Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/AutFinite.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable
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
section AutFiniteSec
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
end AutFiniteSec
end Formalism.HermitianLatticesTheory


