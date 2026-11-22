-- Prove2me | Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
-- name    : Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:31.97886+00:00
-- url     : https://prove2.me/theorems/fd753a7a-fce4-42d8-977a-32a8fbc4af3f
-- title:
--   Real Cyclotomic Subfield
-- statement:
--   Definitions and structural lemmas for Real Cyclotomic Subfield, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/RealCyclotomicSubfield.lean

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace RealCyclotomicSubfield
variable {L : Type} [Field L] [NumberField L]
end RealCyclotomicSubfield
end Formalism.FrobeniusOrbits


