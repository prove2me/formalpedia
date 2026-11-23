-- Prove2me | Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_ValAdd
-- name    : Formalism_PairingDivisors_PairingDivisorProofs_ValAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:47.857144+00:00
-- url     : https://prove2.me/theorems/666ac9be-0052-4324-a3ef-dc8a31c6b6f9
-- title:
--   Val Add
-- statement:
--   Definitions and structural lemmas for Val Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/PairingDivisorProofs/ValAdd.lean

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)
namespace Formalism.PairingDivisionLocalBalance
section Val
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def GeV (w : Pl K) (c : ℝ) (x : K) : Prop := x = 0 ∨ c ≤ (vw w x : ℝ)
end Val
end Formalism.PairingDivisionLocalBalance


