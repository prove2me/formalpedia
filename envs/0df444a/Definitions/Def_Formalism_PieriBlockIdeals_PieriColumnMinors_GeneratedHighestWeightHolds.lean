-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_GeneratedHighestWeightHolds
-- name    : Formalism_PieriBlockIdeals_PieriColumnMinors_GeneratedHighestWeightHolds
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:47:29.199605+00:00
-- url     : https://prove2.me/theorems/48119e5f-5e14-46ff-a0d4-ce4afd01f952
-- title:
--   Generated Highest Weight Holds
-- statement:
--   Definitions and structural lemmas for Generated Highest Weight Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/GeneratedHighestWeightHolds.lean

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.CohomologicalDescent.LP
open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample
section
variable {K N : Type*} [CommRing K] [AddCommGroup N] [Module K N] {q : ℕ}
inductive LowW (T : Fin q → Fin q → Module.End K N) (κ : Fin q → K) : N → Prop
  | base (v : N) : IsHW T κ v → LowW T κ v
  | step (a b : Fin q) (x : N) : b < a → LowW T κ x → LowW T κ (T a b x)
def lowSpan (T : Fin q → Fin q → Module.End K N) (κ : Fin q → K) : Submodule K N :=
  Submodule.span K {x | LowW T κ x}
end
end Formalism.CohomologicalDescent.LP


