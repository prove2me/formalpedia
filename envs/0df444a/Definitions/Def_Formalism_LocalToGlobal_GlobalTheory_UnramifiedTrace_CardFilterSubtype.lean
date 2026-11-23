-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_UnramifiedTrace_CardFilterSubtype
-- name    : Formalism_LocalToGlobal_GlobalTheory_UnramifiedTrace_CardFilterSubtype
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:04.631894+00:00
-- url     : https://prove2.me/theorems/aab64833-7f2e-4b26-866d-90b2e8131c24
-- title:
--   Card Filter Subtype
-- statement:
--   Definitions and structural lemmas for Card Filter Subtype, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/UnramifiedTrace/CardFilterSubtype.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
variable {K X : Type*} [Field K] [Fintype K] [DecidableEq K] [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  [Fintype (Module.Dual K X)]
end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace


