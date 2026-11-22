-- Prove2me | Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_RestrictRoots
-- name    : Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_RestrictRoots
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:07:13.306435+00:00
-- url     : https://prove2.me/theorems/7f2c0b65-aea1-4da1-b001-8885e2025c09
-- title:
--   Restrict Roots
-- statement:
--   Definitions and structural lemmas for Restrict Roots, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/RestrictRoots.lean

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GaloisIrreducibility
open Module Polynomial
section SlopeTestRemainingChoices
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end SlopeTestRemainingChoices
end Formalism.GaloisIrreducibility


