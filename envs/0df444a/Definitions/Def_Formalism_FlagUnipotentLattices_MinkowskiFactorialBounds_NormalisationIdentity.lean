-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NormalisationIdentity
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NormalisationIdentity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:18:30.540202+00:00
-- url     : https://prove2.me/theorems/c2e149bc-115b-4f9c-859a-1b000124541f
-- title:
--   Normalisation Identity
-- statement:
--   Definitions and structural lemmas for Normalisation Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/NormalisationIdentity.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLatticeCounting.P
open Finset Formalism.HermitianLatticeCounting.ExpansionTerms
noncomputable def brG (c : ℝ) (j : ℕ) : ℝ := if j = 0 then 2 + c else 1 + 1 / (j : ℝ)
end Formalism.HermitianLatticeCounting.P


