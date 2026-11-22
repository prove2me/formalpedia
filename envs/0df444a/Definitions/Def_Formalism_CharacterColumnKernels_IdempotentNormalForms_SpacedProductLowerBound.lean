-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound
-- name    : Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:33:32.265385+00:00
-- url     : https://prove2.me/theorems/8f813214-47c5-42bd-8580-93794e0dacd8
-- title:
--   Spaced Product Lower Bound
-- statement:
--   Definitions and structural lemmas for Spaced Product Lower Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SpacedProductLowerBound.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
namespace Formalism.NG
namespace IdemLiftAlt
def nP : ℕ → ℤ[X]
  | 0 => X
  | k + 1 => 3 * nP k ^ 2 - 2 * nP k ^ 3
variable {O A : Type*} [CommRing O] [Ring A] [Algebra O A]
variable [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [Module.Finite O A]
end IdemLiftAlt
end Formalism.NG


