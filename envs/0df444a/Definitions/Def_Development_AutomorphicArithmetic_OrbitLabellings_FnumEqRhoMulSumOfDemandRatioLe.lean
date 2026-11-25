-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_FnumEqRhoMulSumOfDemandRatioLe
-- name    : Development_AutomorphicArithmetic_OrbitLabellings_FnumEqRhoMulSumOfDemandRatioLe
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:14:46.263886+00:00
-- url     : https://prove2.me/theorems/e261955f-bd9f-44e3-b3a5-a1db7293dff1
-- title:
--   Fnum Eq Rho Mul Sum Of Demand Ratio Le
-- statement:
--   Definitions and structural lemmas for Fnum Eq Rho Mul Sum Of Demand Ratio Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/FnumEqRhoMulSumOfDemandRatioLe.lean

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Formalism.IncomingBounds
namespace UpperTheory.AlternatingNumberFlow
section Helpers
variable {l d : ℕ} [NeZero d]
noncomputable def altNum (l d : ℕ) (D : ZMod d → ℝ) (s : ZMod d) : ℝ :=
  ∑ r ∈ Finset.range (2 * d), (-1 : ℝ) ^ r * ((l : ℝ) ^ (r + 1))⁻¹ * D (s - (r : ZMod d))
end Helpers
end UpperTheory.AlternatingNumberFlow


