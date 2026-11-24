-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:31:17.68279+00:00
-- url     : https://prove2.me/theorems/995f0f27-4038-4635-b166-22ab51b0465a
-- title:
--   Exists Ex Of Pow
-- statement:
--   Definitions and structural lemmas for Exists Ex Of Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
namespace GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
def pr (x a : Matrix κ ι ℚ) : ℚ := ∑ k, x k ⬝ᵥ a k
def ex (r : ℚ) : ℂ := cexp (π * I * (r : ℂ))
def fac (ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ) (y : Matrix κ ι ℚ × Matrix κ ι ℚ)
    (x : Matrix κ ι ℚ) : ℂ := ε y * ex (2 * pr x y.1 - pr y.1 y.2)
end
end GlobalTheory.SW.Vac


