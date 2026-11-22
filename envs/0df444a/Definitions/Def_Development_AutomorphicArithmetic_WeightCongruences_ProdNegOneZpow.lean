-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
-- name    : Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:22:00.507154+00:00
-- url     : https://prove2.me/theorems/c33efef9-4375-4e62-bce4-255c392203d4
-- title:
--   Prod Neg One Zpow
-- statement:
--   Definitions and structural lemmas for Prod Neg One Zpow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/ProdNegOneZpow.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace UpperTheory
variable {E K K' : Type} [Field E] [Field K] [Field K'] {ι ι' : Type} [Fintype ι] [Fintype ι']
def MU (φ : ι → E →+* K) (e : ι → ℤ) : Prop :=
  ∀ z : E, (∃ m : ℕ, 0 < m ∧ z ^ m = 1) → ∏ i, φ i z ^ e i = 1
def MUQ (φ : ι → E →+* K) (e : ι → ℚ) : Prop :=
  ∃ a : ι → ℤ, (∀ i, e i = a i) ∧ MU φ a
namespace MU
variable {φ : ι → E →+* K} {e e' : ι → ℤ}
end MU
namespace MUQ
variable {φ : ι → E →+* K} {e : ι → ℚ}
end MUQ
end UpperTheory


