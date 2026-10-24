-- Prove2me | Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Nat
-- name    : KLS408915f_BrownianMotion_Auxiliary_Nat
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:06:08.861458+00:00
-- url     : https://prove2.me/theorems/1a33ae6d-38a6-4711-a081-4c212476e86f
-- title:
--   Even powers remove absolute values
-- statement:
--   Vendored from `RemyDegenne/brownian-motion` at commit `a7ad7af662044313bc80a7c0756360fb3745f931` under Apache-2.0. `pow_two_mul_abs` states that for a linearly ordered strict ordered ring, $|a|^{2n}=a^{2n}$ for every natural number $n$.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/Nat.lean#L8-L10 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.Nat`, definition bundle `KLS408915f_BrownianMotion_Auxiliary_Nat`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs

-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Auxiliary/Nat.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
lemma pow_two_mul_abs {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (n : ℕ) (a : α) :
    |a| ^ (2 * n) = a ^ (2 * n) :=
  Even.pow_abs ⟨n, two_mul n⟩ a


