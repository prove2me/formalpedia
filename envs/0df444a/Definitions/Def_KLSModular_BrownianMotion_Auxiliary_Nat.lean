-- Prove2me | Definitions.Def_KLSModular_BrownianMotion_Auxiliary_Nat
-- name    : KLSModular_BrownianMotion_Auxiliary_Nat
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:35:04.243085+00:00
-- url     : https://prove2.me/theorems/786d8665-2608-4fe8-8656-a0658df4f80e
-- title:
--   Even powers remove absolute values
-- statement:
--   Vendored from `RemyDegenne/brownian-motion` at commit `a7ad7af662044313bc80a7c0756360fb3745f931` under Apache-2.0. `pow_two_mul_abs` states that for a linearly ordered strict ordered ring, $|a|^{2n}=a^{2n}$ for every natural number $n$.
--
--   **Original module imports**
--
--   ```lean
--   public import Mathlib.Algebra.Order.Floor.Semiring
--   public import Mathlib.Algebra.Order.Ring.Abs
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   lemma pow_two_mul_abs {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (n : ℕ) (a : α) :
--       |a| ^ (2 * n) = a ^ (2 * n) :=
--     Even.pow_abs ⟨n, two_mul n⟩ a
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/Auxiliary/Nat.lean) · `BrownianMotion.Auxiliary.Nat` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/Nat.lean#L8-L10 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.Nat`, definition bundle `KLSModular_BrownianMotion_Auxiliary_Nat`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs

-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Auxiliary/Nat.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
lemma pow_two_mul_abs {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (n : ℕ) (a : α) :
    |a| ^ (2 * n) = a ^ (2 * n) :=
  Even.pow_abs ⟨n, two_mul n⟩ a


