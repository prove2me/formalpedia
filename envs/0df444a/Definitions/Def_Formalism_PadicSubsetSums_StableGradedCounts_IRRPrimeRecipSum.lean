-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
-- name    : Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:40:43.025976+00:00
-- url     : https://prove2.me/theorems/3eb1b579-26db-4839-9e64-b009e50713e0
-- title:
--   IRRPrime Recip Sum
-- statement:
--   Definitions and structural lemmas for IRRPrime Recip Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeRecipSum.lean

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Nat
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace PrimeCountingLemmas
noncomputable def S (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N), (1 : ℝ) / p
def test (F r a b p : ℕ) : Bool :=
  Nat.ble (p + 3) a && Nat.blt b (2 * p) && Nat.blt r p && Nat.blt p ((r + 1) * (r + 1)) &&
    Nat.beq (Nat.gcd p F) 1
def term (M F r a b p : ℕ) : ℕ := bif test F r a b p then M / p else 0
def bsum (t : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, lo => t lo
  | k + 1, lo => bsum t k lo + bsum t k (lo + 2 ^ k)
def chk (M F r a b : ℕ) : Bool :=
  Nat.ble M (20 * bsum (term M F r a b) (Nat.log2 a) (b / 2))
def ladder (M F r T : ℕ) : ℕ → ℕ → Bool
  | 0, a => Nat.ble T a
  | f + 1, a => Nat.ble T a || (chk M F r a (a + a / 10) && ladder M F r T f (a + a / 10 + 1))
def upper (n : ℕ) : Finset ℕ := (Finset.range (2 * n + 1)).filter (fun p => p.Prime ∧ n < p)
end PrimeCountingLemmas
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility


