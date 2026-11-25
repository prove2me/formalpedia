-- Prove2me | Definitions.Def_Erdos1063_Lower
-- name    : Erdos1063_Lower
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:25:35.003017+00:00
-- url     : https://prove2.me/theorems/df556d2f-34ec-4374-bdc6-7aeb4e6c0de1
-- title:
--   Lower
-- statement:
--   Definitions and structural lemmas for Lower, from Paul Lee (Paulee314/erdos1063-lean; definition reused under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and source headers)'s pinned Erdos Problem 1063: lower bound and exceptional index structure development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Paulee314/erdos1063-lean/blob/ba104cbcf0bb7c555a8b2f0d58018989a08c638e/Erdos1063/Lower.lean

module
public import Mathlib
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Finset
open scoped Nat
namespace Erdos1063
noncomputable def n (k : ℕ) : ℕ :=
  sInf {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
    ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}
def W (k : ℕ) : ℕ := ∏ p ∈ k.primeFactors, p ^ (padicValNat p k + Nat.log p (k - 1))
end Erdos1063


