-- Prove2me | Definitions.Def_FixedOrderFactor_Defs
-- name    : FixedOrderFactor_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:46:28.624854+00:00
-- url     : https://prove2.me/theorems/775d84a0-dec8-5f82-a8f1-dc0ff6fa5427
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from J. S. Farland (jkfarland-bot/FixedOrderFactor-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned FixedOrderFactor: order-r correction factor for mean squares of L(1, chi) and 35/34 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Defs.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Real
noncomputable section
namespace FixedOrderFactor
def PrimeTo (N : Finset Nat.Primes) (n : ℕ) : Prop := ∀ q ∈ N, ¬ (q : ℕ) ∣ n
instance instDecidablePrimeTo (N : Finset Nat.Primes) : DecidablePred (PrimeTo N) :=
  fun n => inferInstanceAs (Decidable (∀ q ∈ N, ¬ (q : ℕ) ∣ n))
def zetaN (N : Finset Nat.Primes) (s : ℕ) : ℝ :=
  ∑' n : ℕ, if 0 < n ∧ PrimeTo N n then 1 / (n : ℝ) ^ s else 0
def correctionFactor (N : Finset Nat.Primes) (r : ℕ) : ℝ :=
  zetaN N r ^ 2 / zetaN N (2 * r)
def rootOfUnity (r j : ℕ) : ℂ := Complex.exp (2 * π * Complex.I * j / r)
def localTerm (z : ℂ) (x : ℝ) : ℝ := 1 / Complex.normSq (1 - z * x)
def muAvg (r : ℕ) (x : ℝ) : ℝ := (1 / r) * ∑ j ∈ Finset.range r, localTerm (rootOfUnity r j) x
def modelMean (r : ℕ) (S : Finset Nat.Primes) : ℝ :=
  (1 / (r : ℝ) ^ S.card) * ∑ z : S → Fin r,
    ∏ q : S, localTerm (rootOfUnity r (z q)) (1 / ((q : Nat.Primes) : ℝ))
def primesUpTo (N : Finset Nat.Primes) (Y : ℕ) : Finset Nat.Primes :=
  ((Finset.range (Y + 1)).preimage (fun q : Nat.Primes => (q : ℕ))
    Nat.Primes.coe_nat_injective.injOn).filter (· ∉ N)
def two : Nat.Primes := ⟨2, Nat.prime_two⟩
def sqrtCount (M a s : ℕ) : ℕ :=
  ((Finset.range M).filter fun x => Nat.Coprime x M ∧ x ^ 2 % M = a % M ∧ s ∣ x + 1).card
def orbitAvg (s t : ℕ) : ℂ :=
  (1 / (s.totient : ℂ)) * ∑ u ∈ (Finset.range s).filter s.Coprime, rootOfUnity s (u * t)
end FixedOrderFactor


