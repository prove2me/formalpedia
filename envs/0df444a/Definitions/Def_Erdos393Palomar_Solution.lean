-- Prove2me | Definitions.Def_Erdos393Palomar_Solution
-- name    : Erdos393Palomar_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T15:12:05.102112+00:00
-- url     : https://prove2.me/theorems/2a14b735-3ff4-4d9c-9c90-e355a04c0c6f
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Daniel Veljjanoski (veljjanoski/erdos393-palomar; definitions and statement reused under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Erdos Problem 393: factorial factorisation span diverges assuming the abc conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Filter Asymptotics
open scoped Nat
namespace ABC
def radical (n : ℕ) : ℕ := n.primeFactors.prod id
end ABC
namespace Erdos393
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ ∃ a : ℕ, ∃ s ⊆ Finset.Icc a (a + m), a ∈ s ∧ a + m ∈ s ∧
    ∏ i ∈ s, i = n !}
end Erdos393
namespace Erdos393Proof
open ABC Polynomial
abbrev AbcHyp : Prop := ∀ (ε : ℝ), 0 < ε →
    {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧
      ({t.1, t.2.1, t.2.2} : Set ℕ).Pairwise Nat.Coprime ∧ t.1 + t.2.1 = t.2.2 ∧
      (radical <| t.1 * t.2.1 * t.2.2 : ℝ)^(1 + ε) < t.2.2}.Finite
end Erdos393Proof
namespace Erdos393
end Erdos393


