-- Prove2me | Definitions.Def_DedekindSubgroups_Parity
-- name    : DedekindSubgroups_Parity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:04:45.44847+00:00
-- url     : https://prove2.me/theorems/de8b2f1b-0ea0-4fab-9e00-2c9a31d2e3ba
-- title:
--   Parity
-- statement:
--   Definitions and structural lemmas for Parity, from J. S. Farland (jkfarland-bot/DedekindSubgroups-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned DedekindSubgroups: a congruence modulo 16 for sums of Dedekind sums over subgroups of odd order development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Parity.lean

module
public import Definitions.Def_DedekindSubgroups_Meyer
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset Equiv
namespace DedekindSubgroups
section Inversions
variable {h h' k : ℕ}
theorem sig_lt (hk : 0 < k) (h z : ℕ) : sig h k z < k := Nat.mod_lt _ hk
theorem sig_sig (hinv : h * h' % k = 1) {r : ℕ} (hr : r < k) : sig h' k (sig h k r) = r := by
  unfold sig
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, Nat.mul_mod, mul_comm h' h, hinv,
    one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hr]
def invSet (h k : ℕ) : Finset (ℕ × ℕ) :=
  (range k ×ˢ range k).filter (fun p => p.1 < p.2 ∧ sig h k p.2 < sig h k p.1)
def mulPerm (hk : 0 < k) (hinv : h * h' % k = 1) : Perm (Fin k) where
  toFun r := ⟨sig h k r, sig_lt hk _ _⟩
  invFun r := ⟨sig h' k r, sig_lt hk _ _⟩
  left_inv r := by ext; exact sig_sig hinv r.2
  right_inv r := by ext; exact sig_sig (by rwa [mul_comm] : h' * h % k = 1) r.2
end Inversions
end DedekindSubgroups


