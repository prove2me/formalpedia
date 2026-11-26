-- Prove2me | Definitions.Def_SemigroupBetti_Defs
-- name    : SemigroupBetti_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:24:50.656841+00:00
-- url     : https://prove2.me/theorems/3d80b08e-5e54-55fd-a5e8-91eeb9c211e6
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Ben Keene (BenKeene/semigroup-betti; see pinned Apache-2.0 LICENSE and source headers)'s pinned Linear upper bound for the first Betti number of four-generated numerical semigroups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean

module
public import Mathlib
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SemigroupBetti
open Finset
def gens (m a b w : ℕ) : Fin 4 → ℕ := ![m, m + a, m + b, m + w]
structure GenData where
  m : ℕ
  a : ℕ
  b : ℕ
  w : ℕ
  m_pos : 0 < m
  a_pos : 0 < a
  a_lt_b : a < b
  b_lt_w : b < w
  gcd_eq_one : Nat.gcd m (Nat.gcd a (Nat.gcd b w)) = 1
  /-- Minimality: no generator is an `ℕ`-combination of the other three. -/
  minimal : ∀ i : Fin 4, ∀ z : Fin 4 → ℕ, z i = 0 → ∑ j, z j * gens m a b w j ≠ gens m a b w i
def len (z : Fin 4 → ℕ) : ℕ := ∑ i, z i
def supp (z : Fin 4 → ℕ) : Finset (Fin 4) := Finset.univ.filter (fun i => 0 < z i)
def SharesVar (z z' : Fin 4 → ℕ) : Prop := ∃ i, 0 < z i ∧ 0 < z' i
instance : DecidableRel SharesVar := fun z z' =>
  inferInstanceAs (Decidable (∃ i, 0 < z i ∧ 0 < z' i))
namespace GenData
variable (G : GenData)
def n : Fin 4 → ℕ := gens G.m G.a G.b G.w
def g : ℕ := Nat.gcd G.a (Nat.gcd G.b G.w)
def A : ℕ := G.a / G.g
def B : ℕ := G.b / G.g
def W : ℕ := G.w / G.g
def nu (z : Fin 4 → ℕ) : ℕ := ∑ i, z i * G.n i
def omega (z : Fin 4 → ℕ) : ℕ := G.a * z 1 + G.b * z 2 + G.w * z 3
end GenData
end SemigroupBetti


