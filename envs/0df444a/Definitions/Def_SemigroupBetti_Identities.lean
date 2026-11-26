-- Prove2me | Definitions.Def_SemigroupBetti_Identities
-- name    : SemigroupBetti_Identities
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:54:10.982159+00:00
-- url     : https://prove2.me/theorems/5626e9d8-fc2e-4664-b721-14b4aee582a2
-- title:
--   Identities
-- statement:
--   Definitions and structural lemmas for Identities, from Ben Keene (BenKeene/semigroup-betti; see pinned Apache-2.0 LICENSE and source headers)'s pinned Linear upper bound for the first Betti number of four-generated numerical semigroups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Identities.lean

module
public import Definitions.Def_SemigroupBetti_Partition
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SemigroupBetti
open Finset
namespace GenData
variable (G : GenData)
def s : ℕ := G.A
def t : ℕ := G.W - G.B
def dg : ℕ := Nat.gcd G.s G.t
def p : ℕ := G.t / G.dg
def q : ℕ := G.s / G.dg
def R : ℕ := min G.B (G.W - G.A)
def U1 : Fin 4 → ℕ := ![0, G.B, 0, 0]
def V1 : Fin 4 → ℕ := ![G.B - G.A, 0, G.A, 0]
def U2 : Fin 4 → ℕ := ![0, 0, G.W - G.A, 0]
def V2 : Fin 4 → ℕ := ![0, G.W - G.B, 0, G.B - G.A]
def U3 : Fin 4 → ℕ := ![0, G.p, G.q, 0]
def V3 : Fin 4 → ℕ := ![G.p, 0, 0, G.q]
end GenData
end SemigroupBetti


