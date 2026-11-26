-- Prove2me | Definitions.Def_SemigroupBetti_Solution
-- name    : SemigroupBetti_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:58:52.675882+00:00
-- url     : https://prove2.me/theorems/fcb6439d-bd6b-4e28-a994-0173fb8845f1
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Ben Keene (BenKeene/semigroup-betti; see pinned Apache-2.0 LICENSE and source headers)'s pinned Linear upper bound for the first Betti number of four-generated numerical semigroups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/Solution.lean

module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Definitions.Def_SemigroupBetti
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SemigroupBetti
open MvPolynomial
noncomputable def toricIdeal (K : Type*) [Field K] (n : Fin 4 → ℕ) :
    Ideal (MvPolynomial (Fin 4) K) :=
  RingHom.ker (MvPolynomial.aeval (fun i => (Polynomial.X : Polynomial K) ^ n i)).toRingHom
def MinimallyGenerates (n : Fin 4 → ℕ) : Prop :=
  ∀ i : Fin 4, n i ∉ AddSubmonoid.closure (n '' {j | j ≠ i})
def normalizedWidth (n : Fin 4 → ℕ) : ℕ :=
  (n 3 - n 0) / Nat.gcd (n 1 - n 0) (Nat.gcd (n 2 - n 0) (n 3 - n 0))
end SemigroupBetti


