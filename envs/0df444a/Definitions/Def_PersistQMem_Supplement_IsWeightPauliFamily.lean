-- Prove2me | Definitions.Def_PersistQMem_Supplement_IsWeightPauliFamily
-- name    : PersistQMem_Supplement_IsWeightPauliFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:14:17.722975+00:00
-- url     : https://prove2.me/theorems/6cddbb58-899e-4fa9-a538-ea152da78d27
-- title:
--   Canonical weight-$w$ Pauli family
-- statement:
--   On $n$ qubits, a canonical Pauli word is a tensor product of $I,X,Y,Z$ with the standard Hermitian phase of $Y$. Its weight is the number of nonidentity factors. The predicate `IsWeightPauliFamily n w G` says that $G$ enumerates, without repetition, all weight-$w$ words. Their number is
--
--   $$
--   M=3^w\binom nw.
--   $$
--
--   The same module defines the complete family of all $4^n-1=D^2-1$ nonidentity canonical Pauli words and the uniform prior used in Theorem 2.8.
--
--   **Formalization Note** Computational-basis states are indexed by `Fin (2^n)`. The enumeration equivalences record the elementary cardinality identities but assume no analytic profile or copy-complexity conclusion.
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), §2.2, pp.5–6 and §2.4, p.8 (PDF pp.8–9, 11)

import Mathlib

set_option autoImplicit false

open scoped Matrix

namespace PersistQMem
namespace Supplement

/-- A canonical Pauli word on `n` qubits: `0,1,2,3` encode `I,X,Y,Z`. -/
abbrev PauliWord (n : Nat) := Fin n -> Fin 4

/-- The number of nonidentity tensor factors in a Pauli word. -/
def pauliWeight {n : Nat} (s : PauliWord n) : Nat :=
  (Finset.univ.filter (fun i => s i != 0)).card

/-- Computational-basis bit `i` of an index in `Fin (2^n)`. -/
def basisBit {n : Nat} (x : Fin (2 ^ n)) (i : Fin n) : Bool :=
  Nat.testBit x.val i.val

/-- Matrix entry of `I`, `X`, `Y`, or `Z`, with the standard Hermitian phase for `Y`. -/
noncomputable def pauliEntry (a : Fin 4) (x y : Bool) : Complex :=
  if a = 0 then if x = y then 1 else 0
  else if a = 1 then if x != y then 1 else 0
  else if a = 2 then
    if x = false && y = true then -Complex.I
    else if x = true && y = false then Complex.I else 0
  else if x = y then if x then -1 else 1 else 0

/-- The canonical Hermitian matrix of a Pauli word on `n` qubits. -/
noncomputable def pauliMatrix {n : Nat} (s : PauliWord n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) Complex :=
  fun x y => ∏ i, pauliEntry (s i) (basisBit x i) (basisBit y i)

/-- Labels of the canonical weight-`w` Pauli strings. -/
abbrev WeightPauliLabel (n w : Nat) := {s : PauliWord n // pauliWeight s = w}

/-- The number `M = 3^w * binom(n,w)` of weight-`w` Pauli strings. -/
def weightPauliCount (n w : Nat) : Nat := 3 ^ w * Nat.choose n w

/-- `G` is an enumeration of every canonical weight-`w` Pauli string, without repetition.
The equivalence records the elementary count `|P_{n,w}| = 3^w binom(n,w)` rather than assuming
any analytic conclusion of Theorem 2.5. -/
def IsWeightPauliFamily (n w : Nat)
    (G : Fin (weightPauliCount n w) -> Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) Complex) : Prop :=
  exists e : Fin (weightPauliCount n w) ≃ WeightPauliLabel n w,
    forall j, G j = pauliMatrix (e j).1

/-- The number `D^2 - 1` of nonidentity Pauli strings in dimension `D = 2^n`. -/
def completePauliCount (n : Nat) : Nat := (2 ^ n) ^ 2 - 1

/-- Labels of all nonidentity canonical Pauli strings. -/
abbrev CompletePauliLabel (n : Nat) := {s : PauliWord n // s != fun _ => 0}

/-- `G` is an enumeration of every nonidentity canonical Pauli string, without repetition. -/
def IsCompletePauliFamily (n : Nat)
    (G : Fin (completePauliCount n) -> Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) Complex) : Prop :=
  exists e : Fin (completePauliCount n) ≃ CompletePauliLabel n,
    forall j, G j = pauliMatrix (e j).1

/-- The uniform prior on a finite family of size `M`. -/
noncomputable def uniformPrior (M : Nat) (_j : Fin M) : Real := (M : Real)⁻¹

end Supplement
end PersistQMem


