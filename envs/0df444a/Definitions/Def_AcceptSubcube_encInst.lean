-- Prove2me | Definitions.Def_AcceptSubcube_encInst
-- name    : AcceptSubcube_encInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:35.56546+00:00
-- url     : https://prove2.me/theorems/1e47736d-de22-4449-b1bb-e588d546d999
-- title:
--   Binary encodings of instances, assignments and algorithm inputs
-- statement:
--   The paper's algorithms are read as Turing machines, which need fixed encodings of their inputs and outputs as words over a finite alphabet. Over the alphabet $\{0,1,2,3\}$ of the published `OnlineCRS.Combine` encoders, natural numbers are written in binary, rationals as signed numerator, $2$, denominator, bit strings as words of $0$/$1$, lists are prefixed by their length, and tokens are separated by $3$.
--
--   This file fixes the encodings of every input and output of the mission: instances $\mathcal I$ (number of variables, then the length-prefixed list of constraints, each a scope and a table), instance–coin pairs, assignments, lists of assignments, instance–integer pairs, explicit families with labelled coordinates, orientations, recovery inputs $(\mathcal I,b,S)$, walk inputs $(\mathcal I,\tau,r,g,\delta,\xi)$, ball inputs $(\mathcal I,\tau,r)$, moment vectors, weighted CNFs, pins, Gram matrices, and instance–$\zeta$ pairs.
--
--   Every encoding is injective (checked in the mission's verification file) and uses no unary numbers, so the length of an encoding is the usual bit size of the object.
--
--   **Formalization Note** The paper names no machine model; Mathlib's `Turing.TM2ComputableInPolyTime` and `Turing.TM2OutputsInTime` are used over these encodings.
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Theorem 1.1, p.4 ("randomized polynomial-time algorithm"); §1.2, p.3 ("All algorithms below output assignments and run in randomized polynomial time")

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_AcceptSubcube_GInst

namespace AcceptSubcube

open OnlineCRS.Combine

/-- A natural number as one word (binary). -/
def tokNat (n : ℕ) : List (List Sym) := [encNat n]

/-- A rational as one word (reduced numerator with sign, `2`, denominator). -/
def tokRat (q : ℚ) : List (List Sym) := [encRat q]

/-- A bit string (assignment, truth table or coin string) as one word of `0`/`1` symbols. -/
def tokBits (w : List Bool) : List (List Sym) := [w.map bit]

/-- A Boolean as a one-symbol word. -/
def tokBool (b : Bool) : List (List Sym) := [[bit b]]

/-- A length-prefixed list. -/
def tokList {α : Type*} (f : α → List (List Sym)) (l : List α) : List (List Sym) :=
  encNat l.length :: l.flatMap f

/-- A pair: the words of the first component, then those of the second. -/
def tokPair {α β : Type*} (f : α → List (List Sym)) (g : β → List (List Sym)) (x : α × β) :
    List (List Sym) :=
  f x.1 ++ g x.2

/-- An optional value: `0` for none, `1` followed by the value. -/
def tokOpt {α : Type*} (f : α → List (List Sym)) : Option α → List (List Sym)
  | none => [encNat 0]
  | some a => encNat 1 :: f a

/-- A constraint: its scope (length-prefixed list of variable indices) and its truth table. -/
def tokCons : List ℕ × List Bool → List (List Sym) := tokPair (tokList tokNat) tokBits

/-- An instance: `n`, then the length-prefixed list of constraints. -/
def tokInst (I : GInst) : List (List Sym) := tokNat I.n ++ tokList tokCons I.cons

/-- Words joined by the separator symbol `3` (no word contains `3`). -/
def enc {α : Type*} (tok : α → List (List Sym)) (a : α) : List Sym :=
  [(3 : Sym)].intercalate (tok a)

/-- **Binary encoding of an instance** (input of the deterministic machines).

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Theorem 1.1, p.4 ("randomized polynomial-time
algorithm"); §1.2, p.3 ("All algorithms below output assignments and run in randomized polynomial
time").

**Formalization Note.** The paper names no machine model. Polynomial time is read in Mathlib's
`Turing.TM2ComputableInPolyTime` (and, for per-input bounds, `Turing.TM2OutputsInTime`), over the
published alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`, `1` bits, `2` inside a rational, `3`
separator). Numbers are binary (`encNat`, `encRat`), lists are length-prefixed, words are
joined by `3`, and no word contains `3`; no number is unary, so the length of an encoding is the
usual bit size. Every encoder of the mission is `enc` of a token map built from `tokNat`, `tokRat`,
`tokBits`, `tokBool`, `tokList`, `tokPair`, `tokOpt` (all injective; checked in
`Solutions/verification/AcceptSubcube_sanity.lean`). -/
def encInst : GInst → List Sym := enc tokInst

/-- Instance and coin string (input of the randomized machine of Theorem 1.1). -/
def encInstCoins : GInst × List Bool → List Sym := enc (tokPair tokInst tokBits)

/-- An assignment (output of every algorithm). -/
def encAssign : List Bool → List Sym := enc tokBits

/-- A list of assignments (output of enumeration and recovery). -/
def encAssignList : List (List Bool) → List Sym := enc (tokList tokBits)

/-- "Unsatisfiable" (`none`) or a satisfying assignment (Lemma 3.1, last clause). -/
def encOptAssign : Option (List Bool) → List Sym := enc (tokOpt tokBits)

/-- Instance and an integer (`K` of Lemma 3.1, `B₀` of Theorem 5.1(a)). -/
def encInstNat : GInst × ℕ → List Sym := enc (tokPair tokInst tokNat)

/-- A labeled coordinate set `T` and a family of patterns on it (input of Lemma 3.2). -/
def encTF : List ℕ × List (List Bool) → List Sym := enc (tokPair (tokList tokNat) (tokList tokBits))

/-- An orientation as its list of directed edges `(tail, direction)` (output of Lemma 3.2). -/
def encOrient : List (List Bool × ℕ) → List Sym := enc (tokList (tokPair tokBits tokNat))

/-- Instance, budget `b` and drawn set `S` (sorted list) (input of the recovery procedure). -/
def encRecIn : GInst × ℕ × List ℕ → List Sym :=
  enc (tokPair tokInst (tokPair tokNat (tokList tokNat)))

/-- Tokens of the walk input `(I, τ, r, g, δ, ξ)` of Lemma 3.6. -/
def tokWalk : GInst × List Bool × ℕ × ℕ × ℚ × ℚ → List (List Sym) :=
  tokPair tokInst (tokPair tokBits (tokPair tokNat (tokPair tokNat (tokPair tokRat tokRat))))

/-- Walk input `(I, τ, r, g, δ, ξ)` (Lemma 3.6). -/
def encWalk : GInst × List Bool × ℕ × ℕ × ℚ × ℚ → List Sym := enc tokWalk

/-- Walk input with a coin string. -/
def encWalkCoins : (GInst × List Bool × ℕ × ℕ × ℚ × ℚ) × List Bool → List Sym :=
  enc (tokPair tokWalk tokBits)

/-- Tokens of a ball instance `(I, τ, r)`. -/
def tokBall : GInst × List Bool × ℕ → List (List Sym) :=
  tokPair tokInst (tokPair tokBits tokNat)

/-- Ball instance `(I, τ, r)` (Lemma 4.3, Theorem 4.1). -/
def encBall : GInst × List Bool × ℕ → List Sym := enc tokBall

/-- Ball instance with a coin string (Theorem 4.1). -/
def encBallCoins : (GInst × List Bool × ℕ) × List Bool → List Sym :=
  enc (tokPair tokBall tokBits)

/-- Tokens of a moment vector: a list of (variable set as a list, rational moment). -/
def tokMom : List (List ℕ × ℚ) → List (List Sym) := tokList (tokPair (tokList tokNat) tokRat)

/-- A rational point of the relaxation, as its moment list (Lemmas 4.4, 4.5, 4.7). -/
def encMom : List (List ℕ × ℚ) → List Sym := enc tokMom

/-- Tokens of a weighted CNF: a list of (weight, list of literals `(variable, sign)`). -/
def tokCNF : List (ℚ × List (ℕ × Bool)) → List (List Sym) :=
  tokList (tokPair tokRat (tokList (tokPair tokNat tokBool)))

/-- A weighted unary/binary CNF (Lemmas 4.4–4.6). -/
def encCNF : List (ℚ × List (ℕ × Bool)) → List Sym := enc tokCNF

/-- Instance, radius `r` and a rational point (input of Lemma 4.4). -/
def encChargeIn : GInst × ℕ × List (List ℕ × ℚ) → List Sym :=
  enc (tokPair tokInst (tokPair tokNat tokMom))

/-- Number of variables `q`, formula and laws (input of Lemma 4.5). -/
def encPinIn : ℕ × List (ℚ × List (ℕ × Bool)) × List (List ℕ × ℚ) → List Sym :=
  enc (tokPair tokNat (tokPair tokCNF tokMom))

/-- A list of pins `(variable, value)` (output of Lemma 4.5). -/
def encPins : List (ℕ × Bool) → List Sym := enc (tokList (tokPair tokNat tokBool))

/-- Tokens of the rounding input `(q, Φ, G)` of Lemma 4.6 (`G` the Gram matrix by rows). -/
def tokRoundData : ℕ × List (ℚ × List (ℕ × Bool)) × List (List ℚ) → List (List Sym) :=
  tokPair tokNat (tokPair tokCNF (tokList (tokList tokRat)))

/-- Rounding input `(q, Φ, G)` (Lemma 4.6). -/
def encRoundData : ℕ × List (ℚ × List (ℕ × Bool)) × List (List ℚ) → List Sym := enc tokRoundData

/-- Rounding input with a coin string (Lemma 4.6). -/
def encRoundCoins : (ℕ × List (ℚ × List (ℕ × Bool)) × List (List ℚ)) × List Bool → List Sym :=
  enc (tokPair tokRoundData tokBits)

/-- Ball instance and accuracy `ϵ_num` (input of Lemma 4.7). -/
def encSDPIn : GInst × List Bool × ℕ × ℚ → List Sym :=
  enc (tokPair tokInst (tokPair tokBits (tokPair tokNat tokRat)))

/-- Instance and failure parameter `ζ` (Theorem 5.1; the coin length is a polynomial of its
length). -/
def encInstRat : GInst × ℚ → List Sym := enc (tokPair tokInst tokRat)

/-- Instance, failure parameter `ζ` and a coin string (Theorem 5.1). -/
def encInstRatCoins : (GInst × ℚ) × List Bool → List Sym :=
  enc (tokPair (tokPair tokInst tokRat) tokBits)

end AcceptSubcube


