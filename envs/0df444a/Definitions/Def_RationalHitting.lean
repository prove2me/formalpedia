-- Prove2me | Definitions.Def_RationalHitting
-- name    : RationalHitting
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:14.881979+00:00
-- url     : https://prove2.me/theorems/57e97a70-608c-4d40-be18-628b93ec0008
-- statement:
--   Formulas in n variables are finite expression trees built from the variables, rational constants, binary sums, binary products, and unary inverses, with size counting the nodes. A formula evaluates to a matrix v at a tuple X of n rational d×d matrices, via the rational scalar matrices as constants, when the usual sum and product rules hold and an inverse node's value b is a genuine two-sided inverse of the evaluated operand a (a·b = b·a = 1), so there is no totalized inverse. A formula is Admissible if for some positive d and some tuple it evaluates to some matrix, and Nonzero if it evaluates to a nonzero matrix at some such tuple. An Output for n variables is a positive common dimension together with a list of n-tuples of rational matrices of that dimension. Outputs are encoded as bit strings: natural numbers by a unary length prefix, a zero terminator and little-endian binary digits; rationals by a sign bit, the numerator magnitude and the denominator in reduced form; then the dimension, the number of tuples and all entries. A fixed deterministic Turing machine (TM0 with four tape symbols and finitely many states, no advice) is run on the input of n twos, a one, and s twos, and OutputsWithin means it halts within a given number of steps with the encoded output on the right of its tape. Hits(s,H) means that for every Admissible, Nonzero formula of size at most s, some tuple in H evaluates it to a matrix that is invertible. MainStatement is the defined proposition, not an established theorem, that there exist a machine and positive constants C and k such that for all n,s ≥ 1 there is an output H with dimension and encoded length at most C(n+s+1)^k, produced by the machine within C(n+s+1)^k steps, and satisfying Hits(s,H).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/RationalHitting.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/RationalHitting.lean; bytes 16..4196
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace RationalHitting

universe u

inductive Formula (n : ℕ) where
  | var : Fin n → Formula n
  | const : ℚ → Formula n
  | add : Formula n → Formula n → Formula n
  | mul : Formula n → Formula n → Formula n
  | inv : Formula n → Formula n
  deriving DecidableEq

namespace Formula

def size {n : ℕ} : Formula n → ℕ
  | .var _ | .const _ => 1
  | .add f g | .mul f g => f.size + g.size + 1
  | .inv f => f.size + 1

/-- Evaluation in any rational algebra; a unary inverse requires an actual
    two-sided inverse of the evaluated operand, not a totalized inverse. -/
inductive Eval {n : ℕ} {R : Type u} [Ring R]
    (c : ℚ →+* R) (X : Fin n → R) : Formula n → R → Prop where
  | var (i) : Eval c X (.var i) (X i)
  | const (a) : Eval c X (.const a) (c a)
  | add {f g a b} : Eval c X f a → Eval c X g b → Eval c X (.add f g) (a + b)
  | mul {f g a b} : Eval c X f a → Eval c X g b → Eval c X (.mul f g) (a * b)
  | inv {f a b} : Eval c X f a → a * b = 1 → b * a = 1 → Eval c X (.inv f) b

end Formula

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℚ
abbrev Tuple (n d : ℕ) := Fin n → Mat d

def Evaluates {n d : ℕ} (f : Formula n) (X : Tuple n d) (v : Mat d) : Prop :=
  f.Eval (algebraMap ℚ (Mat d)) X v

def Admissible {n : ℕ} (f : Formula n) : Prop :=
  ∃ d, 0 < d ∧ ∃ (X : Tuple n d), ∃ v, Evaluates f X v

def Nonzero {n : ℕ} (f : Formula n) : Prop :=
  ∃ d, 0 < d ∧ ∃ (X : Tuple n d), ∃ v, Evaluates f X v ∧ v ≠ 0

/-- All output tuples have one common positive dimension. -/
structure Output (n : ℕ) where
  dimension : ℕ
  dimension_pos : 0 < dimension
  tuples : List (Tuple n dimension)

/-- Little-endian unsigned binary, prefixed by a unary bit-length and a zero
    terminator. This is a self-delimiting binary encoding, including zero. -/
def encodeNat (a : ℕ) : List Bool :=
  let ds := (Nat.digits 2 a).map (fun b => b != 0)
  List.replicate ds.length true ++ [false] ++ ds

/-- Sign bit, binary numerator magnitude, and positive binary denominator.
    Rat.num and Rat.den are the canonical reduced numerator and denominator. -/
def encodeRat (a : ℚ) : List Bool :=
  [decide (a.num < 0)] ++ encodeNat a.num.natAbs ++ encodeNat a.den

def encodeTuple {n d : ℕ} (X : Tuple n d) : List Bool :=
  (List.finRange n).flatMap fun i =>
    (List.finRange d).flatMap fun j =>
      (List.finRange d).flatMap fun k => encodeRat (X i j k)

def encodeOutput {n : ℕ} (H : Output n) : List Bool :=
  encodeNat H.dimension ++ encodeNat H.tuples.length ++ H.tuples.flatMap encodeTuple

/-- 0 is blank, 1 and 2 are the two literal binary digits, 3 is work space.
    Fixed finite tape alphabet and finite state space; no advice or oracle. -/
abbrev Alphabet := Fin 4
abbrev Machine (m : ℕ) := Turing.TM0.Machine Alphabet (Fin (m + 1))
abbrev Config (m : ℕ) := Turing.TM0.Cfg Alphabet (Fin (m + 1))

def tapeBit (b : Bool) : Alphabet := if b then 2 else 1

def unaryInput (n s : ℕ) : List Alphabet :=
  List.replicate n 2 ++ [1] ++ List.replicate s 2

/-- Exactly t ordinary deterministic TM0 transitions. -/
def run {m : ℕ} (G : Machine m) : ℕ → Config m → Option (Config m)
  | 0, a => some a
  | t + 1, a => (Turing.TM0.step G a).bind (run G t)

def OutputsWithin {m n : ℕ} (G : Machine m) (s bound : ℕ) (H : Output n) : Prop :=
  ∃ t ≤ bound, ∃ a : Config m,
    run G t (Turing.TM0.init (unaryInput n s)) = some a ∧
    Turing.TM0.step G a = none ∧
    a.Tape.right₀ = Turing.ListBlank.mk ((encodeOutput H).map tapeBit)

def Hits {n : ℕ} (s : ℕ) (H : Output n) : Prop :=
  ∀ f : Formula n, f.size ≤ s → Admissible f → Nonzero f →
    ∃ X ∈ H.tuples, ∃ v, Evaluates f X v ∧ IsUnit v

/-- A fixed polynomial bound on bit time, full binary output length,
and common positive dimension. -/
def MainStatement : Prop :=
  ∃ (m : ℕ) (G : Machine m) (C k : ℕ), 0 < C ∧ 0 < k ∧
    ∀ n s : ℕ, 1 ≤ n → 1 ≤ s → ∃ H : Output n,
      H.dimension ≤ C * (n + s + 1) ^ k ∧
      (encodeOutput H).length ≤ C * (n + s + 1) ^ k ∧
      OutputsWithin G s (C * (n + s + 1) ^ k) H ∧ Hits s H



end RationalHitting
end OAI


