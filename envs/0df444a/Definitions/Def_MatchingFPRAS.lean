-- Prove2me | Definitions.Def_MatchingFPRAS
-- name    : MatchingFPRAS
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:18.440001+00:00
-- url     : https://prove2.me/theorems/6be295e2-372c-4f36-8e14-3d2c89354b75
-- statement:
--   A graph input consists of a vertex count n and a finite set of edges, each stored once as a pair (u,v) of Fin n with u<v. A set M of edges is a perfect matching if it is contained in the edge set and every vertex lies in exactly one edge of M; Z(G) is the number of perfect matchings of G, equal to 1 for the empty graph. The block then fixes a concrete computational model: an 8-symbol tape alphabet (blank 0, bits 1 and 2, delimiter 3, sign markers 4 and 5), binary encodings of naturals, integers (sign then magnitude) and rationals (reduced numerator and positive denominator), and an input encoding listing n, the edge count, the edges sorted lexicographically as numerals, and then the rationals ε and δ. A RandomMachine is a single finite transition table of a Post-Turing machine whose transitions read a state, the tape head symbol and one fair random bit, and either halt or move to a new state with one write or one head move. Running it on a finite prefix of t random bits applies one tick per bit starting in state 0, with halted configurations absorbing, and Outputs(A, input, bits, q) means it has halted with the encoding of q to the right of the head. timeBound(C,d,G,ε,δ) is C times (input length + ⌈1/ε⌉ + ⌈log₂⌈1/δ⌉⌉ + 1)^d. MainStatement is a defined proposition, not an established theorem, asserting the existence of a machine A and constants C>0 and d such that for every graph G and every rational ε in (0,1) and δ in (0,1/2), with t equal to that time bound, every random tape of length t makes A halt with some nonnegative rational output, when Z(G)=0 every tape outputs exactly 0, and the fraction of tapes whose output q satisfies (1-ε)Z(G) ≤ q ≤ (1+ε)Z(G) is at least 1-δ. This is the formal statement of a fully polynomial randomized approximation scheme for counting perfect matchings in arbitrary graphs.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MatchingFPRAS.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MatchingFPRAS.lean; bytes 16..4233
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace MatchingFPRAS

/-- Each unordered edge is represented once, by increasing endpoints. -/
structure GraphInput where
  n : ℕ
  edges : Finset (Fin n × Fin n)
  increasing : ∀ e ∈ edges, e.1 < e.2

/-- Exactly one selected edge is incident to every vertex. -/
def Perfect (G : GraphInput) (M : Finset (Fin G.n × Fin G.n)) : Prop :=
  M ⊆ G.edges ∧ ∀ v : Fin G.n, ∃! e, e ∈ M ∧ (e.1 = v ∨ e.2 = v)

noncomputable def perfectMatchings (G : GraphInput) : Finset (Finset (Fin G.n × Fin G.n)) :=
  by
    classical
    exact G.edges.powerset.filter (Perfect G)

/-- The exact unweighted count, including the empty graph. -/
noncomputable def Z (G : GraphInput) : ℕ := (perfectMatchings G).card

abbrev Symbol := Fin 8

/-- Binary numeral followed by a delimiter. Tape blank is 0; bits use 1 and 2. -/
def encodeNat (n : ℕ) : List Symbol :=
  (Nat.bits n).map (fun b => if b then 2 else 1) ++ [3]

def encodeInt (z : ℤ) : List Symbol :=
  (if z < 0 then [5] else [4]) ++ encodeNat z.natAbs

/-- A rational encoded by its reduced numerator and positive denominator. -/
def encodeRat (q : ℚ) : List Symbol := encodeInt q.num ++ encodeNat q.den

/-- Explicit sparse graph encoding, then the two rational parameters. -/
def encodeInput (G : GraphInput) (ε δ : ℚ) : List Symbol :=
  encodeNat G.n ++ encodeNat G.edges.card ++
    (((G.edges.map toLex.toEmbedding).sort (· ≤ ·)).flatMap fun e =>
      encodeNat (ofLex e).1.val ++ encodeNat (ofLex e).2.val) ++
    encodeRat ε ++ encodeRat δ

/-- A uniform randomized Post-Turing machine: a single finite transition table. -/
structure RandomMachine where
  states : ℕ
  transition : Fin (states + 1) → Symbol → Bool →
    Option (Fin (states + 1) × Turing.TM0.Stmt Symbol)

structure Configuration (A : RandomMachine) where
  state : Option (Fin (A.states + 1))
  tape : Turing.Tape Symbol

/-- A halted configuration is absorbing. Each nonhalting tick is exactly one
write or one move, or the detection of halt. -/
def tick (A : RandomMachine) (c : Configuration A) (bit : Bool) : Configuration A :=
  match c.state with
  | none => c
  | some s => match A.transition s c.tape.head bit with
    | none => ⟨none, c.tape⟩
    | some (s', action) =>
      ⟨some s', match action with
        | .move d => c.tape.move d
        | .write a => c.tape.write a⟩

def initial (A : RandomMachine) (input : List Symbol) : Configuration A :=
  ⟨some 0, Turing.Tape.mk₁ input⟩

/-- Bounded execution on a finite prefix of the random tape. -/
def run (A : RandomMachine) (input : List Symbol) {t : ℕ}
    (bits : Fin t → Bool) : Configuration A :=
  (List.ofFn bits).foldl (tick A) (initial A input)

def Outputs (A : RandomMachine) (input : List Symbol) {t : ℕ}
    (bits : Fin t → Bool) (q : ℚ) : Prop :=
  (run A input bits).state = none ∧
    (run A input bits).tape.right₀ = Turing.ListBlank.mk (encodeRat q)

/-- A fixed-degree polynomial in input bits, ε⁻¹, and log δ⁻¹.
Natural ceilings and binary ceiling-log change this bound only by constants. -/
def timeBound (C d : ℕ) (G : GraphInput) (ε δ : ℚ) : ℕ :=
  C * ((encodeInput G ε δ).length + ⌈ε⁻¹⌉₊ + Nat.clog 2 ⌈δ⁻¹⌉₊ + 1) ^ d

noncomputable def goodTapes (A : RandomMachine) (G : GraphInput) (ε δ : ℚ)
    (t : ℕ) : Finset (Fin t → Bool) := by
  classical
  exact Finset.univ.filter fun bits => ∃ q : ℚ,
    Outputs A (encodeInput G ε δ) bits q ∧
    (1 - ε) * (Z G : ℚ) ≤ q ∧ q ≤ (1 + ε) * (Z G : ℚ)

/-- A uniform approximation scheme using independent fair bits. All tapes halt
within the fixed polynomial bound and return a nonnegative rational.
A zero count always produces encoded zero. -/
def MainStatement : Prop :=
  ∃ (A : RandomMachine) (C d : ℕ), 0 < C ∧
    ∀ (G : GraphInput) (ε δ : ℚ), 0 < ε → ε < 1 → 0 < δ → δ < 1 / 2 →
      let t := timeBound C d G ε δ
      (∀ bits : Fin t → Bool, ∃ q : ℚ, 0 ≤ q ∧ Outputs A (encodeInput G ε δ) bits q) ∧
      (Z G = 0 → ∀ bits : Fin t → Bool, Outputs A (encodeInput G ε δ) bits 0) ∧
      ((goodTapes A G ε δ t).card : ℚ) / (2 : ℚ) ^ t ≥ 1 - δ




end MatchingFPRAS
end OAI


