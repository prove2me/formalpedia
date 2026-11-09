-- Prove2me | Definitions.Def_IQPForrelation832_SingleQuery_Programs
-- name    : IQPForrelation832_SingleQuery_Programs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T03:06:39.581303+00:00
-- url     : https://prove2.me/theorems/b52fd98b-5bf8-4936-9760-31b890853d89
-- title:
--   Fixed witness decoder and uniform efficient one-query IQP families
-- statement:
--   A witness program has a width and a finite list of $Z$, $CZ$, and joint-query instructions. Width, instruction count and wire indices use terminated unary codes. A fixed structural parser reads these codes and rejects unknown tags or trailing bits; compilation rejects invalid or coinciding $CZ$ wires. A query acts on the first $n+1$ wires and leaves padding wires untouched.
--
--   Validity requires the compiled list to satisfy the generic IQP predicate and to contain exactly one oracle occurrence. A family is efficient on a dimension domain $D$ when one polynomial-time string generator decodes to its programs and one polynomial-time string machine decides acceptance, with absolute natural constants $C,d$ such that
--   $$
--   m_{n,b}+|D_{n,b}|+2m_{n,b}\le C(n+1)^d\quad(n\in D,\ b\in\{0,1\}).
--   $$
--   The two outer layers each use one Hadamard per wire. Polynomial-time computation has the published finite multi-stack Turing-machine semantics, with a polynomial bound on all input strings. Both machines are fixed before dimensions or oracle functions are chosen.
--
--   The fair randomized acceptance is the arithmetic mean of the two operational Born probabilities. This is a sufficient finite witness gate set for the paper's construction; the generic IQP and Proposition 1 models allow arbitrary supplied diagonal implementations.
-- source:
--   Quentin Buzet, André Chailloux, IQP circuits for 2-Forrelation, STOC 2027 submission #832 (October 2026), pp. 3–4, 13 (Definitions 3–4), 17 (Remark 2), 18–20 (Propositions 6–8). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/832.pdf

import Definitions.Def_IQPForrelation832_SingleQuery_Circuits

set_option autoImplicit false

namespace IQPForrelation832.SingleQuery

open QAlgorithms QAlgorithms.Complexity

/-- A sufficient finite witness gate set. Generic IQP circuits use Middle, not this datatype. -/
inductive Instruction where
  | z (wire : ℕ)
  | cz (first second : ℕ)
  | query
  deriving DecidableEq

structure Program where
  wires : ℕ
  body : List Instruction
  deriving DecidableEq

/-- Structural unary parser; rejects missing terminators. -/
def readNat : Str → Option (ℕ × Str)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
    let (k, tail) ← readNat rest
    some (k+1, tail)

def readInstruction (s : Str) : Option (Instruction × Str) := do
  let (tag, rest) ← readNat s
  match tag with
  | 0 => do
    let (i, tail) ← readNat rest
    some (.z i, tail)
  | 1 => do
    let (i, tail) ← readNat rest
    let (j, tail) ← readNat tail
    some (.cz i j, tail)
  | 2 => some (.query, rest)
  | _ => none

def readInstructions : ℕ → Str → Option (List Instruction × Str)
  | 0, s => some ([], s)
  | k+1, s => do
    let (i, rest) ← readInstruction s
    let (is, tail) ← readInstructions k rest
    some (i :: is, tail)

/-- Fixed decoder: width, instruction count, then tagged instructions. Trailing data fails. -/
def decode (s : Str) : Option Program := do
  let (m, rest) ← readNat s
  let (k, rest) ← readNat rest
  let (body, tail) ← readInstructions k rest
  if tail = [] then some ⟨m, body⟩ else none

/-- The query always acts on the first n+1 wires, leaving every padding wire untouched. -/
noncomputable def compileInstruction (n m : ℕ) (i : Instruction) :
    Option (OracleStep Set.univ (fun _ : Fin 1 => n+1) m) :=
  match i with
  | .z w => if h : w < m then
      some (.gate ⟨Gate.ofMatrix1 pauliZ, Set.mem_univ _,
        (show Fin 1 ↪ Fin m from ⟨fun _ => ⟨w,h⟩, fun a b _ => Subsingleton.elim a b⟩)⟩) else none
  | .cz u v => if h : u < m ∧ v < m ∧ u ≠ v then
      some (.gate ⟨Gate.ofMatrix2 (controlled pauliZ), Set.mem_univ _,
        (show Fin 2 ↪ Fin m from ⟨fun j => if j = 0 then ⟨u,h.1⟩ else ⟨v,h.2.1⟩, by
          intro a b e
          fin_cases a <;> fin_cases b <;> simp_all [Fin.ext_iff]
          all_goals omega⟩)⟩) else none
  | .query => if h : n+1 ≤ m then
      some (.query 0 false none ⟨Fin.castLE h, Fin.castLE_injective h⟩ (by simp)) else none

noncomputable def compile (n : ℕ) (p : Program) : Option (Middle n p.wires) :=
  p.body.mapM (compileInstruction n p.wires)

/-- Both layer structure and actual unitarity are enforced; exactly one black-box occurrence. -/
def Valid (n : ℕ) (p : Program) : Prop :=
  n+1 ≤ p.wires ∧ ∃ c, compile n p = some c ∧ IsIQP c ∧
    OracleCircuit.queryCount c 0 = 1

noncomputable def programBorn (n : ℕ) (p : Program) (a : Str → Str) (b : Bool)
    (f g : Cube n → ℝ) : ℝ :=
  match compile n p with
  | none => 0
  | some c => born c (accepts a n b) f g

/-- One generator and one acceptance machine for the entire family. They receive no oracle
truth tables. PolyTimeComputable supplies finite multi-stack machine semantics and uniform
polynomial time bounds, including behavior on malformed strings. -/
def EfficientOn (D : ℕ → Prop) (p : ℕ → Bool → Program) (a : Str → Str) : Prop :=
  PolyTimeComputable a ∧ ∃ generator : Str → Str,
    PolyTimeComputable generator ∧ ∃ C d : ℕ, ∀ n, D n → ∀ b,
      decode (generator (encNat n ++ [b])) = some (p n b) ∧
      Valid n (p n b) ∧
      (p n b).wires + (p n b).body.length + 2*(p n b).wires ≤ C*(n+1)^d

noncomputable def fairBorn (n : ℕ) (p : ℕ → Bool → Program) (a : Str → Str)
    (f g : Cube n → ℝ) : ℝ :=
  (programBorn n (p n false) a false f g + programBorn n (p n true) a true f g) / 2

end IQPForrelation832.SingleQuery


