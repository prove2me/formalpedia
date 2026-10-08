-- Prove2me | Definitions.Def_WeisfeilerLeman
-- name    : WeisfeilerLeman
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:38.174702+00:00
-- url     : https://prove2.me/theorems/599a332e-4441-4bd4-a48b-3f6c7acecaaf
-- statement:
--   Graphs on n vertices are symmetric, loop-free Boolean adjacency matrices on Fin n, and a graph has diameter two if n>0 and any two distinct vertices are adjacent or share a common neighbour. For a convention (joint or separate) and a tuple length k, the k-dimensional Weisfeiler-Leman style colouring of a k-tuple v of vertices is defined by stages: at stage 0 the colour is the pair of equality pattern and adjacency pattern among the entries of v; at stage t+1 it pairs the stage-t colour of v with a multiset, over all vertices z, of the stage-t colours of the tuples obtained by replacing the ith entry with z. In the joint convention this is one multiset of the k-indexed families of such colours; in the separate convention there is one multiset per coordinate i. The histogram at stage t is the multiset of colours of all k-tuples, and two graphs on n vertices are Equivalent if their histograms agree at every stage t. The block also formalizes computation costs. Graph pairs are encoded as a bit string consisting of a self-delimiting binary encoding of n followed by the two adjacency matrices. Multi-tape Turing machines (at least 3 states and 3 symbols, with left, stay or right moves) start in state 0 with the input on tape 0, halt in state 1 or 2, accept in state 1, and have a halting time defined as the least halting step (0 if never halting). A word RAM has registers, a program of instructions (halt with an answer, jump, compute with a word operation, load, store, branch on zero), and a word width bits(n) that is positive and at most a constant times log2(n+2)+1; it must be able to hold the encoded pair in memory of bits(n)*2^bits(n) bits, with the input packed into memory words. Each word operation is a function on register words that is computed by a Turing machine whose running time is at most constant*(w+1)^exponent on w-bit words. A Model is either a Turing machine or a RAM, with halting, acceptance and time defined accordingly. An input class is either unrestricted or requires both graphs to have diameter two. A model Decides convention k and class p if, for every n and every pair of graphs in the class, it halts on the encoded pair and accepts exactly when the graphs are Equivalent. worstTime is the maximum running time over all pairs in the class on n vertices. MainClaim is a defined proposition, not an established theorem. It asserts that there exist a real c>0 and a threshold k0 such that for every k at least k0, every convention, every input class and every model deciding equivalence for that convention, k and class, there is an n0 such that for all n at least n0 the worst-case running time is at least n^(c*k).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/WeisfeilerLeman.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/WeisfeilerLeman.lean; bytes 16..9062
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace WLTime

inductive Convention where
  | joint | separate
  deriving DecidableEq

def Graph (n : ℕ) :=
  { a : Fin n → Fin n → Bool //
    (∀ x y, a x y = a y x) ∧ (∀ x, a x x = false) }

namespace Graph

def adj {n : ℕ} (G : Graph n) : Fin n → Fin n → Bool := G.val

def diameterTwo {n : ℕ} (G : Graph n) : Prop :=
  0 < n ∧ ∀ x y, x = y ∨ G.adj x y = true ∨
    ∃ z, G.adj x z = true ∧ G.adj z y = true

noncomputable instance (n : ℕ) : Fintype (Graph n) := by
  classical
  unfold Graph
  infer_instance

end Graph

abbrev AtomicColor (k : ℕ) :=
  (Fin k → Fin k → Bool) × (Fin k → Fin k → Bool)

def Color (c : Convention) (k : ℕ) : ℕ → Type
  | 0 => AtomicColor k
  | t + 1 => match c with
    | .joint => Color c k t × Multiset (Fin k → Color c k t)
    | .separate => Color c k t × (Fin k → Multiset (Color c k t))

noncomputable def tupleColor {n : ℕ} (c : Convention) (k : ℕ) (G : Graph n) :
    (t : ℕ) → (Fin k → Fin n) → Color c k t
  | 0, v => (fun i j => decide (v i = v j), fun i j => G.adj (v i) (v j))
  | t + 1, v => match c with
    | .joint => (tupleColor .joint k G t v,
        Finset.univ.val.map (fun z => fun i =>
          tupleColor .joint k G t (Function.update v i z)))
    | .separate => (tupleColor .separate k G t v,
        fun i => Finset.univ.val.map (fun z =>
          tupleColor .separate k G t (Function.update v i z)))

noncomputable def histogram {n : ℕ} (c : Convention) (k : ℕ) (G : Graph n)
    (t : ℕ) : Multiset (Color c k t) :=
  Finset.univ.val.map (tupleColor c k G t)

def Equivalent {n : ℕ} (c : Convention) (k : ℕ) (G H : Graph n) : Prop :=
  ∀ t, histogram c k G t = histogram c k H t

def encodeNat (n : ℕ) : List Bool :=
  let bits := (Nat.digits 2 n).map (fun b => decide (b = 1))
  List.replicate bits.length true ++ [false] ++ bits

def matrixBits {n : ℕ} (G : Graph n) : List Bool :=
  (List.ofFn fun i : Fin n => List.ofFn fun j : Fin n => G.adj i j).flatten

def encodePair {n : ℕ} (G H : Graph n) : List Bool :=
  encodeNat n ++ matrixBits G ++ matrixBits H

inductive Move where
  | left | stay | right
  deriving DecidableEq

def Move.displacement : Move → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

structure TM where
  tapes : ℕ
  states : ℕ
  symbols : ℕ
  tapes_pos : 0 < tapes
  states_ge : 3 ≤ states
  symbols_ge : 3 ≤ symbols
  transition : Fin states → (Fin tapes → Fin symbols) →
    Fin states × (Fin tapes → Fin symbols) × (Fin tapes → Move)

namespace TM

structure Config (M : TM) where
  state : Fin M.states
  head : Fin M.tapes → ℤ
  tape : Fin M.tapes → ℤ → Fin M.symbols

def symbol (M : TM) (b : Bool) : Fin M.symbols :=
  if b then ⟨2, by have := M.symbols_ge; omega⟩ else
    ⟨1, by have := M.symbols_ge; omega⟩

def initial (M : TM) (w : List Bool) : M.Config where
  state := ⟨0, by have := M.states_ge; omega⟩
  head := fun _ => 0
  tape := fun a z => if a.val = 0 ∧ 0 ≤ z ∧ z.toNat < w.length then
    M.symbol (w.getD z.toNat false) else ⟨0, by have := M.symbols_ge; omega⟩

def halted (M : TM) (C : M.Config) : Prop := C.state.val = 1 ∨ C.state.val = 2

instance (M : TM) (C : M.Config) : Decidable (M.halted C) := inferInstanceAs
  (Decidable (C.state.val = 1 ∨ C.state.val = 2))

def step (M : TM) (C : M.Config) : M.Config :=
  if M.halted C then C else
  let tr := M.transition C.state (fun a => C.tape a (C.head a))
  { state := tr.1
    head := fun a => C.head a + (tr.2.2 a).displacement
    tape := fun a z => if z = C.head a then tr.2.1 a else C.tape a z }

def run (M : TM) (w : List Bool) (t : ℕ) : M.Config := M.step^[t] (M.initial w)

def halts (M : TM) (w : List Bool) : Prop := ∃ t, M.halted (M.run w t)

noncomputable def time (M : TM) (w : List Bool) : ℕ := by
  classical
  exact if h : M.halts w then Nat.find h else 0

def accepts (M : TM) (w : List Bool) : Prop :=
  ∃ t, (M.run w t).state.val = 1

def outputs (M : TM) (input output : List Bool) : Prop :=
  M.halts input ∧ ∀ i : Fin output.length,
    (M.run input (M.time input)).tape ⟨0, M.tapes_pos⟩ (i.val : ℤ) =
      M.symbol (output.get i)

end TM

abbrev Word (w : ℕ) := Fin (2 ^ w)

def wordBits {w : ℕ} (a : Word w) : List Bool :=
  List.ofFn (fun i : Fin w => a.val.testBit i.val)

def registerBits {R w : ℕ} (a : Fin R → Word w) : List Bool :=
  (List.ofFn fun i : Fin R => wordBits (a i)).flatten

structure WordOperation (R : ℕ) where
  apply : (w : ℕ) → (Fin R → Word w) → (Fin R → Word w)
  implementation : TM
  exponent : ℕ
  constant : ℕ
  computes : ∀ w a, implementation.outputs
    (encodeNat w ++ registerBits a) (registerBits (apply w a))
  cost : ∀ w (a : Fin R → Word w), implementation.time (encodeNat w ++ registerBits a) ≤
    constant * (w + 1) ^ exponent

inductive RAMInstruction (R P : ℕ) where
  | halt (answer : Bool)
  | jump (pc : Fin P)
  | compute (op : WordOperation R) (next : RAMInstruction R P)
  | load (dest addr : Fin R) (next : RAMInstruction R P)
  | store (addr src : Fin R) (next : RAMInstruction R P)
  | branchZero (reg : Fin R) (yes no : RAMInstruction R P)

structure WordWidth where
  bits : ℕ → ℕ
  positive : ∀ n, 0 < bits n
  bound : ℕ
  logarithmic : ∀ n, bits n ≤ bound * (Nat.log2 (n + 2) + 1)

structure RAM where
  registers : ℕ
  locations : ℕ
  locations_pos : 0 < locations
  width : WordWidth
  program : Fin locations → RAMInstruction registers locations
  input_fits : ∀ n (G H : Graph n),
    (encodePair G H).length ≤ width.bits n * 2 ^ width.bits n

namespace RAM

structure Config (A : RAM) (n : ℕ) where
  pc : Fin A.locations
  registers : Fin A.registers → Word (A.width.bits n)
  memory : Word (A.width.bits n) → Word (A.width.bits n)
  answer : Option Bool

def packedWord (w : ℕ) (input : List Bool) (a : Word w) : Word w :=
  ⟨(∑ i ∈ Finset.range w, if input.getD (w * a.val + i) false then 2 ^ i else 0)
      % (2 ^ w), Nat.mod_lt _ (by positivity)⟩

def initial (A : RAM) (n : ℕ) (w : List Bool) : A.Config n where
  pc := ⟨0, A.locations_pos⟩
  registers := fun _ => ⟨0, by positivity⟩
  memory := packedWord (A.width.bits n) w
  answer := none

def execute (A : RAM) {n : ℕ} :
    RAMInstruction A.registers A.locations → A.Config n → A.Config n
  | .halt b, C => { C with answer := some b }
  | .jump p, C => { C with pc := p }
  | .compute op next, C => A.execute next { C with
      registers := op.apply (A.width.bits n) C.registers }
  | .load dest addr next, C => A.execute next { C with
      registers := Function.update C.registers dest (C.memory (C.registers addr)) }
  | .store addr src next, C => A.execute next { C with
      memory := Function.update C.memory (C.registers addr) (C.registers src) }
  | .branchZero reg yes no, C =>
      if (C.registers reg).val = 0 then A.execute yes C else A.execute no C

def step (A : RAM) {n : ℕ} (C : A.Config n) : A.Config n :=
  match C.answer with
  | some _ => C
  | none => A.execute (A.program C.pc) C

def run (A : RAM) (n : ℕ) (w : List Bool) (t : ℕ) : A.Config n :=
  A.step^[t] (A.initial n w)

def halts (A : RAM) (n : ℕ) (w : List Bool) : Prop :=
  ∃ t, (A.run n w t).answer.isSome = true

noncomputable def time (A : RAM) (n : ℕ) (w : List Bool) : ℕ := by
  classical
  exact if h : A.halts n w then Nat.find h else 0

def accepts (A : RAM) (n : ℕ) (w : List Bool) : Prop :=
  ∃ t, (A.run n w t).answer = some true

end RAM

inductive Model where
  | turing (machine : TM)
  | ram (machine : RAM)

def Model.halts (A : Model) (n : ℕ) (w : List Bool) : Prop := match A with
  | .turing M => M.halts w
  | .ram M => M.halts n w

def Model.accepts (A : Model) (n : ℕ) (w : List Bool) : Prop := match A with
  | .turing M => M.accepts w
  | .ram M => M.accepts n w

noncomputable def Model.time (A : Model) (n : ℕ) (w : List Bool) : ℕ := match A with
  | .turing M => M.time w
  | .ram M => M.time n w

inductive InputClass where
  | unrestricted | diameterTwo
  deriving DecidableEq

def InputClass.contains (p : InputClass) {n : ℕ} (G H : Graph n) : Prop := match p with
  | .unrestricted => True
  | .diameterTwo => G.diameterTwo ∧ H.diameterTwo

def Decides (A : Model) (c : Convention) (k : ℕ) (p : InputClass) : Prop :=
  ∀ n (G H : Graph n), p.contains G H →
    A.halts n (encodePair G H) ∧
      (A.accepts n (encodePair G H) ↔ Equivalent c k G H)

noncomputable def worstTime (A : Model) (p : InputClass) (n : ℕ) : ℕ := by
  classical
  exact Finset.univ.sup (fun pair : Graph n × Graph n =>
    if p.contains pair.1 pair.2 then A.time n (encodePair pair.1 pair.2) else 0)

def MainClaim : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∀ convention : Convention, ∀ p : InputClass, ∀ A : Model,
      Decides A convention k p → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        (n : ℝ) ^ (c * (k : ℝ)) ≤ (worstTime A p n : ℝ)

end WLTime



end OAI


