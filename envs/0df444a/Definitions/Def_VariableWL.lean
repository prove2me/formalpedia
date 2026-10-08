-- Prove2me | Definitions.Def_VariableWL
-- name    : VariableWL
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:37.342771+00:00
-- url     : https://prove2.me/theorems/a83b0789-1cd5-4a64-b1b9-f4744d37ecf0
-- statement:
--   This block formalizes multi-tape Turing machines on binary words and the k-dimensional Weisfeiler-Leman equivalence problem as a language. A Word is a list of booleans. A Machine has a number of states (state indices 0 to states), a number of work symbols, and extraTapes+1 tapes over an alphabet of workSymbols+3 symbols; its transition function maps a state and the tuple of scanned symbols to either nothing (halt) or a new state together with, for each tape, a symbol to write and a head motion left, stay or right (displacement -1, 0, +1). A configuration records the control state, the integer head positions and the doubly infinite tape contents. The input word w is placed on tape 0 at nonnegative positions, with symbol 1 for false, 2 for true and 0 (blank) everywhere else; the start state is 0, all heads are at 0 and the other tapes are blank. run M w n applies the step n times, staying fixed once the machine halts. OutputsWithin(M,w,out,bound) holds if for some t ≤ bound the machine halts at time t and tape 0 then equals exactly the encoding of out, blank elsewhere. InEXPTIME(L) says some machine and constants c, d decide membership in L by outputting [true] or [false] within 2^(c(|w|+1)^d) steps. PolytimeReduces(L,R) says some machine computes within c(|w|+1)^d steps an output out with w ∈ L iff out ∈ R, and EXPTIMEComplete(L) means L is in EXPTIME and every EXPTIME language polytime-reduces to it. A Graph is a finite simple graph on Fin order. For k-tuples of vertices, round-0 colors record the equality and adjacency patterns of all pairs of coordinates, and the round-(s+1) color pairs the round-s color with the multiset, over all vertices z, of the tuples of round-s colors obtained by replacing each coordinate i by z. Two graphs are k-Equivalent when, for every round s, their multisets (histograms) of round-s colors over all k-tuples coincide. Graphs are encoded as words: an integer n is written as a unary block of length equal to its binary-digit list, a false separator, then its binary digits, and a graph is its order code followed by its row-major adjacency matrix; pairCode(G,H,k) concatenates both graph codes and the code of k. WL is the language of such pair codes with k ≥ 2 and G, H k-equivalent. SubWL is the language of pair codes with k ≥ 2 where G has positive order equal to H's, both are connected, both have all degrees at most 3, and G, H are k-equivalent. No hardness or completeness result is asserted here.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/VariableWL.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/VariableWL.lean; bytes 16..4008
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace VariableWL

abbrev Word := List Bool

inductive Motion where
  | left | stay | right
  deriving DecidableEq

def Motion.displacement : Motion → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

structure Machine where
  states : ℕ
  workSymbols : ℕ
  extraTapes : ℕ
  transition : Fin (states + 1) →
    (Fin (extraTapes + 1) → Fin (workSymbols + 3)) →
    Option (Fin (states + 1) ×
      (Fin (extraTapes + 1) → Fin (workSymbols + 3) × Motion))

structure Configuration (M : Machine) where
  control : Fin (M.states + 1)
  heads : Fin (M.extraTapes + 1) → ℤ
  cells : Fin (M.extraTapes + 1) → ℤ → Fin (M.workSymbols + 3)

def wordCells (a : ℕ) (w : Word) (i : ℤ) : Fin (a + 3) :=
  if 0 ≤ i then
    match w[i.toNat]? with
    | none => 0
    | some false => 1
    | some true => 2
  else 0

def initial (M : Machine) (w : Word) : Configuration M where
  control := 0
  heads := fun _ => 0
  cells := fun j => if j = 0 then wordCells M.workSymbols w else fun _ => 0

def scanned {M : Machine} (c : Configuration M) :
    Fin (M.extraTapes + 1) → Fin (M.workSymbols + 3) :=
  fun j => c.cells j (c.heads j)

def step (M : Machine) (c : Configuration M) : Option (Configuration M) :=
  (M.transition c.control (scanned c)).map fun data =>
    { control := data.1
      heads := fun j => c.heads j + (data.2 j).2.displacement
      cells := fun j i => if i = c.heads j then (data.2 j).1 else c.cells j i }

def run (M : Machine) (w : Word) : ℕ → Configuration M
  | 0 => initial M w
  | n + 1 => (step M (run M w n)).getD (run M w n)

def OutputsWithin (M : Machine) (w out : Word) (bound : ℕ) : Prop :=
  ∃ t ≤ bound, step M (run M w t) = none ∧
    (run M w t).cells 0 = wordCells M.workSymbols out

abbrev Language := Set Word

def InEXPTIME (L : Language) : Prop :=
  ∃ M : Machine, ∃ c d : ℕ, ∀ w : Word,
    ∃ b : Bool, (b = true ↔ w ∈ L) ∧
      OutputsWithin M w [b] (2 ^ (c * (w.length + 1) ^ d))

def PolytimeReduces (L R : Language) : Prop :=
  ∃ M : Machine, ∃ c d : ℕ, ∀ w : Word,
    ∃ out : Word, OutputsWithin M w out (c * (w.length + 1) ^ d) ∧
      (w ∈ L ↔ out ∈ R)

def EXPTIMEComplete (L : Language) : Prop :=
  InEXPTIME L ∧ ∀ R : Language, InEXPTIME R → PolytimeReduces R L

structure Graph where
  order : ℕ
  graph : SimpleGraph (Fin order)

abbrev Tuple (G : Graph) (k : ℕ) := Fin k → Fin G.order

def Color (k : ℕ) : ℕ → Type
  | 0 => Fin k → Fin k → Bool × Bool
  | s + 1 => Color k s × Multiset (Fin k → Color k s)

noncomputable def color (G : Graph) (k : ℕ) : (s : ℕ) → Tuple G k → Color k s
  | 0, v => by
      classical
      exact fun i j => (decide (v i = v j), decide (G.graph.Adj (v i) (v j)))
  | s + 1, v => (color G k s v,
      Finset.univ.val.map (fun z => fun i => color G k s (Function.update v i z)))

noncomputable def histogram (G : Graph) (k s : ℕ) : Multiset (Color k s) :=
  Finset.univ.val.map (color G k s)

def Equivalent (G H : Graph) (k : ℕ) : Prop :=
  ∀ s : ℕ, histogram G k s = histogram H k s

def integerCode (n : ℕ) : Word :=
  List.replicate (Nat.bits n).length true ++ [false] ++ Nat.bits n

noncomputable def graphCode (G : Graph) : Word := by
  classical
  exact integerCode G.order ++
    (List.ofFn fun i : Fin G.order =>
      List.ofFn fun j : Fin G.order => decide (G.graph.Adj i j)).flatten

noncomputable def pairCode (G H : Graph) (k : ℕ) : Word :=
  graphCode G ++ graphCode H ++ integerCode k

def WL : Language :=
  { w | ∃ G H : Graph, ∃ k : ℕ, w = pairCode G H k ∧ 2 ≤ k ∧ Equivalent G H k }

noncomputable def Subcubic (G : Graph) : Prop := by
  classical
  exact ∀ v : Fin G.order, G.graph.degree v ≤ 3

def SubWL : Language :=
  { w | ∃ G H : Graph, ∃ k : ℕ, w = pairCode G H k ∧ 2 ≤ k ∧
    0 < G.order ∧ G.order = H.order ∧ G.graph.Connected ∧ H.graph.Connected ∧
    Subcubic G ∧ Subcubic H ∧ Equivalent G H k }



end VariableWL
end OAI


