-- Prove2me | Definitions.Def_WLIdentification
-- name    : WLIdentification
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:37.93508+00:00
-- url     : https://prove2.me/theorems/1e53aff6-0985-444f-8bb1-090e99416d33
-- statement:
--   This block formalizes Weisfeiler-Leman (WL) identification of finite simple graphs and the computational complexity of deciding it. A Graph is a natural number order together with a symmetric, loopless Boolean adjacency relation on Fin order; Isomorphic means a bijection of vertex sets preserving adjacency. For k=1, color refinement is defined: neighborColor assigns at round s a history-carrying color, namely the previous color paired with the multiset of the previous colors of the neighbors, so colors are comparable across graphs, and neighborHistogram is the multiset of all vertex colors. For general k, tupleColor colors k-tuples of vertices, starting from the equality pattern and adjacency pattern among the tuple entries, and at each round pairing the old color with the multiset, over all vertices z, of the whole vector of colors of the k replacements of one coordinate by z (a joint update, not independent marginals); tupleHistogram is the multiset of all tuple colors. Equivalent k G H says the round-s histograms agree for every s, using the k=1 version when k=1 and the tuple version otherwise. Identifies k G says every graph H (of any order) equivalent to G at level k is isomorphic to G, and WLdim G is the infimum of positive k that identify G. The block then defines the language dimensionLanguage of binary words encoding a graph of positive order as a unary order header, a false separator, the row-major adjacency matrix, and a binary numeral k (starting with a true bit, so k>0) such that WLdim G ≤ k; malformed words are excluded. It also gives an explicit deterministic Turing machine model with a finite table of states and symbols, left/stay/right moves, a two-way infinite tape, and halting in states 1 (accept) or 2 (reject), together with definitions of deciding a language within a time bound, InEXPTIME (time 2^(C(n+1)^d)), computing a function in polynomial time, polynomial-time many-one reductions, and EXPTIMEComplete (a language in EXPTIME to which every EXPTIME language reduces). These are definitions only; no complexity result is asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/WLIdentification.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/WLIdentification.lean; bytes 16..5536
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace WLIdentification

structure Graph where
  order : ℕ
  edge : Fin order → Fin order → Bool
  symmetric : ∀ u v, edge u v = edge v u
  loopless : ∀ u, edge u u = false

def Isomorphic (G H : Graph) : Prop :=
  ∃ e : Fin G.order ≃ Fin H.order, ∀ u v, G.edge u v = H.edge (e u) (e v)

/-- Colors retain their full history, and hence are shared between graphs. -/
def NeighborColor : ℕ → Type
  | 0 => Unit
  | s + 1 => NeighborColor s × Multiset (NeighborColor s)

def neighborColor (G : Graph) : (s : ℕ) → Fin G.order → NeighborColor s
  | 0, _ => ()
  | s + 1, v => (neighborColor G s v,
      (Finset.univ.filter (fun w => G.edge v w = true)).val.map (neighborColor G s))

def neighborHistogram (G : Graph) (s : ℕ) : Multiset (NeighborColor s) :=
  Finset.univ.val.map (neighborColor G s)

def TupleColor (k : ℕ) : ℕ → Type
  | 0 => (Fin k → Fin k → Bool) × (Fin k → Fin k → Bool)
  | s + 1 => TupleColor k s × Multiset (Fin k → TupleColor k s)

/-- Joint update: one multiset of whole replacement vectors, not independent marginals. -/
def tupleColor (G : Graph) (k : ℕ) : (s : ℕ) → (Fin k → Fin G.order) → TupleColor k s
  | 0, v => (fun i j => decide (v i = v j), fun i j => G.edge (v i) (v j))
  | s + 1, v => (tupleColor G k s v,
      Finset.univ.val.map (fun z => fun i => tupleColor G k s (Function.update v i z)))

def tupleHistogram (G : Graph) (k s : ℕ) : Multiset (TupleColor k s) :=
  Finset.univ.val.map (tupleColor G k s)

def Equivalent (k : ℕ) (G H : Graph) : Prop :=
  if k = 1 then ∀ s, neighborHistogram G s = neighborHistogram H s
  else ∀ s, tupleHistogram G k s = tupleHistogram H k s

/-- There is no restriction to mates from a graph construction or to a selected order. -/
def Identifies (k : ℕ) (G : Graph) : Prop :=
  ∀ H : Graph, Equivalent k G H → Isomorphic G H

/-- The infimum of the positive identifying dimensions; this set is nonempty for finite G. -/
noncomputable def WLdim (G : Graph) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ Identifies k G}

abbrev Word := List Bool
abbrev BinaryLanguage := Set Word

def binaryValue (bits : Word) : ℕ :=
  bits.foldl (fun z b => 2 * z + if b then 1 else 0) 0

def matrixWord (G : Graph) : Word :=
  (List.ofFn (fun i : Fin G.order => List.ofFn (G.edge i))).flatten

/-- Unary order header, row-major binary matrix, then most-significant-first binary k. -/
def inputWord (G : Graph) (bits : Word) : Word :=
  List.replicate G.order true ++ [false] ++ matrixWord G ++ bits

/-- A malformed word is rejected: membership requires a valid nonempty simple matrix and k>0. -/
def dimensionLanguage : BinaryLanguage :=
  {w | ∃ (G : Graph) (bits : Word),
    0 < G.order ∧ (∃ tail, bits = true :: tail) ∧ 0 < binaryValue bits ∧
    w = inputWord G bits ∧ WLdim G ≤ binaryValue bits}

/- The deterministic local machine model is explicit; no oracle or arbitrary
   state-transition on whole inputs is included. Both alphabets are fixed finite
   types for each machine. Extra symbols and states allow arbitrary finite tables. -/
inductive Move where
  | left | stay | right
  deriving DecidableEq

def Move.displacement : Move → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

structure Machine where
  extraSymbols : ℕ
  extraStates : ℕ
  transition : Fin (extraStates + 3) → Fin (extraSymbols + 3) →
    Fin (extraStates + 3) × Fin (extraSymbols + 3) × Move

structure Configuration (M : Machine) where
  state : Fin (M.extraStates + 3)
  head : ℤ
  tape : ℤ → Fin (M.extraSymbols + 3)

def inputSymbol (M : Machine) (b : Bool) : Fin (M.extraSymbols + 3) :=
  if b then 2 else 1

def initial (M : Machine) (w : Word) : Configuration M where
  state := 0
  head := 0
  tape z := if 0 ≤ z then (w[z.toNat]?).elim 0 (inputSymbol M) else 0

def Halted {M : Machine} (c : Configuration M) : Prop :=
  c.state = 1 ∨ c.state = 2

/-- One read/write/head-movement transition. A halted configuration is frozen. -/
def step (M : Machine) (c : Configuration M) : Configuration M :=
  if c.state = 1 ∨ c.state = 2 then c else
    let t := M.transition c.state (c.tape c.head)
    { state := t.1, head := c.head + t.2.2.displacement,
      tape := Function.update c.tape c.head t.2.1 }

def run (M : Machine) (w : Word) (t : ℕ) : Configuration M :=
  (step M)^[t] (initial M w)

/-- Output is the binary word beginning at origin and ending at its first blank. -/
def Output {M : Machine} (c : Configuration M) (w : Word) : Prop :=
  (∀ i : Fin w.length, c.tape (i.val : ℤ) = inputSymbol M w[i]) ∧
    c.tape (w.length : ℤ) = 0

/-- Uniform genuine executions on every bit word, including malformed graph words. -/
def DecidesWithin (M : Machine) (L : BinaryLanguage) (bound : ℕ → ℕ) : Prop :=
  ∀ w, ∃ t ≤ bound w.length, Halted (run M w t) ∧ ((run M w t).state = 1 ↔ w ∈ L)

def InEXPTIME (L : BinaryLanguage) : Prop :=
  ∃ (M : Machine) (C d : ℕ),
    DecidesWithin M L (fun n => 2 ^ (C * (n + 1) ^ d))

def ComputesWithin (M : Machine) (f : Word → Word) (bound : ℕ → ℕ) : Prop :=
  ∀ w, ∃ t ≤ bound w.length, (run M w t).state = 1 ∧ Output (run M w t) (f w)

def PolytimeManyOne (L S : BinaryLanguage) : Prop :=
  ∃ (f : Word → Word) (M : Machine) (C d : ℕ),
    ComputesWithin M f (fun n => C * (n + 1) ^ d) ∧ ∀ w, w ∈ L ↔ f w ∈ S

def EXPTIMEComplete (S : BinaryLanguage) : Prop :=
  InEXPTIME S ∧ ∀ L : BinaryLanguage, InEXPTIME L → PolytimeManyOne L S



end WLIdentification
end OAI


