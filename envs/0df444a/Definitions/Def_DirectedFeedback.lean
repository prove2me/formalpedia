-- Prove2me | Definitions.Def_DirectedFeedback
-- name    : DirectedFeedback
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:07.924282+00:00
-- url     : https://prove2.me/theorems/312f76e8-f860-435a-bb58-b2e51c7cc2e8
-- statement:
--   Natural numbers are encoded in unary as n true bits followed by one false bit; an input/certificate pair is encoded by the unary input length, then the input and certificate bits. An NP verifier consists of a polynomial certificate-length bound and a Boolean verification function computed in polynomial time on that encoding by a deterministic Turing machine with finitely many stacks and control states and finite stack alphabets. It accepts an input when some certificate of length at most the bound evaluated at the input length verifies successfully. A language belongs to InNP when its membership predicate agrees with such acceptance. A digraph has n vertices and an explicit duplicate-free list of arcs, with no loops but with opposite arcs permitted. A directed cycle is a cyclically ordered nonempty list of distinct vertices whose successive arcs, including the closing arc, all occur; two-vertex cycles are allowed. A feedback vertex set meets every such cycle, and dfvs is its minimum possible cardinality. Graph encoding concatenates unary encodings of n, all vertex indices, the arc count, and every arc endpoint, thus explicitly representing isolated vertices too. A gap instance is a graph and a positive integer threshold k, encoded with k first. For a real factor A and language L, a gap reduction constructs these instances in polynomial time in the raw input length using a finite-alphabet machine, with dfvs ≤ k for inputs in L and dfvs > A k for inputs outside L. MainStatement is the defined proposition that such a reduction exists for every real A ≥ 1 and every language in InNP.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DirectedFeedback.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DirectedFeedback.lean; bytes 16..3931
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace DirectedFeedback

/-- Unary self-delimiting natural numbers. Outputs are explicit, not succinct. -/
def natBits (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- The explicit framing used for an input and its NP certificate. -/
def pairBits (p : List Bool × List Bool) : List Bool :=
  natBits p.1.length ++ p.1 ++ p.2

/-- Finitely many stacks and control states are already part of `FinTM2`.
This additionally excludes infinite stack alphabets. -/
def FiniteAlphabet (M : Turing.FinTM2) : Prop := ∀ k, Finite (M.Γ k)

/-- Polynomially bounded certificates checked by an actual deterministic
finite-alphabet machine, on the explicitly encoded input/certificate pair. -/
structure NPVerifier where
  witnessBound : Polynomial ℕ
  verify : (List Bool × List Bool) → Bool
  computation : Turing.TM2ComputableInPolyTime pairBits (fun b : Bool => [b]) verify
  finiteAlphabet : FiniteAlphabet computation.tm

def NPVerifier.Accepts (V : NPVerifier) (input : List Bool) : Prop :=
  ∃ witness : List Bool, witness.length ≤ V.witnessBound.eval input.length ∧
    V.verify (input, witness) = true

/-- NP is defined independently of SAT or any hardness assertion. -/
def InNP (language : List Bool → Prop) : Prop :=
  ∃ V : NPVerifier, ∀ input, language input ↔ V.Accepts input

/-- Finite loopless digraph. Opposite arcs are permitted. Every arc is listed
explicitly. No symmetric closure or undirected-cycle convention is used. -/
structure Digraph where
  n : ℕ
  arcs : List (Fin n × Fin n)
  loopless : ∀ e ∈ arcs, e.1 ≠ e.2
  nodup : arcs.Nodup

namespace Digraph

/-- An actual simple directed cycle of positive length. A cyclic enumeration
of `r + 1` distinct vertices supplies every successive arc, including the
closing arc. A 2-cycle is allowed; looplessness rules out length 1. -/
def IsCycle (G : Digraph) {r : ℕ} (c : Fin (r + 1) → Fin G.n) : Prop :=
  Function.Injective c ∧ ∀ i, (c i, c (i + 1)) ∈ G.arcs

/-- A feedback set intersects EVERY actual directed cycle. -/
def Feedback (G : Digraph) (F : Finset (Fin G.n)) : Prop :=
  ∀ (r : ℕ) (c : Fin (r + 1) → Fin G.n), G.IsCycle c → ∃ i, c i ∈ F

/-- Minimum number of vertices of a feedback set. No weights or auxiliary
cost oracle appear in this definition. -/
noncomputable def dfvs (G : Digraph) : ℕ := by
  classical
  exact Nat.find (show ∃ k : ℕ, ∃ F : Finset (Fin G.n), G.Feedback F ∧ F.card = k from
    ⟨G.n, Finset.univ, by
      intro r c _
      exact ⟨0, Finset.mem_univ _⟩, by simp⟩)

/-- Full explicit vertex and arc serialization, including isolated vertices. -/
def bits (G : Digraph) : List Bool :=
  ([G.n] ++ List.range G.n ++ [G.arcs.length] ++
    G.arcs.flatMap (fun e => [e.1.val, e.2.val])).flatMap natBits

end Digraph

/-- Output includes a strictly positive integer threshold. -/
structure GapInstance where
  graph : Digraph
  k : ℕ
  k_pos : 0 < k

def GapInstance.bits (I : GapInstance) : List Bool :=
  natBits I.k ++ I.graph.bits

/-- A strict YES/NO gap reduction implemented by a finite-alphabet machine
with polynomial runtime in the raw input bit length. -/
structure GapReduction (A : ℝ) (language : List Bool → Prop) where
  construct : List Bool → GapInstance
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    GapInstance.bits construct
  finiteAlphabet : FiniteAlphabet computation.tm
  completeness : ∀ input, language input →
    (construct input).graph.dfvs ≤ (construct input).k
  soundness : ∀ input, ¬ language input →
    A * ((construct input).k : ℝ) < ((construct input).graph.dfvs : ℝ)

/-- Constant-factor directed feedback vertex set hardness for all NP languages. -/
def MainStatement : Prop :=
  ∀ A : ℝ, 1 ≤ A → ∀ language : List Bool → Prop,
    InNP language → Nonempty (GapReduction A language)

end DirectedFeedback



end OAI


