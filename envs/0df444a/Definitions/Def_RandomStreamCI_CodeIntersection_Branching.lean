-- Prove2me | Definitions.Def_RandomStreamCI_CodeIntersection_Branching
-- name    : RandomStreamCI_CodeIntersection_Branching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:28:52.496189+00:00
-- url     : https://prove2.me/theorems/fdeb4851-7457-4fb4-8cc4-9c8d5aaca06c
-- title:
--   Finite layered transducers and classical streaming execution
-- statement:
--   A general layered transducer has a start state, a time-and-item-controlled transition, and a terminal output map. For Code Intersection the state set has $2^S$ elements and the length is $M$. The reached state is calculated recursively from the actual stream. Edges retain their source state and input label. Vertex and edge posteriors are joint event probabilities divided by their event masses, with zero on unreachable events.
--
--   $$\Pr[B\text{ succeeds}]=\mathbb E_{H,\pi}\,1[\operatorname{Success}(H,B(H,\pi))].$$
--
--   Independent randomized machines are finite PMF mixtures of deterministic machines. This includes arbitrary random tapes through the induced distribution on their finitely many behaviors. Transitions receive no prefix set, full oracle or stream ordering.
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Definition 5, p. 7; analysis notation (9)–(10), pp. 7–8

import Definitions.Def_RandomStreamCI_CodeIntersection_Stream

noncomputable section

namespace RandomStreamCI.CodeIntersection

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- General finite layered deterministic transducer, with an arbitrary output
alphabet. Published Boolean-output decision programs are not the same object. -/
structure LayeredProgram (Input State Output : Type*) (length : ℕ) where
  start : State
  transition : Fin length → State → Input → State
  output : State → Output

/-- Definition 5 (p. 7) for complete oracle streams: length M = n|Σ| and width w, with
states Fin w in every layer. Layer 0's single vertex is `start` (the other states of layer 0
are unreachable). A machine with S bits of memory is a program of width 2^S. -/
abbrev BranchingProgram (n : ℕ) (Alphabet : Type*) [Fintype Alphabet] (w : ℕ) :=
  LayeredProgram (Input n Alphabet) (Fin w) (Option (Word n Alphabet))
    (Fintype.card (Address n Alphabet))

namespace BranchingProgram

variable {n w : ℕ} {Alphabet : Type*} [Fintype Alphabet]

def state (B : BranchingProgram n Alphabet w) (ω : Sample n Alphabet) : ℕ → Fin w
  | 0 => B.start
  | t + 1 => if h : t < Fintype.card (Address n Alphabet) then
      B.transition ⟨t, h⟩ (B.state ω t) (streamItem ω ⟨t, h⟩)
    else B.state ω t

/-- An edge retains the SOURCE state and the complete input label. -/
def edge (B : BranchingProgram n Alphabet w) (ω : Sample n Alphabet)
    (t : Fin (Fintype.card (Address n Alphabet))) : Fin w × Input n Alphabet :=
  (B.state ω t, streamItem ω t)

def success (B : BranchingProgram n Alphabet w) (C : Finset (Word n Alphabet)) : ℝ :=
  streamProbability (fun ω =>
    ValidOutput C ω.1 (B.output (B.state ω (Fintype.card (Address n Alphabet)))))

def vertexEvent [DecidableEq Alphabet] (B : BranchingProgram n Alphabet w) (t : ℕ)
    (v : Fin w) (A : Finset (Address n Alphabet)) (ω : Sample n Alphabet) : Prop :=
  seen ω.2 t = A ∧ B.state ω t = v

def edgeEvent [DecidableEq Alphabet] (B : BranchingProgram n Alphabet w)
    (t : Fin (Fintype.card (Address n Alphabet))) (e : Fin w × Input n Alphabet)
    (A : Finset (Address n Alphabet)) (ω : Sample n Alphabet) : Prop :=
  seen ω.2 (t.val + 1) = A ∧ B.edge ω t = e

def posterior [DecidableEq Alphabet] (B : BranchingProgram n Alphabet w) (t : ℕ)
    (v : Fin w) (A : Finset (Address n Alphabet)) (P : Oracle n Alphabet → Prop) : ℝ :=
  streamProbability (fun ω => B.vertexEvent t v A ω ∧ P ω.1) /
    streamProbability (B.vertexEvent t v A)

def edgePosterior [DecidableEq Alphabet] (B : BranchingProgram n Alphabet w)
    (t : Fin (Fintype.card (Address n Alphabet))) (e : Fin w × Input n Alphabet)
    (A : Finset (Address n Alphabet)) (P : Oracle n Alphabet → Prop) : ℝ :=
  streamProbability (fun ω => B.edgeEvent t e A ω ∧ P ω.1) /
    streamProbability (B.edgeEvent t e A)

/-- Actual posterior law of the restriction H_A; the zero case is not a PMF. -/
def restrictedPosterior [DecidableEq Alphabet] (B : BranchingProgram n Alphabet w) (t : ℕ)
    (v : Fin w) (A : Finset (Address n Alphabet)) (x : A → Bool) : ℝ :=
  B.posterior t v A (fun H => (fun u : A => H u) = x)

/-- Independent private coins, fixed before the input is sampled. All behaviors on
this finite input space form a finite set, so infinite random tapes also induce
such a finite mixture without changing success. -/
def randomizedSuccess {Ω : Type*} [Fintype Ω] (p : PMF Ω)
    (B : Ω → BranchingProgram n Alphabet w) (C : Finset (Word n Alphabet)) : ℝ :=
  ∑ ω, weights p ω * (B ω).success C

end BranchingProgram

end RandomStreamCI.CodeIntersection


