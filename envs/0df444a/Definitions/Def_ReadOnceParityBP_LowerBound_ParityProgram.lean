-- Prove2me | Definitions.Def_ReadOnceParityBP_LowerBound_ParityProgram
-- name    : ReadOnceParityBP_LowerBound_ParityProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:24:53.128885+00:00
-- url     : https://prove2.me/theorems/ade6b16b-0153-4854-ae84-8bf74255cc05
-- title:
--   Read-once parity branching programs
-- statement:
--   Let variables be indexed by a type ι. A parity program P is a finite labelled acyclic multigraph with labels 0, 1, xᵢ, or ¬xᵢ. On each s-to-t edge path the list of tested variable indices is duplicate free, counting either polarity, even if the path is inconsistent on every input. For an assignment a:ι→{0,1}, a path is consistent when every edge label evaluates to one.
--
--   $$P\text{ accepts }a\iff\#\{p:s\leadsto t\mid p\text{ is consistent with }a\}\text{ is odd}.$$
--
--   P computes g when this acceptance condition is equivalent to g(a)=1 for every assignment. Size is the number of edges. This model includes unlayered multigraphs with arbitrary degrees, as required for the lower bound.
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Definition 1.1, p.2, and model discussion p.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_LabelledDAG

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- Edge labels of a parity branching program over variables indexed by `ι`: a constant
`0`/`1`, a variable `x_i`, or a negated variable `¬x_i` (Definition 1.1). -/
inductive BLabel (ι : Type) where
  | const (b : Bool)
  | pos (i : ι)
  | neg (i : ι)

namespace BLabel

variable {ι : Type}

/-- The variable a label reads, if any. -/
def var? : BLabel ι → Option ι
  | const _ => none
  | pos i => some i
  | neg i => some i

/-- The value of a label on an input `a : ι → Bool`. -/
def eval (a : ι → Bool) : BLabel ι → Bool
  | const b => b
  | pos i => a i
  | neg i => !(a i)

end BLabel

/-- Volk, Definition 1.1 (p. 2): a read-once parity branching program (⊕-BP) over variables
indexed by `ι`. It is a finite directed acyclic multigraph with source `s` and target `t`
whose edges are labelled by `0`, `1`, `x_i` or `¬x_i`, such that on every `s → t` path every
variable appears at most once (in either polarity). The restriction is syntactic: it applies
to every `s → t` path, including paths consistent with no input. -/
structure ParityBP (ι : Type) extends LabelledDAG (BLabel ι) where
  readOnce : ∀ p : List (Fin numE), IsWalk graph.tail graph.head p s t →
    (p.filterMap fun e => (label e).var?).Nodup

namespace ParityBP

variable {ι : Type}

/-- The `s → t` paths consistent with the input `a`: every edge label evaluates to `1`. -/
def consistentPaths (P : ParityBP ι) (a : ι → Bool) : Set (List (Fin P.numE)) :=
  {p | IsWalk P.src P.tgt p P.s P.t ∧ ∀ e ∈ p, (P.label e).eval a = true}

/-- The program accepts `a` iff the number of `s → t` paths consistent with `a` is odd.
(The set is finite because the graph is finite and acyclic.) -/
def Accepts (P : ParityBP ι) (a : ι → Bool) : Prop :=
  Odd (P.consistentPaths a).ncard

/-- `P` computes the Boolean function `g`: it accepts exactly the inputs on which `g` is `1`. -/
def Computes (P : ParityBP ι) (g : (ι → Bool) → Bool) : Prop :=
  ∀ a, P.Accepts a ↔ g a = true

end ParityBP

end ReadOnceParityBP.LowerBound


