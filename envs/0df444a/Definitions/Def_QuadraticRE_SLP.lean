-- Prove2me | Definitions.Def_QuadraticRE_SLP
-- name    : QuadraticRE_SLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:04:25.662125+00:00
-- url     : https://prove2.me/theorems/a38d02ff-56ec-4ee5-951f-24659ee3a1e4
-- title:
--   Straight-line programs over $\mathbb F_2$
-- statement:
--   A **straight-line program** over $\mathbb F_2$ is a list of gates, each an input variable, the constant $1$, or the sum or product of two earlier gates, together with a choice of output gates. It computes a map from its inputs to its outputs, and its **size** is the number of gates.
--
--   This is how "uses $O(\cdot)$ operations over $\mathbb F_2$" is read in the mission: as the size of a straight-line program computing the map exactly.
--
--   **Formalization Note** Gates refer to earlier gates by position, and well-formedness is part of the structure. There is no branching, so an operation count is never cheapened by control flow; the $h\times 3$ rank test of the decoder still has a linear-size program.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Propositions 4.2 and 4.4, pp.18–20; "Choosing the parameters", pp.28–29; Lemma 4.11, p.29

import Mathlib
import Definitions.Def_QuadraticRE_SD

namespace QuadraticRE

/-- A gate of a straight-line program over `F₂`: an input, the constant `1`, or the sum or product of
two earlier gates, referred to by position. -/
inductive Gate (ι : Type) where
  | input (i : ι) : Gate ι
  | one : Gate ι
  | add (g g' : ℕ) : Gate ι
  | mul (g g' : ℕ) : Gate ι

/-- A gate only refers to earlier gates. -/
def Gate.WF {ι : Type} (k : ℕ) : Gate ι → Prop
  | .input _ => True
  | .one => True
  | .add g g' => g < k ∧ g' < k
  | .mul g g' => g < k ∧ g' < k

/-- A straight-line program over `F₂` with inputs `ι` and outputs `κ`.

**Formalization Note.** This is the reading of "`O(·)` operations over `F₂`" in
Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), Propositions 4.2 and 4.4, the parameter display pp.28–29 and Lemma 4.11: a Turing machine cannot
meet those linear bounds, and an SLP pays for each operation and has no branching. -/
structure SLP (ι κ : Type) where
  gates : List (Gate ι)
  outs : κ → ℕ
  wf : ∀ (k : ℕ) (hk : k < gates.length), (gates[k]).WF k
  outs_lt : ∀ o, outs o < gates.length

/-- The number of operations: the number of gates. -/
def SLP.size {ι κ : Type} (P : SLP ι κ) : ℕ := P.gates.length

/-- The value of one gate, given the values of the earlier gates. -/
def Gate.val {ι : Type} (x : ι → F2) (vals : List F2) : Gate ι → F2
  | .input i => x i
  | .one => 1
  | .add g g' => vals.getD g 0 + vals.getD g' 0
  | .mul g g' => vals.getD g 0 * vals.getD g' 0

/-- The values of all gates, in order. -/
def SLP.values {ι κ : Type} (P : SLP ι κ) (x : ι → F2) : List F2 :=
  P.gates.foldl (fun vals g => vals ++ [g.val x vals]) []

/-- The map computed by an SLP. -/
def SLP.eval {ι κ : Type} (P : SLP ι κ) (x : ι → F2) (o : κ) : F2 :=
  (P.values x).getD (P.outs o) 0

end QuadraticRE


