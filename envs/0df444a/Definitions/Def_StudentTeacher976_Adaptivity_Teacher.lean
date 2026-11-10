-- Prove2me | Definitions.Def_StudentTeacher976_Adaptivity_Teacher
-- name    : StudentTeacher976_Adaptivity_Teacher
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T10:12:21.192986+00:00
-- url     : https://prove2.me/theorems/2eab40a2-5bda-4d2c-946a-5db6813cdef5
-- title:
--   The fixed least-index teacher, actual run, and good pairs
-- statement:
--   Use the bounded witness presentation and normalized tuple student from §3.1. For each batch of candidate tuples, the teacher chooses the least positive coordinate not witnessed in any candidate, and returns its lexicographically least valid witness. The remaining coordinates contain fixed zero fillers, and this common refutation is sent to every query. If all positive coordinates are covered, the teacher returns a terminal result and issues no further reply.
--
--   For $S\subseteq U$ with $|S|=k-1$ and $x\in U\setminus S$, let $X_{S,x}$ be the increasing enumeration of $S\cup\{x\}$. A pair is good exactly when
--
--   $$
--   (S,x)\text{ is good}\quad\Longleftrightarrow\quad
--   \text{the actual fixed-teacher run on }X_{S,x}\text{ never replies at the coordinate of }x.
--   $$
--
--   The run is a recursion for up to $k$ rounds and stops on the first terminal result. It does not build in a $k-1$ reply bound. Least witnesses are selected from a finite lexicographically ordered list of all words of the permitted length; negative instances have no selected witness.
--
--   This supplies the operational good-pair notion used by Claim 3.1. No arbitrary good-pair relation, covering guarantee, or bound on the trace is assumed.
-- source:
--   Ondřej Ježil, Dimitrios Tsintsilidas, STOC 2027 submission #976 (October 2026), §3.1, teacher and good-pair definitions, p.20 (PDF p.20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_Witness

namespace StudentTeacher976.Adaptivity

/-- All words of length n, in lexicographic order with false before true. -/
def wordsOfLength : ℕ → List Word
  | 0 => [[]]
  | n + 1 => (wordsOfLength n).map (false :: ·) ++ (wordsOfLength n).map (true :: ·)

/-- The bounded lexicographically least valid witness; none on negative instances.
No arbitrary default witness can masquerade as a teacher reply. §3.1 p.20. -/
noncomputable def leastWitness {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (x : Word) : Option Word := by
  classical
  exact (wordsOfLength (W.length.eval x.length)).find? fun y => decide (W.test x y)

/-- The minimum uncovered positive index, its least witness and fixed zero fillers.
If every positive coordinate is covered by some query, none records terminal success;
there is no default index and no extra counterexample in that case. §3.1 p.20. -/
noncomputable def teacher {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (X : List Word) (batch : List (List Word)) : Option TupleReply := by
  classical
  exact ((List.range X.length).find? fun j => decide
    ((∃ z, ValidWitness W (X.getD j []) z) ∧
      ¬ ∃ Y ∈ batch, ValidWitness W (X.getD j []) (Y.getD j []))).bind fun j =>
        (leastWitness W (X.getD j [])).map fun z =>
          (j, (List.range X.length).map fun h =>
            if h = j then z else List.replicate (W.length.eval (X.getD h []).length) false)

/-- Nonterminal replies in the actual causal run, allowing up to budget many replies.
After the first terminal result no later round is run. Each reply is copied to all q
queries. The fact that a winning student receives fewer than budget replies is NOT a
part of this definition; it is the content needed in Claim 3.1's proof. -/
noncomputable def fixedTrace {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (f : TupleStudent) (q : ℕ) (X : List Word) : ℕ → List TupleReply
  | 0 => []
  | t + 1 =>
    let replies := fixedTrace W f q X t
    if replies.length < t then replies
    else match teacher W X (normalize W f X t
      (replies.map fun z => List.replicate q z)) with
      | none => replies
      | some z => replies ++ [z]

/-- Ordered tuple X_(S,x); at a fixed length, the lexicographic ordering on List Bool
is the ordinary increasing binary ordering. §3.1 p.20. -/
def orderedInput (S : Finset Word) (x : Word) : List Word :=
  (insert x S).sort (· ≤ ·)

/-- A good pair refers to the actual fixed-teacher execution, not an arbitrary relation
satisfying a covering axiom. All source membership and size conditions are explicit.
Replies are tested through their indexed input, so zero-based indexing is immaterial. -/
def GoodPair {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (n k q : ℕ) (f : TupleStudent) (S : Finset Word) (x : Word) : Prop :=
  S.card = k - 1 ∧ (∀ y ∈ S, y ∈ positiveInputs W n) ∧
    x ∈ positiveInputs W n ∧ x ∉ S ∧
    ∀ z ∈ fixedTrace W f q (orderedInput S x) k,
      (orderedInput S x).getD z.1 [] ≠ x

end StudentTeacher976.Adaptivity


