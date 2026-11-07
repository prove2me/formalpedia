-- Prove2me | Definitions.Def_DisjointPathsDAG_Encoding
-- name    : DisjointPathsDAG_Encoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:53.068209+00:00
-- url     : https://prove2.me/theorems/8fef32a4-fd99-49bd-8d46-72aa5f919226
-- title:
--   Input and output layouts, and the guarantees of reporting and decision algorithms
-- statement:
--   Instances are written for the machine as follows. Input words: $n$, $m$, the pairs $s_0,t_0,\dots,s_{k-1},t_{k-1}$, and $\mathrm{tail}(e),\mathrm{head}(e)$ for every edge in index order; for the setting of Theorem 4.1 they are followed by the membership bits $[e\in H_i]$. Real inputs: the edge weights (for k-DSP). The input of the extraction step of Lemma 3.4 lists $j$, $M$, the cut bits and the circuit, with $\xi$ and the circuit's constants in field cells.
--
--   The output words are a flag ($0$ means "no") followed, for each $i$, by the length of $P_i$ and its edge indices; an output is a **solution** only if every index is an edge and the tuple of edges is a solution, so malformed output is an invalid tuple, never "no".
--
--   A reporting algorithm **reports within** time $T$ with success probability $p$ if its running time is measurable with expectation at most $T$, every halting run returns "no" or a solution, every halting run returns "no" on an infeasible instance, and on a feasible instance it halts with a solution with probability at least $p$. A decision algorithm **decides within** $T$ if on every tape its running time is at most $T$, it never answers "yes" on an infeasible instance, and on a feasible one it answers "yes" with probability at least $p$.
--
--   These predicates state the guarantees of Proposition 4.6 and Theorem 4.7.
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Section 1, p.2; Proposition 4.6, p.20; Theorem 4.7, p.21; Lemma 3.4, pp.9–10

import Mathlib
import Definitions.Def_DisjointPathsDAG_Graph
import Definitions.Def_DisjointPathsDAG_Machine
import Definitions.Def_DisjointPathsDAG_Regional

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace DisjointPathsDAG

/-!
# Input and output layouts, and the guarantees of a randomized algorithm

Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Section 1, p.2 (the problems), Proposition
4.6, p.20 and Theorem 4.7, p.21 (the guarantees: "never returns an invalid tuple, returns no on every
infeasible instance, and reports a solution with probability at least …"; "Decision with the same
one-sided error has the same worst-case time bound").

**Formalization Note** This module bundles the input encodings, the output decoder and the two
guarantee predicates used by Proposition 4.6 and Theorem 4.7.
* Input words: `n`, `m`, then `sᵢ, tᵢ` for `i = 0, …, k − 1`, then `tail e, head e` for every edge `e`
  in index order; for the setting of Theorem 4.1 they are followed by the membership bits
  `[e ∈ Hᵢ]` (edge-major, label-minor). Real inputs: the edge weights in index order (k-DSP); none for
  k-DP and for the setting of Theorem 4.1. No field inputs. `k` is fixed, so it is not an input.
* Output: the output words are a flag (`0` = "no"), then, for `i = 0, …, k − 1`, the length of `Pᵢ`
  followed by its edge indices. A flag `≠ 0` always decodes to a tuple of lists of naturals; such an
  output is a *solution* only if every index is an edge (`< m`) and the tuple of edges is a solution
  (`liftSol`), so malformed output decodes to an invalid tuple, never to "no".
* The input of the extraction step of Lemma 3.4 (`extractInput`): words `j`, `M`, the cut bits and the
  circuit; field cells `ξ` then the circuit's constants.
* Expected running time is the lower Lebesgue integral of `haltTime` (`ℕ∞`, `⊤` on runs that never
  halt) against the tape law; measurability of the running time and of the success event is part of
  each guarantee. Correctness is required on **every** halting run; the decision bound is worst case.
-/

variable {n m k : ℕ}

/-- The words of a graph with terminal pairs: `n, m, s₀, t₀, …, tail 0, head 0, …`. -/
def graphWords (G : Digraph n m) (pairs : Fin k → Fin n × Fin n) : List ℕ :=
  [n, m] ++ (List.finRange k).flatMap (fun i => [((pairs i).1 : ℕ), ((pairs i).2 : ℕ)]) ++
    (List.finRange m).flatMap (fun e => [(G.tail e : ℕ), (G.head e : ℕ)])

/-- The input of a k-DSP instance: the graph words and the edge weights as reals. -/
def encodeDSP (F : Type) (G : Digraph n m) (wt : Fin m → ℝ) (pairs : Fin k → Fin n × Fin n) :
    Input F :=
  ⟨graphWords G pairs, (List.finRange m).map wt, []⟩

/-- The input of a k-DP instance: the graph words only. -/
def encodeDP (F : Type) (G : Digraph n m) (pairs : Fin k → Fin n × Fin n) : Input F :=
  ⟨graphWords G pairs, [], []⟩

/-- The words of an instance of the setting of Theorem 4.1: the graph words, then the membership
bits `[e ∈ Hᵢ]` for every edge `e` and label `i`. -/
noncomputable def encodeInst (S : Setting n m k) : List ℕ := by
  classical
  exact graphWords S.G S.pairs ++
    (List.finRange m).flatMap (fun e => (List.finRange k).map fun i => if e ∈ S.H i then 1 else 0)

/-- Read `c` length-prefixed lists from a word list (missing words read as empty). -/
def parseLists : ℕ → List ℕ → List (List ℕ)
  | 0, _ => []
  | c + 1, [] => [] :: parseLists c []
  | c + 1, l :: rest => (rest.take l) :: parseLists c (rest.drop l)

/-- Decode output words: `none` ("no") iff the first word is `0` (or the output is empty);
otherwise the tuple of the next `k` length-prefixed lists. -/
def decodePaths (k : ℕ) (ws : List ℕ) : Option (Fin k → List ℕ) :=
  if ws.headD 0 = 0 then none else some fun i => (parseLists k ws.tail).getD i []

/-- A decoded tuple of index lists is a solution for the predicate `Sol` on edge tuples: every index
is an edge and the tuple of edges satisfies `Sol`. -/
def liftSol (Sol : (Fin k → List (Fin m)) → Prop) (P : Fin k → List ℕ) : Prop :=
  ∃ P' : Fin k → List (Fin m), (fun i => (P' i).map Fin.val) = P ∧ Sol P'

/-- The guarantees of a reporting algorithm `Prog` run with width `w` over the field `F` on the input
`I`: measurable running time with expectation at most `T`; every halting run outputs "no" or a
solution (`Sol`); every halting run outputs "no" when the instance is infeasible; and, when it is
feasible, the run halts with a solution with probability at least `p`. -/
def ReportsWithin (k : ℕ) (Prog : Program) (w : ℕ) (F : Type) [Field F] [Finite F] (I : Input F)
    (T : ℝ) (Sol : (Fin k → List ℕ) → Prop) (feasible : Prop) (p : ℝ) : Prop :=
  Measurable (fun ω => (haltTime w F Prog I ω : ℝ≥0∞)) ∧
  ∫⁻ ω, (haltTime w F Prog I ω : ℝ≥0∞) ∂(tapeLaw F) ≤ ENNReal.ofReal T ∧
  (∀ (ω : Tape F) (t : ℕ), HaltsAt w F Prog I ω t →
    ∀ P, decodePaths k (outWords I (stateAt w F Prog I ω t)) = some P → Sol P) ∧
  (¬ feasible → ∀ (ω : Tape F) (t : ℕ), HaltsAt w F Prog I ω t →
    decodePaths k (outWords I (stateAt w F Prog I ω t)) = none) ∧
  (feasible →
    MeasurableSet {ω : Tape F | ∃ t, HaltsAt w F Prog I ω t ∧
      ∃ P, decodePaths k (outWords I (stateAt w F Prog I ω t)) = some P ∧ Sol P} ∧
    ENNReal.ofReal p ≤ tapeLaw F {ω : Tape F | ∃ t, HaltsAt w F Prog I ω t ∧
      ∃ P, decodePaths k (outWords I (stateAt w F Prog I ω t)) = some P ∧ Sol P})

/-- The guarantees of a decision algorithm `Prog` (width `w`, field `F`, input `I`): on **every** tape
the running time is at most `T`; it never answers "yes" on an infeasible instance; on a feasible one
it halts with "yes" with probability at least `p`. -/
def DecidesWithin (Prog : Program) (w : ℕ) (F : Type) [Field F] [Finite F] (I : Input F) (T : ℝ)
    (feasible : Prop) (p : ℝ) : Prop :=
  (∀ ω : Tape F, (haltTime w F Prog I ω : ℝ≥0∞) ≤ ENNReal.ofReal T) ∧
  (¬ feasible → ∀ (ω : Tape F) (t : ℕ), HaltsAt w F Prog I ω t →
    ¬ answerYes I (stateAt w F Prog I ω t)) ∧
  (feasible →
    MeasurableSet {ω : Tape F | ∃ t, HaltsAt w F Prog I ω t ∧ answerYes I (stateAt w F Prog I ω t)} ∧
    ENNReal.ofReal p ≤
      tapeLaw F {ω : Tape F | ∃ t, HaltsAt w F Prog I ω t ∧ answerYes I (stateAt w F Prog I ω t)})

/-- The input of the extraction step of Lemma 3.4: words `j`, `M`, the cut bits `[e ∈ cut]` for
`e < M`, and the encoding of the circuit `P`; field cells `ξ 0, …, ξ (M − 1)` followed by the
constants `cs` of `P`. -/
noncomputable def extractInput {V : Type} [DecidableEq V] {M : ℕ} {F : Type} (ends : Fin M → V × V)
    (L U : Finset V) (j : ℕ) (P : SLP) (ξ : Fin M → F) (cs : List F) : Input F := by
  classical
  exact ⟨j :: M :: ((List.finRange M).map fun e => if e ∈ cutEdges ends L U then 1 else 0) ++ P.encode,
    [], (List.finRange M).map ξ ++ cs⟩

end DisjointPathsDAG


