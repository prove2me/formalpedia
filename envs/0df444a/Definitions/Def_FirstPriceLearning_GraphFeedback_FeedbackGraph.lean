-- Prove2me | Definitions.Def_FirstPriceLearning_GraphFeedback_FeedbackGraph
-- name    : FirstPriceLearning_GraphFeedback_FeedbackGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:15.052513+00:00
-- url     : https://prove2.me/theorems/b96ced48-ba80-45dc-9c08-0a5e9b52c34b
-- title:
--   Directed feedback graphs: independent sets, independence number, DAGs, revealed sets, weak domination
-- statement:
--   This module fixes the vocabulary of directed feedback graphs used in §3.1 and Appendix A of Han, Zhou and Weissman.
--
--   A directed graph on a vertex set $V$ is a relation $E \subseteq V \times V$; the pair $(a,b) \in E$ is an edge from $a$ to $b$, and $b$ is then a child (out-neighbour) of $a$. In the bandit models of the paper the vertices are actions and the edge $(a,b)$ means that playing $a$ reveals the reward of $b$. The module defines:
--
--   1. **Independent set.** A finite set $S \subseteq V$ is independent if $(a,b) \notin E$ for all distinct $a, b \in S$.
--   2. **Independence number at most $\alpha$.** Every independent set has at most $\alpha$ elements. The independence number of $G$ (p. 11) is the least such $\alpha$, i.e. the largest size of an independent set.
--   3. **No self-loops.** $(a,a) \notin E$ for every vertex $a$ (p. 11: the self-loops are removed).
--   4. **Directed acyclic graph (DAG).** No vertex can reach itself along a nonempty directed path of edges.
--   5. **Revealed set.** When $a$ is played, the revealed actions are $I = \{a\} \cup \{b : (a,b) \in E\}$.
--   6. **Weakly dominating set** (Remark 4, p. 35). A finite set $S$ such that every vertex is in $S$ or is a child of some vertex of $S$.
--   7. **Out-degree in a restriction.** For a finite set $S$ and a vertex $a$, the number of $b \in S$ with $(a,b) \in E$: the out-degree of $a$ in the restriction $G_0$ of $G$ to $S$ when $a \in S$.
--
--   These notions state Lemma 10 and the action rules of Algorithms 1 and 2 (Option I: largest out-degree in $G_0$; Option II: in-degree zero in $G_0$).
--
--   **Formalization Note** The graph is a relation `E : V → V → Prop`. The theorems of the mission assume "independence number at most $\alpha$"; their bounds increase with $\alpha$, so this is equivalent to assuming that the independence number equals $\alpha$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 11 (independence number, self-loops), p. 12 (DAG), p. 35, Remark 4 (weakly dominating set)

import Mathlib

namespace FirstPriceLearning.GraphFeedback

/-! Directed feedback graphs (Han, Zhou, Weissman, arXiv:2003.09795v7, §3.1, p. 11, and App. A,
p. 35). A directed graph on a vertex type `V` is a relation `E : V → V → Prop`; `E a b` is the
edge `(a, b)`. In the bandit models of the paper the edge `(a, b)` means "playing `a` reveals the
reward of `b`", so the out-neighbours of `a` are revealed. -/

/-- A finite vertex set `S` is independent in `E`: no edge `(a, b) ∈ E` joins two distinct
members of `S` (p. 11: `(a_i, a_j) ∉ E` for all `i ≠ j`). -/
def IsIndependentSet {V : Type} (E : V → V → Prop) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ E a b

/-- The independence number of `E` is at most `α`: every independent vertex set has at most `α`
elements. (The independence number of p. 11 is the least such `α`.) -/
def IndepNumberLE {V : Type} (E : V → V → Prop) (α : ℕ) : Prop :=
  ∀ S : Finset V, IsIndependentSet E S → S.card ≤ α

/-- `E` has no self-loops (p. 11: "we manually take out all self loops"). -/
def NoSelfLoops {V : Type} (E : V → V → Prop) : Prop :=
  ∀ a, ¬ E a a

/-- `E` is a directed acyclic graph (DAG): there is no directed cycle, i.e. no vertex reaches
itself by a nonempty path of edges (p. 12). -/
def IsDAG {V : Type} (E : V → V → Prop) : Prop :=
  ∀ a, ¬ Relation.TransGen E a a

/-- The vertices revealed when `a` is played: `b ∈ I = {a} ∪ {b : (a, b) ∈ E}`. -/
def Revealed {V : Type} (E : V → V → Prop) (a b : V) : Prop :=
  b = a ∨ E a b

/-- `S` is a weakly dominating set of `E` (Remark 4, p. 35): every vertex is in `S` or is a
child (out-neighbour) of some vertex of `S`. -/
def IsWeaklyDominating {V : Type} (E : V → V → Prop) (S : Finset V) : Prop :=
  ∀ v, v ∈ S ∨ ∃ u ∈ S, E u v

open Classical in
/-- The out-degree of `a` in the restriction of `E` to the vertex set `S`: the number of
`b ∈ S` with `(a, b) ∈ E`. -/
noncomputable def outDegreeIn {V : Type} (E : V → V → Prop) (S : Finset V) (a : V) : ℕ :=
  (S.filter (fun b => E a b)).card

end FirstPriceLearning.GraphFeedback


