-- Prove2me | Definitions.Def_LabelConnected_Treewidth_CleanUp
-- name    : LabelConnected_Treewidth_CleanUp
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:27:17.713929+00:00
-- url     : https://prove2.me/theorems/2f38500a-ab26-4ecc-84a9-0b784a87fcec
-- title:
--   Clean multigraphs and the Clean-Up Rule, with its exhaustive applications
-- statement:
--   A multigraph is **clean** if it has no loops and every parallel class has at most three edges. The **Clean-Up Rule** deletes a loop, or deletes an arbitrary edge from a parallel class that contains at least four edges.
--
--   Starting from $G$, the rule acts on the current edge set $S \subseteq E(G)$: one application turns $S$ into $S \setminus \{e\}$ for an edge $e \in S$ that is a loop or whose parallel class within $S$ has at least four edges. An **exhaustive application** ends in an edge set $S'$ reachable from $E(G)$ by applications,
--   $$E(G) = S_0 \to S_1 \to \cdots \to S_k = S',$$
--   at which the rule no longer applies; the resulting graph is $G' = (V(G), S')$. Since the deleted edge is arbitrary, any such $S'$ is a result.
--
--   **Formalization Note.** `parallelClass`, `IsClean`, `CleanUpStep`, `IsCleanUpResult` (reflexive-transitive closure from `Finset.univ`, no further step).
-- source:
--   Klasing, Mertzios, Molter, Morawietz, Spirakis, Recognizing Label-Connected Graphs, arXiv:2611.05144 (PDF sha256 8dde27a5…), §5.1, pp. 17–18, the Clean-Up Rule

import Mathlib
import Definitions.Def_LabelConnected_Treewidth_Multigraph

open Classical

namespace LabelConnected.Treewidth

/-! # Clean multigraphs and the Clean-Up Rule

Klasing, Mertzios, Molter, Morawietz, Spirakis, *Recognizing Label-Connected Graphs*,
arXiv:2611.05144 (PDF sha256 8dde27a5…), §5.1, pp. 17–18: "We call a multigraph clean if it has no
loops and every parallel class has at most three edges." "Clean-Up Rule. Delete a loop, or delete an
arbitrary edge from a parallel class that contains at least four edges."

**Formalization Note.** The rule acts on the current edge set `S ⊆ E(G)` (the graph `(V(G), S)`),
starting from `S = E(G)`; one application deletes one edge `e ∈ S` that is a loop or whose parallel class
in `S` has at least four edges. An **exhaustive application** is any edge set reachable from
`E(G)` by applications at which no further application is possible; "arbitrary edge" means every
choice is allowed, so statements about the result quantify over all of them. -/

variable {n : ℕ} {E : Type} [Fintype E] [DecidableEq E]

/-- The parallel class of `e` inside `S`: the edges of `S` with the same unordered endpoint pair. -/
noncomputable def parallelClass (ends : E → Fin n × Fin n) (S : Finset E) (e : E) : Finset E :=
  S.filter fun f => Parallel ends e f

/-- The multigraph is **clean**: no loops, and every parallel class has at most three edges. -/
def IsClean (ends : E → Fin n × Fin n) : Prop :=
  (∀ e, ¬ IsLoop ends e) ∧ ∀ e, (parallelClass ends Finset.univ e).card ≤ 3

/-- One application of the **Clean-Up Rule** to `(V(G), S)`, giving `(V(G), S')`. -/
def CleanUpStep (ends : E → Fin n × Fin n) (S S' : Finset E) : Prop :=
  ∃ e ∈ S, (IsLoop ends e ∨ 4 ≤ (parallelClass ends S e).card) ∧ S' = S.erase e

/-- `S'` is the edge set left by some exhaustive application of the Clean-Up Rule to `G`. -/
def IsCleanUpResult (ends : E → Fin n × Fin n) (S' : Finset E) : Prop :=
  Relation.ReflTransGen (CleanUpStep ends) Finset.univ S' ∧ ¬ ∃ S'', CleanUpStep ends S' S''

end LabelConnected.Treewidth


