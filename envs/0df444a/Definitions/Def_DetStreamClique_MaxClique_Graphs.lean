-- Prove2me | Definitions.Def_DetStreamClique_MaxClique_Graphs
-- name    : DetStreamClique_MaxClique_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:02:19.5586+00:00
-- url     : https://prove2.me/theorems/050b3037-1f7a-4118-a058-0479e5477b59
-- title:
--   Graph streams, approximate cliques and protocol correctness
-- statement:
--   Vertices are $V=\operatorname{Fin}(n)$ and graphs are simple, undirected and unweighted. An insertion-only stream is a list of unordered, distinct, non-loop edges. Its final graph has exactly those edges. For a real approximation ratio $\beta$, a valid approximate output is a finite vertex set $U$ satisfying
--   $$U\text{ is a clique of }G,\qquad |U|\ge\omega(G)/\beta.$$
--
--   Streaming correctness quantifies over every legal stream, hence every graph and every ordering. Protocol correctness quantifies over every pair of edge-disjoint graphs held by Alice and Bob, with output evaluated on their union. A separate predicate requires only that this output always be a clique. The induced-edge construction keeps the ambient vertex set and retains just the original edges whose endpoints lie in the specified subset.
--
--   These predicates connect the generic machine and protocol interfaces to the paper's problem without supplying either party with the other's input. Ratios in theorem statements satisfy $\beta\ge1$; the definitions themselves are total.
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, §1 and §2.1, pp. 2, 6

import Mathlib
import Definitions.Def_DetStreamClique_MaxClique_Machines

open scoped Classical

namespace DetStreamClique.MaxClique

abbrev Graph (n : ℕ) := SimpleGraph (Fin n)
abbrev Edge (n : ℕ) := Sym2 (Fin n)
abbrev GraphStream (n : ℕ) := List (Edge n)

/-- Each undirected edge arrives once; loops are forbidden. -/
def ValidStream {n : ℕ} (xs : GraphStream n) : Prop :=
  xs.Nodup ∧ ∀ e ∈ xs, ¬ e.IsDiag

def streamGraph {n : ℕ} (xs : GraphStream n) : Graph n :=
  SimpleGraph.fromEdgeSet {e | e ∈ xs}

/-- A clique, together with the real-valued approximation guarantee. -/
def ApproxClique {n : ℕ} (β : ℝ) (G : Graph n) (out : Finset (Fin n)) : Prop :=
  G.IsClique (out : Set (Fin n)) ∧ (G.cliqueNum : ℝ) / β ≤ (out.card : ℝ)

def StreamCorrect {n : ℕ} {S : Type}
    (a : StreamingMachine (Edge n) (Finset (Fin n)) S) (β : ℝ) : Prop :=
  ∀ xs, ValidStream xs → ApproxClique β (streamGraph xs) (a.run xs)

def EdgeDisjoint {n : ℕ} (A B : Graph n) : Prop :=
  Disjoint A.edgeSet B.edgeSet

def ProtocolCorrect {n : ℕ} {M : Type}
    (π : OneWayProtocol (Graph n) (Graph n) M (Finset (Fin n))) (β : ℝ) : Prop :=
  ∀ A B, EdgeDisjoint A B → ApproxClique β (A ⊔ B) (π.receive (π.send A) B)

/-- The validity clause alone, with no approximation assumption. -/
def ProtocolCliqueValid {n : ℕ} {M : Type}
    (π : OneWayProtocol (Graph n) (Graph n) M (Finset (Fin n))) : Prop :=
  ∀ A B, EdgeDisjoint A B → (A ⊔ B).IsClique (π.receive (π.send A) B : Set (Fin n))

/-- Induced edges on U, retaining the ambient vertex set. -/
def inducedEdges {n : ℕ} (G : Graph n) (U : Finset (Fin n)) : Graph n where
  Adj u v := G.Adj u v ∧ u ∈ U ∧ v ∈ U
  symm := ⟨by intros u v h; exact ⟨G.symm.symm u v h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro v h; exact G.loopless.irrefl v h.1⟩

end DetStreamClique.MaxClique


