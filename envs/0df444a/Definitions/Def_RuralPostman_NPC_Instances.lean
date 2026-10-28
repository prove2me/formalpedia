-- Prove2me | Definitions.Def_RuralPostman_NPC_Instances
-- name    : RuralPostman_NPC_Instances
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:57.669535+00:00
-- url     : https://prove2.me/theorems/2710e86c-16a5-4d7c-b4b9-c9c20e28ec4e
-- title:
--   §2, p. 5 — rural postman instances, postman's tours, tour weight, and the RURAL POSTMAN and HAMILTON CIRCUIT languages
-- statement:
--   This file sets up the four decision problems in the proof of the Theorem of §2 of Lenstra and Rinnooy Kan.
--
--   A **rural postman instance** consists of a graph $G=(N,A)$ with node set $N=\{0,\dots,n-1\}$, a finite list of arcs $a=(\mathrm{tail}(a),\mathrm{head}(a))$ each carrying a weight $w(a)\in\mathbb N\cup\{0\}$ and a flag saying whether $a$ belongs to the set $R\subseteq A$ of **required arcs**, and a threshold $k\in\mathbb N$. Parallel arcs and loops are allowed.
--
--   A **traversal** of an arc $a$ runs either from $\mathrm{tail}(a)$ to $\mathrm{head}(a)$ (forward) or from $\mathrm{head}(a)$ to $\mathrm{tail}(a)$ (backward). A **postman's tour** is a cyclic sequence of traversals $\tau_0,\dots,\tau_{m-1}$ such that
--
--   1. each $\tau_i$ ends at the node where $\tau_{i+1 \bmod m}$ starts (a closed walk; nodes and arcs may repeat);
--   2. in the directed problem every traversal is forward;
--   3. every required arc $a\in R$ is traversed at least once.
--
--   Its **weight** is $\sum_{i<m} w(\tau_i)$, counting repeated traversals with multiplicity. The instance is a yes-instance of UNDIRECTED (resp. DIRECTED) RURAL POSTMAN if it has an undirected (resp. directed) postman's tour of weight $\le k$.
--
--   For HAMILTON CIRCUIT a graph $H$ on $\{0,\dots,n-1\}$ is a Boolean adjacency matrix; it is undirected when the matrix is symmetric. DIRECTED HAMILTON CIRCUIT asks for a cyclic ordering $\sigma_0,\dots,\sigma_{n-1}$ of all nodes with an arc from each $\sigma_i$ to $\sigma_{i+1 \bmod n}$; UNDIRECTED HAMILTON CIRCUIT asks the same of a symmetric matrix with $n\ge 3$ (an undirected cycle needs at least three nodes).
--
--   Each problem becomes a language over the four-letter alphabet $\{0,1,-,\#\}$: an instance is written as a list of natural numbers in binary (for a rural postman instance: $n$, the number of arcs, then tail, head, weight and required-bit of each arc, then $k$; for a graph: $n$ and its adjacency matrix row by row), and the language consists of the codes of the yes-instances.
--
--   These are the objects of the Theorem and of every milestone of the mission.
--
--   **Formalization Note** Nodes are `Fin n` (0-based). The empty tour is allowed; it is a postman's tour exactly when $R=\emptyset$. Tours have no length bound: weights may be $0$, so a tour of weight $\le k$ may be long. The graph code `dhpCode` and the predicate `HasHamiltonCircuit` are reused from the published definitions `SchedComplexity.NoWait.DirectedGraphs`.
-- source:
--   Lenstra, Rinnooy Kan, On general routing problems, Mathematisch Centrum report BW 42/74 (December 1974), p. 5, §2, proof of the Theorem (the problems UNDIRECTED (DIRECTED) HAMILTON CIRCUIT and UNDIRECTED (DIRECTED) RURAL POSTMAN)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_SchedComplexity_NoWait_DirectedGraphs

namespace RuralPostman.NPC

open ProjSchedTW.Complexity (BSym encNats)
open SchedComplexity.NoWait (HasHamiltonCircuit dhpCode)

/-! # Rural postman instances and the four decision problems of §2

Lenstra and Rinnooy Kan, *On general routing problems*, Mathematisch Centrum report BW 42/74
(December 1974), p. 5, proof of the Theorem: UNDIRECTED (DIRECTED) HAMILTON CIRCUIT and
UNDIRECTED (DIRECTED) RURAL POSTMAN. Nodes are `Fin n` (0-based). -/

/-- An instance of RURAL POSTMAN: a graph `G = (N, A)` on the nodes `N = Fin n`, given as a list
of arcs `(tail, head, w, required?)` with weight `w ∈ ℕ`; the arcs flagged `true` form the
required subset `R ⊆ A`; and the threshold `k`. Parallel arcs and loops are allowed. In the
undirected problem an arc may be traversed in either direction, in the directed problem only from
its tail to its head. -/
structure RPInstance where
  /-- The number of nodes; the nodes are `Fin n`. -/
  n : ℕ
  /-- The arcs `(tail, head, weight, required?)`. -/
  arcs : List (Fin n × Fin n × ℕ × Bool)
  /-- The weight threshold `k`. -/
  k : ℕ

namespace RPInstance

variable (I : RPInstance)

/-- A traversal of an arc: the arc's index in `I.arcs` and its direction (`true` = from tail to
head, `false` = from head to tail). -/
abbrev Traversal : Type := Fin I.arcs.length × Bool

/-- The node at which a traversal starts. -/
def trSrc (t : I.Traversal) : Fin I.n :=
  if t.2 then (I.arcs.get t.1).1 else (I.arcs.get t.1).2.1

/-- The node at which a traversal ends. -/
def trDst (t : I.Traversal) : Fin I.n :=
  if t.2 then (I.arcs.get t.1).2.1 else (I.arcs.get t.1).1

/-- Arc `e` is required (`e ∈ R`). -/
def IsRequired (e : Fin I.arcs.length) : Prop := (I.arcs.get e).2.2.2 = true

instance (e : Fin I.arcs.length) : Decidable (I.IsRequired e) := by
  unfold IsRequired; infer_instance

/-- A postman's tour: a cyclic sequence of traversals `τ₀, …, τ_{m-1}` in which each traversal
ends where the next one (cyclically) starts, so that it is a closed walk; in the directed problem
(`directed = true`) every arc is traversed from tail to head; and every required arc is traversed
at least once. Nodes and arcs may repeat; the empty sequence is allowed. -/
def IsTour (directed : Bool) (τ : List I.Traversal) : Prop :=
  (directed = true → ∀ t ∈ τ, t.2 = true) ∧
  (∀ i : Fin τ.length, I.trDst (τ.get i) = I.trSrc (τ.get (finRotate τ.length i))) ∧
  (∀ e : Fin I.arcs.length, I.IsRequired e → ∃ b : Bool, (e, b) ∈ τ)

/-- The weight of a tour: the sum of the weights of its traversals, counted with multiplicity. -/
def tourWeight (τ : List I.Traversal) : ℕ :=
  (τ.map fun t => (I.arcs.get t.1).2.2.1).sum

/-- The instance is a yes-instance of UNDIRECTED (`directed = false`) or DIRECTED
(`directed = true`) RURAL POSTMAN: it has a postman's tour of weight `≤ k`. -/
def RPYes (directed : Bool) : Prop :=
  ∃ τ : List I.Traversal, I.IsTour directed τ ∧ I.tourWeight τ ≤ I.k

end RPInstance

/-- The code of a rural postman instance: `n`, the number of arcs, then for each arc its tail,
head, weight and required-bit (`1`/`0`), then `k`, all in binary. The code determines the
instance. -/
def rpCode (I : RPInstance) : List BSym :=
  encNats (I.n :: I.arcs.length ::
    (I.arcs.flatMap fun a => [a.1.val, a.2.1.val, a.2.2.1, if a.2.2.2 then 1 else 0]) ++ [I.k])

/-- UNDIRECTED RURAL POSTMAN as a language: the codes of the instances with an undirected
postman's tour of weight `≤ k`. -/
def urpLang : CookPvsNP.Lang BSym :=
  { w | ∃ I : RPInstance, I.RPYes false ∧ w = rpCode I }

/-- DIRECTED RURAL POSTMAN as a language: the codes of the instances with a directed postman's
tour of weight `≤ k`. -/
def drpLang : CookPvsNP.Lang BSym :=
  { w | ∃ I : RPInstance, I.RPYes true ∧ w = rpCode I }

/-- A Bool adjacency matrix is symmetric, i.e. it describes an undirected graph. -/
def IsSymm {n : ℕ} (adj : Fin n → Fin n → Bool) : Prop := ∀ u v, adj u v = adj v u

/-- UNDIRECTED HAMILTON CIRCUIT as a language: the codes `dhpCode adj` of the symmetric matrices
on at least 3 nodes whose graph has a Hamilton circuit (an undirected cycle through every node
exactly once). The diagonal (loops) plays no role. -/
def uhcLang : CookPvsNP.Lang BSym :=
  { w | ∃ (n : ℕ) (adj : Fin n → Fin n → Bool),
      IsSymm adj ∧ 3 ≤ n ∧ HasHamiltonCircuit adj ∧ w = dhpCode adj }

/-- DIRECTED HAMILTON CIRCUIT as a language: the codes `dhpCode adj` of the directed graphs that
have a Hamilton circuit. -/
def dhcLang : CookPvsNP.Lang BSym :=
  { w | ∃ (n : ℕ) (adj : Fin n → Fin n → Bool), HasHamiltonCircuit adj ∧ w = dhpCode adj }

end RuralPostman.NPC


