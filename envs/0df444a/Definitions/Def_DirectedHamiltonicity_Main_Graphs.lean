-- Prove2me | Definitions.Def_DirectedHamiltonicity_Main_Graphs
-- name    : DirectedHamiltonicity_Main_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:23:34.182936+00:00
-- url     : https://prove2.me/theorems/43136af7-7f84-41f2-9775-83c48aee5e40
-- title:
--   Directed multigraphs, Hamiltonian paths and cycles, the incoming Laplacian and out-arborescences
-- statement:
--   A **directed multigraph** $H$ on a vertex set $V$ has a set $E(H)$ of labelled arcs; each arc $e$ has a tail and a head, and several arcs may join the same ordered pair (parallel arcs). Loops are allowed unless excluded.
--
--   1. A **Hamiltonian path from $s$ to $t$** in $H$, with $n=|V|$, is a sequence of arcs $e_0,\dots,e_{n-2}$ for which the vertex sequence $v_0=s$, $v_{i+1}=\mathrm{head}(e_i)$ satisfies $\mathrm{tail}(e_i)=v_i$, visits every vertex exactly once, and ends at $v_{n-1}=t$. The set of these paths is $\mathcal P_{s,t}(H)$. Two paths through the same vertices along different parallel arcs are different paths. For weights $w:E(H)\to\mathbb Z_{\ge0}$ the weight of a path is $\sum_i w(e_i)$; for labels $p$ in a commutative ring, $\sum_{P\in\mathcal P_{s,t}(H)}\prod_{e\in P}p(e)$ is the **path sum**.
--   2. The **Laplacian** $L(H,p)$ for labels $p:E(H)\to R$ is the $V\times V$ matrix
--   $$L(H,p)_{uv}=\begin{cases}\sum_{w\in V}\sum_{e\in E_{wu}(H)}p(e), & u=v,\\ -\sum_{e\in E_{uv}(H)}p(e), & u\ne v,\end{cases}$$
--   where $E_{uv}(H)$ is the set of arcs from $u$ to $v$. $L_s(H,p)$ deletes row and column $s$.
--   3. An **out-arborescence rooted at $s$** is a set $T$ of arcs such that no arc of $T$ enters $s$, every vertex $v\ne s$ is entered by exactly one arc of $T$, and every vertex is reachable from $s$ along arcs of $T$: a spanning tree with all arcs directed away from $s$.
--   4. A directed graph on $\{0,\dots,n-1\}$ given by a Boolean adjacency matrix has a **Hamiltonian cycle** when $n\ge1$ and some cyclic ordering $\sigma(0),\dots,\sigma(n-1)$ of all vertices, each exactly once, has every arc $\sigma(i)\to\sigma(i+1)$ present, including the closing arc $\sigma(n-1)\to\sigma(0)$. For $n=1$ this is the self-loop at the single vertex; for $n=2$ it is a directed 2-cycle.
--
--   These are the graph objects of §2 and §4.1 used by every statement of the mission.
--
--   **Formalization Note** Arcs are a type `E` with maps `tail`, `head`; a path is a function `Fin (n-1) → E`. A simple digraph given by a relation `adj` is the multigraph whose arcs are the pairs `(u,v)` with `adj u v`.
--
--   **Reuse Note** The graph carrier is the published `AtomicDynRouting.ResidenceTime.Network`, which stores only tail and head. `Multidigraph` is an abbreviation for that carrier; acyclicity, routing agents and unit travel times are not imposed or used. The Hamiltonian paths, labelled arc subsets and matrices are separate constructions on it.
-- source:
--   Tomohiro Koana, Soh Kumabe, Breaking the $2^n$ barrier for directed hamiltonicity, STOC 2027 submission #811 (October 2026), source.pdf SHA-256 103ec74bdf635a66ec16e2c21d6fbc0896c1aa986065e20007ae217a701fffb3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/811.pdf, PDF p.4 / printed p.3 (§2) and PDF p.8 / printed p.7 (§4.1, Laplacian and out-arborescences)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network

namespace DirectedHamiltonicity.Main

/-!
# Directed multigraphs with labelled arcs, Hamiltonian paths and cycles, Laplacians, arborescences

T. Koana, S. Kumabe, *Breaking the 2^n barrier for directed hamiltonicity*, STOC 2027 submission #811
(October 2026), §2 (PDF p.4 / printed p.3) and §4.1 (PDF p.8 / printed p.7).

A directed multigraph on the vertex type `V` has an arc type `E`; every arc has its own label, a tail
and a head. Parallel arcs and loops are allowed unless a hypothesis excludes them. A Hamiltonian
`s`–`t` path is a sequence of `n - 1` arcs (`n = |V|`), so two paths through the same vertices along
different parallel copies are different paths.
-/

/-- A directed multigraph on vertex type `V` with labelled arcs `E`: each arc `e` goes from `tail e`
to `head e`. -/
abbrev Multidigraph (V E : Type) := AtomicDynRouting.ResidenceTime.Network V E

namespace Multidigraph

variable {V E F : Type}

/-- No arc is a loop. -/
def Loopless (H : Multidigraph V E) : Prop := ∀ e, H.tail e ≠ H.head e

/-- The sub-multigraph keeping exactly the arcs satisfying `P` (same vertex set, same labels). -/
def restrictArcs (H : Multidigraph V E) (P : E → Prop) : Multidigraph V {e // P e} :=
  ⟨fun e => H.tail e.1, fun e => H.head e.1⟩

/-- The multigraph with the arcs of `H` and the arcs of `A` (disjoint union of arc sets, same
vertices). -/
def addArcs (H : Multidigraph V E) (A : Multidigraph V F) : Multidigraph V (E ⊕ F) :=
  ⟨Sum.elim H.tail A.tail, Sum.elim H.head A.head⟩

/-- The vertex sequence `s = v₀, v₁, …, v_k` of an arc sequence `e₀, …, e_{k-1}` started at `s`:
`v_{i+1} = head eᵢ`. -/
def walkVerts (H : Multidigraph V E) (s : V) {k : ℕ} (e : Fin k → E) : Fin (k + 1) → V :=
  Fin.cons s (fun i => H.head (e i))

/-- `e` is a Hamiltonian path from `s` to `t`: `n - 1` arcs (`n = |V|`) with `tail eᵢ = vᵢ`, whose
vertex sequence `v₀ = s, …, v_{n-1}` visits every vertex exactly once and ends at `t`. -/
def IsHamPath [Fintype V] (H : Multidigraph V E) (s t : V) (e : Fin (Fintype.card V - 1) → E) :
    Prop :=
  (∀ i, H.tail (e i) = H.walkVerts s e i.castSucc) ∧
  Function.Injective (H.walkVerts s e) ∧
  H.walkVerts s e (Fin.last _) = t

open Classical in
/-- The finite set `𝒫_{s,t}(H)` of Hamiltonian paths from `s` to `t`, each an arc sequence. -/
noncomputable def hamPaths [Fintype V] [Fintype E] (H : Multidigraph V E) (s t : V) :
    Finset (Fin (Fintype.card V - 1) → E) :=
  Finset.univ.filter (H.IsHamPath s t)

/-- The total weight `∑_{e ∈ P} w(e)` of an arc sequence. -/
def pathWeight {k : ℕ} (w : E → ℕ) (P : Fin k → E) : ℕ := ∑ i, w (P i)

open Classical in
/-- The number of Hamiltonian `s`–`t` paths of total weight exactly `B` (an arbitrary integer). -/
noncomputable def weightedPathCount [Fintype V] [Fintype E] (H : Multidigraph V E) (w : E → ℕ)
    (s t : V) (B : ℤ) : ℕ :=
  ((H.hamPaths s t).filter (fun P => ((pathWeight w P : ℕ) : ℤ) = B)).card

/-- The sum over Hamiltonian `s`–`t` paths of the product of the arc labels,
`∑_{P ∈ 𝒫_{s,t}(H)} ∏_{e ∈ P} p(e)`. -/
noncomputable def hamPathPoly [Fintype V] [Fintype E] {R : Type} [CommRing R]
    (H : Multidigraph V E) (p : E → R) (s t : V) : R :=
  ∑ P ∈ H.hamPaths s t, ∏ i, p (P i)

open Classical in
/-- The (incoming) Laplacian `L(H,p)` of §4.1: the diagonal entry at `u` is the sum of `p(e)` over all
arcs `e` entering `u`, and the entry `(u, v)`, `u ≠ v`, is minus the sum of `p(e)` over the arcs
from `u` to `v`. -/
noncomputable def laplacian [Fintype E] {R : Type} [CommRing R] (H : Multidigraph V E)
    (p : E → R) : Matrix V V R :=
  fun u v =>
    if u = v then ∑ e ∈ Finset.univ.filter (fun e => H.head e = u), p e
    else -∑ e ∈ Finset.univ.filter (fun e => H.tail e = u ∧ H.head e = v), p e

/-- `L_s(H,p)`: the Laplacian with row and column `s` deleted, indexed by the vertices `v ≠ s`. -/
noncomputable def reducedLaplacian [Fintype E] {R : Type} [CommRing R] (H : Multidigraph V E)
    (p : E → R) (s : V) : Matrix {v // v ≠ s} {v // v ≠ s} R :=
  (H.laplacian p).submatrix Subtype.val Subtype.val

/-- The arc set `T` is a spanning out-arborescence of `H` rooted at `s`: no arc of `T` enters `s`,
every vertex `v ≠ s` is entered by exactly one arc of `T`, and every vertex is reachable from `s`
along arcs of `T`. (Equivalently: a spanning tree whose arcs are all directed away from `s`.) -/
def IsOutArborescence (H : Multidigraph V E) (s : V) (T : Finset E) : Prop :=
  (∀ e ∈ T, H.head e ≠ s) ∧
  (∀ v, v ≠ s → ∃! e, e ∈ T ∧ H.head e = v) ∧
  ∀ v, Relation.ReflTransGen (fun a b => ∃ e ∈ T, H.tail e = a ∧ H.head e = b) s v

end Multidigraph

open Multidigraph

/-- The directed graph given by a Boolean adjacency matrix on `Fin n`, viewed as a multigraph whose
arcs are the ordered pairs `(u, v)` with `adj u v = true` (one arc per pair; loops allowed). -/
def ofAdj {V : Type} (adj : V → V → Prop) : Multidigraph V {a : V × V // adj a.1 a.2} :=
  ⟨fun a => a.1.1, fun a => a.1.2⟩

/-- The `n`-vertex directed graph with Boolean adjacency matrix `adj` has a Hamiltonian cycle: `n ≥ 1`
and there is a cyclic ordering `σ(0), σ(1), …, σ(n-1)` of all vertices, each exactly once, such that
every arc `σ(i) → σ(i+1)`, including the closing arc `σ(n-1) → σ(0)`, is present. For `n = 1` this is
the self-loop at the single vertex. -/
def HasHamCycle (n : ℕ) (adj : Fin n → Fin n → Bool) : Prop :=
  0 < n ∧ ∃ σ : Fin n ≃ Fin n, ∀ i, adj (σ i) (σ (finRotate n i)) = true

end DirectedHamiltonicity.Main


