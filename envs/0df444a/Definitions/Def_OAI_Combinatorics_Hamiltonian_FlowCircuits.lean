-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
-- name    : OAI_Combinatorics_Hamiltonian_FlowCircuits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:19:06.826528+00:00
-- url     : https://prove2.me/theorems/c6236310-7653-4701-aff3-cd896a198923
-- title:
--   Minimal flow circuits, vertex stars, and cyclically indexed cycles in graphs
-- statement:
--   Let $N$ be an oriented network with finite vertex set $V$, finite edge set $E$, tail map $t$ and head map $h$. Its boundary operator $\partial_N : \mathbb{R}^E \to \mathbb{R}^V$ is $(\partial_N x)(v) = \sum_{h(e) = v} x_e - \sum_{t(e) = v} x_e$ (net inflow at $v$), and $\operatorname{supp}(x) = \{ e : x_e \neq 0 \}$. The underlying simple graph $G(N)$ joins two distinct vertices $v, w$ when some edge has endpoint set $\{v, w\}$.
--
--   1. **Flow circuit.** An edge function $x \in \mathbb{R}^E$ is a flow circuit of $N$ if $\partial_N x = 0$, $x \neq 0$, and its support is minimal among flows in the sense that for every $y \in \mathbb{R}^E$
--   $$
--   \partial_N y = 0 \ \text{ and } \ \operatorname{supp}(y) \subseteq \operatorname{supp}(x) \quad \Longrightarrow \quad y = 0 \ \text{ or } \ \operatorname{supp}(y) = \operatorname{supp}(x).
--   $$
--   These are the support-minimal (elementary) circulations of $N$.
--
--   2. **Star and other endpoint.** The star of a vertex $v$ is the set of edges incident to it, $\operatorname{star}(v) = \{ e : v \in \{t(e), h(e)\} \}$. For an edge $e$ and a vertex $v$, the other end of $e$ is $h(e)$ if $t(e) = v$, and $t(e)$ otherwise; for a non-loop edge at $v$ it is the endpoint different from $v$.
--
--   3. **Cycle coordinates.** For a simple graph $G$ on a vertex set $V$ (no finiteness needed), a cycle in coordinates consists of a natural number $n$ and an injective map $\mathbb{Z}/m \to V$, $i \mapsto v_i$, where $m = n + 3$, such that
--   $$
--   v_i \text{ is adjacent to } v_{i+1} \text{ in } G \qquad \text{for all } i \in \mathbb{Z}/m \ (\text{indices mod } m).
--   $$
--   It is a simple cycle of length $m \geq 3$ together with a chosen starting vertex and direction of traversal.
--
--   4. **Edges of a cycle.** If $C$ is a cycle in coordinates in $G(N)$, then for each $i$ an edge $e_i$ of $N$ with endpoint set $\{v_i, v_{i+1}\}$ is chosen (one exists by adjacency), and $E(C) = \{ e_i : i \in \mathbb{Z}/m \}$ is the edge set of the cycle.
--
--   The file also contains three auxiliary facts about cyclic indices: a predicate on $\mathbb{Z}/n$ ($n \geq 1$) that holds somewhere and satisfies "$P(i+1)$ implies $P(i)$" for all $i$ holds everywhere; $1 \neq 0$ in $\mathbb{Z}/(n+3)$; and an orientation lemma: if $a_0, \dots, a_{m-1}$ are distinct elements of a set $A$ indexed by $\mathbb{Z}/m$, $\tau : A \to V$ is injective and $\tau(a_i) \in \{v_i, v_{i+1}\}$ for every $i$, then either $\tau(a_i) = v_i$ for all $i$ or $\tau(a_i) = v_{i+1}$ for all $i$.
--
--   Flow circuits and cycle coordinates connect cycles of a graph with the linear algebra of flows: elsewhere it is shown that a flow supported on the edge set of a cycle of a simple network is a flow circuit, and the orientation lemma propagates a local choice of endpoints coherently around a cycle.
--
--   **Formalization Note** `FlowCircuit x` is a `Prop`-valued structure; `star`, `otherEnd`, `cycleEdge` (defined by choice) and `cycleEdges` are as above. `CycleCoordinates G` stores `n`, an embedding `vertex : Fin (n + 3) ↪ V` and the adjacency proof, with addition in `Fin (n + 3)` wrapping around. The auxiliary theorems are `cyclic_propagation`, `cyclic_one_ne_zero` and `CycleCoordinates.tail_orientation`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/FlowCircuits.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/FlowCircuits.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BarnetteHamiltonian mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Minimal flow circuits, triangular faces, and simple cycle coordinates. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

structure FlowCircuit (x : E → ℝ) : Prop where
  conserved : N.boundary x = 0
  nonzero : x ≠ 0
  minimal : ∀ y, N.boundary y = 0 → N.flowSupport y ⊆ N.flowSupport x →
    y = 0 ∨ N.flowSupport y = N.flowSupport x

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] in
def star (v : V) : Finset E := Finset.univ.filter fun e => N.Incident e v

omit [Fintype V] in
@[simp] lemma mem_star (e : E) (v : V) : e ∈ N.star v ↔ N.Incident e v := by
  simp [star]

omit [Fintype V] in
def otherEnd (e : E) (v : V) : V := if N.tail e = v then N.head e else N.tail e

end
end Barnette.Network
namespace Barnette

open Fin.NatCast

theorem cyclic_propagation {n : ℕ} [NeZero n] (P : Fin n → Prop)
    (hstep : ∀ i, P (i + 1) → P i) {q : Fin n} (hq : P q) : ∀ i, P i := by
  have h : ∀ k : ℕ, P (q - (k : Fin n)) := by
    intro k
    induction k with
    | zero => simpa using hq
    | succ k hk =>
      apply hstep (q - ((k + 1 : ℕ) : Fin n))
      simpa only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub, sub_add_cancel] using hk
  intro i
  simpa only [Fin.cast_val_eq_self, sub_sub_cancel] using h (q - i).val

theorem cyclic_one_ne_zero (n : ℕ) : (1 : Fin (n + 3)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp at this

structure CycleCoordinates {V : Type*} (G : SimpleGraph V) where
  n : ℕ
  vertex : Fin (n + 3) ↪ V
  adjacent : ∀ i, G.Adj (vertex i) (vertex (i + 1))

namespace CycleCoordinates

variable {V : Type*} {G : SimpleGraph V} (C : CycleCoordinates G)

theorem tail_orientation {A : Type*} (face : Fin (C.n + 3) ↪ A)
    (tail : A → V) (htail : Function.Injective tail)
    (hend : ∀ i, tail (face i) = C.vertex i ∨ tail (face i) = C.vertex (i + 1)) :
    (∀ i, tail (face i) = C.vertex i) ∨
      (∀ i, tail (face i) = C.vertex (i + 1)) := by
  classical
  by_cases h : ∃ q, tail (face q) = C.vertex q
  · obtain ⟨q, hq⟩ := h
    left
    apply cyclic_propagation (fun i => tail (face i) = C.vertex i) _ hq
    intro i hi
    rcases hend i with h | h
    · exact h
    · have heq : face i = face (i + 1) := htail (h.trans hi.symm)
      have hi1 := face.injective heq
      have hbad : (1 : Fin (C.n + 3)) = 0 := by
        exact add_left_cancel (by simpa using hi1.symm : i + 1 = i + 0)
      exact (cyclic_one_ne_zero C.n hbad).elim
  · right
    intro i
    exact (hend i).resolve_left (fun hi => h ⟨i, hi⟩)

end CycleCoordinates
end Barnette

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E]
  (N : Network V E) (C : Barnette.CycleCoordinates N.graph)

omit [Fintype V] [Fintype E] in
def cycleEdge (i : Fin (C.n+3)) : E := (C.adjacent i).2.choose

omit [Fintype V] [Fintype E] in
def cycleEdges : Finset E := Finset.univ.image (N.cycleEdge C)

omit [Fintype V] [Fintype E] in
@[simp] lemma mem_cycleEdges (e : E) : e ∈ N.cycleEdges C ↔ ∃ i, N.cycleEdge C i = e := by
  simp [cycleEdges]

end
end Barnette.Network

end OAI


