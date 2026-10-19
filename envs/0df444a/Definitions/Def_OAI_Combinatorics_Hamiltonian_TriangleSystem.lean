-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
-- name    : OAI_Combinatorics_Hamiltonian_TriangleSystem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:26:38.856994+00:00
-- url     : https://prove2.me/theorems/eadc4cad-33c9-4a3f-a655-a00240c26c15
-- title:
--   Triangle systems, corner-choice states, partner states, and opposite graphs
-- statement:
--   This file introduces an abstract framework for choosing one corner from each triangle of a family, together with triangle potentials in an oriented network.
--
--   1. **Triangle system.** A triangle system with index set $A$ on a vertex set $V$ assigns to every $a \in A$ an injective labelling $i \mapsto v_a(i) \in V$ of three corners, $i \in \mathbb{Z}/3$, such that two distinct triangles never share two corners: if $i \neq j$, $k \neq l$, $v_a(i) = v_b(k)$ and $v_a(j) = v_b(l)$, then $a = b$.
--
--   2. **States.** For a set $X \subseteq V$, a state with target $X$ is a corner choice $s : A \to \mathbb{Z}/3$ such that, writing $\bar s(a) = v_a(s(a))$ for the chosen corner,
--   $$
--   \bar s : A \to X, \qquad a \mapsto v_a(s(a)),
--   $$
--   is a bijection. Thus a state matches every triangle with one of its own corners so that every element of $X$ is used exactly once. A state is determined by its chosen corners, it induces a bijection between $A$ and $X$, and if $A$ is finite there are only finitely many states.
--
--   3. **Partners.** Two states $r, s$ with the same target are partners if $\bar r(a) \neq \bar s(a)$, equivalently $r(a) \neq s(a)$, for every $a \in A$.
--
--   4. **Third index and index step.** For $i, j \in \mathbb{Z}/3$ the third index is $\theta(i, j) = -(i + j)$; for $i \neq j$ it is the unique element different from both, and $\theta(\theta(i, j), j) = i$. The index step is the integer
--   $$
--   \delta(i, j) = \begin{cases} 0 & \text{if } i = j, \\ 1 & \text{if } j = i + 1, \\ -1 & \text{if } j = i - 1. \end{cases}
--   $$
--   The file also proves the case analysis: if $i \neq j$, $l \notin \{i, j\}$ and $k \neq l$, then either $i = k$ and $j = \theta(k, l)$, or $j = k$ and $i = \theta(k, l)$.
--
--   5. **Opposite graph of a state.** For a state $s$, the simple graph on $V$ in which distinct vertices $v, w$ are adjacent if some triangle $a$ has $v = v_a(i)$ and $w = v_a(j)$ with $i \neq s(a)$ and $j \neq s(a)$: every triangle contributes the side opposite to its chosen corner.
--
--   6. **Triangle potential and sides in a network.** Let $D$ be an oriented network with edge set $E$, let $\sigma_D(e, z)$ be $1$ if the tail of $e$ in $D$ is $z$ and $-1$ otherwise, and consider a labelled triangle of $D$ with corners $c_0, c_1, c_2$ and edges $e_i$ joining $c_i$ and $c_{i+1}$. For $\alpha \in \mathbb{R}^E$ the potential $p : \mathbb{Z}/3 \to \mathbb{R}$ integrates $\alpha$ along the triangle starting from $c_0$:
--   $$
--   p(0) = 0, \qquad p(1) = \alpha(e_0)\, \sigma_D(e_0, c_0), \qquad p(2) = p(1) + \alpha(e_1)\, \sigma_D(e_1, c_1).
--   $$
--   The side between corners $i$ and $j$ is $e_i$ if $j = i + 1$ and $e_j$ otherwise; it always belongs to the triangle's edge set and, for $i \neq j$, joins $c_i$ and $c_j$.
--
--   In the main construction the triangles are the faces surrounding the black vertices of a cubic bipartite plane graph, the corners are faces of that graph, and states are bijections between the non-root black vertices and the faces away from the root. The proof looks for a pair of partner states for which the opposite graph of one of them is acyclic; the index steps and potentials supply the integer and real weights with which states are counted.
--
--   **Formalization Note** `TriangleSystem A V` has fields `vertex`, `vertex_injective` and `edge_unique`; `State X` is a subtype of `A → Fin 3`, with `State.value`, `State.toEquiv`, the extensionality lemma `State.ext` and finiteness instances; then `Partner`, `thirdIndex` (with `thirdIndex_distinct`, `thirdIndex_involution`, `other_corners`), the integer-valued `indexDelta`, `oppositeGraph`, and for networks `Triangle.potential` and `Triangle.side` (with `side_mem`, `side_ends`). Two private lemmas about `ite` are local rewriting helpers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/TriangleSystem.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/TriangleSystem.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BarnetteHamiltonian mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Triangle incidence states, opposite graphs, and oriented potentials. -/

namespace Barnette

structure TriangleSystem (A V : Type*) where
  vertex : A → Fin 3 → V
  vertex_injective : ∀ t, Function.Injective (vertex t)
  edge_unique : ∀ t u i j k l, i ≠ j → k ≠ l →
    vertex t i = vertex u k → vertex t j = vertex u l → t = u

namespace TriangleSystem

variable {A V : Type*} (T : TriangleSystem A V)

def State (X : Set V) :=
  {c : A → Fin 3 // Function.Injective (fun t => T.vertex t (c t)) ∧
    Set.range (fun t => T.vertex t (c t)) = X}

namespace State

variable {T} {X : Set V}

def value (s : T.State X) (t : A) : V := T.vertex t (s.val t)

theorem value_injective (s : T.State X) : Function.Injective s.value := s.property.1

theorem value_range (s : T.State X) : Set.range s.value = X := s.property.2

theorem value_mem (s : T.State X) (t : A) : s.value t ∈ X := by
  exact (Set.ext_iff.mp s.value_range _).mp ⟨t, rfl⟩

noncomputable def toEquiv (s : T.State X) : A ≃ X :=
  Equiv.ofBijective (fun t => ⟨s.value t, s.value_mem t⟩) ⟨by
    intro t u h
    exact s.value_injective (congrArg Subtype.val h), by
    intro v
    obtain ⟨t, ht⟩ := (Set.ext_iff.mp s.value_range v.val).mpr v.property
    exact ⟨t, Subtype.ext ht⟩⟩

@[simp] theorem coe_toEquiv (s : T.State X) (t : A) : (s.toEquiv t : V) = s.value t := rfl

theorem value_eq_iff (r s : T.State X) (t : A) :
    r.value t = s.value t ↔ r.val t = s.val t := T.vertex_injective t |>.eq_iff

@[ext] theorem ext {r s : T.State X} (h : ∀ t, r.value t = s.value t) : r = s := by
  apply Subtype.ext
  funext t
  exact (value_eq_iff r s t).mp (h t)

instance [Finite A] : Finite (T.State X) := inferInstanceAs (Finite (Subtype _))

noncomputable instance [Fintype A] : Fintype (T.State X) := Fintype.ofFinite _

end State

def Partner {X : Set V} (r s : T.State X) : Prop := ∀ t, r.value t ≠ s.value t

def thirdIndex (i j : Fin 3) : Fin 3 := -(i + j)

theorem thirdIndex_distinct : ∀ i j : Fin 3, i ≠ j →
    thirdIndex i j ≠ i ∧ thirdIndex i j ≠ j := by decide

theorem thirdIndex_involution : ∀ i j : Fin 3, thirdIndex (thirdIndex i j) j = i := by
  decide

theorem other_corners : ∀ i j r s : Fin 3,
    i ≠ j → i ≠ s → j ≠ s → r ≠ s →
    (i = r ∧ j = thirdIndex r s) ∨ (j = r ∧ i = thirdIndex r s) := by decide

def indexDelta (i j : Fin 3) : ℤ := if i = j then 0 else if j = i + 1 then 1 else -1

def oppositeGraph {X : Set V} (s : T.State X) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ∃ t i j, T.vertex t i = v ∧ T.vertex t j = w ∧
    i ≠ s.val t ∧ j ≠ s.val t
  symm := ⟨by
    rintro v w ⟨hvw, t, i, j, hi, hj, his, hjs⟩
    exact ⟨hvw.symm, t, j, i, hj, hi, hjs, his⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

end TriangleSystem
end Barnette
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype E] [Fintype F] in
def Triangle.potential {s : Finset E} (t : D.Triangle s) (α : E → ℝ) : Fin 3 → ℝ :=
  ![0, α (t.edge 0) * D.arcSign (t.edge 0) (t.corner 0),
    α (t.edge 0) * D.arcSign (t.edge 0) (t.corner 0) +
      α (t.edge 1) * D.arcSign (t.edge 1) (t.corner 1)]

omit [Fintype V] [Fintype E] [Fintype F] in
def Triangle.side {s : Finset E} (t : D.Triangle s) (i j : Fin 3) : E :=
  if j = i+1 then t.edge i else t.edge j

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.side_mem {s : Finset E} (t : D.Triangle s) (i j : Fin 3) :
    t.side D i j ∈ s := by
  have hh (k : Fin 3) : t.edge k ∈ s := by
    have hm : t.edge k ∈ Finset.univ.image t.edge := Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
    rwa [t.edge_range] at hm
  unfold side
  split_ifs <;> apply hh

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.side_ends {s : Finset E} (t : D.Triangle s) {i j : Fin 3} (hij : i ≠ j) :
    s(D.tail (t.side D i j),D.head (t.side D i j)) = s(t.corner i,t.corner j) := by
  have hfin : ∀ i j : Fin 3, i ≠ j → j = i+1 ∨ i = j+1 := by decide
  rcases hfin i j hij with hj | hi
  · simp only [side,ite_eq_left hj]
    exact (t.edge_ends i).trans (by rw [hj])
  · have hj : j ≠ i+1 := by
      intro hh
      exact (by decide : ∀ i j : Fin 3, i = j+1 → j = i+1 → False) i j hi hh
    simp only [side,ite_eq_right hj]
    exact (t.edge_ends j).trans (by rw [hi,Sym2.eq_swap])

end
end Barnette.Network

end OAI


