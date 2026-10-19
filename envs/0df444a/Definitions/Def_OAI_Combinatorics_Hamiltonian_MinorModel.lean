-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorModel
-- name    : OAI_Combinatorics_Hamiltonian_MinorModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:59:23.425093+00:00
-- url     : https://prove2.me/theorems/48dd8a60-326d-4598-a6f0-16c426d9b4ce
-- title:
--   Minor models of graphs, clean connecting paths, and growing a corridor model into a minor model
-- statement:
--   Throughout, $G$ is a simple graph on a vertex set $V$ and $H$ is a simple graph on a vertex set $W$. For $X\subseteq W$ we write $H[X]$ for the subgraph of $H$ induced on $X$; a connected graph is in particular nonempty. A *dart* of $G$ is an ordered pair $(u,w)$ of adjacent vertices, and its underlying edge is $\{u,w\}$. The file defines the following objects.
--
--   1. **Minor models.** A minor model of $G$ in $H$ is a family $(B_v)_{v\in V}$ of *branch sets* $B_v\subseteq W$ such that every $B_v$ is finite and $H[B_v]$ is connected, $B_v\cap B_w=\varnothing$ for $v\ne w$, and every edge of $G$ is represented by an edge of $H$:
--   $$vw\in E(G)\ \Longrightarrow\ \exists\,a\in B_v,\ \exists\,b\in B_w:\ ab\in E(H).$$
--   Contracting every branch set to a single vertex exhibits $G$ as a minor of $H$.
--
--   2. **Clean connections.** For $A,B,C\subseteq W$, a clean connection from $A$ to $B$ inside $C$ is a path $p_0p_1\cdots p_k$ in $H$ all of whose vertices lie in $C$, with $p_0\in A$ and $p_k\in B$, which meets $A$ only in $p_0$ and $B$ only in $p_k$. The file proves that if some vertex of $A$ is joined to some vertex of $B$ by a walk in $H$, then a shortest walk from $A$ to $B$ is a path meeting $A$ only at its start and $B$ only at its end; applied inside $H[C]$, this shows that a clean connection exists whenever $H[C]$ is connected and $C$ meets both $A$ and $B$. The *left set* of a clean connection is $\{p_0,\dots,p_{k-1}\}$, the vertex set of the path without its last vertex (it is $\{p_0\}$ when $k=0$). The left set is finite, induces a connected subgraph, contains $p_0$ and lies in $C$; if $A\cap B=\varnothing$, it is disjoint from $B$ and contains a neighbour of $p_k$.
--
--   3. **Corridor models.** A corridor model of $G$ in $H$ consists of branch sets $B_v\subseteq W$ for $v\in V$ and corridors $K_d\subseteq W$, one for each dart $d$ of $G$, all finite and inducing connected subgraphs of $H$, such that $B_v\cap B_w=\varnothing$ for $v\ne w$; $K_d\cap K_{d'}=\varnothing$ whenever $d$ and $d'$ have different underlying edges; $B_v\cap K_d=\varnothing$ whenever $v$ is not an endpoint of $d$; and $K_{(u,w)}$ meets both $B_u$ and $B_w$.
--
--   4. **Grown branches.** Given a corridor model, choose for every edge $e$ of $G$ a dart $d_e=(u_e,w_e)$ with underlying edge $e$ and a clean connection $P_e$ from $B_{u_e}$ to $B_{w_e}$ inside $K_{d_e}$ (it exists by item 2), and let the *extension* $X_e$ be the left set of $P_e$. The grown branch of $v\in V$ is
--   $$\widehat B_v\;=\;B_v\ \cup\bigcup_{e\in E(G):\ u_e=v}X_e .$$
--   The file proves that each $X_e$ is finite, induces a connected subgraph, lies in $K_{d_e}$ and is disjoint from every $B_v$ with $v\ne u_e$, and that $X_e\cap X_f=\varnothing$ for $e\ne f$. Consequently the grown branches induce connected subgraphs, are pairwise disjoint, and for every edge $vw$ of $G$ some vertex of $\widehat B_v$ is adjacent in $H$ to some vertex of $\widehat B_w$. If $V$ is finite, every $\widehat B_v$ is finite and $(\widehat B_v)_{v\in V}$ is a minor model of $G$ in $H$.
--
--   A corridor model is what a crossing-free drawing provides after thickening it inside a fine lattice: disjoint regions for the vertices and disjoint corridors for the edges. Item 4 turns it into a genuine minor model by absorbing, for each edge, the part of a clean path through its corridor up to the last step before the far branch set into the branch set of the near endpoint. In the Hamiltonicity proof this is applied with $H$ the square lattice graph on $\mathbb{Z}^2$, which shows that every finite plane graph is a minor of the square lattice.
--
--   **Formalization Note** `MinorModel G H` is a structure with fields `branch`, `branch_finite`, `branch_connected`, `branches_disjoint` and `adjacency`. Clean connections are the structure `WalkSelection.CleanConnection`, the shortest-walk lemma is `shortest_join`, and the left set `leftSet` is the support of `walk.dropLast`. Corridor models are `CorridorModel G H` (introduced in the corridor module) and darts are Mathlib's `G.Dart`. The dart $d_e$ (`edgeDart`) and the path $P_e$ (`connection`) are fixed by `Classical.choose` and `Classical.choice`; `extension`, `grownBranch` and `toMinorModel` (which needs `[Fintype V]`) implement item 4.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/MinorModel.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/MinorModel.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorDuality
import Definitions.Def_OAI_Combinatorics_Hamiltonian_BMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Matching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ForestMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ThreeCuts
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Gluing
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Traces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_SquareGrid
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Corridors

namespace OAI

/-! Clean finite walks, disjoint grown branches, and lattice minors. -/

namespace Barnette

noncomputable section

structure MinorModel {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) where
  branch : V → Set W
  branch_finite : ∀ v, (branch v).Finite
  branch_connected : ∀ v, (H.induce (branch v)).Connected
  branches_disjoint : ∀ v w, v ≠ w → Disjoint (branch v) (branch w)
  adjacency : ∀ v w, G.Adj v w → ∃ a ∈ branch v, ∃ b ∈ branch w, H.Adj a b

namespace WalkSelection

variable {W : Type*} {H : SimpleGraph W}

theorem shortest_join {A B : Set W}
    (hex : ∃ a ∈ A, ∃ b ∈ B, H.Reachable a b) :
    ∃ (a : W) (_ha : a ∈ A) (b : W) (_hb : b ∈ B) (p : H.Walk a b),
      p.IsPath ∧ (∀ x ∈ p.support, x ∈ A → x = a) ∧
        (∀ x ∈ p.support, x ∈ B → x = b) := by
  classical
  let P : ℕ → Prop := fun n => ∃ a ∈ A, ∃ b ∈ B, ∃ p : H.Walk a b, p.length = n
  have hp : ∃ n, P n := by
    obtain ⟨a, ha, b, hb, ⟨p⟩⟩ := hex
    exact ⟨p.length, a, ha, b, hb, p, rfl⟩
  obtain ⟨a, ha, b, hb, p, hlen⟩ := Nat.find_spec hp
  have minimal {x y : W} (hx : x ∈ A) (hy : y ∈ B) (q : H.Walk x y) :
      p.length ≤ q.length := by
    rw [hlen]
    exact Nat.find_min' hp ⟨x, hx, y, hy, q, rfl⟩
  have hpath : p.IsPath := by
    obtain ⟨q, hq⟩ := p.reachable.exists_walk_length_eq_dist
    apply p.isPath_of_length_eq_dist
    exact le_antisymm (hq ▸ minimal ha hb q) (SimpleGraph.dist_le p)
  refine ⟨a, ha, b, hb, p, hpath, ?_, ?_⟩
  · intro x hx hxA
    by_contra hxa
    have hshort := p.length_dropUntil_lt_length hx hxa
    exact (not_lt_of_ge (minimal hxA hb (p.dropUntil x hx))) hshort
  · intro x hx hxB
    by_contra hxb
    have hshort := p.length_takeUntil_lt_length hx hxb
    exact (not_lt_of_ge (minimal ha hxB (p.takeUntil x hx))) hshort

structure CleanConnection (A B C : Set W) where
  start : W
  finish : W
  start_mem : start ∈ A
  finish_mem : finish ∈ B
  walk : H.Walk start finish
  isPath : walk.IsPath
  support_subset : ∀ x ∈ walk.support, x ∈ C
  clean_start : ∀ x ∈ walk.support, x ∈ A → x = start
  clean_finish : ∀ x ∈ walk.support, x ∈ B → x = finish

theorem exists_clean_connection {A B C : Set W}
    (hC : (H.induce C).Connected) (hA : (A ∩ C).Nonempty) (hB : (B ∩ C).Nonempty) :
    Nonempty (CleanConnection (H := H) A B C) := by
  classical
  obtain ⟨a, ha, haC⟩ := hA
  obtain ⟨b, hb, hbC⟩ := hB
  obtain ⟨u, hu, v, hv, p, hpath, hcleanA, hcleanB⟩ :=
    shortest_join (H := H.induce C) (A := {x | x.val ∈ A}) (B := {x | x.val ∈ B})
      ⟨⟨a, haC⟩, ha, ⟨b, hbC⟩, hb, hC _ _⟩
  let f : H.induce C →g H := ⟨Subtype.val, fun h => h⟩
  let q : H.Walk u.val v.val := p.map f
  have hs : q.support = p.support.map Subtype.val := p.support_map _
  refine ⟨{
    start := u.val
    finish := v.val
    start_mem := hu
    finish_mem := hv
    walk := q
    isPath := hpath.map Subtype.val_injective
    support_subset := ?_
    clean_start := ?_
    clean_finish := ?_
  }⟩
  · intro x hx
    rw [hs] at hx
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hx
    exact z.property
  · intro x hx hxA
    rw [hs] at hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact congrArg Subtype.val (hcleanA z hz hxA)
  · intro x hx hxB
    rw [hs] at hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact congrArg Subtype.val (hcleanB z hz hxB)

namespace CleanConnection
variable {A B C : Set W} (p : CleanConnection (H := H) A B C)

def leftSet : Set W := {x | x ∈ p.walk.dropLast.support}

theorem leftSet_finite : p.leftSet.Finite := p.walk.dropLast.support.finite_toSet

theorem leftSet_connected : (H.induce p.leftSet).Connected :=
  p.walk.dropLast.connected_induce_support

theorem start_mem_leftSet : p.start ∈ p.leftSet := p.walk.dropLast.start_mem_support

theorem leftSet_subset : p.leftSet ⊆ C := by
  intro x hx
  apply p.support_subset x
  exact (p.walk.isSubwalk_take _).support_subset hx

theorem leftSet_disjoint_finish (hAB : Disjoint A B) : Disjoint p.leftSet B := by
  have hne : p.start ≠ p.finish := by
    intro heq
    exact Set.disjoint_left.mp hAB p.start_mem (heq ▸ p.finish_mem)
  have hn : ¬p.walk.Nil := SimpleGraph.Walk.not_nil_of_ne hne
  have hd := p.isPath.support_nodup
  rw [← p.walk.support_dropLast_concat hn] at hd
  have hfinish : p.finish ∉ p.leftSet := by
    intro h
    exact hd.disjoint h (by simp)
  rw [Set.disjoint_left]
  intro x hx hxB
  have hs : x ∈ p.walk.support := (p.walk.isSubwalk_take _).support_subset hx
  have heq := p.clean_finish x hs hxB
  exact hfinish (heq ▸ hx)

theorem leftSet_adj_finish (hAB : Disjoint A B) :
    ∃ a ∈ p.leftSet, H.Adj a p.finish := by
  have hne : p.start ≠ p.finish := by
    intro heq
    exact Set.disjoint_left.mp hAB p.start_mem (heq ▸ p.finish_mem)
  exact ⟨p.walk.penultimate, p.walk.dropLast.end_mem_support,
    p.walk.adj_penultimate (SimpleGraph.Walk.not_nil_of_ne hne)⟩

end CleanConnection

end WalkSelection
end
end Barnette

namespace Barnette

namespace CorridorModel
noncomputable section
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

 theorem exists_edgeDart (e : G.edgeSet) : ∃ d : G.Dart, d.edge = e.val := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ a b => exact ⟨⟨(a, b), he⟩, rfl⟩

def edgeDart (e : G.edgeSet) : G.Dart := Classical.choose (exists_edgeDart e)

@[simp] theorem edgeDart_edge (e : G.edgeSet) : (edgeDart e).edge = e.val :=
  Classical.choose_spec (exists_edgeDart e)

variable (M : CorridorModel G H)

def connection (e : G.edgeSet) : WalkSelection.CleanConnection (H := H)
    (M.branch (edgeDart e).fst) (M.branch (edgeDart e).snd) (M.corridor (edgeDart e)) :=
  Classical.choice (WalkSelection.exists_clean_connection
    (M.corridor_connected _) (M.incident_meets _).1 (M.incident_meets _).2)

def extension (e : G.edgeSet) : Set W := (M.connection e).leftSet

theorem extension_finite (e : G.edgeSet) : (M.extension e).Finite :=
  (M.connection e).leftSet_finite

theorem extension_connected (e : G.edgeSet) : (H.induce (M.extension e)).Connected :=
  (M.connection e).leftSet_connected

theorem extension_subset (e : G.edgeSet) : M.extension e ⊆ M.corridor (edgeDart e) :=
  (M.connection e).leftSet_subset

theorem extension_disjoint_branch (e : G.edgeSet) (v : V) (hv : v ≠ (edgeDart e).fst) :
    Disjoint (M.extension e) (M.branch v) := by
  by_cases hs : v = (edgeDart e).snd
  · subst v
    exact (M.connection e).leftSet_disjoint_finish
      (M.branches_disjoint _ _ (edgeDart e).fst_ne_snd)
  · exact ((M.nonincident_disjoint _ _ hv hs).mono_right (M.extension_subset e)).symm

theorem extensions_disjoint (e f : G.edgeSet) (hef : e ≠ f) :
    Disjoint (M.extension e) (M.extension f) := by
  have hne : (edgeDart e).edge ≠ (edgeDart f).edge := by
    simpa only [edgeDart_edge] using (fun h => hef (Subtype.ext h) : e.val ≠ f.val)
  exact (M.corridors_disjoint _ _ hne).mono (M.extension_subset e) (M.extension_subset f)

def grownBranch (v : V) : Set W := M.branch v ∪
  ⋃ e : {e : G.edgeSet // (edgeDart e).fst = v}, M.extension e.val

theorem branch_subset_grown (v : V) : M.branch v ⊆ M.grownBranch v :=
  Set.subset_union_left

theorem extension_subset_grown (e : G.edgeSet) : M.extension e ⊆ M.grownBranch (edgeDart e).fst :=
  fun _ hx => Or.inr (Set.mem_iUnion.mpr ⟨⟨e, rfl⟩, hx⟩)

theorem grownBranch_connected (v : V) : (H.induce (M.grownBranch v)).Connected := by
  obtain ⟨⟨a, ha⟩⟩ := (M.branch_connected v).nonempty
  apply H.induce_connected_of_patches a (M.branch_subset_grown v ha)
  intro x hx
  rcases hx with hx | hx
  · exact ⟨M.branch v, M.branch_subset_grown v, ha, hx, M.branch_connected v _ _⟩
  · obtain ⟨⟨e, he⟩, hx⟩ := Set.mem_iUnion.mp hx
    have hext : M.extension e ⊆ M.grownBranch v := by
      simpa only [he] using M.extension_subset_grown e
    have hi : (M.branch v ∩ M.extension e).Nonempty := by
      refine ⟨(M.connection e).start, ?_, (M.connection e).start_mem_leftSet⟩
      simpa only [he] using (M.connection e).start_mem
    exact ⟨M.branch v ∪ M.extension e,
      Set.union_subset (M.branch_subset_grown v) hext, Or.inl ha, Or.inr hx,
      SimpleGraph.induce_union_connected (M.branch_connected v).preconnected
        (M.extension_connected e).preconnected hi _ _⟩

theorem grownBranches_disjoint (v w : V) (hvw : v ≠ w) :
    Disjoint (M.grownBranch v) (M.grownBranch w) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Set.disjoint_left.mp (M.branches_disjoint v w hvw) hx hy
  · obtain ⟨⟨e, he⟩, hy⟩ := Set.mem_iUnion.mp hy
    exact Set.disjoint_left.mp (M.extension_disjoint_branch e v (he ▸ hvw)) hy hx
  · obtain ⟨⟨e, he⟩, hx⟩ := Set.mem_iUnion.mp hx
    exact Set.disjoint_left.mp (M.extension_disjoint_branch e w (he ▸ hvw.symm)) hx hy
  · obtain ⟨⟨e, he⟩, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨⟨f, hf⟩, hy⟩ := Set.mem_iUnion.mp hy
    have hef : e ≠ f := by
      intro h
      subst f
      exact hvw (he.symm.trans hf)
    exact Set.disjoint_left.mp (M.extensions_disjoint e f hef) hx hy

theorem grownBranch_adjacency (v w : V) (hvw : G.Adj v w) :
    ∃ a ∈ M.grownBranch v, ∃ b ∈ M.grownBranch w, H.Adj a b := by
  let e : G.edgeSet := ⟨s(v, w), hvw⟩
  have hAB := M.branches_disjoint _ _ (edgeDart e).fst_ne_snd
  obtain ⟨a, ha, hadj⟩ := (M.connection e).leftSet_adj_finish hAB
  have ha' : a ∈ M.grownBranch (edgeDart e).fst := M.extension_subset_grown e ha
  have hb' : (M.connection e).finish ∈ M.grownBranch (edgeDart e).snd :=
    M.branch_subset_grown _ (M.connection e).finish_mem
  have hd : (edgeDart e).edge = s(v, w) := edgeDart_edge e
  rcases SimpleGraph.dart_edge_eq_mk'_iff'.mp hd with ⟨h₁, h₂⟩ | ⟨h₂, h₁⟩
  · exact ⟨a, h₁ ▸ ha', (M.connection e).finish, h₂ ▸ hb', hadj⟩
  · exact ⟨(M.connection e).finish, h₁ ▸ hb', a, h₂ ▸ ha', hadj.symm⟩

variable [Fintype V]

theorem grownBranch_finite (v : V) : (M.grownBranch v).Finite := by
  classical
  exact (M.branch_finite v).union (Set.finite_iUnion (fun e => M.extension_finite e.val))

def toMinorModel : MinorModel G H where
  branch := M.grownBranch
  branch_finite := M.grownBranch_finite
  branch_connected := M.grownBranch_connected
  branches_disjoint := M.grownBranches_disjoint
  adjacency := M.grownBranch_adjacency

end
end CorridorModel
end Barnette

namespace Barnette.PlaneEmbedding
noncomputable section
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

end
end Barnette.PlaneEmbedding

end OAI


