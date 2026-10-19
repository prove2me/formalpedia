-- Prove2me | Definitions.Def_OAI_Analysis_Littlewood_Nibble
-- name    : OAI_Analysis_Littlewood_Nibble
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:06:17.460013+00:00
-- url     : https://prove2.me/theorems/d97e20d0-fc38-4f06-9fc6-4ef48e944486
-- title:
--   Hypergraph incidences, collision counts, and partial-matching states for the Rödl nibble
-- statement:
--   Fix a vertex type $V$ and a finite type $E$ of edge labels. A hypergraph is described by a finite set $S\subseteq E$ of edges together with a map $A$ assigning to each edge label $e$ its finite vertex set $A(e)\subseteq V$. A configuration $s:E\to\{\mathrm{true},\mathrm{false}\}$ marks the selected edges, $U\subseteq V$ is a finite set of vertices, and $\mathbf{1}[s_e]$ is $1$ if $e$ is selected and $0$ otherwise.
--
--   1. **Incident edges.** $\mathrm{inc}(v)=\{e\in S:\ v\in A(e)\}$; its size is the degree of $v$.
--
--   2. **Hit edges.** For a finite $W\subseteq V$, $\mathrm{hits}(W)=\bigcup_{v\in W}\mathrm{inc}(v)=\{e\in S:\ A(e)\cap W\ne\emptyset\}$.
--
--   3. **Untouched vertices.** $\mathrm{untouched}(U,s)=\{v\in U:\ s_e=\mathrm{false}\text{ for every }e\in\mathrm{inc}(v)\}$, the vertices of $U$ missed by all selected edges.
--
--   4. **Restricted edges.** For $W\subseteq V$, $\mathrm{restrict}(W)=\{e\in S:\ A(e)\subseteq W\}$, the edges surviving the deletion of all vertices outside $W$.
--
--   5. **Isolated and colliding selections.** $\mathrm{isolated}(s)$ is the set of selected $e\in S$ with $A(e)\cap A(f)=\emptyset$ for every other selected $f\in S$; $\mathrm{colliding}(s)$ is the set of selected $e\in S$ for which some selected $f\in S$, $f\ne e$, satisfies $A(e)\cap A(f)\ne\emptyset$.
--
--   6. **Collision count.**
--   $$
--   \mathrm{coll}(U,s)=\sum_{v\in U}\ \sum_{e\in\mathrm{inc}(v)}\ \sum_{f\in\mathrm{inc}(v),\,f\ne e}\mathbf{1}[s_e]\,\mathbf{1}[s_f],
--   $$
--   the number of triples $(v,e,f)$ with $v\in U$ and $e\ne f$ two selected edges through $v$.
--
--   7. **Packing state.** A packing state relative to $(U,S,A)$ is a triple $(W,F,M)$ of finite sets with $W\subseteq U$ (active vertices), $F\subseteq S$ (active edges) and $M\subseteq S$ (chosen edges), such that $A(e)\subseteq W$ for every $e\in F$, the sets $A(e)$ with $e\in M$ are pairwise disjoint (so $M$ is a matching), and $W$ is disjoint from $\bigcup_{e\in M}A(e)$.
--
--   8. **Initial state and composition.** If $A(e)\subseteq U$ for all $e\in S$, the initial state is $(U,S,\emptyset)$. If $P=(W,F,M)$ is a packing state relative to $(U,S,A)$ and $Q=(W',F',M')$ is a packing state relative to $(W,F,A)$, their composition is $(W',F',M\cup M')$, again a packing state relative to $(U,S,A)$.
--
--   These are the bookkeeping objects of the Rödl nibble. In one round every active edge is selected independently with a small probability; the selected edges meeting no other selected edge join the matching, and the next round runs on the vertices missed by all selected edges (after discarding a few atypical ones) and on the edges they still span. Degrees, codegrees and the collision count control the number of wasted vertices, and composing packing states iterates the rounds. The outcome is an almost perfect matching theorem: an $r$-uniform hypergraph whose degrees are all close to some large $D$ and whose codegrees are small compared with $D$ has a matching covering all but an arbitrarily small fraction of its vertices.
--
--   **Formalization Note** `incident`, `hits`, `untouched`, `restrictEdges`, `isolated` and `colliding` return `Finset`s, and `collisionCount` is real-valued, built from `selectedIndicator` of the product-probability file; `mem_incident` and `mem_hits` are simp lemmas. `PackingState U S A` is a structure whose fields are the three sets and the properties of item 7; `PackingState.initial` takes the hypothesis $A(e)\subseteq U$ for $e\in S$, and `PackingState.compose P Q` is the composition of item 8.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Nibble.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Nibble.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AsymptoticallyMinimalLittlewood mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uE uV

namespace AsymptoticallyMinimalLittlewood
namespace Nibble
open scoped BigOperators
open Finset
section SetUnions
variable {I : Type uI} {E : Type uE} [DecidableEq I] [DecidableEq E]

end SetUnions

section Hypergraph
variable {V : Type uV} {E : Type uE} [DecidableEq V] [Fintype E] [DecidableEq E]

def incident (S : Finset E) (A : E → Finset V) (v : V) : Finset E :=
  S.filter fun e ↦ v ∈ A e

def hits (S : Finset E) (A : E → Finset V) (W : Finset V) : Finset E :=
  W.biUnion (incident S A)

omit [Fintype E] [DecidableEq E] in
@[simp] lemma mem_incident (S : Finset E) (A : E → Finset V) (v : V) (e : E) :
    e ∈ incident S A v ↔ e ∈ S ∧ v ∈ A e := by simp [incident]

omit [Fintype E] in
@[simp] lemma mem_hits (S : Finset E) (A : E → Finset V) (W : Finset V) (e : E) :
    e ∈ hits S A W ↔ e ∈ S ∧ ∃ v ∈ W, v ∈ A e := by
  simp only [hits, Finset.mem_biUnion, mem_incident]
  aesop

/-- Count the vertices missed by the selected edges. -/
def untouched (U : Finset V) (S : Finset E) (A : E → Finset V) (s : E → Bool) : Finset V :=
  U.filter fun v ↦ ∀ e ∈ incident S A v, s e = false

/-- Edges remaining after a vertex deletion. -/
def restrictEdges (S : Finset E) (A : E → Finset V) (W : Finset V) : Finset E :=
  S.filter fun e ↦ A e ⊆ W

/-- The selected edges that meet no other selected edge. -/
def isolated (S : Finset E) (A : E → Finset V) (s : E → Bool) : Finset E :=
  S.filter fun e ↦ s e = true ∧ ∀ f ∈ S, f ≠ e → s f = true → Disjoint (A e) (A f)

def colliding (S : Finset E) (A : E → Finset V) (s : E → Bool) : Finset E :=
  S.filter fun e ↦ s e = true ∧ ∃ f ∈ S, f ≠ e ∧ s f = true ∧ ¬ Disjoint (A e) (A f)

def collisionCount (U : Finset V) (S : Finset E) (A : E → Finset V) (s : E → Bool) : ℝ :=
  ∑ v ∈ U, ∑ e ∈ incident S A v, ∑ f ∈ (incident S A v).erase e,
    selectedIndicator e s * selectedIndicator f s

/-- The bookkeeping invariant of a partial matching and its active graph. -/
structure PackingState (U : Finset V) (S : Finset E) (A : E → Finset V) where
  vertices : Finset V
  edges : Finset E
  chosen : Finset E
  vertices_sub : vertices ⊆ U
  edges_sub : edges ⊆ S
  support : ∀ e ∈ edges, A e ⊆ vertices
  chosen_sub : chosen ⊆ S
  matching : (chosen : Set E).Pairwise (fun e f ↦ Disjoint (A e) (A f))
  separation : Disjoint vertices (chosen.biUnion A)

namespace PackingState

noncomputable def initial (U : Finset V) (S : Finset E) (A : E → Finset V)
    (hsub : ∀ e ∈ S, A e ⊆ U) : PackingState U S A where
  vertices := U
  edges := S
  chosen := ∅
  vertices_sub := Finset.Subset.refl _
  edges_sub := Finset.Subset.refl _
  support := hsub
  chosen_sub := Finset.empty_subset _
  matching := by simp
  separation := by simp

noncomputable def compose {U : Finset V} {S : Finset E} {A : E → Finset V}
    (P : PackingState U S A) (Q : PackingState P.vertices P.edges A) : PackingState U S A where
  vertices := Q.vertices
  edges := Q.edges
  chosen := P.chosen ∪ Q.chosen
  vertices_sub := Q.vertices_sub.trans P.vertices_sub
  edges_sub := Q.edges_sub.trans P.edges_sub
  support := Q.support
  chosen_sub := Finset.union_subset P.chosen_sub (Q.chosen_sub.trans P.edges_sub)
  matching := by
    have hcross (e : E) (he : e ∈ P.chosen) (f : E) (hf : f ∈ Q.chosen) :
        Disjoint (A e) (A f) := by
      apply P.separation.symm.mono
      · intro v hv
        exact Finset.mem_biUnion.mpr ⟨e, he, hv⟩
      · exact P.support f (Q.chosen_sub hf)
    intro e he f hf hef
    rcases Finset.mem_union.mp he with he | he <;> rcases Finset.mem_union.mp hf with hf | hf
    · exact P.matching he hf hef
    · exact hcross e he f hf
    · exact (hcross f hf e he).symm
    · exact Q.matching he hf hef
  separation := by
    rw [Finset.union_biUnion]
    exact Finset.disjoint_union_right.mpr
      ⟨P.separation.mono_left Q.vertices_sub, Q.separation⟩

end PackingState

open Filter Topology

end Hypergraph

end Nibble
end AsymptoticallyMinimalLittlewood

end OAI


