-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingEntropy_Components
-- name    : OAI_Combinatorics_MatchingEntropy_Components
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:42:10.542585+00:00
-- url     : https://prove2.me/theorems/b54902f4-a35f-428a-b67a-b712d545003c
-- title:
--   Connected components of a multigraph and perfect matchings componentwise
-- statement:
--   Let $G$ be a loopless multigraph with finite vertex set $V$ and finite edge set $E$: every edge $e$ has two endpoints $\ell(e)\neq r(e)$, and parallel edges are distinct elements of $E$. A vertex $v$ is incident to $e$ if $v\in\{\ell(e),r(e)\}$, a perfect matching is a set of edges covering every vertex exactly once, and $\mathcal M(G)$ denotes the set of perfect matchings.
--
--   1. *Underlying simple graph.* $\underline G$ is the simple graph on $V$ in which $v$ and $w$ are adjacent if and only if some edge $e$ satisfies $\{\ell(e),r(e)\}=\{v,w\}$; it has no loops because $G$ has none.
--   2. *Components.* $\mathcal C(G)$ is the finite set of connected components of $\underline G$, and $\kappa(v)\in\mathcal C(G)$ is the component of $v$. Both endpoints of an edge lie in the same component, $\kappa(\ell(e))=\kappa(r(e))$, and more generally $\kappa(\ell(e))=\kappa(v)$ whenever $v$ is incident to $e$.
--   3. *Component graphs.* For $c\in\mathcal C(G)$, $G_c$ is the loopless multigraph with vertex set $V_c=\{v:\ \kappa(v)=c\}$, edge set $E_c=\{e:\ \kappa(\ell(e))=c\}$ and the endpoints inherited from $G$; incidence in $G_c$ coincides with incidence in $G$.
--   4. *Restriction and gluing.* For $M\in\mathcal M(G)$ and every component $c$, $M\cap E_c\in\mathcal M(G_c)$; and for every family $(M_c)_{c\in\mathcal C(G)}$ with $M_c\in\mathcal M(G_c)$, the union is a perfect matching of $G$:
--   $$
--   M\longmapsto(M\cap E_c)_{c\in\mathcal C(G)},\qquad (M_c)_{c\in\mathcal C(G)}\longmapsto\bigcup_{c\in\mathcal C(G)}M_c .
--   $$
--   An edge of $E_c$ belongs to $M\cap E_c$ if and only if it belongs to $M$, and it belongs to the glued matching if and only if it belongs to $M_c$. Consequently the two maps are mutually inverse, and $\mathcal M(G)$ corresponds bijectively to $\prod_{c\in\mathcal C(G)}\mathcal M(G_c)$.
--
--   Perfect matchings of a multigraph therefore decompose over its connected components. This lets statements about perfect matchings, and about laws on them, be proved one component at a time, for instance for connected graphs first, and then assembled.
--
--   **Formalization Note** The simple graph is `underlyingSimple G : SimpleGraph V`, and `Component G` is its type of connected components, with classical `Fintype` and `DecidableEq` instances. The remaining declarations are `componentOf`, `componentGraph`, `componentRestrict` and `componentGlue`, together with the lemmas `component_edge_eq`, `component_incident_iff`, `component_eq_of_incident`, `mem_componentRestrict` and `mem_componentGlue`; the component of an edge is defined through its left endpoint. The module also contains empty sections that declare nothing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingEntropy/Components.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingEntropy/Components.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangleFace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Model
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Simplex
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Coupling
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Basic
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_OddCuts
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Contraction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Polytope
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Face
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Entropy
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Duality
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_EdgeReduction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_MinimalFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_FractionalReduction

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def underlyingSimple (G : LooplessGraph V E) : SimpleGraph V where
  Adj v w := ∃ e, (G.left e = v ∧ G.right e = w) ∨ (G.left e = w ∧ G.right e = v)
  symm := ⟨by
    rintro v w ⟨e, h | h⟩
    · exact ⟨e, Or.inr h⟩
    · exact ⟨e, Or.inl h⟩⟩
  loopless := ⟨by
    rintro v ⟨e, h | h⟩ <;> exact G.loopless e (h.1.trans h.2.symm)⟩

abbrev Component (G : LooplessGraph V E) := (underlyingSimple G).ConnectedComponent
noncomputable instance componentFintype (G : LooplessGraph V E) : Fintype (Component G) := Fintype.ofFinite _
noncomputable instance componentDecidableEq (G : LooplessGraph V E) : DecidableEq (Component G) := Classical.decEq _

def componentOf (G : LooplessGraph V E) (v : V) : Component G :=
  (underlyingSimple G).connectedComponentMk v

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem component_edge_eq (G : LooplessGraph V E) (e : E) :
    componentOf G (G.left e) = componentOf G (G.right e) :=
  SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ⟨e, Or.inl ⟨rfl,rfl⟩⟩

def componentGraph (G : LooplessGraph V E) (c : Component G) :
    LooplessGraph {v // componentOf G v = c} {e // componentOf G (G.left e) = c} where
  left e := ⟨G.left e.val,e.property⟩
  right e := ⟨G.right e.val,(component_edge_eq G e.val).symm.trans e.property⟩
  loopless e h := G.loopless e.val (congrArg Subtype.val h)

section ProductLaws
variable {I : Type uI} [Fintype I] [DecidableEq I] {A : I → Type uA}
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

end ProductLaws

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem component_incident_iff (G : LooplessGraph V E) (c : Component G)
    (v : {v // componentOf G v = c}) (e : {e // componentOf G (G.left e) = c}) :
    (componentGraph G c).Incident v e ↔ G.Incident v.val e.val := by
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem component_eq_of_incident (G : LooplessGraph V E) {v : V} {e : E} (h : G.Incident v e) :
    componentOf G (G.left e) = componentOf G v := by
  rcases h with h | h
  · rw [h]
  · rw [component_edge_eq G e, h]

def componentRestrict (G : LooplessGraph V E) (c : Component G) (M : G.Matching) :
    (componentGraph G c).Matching := by
  classical
  refine ⟨M.val.subtype (fun e => componentOf G (G.left e) = c), ?_⟩
  intro v
  obtain ⟨e,he,hu⟩ := M.property v.val
  have hc : componentOf G (G.left e) = c := (component_eq_of_incident G he.2).trans v.property
  refine ⟨⟨e,hc⟩, ⟨by simpa using he.1,(component_incident_iff G c v _).mpr he.2⟩, ?_⟩
  intro f hf
  exact Subtype.ext (hu f.val ⟨by simpa using hf.1,(component_incident_iff G c v f).mp hf.2⟩)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
@[simp] theorem mem_componentRestrict (G : LooplessGraph V E) (c : Component G) (M : G.Matching)
    (e : {e // componentOf G (G.left e) = c}) :
    e ∈ (componentRestrict G c M).val ↔ e.val ∈ M.val := by
  simp [componentRestrict]

def componentGlue (G : LooplessGraph V E) (M : ∀ c : Component G, (componentGraph G c).Matching) :
    G.Matching := by
  classical
  let N := Finset.univ.filter (fun e => (⟨e,rfl⟩ : {f // componentOf G (G.left f) = componentOf G (G.left e)}) ∈ (M (componentOf G (G.left e))).val)
  have hmem (c : Component G) (e : {e // componentOf G (G.left e) = c}) : e.val ∈ N ↔ e ∈ (M c).val := by
    obtain ⟨e,he⟩ := e
    subst c
    simp [N]
  refine ⟨N, ?_⟩
  intro v
  obtain ⟨e,he,hu⟩ := (M (componentOf G v)).property ⟨v,rfl⟩
  refine ⟨e.val,⟨(hmem _ e).mpr he.1,(component_incident_iff G _ _ e).mp he.2⟩,?_⟩
  intro f hf
  have hfc := component_eq_of_incident G hf.2
  exact congrArg Subtype.val (hu ⟨f,hfc⟩ ⟨(hmem _ _).mp hf.1,(component_incident_iff G _ _ _).mpr hf.2⟩)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_componentGlue (G : LooplessGraph V E)
    (M : ∀ c : Component G, (componentGraph G c).Matching) (c : Component G)
    (e : {e // componentOf G (G.left e) = c}) :
    e.val ∈ (componentGlue G M).val ↔ e ∈ (M c).val := by
  obtain ⟨e,he⟩ := e
  subst c
  simp [componentGlue]

section FiberComposition
variable {A : Type uA} {B : Type uB} {C : Type uC} [Fintype A] [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
end FiberComposition

end MatchingEntropyBounds.Refined

end

end OAI


