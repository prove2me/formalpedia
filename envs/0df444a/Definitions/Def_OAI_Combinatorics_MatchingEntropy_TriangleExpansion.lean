-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingEntropy_TriangleExpansion
-- name    : OAI_Combinatorics_MatchingEntropy_TriangleExpansion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:44:47.05633+00:00
-- url     : https://prove2.me/theorems/f0876306-d889-4d07-8144-1d86c87f6a9c
-- title:
--   Triangle expansion at a vertex: incidences, and expanding and contracting perfect matchings
-- statement:
--   Throughout, $G$ is a loopless multigraph with finite vertex set $V$ and finite edge set $E$: every edge $e$ has two endpoints $\ell(e)\neq r(e)$, parallel edges are allowed, and a vertex $w$ is *incident* to $e$ if $w\in\{\ell(e),r(e)\}$. A *perfect matching* of $G$ is a set $M\subseteq E$ such that every vertex is incident to exactly one edge of $M$.
--
--   Fix a vertex $v\in V$ and an arbitrary labelling $c:E\to\{0,1,2\}$ of the edges (no condition on $c$ is imposed in this module). The *triangle expansion* $H=G^{c}_{v}$ of $G$ at $v$ along $c$ has vertex set $V\sqcup\{t_1,t_2\}$ and edge set $E\sqcup\{n_0,n_1,n_2\}$; write $t_0=v$ and call $t_0,t_1,t_2$ the *tips*. An old edge $e\in E$ keeps its endpoints, except that an endpoint equal to $v$ is moved to the tip $t_{c(e)}$; the new edge $n_i$ joins $t_{i+1}$ and $t_{i+2}$, indices taken modulo $3$. Thus $v$ is blown up into the triangle $t_0t_1t_2$, and the label of an edge at $v$ records the corner of the triangle to which it is reattached.
--
--   The module provides the following objects.
--
--   1. **Incidences in $H$.** Let $t_j$ be a tip, $e\in E$ an old edge, $n_i$ a new edge and $w\neq v$ an old vertex. Then $t_j$ is incident to $e$ in $H$ if and only if $e$ is incident to $v$ in $G$ and $c(e)=j$; $w$ is incident to $e$ in $H$ if and only if $w$ is incident to $e$ in $G$; $t_j$ is incident to $n_i$ if and only if $i\neq j$; and $w$ is incident to no new edge. Moreover the three tips are distinct, and a reattached endpoint of an old edge with label $i$ equals the tip $t_j$ exactly when the original endpoint was $v$ and $i=j$, and equals an old vertex $z\neq v$ exactly when the original endpoint was $z$.
--   2. **The matching edge at $v$.** For a perfect matching $M$ of $G$, $e_M(v)$ denotes the unique edge of $M$ incident to $v$; every edge of $M$ incident to $v$ equals $e_M(v)$.
--   3. **Expansion of a perfect matching.** For a perfect matching $M$ of $G$ put
--   $$
--   \widehat M \;=\; M\ \sqcup\ \{\,n_{c(e_M(v))}\,\}\ \subseteq\ E\sqcup\{n_0,n_1,n_2\},
--   $$
--   the old edges of $M$ together with the triangle edge whose index is the label of $e_M(v)$. For every labelling $c$, $\widehat M$ is a perfect matching of $H$ (the tip $t_{c(e_M(v))}$ is covered by $e_M(v)$ and the other two tips by $n_{c(e_M(v))}$), so $M\mapsto\widehat M$ maps perfect matchings of $G$ to perfect matchings of $H$.
--   4. **Crossing once.** A perfect matching $N$ of $H$ *crosses once* if there is exactly one edge $e\in E$ that is incident to $v$ in $G$ and belongs to $N$.
--   5. **Contraction.** For a perfect matching $N$ of $H$ let $N|_E=\{e\in E:\ e\in N\}$ be its set of old edges. If $N$ crosses once, then $N|_E$ is a perfect matching of $G$; it is called the contraction $\check N$ of $N$.
--   6. **Index types for iterated expansions.** Types $V_n$ and $E_n$ for $n\in\mathbb{N}$ are defined recursively by
--   $$
--   V_0=\{0,1\},\quad V_{n+1}=V_n\sqcup\{0,1\},\qquad E_0=\{0,1,2\},\quad E_{n+1}=E_n\sqcup\{0,1,2\},
--   $$
--   so $|V_n|=2(n+1)$ and $|E_n|=3(n+1)$. Because a triangle expansion turns the vertex type $V$ into $V\sqcup\{t_1,t_2\}$ and the edge type $E$ into $E\sqcup\{n_0,n_1,n_2\}$, they are designed as the vertex and edge types of graphs obtained from a graph with two vertices and three edges by $n$ successive triangle expansions (the graphs themselves are not defined in this module). Both are finite and carry decidable equality.
--
--   Expansion and contraction set up the dictionary between perfect matchings of $G$ and those perfect matchings of $H$ that use exactly one of the edges leaving the triangle. This dictionary is the combinatorial basis for comparing the perfect matching polytope of $G$ with the part of the perfect matching polytope of $H$ on which the cut around the triangle carries total weight one.
--
--   **Formalization Note** The vertex type of $H$ is `V ⊕ Fin 2`, with the tips $t_0,t_1,t_2$ being `Sum.inl v`, `Sum.inr 0`, `Sum.inr 1`, and its edge type is `E ⊕ Fin 3`. The construction of $H$ (`triangleExpansion`, `triangleTip`, `reattach`) is imported. This module defines `incidentChoice` (the edge $e_M(v)$, selected with `Classical.choose`), `expandEdges` and `expandMatching`, `CrossOnce`, `contractEdges` and `contractMatching`, and the types `KleeV`, `KleeE` with noncomputable `Fintype` instances and classical `DecidableEq` instances. The incidence facts of item 1 are the lemmas `triangleTip_injective`, `reattach_eq_tip`, `reattach_eq_inl`, `expanded_incident_old_tip`, `expanded_incident_old_inl`, `expanded_incident_new_tip` and `expanded_incident_new_inl`. Perfect matchings are bundled as finite edge sets together with the proof that they are perfect matchings.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingEntropy/TriangleExpansion.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingEntropy/TriangleExpansion.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Components

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

section TriangleExpansion
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

end TriangleExpansion

def KleeV : ℕ → Type
  | 0 => Fin 2
  | n + 1 => KleeV n ⊕ Fin 2

def KleeE : ℕ → Type
  | 0 => Fin 3
  | n + 1 => KleeE n ⊕ Fin 3

noncomputable instance kleeVFintype (n : ℕ) : Fintype (KleeV n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (Fin 2))
  | succ n ih =>
    let : Fintype (KleeV n) := ih
    exact inferInstanceAs (Fintype (KleeV n ⊕ Fin 2))
noncomputable instance kleeEFintype (n : ℕ) : Fintype (KleeE n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (Fin 3))
  | succ n ih =>
    let : Fintype (KleeE n) := ih
    exact inferInstanceAs (Fintype (KleeE n ⊕ Fin 3))
noncomputable instance kleeVDecEq (n : ℕ) : DecidableEq (KleeV n) := Classical.decEq _
noncomputable instance kleeEDecEq (n : ℕ) : DecidableEq (KleeE n) := Classical.decEq _

section ExpansionSupport
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem triangleTip_injective (v : V) : Function.Injective (triangleTip v) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [triangleTip]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem reattach_eq_tip (v w : V) (i j : Fin 3) :
    reattach v i w = triangleTip v j ↔ w = v ∧ i = j := by
  by_cases h : w = v
  · simp [reattach,h,(triangleTip_injective v).eq_iff]
  · fin_cases j <;> simp [reattach,h,triangleTip]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem reattach_eq_inl (v w z : V) (hz : z ≠ v) (i : Fin 3) :
    reattach v i w = Sum.inl z ↔ w = z := by
  by_cases h : w = v
  · subst w
    fin_cases i <;> simp [reattach,triangleTip,hz.symm]
  · simp [reattach,h]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expanded_incident_old_tip (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (e : E) (j : Fin 3) :
    (triangleExpansion G c v).Incident (triangleTip v j) (Sum.inl e) ↔
      G.Incident v e ∧ c e = j := by
  simp only [LooplessGraph.Incident,triangleExpansion,Sum.elim_inl,reattach_eq_tip]
  tauto

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expanded_incident_old_inl (G : LooplessGraph V E) (c : E → Fin 3) (v w : V)
    (hw : w ≠ v) (e : E) :
    (triangleExpansion G c v).Incident (Sum.inl w) (Sum.inl e) ↔ G.Incident w e := by
  simp only [LooplessGraph.Incident,triangleExpansion,Sum.elim_inl,reattach_eq_inl v _ w hw]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expanded_incident_new_tip (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (i j : Fin 3) :
    (triangleExpansion G c v).Incident (triangleTip v j) (Sum.inr i) ↔ i ≠ j := by
  simp only [LooplessGraph.Incident,triangleExpansion,Sum.elim_inr,
    (triangleTip_injective v).eq_iff]
  fin_cases i <;> fin_cases j <;> decide

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expanded_incident_new_inl (G : LooplessGraph V E) (c : E → Fin 3) (v w : V)
    (hw : w ≠ v) (i : Fin 3) :
    ¬(triangleExpansion G c v).Incident (Sum.inl w) (Sum.inr i) := by
  fin_cases i <;> simp [LooplessGraph.Incident,triangleExpansion,triangleTip,hw.symm]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
def incidentChoice (G : LooplessGraph V E) (M : G.Matching) (v : V) : E :=
  Classical.choose (M.property v)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem incidentChoice_spec (G : LooplessGraph V E) (M : G.Matching) (v : V) :
    incidentChoice G M v ∈ M.val ∧ G.Incident v (incidentChoice G M v) :=
  (Classical.choose_spec (M.property v)).1

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem eq_incidentChoice (G : LooplessGraph V E) (M : G.Matching) (v : V) {e : E}
    (he : e ∈ M.val) (hv : G.Incident v e) : e = incidentChoice G M v :=
  (Classical.choose_spec (M.property v)).2 e ⟨he,hv⟩

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
def expandEdges (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (M : G.Matching) :
    Finset (E ⊕ Fin 3) := M.val.disjSum {c (incidentChoice G M v)}

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expandEdges_matching (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (M : G.Matching) :
    (triangleExpansion G c v).IsPerfectMatching (expandEdges G c v M) := by
  let e := incidentChoice G M v
  have he := incidentChoice_spec G M v
  have htip (j : Fin 3) : ∃! f, f ∈ expandEdges G c v M ∧
      (triangleExpansion G c v).Incident (triangleTip v j) f := by
    by_cases hj : c e = j
    · refine ⟨Sum.inl e,⟨by simp [expandEdges,he.1,e],
        (expanded_incident_old_tip G c v e j).mpr ⟨he.2,hj⟩⟩,?_⟩
      intro f hf
      rcases f with f | f
      · have hfm : f ∈ M.val := by simpa [expandEdges] using hf.1
        exact congrArg Sum.inl (eq_incidentChoice G M v hfm
          ((expanded_incident_old_tip G c v f j).mp hf.2).1)
      · have hfcol : f = c e := by simpa [expandEdges,e] using hf.1
        exact ((expanded_incident_new_tip G c v f j).mp hf.2 (hfcol.trans hj)).elim
    · refine ⟨Sum.inr (c e),⟨by simp [expandEdges,e],
        (expanded_incident_new_tip G c v (c e) j).mpr hj⟩,?_⟩
      intro f hf
      rcases f with f | f
      · have hfm : f ∈ M.val := by simpa [expandEdges] using hf.1
        have hfv := (expanded_incident_old_tip G c v f j).mp hf.2
        have hfe : f = e := eq_incidentChoice G M v hfm hfv.1
        exact (hj (hfe ▸ hfv.2)).elim
      · exact congrArg Sum.inr (by simpa [expandEdges,e] using hf.1)
  intro w
  rcases w with w | w
  · by_cases hw : w = v
    · subst w
      exact htip 0
    · obtain ⟨f,hf,hu⟩ := M.property w
      refine ⟨Sum.inl f,⟨by simpa [expandEdges] using hf.1,
        (expanded_incident_old_inl G c v w hw f).mpr hf.2⟩,?_⟩
      intro g hg
      rcases g with g | g
      · exact congrArg Sum.inl (hu g ⟨by simpa [expandEdges] using hg.1,
          (expanded_incident_old_inl G c v w hw g).mp hg.2⟩)
      · exact (expanded_incident_new_inl G c v w hw g hg.2).elim
  · fin_cases w
    · exact htip 1
    · exact htip 2

omit [Fintype V] [Fintype E] [DecidableEq E] in
def expandMatching (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (M : G.Matching) :
    (triangleExpansion G c v).Matching := ⟨expandEdges G c v M,expandEdges_matching G c v M⟩

def CrossOnce (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching) : Prop :=
  ∃! e, Sum.inl e ∈ N.val ∧ G.Incident v e

def contractEdges (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching) : Finset E :=
  Finset.univ.filter (fun e => Sum.inl e ∈ N.val)

omit [Fintype V] in
theorem contractEdges_matching (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching) (hN : CrossOnce G c v N) :
    G.IsPerfectMatching (contractEdges G c v N) := by
  intro w
  by_cases hw : w = v
  · subst w
    simpa only [CrossOnce,contractEdges,Finset.mem_filter,Finset.mem_univ,true_and] using hN
  · obtain ⟨f,hf,hu⟩ := N.property (Sum.inl w)
    rcases f with f | f
    · refine ⟨f,⟨by simpa [contractEdges] using hf.1,
        (expanded_incident_old_inl G c v w hw f).mp hf.2⟩,?_⟩
      intro g hg
      apply Sum.inl.inj
      exact hu (Sum.inl g) ⟨by simpa [contractEdges] using hg.1,
        (expanded_incident_old_inl G c v w hw g).mpr hg.2⟩
    · exact (expanded_incident_new_inl G c v w hw f hf.2).elim

def contractMatching (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching) (hN : CrossOnce G c v N) : G.Matching :=
  ⟨contractEdges G c v N,contractEdges_matching G c v N hN⟩

end ExpansionSupport
end MatchingEntropyBounds.Refined

end

end OAI


