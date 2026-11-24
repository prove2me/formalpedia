-- Prove2me | Definitions.Def_BicliqueSDP_Chain_Supplement_Gadget
-- name    : BicliqueSDP_Chain_Supplement_Gadget
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:14:12.433494+00:00
-- url     : https://prove2.me/theorems/f8cbc8b1-0e8e-4e2d-badd-12e2081d618e
-- title:
--   Definition 2.5 — the bipartite graph H_G and independent-set forms
-- statement:
--   Let $G=(V,E)$ be a finite simple graph and $n=|V|$. Each side of $H_G$ consists of a copy of $V$ and $n+1$ vertices for each unordered edge of $G$. Its edges are exactly the matched vertex copies, every $L_e\times R_e$, and $v_1R_e$ whenever $v\in e$.
--
--   $$V_1=V_2=V\sqcup(E\times\{0,\ldots,n\}),\qquad |L_e|=|R_e|=n+1.$$
--
--   The definitions also give inclusion-maximal and maximum biindependent pairs, the edges incident to a subset $A\subseteq V$, and the sets in (17). For a chosen edge set $F$, the left set contains the vertex copies in $A$ and all $L_e$ with $e\in F$; the right set contains the copies in $V\setminus A$ and all $R_e$ with $e\notin F$. They are used in the corrected Lemma 2.6.
--
--   **Formalization Note** $\alpha$ and biindependence come from the published base definitions. The correction allows any $F$ containing all edges incident to $A$, rather than requiring equality; the printed choice remains available.
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, p. 9, Definition 2.5 and Eq. (17)

import Definitions.Def_BicliqueSDP_Chain_Model
set_option autoImplicit false

namespace BicliqueSDP.Chain.Supplement
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An unordered edge, counted once. -/
abbrev Edge := G.edgeSet
/-- Each side of H_G in Definition 2.5, with exactly n+1 vertices in each edge gadget. -/
abbrev HGSide := V ⊕ (Edge G × Fin (Fintype.card V + 1))

/-- Exactly the three edge families in Definition 2.5. -/
def HGEdge : HGSide G → HGSide G → Prop
  | Sum.inl v, Sum.inl w => v = w
  | Sum.inl v, Sum.inr q => v ∈ q.1.val
  | Sum.inr p, Sum.inr q => p.1 = q.1
  | Sum.inr _, Sum.inl _ => False

instance : DecidableRel (HGEdge G) := fun x y => by
  cases x <;> cases y <;> unfold HGEdge <;> infer_instance

/-- Edges meeting A. -/
def incidentEdges (A : Finset V) : Finset (Edge G) :=
  Finset.univ.filter fun e => ∃ v ∈ A, v ∈ e.val

/-- Left side of (17), allowing the corrected choice F ⊇ incidentEdges A. -/
def formLeft (A : Finset V) (F : Finset (Edge G)) : Finset (HGSide G) := by
  classical
  exact Finset.univ.filter fun x => match x with
    | Sum.inl v => v ∈ A
    | Sum.inr p => p.1 ∈ F

/-- Right side of (17): B = V ∖ A and E₂ = E ∖ F. -/
def formRight (A : Finset V) (F : Finset (Edge G)) : Finset (HGSide G) := by
  classical
  exact Finset.univ.filter fun x => match x with
    | Sum.inl v => v ∉ A
    | Sum.inr p => p.1 ∉ F

variable {L R : Type} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
  (E : L → R → Prop) [DecidableRel E]

/-- Inclusion maximality among all biindependent pairs, with the fixed bipartition. -/
def IsMaximalPair (A : Finset L) (B : Finset R) : Prop :=
  IsBiindep E A B ∧ ∀ A' B', IsBiindep E A' B' → A ⊆ A' → B ⊆ B' → A' = A ∧ B' = B

/-- Maximum cardinality among all biindependent pairs. -/
def IsMaximumPair (A : Finset L) (B : Finset R) : Prop :=
  IsBiindep E A B ∧ (A.card : ℝ) + B.card = alpha E

end
end BicliqueSDP.Chain.Supplement


