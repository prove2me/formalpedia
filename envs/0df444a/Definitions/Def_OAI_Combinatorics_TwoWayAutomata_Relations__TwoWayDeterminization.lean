-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations__TwoWayDeterminization
-- name    : OAI_Combinatorics_TwoWayAutomata_Relations__TwoWayDeterminization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:36:27.535178+00:00
-- url     : https://prove2.me/theorems/36a5cced-3f57-40ac-8721-e573890e15bf
-- title:
--   Block relations and Kleene-algebra identities for reflexive–transitive closures of relations
-- statement:
--   Throughout, $\alpha,\beta,\gamma$ are arbitrary sets. A relation from $\alpha$ to $\beta$ is a subset $R\subseteq\alpha\times\beta$. For $R\subseteq\alpha\times\beta$ and $S\subseteq\beta\times\gamma$ we write $RS$ for their composition in path order (first $R$, then $S$):
--   $$(x,z)\in RS\iff\exists\,y\in\beta:\ (x,y)\in R\ \text{and}\ (y,z)\in S .$$
--   $\mathrm{Id}$ denotes the identity relation, and for $R\subseteq\alpha\times\alpha$, $R^*$ is the reflexive–transitive closure: $(x,y)\in R^*$ iff there are $k\ge 0$ and $x=x_0,x_1,\dots,x_k=y$ with $(x_{i-1},x_i)\in R$ for $1\le i\le k$. Composition is associative, so longer products are written without brackets.
--
--   1. **Block relation.** Given $E\subseteq\alpha\times\alpha$, $F\subseteq\alpha\times\beta$, $G\subseteq\beta\times\alpha$ and $H\subseteq\beta\times\beta$, the block relation $\begin{bmatrix}E&F\\G&H\end{bmatrix}$ is the relation on the disjoint union $\alpha\sqcup\beta$ that relates two points of $\alpha$ iff they are related by $E$, a point of $\alpha$ to a point of $\beta$ iff they are related by $F$, a point of $\beta$ to a point of $\alpha$ iff they are related by $G$, and two points of $\beta$ iff they are related by $H$. It is a directed graph with two kinds of vertices.
--   2. **Elementary laws.** For relations of matching types: if $R\subseteq S$ then $R^*\subseteq S^*$; $\emptyset^*=\mathrm{Id}$; $R^*R^*=R^*$; $R^*=\mathrm{Id}\cup R^*R$; $A(B\cup C)=AB\cup AC$; and $(A\cup B)C=AC\cup BC$.
--   3. **Denesting and sliding.** For $A,B\subseteq\alpha\times\alpha$, $(A\cup B)^*=A^*(BA^*)^*$. For $A\subseteq\alpha\times\beta$ and $B\subseteq\beta\times\alpha$,
--   $$A\,(BA)^*=(AB)^*A\qquad\text{and}\qquad (AB)^*=\mathrm{Id}\cup A\,(BA)^*B .$$
--   4. **Eliminating two internal boundaries.** For $A,B,C,D\subseteq\alpha\times\alpha$,
--   $$(A\cup BD^*C)^*\,BD^*=A^*B\,(D\cup CA^*B)^*,\qquad (A\cup BD^*C)^*=A^*\cup A^*B\,(D\cup CA^*B)^*\,CA^*,$$
--   and for $L,R,B,E,D\subseteq\alpha\times\alpha$,
--   $$(LR\cup BD^*ER)^*\,(L\cup BD^*E)=(LR)^*L\;\cup\;(LR)^*B\,\big(D\cup ER\,(LR)^*B\big)^*E\,(RL)^* .$$
--
--   The laws in items 2 and 3 are the standard Kleene-algebra identities (monotonicity, unfolding, denesting and sliding) for relations. The identities in item 4 say that paths alternating between two kinds of loops can be summarized by eliminating either kind first; they are the computational core of the associativity of the product of boundary diagrams, which record how a two-way automaton can traverse a segment of its tape. The block relation is the edge relation obtained by joining two path networks.
--
--   **Formalization Note** Relations are Mathlib's `SetRel α β`; composition is `R ○ S` (`SetRel.comp`, in path order), the identity is `SetRel.id`, and the closure `relStar R` (from the base definitions) is defined through `Relation.ReflTransGen`. The block relation is `blockRelation E F G H : SetRel (α ⊕ β) (α ⊕ β)`. The laws are `relStar_mono`, `relStar_empty`, `relStar_comp_self`, `relStar_unfold`, `relComp_union`, `union_relComp`, `relStar_union`, `comp_relStar_rotate`, `relStar_comp_unfold`, `relStar_block_forward`, `relStar_block_return` and `relStar_block_exit`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Relations.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Relations.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayDeterminization mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayDeterminization

namespace OAI

namespace TwoWayComplementation

open scoped SetRel

@[gcongr]
theorem relStar_mono {α : Type*} {R S : SetRel α α} (h : R ⊆ S) :
    relStar R ⊆ relStar S :=
  fun _ hab => hab.mono (fun _ _ hxy => h hxy) _ _

@[simp]
theorem relStar_empty {α : Type*} : relStar (∅ : SetRel α α) = SetRel.id := by
  ext ⟨a, b⟩
  constructor
  · intro h
    cases h with
    | refl => rfl
    | tail _ h => exact h.elim
  · rintro rfl
    exact Relation.ReflTransGen.refl

@[simp]
theorem relStar_comp_self {α : Type*} (R : SetRel α α) :
    relStar R ○ relStar R = relStar R := by
  ext ⟨a, b⟩
  exact ⟨fun ⟨_, hac, hcb⟩ => hac.trans hcb,
    fun hab => ⟨b, hab, Relation.ReflTransGen.refl⟩⟩

/-- A directed graph partitioned into two kinds of vertices. -/
def blockRelation {α β : Type*} (E : SetRel α α) (F : SetRel α β)
    (G : SetRel β α) (H : SetRel β β) : SetRel (α ⊕ β) (α ⊕ β) :=
  {xy | match xy.1, xy.2 with
    | .inl a, .inl b => (a, b) ∈ E
    | .inl a, .inr b => (a, b) ∈ F
    | .inr a, .inl b => (a, b) ∈ G
    | .inr a, .inr b => (a, b) ∈ H}

/-- Closure of a union factors into alternating finite paths. -/
theorem relStar_union {α : Type*} (A B : SetRel α α) :
    relStar (A ∪ B) = relStar A ○ relStar (B ○ relStar A) := by
  ext ⟨a, b⟩
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨b, .refl, .refl⟩
    | @head a c hstep _ ih =>
      obtain ⟨d, hcd, hdb⟩ := ih
      rcases hstep with hA | hB
      · exact ⟨d, hcd.head hA, hdb⟩
      · exact ⟨a, .refl, hdb.head ⟨c, hB, hcd⟩⟩
  · rintro ⟨c, hac, hcb⟩
    have hA := relStar_mono (show A ⊆ A ∪ B from Set.subset_union_left) hac
    refine hA.trans (Relation.reflTransGen_closed ?_ _ _ hcb)
    rintro x y ⟨z, hxz, hzy⟩
    exact (relStar_mono Set.subset_union_left hzy).head (Or.inr hxz)

/-- A finite alternating path can be rotated between its endpoint types. -/
theorem comp_relStar_rotate {α β : Type*} (A : SetRel α β) (B : SetRel β α) :
    A ○ relStar (B ○ A) = relStar (A ○ B) ○ A := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨c, hac, hcb⟩
    induction hcb with
    | refl => exact ⟨a, .refl, hac⟩
    | @tail x y _ hxy ih =>
      obtain ⟨p, hap, hpx⟩ := ih
      obtain ⟨q, hxq, hqy⟩ := hxy
      exact ⟨q, hap.tail ⟨x, hpx, hxq⟩, hqy⟩
  · rintro ⟨c, hac, hcb⟩
    induction hac generalizing b with
    | refl => exact ⟨b, hcb, .refl⟩
    | @tail x y _ hxy ih =>
      obtain ⟨p, hxp, hpy⟩ := hxy
      obtain ⟨q, haq, hqp⟩ := ih p hxp
      exact ⟨q, haq, hqp.tail ⟨y, hpy, hcb⟩⟩

theorem relComp_union {α β γ : Type*} (A : SetRel α β) (B C : SetRel β γ) :
    A ○ (B ∪ C) = (A ○ B) ∪ (A ○ C) := by
  ext ⟨x, y⟩
  simp only [SetRel.comp, Set.mem_ofPred_eq, Set.mem_union]
  aesop

theorem union_relComp {α β γ : Type*} (A B : SetRel α β) (C : SetRel β γ) :
    (A ∪ B) ○ C = (A ○ C) ∪ (B ○ C) := by
  ext ⟨x, y⟩
  simp only [SetRel.comp, Set.mem_ofPred_eq, Set.mem_union]
  aesop

theorem relStar_unfold {α : Type*} (R : SetRel α α) :
    relStar R = SetRel.id ∪ (relStar R ○ R) := by
  ext ⟨x, y⟩
  constructor
  · intro h
    cases h with
    | refl => exact Or.inl rfl
    | @tail z _ hxz hzy => exact Or.inr ⟨z, hxz, hzy⟩
  · rintro (h | ⟨z, hxz, hzy⟩)
    · cases h
      exact Relation.ReflTransGen.refl
    · exact hxz.tail hzy

/-- Eliminating two internal boundaries in either order gives the same through relation. -/
theorem relStar_block_forward {α : Type*} (A B C D : SetRel α α) :
    relStar (A ∪ (B ○ relStar D ○ C)) ○ B ○ relStar D =
      relStar A ○ B ○ relStar (D ∪ (C ○ relStar A ○ B)) := by
  simpa only [relStar_union, SetRel.comp_assoc] using
    congrArg (relStar A ○ ·)
      (comp_relStar_rotate (B ○ relStar D) (C ○ relStar A)).symm

/-- The corresponding return relation when eliminating two internal boundaries. -/
theorem relStar_block_return {α : Type*} (A B C D : SetRel α α) :
    relStar (A ∪ (B ○ relStar D ○ C)) =
      relStar A ∪ (relStar A ○ B ○ relStar (D ∪ (C ○ relStar A ○ B)) ○
        C ○ relStar A) := by
  have hunfold := congrArg (relStar A ○ ·)
    (relStar_unfold (B ○ relStar D ○ C ○ relStar A))
  have hreturn : relStar (A ∪ (B ○ relStar D ○ C)) =
      relStar A ∪ (relStar (A ∪ (B ○ relStar D ○ C)) ○ B ○ relStar D ○
        C ○ relStar A) := by
    simpa only [relStar_union, relComp_union, SetRel.comp_id, SetRel.comp_assoc] using hunfold
  rw [hreturn, relStar_block_forward]

theorem relStar_comp_unfold {α β : Type*} (R : SetRel α β) (L : SetRel β α) :
    relStar (R ○ L) = SetRel.id ∪ (R ○ relStar (L ○ R) ○ L) := by
  calc
    _ = SetRel.id ∪ (relStar (R ○ L) ○ (R ○ L)) := relStar_unfold _
    _ = _ := by rw [comp_relStar_rotate, SetRel.comp_assoc]

theorem relStar_block_exit {α : Type*} (L R B E D : SetRel α α) :
    relStar ((L ○ R) ∪ (B ○ relStar D ○ E ○ R)) ○ (L ∪ (B ○ relStar D ○ E)) =
      (relStar (L ○ R) ○ L) ∪
        (relStar (L ○ R) ○ B ○ relStar (D ∪ (E ○ R ○ relStar (L ○ R) ○ B)) ○
          E ○ relStar (R ○ L)) := by
  have hF := relStar_block_forward (L ○ R) B (E ○ R) D
  have hW := relStar_block_return (L ○ R) B (E ○ R) D
  simp only [SetRel.comp_assoc] at hF hW
  calc
    _ = (relStar ((L ○ R) ∪ (B ○ relStar D ○ E ○ R)) ○ L) ∪
        ((relStar ((L ○ R) ∪ (B ○ relStar D ○ E ○ R)) ○ B ○ relStar D) ○ E) := by
          simp only [relComp_union, SetRel.comp_assoc]
    _ = ((relStar (L ○ R) ∪
          (relStar (L ○ R) ○ B ○ relStar (D ∪ (E ○ R ○ relStar (L ○ R) ○ B)) ○
            E ○ R ○ relStar (L ○ R))) ○ L) ∪
        ((relStar (L ○ R) ○ B ○ relStar (D ∪ (E ○ R ○ relStar (L ○ R) ○ B))) ○ E) := by
          simpa only [SetRel.comp_assoc] using
            congrArg₂ (· ∪ ·) (congrArg (· ○ L) hW) (congrArg (· ○ E) hF)
    _ = _ := by
      rw [relStar_comp_unfold R L]
      simp only [union_relComp, relComp_union, SetRel.comp_id, SetRel.comp_assoc]
      ac_rfl

end TwoWayComplementation

end OAI


