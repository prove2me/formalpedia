-- Prove2me | Definitions.Def_OAI_Combinatorics_ParityLifts_RootedTests
-- name    : OAI_Combinatorics_ParityLifts_RootedTests
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:16:13.488301+00:00
-- url     : https://prove2.me/theorems/4b3ae986-6241-4dcc-b587-e9552f8a2924
-- title:
--   Rooted homomorphism counts from sources with bounded bags
-- statement:
--   This file introduces rooted test graphs and their rooted homomorphism counts, the building blocks of an algebra of functions on $k$-tuples that can express Weisfeiler–Leman colours.
--
--   1. **Rooted tests.** For $k,t\in\mathbb{N}$, a rooted test $F$ consists of a finite vertex set $V_F$ with a symmetric relation $R_F$ (loops allowed), a root tuple $\ell=(\ell_0,\dots,\ell_{k-1})\in V_F^{\,k}$ (repetitions allowed), and a ranked bag tree for $R_F$ on a finite node set, with bags of size at most $t$ and adjacent bags sharing fewer than $t$ vertices, whose root bag is exactly $\{\ell_0,\dots,\ell_{k-1}\}$.
--   2. **Relation maps.** For a relation $R$ on a set $A$ and a graph $G$ on $V$, a relation map is a function $f\colon A\to V$ with $f(a)\sim_G f(b)$ whenever $R(a,b)$. When $R$ is the adjacency relation of a graph, relation maps are exactly graph homomorphisms.
--   3. **Rooted counts.** For a finite graph $G$ on $V$ and $x\in V^k$,
--   $$
--   h_F(G,x)=\bigl|\{f\colon V_F\to V \text{ a relation map}:\ f(\ell_i)=x_i \text{ for all } i\in[k]\}\bigr|\in\mathbb{Q}.
--   $$
--   Every relation map is counted for exactly one root tuple: the pairs $(x,f)$ with $f$ counted in $h_F(G,x)$ correspond bijectively to all relation maps $V_F\to V$, so $\sum_{x\in V^k}h_F(G,x)$ is the total number of relation maps.
--   4. **Single-bag tests.** If $A$ is finite with $|A|\le t$, $R$ is a symmetric relation on $A$ and $r\colon[k]\to A$ is surjective, then $A$ with relation $R$, roots $r$ and a one-node tree whose only bag is $A$ is a rooted test.
--   5. **Isolated roots.** For $k\le t$, the single-bag test on $[k]$ with empty relation and roots $\ell_i=i$ satisfies $h(G,x)=1$ for every finite graph $G$ and every $x$.
--
--   Rooted counts serve as the tests in the direction from homomorphism counts to Weisfeiler–Leman equivalence: results built on these definitions show that rational linear combinations of the functions $x\mapsto h_F(G,x)$, over sources with bags of size at most $t$, express every colour-class indicator of $k$-variable refinement, so equal homomorphism counts from all such sources force equal colour histograms. A loop in $R_F$ makes the count vanish on every simple graph; such loops can arise when roots are identified and are kept rather than deleted.
--
--   **Formalization Note** The structure is `RootedTest k t`, with fields `Vertex`, `relation`, `symmetric`, `roots`, `Node`, `tree` and `root_bag` (plus finiteness instances). Relation maps are `RelationMaps R G`, the rooted maps are `RootedTest.Maps F G x`, and `RootedTest.count` is $h_F(G,x)$, cast to the rationals. The bijections of items 2 and 3 are `relationMapsSimpleEquiv` and `RootedTest.totalEquiv`; items 4 and 5 are `singleBagTest`, `isolatedTest` and `isolatedTest_count`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/RootedTests.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/RootedTests.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ParityLifts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection
import Definitions.Def_OAI_Combinatorics_ParityLifts_RankedTrees

namespace OAI

namespace ParityWL

open scoped BigOperators

section RootedTests

open scoped Classical

/-- Sources may have loops during root gluing. A loop contributes zero on every
simple target; it is never silently deleted. -/
structure RootedTest (k t : ℕ) where
  Vertex : Type
  vertexFintype : Fintype Vertex
  relation : Vertex → Vertex → Prop
  symmetric : Std.Symm relation
  roots : Fin k → Vertex
  Node : Type
  nodeFintype : Fintype Node
  tree : RankedBagTree (N := Node) relation t
  root_bag : tree.bag tree.root = Finset.univ.image roots

attribute [instance] RootedTest.vertexFintype RootedTest.nodeFintype

noncomputable def RelationMaps {A V : Type} (R : A → A → Prop) (G : SimpleGraph V) :=
  {f : A → V // ∀ a b, R a b → G.Adj (f a) (f b)}

noncomputable instance relationMapsFintype {A V : Type} [Fintype A] [Fintype V]
    (R : A → A → Prop) (G : SimpleGraph V) : Fintype (RelationMaps R G) := by
  unfold RelationMaps
  infer_instance

noncomputable def RootedTest.Maps {k t : ℕ} (F : RootedTest k t) {V : Type}
    (G : SimpleGraph V) (x : Fin k → V) :=
  {f : RelationMaps F.relation G // ∀ i, f.1 (F.roots i) = x i}

noncomputable instance rootedMapsFintype {k t : ℕ} (F : RootedTest k t)
    {V : Type} [Fintype V] (G : SimpleGraph V) (x : Fin k → V) : Fintype (F.Maps G x) := by
  unfold RootedTest.Maps
  infer_instance

noncomputable def RootedTest.count {k t : ℕ} (F : RootedTest k t)
    {V : Type} [Fintype V] (G : SimpleGraph V) (x : Fin k → V) : ℚ :=
  Fintype.card (F.Maps G x)

noncomputable def RootedTest.totalEquiv {k t : ℕ} (F : RootedTest k t)
    {V : Type} (G : SimpleGraph V) :
    ((x : Fin k → V) × F.Maps G x) ≃ RelationMaps F.relation G where
  toFun f := f.2.1
  invFun f := ⟨fun i => f.1 (F.roots i), ⟨f, fun _ => rfl⟩⟩
  left_inv f := by
    rcases f with ⟨x, f, hf⟩
    have he : (fun i => f.1 (F.roots i)) = x := funext hf
    subst x
    rfl
  right_inv _ := rfl

noncomputable def relationMapsSimpleEquiv {A V : Type} (F : SimpleGraph A)
    (G : SimpleGraph V) : RelationMaps F.Adj G ≃ (F →g G) where
  toFun f := ⟨f.1, fun h => f.2 _ _ h⟩
  invFun f := ⟨f, fun _ _ h => f.map_adj h⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def singleBagTest {k t : ℕ} {A : Type} [Fintype A]
    (R : A → A → Prop) (hs : Std.Symm R) (r : Fin k → A)
    (hr : Function.Surjective r) (hA : Fintype.card A ≤ t) : RootedTest k t where
  Vertex := A
  vertexFintype := inferInstance
  relation := R
  symmetric := hs
  roots := r
  Node := Unit
  nodeFintype := inferInstance
  tree :=
    { root := ()
      parent := fun _ => ()
      rank := fun _ => 0
      parent_lt := by intro i hi; exact (hi (Subsingleton.elim _ _)).elim
      bag := fun _ => Finset.univ
      top := fun _ => ()
      top_mem := fun _ => Finset.mem_univ _
      top_ancestor := by intro x i _; cases i; exact .refl
      interval_mem := by intros; exact Finset.mem_univ _
      edge_cover := fun _ _ _ => ⟨(), Finset.mem_univ _, Finset.mem_univ _⟩
      width := by intro _; simpa only [Finset.card_univ] using hA
      intersection := by intro i hi; exact (hi (Subsingleton.elim _ _)).elim }
  root_bag := by
    ext a
    simp only [Finset.mem_univ, Finset.mem_image, true_and, true_iff]
    exact hr a

noncomputable def isolatedTest (k t : ℕ) (hkt : k ≤ t) : RootedTest k t :=
  singleBagTest (fun _ _ : Fin k => False) ⟨fun _ _ h => h⟩ id Function.surjective_id
    (by simpa using hkt)

lemma isolatedTest_count (k t : ℕ) (hkt : k ≤ t) {V : Type} [Fintype V]
    (G : SimpleGraph V) (x : Fin k → V) : (isolatedTest k t hkt).count G x = 1 := by
  let f : (isolatedTest k t hkt).Maps G x := ⟨⟨x, fun _ _ h => h.elim⟩, fun _ => rfl⟩
  have hi : Unique ((isolatedTest k t hkt).Maps G x) :=
    { default := f
      uniq := by
        intro g
        apply Subtype.ext
        apply Subtype.ext
        funext i
        exact g.2 i }
  simp only [RootedTest.count, Fintype.card_unique, Nat.cast_one]

end RootedTests

end ParityWL

end OAI


