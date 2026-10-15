-- Prove2me | Definitions.Def_OAI_Analysis_ForestSpace_Trees
-- name    : OAI_Analysis_ForestSpace_Trees
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:00:59.473318+00:00
-- url     : https://prove2.me/theorems/6f551b57-ca5f-416c-9396-397f36680d05
-- title:
--   The word tree and the forest of countably branching trees of finite height
-- statement:
--   Two concrete forests are used. **Words** are finite sequences $s=(s_1,\dots,s_n)$ of natural numbers, ordered by the prefix relation: $s\le t$ if $s$ is an initial segment of $t$. The empty word is the root, so the words form the countably branching tree $\mathbb{N}^{<\omega}$. The **finite-height forest** $\mathcal V$ is the disjoint union over $h\ge1$ of the trees $\mathbb{N}^{\le h}$. Its vertices are pairs $(h,s)$ with $h\in\mathbb{N}$, $h\ge1$, and $s$ a word of length $|s|\le h$. They are ordered by $(h,s)\le(h',s')$ if and only if $h=h'$ and $s$ is a prefix of $s'$.
--
--   1. **Words.** Two words are equal when their letter sequences agree. The set of words is countable and infinite, its order is the prefix order, and every word has finitely many predecessors, namely its prefixes. The *child* of $s$ with label $j\in\mathbb{N}$ is $s^\frown j=(s_1,\dots,s_n,j)$, and the map $j\mapsto s^\frown j$ is injective.
--   2. **Vertices of $\mathcal V$.** Two vertices are equal when their heights and words agree. $\mathcal V$ is countable and infinite, its order is the one above, and every vertex has finitely many predecessors. For $h\ge1$ and $|s|\le h$, $\mathrm{node}(h,s)$ is the vertex $(h,s)\in\mathcal V$. A vertex $(h,s)$ with $|s|<h$ has the children $(h,s^\frown j)$, $j\in\mathbb{N}$, and the map $j\mapsto(h,s^\frown j)$ is injective.
--   3. **Tree path vectors.** Let $X(\mathcal V)\subseteq J(\mathcal V)^*$ be the closed span of the coordinate functionals $e_w^*$. For every pair $(h,s)\in\mathbb{N}\times\mathbb{N}^{<\omega}$,
--   $$
--   \pi(h,s)=\begin{cases}\sum_{w\le(h,s)}e_w^*, & \text{if } h\ge1 \text{ and } |s|\le h,\\ 0, & \text{otherwise.}\end{cases}
--   $$
--   This is a total version of the root-to-vertex path vector.
--
--   $\mathcal V$ is the concrete forest of the main construction. It is countable and infinite, and every vertex has finitely many ancestors; these are the standing hypotheses of the general-forest results. The component of height $h$ is the countably branching tree of height $h$. The children of a vertex give infinitely many branches, and the corresponding path vectors are used to build weakly null trees in $X(\mathcal V)$.
--
--   **Formalization Note** `Word` wraps a `List ℕ`. `Vertex` is a structure with fields `height`, `positive : 1 ≤ height`, `word` and `bounded : word.letters.length ≤ height`; both types and their orders come from the base definitions. This file adds `Word.ext`, `Word.le_def`, `Word.finiteAncestors`, `Word.child` and `Word.child_injective`, together with the corresponding `Vertex` lemmas. It also adds `Vertex.node`, `Vertex.child` (which takes the proof of $|s|<h$ as an argument), anonymous `Countable` and `Infinite` instances, and `Vertex.treePath h s`. The last is defined by cases so that it is total, and its off-tree value $0$ is never used.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Trees.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Trees.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForestSpace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Definitions.Def_OAI_Analysis_ForestSpace_Projections
import Definitions.Def_OAI_Analysis_ForestSpace_Renorming
import Definitions.Def_OAI_Analysis_ForestSpace_Coordinates

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section Words

namespace Word
@[ext] theorem ext {a b : Word} (h : a.letters = b.letters) : a = b := by
  cases a; cases b; cases h; rfl
instance : Countable Word := Function.Injective.countable (f := letters) (fun _ _ => ext)
instance : Infinite Word := Infinite.of_injective (fun n : ℕ => Word.mk [n]) (by
  intro i j h
  simpa using congrArg letters h)
@[simp] theorem le_def (a b : Word) : a ≤ b ↔ a.letters <+: b.letters := Iff.rfl
 theorem finiteAncestors (v : Word) : (Set.Iic v).Finite := by
  apply (v.letters.inits.toFinset.finite_toSet.image Word.mk).subset
  intro w hw
  exact ⟨w.letters,by simpa only [Finset.mem_coe,List.mem_toFinset,List.mem_inits] using (show w.letters <+: v.letters from hw),rfl⟩

def child (s : Word) (j : ℕ) : Word := ⟨s.letters++[j]⟩

 theorem child_injective (s : Word) : Function.Injective (child s) := by
  intro i j h
  have hh := congrArg letters h
  simpa [child] using hh

end Word

end Words

section FiniteHeightForest

namespace Vertex
@[ext] theorem ext {a b : Vertex} (hh : a.height = b.height) (hw : a.word = b.word) : a = b := by
  cases a; cases b; cases hh; cases hw; rfl
instance : Countable Vertex := Function.Injective.countable
  (f := fun v : Vertex => (v.height,v.word)) (by
    intro a b h
    exact ext (congrArg Prod.fst h) (congrArg Prod.snd h))
@[simp] theorem le_def (a b : Vertex) : a ≤ b ↔ a.height = b.height ∧ a.word ≤ b.word := Iff.rfl
 theorem finiteAncestors (v : Vertex) : (Set.Iic v).Finite := by
  apply Set.Finite.of_finite_image (f := fun w : Vertex => w.word)
    ((Word.finiteAncestors v.word).subset ?_) ?_
  · rintro _ ⟨w,hw,rfl⟩
    exact hw.2
  · intro a ha b hb he
    exact ext (ha.1.trans hb.1.symm) he

def node (h : ℕ) (hh : 1 ≤ h) (s : List ℕ) (hs : s.length ≤ h) : Vertex :=
  ⟨h,hh,Word.mk s,hs⟩

def child (v : Vertex) (hv : v.word.letters.length < v.height) (j : ℕ) : Vertex :=
  ⟨v.height,v.positive,Word.child v.word j,by
    simp only [Word.child,List.length_append,List.length_singleton]
    omega⟩

 theorem child_injective (v : Vertex) (hv : v.word.letters.length < v.height) :
    Function.Injective (child v hv) := by
  intro i j h
  exact Word.child_injective v.word (congrArg word h)

instance : Infinite Vertex := Infinite.of_injective
  (child (node 1 le_rfl [] (by simp)) (by simp [node]))
  (child_injective _ _)

/-- A total extension of the path vector; the off-tree values are never used. -/
noncomputable def treePath (h : ℕ) (s : List ℕ) : X Vertex :=
  if hh : 1 ≤ h then if hs : s.length ≤ h then
    pathVector (node h hh s hs) (finiteAncestors _) else 0 else 0

end Vertex

end FiniteHeightForest

end

end ForestSpace

end OAI


