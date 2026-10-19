-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
-- name    : OAI_Combinatorics_FiniteCircle_TaggedRows
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T12:37:48.93582+00:00
-- url     : https://prove2.me/theorems/5c96bdd3-9583-4b1f-9720-5d4d330f091f
-- title:
--   Tagged rows and restriction of word matchings to segments
-- statement:
--   Let $J$ and $\beta$ be sets. For a tag $j\in J$ and a word $u=u_1\cdots u_m$ over $\beta$ write $j\otimes u=(j,u_1)(j,u_2)\cdots(j,u_m)$, the copy of $u$ in which every letter carries the label $j$. For words $x,y$ over $\beta$, a matching $(L,R)$ of size $q$ between them consists of strictly increasing position maps $L,R$ on $\{0,\dots,q-1\}$ with $x_{L(i)}=y_{R(i)}$, and for a block length $W$ the source block $B_W(i)$ is the set of indices $k$ with $\lfloor L(k)/W\rfloor=i$. The module defines the following objects.
--
--   1. **Tagged rows.** For a list of tags $j_1,\dots,j_r$ and a word-valued map $W:J\to\beta^{\ast}$, the tagged row is the word over $J\times\beta$
--   $$
--   \operatorname{row}(j_1\cdots j_r;W)=(j_1\otimes W(j_1))\,(j_2\otimes W(j_2))\cdots(j_r\otimes W(j_r)),
--   $$
--   so the empty list gives the empty word and $\operatorname{row}(j\,js;W)=(j\otimes W(j))\operatorname{row}(js;W)$.
--   2. **Restriction of a matching to segments.** Let $S$ be a set of matching indices, and let $[s,s+n)$ and $[t,t+m)$ be windows of positions with $s+n\le|x|$ and $t+m\le|y|$ such that $s\le L(k)<s+n$ and $t\le R(k)<t+m$ for every $k\in S$. Enumerating $S$ increasingly as $k_0<k_1<\dots<k_{|S|-1}$, the pairs $\bigl(L(k_i)-s,\;R(k_i)-t\bigr)$ form a matching of size $|S|$ between the segments $x_s\cdots x_{s+n-1}$ and $y_t\cdots y_{t+m-1}$ (the module also records that the $i$-th letter of the segment of $x$ is $x_{s+i}$).
--   3. **Single-target rows.** The source block $B_W(i)$ has a single target row if all its right endpoints lie in one block of $y$: there is $j$ with $\lfloor R(k)/W\rfloor=j$ for all $k\in B_W(i)$ (this holds vacuously for an empty block).
--   4. **Uniform concatenations.** If every word $f(a)$, $a$ in a list $xs$, has length $\Lambda$, then the concatenation of the $f(a)$ along $xs$ has length $|xs|\cdot\Lambda$.
--
--   The circle words of the construction are concatenations of rows of tagged copies of lower-level words. Tags make letters coming from different blocks distinct, so a common subsequence of two rows splits into matchings between blocks with equal tags. The restriction to segments turns such pieces into genuine matchings of the blocks, and the single-target dichotomy separates the case where a whole source row is sent into one row of the other word from the case where it is split, which costs a large span loss.
--
--   **Formalization Note** `taggedRow js W` is `js.flatMap (fun j => (W j).map (fun b => (j,b)))`. `WordMatching.onSegments` is a definition producing the restricted matching; the increasing enumeration of $S$ is `S.orderEmbOfFin`. `get_segment`, `taggedRow_nil`, `taggedRow_cons` and `length_flatMap_uniform` are auxiliary lemmas, and block indices use natural-number division.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/TaggedRows.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/TaggedRows.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FiniteCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

def taggedRow {J β : Type*} (js : List J) (W : J → List β) : List (J × β) :=
  js.flatMap (fun j => (W j).map (fun b => (j,b)))

@[simp] theorem taggedRow_nil {J β : Type*} (W : J → List β) : taggedRow [] W = [] := rfl
@[simp] theorem taggedRow_cons {J β : Type*} (j : J) (js : List J) (W : J → List β) :
    taggedRow (j::js) W = (W j).map (fun b => (j,b)) ++ taggedRow js W := rfl

theorem get_segment {β : Type*} (x : List β) {s n : ℕ} (hs : s+n ≤ x.length)
    (i : Fin (segment x s n).length) :
    (segment x s n).get i = x.get ⟨s+i.val, by
      have hi := i.isLt
      simp only [length_segment hs] at hi
      omega⟩ := by
  change ((x.drop s).take n)[i.val] = _
  simp only [List.getElem_take, List.getElem_drop, List.get_eq_getElem]

namespace WordMatching
variable {β : Type*} {x y : List β} {q : ℕ}

def onSegments (A : WordMatching x y q) (S : Finset (Fin q))
    {s n t m : ℕ} (hs : s+n ≤ x.length) (ht : t+m ≤ y.length)
    (hleft : ∀ i ∈ S, s ≤ (A.left i).val ∧ (A.left i).val < s+n)
    (hright : ∀ i ∈ S, t ≤ (A.right i).val ∧ (A.right i).val < t+m) :
    WordMatching (segment x s n) (segment y t m) S.card := by
  let f : Fin S.card → Fin (segment x s n).length := fun i =>
    ⟨(A.left (S.orderEmbOfFin rfl i)).val-s, by
      rw [length_segment hs]
      have hh := hleft _ (S.orderEmbOfFin_mem rfl i)
      omega⟩
  let g : Fin S.card → Fin (segment y t m).length := fun i =>
    ⟨(A.right (S.orderEmbOfFin rfl i)).val-t, by
      rw [length_segment ht]
      have hh := hright _ (S.orderEmbOfFin_mem rfl i)
      omega⟩
  have hf : StrictMono f := by
    intro i j hij
    have hh : (A.left (S.orderEmbOfFin rfl i)).val < (A.left (S.orderEmbOfFin rfl j)).val :=
      A.left.strictMono ((S.orderEmbOfFin rfl).strictMono hij)
    have hi := hleft _ (S.orderEmbOfFin_mem rfl i)
    change (A.left (S.orderEmbOfFin rfl i)).val-s < (A.left (S.orderEmbOfFin rfl j)).val-s
    omega
  have hg : StrictMono g := by
    intro i j hij
    have hh : (A.right (S.orderEmbOfFin rfl i)).val < (A.right (S.orderEmbOfFin rfl j)).val :=
      A.right.strictMono ((S.orderEmbOfFin rfl).strictMono hij)
    have hi := hright _ (S.orderEmbOfFin_mem rfl i)
    change (A.right (S.orderEmbOfFin rfl i)).val-t < (A.right (S.orderEmbOfFin rfl j)).val-t
    omega
  refine ⟨OrderEmbedding.ofStrictMono f hf, OrderEmbedding.ofStrictMono g hg, ?_⟩
  intro i
  change (segment x s n).get (f i) = (segment y t m).get (g i)
  rw [get_segment x hs, get_segment y ht]
  have hi := hleft _ (S.orderEmbOfFin_mem rfl i)
  have hj := hright _ (S.orderEmbOfFin_mem rfl i)
  convert A.letters (S.orderEmbOfFin rfl i) using 1
  · congr 1
    apply Fin.ext
    change s+((A.left (S.orderEmbOfFin rfl i)).val-s) = _
    omega
  · congr 1
    apply Fin.ext
    change t+((A.right (S.orderEmbOfFin rfl i)).val-t) = _
    omega

end WordMatching

namespace WordMatching
variable {β : Type*} {x y : List β} {q : ℕ}

def singleTargetRow (A : WordMatching x y q) (W i : ℕ) : Prop :=
  ∃ j : ℕ, ∀ k ∈ A.sourceBlock W i, (A.right k).val/W = j

end WordMatching

theorem length_flatMap_uniform {α β : Type*} (xs : List α) (f : α → List β) (L : ℕ)
    (hl : ∀ a ∈ xs, (f a).length = L) : (xs.flatMap f).length = xs.length*L := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [hl a (by simp), ih (fun a ha => hl a (by simp [ha]))]
    nlinarith

end FiniteCircle

end OAI


