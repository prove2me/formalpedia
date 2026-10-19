-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
-- name    : OAI_Combinatorics_FiniteCircle_Matching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T12:36:39.67323+00:00
-- url     : https://prove2.me/theorems/baf7d9ca-0cb2-4d80-b666-b85d5fec50cd
-- title:
--   Segments, slides and order-preserving matchings between words
-- statement:
--   Let $x,y$ be finite words over an alphabet $\alpha$, with positions numbered from $0$. The module introduces the combinatorial vocabulary used to analyse common subsequences block by block.
--
--   1. **Segments.** $\operatorname{seg}(x,s,n)$ is the factor of $x$ that starts at position $s$ and has length $n$, cut short at the end of $x$ if necessary; it has length exactly $n$ when $s+n\le|x|$.
--   2. **Slides.** A slide replaces a word by another of the same length by deleting one letter and inserting one letter: a forward slide is $u\,a\,v\,t\mapsto u\,v\,b\,t$ and a backward slide is $u\,v\,b\,t\mapsto u\,a\,v\,t$ (with $u,v,t$ words and $a,b$ letters). Thus $y$ arises from $x$ by one slide exactly when $y$ is obtained from $x$ by deleting one letter and then inserting one letter at any position (a substitution is the case of empty $v$). A slide path of length $n$ from $x$ to $y$ is a chain of $n$ slides.
--   3. **Word matchings.** A matching of size $q$ between $x$ and $y$ is a pair of strictly increasing maps $L:\{0,\dots,q-1\}\to\{0,\dots,|x|-1\}$ and $R:\{0,\dots,q-1\}\to\{0,\dots,|y|-1\}$ with $x_{L(i)}=y_{R(i)}$ for every $i$; in other words, a common subsequence of length $q$ together with its positions in both words. The reversed matching exchanges $L$ and $R$.
--   4. **Spans, source blocks and losses.** For a set $S$ of matching indices, the right span $\operatorname{span}_R(S)$ is the set of positions $j$ of $y$ with $R(i)\le j\le R(k)$ for some $i,k\in S$, that is, the interval of $y$ covered by the partners of $S$. For a block length $w$ and a block index $i$, the source block
--   $$
--   B_w(i)=\{\,k : \lfloor L(k)/w\rfloor=i\,\}
--   $$
--   collects the pairs whose left endpoint lies in the $i$-th block $\{iw,\dots,iw+w-1\}$ of $x$. Its source loss $w-|B_w(i)|$ counts the positions of that block left unmatched, and its span loss $|\operatorname{span}_R(B_w(i))|-|B_w(i)|$ counts the unmatched positions of $y$ inside the interval spanned by its partners.
--   5. **Convex index sets.** A set $S$ of matching indices is convex if it contains every index lying between two of its elements.
--
--   An optimal common subsequence is a matching of size $\operatorname{lcs}(x,y)$, so matchings make the longest-common-subsequence length concrete. Cutting a matching between block-encoded words into source blocks and measuring the two losses is the basic device for showing that a nearly optimal alignment of codewords must respect the block structure. Slides model length-preserving pairs of edits and connect two words of equal length through a path of length controlled by their deficit.
--
--   **Formalization Note** A matching is the structure `WordMatching x y q`, whose fields `left` and `right` are order embeddings of `Fin q` into the position types of `x` and `y`, and `symm` is the reversed matching. `Slide` and `SlidePath n x y` are inductive predicates and `segment x s n` is `(x.drop s).take n`. Block indices use natural-number division, so for $w=0$ every pair lies in block $0$. `sourceLoss` and `spanLoss` use truncated subtraction; the span loss never truncates (a span contains the right endpoints of its pairs), and the source loss does not truncate when $w>0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Matching.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Matching.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FiniteCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

def segment {α : Type*} (x : List α) (start size : ℕ) : List α := (x.drop start).take size

theorem length_segment {α : Type*} {x : List α} {start size : ℕ}
    (h : start + size ≤ x.length) : (segment x start size).length = size := by
  simp only [segment, List.length_take, List.length_drop]
  omega

inductive Slide {α : Type*} : List α → List α → Prop
  | forward (u v t : List α) (a b : α) :
      Slide (u ++ a :: (v ++ t)) (u ++ v ++ b :: t)
  | backward (u v t : List α) (a b : α) :
      Slide (u ++ v ++ b :: t) (u ++ a :: (v ++ t))

namespace Slide
variable {α : Type*} {x y : List α}

end Slide

inductive SlidePath {α : Type*} : ℕ → List α → List α → Prop
  | nil (x : List α) : SlidePath 0 x x
  | cons {n : ℕ} {x y z : List α} : Slide x y → SlidePath n y z → SlidePath (n + 1) x z

namespace SlidePath
variable {α : Type*} {x y z : List α} {n m : ℕ}

end SlidePath

structure WordMatching {α : Type*} (x y : List α) (q : ℕ) where
  left : Fin q ↪o Fin x.length
  right : Fin q ↪o Fin y.length
  letters : ∀ i, x.get (left i) = y.get (right i)

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

def symm (A : WordMatching x y q) : WordMatching y x q where
  left := A.right
  right := A.left
  letters i := (A.letters i).symm

def rightSpan (A : WordMatching x y q) (S : Finset (Fin q)) : Finset (Fin y.length) :=
  Finset.univ.filter (fun j => ∃ i ∈ S, ∃ k ∈ S, A.right i ≤ j ∧ j ≤ A.right k)

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

def sourceBlock (A : WordMatching x y q) (w i : ℕ) : Finset (Fin q) :=
  Finset.univ.filter (fun k => (A.left k).val / w = i)

@[simp] theorem mem_sourceBlock (A : WordMatching x y q) (w i : ℕ) (k : Fin q) :
    k ∈ A.sourceBlock w i ↔ (A.left k).val / w = i := by simp [sourceBlock]

def sourceLoss (A : WordMatching x y q) (w i : ℕ) : ℕ := w - (A.sourceBlock w i).card

def spanLoss (A : WordMatching x y q) (w i : ℕ) : ℕ :=
  (A.rightSpan (A.sourceBlock w i)).card - (A.sourceBlock w i).card

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

def ConvexIndices (S : Finset (Fin q)) : Prop :=
  ∀ i ∈ S, ∀ k ∈ S, ∀ j, i ≤ j → j ≤ k → j ∈ S

end WordMatching

end FiniteCircle

end OAI


