-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
-- name    : OAI_Combinatorics_FiniteCircle_BlockMatching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:01:43.078165+00:00
-- url     : https://prove2.me/theorems/93d5b3cc-b8a5-4bcc-805c-56d2b9ec4c43
-- title:
--   Within-block offsets, block pairs and target blocks of a word matching
-- statement:
--   Let $x,y$ be finite words and let $(L,R)$ be a matching of size $q$ between them: strictly increasing maps $L$ and $R$ from $\{0,\dots,q-1\}$ to the positions of $x$ and of $y$ with $x_{L(k)}=y_{R(k)}$ for all $k$. Fix a block length $w$, so that position $n$ lies in block $\lfloor n/w\rfloor$ at offset $n\bmod w$, and recall that the source block $B_w(i)$ is the set of indices $k$ with $\lfloor L(k)/w\rfloor=i$.
--
--   1. **Local indices.** For $w>0$ and a set $S$ of matching indices, enumerate $S$ increasingly as $k_0<k_1<\dots<k_{|S|-1}$; the local index list is
--   $$
--   \bigl(L(k_0)\bmod w,\ L(k_1)\bmod w,\ \dots,\ L(k_{|S|-1})\bmod w\bigr),
--   $$
--   a list of offsets in $\{0,\dots,w-1\}$ of length $|S|$.
--   2. **Block pairs.** For block indices $i$ of $x$ and $j$ of $y$,
--   $$
--   B_w(i,j)=\{\,k:\ \lfloor L(k)/w\rfloor=i,\ \lfloor R(k)/w\rfloor=j\,\},
--   $$
--   the pairs leading from block $i$ of $x$ to block $j$ of $y$; it is the intersection of the source block $B_w(i)$ with the source block of $j$ for the reversed matching.
--   3. **Target blocks.** For a set $S$ of matching indices, $\{\lfloor R(k)/w\rfloor : k\in S\}$ is the set of blocks of $y$ that $S$ reaches.
--
--   When $x$ and $y$ are block encodings with codewords of length $w$, the pairs in a block pair form a matching between two codewords, and their local indices on the two sides are the position lists that the anchor-locality property of the code constrains. A source block whose partners span a short interval of $y$ reaches only a few target blocks, so one block pair carries a large part of the block; this is how a letter-level correspondence is recovered from a bit-level alignment.
--
--   **Formalization Note** The definitions live in the namespace of `WordMatching`: `localIndices A hw S` (with `hw : 0 < w`, the increasing enumeration being `S.orderEmbOfFin`), `blockPair A w i j`, defined as `A.sourceBlock w i ∩ A.symm.sourceBlock w j`, and `targetBlocks A w S`, a finset of natural numbers; `localIndices_length` is the length lemma. Block indices use natural-number division.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/BlockMatching.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/BlockMatching.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FiniteCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

def localIndices (A : WordMatching x y q) {w : ℕ} (hw : 0 < w)
    (S : Finset (Fin q)) : List (Fin w) :=
  List.ofFn (fun k : Fin S.card =>
    ⟨(A.left (S.orderEmbOfFin rfl k)).val % w, Nat.mod_lt _ hw⟩)

@[simp] theorem localIndices_length (A : WordMatching x y q) {w : ℕ} (hw : 0 < w)
    (S : Finset (Fin q)) : (A.localIndices hw S).length = S.card := List.length_ofFn

def blockPair (A : WordMatching x y q) (w i j : ℕ) : Finset (Fin q) :=
  A.sourceBlock w i ∩ A.symm.sourceBlock w j

def targetBlocks (A : WordMatching x y q) (w : ℕ) (S : Finset (Fin q)) : Finset ℕ :=
  S.image (fun k => (A.right k).val / w)

end WordMatching

end FiniteCircle

end OAI


