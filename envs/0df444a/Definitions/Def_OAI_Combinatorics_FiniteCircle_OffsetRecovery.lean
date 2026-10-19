-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery
-- name    : OAI_Combinatorics_FiniteCircle_OffsetRecovery
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:04:27.640882+00:00
-- url     : https://prove2.me/theorems/f21d24ea-9d6c-4421-bd8c-5a47cbd7f721
-- title:
--   Offset matching predicates and well-aligned blocks for matchings of encoded words
-- statement:
--   Let $\bar x,\bar y$ be finite words and $(L,R)$ a matching of size $q$ between them: strictly increasing maps from $\{0,\dots,q-1\}$ to the positions of $\bar x$ and of $\bar y$ with $\bar x_{L(k)}=\bar y_{R(k)}$. Fix a block length $w$; for a block index $i$ and an offset $p$, the position $iw+p$ of $\bar x$ is the $p$-th position of block $i$.
--
--   1. **Matched offsets.** Offset $p$ of block $i$ is matched if $L(k)=iw+p$ for some $k$.
--   2. **Partner block.** If offset $p$ of block $i$ is matched by the pair $k$ (which is unique since $L$ is injective), its partner block is $\lfloor R(k)/w\rfloor$; otherwise the partner block is set to $0$.
--   3. **Duplicates.** Offset $p$ is a duplicate at block $i$ if the positions $iw+p$ and $(i+1)w+p$ are both matched, by pairs $k$ and $k'$, and their partners lie in the same block of $\bar y$: $\lfloor R(k)/w\rfloor=\lfloor R(k')/w\rfloor$.
--   4. **Good blocks.** Suppose $\bar x=\operatorname{enc}_c(x)$ and $\bar y=\operatorname{enc}_c(y)$ are block encodings of words $x,y$ over an alphabet $\alpha$ under a binary code $c:\alpha\to\{0,1\}^{w_0}$ (each letter replaced by its codeword), and let $\eta\in\mathbb{R}$. With $B_w(i)=\{k:\lfloor L(k)/w\rfloor=i\}$ the source block of block $i$ and $\operatorname{span}_R(S)$ the set of positions of $\bar y$ between the smallest and largest partner of $S$, the set of good blocks is
--   $$
--   G_\eta=\Bigl\{\,i<|x|:\ w-|B_w(i)|\le\eta w\ \text{ and }\ |\operatorname{span}_R(B_w(i))|-|B_w(i)|\le\eta w\,\Bigr\},
--   $$
--   the blocks that lose at most $\eta w$ positions on the source side and whose partners leave at most $\eta w$ gaps on the target side.
--
--   Fixing an offset $p$, the map $i\mapsto$ (partner block of offset $p$ in block $i$) reads off a letter-level alignment of $x$ and $y$ from a bit-level alignment of their encodings; unmatched offsets and duplicates measure how far it is from a matching. Averaging over offsets and restricting to good blocks gives, for offset-local codes, words of equal length and suitable parameters, a lower bound of the deficit of the encodings by a constant times $w\cdot\operatorname{def}(x,y)$.
--
--   **Formalization Note** The definitions live in the namespace of `WordMatching`: `matchedAt`, `partnerAt` (via `Classical.choose`, with default value $0$), `duplicateAt` (with decidability instances) and `offsetGood A w η`, a finset of natural numbers built with truncated subtractions `sourceLoss` and `spanLoss`. In `offsetGood` the block length $w$ is an explicit argument, formally distinct from the codeword length $w_0$ of the code $c$; in the applications the two coincide.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/OffsetRecovery.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/OffsetRecovery.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

def matchedAt (A : WordMatching x y q) (w i p : ℕ) : Prop :=
  ∃ k : Fin q, (A.left k).val = i*w+p

instance matchedAtDecidable (A : WordMatching x y q) (w i p : ℕ) :
    Decidable (A.matchedAt w i p) := inferInstanceAs (Decidable (∃ k : Fin q, (A.left k).val = i*w+p))

noncomputable def partnerAt (A : WordMatching x y q) (w i p : ℕ) : ℕ :=
  if h : A.matchedAt w i p then (A.right (Classical.choose h)).val/w else 0

def duplicateAt (A : WordMatching x y q) (w i p : ℕ) : Prop :=
  ∃ k l : Fin q, (A.left k).val = i*w+p ∧ (A.left l).val = (i+1)*w+p ∧
    (A.right k).val/w = (A.right l).val/w

instance duplicateAtDecidable (A : WordMatching x y q) (w i p : ℕ) :
    Decidable (A.duplicateAt w i p) := inferInstanceAs (Decidable (∃ k l : Fin q,
      (A.left k).val = i*w+p ∧ (A.left l).val = (i+1)*w+p ∧
      (A.right k).val/w = (A.right l).val/w))

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

noncomputable def offsetGood (A : WordMatching (encode c x) (encode c y) q) (w : ℕ) (η : ℝ) : Finset ℕ :=
  (Finset.range x.length).filter (fun i =>
    (A.sourceLoss w i : ℝ) ≤ η*w ∧ (A.spanLoss w i : ℝ) ≤ η*w)

end WordMatching

end FiniteCircle

end OAI


