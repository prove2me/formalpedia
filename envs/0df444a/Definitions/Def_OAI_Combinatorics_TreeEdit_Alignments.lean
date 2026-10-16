-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
-- name    : OAI_Combinatorics_TreeEdit_Alignments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:14:33.19119+00:00
-- url     : https://prove2.me/theorems/84091fe2-6f61-4553-ba93-96a814352c76
-- title:
--   Alignments of two words, block indices and spans of increasing maps
-- statement:
--   This file introduces the bookkeeping objects used to compare common subsequences of words with those of their block encodings. Positions in a word $x=x_0x_1\cdots x_{|x|-1}$ are numbered from $0$, and $[n]=\{0,1,\dots,n-1\}$.
--
--   1. **Alignment.** For words $x,y$ over an alphabet $\alpha$ and $n\in\mathbb{N}$, an alignment of size $n$ is a pair of strictly increasing maps $\lambda:[n]\to[|x|]$ and $\rho:[n]\to[|y|]$ such that
--
--      $$x_{\lambda(i)}=y_{\rho(i)}\qquad\text{for every } i\in[n].$$
--
--      Equivalently, it is a common subsequence of $x$ and $y$ of length $n$ together with a choice of its positions in both words.
--
--   2. **Block index.** Let $P>0$. When a word of length $MP$ is cut into $M$ consecutive blocks of length $P$, position $i\in[MP]$ lies in block
--
--      $$\operatorname{blk}_P(i)=\lfloor i/P\rfloor\in[M].$$
--
--   3. **Index span.** For a strictly increasing map $f:[N]\to[L]$ and a set $S\subseteq[N]$,
--
--      $$\operatorname{span}_f(S)=\begin{cases}\{\,p\in[L] : f(\min S)\le p\le f(\max S)\,\}, & S\neq\varnothing,\\ \varnothing, & S=\varnothing,\end{cases}$$
--
--      the smallest interval of $[L]$ containing $f(S)$. In particular $\operatorname{span}_f(\varnothing)=\varnothing$.
--
--   An alignment of size $n$ witnesses $\operatorname{lcs}(x,y)\ge n$, and a longest common subsequence gives an alignment of size $\operatorname{lcs}(x,y)$. When $x$ and $y$ are block encodings, the block index records which encoded symbol an aligned position belongs to, and the span of a group of aligned positions measures how much of the other word they occupy. These are the tools for comparing deficits and edit distances of encoded words with those of the original words.
--
--   **Formalization Note** `Alignment x y n` is a structure whose fields `left` and `right` are order embeddings `Fin n ↪o Fin x.length` and `Fin n ↪o Fin y.length`, with `agree` stating equality of the matched symbols. `blockIndex hP i` takes the proof `hP : 0 < P`; `indexSpan f s` is the `Finset.Icc` from `f (s.min' h)` to `f (s.max' h)` for nonempty `s`, and the simp lemma `indexSpan_empty` records the empty case.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/Alignments.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/Alignments.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TreeEdit mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TreeEdit

universe u

variable {α : Type u} {x y z : List α}

structure Alignment (x y : List α) (n : ℕ) where
  left : Fin n ↪o Fin x.length
  right : Fin n ↪o Fin y.length
  agree : ∀ i, x.get (left i) = y.get (right i)

namespace Alignment

variable {n : ℕ}

end Alignment

def blockIndex {M P : ℕ} (hP : 0 < P) (i : Fin (M * P)) : Fin M :=
  ⟨i.val / P, (Nat.div_lt_iff_lt_mul hP).mpr i.isLt⟩

noncomputable def indexSpan {N L : ℕ} (f : Fin N ↪o Fin L) (s : Finset (Fin N)) :
    Finset (Fin L) :=
  if h : s.Nonempty then Finset.Icc (f (s.min' h)) (f (s.max' h)) else ∅

@[simp] theorem indexSpan_empty {N L : ℕ} (f : Fin N ↪o Fin L) :
    indexSpan f ∅ = ∅ := by simp [indexSpan]

end TreeEdit

end OAI


