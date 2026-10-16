-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_Delimiter
-- name    : OAI_Combinatorics_TreeEdit_Delimiter
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:36:22.497981+00:00
-- url     : https://prove2.me/theorems/93f0e1aa-4d40-444a-bb14-4769ab1ded40
-- title:
--   Synchronizing binary block codes with a delimiter header
-- statement:
--   This file defines a binary block code whose codewords can only be found at block boundaries of an encoded word. For a code $c:\alpha\to\{0,1\}^B$ (each symbol of an alphabet $\alpha$ is sent to a binary word of length $B$), $\operatorname{enc}_c(x)=c(x_0)c(x_1)\cdots$ denotes the concatenation of the codewords of the symbols of a finite word $x=x_0x_1\cdots$, and $\operatorname{seg}(w,n,B)=w_nw_{n+1}\cdots w_{n+B-1}$ is the window of length $B$ of a word $w$ starting at position $n$ (positions are numbered from $0$).
--
--   1. **Synchronizing codes.** $c$ is synchronizing if for every finite word $x$ over $\alpha$, every symbol $a\in\alpha$ and every $n\in\mathbb{N}$ with $n+B\le|\operatorname{enc}_c(x)|$,
--
--      $$\operatorname{seg}\bigl(\operatorname{enc}_c(x),n,B\bigr)=c(a)\ \Longrightarrow\ \exists\, i<|x|:\ n=iB\ \text{ and }\ x_i=a.$$
--
--      That is, a codeword occurs in an encoded word only at the start of a block, and only at a block encoding that very symbol.
--
--   2. **Delimited bit pattern.** For a label $\lambda=(\lambda_0,\dots,\lambda_{t-1})\in\{0,1\}^t$, the word $b(\lambda)\in\{0,1\}^{2t+3}$ has bit $1$ at positions $0$ and $1$, bit $\lambda_q$ at position $2q+3$ for $0\le q<t$, and bit $0$ at every other position:
--
--      $$b(\lambda)=1\,1\,0\,\lambda_0\,0\,\lambda_1\,0\cdots0\,\lambda_{t-1}\,0.$$
--
--   3. **Delimiter code.** For a labelling $\lambda:\alpha\to\{0,1\}^t$, the code $a\mapsto b(\lambda(a))$ of width $2t+3$.
--
--   4. **Width.** $w(A)=2\lceil\log_2A\rceil+3$ for $A\in\mathbb{N}$, where $\lceil\log_2A\rceil$ is the least $e\in\mathbb{N}$ with $A\le2^e$; in particular $w(A)=3$ for $A\le1$.
--
--   In a concatenation of delimited patterns the header $11$ occurs exactly at block starts, because label bits are separated by zeros and every pattern ends with $0$. With injective labels of length $\lceil\log_2|\alpha|\rceil$ the delimiter code is synchronizing and has width $w(|\alpha|)$. It converts words of one length over a large finite alphabet into binary words, losing a factor $2$ in deficits and at most a factor $w(|\alpha|)$ in edit distance; this is how the circle-tree words become binary witnesses.
--
--   **Formalization Note** The Lean names are `Delimiter.Synchronizing`, `bit`, `code` (built with `vectorWord`) and `width` (using `Nat.clog 2`). Windows are `segment`, and the conclusion of `Synchronizing` provides `i : Fin x.length` with `n = i * B` and `x.get i = a`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/Delimiter.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/Delimiter.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TreeEdit mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_SampledSpectrum
import Definitions.Def_OAI_Combinatorics_TreeEdit_PrimeSupply
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleObstruction
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleParameters

namespace OAI

namespace TreeEdit.Delimiter
open scoped BigOperators
open Classical

def Synchronizing {α : Type*} {B : ℕ} (c : α → Word Bool B) : Prop :=
  ∀ (x : List α) (a : α) (n : ℕ), n+B ≤ (encode c x).length →
    segment (encode c x) n B = (c a).val →
      ∃ i : Fin x.length, n = i.val*B ∧ x.get i = a

end TreeEdit.Delimiter

namespace TreeEdit.Delimiter
open scoped BigOperators
open Classical

def bit {t : ℕ} (label : Fin t → Bool) (i : Fin (2*t+3)) : Bool :=
  if hi : i.val < 2 then true else
    if h : i.val % 2 = 1 then label ⟨(i.val-3)/2, by have := i.isLt; omega⟩ else false

def code {α : Type*} {t : ℕ} (label : α → (Fin t → Bool)) (a : α) : Word Bool (2*t+3) :=
  vectorWord (bit (label a))

def width (A : ℕ) : ℕ := 2*Nat.clog 2 A+3

end TreeEdit.Delimiter

end OAI


