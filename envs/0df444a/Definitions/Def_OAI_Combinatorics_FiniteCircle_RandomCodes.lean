-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes
-- name    : OAI_Combinatorics_FiniteCircle_RandomCodes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:07:13.87315+00:00
-- url     : https://prove2.me/theorems/e38db97c-6aff-4ec2-8334-b23bda7f9a2d
-- title:
--   Random binary codes: small hole sets, dense position lists, strong locality and bad witnesses
-- statement:
--   This file sets up a counting (union-bound) construction of binary codes with a strong locality property. Throughout, $w\in\mathbb{N}$ is a block length, $[w]=\{0,1,\dots,w-1\}$ is the set of positions, and a binary code on an alphabet $\alpha$ is a map $c:\alpha\to\{0,1\}^{w}$; $c(a)_i$ denotes bit $i$ of the codeword of the letter $a$. For a strictly increasing list $I=(i_1<\dots<i_\ell)$ of positions put $\operatorname{span}(I)=i_\ell+1-i_1$ (and $\operatorname{span}(I)=0$ for the empty list), so that $\operatorname{span}(I)-\ell$ is the number of positions of the interval $[i_1,i_\ell]$ that $I$ skips.
--
--   1. **Small hole sets.** $\mathcal{H}_w$ is the set of subsets $S\subseteq[w]$ with $|S|\le w/2^{20}$ (here $2^{20}=1048576$); it is a finite set.
--
--   2. **Dense parameters and dense lists.** A dense parameter is a triple $P=(s,e,S)\in[w]\times[w]\times\mathcal{H}_w$. Its dense list is the increasing enumeration
--   $$
--   D(P)=\operatorname{sort}\bigl(\{s,s+1,\dots,e\}\setminus S\bigr)
--   $$
--   of an interval of positions from which a small set of holes has been removed (it is empty if $s>e$).
--
--   3. **Strong locality.** A code $c:\alpha\to\{0,1\}^w$ is strongly local if the following holds for all letters $a,b\in\alpha$ and all strictly increasing position lists $I=(i_1<\dots<i_\ell)$ and $J=(j_1<\dots<j_\ell)$ of a common length $\ell$: if
--   $$
--   w\le16\,\ell,\qquad \operatorname{span}(I)-\ell\le\frac{w}{2^{20}},\qquad \operatorname{span}(J)-\ell\le\frac{w}{2^{20}},\qquad c(a)_{i_k}=c(b)_{j_k}\ \text{ for } 1\le k\le\ell,
--   $$
--   then $a=b$ and $i_k=j_k$ for at least one $k$. Thus two codewords can agree along a long (at least $w/16$ pairs), almost gap-free, order-preserving pairing of positions only if they are the same codeword and the pairing contains a diagonal pair.
--
--   4. **Dense witnesses and bad witnesses.** A dense witness is a pair $W=((a,P),(b,Q))$ consisting of two letters $a,b\in\alpha$ with dense parameters $P,Q$. A bit assignment $\omega:\alpha\times[w]\to\{0,1\}$, read as the code $a\mapsto(\omega(a,0),\dots,\omega(a,w-1))$, makes $W$ bad if, writing $D(P)=(i_1,\dots,i_\ell)$ and $D(Q)=(j_1,\dots,j_{\ell'})$,
--   $$
--   \ell'=\ell,\qquad w\le16\,\ell,\qquad \bigl(a\neq b\ \text{ or }\ i_k\neq j_k\ \text{for every } k\bigr),\qquad \omega(a,i_k)=\omega(b,j_k)\ \text{ for every } k\le\ell .
--   $$
--   So a bad witness is a violation of strong locality whose two position lists are dense lists.
--
--   Every non-empty strictly increasing position list that skips at most $w/2^{20}$ positions of its span is a dense list, so a bit assignment for which no dense witness is bad defines a strongly local code. There are $|\alpha|^2w^4|\mathcal{H}_w|^2$ dense witnesses, and each of them is bad for at most $2^{|\alpha|w-\lfloor w/64\rfloor}$ of the $2^{|\alpha|w}$ bit assignments; this is how strongly local codes of length $w=O(\log|\alpha|)$ are shown to exist. Strong locality in turn yields the offset-locality required of the binary encodings in the lower-bound construction.
--
--   **Formalization Note** `SmallHoles w` is the subtype of `Finset (Fin w)` cut out by the real inequality `(S.card : Real) <= w/1048576`, with a noncomputable `Fintype` instance; `DenseParameters w` is the product `Fin w × Fin w × SmallHoles w`, and `denseList` sorts the finset `Finset.Icc s e \ S`. `StrongLocal c` is phrased with `indexSpan` and the truncated natural-number difference `indexSpan is - is.length`, cast to the reals, and the diagonal pair is expressed as membership of `(i, i)` in `is.zip js`. `DenseWitness α w` pairs two elements of `α × DenseParameters w`, and `badDenseWitness W ω` is the conjunction displayed in item 4.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/RandomCodes.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/RandomCodes.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

open Classical

abbrev SmallHoles (w : ℕ) := {S : Finset (Fin w) // (S.card : ℝ) ≤ (w : ℝ)/1048576}
abbrev DenseParameters (w : ℕ) := Fin w × Fin w × SmallHoles w

noncomputable instance (w : ℕ) : Fintype (SmallHoles w) := Fintype.ofFinite _

def denseList {w : ℕ} (P : DenseParameters w) : List (Fin w) :=
  (Finset.Icc P.1 P.2.1 \ P.2.2.val).sort (· ≤ ·)

def StrongLocal {α : Type*} {w : ℕ} (c : α → Fin w → Bool) : Prop :=
  ∀ a b : α, ∀ is js : List (Fin w),
    is.Pairwise (fun i j => i.val < j.val) →
    js.Pairwise (fun i j => i.val < j.val) →
    is.length = js.length → w ≤ 16*is.length →
    (indexSpan is - is.length : ℕ) ≤ (w : ℝ)/1048576 →
    (indexSpan js - js.length : ℕ) ≤ (w : ℝ)/1048576 →
    (∀ ij ∈ is.zip js, c a ij.1 = c b ij.2) →
    a = b ∧ ∃ i : Fin w, (i, i) ∈ is.zip js

abbrev DenseWitness (α : Type*) (w : ℕ) := (α × DenseParameters w) × (α × DenseParameters w)

def badDenseWitness {α : Type*} {w : ℕ} (W : DenseWitness α w) (ω : α × Fin w → Bool) : Prop :=
  let is := denseList W.1.2
  let js := denseList W.2.2
  is.length = js.length ∧ w ≤ 16*is.length ∧
  (W.1.1 ≠ W.2.1 ∨ ∀ i : Fin w, (i,i) ∉ is.zip js) ∧
  ∀ ij ∈ is.zip js, ω (W.1.1, ij.1) = ω (W.2.1, ij.2)

end FiniteCircle

end OAI


