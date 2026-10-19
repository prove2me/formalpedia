-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
-- name    : OAI_Combinatorics_FiniteCircle_Translations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T12:59:33.924771+00:00
-- url     : https://prove2.me/theorems/75a7b0b2-1ee7-4358-975f-03e3f5880b11
-- title:
--   Copy counts and leaf-indexed versions of the mask and excluded words
-- statement:
--   Recall the two families of finite-circle words. For a table $p(l,k)$ ($k<h$) and $M,R\in\mathbb{N}$, the mask word $W_l(v)$ of a level-$l$ state $v$ is the binary half-circle indicator of length $M$ rotated by $v$ when $l=0$, and for $l+1$ the concatenation over $a=0,\dots,R\,P_{l+1}-1$ (with $P_l=\prod_{k<h}p(l,k)$) of the rows formed by the tagged words $W_l(v_j+\gamma_{l+1}(a,j))$, one for each tag $j=(k,b)$ with $k<h$ and $b<p(l+1,k)$; here $\gamma_{l+1}(a,j)\in\mathbb{Z}/M$ is a residue shift determined by $a\bmod p(l+1,k)$. The excluded word $X_l(v)$ is built in the same way with tags $i<h$ and shifts $\tau_{l+1}(s,i)=\sum_{j\ne i}(M/p(l+1,j))(s\bmod p(l+1,j))$, the level-$0$ letters also recording their position. A state of level $l$ is a nested assignment of residues; it is the same as a function on the leaves $\mathrm{Leaf}_l=J_l\times\dots\times J_1$ of the tag tree.
--
--   1. **Copy counts.** For $R\in\mathbb{N}$ and $P:\mathbb{N}\to\mathbb{N}$, put $N_0=1$ and $N_{l+1}=R\,P(l+1)\,N_l$, so that
--   $$
--   N_l=\prod_{r=1}^{l}R\,P(r).
--   $$
--   2. **Leaf-indexed mask words.** For $v:\mathrm{Leaf}_l\to\mathbb{Z}/M$, where the children at height $r$ are the mask tags $(k,b)$, the word $W_l(v)$ is the mask word of the nested state whose level-$0$ residues are the values of $v$.
--   3. **Leaf-indexed excluded words.** Likewise, for $v:\mathrm{Leaf}_l\to\mathbb{Z}/M$ with $J_r=\{0,\dots,h-1\}$, the word $X_l(v)$ is the excluded word of the corresponding nested state.
--
--   With $P(r)=P_r$, the number $N_l$ counts how many times the base block of each leaf occurs in a level-$l$ word, so that the mask length equals $M\cdot|\mathrm{Leaf}_l|\cdot N_l$. Indexing states by leaves makes the state space the abelian group $(\mathbb{Z}/M)^{\mathrm{Leaf}_l}$, in which rotating phases is addition; this is the setting for the Fourier argument and for the upper bound of the edit distance between two words by $2N_l$ times the total circular distance between their leaf phases.
--
--   **Formalization Note** The definitions are `treeCopies R P l`, `flatMaskWord h p R M l v` (the base `maskWord` applied to `flatMaskState`) and `flatExcludedWord h p R M l v` (the base `excludedWord` applied to `flatExcludedState`); leaves are `TreeLeaf (MaskChildren h p) l` and `TreeLeaf (fun _ => Fin h) l` respectively.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Translations.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Translations.lean by skeleton subtraction
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

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

noncomputable def treeCopies (R : ℕ) (P : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | l+1 => (R*P (l+1))*treeCopies R P l

noncomputable def flatMaskWord (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : TreeLeaf (MaskChildren h p) l → ZMod M) : List (MaskAlphabet h p l) :=
  maskWord h p R M l (flatMaskState h p M l v)

noncomputable def flatExcludedWord (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : TreeLeaf (fun _ => Fin h) l → ZMod M) : List (ExcludedAlphabet h M l) :=
  excludedWord h p R M l (flatExcludedState h M l v)

end FiniteCircle

end OAI


