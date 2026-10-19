-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes
-- name    : OAI_Combinatorics_FiniteCircle_Codes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:08:42.758264+00:00
-- url     : https://prove2.me/theorems/f0321e12-7a91-44ce-b60d-7f9f01a3575f
-- title:
--   Windows of a binary codeword have the prescribed length
-- statement:
--   Let $\alpha$ be an alphabet, $w\in\mathbb{N}$, and let $c:\alpha\to\{0,1\}^w$ be a binary code, so that every letter $a$ has the codeword $c(a)=c(a)_0\,c(a)_1\cdots c(a)_{w-1}$. For $s,u\in\mathbb{N}$, the window of $c(a)$ of length $u$ at offset $s$ is the word obtained by deleting the first $s$ bits of $c(a)$ and keeping the first $u$ of the remaining bits (all of them if fewer than $u$ remain). This module records that a window which fits inside the codeword has exactly the requested length:
--   $$
--   s+u\le w\quad\Longrightarrow\quad \bigl|\,c(a)_s\,c(a)_{s+1}\cdots c(a)_{s+u-1}\,\bigr|=u .
--   $$
--
--   Windows of codewords are the objects of the offset-locality condition on codes, which bounds the longest common subsequence of two windows of length $\lfloor w/8\rfloor$ of the codewords of two different letters, taken at arbitrary offsets for which the windows fit inside the codewords. The length identity is the bookkeeping fact needed whenever such a bound on common subsequences of windows is turned into a bound on their deficits.
--
--   **Formalization Note** The window is `interval c a s u`, defined in the base file of the development as `((List.ofFn (c a)).drop s).take u`. The module consists of the simp lemma `length_interval`; its hypothesis `s + u <= w` is needed because `List.drop` and `List.take` truncate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Codes.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Codes.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

@[simp] theorem length_interval {α : Type*} {w : ℕ} (c : α → Fin w → Bool)
    (a : α) {s u : ℕ} (hs : s+u ≤ w) : (interval c a s u).length = u := by
  simp only [interval, List.length_take, List.length_drop, List.length_ofFn]
  omega

end FiniteCircle

end OAI


