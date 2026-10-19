-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_Windows
-- name    : OAI_Combinatorics_FiniteCircle_Windows
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:14:22.073882+00:00
-- url     : https://prove2.me/theorems/570caae7-35a9-4736-b113-f7cbd81d8b39
-- title:
--   Consecutive sliding windows of a word
-- statement:
--   Let $x=x_0x_1\cdots x_{N-1}$ be a word over an alphabet $\alpha$. For $p,\ell\in\mathbb{N}$ write $x[p,p+\ell)$ for the segment of $x$ of length $\ell$ starting at position $p$, namely $x_px_{p+1}\cdots x_{p+\ell-1}$, truncated at the end of $x$ (it is shorter than $\ell$, possibly empty, when $p+\ell>N$).
--
--   For $\sigma,m,s\in\mathbb{N}$, the list of sliding windows of $x$ with start $\sigma$, block length $m$ and $s$ windows is
--   $$
--   \operatorname{win}(x;\sigma,m,s)=\Bigl(x\bigl[\sigma+r,\ \sigma+r+m-s+1\bigr)\Bigr)_{r=0,1,\dots,s-1},
--   $$
--   the $s$ segments of common length $m-s+1$ that start at the consecutive positions $\sigma,\sigma+1,\dots,\sigma+s-1$. When $1\le s\le m$ the last window ends at position $\sigma+m-1$, so all windows lie inside the block $x[\sigma,\sigma+m)$. The module also records that the list has exactly $s$ entries.
--
--   Sliding windows are the local pieces of a word that the upper-bound embedding compares: a word is cut into consecutive blocks of length $m$, each block is represented by its $s$ windows, and these windows are then normalised to a common length and classified by random partitions, whose label histograms give the coordinates of the embedding.
--
--   **Formalization Note** `windows x start m s` is `List.ofFn (fun r : Fin s => segment x (start + r) (m - s + 1))`, where `segment x p l` is `(x.drop p).take l`. Natural-number subtraction truncates, so for `s > m` every window has length at most one. `length_windows` is a simp lemma.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Windows.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Windows.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Lower

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

def windows {α : Type*} (x : List α) (start m s : ℕ) : List (List α) :=
  List.ofFn (fun r : Fin s => segment x (start + r) (m - s + 1))

@[simp] theorem length_windows {α : Type*} (x : List α) (start m s : ℕ) :
    (windows x start m s).length = s := List.length_ofFn

open scoped BigOperators List

open scoped BigOperators

end FiniteCircle

end OAI


