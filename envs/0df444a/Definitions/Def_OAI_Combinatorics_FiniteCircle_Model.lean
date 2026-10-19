-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
-- name    : OAI_Combinatorics_FiniteCircle_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T12:34:50.982869+00:00
-- url     : https://prove2.me/theorems/aee6670b-5b77-4bcb-84be-d026017deaa0
-- title:
--   Deficit of two words of possibly different lengths
-- statement:
--   Let $\alpha$ be an alphabet and let $x,y$ be finite words over $\alpha$, of lengths $|x|$ and $|y|$. Write $\operatorname{lcs}(x,y)$ for the length of a longest common subsequence of $x$ and $y$: the largest $n$ such that some word of length $n$ can be obtained both from $x$ and from $y$ by deleting letters (the kept letters need not be contiguous).
--
--   The module defines the *unequal-length deficit*
--
--   $$
--   \operatorname{udef}(x,y)=\max(|x|,|y|)-\operatorname{lcs}(x,y),
--   $$
--
--   the number of letters of the longer word that an optimal common subsequence leaves uncovered. Because $\operatorname{lcs}(x,y)\le\min(|x|,|y|)$, this is a nonnegative integer; it is symmetric in $x$ and $y$, it vanishes exactly when $x=y$, and for words of equal length it coincides with the one-sided deficit $\operatorname{def}(x,y)=|x|-\operatorname{lcs}(x,y)$.
--
--   The unequal-length deficit is the symmetric quantity used to compare corresponding segments of two words whose lengths may differ, for example segments cut out of words related by a few deletions and insertions. It is also what the ordinary deficit becomes after both words are padded with a fresh symbol to a common length $n\ge\max(|x|,|y|)$, which is how words of different lengths are handled in the upper-bound embedding.
--
--   **Formalization Note** The definition is `unequalDeficit x y`, a natural number computed with truncated subtraction; no truncation occurs because `lcs x y` is at most both lengths. The longest-common-subsequence length `lcs` is defined elsewhere as the supremum of the lengths of common sublists (`List.Sublist`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FiniteCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FiniteCircle

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

universe u v

noncomputable def unequalDeficit {α : Type u} (x y : List α) : ℕ :=
  max x.length y.length - lcs x y

end FiniteCircle

end OAI


