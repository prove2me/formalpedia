-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_Main
-- name    : OAI_Combinatorics_FiniteCircle_Main
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:24:07.889782+00:00
-- url     : https://prove2.me/theorems/e292aa1f-7c43-4d87-a6ac-88ee556de6d2
-- title:
--   Words of bounded length over a finite alphabet form a finite set
-- statement:
--   For an alphabet $\alpha$ and $d\in\mathbb{N}$ let
--   $$
--   W_d(\alpha)=\{x\in\alpha^{*}:\ |x|\le d\}
--   $$
--   be the set of words (finite sequences of letters) over $\alpha$ of length at most $d$. This module registers the fact that $W_d(\alpha)$ is finite whenever $\alpha$ is finite; indeed it has $\sum_{k=0}^{d}|\alpha|^k$ elements.
--
--   The main theorem compares the edit-distance metric on $W_d(\alpha)$ with $\ell^1$. Here the edit distance $\operatorname{ed}(x,y)$ is the least number of single-letter insertions, deletions and substitutions turning $x$ into $y$, and $E(\alpha,d)$ is the least distortion of an injective map $f$ from $W_d(\alpha)$ into $\ell^1$, the distortion being the product of $\sup\|f(x)-f(y)\|_1/\operatorname{ed}(x,y)$ and $\sup\operatorname{ed}(x,y)/\|f(x)-f(y)\|_1$ over distinct $x,y$. Finiteness of $W_d(\alpha)$ makes these suprema maxima over finitely many pairs and permits finite sums over words; as a typeclass instance it is supplied automatically wherever the final argument needs it.
--
--   **Formalization Note** `Words α d` is the subtype of lists over `α` of length at most `d`; the instance `wordsFinite` provides `Finite (Words α d)` under `[Finite α]`, via `List.finite_length_le`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Main.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Main.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Windows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Partitions
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Histograms
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Separation

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

instance wordsFinite (α : Type*) [Finite α] (d : ℕ) : Finite (Words α d) :=
  (List.finite_length_le α d).to_subtype

end FiniteCircle

end OAI


