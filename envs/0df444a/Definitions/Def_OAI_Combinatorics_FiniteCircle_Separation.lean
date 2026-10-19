-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_Separation
-- name    : OAI_Combinatorics_FiniteCircle_Separation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:20:29.576991+00:00
-- url     : https://prove2.me/theorems/df3eeb1c-bc20-4f27-bfc2-dd81394f276c
-- title:
--   Coordinate $\ell^1$ distance, normalised window words and the partition rate
-- statement:
--   This module collects three auxiliary notions used by the window-histogram embedding of words into $\ell^1$.
--
--   1. **Coordinate distance.** For a finite index set $\iota$ and a map $F:X\to\mathbb{R}^{\iota}$,
--   $$
--   d_F(x,y)=\sum_{i\in\iota}\bigl|F(x)_i-F(y)_i\bigr| ,
--   $$
--   the $\ell^1$ distance between the images of $x,y\in X$.
--
--   2. **Normalised words.** For a padding letter $a\in\alpha$, a length $m\in\mathbb{N}$ and a word $x$ over $\alpha$, $\operatorname{nor}_{a,m}(x)\in\alpha^m$ is the word of length exactly $m$ formed by the first $m$ letters of $x$ followed, when $|x|<m$, by $m-|x|$ copies of $a$.
--
--   3. **Window words.** Write $x[p,p+\ell)$ for the segment of $x$ of length $\ell$ starting at position $p$ (truncated at the end of $x$). For $\sigma,m,s\in\mathbb{N}$, the window words of $x$ are the $s$ normalised sliding windows
--   $$
--   \Bigl(\operatorname{nor}_{a,m}\bigl(x[\sigma+r,\ \sigma+r+m-s+1)\bigr)\Bigr)_{r=0,1,\dots,s-1}\in\bigl(\alpha^m\bigr)^s ;
--   $$
--   the module records that this list has exactly $s$ entries.
--
--   4. **Partition rate.** For $s\in\mathbb{N}$,
--   $$
--   r(s)=\frac{4\log(s+1)}{s}\quad(s\ge1),\qquad r(0)=0 .
--   $$
--
--   In the upper bound, words of length $m$ are already embedded into $\ell^1$ by a map $F$ with $\operatorname{def}(u,v)\le d_F(u,v)\le\Lambda\operatorname{def}(u,v)$, where $\operatorname{def}(u,v)=|u|-\operatorname{lcs}(u,v)$ is the deficit with respect to a longest common subsequence. One then uses random partitions of $\alpha^m$ in which two words $u,v$ lie in the same part with probability $\exp(-r(s)\,d_F(u,v))$, and compares longer words through the histograms of the partition labels of their window words. The normalisation makes every window an element of the single finite set $\alpha^m$ on which these partitions live.
--
--   **Formalization Note** `coordDist F x y` takes `F : X -> ι -> Real` with `[Fintype ι]`. `normalizeWord a m x` is the vector `x.take m ++ List.replicate (m - x.length) a` of type `List.Vector α m`, and `windowWords a x start m s` maps it over `windows x start m s`, the list of segments `segment x (start + r) (m - s + 1)` for `r < s`; `length_windowWords` is a simp lemma. `partitionRate s` is `4 * Real.log (s+1) / s`, so its value at `s = 0` comes from Lean's convention that division by zero gives zero.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Separation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Separation.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

noncomputable def coordDist {X ι : Type*} [Fintype ι] (F : X → ι → ℝ) (x y : X) : ℝ :=
  ∑ i, |F x i - F y i|

def normalizeWord {α : Type*} (a : α) (m : ℕ) (x : List α) : List.Vector α m :=
  ⟨x.take m ++ List.replicate (m - x.length) a, by simp; omega⟩

def windowWords {α : Type*} (a : α) (x : List α) (start m s : ℕ) : List (List.Vector α m) :=
  (windows x start m s).map (normalizeWord a m)

@[simp] theorem length_windowWords {α : Type*} (a : α) (x : List α) (start m s : ℕ) :
    (windowWords a x start m s).length = s := by simp [windowWords]

noncomputable def partitionRate (s : ℕ) : ℝ := 4 * Real.log (s+1) / s

end FiniteCircle

end OAI


