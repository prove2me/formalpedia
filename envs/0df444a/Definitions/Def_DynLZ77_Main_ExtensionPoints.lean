-- Prove2me | Definitions.Def_DynLZ77_Main_ExtensionPoints
-- name    : DynLZ77_Main_ExtensionPoints
-- status  : Definition
-- author  : @shaygo
-- created : 2026-11-25T08:59:13.197166+00:00
-- url     : https://prove2.me/theorems/4e13429c-dc91-41da-bf00-aa9ba71e2a67
-- title:
--   Extension points $p_{i,j,S}=(\mathrm{LCS}_S(i,j),\mathrm{LCP}_S(i,j))$ and non-dominated extension points $\mathrm{DExt}_I(i,S)$
-- statement:
--   Let $S$ be a string of length $n$ and $I\subseteq[1..n]$ a set of indices. For $i\in I$ let $I_i=I\cap[1..i-1]$. For $j\in I_i$ the **extension point** of the pair $(i,j)$ is
--   $$
--   p_{i,j,S}=\bigl(\mathrm{LCS}_S(i,j),\ \mathrm{LCP}_S(i,j)\bigr),
--   $$
--   the lengths of the longest common suffix of $S[1..i]$ and $S[1..j]$ and of the longest common prefix of $S[i..n]$ and $S[j..n]$. Set $\mathrm{Ext}_I(i,S)=\{p_{i,j,S}\mid j\in I_i\}$. For a finite set $P$ of points, $\mathrm{ND}(P)$ is the set of points $(x,y)\in P$ for which no other point $(x',y')\in P\setminus\{(x,y)\}$ has $x'\ge x$ and $y'\ge y$. The **non-dominated extension points** of $i$ are
--   $$
--   \mathrm{DExt}_I(i,S)=\mathrm{ND}\bigl(\mathrm{Ext}_I(i,S)\bigr).
--   $$
--
--   Lemma 2.2 bounds $\sum_{i\in I}|\mathrm{DExt}_I(i,S)|$ by $O(|I|\log^2 n)$, and the proof of Lemma 1.2 maps irreducible positions injectively to non-dominated extension points.
--
--   **Formalization Note.** `extPoint S i j` is $p_{i,j,S}$, `ext S I i` is $\mathrm{Ext}_I(i,S)$ with $I_i$ written as the elements of $I$ smaller than $i$, `nonDominated P` is $\mathrm{ND}(P)$ and `dext S I i` is $\mathrm{DExt}_I(i,S)$. Positions are 1-based; `lcsAt`, `lcpAt` are those of `DynLZ77_Main_Strings`.
-- source:
--   Boneh, Fried, Golan, Kraus, Dynamic LZ77: No Space for Improvement, STOC 2027 submission (manuscript sha256 2a15e146…, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1131.pdf), §8.1 Non-Dominated Extension Points, p. 49 (PDF 51); following Boneh, Golan, Kraus, The Complexity of Dynamic LZ77 is Θ̃(n^{2/3}), arXiv:2502.12000 (v3), §4

import Mathlib.Data.Finset.Image
import Definitions.Def_DynLZ77_Main_Strings

set_option autoImplicit false

/-!
# Extension points and non-dominated extension points

Boneh, Fried, Golan, Kraus, *Dynamic LZ77: No Space for Improvement*, STOC 2027 submission
(manuscript sha256 2a15e146…), §8.1 "Non-Dominated Extension Points", p. 49 (PDF 51), following
Boneh, Golan, Kraus, *The Complexity of Dynamic LZ77 is Theta~(n^{2/3})*, arXiv:2502.12000 (v3), §4.

**Formalization Note.** Positions are 1-based, as in `Def_DynLZ77_Main_Strings`.
* `extPoint S i j` is `p_{i,j,S} = (LCS_S(i,j), LCP_S(i,j))`.
* `ext S I i` is `Ext_I(i,S) = {p_{i,j,S} | j ∈ I_i}` with `I_i = I ∩ [1..i−1]`, written as the
  elements of `I` smaller than `i` (for `I ⊆ [1..n]` this is the same set).
* `nonDominated P` is `ND(P)`: the points `(x,y) ∈ P` with no other point `(x′,y′) ∈ P` such that
  `x′ ≥ x` and `y′ ≥ y`.
* `dext S I i` is `DExt_I(i,S) = ND(Ext_I(i,S))`.
-/

namespace DynLZ77.Main

variable {α : Type} [DecidableEq α]

/-- The extension point `p_{i,j,S} = (LCS_S(i,j), LCP_S(i,j))`. -/
def extPoint (S : List α) (i j : ℕ) : ℕ × ℕ := (lcsAt S i j, lcpAt S i j)

/-- `Ext_I(i,S)`: the extension points `p_{i,j,S}` of the indices `j ∈ I` smaller than `i`. -/
def ext (S : List α) (I : Finset ℕ) (i : ℕ) : Finset (ℕ × ℕ) :=
  (I.filter (fun j => j < i)).image (extPoint S i)

/-- `ND(P)`: the points of `P` that are not dominated (weakly in both coordinates) by another
point of `P`. -/
def nonDominated (P : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  P.filter (fun q => ∀ q' ∈ P, q' ≠ q → ¬ (q.1 ≤ q'.1 ∧ q.2 ≤ q'.2))

/-- `DExt_I(i,S) = ND(Ext_I(i,S))`, the non-dominated extension points of `i`. -/
def dext (S : List α) (I : Finset ℕ) (i : ℕ) : Finset (ℕ × ℕ) :=
  nonDominated (ext S I i)

end DynLZ77.Main


