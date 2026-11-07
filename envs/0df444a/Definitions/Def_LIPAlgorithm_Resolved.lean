-- Prove2me | Definitions.Def_LIPAlgorithm_Resolved
-- name    : LIPAlgorithm_Resolved
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:49.183143+00:00
-- url     : https://prove2.me/theorems/118fdaec-4466-47c6-b217-75dd4b2ea109
-- title:
--   Projected polytopes, resolved and ambiguous ranks, fixed vectors
-- statement:
--   Let $A=\mathrm{Min}(L)$ with its vector matroid. For an independent set $B$ write $p_B=\sum_{b\in B}b$. The rank-$j$ projected polytope and its support function are
--
--   $$P_j=\mathrm{conv}\{p_B:B\text{ independent},\ |B|=j\},\qquad h_j(w)=\max_{p\in P_j}\langle w,p\rangle.$$
--
--   Rank $j$ is **resolved** at $w$ if the maximizing set $F_j(w)$ is a single vertex of $P_j$, and **ambiguous** otherwise. With $\mathrm{Amb}(w)$ the number of ambiguous $j\in[n]$ and $J(w)$ the set of $j\in[n]$ for which $j-1$ and $j$ are resolved, the fixed vectors are $u_j(w)=p_j(w)-p_{j-1}(w)$, where $p_j(w)$ is the vertex at a resolved rank.
--
--   These objects measure how much of the shell a marker $w$ pins down.
--
--   **Formalization Note** A vertex is an extreme point. All of this is defined for every $w\in\mathbb R^n$. Rank $0$ has $P_0=\{0\}$, so it is resolved with $p_0=0$, which is what the paper declares.
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), §3 preamble, p.17; Definitions 3.1, 3.2, p.18; Lemma 3.7, p.20; Definition 2.24, p.17

import Mathlib
import Definitions.Def_LIPAlgorithm_minShell

namespace LIPAlgorithm

/-- The independent `j`-subsets of `A = Min(L)`: the sets `B ∈ I` with `|B| = j` of the vector matroid
(Definition 2.24, p.17; §3 preamble, p.17). -/
def indepSets {n : ℕ} (L : Submodule ℤ (E n)) (j : ℕ) : Set (Finset (E n)) :=
  {B | (B : Set (E n)) ⊆ minShell L ∧ B.card = j ∧
    LinearIndependent ℝ (fun b : (B : Set (E n)) => (b : E n))}

/-- `p_B = ∑_{b ∈ B} b` (§3 preamble, p.17). -/
def pSum {n : ℕ} (B : Finset (E n)) : E n :=
  ∑ b ∈ B, b

/-- The rank-`j` projected polytope `P_j = conv{p_B : B ∈ I, |B| = j}` (Definition 3.1, p.18). -/
def polyP {n : ℕ} (L : Submodule ℤ (E n)) (j : ℕ) : Set (E n) :=
  convexHull ℝ (pSum '' indepSets L j)

/-- The support function `h_j(w) = max_{p ∈ P_j} ⟨w, p⟩` (Definition 3.1, p.18).

**Formalization Note.** A supremum, attained for `1 ≤ j ≤ n` since `Min(L)` is finite for a lattice and
`P_j` is a nonempty polytope for a well-rounded lattice. The paper uses only those `j`. -/
noncomputable def supportH {n : ℕ} (L : Submodule ℤ (E n)) (j : ℕ) (w : E n) : ℝ :=
  sSup ((fun p => inner ℝ w p) '' polyP L j)

/-- The maximum-achieving set `F_j(w) = argmax_{p ∈ P_j} ⟨w, p⟩` (Definition 3.2, p.18). -/
def faceF {n : ℕ} (L : Submodule ℤ (E n)) (j : ℕ) (w : E n) : Set (E n) :=
  {p | p ∈ polyP L j ∧ ∀ q ∈ polyP L j, inner ℝ w q ≤ inner ℝ w p}

/-- "Rank j is called resolved at w if the maximum-achieving set … is a single vertex of P_j"
(Definition 3.2, p.18). A vertex is "not a nontrivial convex combination of other points" (§3, p.17), that
is, an extreme point.

**Formalization Note.** Defined for every `w ∈ ℝⁿ`, not only `w ∈ L*`, as in Lemma 3.3, p.18. At `j = 0`
the polytope is `{0}`, so rank `0` is resolved, which is what Lemma 3.7, p.20 declares. -/
def Resolved {n : ℕ} (L : Submodule ℤ (E n)) (j : ℕ) (w : E n) : Prop :=
  ∃ p ∈ (polyP L j).extremePoints ℝ, faceF L j w = {p}

/-- "Otherwise rank j is ambiguous at w" (Definition 3.2, p.18). -/
def Ambiguous {n : ℕ} (L : Submodule ℤ (E n)) (j : ℕ) (w : E n) : Prop :=
  ¬ Resolved L j w

open Classical in
/-- `Amb(w) = |{j ∈ [n] : j is ambiguous at w}|` (Lemma 3.7, p.20). -/
noncomputable def ambCount {n : ℕ} (L : Submodule ℤ (E n)) (w : E n) : ℕ :=
  ((Finset.Icc 1 n).filter fun j => Ambiguous L j w).card

open Classical in
/-- `J(w) = {j ∈ [n] : j − 1 and j are resolved at w}` (Lemma 3.7, p.20). -/
noncomputable def fixedSteps {n : ℕ} (L : Submodule ℤ (E n)) (w : E n) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun j => Resolved L (j - 1) w ∧ Resolved L j w

open Classical in
/-- The vertex `p_j(w)` of a resolved rank (Lemma 3.7, p.20); `0` at an ambiguous rank, where the paper does
not use it. -/
noncomputable def vertexAt {n : ℕ} (L : Submodule ℤ (E n)) (j : ℕ) (w : E n) : E n :=
  if h : Resolved L j w then h.choose else 0

/-- The fixed vector `u_j(w) = p_j(w) − p_{j−1}(w)` (Lemma 3.7, p.20), used at `j ∈ J(w)`. -/
noncomputable def fixedVec {n : ℕ} (L : Submodule ℤ (E n)) (j : ℕ) (w : E n) : E n :=
  vertexAt L j w - vertexAt L (j - 1) w

end LIPAlgorithm


