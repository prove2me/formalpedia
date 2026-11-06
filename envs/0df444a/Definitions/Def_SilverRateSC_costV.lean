-- Prove2me | Definitions.Def_SilverRateSC_costV
-- name    : SilverRateSC_costV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:45:01.403885+00:00
-- url     : https://prove2.me/theorems/d56e6cfb-9c4c-49f4-a25a-7dde42244a97
-- title:
--   The minimum checkpoint cost $V_\Lambda(g,B)$ of Appendix B
-- statement:
--   Fix $1\le c\le2$, $a\ge8$ and $\Lambda\ge a$. For nonnegative $g=(g_1,\dots,g_r)$ and $B=(B_1,\dots,B_r)$ arranged as $g_1,B_1,\dots,g_r,B_r$, a set $T$ of indices is admissible if $B_j>0$ for $j\in T$. For $j\in T$, $\tilde s_j$ is the sum of all entries after the previous selected $B$ and before $B_j$; $s_{\rm tail}$ is the sum of the entries after the last selected $B$. Then
--   $$P(T)=\prod_{j\in T}\frac{B_j}{c(a+\tilde s_j)},\qquad Q_\Lambda(T;g,B)=\frac{c(\Lambda+s_{\rm tail})}{P(T)},\qquad Q_\Lambda(\varnothing;g,B)=c\Bigl[\Lambda+\sum_j(g_j+B_j)\Bigr],$$
--   and $V_\Lambda(g,B):=\min_{T\text{ admissible}}Q_\Lambda(T;g,B)$.
--
--   The minimum cost is the reciprocal form of the checkpoint score; bounding it uniformly in $B$ (Lemma B.5) controls the maximizing checkpoint sets of Lemma 4.1.
--
--   **Formalization Note** The minimum ranges over the admissible subsets of $\{1,\dots,r\}$ and is attained since $\varnothing$ is admissible; for $T=\varnothing$ the general formula gives the paper's $Q_\Lambda(\varnothing)$.
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), §B.1, pp.37–38

import Mathlib

open Classical

namespace SilverRateSC

/-- Admissible set for the cost: `T ⊆ {1, …, r}` selecting only entries with `B_j > 0`. -/
def IsCostAdmissible (r : ℕ) (B : ℕ → ℝ) (T : Finset ℕ) : Prop :=
  T ⊆ Finset.Icc 1 r ∧ ∀ j ∈ T, 0 < B j

/-- `s̃_j`: the sum of all entries of `g_1, B_1, …, g_r, B_r` after the previous selected `B` and
before `B_j` (from the beginning of the list for the first selected position). -/
noncomputable def sTilde (g B : ℕ → ℝ) (T : Finset ℕ) (j : ℕ) : ℝ :=
  g j + ∑ i ∈ (Finset.Ico 1 j).filter (fun i => ∀ t ∈ T, t < j → t < i), (g i + B i)

/-- `s_tail`: the sum of the entries after the last selected `B` (all entries if `T = ∅`). -/
noncomputable def costTail (r : ℕ) (g B : ℕ → ℝ) (T : Finset ℕ) : ℝ :=
  ∑ i ∈ (Finset.Icc 1 r).filter (fun i => ∀ t ∈ T, t < i), (g i + B i)

/-- The checkpoint score `P(T) = ∏_{j ∈ T} B_j / (c(a + s̃_j))`. -/
noncomputable def costP (a c : ℝ) (g B : ℕ → ℝ) (T : Finset ℕ) : ℝ :=
  ∏ j ∈ T, B j / (c * (a + sTilde g B T j))

/-- The cost `Q_Λ(T; g, B) = c(Λ + s_tail)/P(T)`. -/
noncomputable def costQ (a c Λ : ℝ) (r : ℕ) (g B : ℕ → ℝ) (T : Finset ℕ) : ℝ :=
  c * (Λ + costTail r g B T) / costP a c g B T

/-- **The minimum checkpoint cost** (Appendix B.1). Fix `1 ≤ c ≤ 2`, `a ≥ 8`. For nonnegative
`g = (g_1, …, g_r)`, `B = (B_1, …, B_r)` arranged as `g_1, B_1, …, g_r, B_r`, only entries
`B_j > 0` may be selected; `P(T) = ∏_{j∈T} B_j/(c(a + s̃_j))`, `Q_Λ(T; g, B) = c(Λ + s_tail)/P(T)`
(`Λ ≥ a`), `Q_Λ(∅; g, B) = c[Λ + ∑_j (g_j + B_j)]`, and
`V_Λ(g, B) := min_{T admissible} Q_Λ(T; g, B)`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, §B.1, pp. 37–38.

**Formalization Note** Vectors are `ℕ → ℝ` read at positions `1, …, r`. The minimum is a
`Finset.inf'` over the admissible subsets of `{1, …, r}`, nonempty because `∅` is admissible;
with `T = ∅`, `P = 1` (empty product) and `s_tail` is the sum of all entries, which is the
paper's `Q_Λ(∅)`. -/
noncomputable def costV (a c Λ : ℝ) (r : ℕ) (g B : ℕ → ℝ) : ℝ :=
  ((Finset.Icc 1 r).powerset.filter (IsCostAdmissible r B)).inf'
    ⟨∅, by simp [IsCostAdmissible]⟩ (costQ a c Λ r g B)

end SilverRateSC


