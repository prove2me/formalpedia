-- Prove2me | Definitions.Def_SilverRateSC_score
-- name    : SilverRateSC_score
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:45:03.45366+00:00
-- url     : https://prove2.me/theorems/4a2dd2bc-3da9-4977-af97-5a3c9f54139b
-- title:
--   Admissible checkpoint sets and the score $P_w(T;H)$, (17)–(18)
-- statement:
--   Fix $a\ge8$, $1\le c\le2$. For a block $H=(h_1,\dots,h_r)$ of nonnegative stepsizes with incoming tail sum $w\ge0$, a checkpoint set $T=\{t_1<\dots<t_k\}\subseteq\{1,\dots,r\}$ is **admissible** if it selects only steps with $b_i:=h_{t_i}>8$. With
--   $$s_1:=w+\sum_{j=1}^{t_1-1}h_j,\qquad s_i:=\sum_{j=t_{i-1}+1}^{t_i-1}h_j\ (2\le i\le k),\qquad s_{\rm tail}:=\sum_{j=t_k+1}^rh_j,$$
--   the **score** is
--   $$P_w(T;H):=\prod_{i=1}^k\frac{b_i-8}{c(a+s_i+8)},\qquad P_w(\varnothing;H):=1.$$
--   A **maximizing set** is an admissible set whose score is at least that of every admissible set; one exists because there are finitely many sets, and its score is at least $1$.
--
--   **Formalization Note** The block is read at positions $1,\dots,r$ of a function $\mathbb N\to\mathbb R$. The score is only compared over admissible sets, so a step $\le8$ never enters a factor.
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), §4.1, (17)–(18), p.17

import Mathlib

open Classical

namespace SilverRateSC

/-- Admissible checkpoint set: `T ⊆ {1, …, r}` selecting only steps with `h_t > 8`. -/
def IsAdmissible (r : ℕ) (h : ℕ → ℝ) (T : Finset ℕ) : Prop :=
  T ⊆ Finset.Icc 1 r ∧ ∀ t ∈ T, 8 < h t

/-- The gap sum `s_i` (17) before the checkpoint `t = t_i ∈ T`: `s_1 = w + ∑_{j=1}^{t_1−1} h_j`
and `s_i = ∑_{j=t_{i−1}+1}^{t_i−1} h_j` for `i ≥ 2`. -/
noncomputable def gapSum (w : ℝ) (h : ℕ → ℝ) (T : Finset ℕ) (t : ℕ) : ℝ :=
  (if ∃ t' ∈ T, t' < t then 0 else w) +
    ∑ j ∈ (Finset.Ico 1 t).filter (fun j => ∀ t' ∈ T, t' < t → t' < j), h j

/-- The tail sum `s_tail = ∑_{j=t_k+1}^r h_j` after the last checkpoint (17). -/
noncomputable def tailSum (r : ℕ) (h : ℕ → ℝ) (T : Finset ℕ) : ℝ :=
  ∑ j ∈ (Finset.Icc 1 r).filter (fun j => ∀ t ∈ T, t < j), h j

/-- **The checkpoint score within a block** (16)–(18). Fix `a ≥ 8`, `1 ≤ c ≤ 2`. For a block
`H = (h_1, …, h_r)` with incoming tail sum `w ≥ 0`, an admissible checkpoint set
`T = {t_1 < ⋯ < t_k} ⊆ {1, …, r}` selects only steps with `b_i := h_{t_i} > 8`, and
`P_w(T; H) := ∏_{i=1}^k (b_i − 8)/(c(a + s_i + 8))`, `P_w(∅; H) := 1`, with
`s_1 := w + ∑_{j=1}^{t_1−1} h_j`, `s_i := ∑_{j=t_{i−1}+1}^{t_i−1} h_j` (`2 ≤ i ≤ k`).

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, §4.1, (17)–(18), p. 17.

**Formalization Note** The block is `h : ℕ → ℝ` read at the 1-based positions `1, …, r`; a
checkpoint set is a `Finset ℕ`. The score is a product over `T` (empty product `1`). It is only
compared over admissible sets (`IsAdmissible`), so a step `≤ 8` never enters a factor. -/
noncomputable def score (a c w : ℝ) (h : ℕ → ℝ) (T : Finset ℕ) : ℝ :=
  ∏ t ∈ T, (h t - 8) / (c * (a + gapSum w h T t + 8))

/-- A maximizing checkpoint set: admissible, with score at least that of every admissible set. -/
def IsMaximizing (a c w : ℝ) (r : ℕ) (h : ℕ → ℝ) (T : Finset ℕ) : Prop :=
  IsAdmissible r h T ∧ ∀ T', IsAdmissible r h T' → score a c w h T' ≤ score a c w h T

end SilverRateSC


