-- Prove2me | Definitions.Def_SilverRateLB_gapMass
-- name    : SilverRateLB_gapMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:20:20.931078+00:00
-- url     : https://prove2.me/theorems/3647f118-4e35-4f14-bdbd-4b62b11673cd
-- title:
--   Checkpoints, admissibility and the gap data $b_i$, $s_i$ of (4)
-- statement:
--   Fix a schedule $H=(h_1,\dots,h_n)$. A **checkpoint set** is a set of update indices $T=\{t_1<\dots<t_k\}\subseteq\{1,\dots,n\}$; set $t_0=0$ and $t_{k+1}=n+1$. The updates strictly between successive checkpoints form a **gap**, and
--   $$b_i := h_{t_i}\quad(1\le i\le k),\qquad s_i := \sum_{t=t_{i-1}+1}^{t_i-1} h_t\quad(1\le i\le k+1).$$
--   $b_i$ is the stepsize at checkpoint $t_i$ and $s_i$ the mass of the preceding gap; $s_{k+1}$ is the mass of the final gap. A checkpoint set is **admissible** if $b_i>2$ for every $i$.
--
--   **Formalization Note** Positions are 1-based and $T$ is a finite set of natural numbers, sorted increasingly to read off $t_1<\dots<t_k$. An empty gap has mass $0$. The module also provides the list of the stepsizes of gap $i$, $(h_{t_{i-1}+1},\dots,h_{t_i-1})$.
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), §2.2, (4), p. 8; admissibility pp. 10–11

import Mathlib

namespace SilverRateLB

/-- The stepsize `h_t` at the 1-based position `t` of a schedule `H = (h_1, …, h_n)`. It is
used only for `1 ≤ t ≤ n`. -/
def hAt (H : List ℝ) (t : ℕ) : ℝ := H.getD (t - 1) 0

/-- **Admissible checkpoint set.** `T ⊆ {1, …, n}` is a set of update indices (checkpoints), and
it is admissible when every checkpoint `t ∈ T` has stepsize `h_t > 2`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, §2.2, p. 8:
"select a set of update indices T = {t1 < ··· < tk} called checkpoints"; p. 10–11: "we use
checkpoints with bi > 2, which we call admissible. A checkpoint set is admissible if all its
checkpoints are admissible." -/
def IsAdmissible (H : List ℝ) (T : Finset ℕ) : Prop :=
  ∀ t ∈ T, 1 ≤ t ∧ t ≤ H.length ∧ 2 < hAt H t

/-- The checkpoint `t_i` of `T = {t_1 < ⋯ < t_k}`, with the conventions `t_0 = 0` and
`t_{k+1} = n + 1` (§2.2, p. 8). -/
def tIdx (H : List ℝ) (T : Finset ℕ) (i : ℕ) : ℕ :=
  if i = 0 then 0 else (T.sort (· ≤ ·)).getD (i - 1) (H.length + 1)

/-- The checkpoint stepsize `b_i := h_{t_i}`, `1 ≤ i ≤ k` ((4), p. 8). -/
def ckptStep (H : List ℝ) (T : Finset ℕ) (i : ℕ) : ℝ := hAt H (tIdx H T i)

/-- **Gap mass** (4): `s_i := ∑_{t = t_{i−1}+1}^{t_i − 1} h_t`, `1 ≤ i ≤ k + 1`, the sum of the
stepsizes strictly between two successive checkpoints (with `t_0 = 0`, `t_{k+1} = n + 1`).

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, §2.2, (4),
p. 8: "Set t0 = 0, tk+1 = n+1, and define bi := hti (1 ≤ i ≤ k), si := ∑_{t=ti−1+1}^{ti−1} ht
(1 ≤ i ≤ k+1)."

**Formalization Note** Positions are 1-based, `k = T.card`, and the checkpoints are `T` sorted
increasingly. An empty gap (two adjacent checkpoints) has mass `0`. -/
noncomputable def gapMass (H : List ℝ) (T : Finset ℕ) (i : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ioo (tIdx H T (i - 1)) (tIdx H T i), hAt H t

/-- The stepsizes `(h_{t_{i−1}+1}, …, h_{t_i − 1})` of gap `i`, in order (§3.1, p. 12: "For gap i,
apply Lemma 3.2 to h_{ti−1+1}, ..., h_{ti−1}"). Its length is `t_i − t_{i−1} − 1` and its sum is
`gapMass H T i`. -/
def gapList (H : List ℝ) (T : Finset ℕ) (i : ℕ) : List ℝ :=
  (H.drop (tIdx H T (i - 1))).take (tIdx H T i - tIdx H T (i - 1) - 1)

end SilverRateLB


