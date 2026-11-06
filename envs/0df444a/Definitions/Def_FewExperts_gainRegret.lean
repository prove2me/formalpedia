-- Prove2me | Definitions.Def_FewExperts_gainRegret
-- name    : FewExperts_gainRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:12.944081+00:00
-- url     : https://prove2.me/theorems/cc3daf3a-aea7-41dd-8474-b5a87959e317
-- title:
--   Gains, mixed predictions, cumulative gains and regret $R=\max_i\sum_t g_t^i-\sum_t g_t^{i^*_t}$
-- statement:
--   **Prediction with expert advice** against an oblivious adversary. There are $N$ experts and $T$ rounds. The gains $g_t^i\in[0,1]$ for $t=1,\dots,T$ and $i=1,\dots,N$ are fixed in advance.
--
--   1. A **mixed prediction** is a probability vector $w$ over the experts. The gain of an algorithm predicting $w_u$ at round $u$ is the weighted average $g_u^{\mathcal A}=\sum_i w_u(i)\,g_u^i$.
--   2. The **cumulative gains** are $G_t^i=\sum_{u=1}^t g_u^i$ and $G_t^{\mathcal A}=\sum_{u=1}^t g_u^{\mathcal A}$.
--   3. If the experts actually picked at rounds $1,\dots,T$ are $i^*_1,\dots,i^*_T$, the **regret** against the best expert is
--
--   $$
--   R=\Bigl(\max_i\sum_{t=1}^T g_t^i\Bigr)-\sum_{t=1}^T g_t^{i^*_t}.
--   $$
--
--   These are the objects in which the paper's guarantees are stated.
--
--   **Formalization Note** Experts are `Fin N`, and rounds are 1-based. A gain array is a function `ℕ → Fin N → ℝ`, constrained only on rounds $1,\dots,T$. The maximum is `⨆ i`, which equals the maximum when $N\ge1$.
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), §3.1, p.13 (PDF p.14)

import Mathlib

namespace FewExperts

/-- A gain array for `N` experts over the horizon `T` (§3.1, p.13): `g t i ∈ [0, 1]` for every
round `t ∈ {1, …, T}` and every expert `i`. Values at rounds `0` and `> T` are never read by the
protocol. -/
def IsGainSeq {N : ℕ} (T : ℕ) (g : ℕ → Fin N → ℝ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ T → ∀ i, g t i ∈ Set.Icc (0 : ℝ) 1

/-- A mixed prediction (§3.1, p.13): a probability vector over the experts. -/
def IsProbVec {N : ℕ} (w : Fin N → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1

/-- The cumulative gain `G_t^i = ∑_{u=1}^t g_u^i` of expert `i` (p.13). -/
noncomputable def cumGain {N : ℕ} (g : ℕ → Fin N → ℝ) (t : ℕ) (i : Fin N) : ℝ :=
  ∑ u ∈ Finset.Icc 1 t, g u i

/-- The gain `g_u^A = ∑_i w_u(i) g_u^i` at round `u` of an algorithm whose (mixed) prediction at
round `u` is `w u` (p.13: "taking the weighted average of the experts' gains when it predicts a
mix"). -/
noncomputable def mixGain {N : ℕ} (g : ℕ → Fin N → ℝ) (w : ℕ → Fin N → ℝ) (u : ℕ) : ℝ :=
  ∑ i, w u i * g u i

/-- The cumulative (mixed) gain `G_t^A = ∑_{u=1}^t g_u^A` of an algorithm with predictions `w`
(p.13). -/
noncomputable def cumMix {N : ℕ} (g : ℕ → Fin N → ℝ) (w : ℕ → Fin N → ℝ) (t : ℕ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 t, mixGain g w u

/-- **Regret against the best expert** (§3.1, p.13).
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), §3.1, p.13 (PDF 14): "The goal is to minimize regret against the best expert, which
is defined as R = (max_i ∑_{t=1}^T g_t^i) − ∑_{t=1}^T g_t^{i*_t}."

For the experts `a t` actually picked at rounds `t = 1, …, T`,
`gainRegret T g a = max_i ∑_{t=1}^T g t i − ∑_{t=1}^T g t (a t)`.

**Formalization Note** The maximum over the finite set `Fin N` is written `⨆ i`; it is the true
maximum when `N ≥ 1` (every statement of the mission has `N ≠ 0`). -/
noncomputable def gainRegret {N : ℕ} (T : ℕ) (g : ℕ → Fin N → ℝ) (a : ℕ → Fin N) : ℝ :=
  (⨆ i, cumGain g T i) - ∑ t ∈ Finset.Icc 1 T, g t (a t)

end FewExperts


