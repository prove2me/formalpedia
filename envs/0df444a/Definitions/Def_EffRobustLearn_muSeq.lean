-- Prove2me | Definitions.Def_EffRobustLearn_muSeq
-- name    : EffRobustLearn_muSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:36:22.075197+00:00
-- url     : https://prove2.me/theorems/97594fcf-6173-43e2-8693-aa07543c2b01
-- title:
--   The iterates $\bar\mu_t$, the hypotheses $h_t$ and the output $\bar h_T$
-- statement:
--   From an initial concept $c_0$ and concepts $c_t$, the iterates are $\bar\mu_1=c_0$ and $\bar\mu_{t+1}=(1-\gamma_t)\bar\mu_t+\gamma_tc_t$. The hypotheses are $h_t=\mathrm{maj}_k\circ\bar\mu_t$, and the output is
--   $$\bar h_T(x)=T^{-1}\sum_{t=1}^Th_t(x).$$
--
--   **Formalization Note** $\bar\mu_t$ depends only on $c_1,\dots,c_{t-1}$. Each is computed pointwise, without a list of convex weights; membership in $\mathrm{conv}(C)$ is a consequence, by induction.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Algorithm 1, lines 3, 6, 9, 11, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_EffRobustLearn_toPM
import Definitions.Def_EffRobustLearn_majK
import Definitions.Def_EffRobustLearn_numRounds

namespace EffRobustLearn

/-- The iterates of Algorithm 1, lines 3 and 9, Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.14, from the initial concept `c0` and the concepts `c_t`:
`μ̄_1 = c0` and `μ̄_{t+1} = (1 - γ_t) μ̄_t + γ_t c_t`. Rounds are 1-based; the value at index `0` is never used. `μ̄_t`
depends only on `c_1, …, c_{t-1}`. -/
noncomputable def muSeq {X : Type*} (c0 : X → Bool) (c : ℕ → X → Bool) : ℕ → X → ℝ
  | 0 => toPM c0
  | 1 => toPM c0
  | t + 2 => fun x => (1 - stepSize (t + 1)) * muSeq c0 c (t + 1) x + stepSize (t + 1) * toPM (c (t + 1)) x

/-- The hypotheses of Algorithm 1, line 6, p.14: `h_t(x) = maj_k(μ̄_t(x))` with `k = ⌈64/ε²⌉`. -/
noncomputable def hSeq {X : Type*} (ε : ℝ) (c0 : X → Bool) (c : ℕ → X → Bool) (t : ℕ) (x : X) : ℝ :=
  majK (majParam ε) (muSeq c0 c t x)

/-- The output of Algorithm 1, line 11, p.14: `h̄_T(x) = T⁻¹ ∑_{t=1}^T h_t(x)`. The returned randomized hypothesis is
`h(x) ∼ Rad(h̄_T(x))`, and `err_D(h, c⋆) = err_D(h̄_T, c⋆)` (p.18). -/
noncomputable def hbarSeq {X : Type*} (ε : ℝ) (c0 : X → Bool) (c : ℕ → X → Bool) (x : X) : ℝ :=
  (1 / (numRounds ε : ℝ)) * ∑ t ∈ Finset.Icc 1 (numRounds ε), hSeq ε c0 c t x

end EffRobustLearn


