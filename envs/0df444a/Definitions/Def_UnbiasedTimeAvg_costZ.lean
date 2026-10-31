-- Prove2me | Definitions.Def_UnbiasedTimeAvg_costZ
-- name    : UnbiasedTimeAvg_costZ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:18:37.931118+00:00
-- url     : https://prove2.me/theorems/e12d66a8-6bb8-4d9c-8ea8-7ffccc398965
-- title:
--   The expected cost $T_k$ of $Z_k$ (the paper's cost model)
-- statement:
--   The paper assumes that simulating $f_{k,l}$ costs $k2^l$ in expectation (p.8). Simulating $Z_k$ at level $N=l$ requires $f_{k,l+1}$ and $f_{k,l}$, which costs $3k2^l$ (proof of Lemma 3.2, p.28). Hence the expected time to simulate $Z_k$ is
--   $$T_k=\sum_{l=0}^\infty p_l\cdot 3k2^l.$$
--
--   **Formalization Note** This is the paper's stated simplifying cost model, taken as the definition; no machine model is formalized. It is a real `tsum`, so the theorems bounding it also assert the convergence of the series.
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), p.8 (cost of f_{k,l}, definition of T_k) and proof of Lemma 3.2, p.28

import Mathlib

namespace UnbiasedTimeAvg

/-- **The expected time `T_k` to simulate `Z_k`, under the paper's cost model.**
Kahalé, arXiv:2209.09581v1, p.8 ("For simplicity, it is assumed that the expected time to simulate
`f_{k,l}` is equal to `k2^l`. … Let `T_k` be the expected time required to simulate `Z_k`") and
the proof of Lemma 3.2, p.28 ("The expected cost of computing `f_{k,l+1} − f_{k,l}` is at most
`3k2^l`").

`costZ p k = Σ_{l ≥ 0} p_l · 3k2^l`: with probability `p_l` the level is `N = l`, and simulating
`f_{k,l+1}` and `f_{k,l}` costs `k2^{l+1} + k2^l = 3k2^l`.

**Formalization Note.** The paper has no formal machine model; this definition *is* its stated
simplifying cost model, not a theorem about running time. It is a real `tsum`, so the theorems
that bound it also assert its summability. -/
noncomputable def costZ (p : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑' l : ℕ, p l * (3 * (k : ℝ) * 2 ^ l)

end UnbiasedTimeAvg


