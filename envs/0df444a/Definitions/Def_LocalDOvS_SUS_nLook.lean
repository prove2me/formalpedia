-- Prove2me | Definitions.Def_LocalDOvS_SUS_nLook
-- name    : LocalDOvS_SUS_nLook
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:25:21.928897+00:00
-- url     : https://prove2.me/theorems/faaf5d0d-5eda-4165-a068-f9893149f687
-- title:
--   Sample size $n(M)$ of a test at active-set size $M$
-- statement:
--   The per-point sample size of a test when the active set has $M$ points:
--
--   $$
--   n(M):=\Big\lceil\frac{12800\,\sigma^2\log(2/\alpha)}{M^2\epsilon^2}\Big\rceil ,
--   $$
--
--   the least $n$ with $h(n,\sigma,\alpha)\le M\epsilon/80$. Line 8 of Algorithm 2 stops sampling a point once its half-width is at most $|S|\epsilon/80$, which happens exactly at $n(|S|)$ samples.
--
--   **Formalization Note** $\alpha=\delta/(2N^2)$; the paper's proof of Lemma EC.6 writes $n(|S_k|)$ with $\log(4T_{\max}/\delta)$, $T_{\max}=N$.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Algorithm 2, lines 7–8, p.15; proof of Lemma EC.6, p.ec11

import Mathlib
import Definitions.Def_LocalDOvS_SUS_alphaSUS

open scoped NNReal

namespace LocalDOvS.SUS

/-- The per-point sample size of a test at active-set size `M` (Zhang–Zheng–Lavaei,
arXiv:2012.02427v2, Algorithm 2, lines 7–8, p.15, and `n(|S_k|)` in the proof of Lemma EC.6,
p.ec11): `n(M) := ⌈12800 σ² log(2/α) / (M² ε²)⌉`, the least `n` with
`h(n, σ, α) ≤ M · ε / 80`.

**Formalization Note.** `α = alphaSUS N δ`, so `log(2/α) = log(4N²/δ)`; the paper prints
`log(4 T_max/δ)` with `T_max = N`. Natural-number ceiling `⌈·⌉₊`. -/
noncomputable def nLook (N : ℕ) (σ : ℝ≥0) (ε δ : ℝ) (M : ℕ) : ℕ :=
  ⌈12800 * (σ : ℝ) ^ 2 * Real.log (2 / alphaSUS N δ) / ((M : ℝ) ^ 2 * ε ^ 2)⌉₊

end LocalDOvS.SUS


