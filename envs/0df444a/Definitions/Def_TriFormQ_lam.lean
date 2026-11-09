-- Prove2me | Definitions.Def_TriFormQ_lam
-- name    : TriFormQ_lam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:44:10.530806+00:00
-- url     : https://prove2.me/theorems/c4f31927-f4a1-4f6d-9fdc-f02406be6017
-- title:
--   Failure-parameter factor $\lambda(\varepsilon)=\max\{1,\log_2(1/\varepsilon)\}$
-- statement:
--   For a failure probability $\varepsilon>0$ set
--
--   $$\lambda(\varepsilon)=\max\{1,\ \log_2(1/\varepsilon)\}.$$
--
--   Every factor $\log(1/\varepsilon)$ or $\log(1/\delta)$ that multiplies or adds into a query bound of this mission is written as $\lambda(\cdot)$. For $\varepsilon\le 1/2$ it equals $\log_2(1/\varepsilon)$. The maximum with $1$ keeps the bounds meaningful as $\varepsilon\to 1$, where $\log(1/\varepsilon)\to 0$ although an algorithm with nontrivial success must still make a query.
--
--   **Formalization Note** Logarithms are base 2 (the paper's convention, p.10); `Real.logb 2` is used.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 1, p.3 (PDF p.6); Lemma 4, p.15 (PDF p.18)

import Mathlib

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 1, p.3 (PDF p.6),
Lemma 4, p.15, Theorem 6, p.29, Theorem 7, p.34: the failure-parameter factor
`λ(ε) = max{1, log₂(1/ε)}` used for every `log(1/ε)` that multiplies or adds into a query
bound.

**Formalization Note.** Logarithms are base 2 (§2, p.10). For `ε ≤ 1/2`, `λ(ε) = log₂(1/ε)`;
the `max` with 1 keeps a bound meaningful as `ε → 1`, where the printed `log(1/ε)` tends to 0
while any algorithm with nontrivial success needs at least one query. -/
noncomputable def lam (ε : ℝ) : ℝ :=
  max 1 (Real.logb 2 (1 / ε))

end TriFormQ


