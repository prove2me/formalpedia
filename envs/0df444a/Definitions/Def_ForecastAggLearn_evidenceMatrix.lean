-- Prove2me | Definitions.Def_ForecastAggLearn_evidenceMatrix
-- name    : ForecastAggLearn_evidenceMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:14.458983+00:00
-- url     : https://prove2.me/theorems/31d4fac3-6d6a-462e-9785-f6bde90e04c1
-- title:
--   Evidence matrix $A\in\{0,1\}^{n\times m}$
-- statement:
--   There are $n$ experts and $m$ signals. Expert $i\in[n]$ observes the signals $(s_j)_{j\in A_i}$ for a set $A_i\subseteq[m]$. The **evidence matrix** $A\in\{0,1\}^{n\times m}$ records who sees what:
--
--   $$
--   A(i,j)=\begin{cases}1 & j\in A_i,\\ 0 & j\notin A_i.\end{cases}
--   $$
--
--   Row $i$ of $A$ is the indicator of $A_i$. In log-likelihood space the experts' forecasts are $A\tilde y+\tilde\mu\mathbf 1_n$, so the injectivity of $A$ and its least singular value govern whether, and how fast, the optimal aggregate can be learned.
--
--   **Formalization Note** Experts are `Fin n`, signals `Fin m`, and $A_i$ is `Aset i : Finset (Fin m)`. An empty $A_i$ is allowed; that expert reports the prior.
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, §2, p.9

import Mathlib

namespace ForecastAggLearn

/-- **The evidence matrix.**
Babichenko, Garber, arXiv:1802.07107v1, §2, p.9: "Expert i ∈ [n] observes only the signals
(s_j)_{j∈A_i} where A_i ⊂ [m]. We denote by A ∈ {0,1}^{n×m} the evidence matrix, where
A(i, j) = 1 iff j ∈ A_i."

`Aset i` is the set `A_i ⊆ [m]` of signals observed by expert `i`.

**Formalization Note.** Experts are `Fin n` and signals `Fin m` (0-based). An empty `A_i` is
allowed: that expert observes nothing and reports the prior. -/
def evidenceMatrix {n m : ℕ} (Aset : Fin n → Finset (Fin m)) : Matrix (Fin n) (Fin m) ℝ :=
  fun i j => if j ∈ Aset i then 1 else 0

end ForecastAggLearn


