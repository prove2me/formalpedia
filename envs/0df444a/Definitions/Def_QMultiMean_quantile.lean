-- Prove2me | Definitions.Def_QMultiMean_quantile
-- name    : QMultiMean_quantile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:07:55.947208+00:00
-- url     : https://prove2.me/theorems/eacc90c6-848c-458e-940d-5c22bfbb5abe
-- title:
--   Quantile $Q(p)=\sup\{x:\Pr[X\ge x]\ge p\}$
-- statement:
--   Let $Z$ be a finite real-valued random variable with probability mass function $P$, and let $p\in(0,1]$. The **quantile of order $p$** is
--   $$Q(p)=\sup\{x\in\mathbb R:\Pr[Z\ge x]\ge p\}.$$
--   The set is nonempty and bounded above, and the supremum is attained. $Q$ is nonincreasing in $p$.
--
--   The quantile estimator of Proposition 2.9 and the analysis of Algorithm 2 are stated in terms of $Q$.
--
--   **Formalization Note** Every statement of the mission evaluates $Q$ at orders in $(0,1]$. Outside that range `sSup` returns $0$.
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, p.6, Definition 2.3

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable

set_option autoImplicit false

namespace QMultiMean

/-- The **quantile** of order `p` of a finite real-valued random variable `Z` under `P`
(Cornelissen, Hamoudi, Jerbi, arXiv:2111.09787v2, Definition 2.3, p.6):
`Q(p) = sup {x ∈ ℝ : Pr[Z ≥ x] ≥ p}`.

**Formalization Note.** For `p ∈ (0, 1]` and a probability mass function `P` the set is nonempty
(it contains `min_ω Z(ω)`) and bounded above (by `max_ω Z(ω)`), and the supremum is attained. Every
statement of this mission uses `Q` only at orders in `(0, 1]`. Outside that range `sSup` returns the
junk value `0` (the paper's `Q(0) = +∞`, `Q(p) = −∞` for `p > 1`). -/
noncomputable def quantile {N : ℕ} (P : Fin (N + 1) → ℝ) (Z : Fin (N + 1) → ℝ) (p : ℝ) : ℝ :=
  sSup {x : ℝ | p ≤ prob P (fun ω => x ≤ Z ω)}

end QMultiMean


