-- Prove2me | Definitions.Def_ConvBoundsQA_qPlus
-- name    : ConvBoundsQA_qPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:13.094984+00:00
-- url     : https://prove2.me/theorems/c185736d-4a5b-4758-862f-ce198d8c5895
-- title:
--   Left and right quantile functionals $q^-_t(\mu)$, $q^+_t(\mu)$
-- statement:
--   Let $\mathcal M$ be the set of Borel probability measures on $\mathbb R$. For $\mu\in\mathcal M$ the **left quantile** at level $t\in(0,1]$ and the **right quantile** at level $t\in[0,1)$ are
--   $$
--   q^-_t(\mu)=\inf\{x\in\mathbb R:\mu(-\infty,x]\ge t\},\qquad q^+_t(\mu)=\inf\{x\in\mathbb R:\mu(-\infty,x]>t\}.
--   $$
--   The extreme cases $q^+_0(\mu)$ and $q^-_1(\mu)$ are the essential infimum and the essential supremum of $\mu$, and may be $-\infty$ and $+\infty$ respectively; for $t\in(0,1)$ both quantiles are finite.
--
--   These are the quantile (Value-at-Risk) functionals of the whole mission.
--
--   **Formalization Note** Both infima are taken in the extended reals `EReal` over the image of the real set, so the empty set gives $+\infty$ and a set unbounded below gives $-\infty$. The values outside the stated ranges of $t$ are never used.
-- source:
--   Blanchet, Lam, Liu, Wang, Convolution Bounds on Quantile Aggregation, arXiv:2007.09320v5, §3, p.7

import Mathlib

open MeasureTheory

namespace ConvBoundsQA

/-- The left quantile functional `q⁻_t(μ) = inf {x ∈ ℝ : μ(−∞, x] ⩾ t}`
(Blanchet, Lam, Liu, Wang, *Convolution Bounds on Quantile Aggregation*, arXiv:2007.09320v5, §3, p.7).
The page defines it for `t ∈ (0, 1]`; `q⁻_1` is the essential supremum.

**Formalization Note** The infimum is taken in `EReal`, so `q⁻_1(μ) = +∞` when `μ` has unbounded
support above (the empty set has infimum `⊤`) and the value `−∞` is representable. For a probability
measure and `t ∈ (0, 1)` the value is a real number. Outside `t ∈ (0, 1]` the value is not used. -/
noncomputable def qMinus (t : ℝ) (μ : Measure ℝ) : EReal :=
  sInf ((fun x : ℝ => (x : EReal)) '' {x : ℝ | ENNReal.ofReal t ≤ μ (Set.Iic x)})

/-- The right quantile functional `q⁺_t(μ) = inf {x ∈ ℝ : μ(−∞, x] > t}`
(Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, §3, p.7). The page defines it for `t ∈ [0, 1)`;
`q⁺_0` is the essential infimum.

**Formalization Note** The infimum is taken in `EReal`, so `q⁺_0(μ) = −∞` when `μ` has support
unbounded below (the set is then not bounded below). For a probability measure and `t ∈ (0, 1)` the
value is a real number. Outside `t ∈ [0, 1)` the value is not used (at `t = 1` the set is empty and
the value is `⊤`). -/
noncomputable def qPlus (t : ℝ) (μ : Measure ℝ) : EReal :=
  sInf ((fun x : ℝ => (x : EReal)) '' {x : ℝ | ENNReal.ofReal t < μ (Set.Iic x)})

end ConvBoundsQA


