-- Prove2me | Definitions.Def_QuantileMDP_quantile
-- name    : QuantileMDP_quantile
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:41:24.519111+00:00
-- url     : https://prove2.me/theorems/d6786fb9-1782-4beb-8d86-cda29b47e181
-- title:
--   The $\tau$-quantile $Q_\tau$ of a law on $\mathbb R$, with $Q_0=\operatorname{ess\,inf}$ and $Q_1=\operatorname{ess\,sup}$
-- statement:
--   Let $\mu$ be a law on $\mathbb R$ (the distribution of a random variable $X$) and $\tau\in[0,1]$. The **$\tau$-quantile** of $\mu$ is
--
--   $$
--   Q_\tau(\mu)=\begin{cases}
--   \sup\{D\in\mathbb R:\ \mu([D,\infty))=1\}, & \tau=0,\\
--   \inf\{x\in\mathbb R:\ \mu((-\infty,x])\ge\tau\}, & 0<\tau<1,\\
--   \inf\{U\in\mathbb R:\ \mu((-\infty,U])=1\}, & \tau=1,
--   \end{cases}
--   $$
--
--   with the supremum and infimum taken in the extended reals $[-\infty,+\infty]$. For $\tau\in(0,1)$ this is Definition 1, $Q_\tau(X)=\inf\{x\mid P(X\le x)\ge\tau\}$; for $\tau=0$ and $\tau=1$ it is the precise form of footnote 1, the essential infimum and the essential supremum of $X$.
--
--   The quantile of a random variable is the quantile of its law. This is the objective of the quantile MDP: the policy maximizes $Q_\tau$ of the cumulative reward.
--
--   **Formalization Note** The value lies in `EReal`, so that $\pm\infty$ (possible for unbounded laws, and for the zero measure) are representable rather than replaced by a default $0$. Values at $\tau\notin[0,1]$ are never used.
-- source:
--   Li, Zhong, Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §3.1, Definition 1 and footnote 1, p.9

import Mathlib

open MeasureTheory

namespace QuantileMDP

/-- The `τ`-quantile of a law `μ` on `ℝ` (Definition 1 and footnote 1). For `τ ∈ (0,1)`,
`Q_τ = inf {x | P(X ≤ x) ≥ τ}`; `Q_0 = sup {D ∈ ℝ | P(X ≥ D) = 1}` (essential infimum) and
`Q_1 = inf {U ∈ ℝ | P(X ≤ U) = 1}` (essential supremum).
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, §3.1,
Definition 1 and footnote 1, p.9.

**Formalization Note** The quantile of a random variable `X` is the quantile of its law
`P.map X`. The value lies in `EReal`, so that `Q_0 = -∞` and `Q_1 = +∞` are representable for
unbounded laws; the infimum and supremum are taken in `EReal` over the coerced real sets. The
endpoints `τ = 0` and `τ = 1` use the precise forms of footnote 1. Values for `τ ∉ [0,1]` are not
used by any statement of the mission. -/
noncomputable def quantile (μ : Measure ℝ) (τ : ℝ) : EReal :=
  if τ = 0 then sSup ((fun x : ℝ => (x : EReal)) '' {D : ℝ | μ (Set.Ici D) = 1})
  else if τ = 1 then sInf ((fun x : ℝ => (x : EReal)) '' {U : ℝ | μ (Set.Iic U) = 1})
  else sInf ((fun x : ℝ => (x : EReal)) '' {x : ℝ | ENNReal.ofReal τ ≤ μ (Set.Iic x)})

end QuantileMDP


