-- Prove2me | Definitions.Def_StarShapedRisk_LawInvariant_VaR
-- name    : StarShapedRisk_LawInvariant_VaR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:06:25.976128+00:00
-- url     : https://prove2.me/theorems/9bc635be-6b26-4f63-b108-d3ef43c0fa0f
-- title:
--   Value-at-Risk and first-order stochastic dominance of losses
-- statement:
--   Let $P$ be a probability measure on a measurable space $(\Omega,\mathcal F)$ and let $X:\Omega\to\mathbb R$ represent a loss. The **Value-at-Risk** of $X$ at level $\alpha$ is
--   $$\mathrm{VaR}_\alpha(X)=\inf\{x\in\mathbb R : P(X>x)\le 1-\alpha\},$$
--   the smallest capital reserve that brings the probability of a loss exceeding the reserve down to at most $1-\alpha$. Equivalently, it is the lower $\alpha$-quantile $\inf\{x : F_X(x)\ge\alpha\}$ of the distribution function $F_X(x)=P(X\le x)$.
--
--   For losses $X,Y$, $X$ **first-order stochastically dominates** $Y$, written $X\succsim_{\mathrm{FSD}}Y$, if $F_X\ge F_Y$, that is,
--   $$P(X\le x)\ \ge\ P(Y\le x)\qquad\text{for all }x\in\mathbb R.$$
--   Since $X$ and $Y$ are losses, $X\succsim_{\mathrm{FSD}}Y$ means that $X$ is the stochastically smaller loss.
--
--   These two notions are the building blocks of Eq. (A.1) and of the representation (25) in Theorem 5.
--
--   **Formalization Note** Both notions are defined for arbitrary functions $\Omega\to\mathbb R$; the theorems apply them only to bounded measurable positions. Probabilities are in $[0,\infty]$ (`ENNReal`) and $1-\alpha$ enters through `ENNReal.ofReal`. VaR uses `sInf`: for bounded $X$ and $\alpha\in(0,1]$ the set is nonempty and bounded below, while for $X$ unbounded above the set may be empty and Lean returns the default value $0$.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), p. 2641 (definition of VaR); p. 2652, Appendix, proof of Theorem 5, Eq. (A.1) (definition of ≿FSD)

import Mathlib

namespace StarShapedRisk.LawInvariant

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Value-at-Risk of the loss `X` at level `α` under `P`:
`VaR_α(X) = inf {x ∈ ℝ | P(X > x) ≤ 1 - α}`. For a bounded `X` and `α ∈ (0,1]` the set is
nonempty and bounded below. If `X` is unbounded above the set can be empty and `sInf` returns
Lean's junk value `0`. -/
noncomputable def VaR (P : Measure Ω) (α : ℝ) (X : Ω → ℝ) : ℝ :=
  sInf {x : ℝ | P {ω | x < X ω} ≤ ENNReal.ofReal (1 - α)}

/-- First-order stochastic dominance between losses: `X ≿FSD Y` means `F_X ≥ F_Y`, i.e.
`P(X ≤ x) ≥ P(Y ≤ x)` for every real `x`. With the loss convention, `X` is the smaller loss. -/
def FSD (P : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ∀ x : ℝ, P {ω | Y ω ≤ x} ≤ P {ω | X ω ≤ x}

end StarShapedRisk.LawInvariant


