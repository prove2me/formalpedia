-- Prove2me | Definitions.Def_MultiItemRev_KSeparate_Model
-- name    : MultiItemRev_KSeparate_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:28:00.446005+00:00
-- url     : https://prove2.me/theorems/3394255e-c7a6-46ba-889a-c8d77517a0ef
-- title:
--   p. 21 — stochastic domination and the equal-revenue law
-- statement:
--   This module adds two one-good distributional notions to the single-buyer model. A nonnegative random value $X$ is **stochastically dominated** by $Y$ when every upper-tail probability is smaller:
--
--   $$\Pr[X\ge p]\le\Pr[Y\ge p]\qquad\text{for every real }p.$$
--
--   The **equal-revenue law** is supported on $[1,\infty)$ and has density $f(x)=1/x^2$ there. Its upper tail is $\Pr[V\ge p]=1/p$ for $p\ge1$; hence a posted price $p\ge1$ gives revenue $p\Pr[V\ge p]=1$. These definitions are used in the paper's comparisons of separate and bundled revenue.
--
--   **Formalization Note** This module imports `MultiItemRev.Decomp.Model` for the mechanism and revenue definitions. `StochDominated` quantifies over $p\ge0$ because values are nonnegative: for probability laws, the condition for $p<0$ holds automatically. `erLaw` is the pushforward under `Real.toNNReal` of Lebesgue measure on $[1,\infty)$ weighted by $1/x^2$.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 21, §5 (stochastic domination and the equal-revenue distribution)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KSeparate

def StochDominated (ν ν' : Measure ℝ≥0) : Prop :=
  ∀ p : ℝ≥0, ν {t | p ≤ t} ≤ ν' {t | p ≤ t}

noncomputable def erLaw : Measure ℝ≥0 :=
  ((volume.restrict (Set.Ici (1 : ℝ))).withDensity
    (fun x => ENNReal.ofReal (1 / x ^ 2))).map Real.toNNReal

end MultiItemRev.KSeparate


