-- Prove2me | Definitions.Def_PlugInRisk_IsPareto
-- name    : PlugInRisk_IsPareto
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:39.89961+00:00
-- url     : https://prove2.me/theorems/1a8ea61d-8aa5-434a-9109-642be0fc49a3
-- title:
--   Pareto law with scale $x$ and shape $q$
-- statement:
--   A law $\nu$ on $\mathbb R$ (equivalently a random variable $X$ with this law) is **Pareto with scale parameter $x>0$ and shape parameter $q>0$** if
--
--   $$
--   \nu([t,\infty))=P[X\ge t]=\begin{cases}(x/t)^q,& t\ge x,\\ 1,& t<x.\end{cases}
--   $$
--
--   Such a variable has finite moments exactly of order below $q$; it is the test variable in the definition of $q$-regularity.
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, p.7

import Mathlib

open MeasureTheory

namespace PlugInRisk

/-- **Pareto law** (Bartl & Tangpi, arXiv:2003.10479v2, p.7): a random variable `X` has Pareto
distribution with scale parameter `x > 0` and shape parameter `q > 0` if
`P[X ≥ t] = (x/t)^q` for `t ≥ x` and `P[X ≥ t] = 1` for `t < x`.

`IsPareto ν x q` says the law `ν` on `ℝ` has this tail; `X` is Pareto iff its law is.

**Formalization Note** Stated on the law `ν`; the condition forces `ν` to be a probability
measure (let `t → −∞`). -/
def IsPareto (ν : Measure ℝ) (x q : ℝ) : Prop :=
  ∀ t : ℝ, ν (Set.Ici t) = if x ≤ t then ENNReal.ofReal ((x / t) ^ q) else 1

end PlugInRisk


