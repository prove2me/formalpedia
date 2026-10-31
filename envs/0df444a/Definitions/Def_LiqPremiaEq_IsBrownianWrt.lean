-- Prove2me | Definitions.Def_LiqPremiaEq_IsBrownianWrt
-- name    : LiqPremiaEq_IsBrownianWrt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:04.041999+00:00
-- url     : https://prove2.me/theorems/39942c7c-c7cb-4a85-99e1-11a7a2f4bf92
-- title:
--   Brownian motion with respect to a filtration
-- statement:
--   Let $(\Omega,\mathcal F,P)$ carry a filtration $(\mathcal F_t)_{t\ge0}$ and a $D$-dimensional process $W$. $W$ is a **Brownian motion with respect to $(\mathcal F_t)$** if
--
--   1. $W$ is $(\mathcal F_t)$-adapted;
--   2. every path $t\mapsto W_t(\omega)$ is continuous;
--   3. for $s\le t$, the increment $W_t-W_s$ is independent of $\mathcal F_s$.
--
--   Together with the requirement that $W$ be a standard $D$-dimensional Brownian motion (the published `Peng1990.SMP.IsStdBrownian`), this is the paper's standing setting: a filtered probability space $(\Omega,\mathcal F,(\mathcal F_t)_{t\in[0,T]},P)$ supporting a $D$-dimensional standard Brownian motion.
--
--   **Formalization Note** The filtration is arbitrary, not the natural filtration of $W$. Time is $\mathbb R_{\ge0}$; the paper's $[0,T]$ is read off by restriction. Continuity of all paths (the usual definition) makes $W$ progressively measurable.
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, Notation, p.3

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LiqPremiaEq

/-- `W` is a Brownian motion **with respect to the filtration `𝓕`**: it is `𝓕`-adapted, every
path `t ↦ W t ω` is continuous, and for `s ≤ t` the increment `W t − W s` is independent of `𝓕 s`
under `P`. Together with `Peng1990.SMP.IsStdBrownian P W` (Brownian laws, independent
coordinates) this is "a filtered probability space `(Ω, 𝓕, (𝓕ₜ), P)` supporting a
`D`-dimensional standard Brownian motion".
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Notation, p.3.

**Formalization Note** The filtration is arbitrary (not the natural filtration of `W`). Paths are
continuous for every `ω`, as in the usual definition of Brownian motion; with this, `W` is
progressively measurable. Time is `ℝ≥0`; the paper's `[0, T]` is read off by restriction. -/
structure IsBrownianWrt {Ω : Type*} [mΩ : MeasurableSpace Ω] {D : ℕ}
    (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (W : ℝ≥0 → Ω → Fin D → ℝ) : Prop where
  adapted : StronglyAdapted 𝓕 W
  cont : ∀ ω, Continuous (fun t => W t ω)
  indep_incr : ∀ s t : ℝ≥0, s ≤ t →
    Indep (MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance) (𝓕 s) P

end LiqPremiaEq


