-- Prove2me | Definitions.Def_HedgePSNV_IsMartingaleOn
-- name    : HedgePSNV_IsMartingaleOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:00:24.408182+00:00
-- url     : https://prove2.me/theorems/05273f94-5d39-43ad-ba53-7028d2f9a434
-- title:
--   Martingale on the time interval $[0,T]$
-- statement:
--   Let $(\Omega,\mathcal F)$ carry a filtration $(\mathcal F_t)_{t\ge0}$, a measure $Q$ and a real process $Y$. $Y$ is a **martingale on $[0,T]$** under $Q$ with respect to $(\mathcal F_t)$ when, for every $t\le T$, $Y_t$ is $\mathcal F_t$-measurable and $Q$-integrable, and
--   $$
--   \mathbb E_Q[Y_t\mid\mathcal F_s]=Y_s\quad Q\text{-a.s.},\qquad 0\le s\le t\le T .
--   $$
--   This is the notion of martingale in every statement of the mission: Assumption 5 ($Z$ is a martingale over $[0,T]$), the sets $\mathcal M_X$, $\mathcal M_N$, $\mathcal A_X$, $\mathcal A_N$ of (EC.7.13)–(EC.7.17), and Lemmas EC.1–EC.4.
--
--   **Formalization Note** Mathlib's `Martingale` constrains all times in $\mathbb R_{\ge0}$; the paper's martingales live on $[0,T]$, so this predicate says nothing after $T$. Measurability is strong measurability.
-- source:
--   Wang–Yao–Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, footnote 4, p.11; Assumption 5, p.12; (EC.7.13)–(EC.7.15), p.ec29

import Mathlib

open MeasureTheory
open scoped NNReal

namespace HedgePSNV

/-- `Y` is a martingale on the time interval `[0, T]` under the measure `Q` with respect to
the filtration `F`: each `Y t` (`t ≤ T`) is `F t`-strongly measurable and `Q`-integrable, and
`E_Q[Y t | F s] = Y s` `Q`-a.s. for `s ≤ t ≤ T`. This is the notion of martingale used
throughout arXiv:2201.01026v4 (footnote 4, p.11: "martingales … are defined with respect to
F_t"; Assumption 5, p.12; (EC.7.13)–(EC.7.15), p.ec29).

**Formalization Note** Mathlib's `Martingale` is over the whole index set `ℝ≥0`; the paper's
martingales live on `[0, T]`, so this predicate only constrains `t ≤ T`. -/
def IsMartingaleOn {Ω : Type*} [m : MeasurableSpace Ω] (T : ℝ≥0) (F : Filtration ℝ≥0 m)
    (Q : Measure Ω) (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ t : ℝ≥0, t ≤ T → StronglyMeasurable[F t] (Y t)) ∧
  (∀ t : ℝ≥0, t ≤ T → Integrable (Y t) Q) ∧
  ∀ s t : ℝ≥0, s ≤ t → t ≤ T → condExp (F s) Q (Y t) =ᵐ[Q] Y s

end HedgePSNV


