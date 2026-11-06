-- Prove2me | Definitions.Def_RiskDistMDP_DPP_JpolInf
-- name    : RiskDistMDP_DPP_JpolInf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:28.209591+00:00
-- url     : https://prove2.me/theorems/04d1525a-d9e5-4940-800f-34531dfa041a
-- title:
--   Infinite-horizon policy values $J^{\mathfrak p}_{t,\infty}$ (5.1)
-- statement:
--   For $\mathfrak p\in\Pi$,
--   $$J^{\mathfrak p}_{0,\infty}:=\lim_{T\to\infty}J^{\mathfrak p}_{0,T},\qquad J^{\mathfrak p}_{t,\infty}(x):=\lim_{T\to\infty}J^{\mathfrak p}_{t,T}(x),\quad x\in\mathbb X.$$
--
--   **Formalization Note** `limUnder atTop`, pointwise, in $\mathbb R$ for $t\ge1$ and in `EReal` at time $0$; Lemma 5.1 states that the limits exist. They are not defined as fixed points.
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, (5.1), p. 20

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_Jpol

set_option autoImplicit false

open MeasureTheory Filter

namespace RiskDistMDP.DPP

/-- The infinite-horizon value of a Markovian policy, `J^𝔭_{t,∞}(x) := lim_{T→∞} J^𝔭_{t,T}(x)`,
`x ∈ 𝕏` (arXiv:2203.09612v4, (5.1), p.20).

**Formalization Note** `limUnder atTop` in `ℝ`, pointwise in `x`, for `t ≥ 1`. It is a junk value
where the sequence diverges; Lemma 5.1 (`lemma_5_1`) states uniform convergence for `𝔭 ∈ Π`. It is
not defined as a fixed point of `ℌ^𝔭`. -/
noncomputable def JpolInf {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] (R : RiskMDP 𝕏 𝔸)
    (𝔭 : ℕ → 𝕏 → ProbabilityMeasure 𝔸) (t : ℕ) (x : 𝕏) : ℝ :=
  limUnder atTop fun T => Jpol R 𝔭 T t x

/-- `J^𝔭_{0,∞} := lim_{T→∞} J^𝔭_{0,T}` (arXiv:2203.09612v4, (5.1), p.20), as a `limUnder atTop`
in `EReal`. -/
noncomputable def Jpol0Inf {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] (R : RiskMDP 𝕏 𝔸)
    (𝔭 : ℕ → 𝕏 → ProbabilityMeasure 𝔸) : EReal :=
  limUnder atTop fun T => Jpol0 R 𝔭 T

end RiskDistMDP.DPP


