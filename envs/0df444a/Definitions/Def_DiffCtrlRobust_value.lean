-- Prove2me | Definitions.Def_DiffCtrlRobust_value
-- name    : DiffCtrlRobust_value
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:10.756239+00:00
-- url     : https://prove2.me/theorems/42dc33eb-f604-4ec1-8ffc-3997623b4b1b
-- title:
--   The optimal value $V_\alpha(x)$
-- statement:
--   The optimal value of the model $(b,\sigma,c)$ from $x$ is
--
--   $$
--   V_\alpha(x)=\inf_{U\in\mathfrak U}\mathcal J^U_\alpha(x,c),
--   $$
--
--   the infimum of the discounted cost over all admissible controls on the given probability space with the given Wiener process. Applied to $(b_n,\sigma_n,c_n)$ this is $V^n_\alpha$ of (2.18).
--
--   **Formalization Note** The infimum runs over admissible pairs $(U,X)$. Under (A1)–(A3) the set is nonempty, and for a cost bounded by $M$ it is bounded below by $-M/\alpha$.
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, §2.1, pp.6–7, (2.3), and §2.2, p.8, (2.18)

import Definitions.Def_DiffCtrlRobust_IsAdmissibleSolution
import Definitions.Def_DiffCtrlRobust_discCost

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- The optimal value `V_α(x) = inf_{U ∈ 𝔘} 𝒥^U_α(x, c)` of (2.3), and `V^n_α` of (2.18)
(arXiv:2205.05894v2, §2.1, p.6, and §2.2, p.8): the infimum of the discounted cost over all
admissible controls, on the given probability space with the given Brownian motion.

**Formalization Note.** The infimum runs over admissible pairs `(u, X)`, not over all processes. The
set is nonempty under (A1)–(A3), since every stationary Markov solution gives an admissible pair,
and for a cost bounded by `M` it is bounded below by `-M / α`, so `sInf` is a true infimum. -/
noncomputable def value {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {U : Type*} [MeasurableSpace U]
    (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d) (α : ℝ) (b : SDEState d → U → SDEState d)
    (σ : SDEState d → SDEDiffusion d) (c : SDEState d → U → ℝ) (x : SDEState d) : ℝ :=
  sInf {J : ℝ | ∃ (u : ℝ≥0 → Ω → ProbabilityMeasure U) (X : ℝ≥0 → Ω → SDEState d),
    IsAdmissibleSolution P W b σ x u X ∧ J = discCost P α c u X}

end DiffCtrlRobust


