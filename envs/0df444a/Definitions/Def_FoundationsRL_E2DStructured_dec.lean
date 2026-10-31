-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_dec
-- name    : FoundationsRL_E2DStructured_dec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:24:20.040965+00:00
-- url     : https://prove2.me/theorems/d84d9822-be87-4b9b-b14b-0068a7a2c82d
-- title:
--   The Decision-Estimation Coefficient $\mathrm{dec}_\gamma(\mathcal F,\hat f)$
-- statement:
--   The **Decision-Estimation Coefficient** of a class $\mathcal F$ at a reference model $\hat f$ is
--   $$\mathrm{dec}_\gamma(\mathcal F,\hat f)=\inf_{p\in\Delta(\Pi)}\sup_{f\in\mathcal F}\mathbb E_{\pi\sim p}\big[f(\pi_f)-f(\pi)-\gamma\,(f(\pi)-\hat f(\pi))^2\big].$$
--   It is the value of a game in which the learner picks a distribution over decisions and an adversary picks a problem instance, and it measures the trade-off between regret and information.
--
--   **Formalization Note** The notes print $\min$ and $\max$; they are read as $\inf$ and $\sup$, as in (4.19), since they need not be attained. The value lies in the extended reals.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.2, (4.15), p. 65

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_decGame

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- The Decision-Estimation Coefficient at a reference model,
`dec_γ(F, f̂) = inf_{p∈Δ(Π)} sup_{f∈F} E_{π∼p}[f(π_f) − f(π) − γ·(f(π) − f̂(π))²]`
(Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.2, p. 65, (4.15)).

**Formalization Note.** `min`/`max` are read `inf`/`sup`, as in (4.19): they need not be attained.
`Δ(Π)` is `ProbabilityMeasure D`. For `γ = 0` the reference model plays no role, since
`0 * ⊤ = 0` in `EReal`. -/
noncomputable def dec {D : Type*} [MeasurableSpace D] (γ : ℝ) (F : Set (D → ℝ))
    (fhat : D → ℝ) : EReal :=
  ⨅ p : ProbabilityMeasure D, decGame γ F fhat p

end FoundationsRL.E2DStructured


