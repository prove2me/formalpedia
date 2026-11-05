-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_mvValue
-- name    : BauerleRiederMDP_PartialObs_mvValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:04:27.477216+00:00
-- url     : https://prove2.me/theorems/d16f7354-7670-4bc7-bf30-222009a6e7fd
-- title:
--   The value of the mean-variance problem (MV)
-- statement:
--   The mean–variance problem with partial observation is
--   $$
--   (MV)\qquad \operatorname{Var}^\pi_{x_0}(X_N)\to\min,\qquad \mathbb E^\pi_{x_0}[X_N]\ge\mu,\qquad \pi\in\Pi_N,
--   $$
--   over the history-dependent policies $\Pi_N$. Its value is the infimum of $\operatorname{Var}(X_N)=\mathbb E\big(X_N-\mathbb E X_N\big)^2$ over the admissible strategies, computed under the market law with $Y_0\sim Q_0$.
--
--   **Formalization Note** Extended-real infimum, so an empty admissible set gives $+\infty$.
-- source:
--   Bäuerle & Rieder (2011), §6.2, problem (MV), p.184 (PDF 197)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_mvAdmissible

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **The value of the mean-variance problem (MV) with partial observation.**
Bäuerle & Rieder (2011), §6.2, p.184 (PDF 197):
`Var^π_{x_0}(X_N) → min`, `IE^π_{x_0}[X_N] ≥ μ`, `π ∈ Π_N`.

`mvValue M i N x0 μ` is the infimum, over the admissible strategies (`mvAdmissible`), of
`Var(X_N) = ∫ (X_N − IE X_N)² dP` under the market law `P = M.returnLaw M.Q0 N`.

**Formalization Note.** In `EReal`, so the infimum over an empty set is `+∞` (no junk value). -/
noncomputable def mvValue {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d)
    (i : ℕ → ℝ) (N : ℕ) (x0 μ : ℝ) : EReal :=
  ⨅ φ ∈ {φ : (n : ℕ) → (Fin n → Fin d → ℝ) → Fin d → ℝ | mvAdmissible M i N x0 μ φ},
    ((∫ r, (wealth i x0 φ N r - ∫ r', wealth i x0 φ N r' ∂M.returnLaw M.Q0 N) ^ 2
      ∂M.returnLaw M.Q0 N : ℝ) : EReal)

end BauerleRiederMDP.PartialObs


