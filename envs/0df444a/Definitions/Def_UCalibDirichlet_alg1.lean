-- Prove2me | Definitions.Def_UCalibDirichlet_alg1
-- name    : UCalibDirichlet_alg1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:16.132924+00:00
-- url     : https://prove2.me/theorems/bc855c11-75dc-48d7-8d9d-f9d4f910611f
-- title:
--   Algorithm 1: Laplace-smoothed Dirichlet forecaster
-- statement:
--   Algorithm 1 starts from $a_1=\mathbf 1\in\mathbb R^K$; in round $t$ it draws its forecast $P_t\sim\mathrm{Dir}(a_t)$, observes $i_t$ and sets $a_{t+1}=a_t+e_{i_t}$. Equivalently $a_t=N_{t-1}+\mathbf 1$: the label counts so far plus one hallucinated observation of each label (Laplace smoothing). The algorithm does not depend on the loss.
--
--   **Formalization Note** All Dirichlet parameters are at least $1$, so the forecast law is the standard Dirichlet distribution on the simplex.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Algorithm 1, p.3

import Mathlib
import Definitions.Def_UCalibDirichlet_dir
import Definitions.Def_UCalibDirichlet_Forecaster
import Definitions.Def_UCalibDirichlet_counts

namespace UCalibDirichlet

/-- **Algorithm 1 (Laplace-smoothed Dirichlet forecaster).** Frongillo, Luo, Mehta & Schneider
(manuscript, STOC 2027 submission), Algorithm 1, p.3: "Initialize: `a_1 = 𝟏 ∈ ℝ^K`. for
`t = 1, …, T` do Draw `P_t ∼ Dir(a_t)` as the prediction for round `t`. Observe `i_t ∈ [K]` and set
`a_{t+1} = a_t + e_{i_t}`." So `a_t = N_{t−1} + 𝟏` (p.3).

`alg1 t h = Dir(𝟏 + N(h))`, where `N(h)` are the label counts of the history `h` of past outcomes.

**Formalization Note.** All Dirichlet parameters are at least `1`, so `dir` is the standard
Dirichlet law. The forecasts are drawn afresh each round given the past outcomes, which is all
the expected regret against a fixed sequence depends on (`Forecaster`). -/
noncomputable def alg1 {K : ℕ} : Forecaster K :=
  fun _ h => dir (fun j => 1 + (counts h j : ℝ))

end UCalibDirichlet


