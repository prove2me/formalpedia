-- Prove2me | Definitions.Def_UCalibDirichlet_regret
-- name    : UCalibDirichlet_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:30.98472+00:00
-- url     : https://prove2.me/theorems/07205803-3654-4b4a-a813-43ef208ee815
-- title:
--   Expected regret $\mathrm{Reg}_\ell(T)$ for a fixed outcome sequence
-- statement:
--   For a loss $\ell$, a forecaster and a fixed outcome sequence $i_1,\dots,i_T$,
--   $$\mathrm{Reg}_\ell(T)=\mathbb E\Big[\sum_{t=1}^T\ell(P_t,i_t)-\inf_{p\in\Delta_K}\sum_{t=1}^T\ell(p,i_t)\Big],$$
--   the expected difference between the forecaster's total loss and that of the best fixed prediction in hindsight; the expectation is over the forecaster's randomness. The forecast $P_t$ of round $t$ has the law the forecaster assigns to the history $i_1,\dots,i_{t-1}$.
--
--   **Formalization Note** Computed in the extended reals with the exact expected loss (the value $+\infty$ is kept). Rounds are indexed from $0$.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), display (2), p.1; p.3; proof of Theorem 1.8, p.14

import Mathlib
import Definitions.Def_UCalibDirichlet_Forecaster
import Definitions.Def_UCalibDirichlet_expLoss

namespace UCalibDirichlet

/-- **Expected regret `Reg_ℓ(T)`, display (2), for a fixed outcome sequence.** Frongillo, Luo,
Mehta & Schneider (manuscript, STOC 2027 submission), §1, p.1: "we define the expected regret of
the forecaster with respect to this loss as
`Reg_ℓ(T) = E[∑_{t=1}^T ℓ(P_t, i_t) − inf_{p∈Δ_K} ∑_{t=1}^T ℓ(p, i_t)]`, (2)"; p.3: "we fix the
outcome sequence so that the expectation in the definition of the regret is only with respect to
the randomness of the algorithm's forecasts `P_1, …, P_T`"; p.14: "`Reg_F(T; i_{1:T})` denotes the
algorithm's expected regret for the fixed, oblivious label sequence `i_{1:T}`".

For an outcome sequence `i : Fin T → Fin K` (round `t` is `t : Fin T`, 0-based), the forecast of
round `t` has law `σ t (i_{<t})`, and
`regret ℓ σ i = ∑_t E_{P∼σ t (i_{<t})}[ℓ(P, i t)] − inf_{p ∈ Δ_K} ∑_t ℓ(p, i t)`.

**Formalization Note.** Computed in `EReal` with `expLoss` (exact for proper losses, including the
value `+∞`). The benchmark is deterministic, so the expectation of the difference is the
difference of the expectations; the infimum is the `EReal` infimum over the subtype `Δ_K`. -/
noncomputable def regret {K T : ℕ} (ℓ : (Fin K → ℝ) → Fin K → EReal) (σ : Forecaster K)
    (i : Fin T → Fin K) : EReal :=
  (∑ t : Fin T, expLoss ℓ (σ t (fun s : Fin t => i (Fin.castLT s (s.isLt.trans t.isLt)))) (i t)) -
    ⨅ p : stdSimplex ℝ (Fin K), ∑ t, ℓ p (i t)

end UCalibDirichlet


