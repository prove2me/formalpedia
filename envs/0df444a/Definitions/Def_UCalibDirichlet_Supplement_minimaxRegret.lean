-- Prove2me | Definitions.Def_UCalibDirichlet_Supplement_minimaxRegret
-- name    : UCalibDirichlet_Supplement_minimaxRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:10:54.167839+00:00
-- url     : https://prove2.me/theorems/16d23653-6fa1-482a-a295-afd6df09a9fc
-- title:
--   Minimax regret $R^*_F(T)$
-- statement:
--   For a loss $\ell$ on $\Delta_K\times[K]$ and a horizon $T$, the **minimax regret** is
--   $$R^*_\ell(T)=\inf_{\sigma}\ \sup_{i_1,\dots,i_T\in[K]}\mathrm{Reg}_\ell(T;\,\sigma,\,i_{1:T}),$$
--   the infimum over (randomized) forecasters $\sigma$ of the largest expected regret (display (2)) over outcome sequences. A forecaster announces, in each round, a forecast drawn from a probability law on $\Delta_K$ that may depend on the past outcomes.
--
--   The paper's lower bounds (Theorem 1.8 (iv), Theorems 1.9, 1.14, E.6, E.8) are lower bounds on $R^*$; the upper bounds of Algorithm 1 give upper bounds on it.
--
--   **Formalization Note** Forecasters are the base model's forecasters (a law on $\Delta_K$ per round and history of outcomes). The infimum ranges over forecasters for which the expected losses exist, i.e. each $\ell(\cdot,j)$ is almost-everywhere measurable under each forecast law of the first $T$ rounds, the same admissibility as in Theorem 1.8 (iv). Deterministic forecasters are admissible, so the class is never empty. Infimum and supremum are taken in the extended reals.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), §1.1.3, p.8 (R*_F(T)); App. E.1.1, p.40; Theorem 1.9, p.7

import Mathlib
import Definitions.Def_UCalibDirichlet_Forecaster
import Definitions.Def_UCalibDirichlet_IsForecaster
import Definitions.Def_UCalibDirichlet_regret

open MeasureTheory

namespace UCalibDirichlet.Supplement

/-- **Minimax regret `R*_F(T)`.** Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027
submission), §1.1.3, p.8: "Throughout, we write `R*_F(T)` for the minimax regret"; App. E.1.1, p.40;
Theorem 1.9, p.7 ("the minimax regret for this loss").

`minimaxRegret ℓ T = inf_σ sup_{i_{1:T}} Reg_ℓ(T; σ, i_{1:T})`, the infimum over admissible
(randomized) forecasters `σ` of the worst-case expected regret over outcome sequences of length `T`.

**Formalization Note.** Forecasters are the base `Forecaster` (a forecast law per round and past
outcomes) with `IsForecaster` (probability laws carried by `Δ_K`). As in base Theorem 1.8 (iv), a
forecaster is admissible when each `ℓ(·, j)` is a.e.-measurable under each of its forecast laws in
the first `T` rounds, which is what the expectation `E[ℓ(P_t, i_t)]` in (2) presupposes. Every
deterministic forecaster (Dirac laws on `Δ_K`) is admissible, so the class is nonempty for
`K ≥ 1`. The adversary picks the outcome sequence in advance (p.3); the infimum and supremum are
taken in `EReal`. -/
noncomputable def minimaxRegret {K : ℕ} (ℓ : (Fin K → ℝ) → Fin K → EReal) (T : ℕ) : EReal :=
  ⨅ σ : {σ : Forecaster K // IsForecaster σ ∧
      ∀ t, t < T → ∀ (h : Fin t → Fin K) (j : Fin K), AEMeasurable (fun p => ℓ p j) (σ t h)},
    ⨆ i : Fin T → Fin K, regret ℓ σ.1 i

end UCalibDirichlet.Supplement


