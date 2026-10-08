-- Prove2me | Definitions.Def_AsympCalib_Main_Setting
-- name    : AsympCalib_Main_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:03:59.893678+00:00
-- url     : https://prove2.me/theorems/5292e9b9-31ab-4ed7-b622-d477d735c397
-- title:
--   §§2, 5–6 — grid, weighted calibration, regret potential and adapted forecaster
-- statement:
--   The forecaster uses the grid $G_k=\{i/k:0\le i\le k\}$ of possible rain probabilities. A grid point $p$ is represented as the binary probability vector $(1-p,p)$, and its Brier loss against outcome $X_s\in\{0,1\}$ is $(X_s-p)^2$. For a weight vector $\mu_s$ on the grid, define
--
--   $$
--   \widetilde n_t(i/k)=\sum_{s<t}\mu_s^i,\quad
--   \widetilde\rho_t(i/k)=\frac{\sum_{s<t}\mu_s^iX_s}{\widetilde n_t(i/k)},\quad
--   \widetilde C_t=\sum_{i=0}^k\frac{\widetilde n_t(i/k)}t(\widetilde\rho_t(i/k)-i/k)^2.
--   $$
--
--   For each ordered pair $(i,j)$, $R_t^{i\to j}$ is the nonnegative part of the weighted Brier-loss improvement from replacing $i/k$ by $j/k$. The potential is $\widetilde R_t^\delta=\sum_{i,j}g_\delta(R_t^{i\to j})$, where $g_\delta(x)=\delta x^2/2$ for $x\ge0$ and $0$ for $x<0$. The conservation condition balances the regret flows into and out of every grid point.
--
--   A forecasting rule $\sigma$ maps each finite history of realised forecasts and binary outcomes to a probability distribution on the grid. Its induced forecast is a distribution on the vectors $(1-i/k,i/k)$. Along a history, round $s$ uses $\sigma$ applied to the prefix before that round; the outcome is the history's binary outcome.
--
--   These objects are the common interface for the paper's algorithm and its calibration and regret estimates.
--
--   **Formalization Note** Rounds are indexed from $0$, so the paper's $R_{t-1}$ in round $t$ is regret over rounds before index $t$. The diagonal regret terms cancel, permitting full sums in condition (2). The grid has $k+1$ points. When $\widetilde n_t=0$, Lean assigns $\widetilde\rho_t=0$; when $t=0$, $\widetilde C_t=0$. Probability distributions are `PMF`s, so each $\sigma(h)$ is normalized. In all theorem applications $k>0$.
-- source:
--   Foster and Vohra, Asymptotic calibration, Biometrika 85 (1998), pp. 380–381, §2; pp. 384–385, §5 (1), (2); pp. 386–387, §6, Table 1 and (5); https://doi.org/10.1093/biomet/85.2.379

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_CalibratedCE_Forecast_HistLaw
import Definitions.Def_CalibratedCE_Forecast_Regret
import Definitions.Def_CalibratedCE_Forecast_CalibScoreH

noncomputable section

namespace AsympCalib.Main

def gridPt (k : ℕ) (i : Fin (k + 1)) : ℝ := (i : ℝ) / (k : ℝ)

def gridVec (k : ℕ) (i : Fin (k + 1)) : Fin 2 → ℝ :=
  ![1 - gridPt k i, gridPt k i]

def brierLoss (k : ℕ) (X : ℕ → ℝ) (s : ℕ) (i : Fin (k + 1)) : ℝ :=
  (X s - gridPt k i) ^ 2

def nTilde (k : ℕ) (μ : ℕ → Fin (k + 1) → ℝ) (t : ℕ)
    (i : Fin (k + 1)) : ℝ :=
  ∑ s ∈ Finset.range t, μ s i

def rhoTilde (k : ℕ) (X : ℕ → ℝ) (μ : ℕ → Fin (k + 1) → ℝ)
    (t : ℕ) (i : Fin (k + 1)) : ℝ :=
  (∑ s ∈ Finset.range t, μ s i * X s) / nTilde k μ t i

def CTilde (k : ℕ) (X : ℕ → ℝ) (μ : ℕ → Fin (k + 1) → ℝ)
    (t : ℕ) : ℝ :=
  ∑ i : Fin (k + 1),
    nTilde k μ t i / (t : ℝ) * (rhoTilde k X μ t i - gridPt k i) ^ 2

def gδ (δ x : ℝ) : ℝ := if 0 ≤ x then δ / 2 * x ^ 2 else 0

def RTilde (k : ℕ) (X : ℕ → ℝ) (μ : ℕ → Fin (k + 1) → ℝ)
    (δ : ℝ) (t : ℕ) : ℝ :=
  ∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
    gδ δ (CalibratedCE.Forecast.Rg (brierLoss k X) μ t i j)

def Conservation (k : ℕ) (X : ℕ → ℝ) (μ : ℕ → Fin (k + 1) → ℝ)
    (s : ℕ) : Prop :=
  ∀ i : Fin (k + 1),
    μ s i * (∑ j : Fin (k + 1),
      CalibratedCE.Forecast.Rg (brierLoss k X) μ s i j) =
    ∑ j : Fin (k + 1),
      μ s j * CalibratedCE.Forecast.Rg (brierLoss k X) μ s j i

abbrev History := List ((Fin 2 → ℝ) × Fin 2)

def outcomeR (h : History) (s : ℕ) : ℝ :=
  if (h.getD s default).2 = 1 then 1 else 0

noncomputable def muH {k : ℕ} (σ : History → PMF (Fin (k + 1)))
    (h : History) (s : ℕ) (i : Fin (k + 1)) : ℝ :=
  (σ (h.take s) i).toReal

def forecaster (k : ℕ) (σ : History → PMF (Fin (k + 1)))
    (h : History) : PMF (Fin 2 → ℝ) :=
  (σ h).map (gridVec k)

noncomputable def CTildeH (k : ℕ) (σ : History → PMF (Fin (k + 1)))
    (h : History) : ℝ :=
  CTilde k (outcomeR h) (muH σ h) h.length

def IsConservationForecaster (k : ℕ) (σ : History → PMF (Fin (k + 1))) : Prop :=
  ∀ h : History, ∀ i : Fin (k + 1),
    (σ h i).toReal * (∑ j : Fin (k + 1),
      CalibratedCE.Forecast.Rg (brierLoss k (outcomeR h))
        (muH σ h) h.length i j) =
    ∑ j : Fin (k + 1),
      (σ h j).toReal *
        CalibratedCE.Forecast.Rg (brierLoss k (outcomeR h))
          (muH σ h) h.length j i

end AsympCalib.Main


