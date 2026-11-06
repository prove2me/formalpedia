-- Prove2me | Definitions.Def_UCalibDirichlet_IsForecaster
-- name    : UCalibDirichlet_IsForecaster
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:54.472627+00:00
-- url     : https://prove2.me/theorems/2b01f487-daac-4577-9d70-aefbf7882fc7
-- title:
--   Valid forecaster: forecasts are random elements of $\Delta_K$
-- statement:
--   A forecaster is **valid** if, for every round and every history of past outcomes, the law of its forecast is a probability measure carried by the simplex $\Delta_K=\{p\in\mathbb R^K_{\ge0}:\|p\|_1=1\}$.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), §1, p.1

import Mathlib
import Definitions.Def_UCalibDirichlet_Forecaster

open MeasureTheory

namespace UCalibDirichlet

/-- **Validity of a forecaster: each forecast is a random element of `Δ_K`.** Frongillo, Luo,
Mehta & Schneider (manuscript, STOC 2027 submission), §1, p.1: the forecaster "(randomly)
announces a distribution `P_t ∈ Δ_K = {p ∈ ℝ^K_+ : ‖p‖₁ = 1}`".

`IsForecaster σ` says that for every round and history, `σ t h` is a probability measure giving
measure zero to the complement of the simplex `Δ_K = stdSimplex ℝ (Fin K)`. -/
def IsForecaster {K : ℕ} (σ : Forecaster K) : Prop :=
  ∀ t (h : Fin t → Fin K), IsProbabilityMeasure (σ t h) ∧ σ t h (stdSimplex ℝ (Fin K))ᶜ = 0

end UCalibDirichlet


