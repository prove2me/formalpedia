-- Prove2me | Definitions.Def_UCalibDirichlet_VF
-- name    : UCalibDirichlet_VF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:06.981387+00:00
-- url     : https://prove2.me/theorems/c83067c7-0903-4d2a-a581-147d169ee460
-- title:
--   Smoothing penalty $V_F(T)$
-- statement:
--   For $F:\Delta_K\to\mathbb R$ and a horizon $T$,
--   $$V_F(T)=T\sup_{p\in\Delta_K}\Big\{F(p)-F\Big(\frac{Tp+\mathbf 1}{T+K}\Big)\Big\},$$
--   where $\mathbf 1$ is the all-ones vector. The point $(Tp+\mathbf 1)/(T+K)$ is the empirical distribution $p$ smoothed by one hallucinated observation of each label, as in Algorithm 1; $V_F(T)$ measures the cost of this Laplace smoothing in the BTPL regret (Lemma 1.5).
--
--   **Formalization Note** The supremum is the real supremum over the simplex; for a convex finite $F$ on $\Delta_K$ the family is bounded, so it is not a default value.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Lemma 1.5, display (9), p.4

import Mathlib

namespace UCalibDirichlet

/-- **The smoothing penalty `V_F(T)`, display (9).** Frongillo, Luo, Mehta & Schneider (manuscript,
STOC 2027 submission), Lemma 1.5, p.4:
"`V_F(T) = T sup_{p∈Δ_K} { F(p) − F((Tp + 1)/(T + K)) }`. (9)"

`VF F T = T · sup_{p ∈ Δ_K} (F(p) − F((T p + 𝟏)/(T + K)))`, the vector `(Tp + 𝟏)/(T + K)` taken
coordinatewise (`𝟏` the all-ones vector).

**Formalization Note.** The supremum is the real `⨆` over the subtype `stdSimplex ℝ (Fin K)`. For
`p ∈ Δ_K` the point `(Tp + 𝟏)/(T + K)` lies in `Δ_K`, so only values of `F` on the simplex enter.
For a finite convex `F` on `Δ_K` the family is bounded (a convex function on a simplex is bounded
above by its maximum over the vertices and below by an affine minorant), so the supremum is not
a junk value. -/
noncomputable def VF {K : ℕ} (F : (Fin K → ℝ) → ℝ) (T : ℕ) : ℝ :=
  T * ⨆ p : stdSimplex ℝ (Fin K), (F p - F (fun j => ((T : ℝ) * p.1 j + 1) / (T + K)))

end UCalibDirichlet


