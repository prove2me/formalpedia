-- Prove2me | Definitions.Def_NashAmplification_Filtering_Errors
-- name    : NashAmplification_Filtering_Errors
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:26:30.747896+00:00
-- url     : https://prove2.me/theorems/f6d17331-b927-494e-9f5e-f7d185943d1f
-- title:
--   Score and weight errors and the explicit deviation constant
-- statement:
--   Compare the empirical calculation on $Y$ with recovery on the original $\sigma$. For source round $s$, define
--   $$e_s^W=C^{-1}\sum_j|\widehat W_s(Y_j)-W_s(Y_j)|,\quad e_s^V=C^{-1}\sum_j|V_{\widehat Q_s}(Y_{j,s})-V_{Q_s}(Y_{j,s})|,$$
--   and $e_s^*=|V_{\widehat Q_s}(a_s^*)-V_{Q_s}(a_s^*)|$. Put $\Gamma_k=3k^2$, $E_0^W=0$, $m_s=q^{s-1}$, and define
--   $$E_s^V=\frac{(k-1)E_{s-1}^W+\Gamma_k}{m_s^{k-1}},\qquad E_s^W=2E_{s-1}^W+2E_s^V/h+2.$$
--   Finally set
--   $$K=\sum_{s=1}^t\left[\frac{4(E_{s-1}^W+2+4E_s^V/\Delta)}{\beta q^{s-1}}+\frac{4E_s^V}{\Delta}\right].$$
--   These finite recurrences make the constants explicit and independent of the game, action counts, profile and number of constructed players.
-- source:
--   Deng, Li, Wang and Zhang, Hardness Amplification for Approximate Nash Equilibrium with a Constant Number of Players, STOC 2027 submission #120 (October 2026), SHA-256 c201a27da9b9920a924945f1a30c7919ae6b922c99430223ee9bbcdec5b0ffa8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/120.pdf, (3.7)–(3.9), (3.13), (3.27), PDF pp. 16, 18, 22 (printed pp. 15, 17, 21)

import Definitions.Def_NashAmplification_Filtering_Process

open scoped BigOperators
noncomputable section

namespace NashAmplification.Filtering

def errorW {k C t : ℕ} {n : Fin k → ℕ} (u : Utility n) (β Δ : ℝ)
    (σ : Fin C → Seq n t → ℝ) (s : ℕ) (y : Fin C → Seq n t) : ℝ :=
  (∑ j, |weights u (1-β/2) (Δ/4) (empirical y) s (y j) -
          weights u (1-β/2) (Δ/4) (mixture σ) s (y j)|) / C

def errorV {k C t : ℕ} {n : Fin k → ℕ} (u : Utility n) (β Δ : ℝ)
    (σ : Fin C → Seq n t → ℝ) (r : Fin t) (y : Fin C → Seq n t) : ℝ :=
  (∑ j, |score u (roundLaw u (1-β/2) (Δ/4) (empirical y) r) (y j r) -
          score u (roundLaw u (1-β/2) (Δ/4) (mixture σ) r) (y j r)|) / C

def errorStar {k C t : ℕ} {n : Fin k → ℕ} (hn : ∀ r, 0 < n r)
    (u : Utility n) (β Δ : ℝ) (σ : Fin C → Seq n t → ℝ)
    (r : Fin t) (y : Fin C → Seq n t) : ℝ :=
  |score u (roundLaw u (1-β/2) (Δ/4) (empirical y) r) (zStar hn u β Δ σ r) -
   score u (roundLaw u (1-β/2) (Δ/4) (mixture σ) r) (zStar hn u β Δ σ r)|

/-- (3.13): pair (E^V_s, E^W_s), s is one-based except the initial pair. -/
def coefficients (k : ℕ) (β Δ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | s+1 =>
    let prev := (coefficients k β Δ s).2
    let v := (((k-1 : ℕ) : ℝ) * prev + 3 * (k : ℝ)^2) /
      ((1-β/2)^s)^ (k-1)
    (v, 2 * prev + 2 * v / (Δ/4) + 2)

/-- Exact coefficient (3.27), independent of G, A, C and σ. -/
def deviationK (k t : ℕ) (β Δ : ℝ) : ℝ :=
  ∑ r : Fin t, (4 * ((coefficients k β Δ r.val).2 + 2 +
      4 * (coefficients k β Δ (r.val+1)).1 / Δ) / (β * (1-β/2)^r.val) +
      4 * (coefficients k β Δ (r.val+1)).1 / Δ)
end NashAmplification.Filtering


