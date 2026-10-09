-- Prove2me | Definitions.Def_MHSpectralGap_GlobalLip_Assumptions
-- name    : MHSpectralGap_GlobalLip_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:05:57.822822+00:00
-- url     : https://prove2.me/theorems/7d79b80f-4ed4-41e5-98ce-5f08f916578d
-- title:
--   Assumptions 2.10–2.11 and (3.2): acceptance, global Lipschitz and distance
-- statement:
--   Assumption 2.10 requires a positive radius function $r$, a threshold $R>0$, and an acceptance lower bound outside the ball of radius $R$: on the ball of radius $r(\|x\|)$ around $(1-\rho)x$, acceptance is uniformly bounded below by a positive constant. Assumption 2.11 requires $\Phi$ globally Lipschitz and $e^{-\Phi}$ integrable under $\gamma$. The distance in (3.2) is
--
--   $$d_\varepsilon(x,y)=1\wedge\frac{\|x-y\|}{\varepsilon}.$$
--
--   The file also records the two allowed regimes of Theorem 2.12: $r(s)=r_0s^a$ with $a\in(1/2,1)$ and either a positive power or positive exponential Lyapunov function, or constant $r_0>0$ with a positive power Lyapunov function.
--
--   **Formalization Note** The pointwise acceptance lower bound is equivalent to the paper's strict infimum bound because the lower bound constant is existential. The radius function is represented on the nonnegative arguments used by the chain. The power exponent is a natural number at least one; the exponential coefficient is positive.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, pp. 12 and 18, Assumptions 2.10–2.11, Theorem 2.12 and (3.2)

import Mathlib
import Definitions.Def_MHSpectralGap_GlobalLip_PCN

namespace MHSpectralGap.GlobalLip

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Assumption 2.10, expressed using the actual pCN acceptance probability. -/
def Assumption210 {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Φ : H → ℝ) (δ : ℝ) (r : ℝ → ℝ) : Prop :=
  (∀ s, 0 ≤ r s) ∧
  ∃ R : ℝ, 0 < R ∧ ∃ αl : ℝ,
    (∀ s, R ≤ |s| → r s ≤ rho δ / 2 * |s|) ∧
    ∀ x : H, R ≤ ‖x‖ →
      ∀ z ∈ Metric.ball ((1 - rho δ) • x) (r ‖x‖),
        Real.exp αl < min 1 (Real.exp (Φ x - Φ z))

/-- Assumption 2.11. -/
def Assumption211 {H : Type} [PseudoMetricSpace H] [MeasurableSpace H]
    (Φ : H → ℝ) (γ : Measure H) (L : ℝ≥0) : Prop :=
  LipschitzWith L Φ ∧ Integrable (fun x => Real.exp (-Φ x)) γ

/-- The cost (3.2). -/
noncomputable def dEps {H : Type} [NormedAddCommGroup H] (ε : ℝ)
    (x y : H) : ℝ := min 1 (‖x - y‖ / ε)

/-- The two cases and Lyapunov functions of Theorem 2.12. -/
def Theorem212Case {H : Type} [NormedAddCommGroup H]
    (r : ℝ → ℝ) (V : H → ℝ) : Prop :=
  (∃ r₀ : ℝ, 0 < r₀ ∧ ∃ a : ℝ, a ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧
      (∀ s, 0 ≤ s → r s = r₀ * s ^ a) ∧
      ((∃ i : ℕ, 1 ≤ i ∧ V = fun x => ‖x‖ ^ i) ∨
       (∃ v : ℝ, 0 < v ∧ V = fun x => Real.exp (v * ‖x‖)))) ∨
  (∃ r₀ : ℝ, 0 < r₀ ∧ (∀ s, 0 ≤ s → r s = r₀) ∧
      ∃ i : ℕ, 1 ≤ i ∧ V = fun x => ‖x‖ ^ i)

end MHSpectralGap.GlobalLip


