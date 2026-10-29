-- Prove2me | Definitions.Def_PeskirShiryaev_UltimateMaximum_predictionModel
-- name    : PeskirShiryaev_UltimateMaximum_predictionModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:27:15.015672+00:00
-- url     : https://prove2.me/theorems/e8096659-4ec0-4a64-986a-3a8853731cc0
-- title:
--   Natural-filtration prediction loss and drawdown stopping rule
-- statement:
--   For a real process $B$ indexed by nonnegative time, let $\mathcal F_t^B=\sigma(B_s:0\le s\le t)$ and $S_t=\sup_{0\le s\le t}B_s$. A time $\tau:\Omega\to[0,\infty)$ is admissible when $\{\tau\le t\}\in\mathcal F_t^B$ for every $t\ge0$ and $\tau\le1$ everywhere. For a measure $P$, define
--   $$L(\tau)=(B_\tau-S_1)^2,\qquad V_* =\inf_{\tau\text{ admissible}}\mathbb E_P L(\tau).$$
--   The expectation in this definition is the nonnegative extended integral. The candidate rule is
--   $$\tau_*=\inf\{t\in[0,1]:S_t-B_t\ge z_*\sqrt{1-t}\}.$$
--   For $t<1$ define $H_t=2[1-\Phi((S_t-B_t)/\sqrt{1-t})]$, and set $H_t=0$ for $t\ge1$. Finally put $A(\tau)=\int_0^\tau(1-2H_t)\,dt$. These are the actual prediction objective, the observable drawdown rule, and the adapted running-cost expression; no optimality is built into them.
--
--   **Formalization Note** The functions are defined on arbitrary inputs, but the theorems require a measurable Brownian motion with continuous paths. Under those hypotheses each running supremum is finite and its set is nonempty; time $1$ belongs to the hitting set. The admissible class contains the constant zero time. $V_*$ lies in $[0,\infty]$, while $L$ and $A$ are real-valued. The arbitrary endpoint convention $H_1=0$ does not change a time integral. Only the restriction of the process to $[0,1]$ is used.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, p. 441 (PDF p. 457), Eqs. (30.1.1)–(30.1.2); p. 442 / PDF 458, Eqs. (30.1.6), (30.1.8), (30.1.10)

import Mathlib
import Definitions.Def_PeskirShiryaev_UltimateMaximum_gaussianBoundary

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace PeskirShiryaev.UltimateMaximum

@[instance_reducible]
noncomputable def past {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ (s : ℝ≥0) (_ : s ≤ t), MeasurableSpace.comap (B s) inferInstance

def Admissible {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) : Prop :=
  (∀ t : ℝ≥0, MeasurableSet[past B t] {ω | τ ω ≤ t}) ∧ (∀ ω, τ ω ≤ 1)

noncomputable def maximum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  sSup {x : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ B s ω = x}

noncomputable def squaredError {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (ω : Ω) : ℝ := (B (τ ω) ω - maximum B 1 ω) ^ 2

noncomputable def predictionValue {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  ⨅ τ : {τ : Ω → ℝ≥0 // Admissible B τ},
    ∫⁻ ω, ENNReal.ofReal (squaredError B τ.val ω) ∂P

noncomputable def optimalTime {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 :=
  sInf {t : ℝ≥0 | t ≤ 1 ∧
    maximum B t ω - B t ω ≥ criticalLevel * Real.sqrt (1 - (t : ℝ))}

noncomputable def clarkIntegrand {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  if t < 1 then 2 * (1 - Phi ((maximum B t ω - B t ω) / Real.sqrt (1 - (t : ℝ))))
  else 0

noncomputable def accumulatedCost {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (ω : Ω) : ℝ :=
  ∫ t in (0 : ℝ)..(τ ω : ℝ), 1 - 2 * clarkIntegrand B t.toNNReal ω

end PeskirShiryaev.UltimateMaximum

/- Imported definition bodies (verbatim code, for standalone inspection):

namespace PeskirShiryaev.UltimateMaximum

noncomputable def phi (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi)

noncomputable def Phi (x : ℝ) : ℝ := ∫ y in Iic x, phi y

noncomputable def runningCost (x : ℝ) : ℝ := 4 * Phi x - 3

noncomputable def rootEquation (z : ℝ) : ℝ := 4 * Phi z - 2 * z * phi z - 3

noncomputable def criticalLevel : ℝ := sInf {z : ℝ | 0 ≤ z ∧ rootEquation z = 0}

noncomputable def candidate (z : ℝ) : ℝ :=
  if |z| ≤ criticalLevel then
    Phi criticalLevel * (1 + z ^ 2) - |z| * phi |z| +
      (1 - z ^ 2) * Phi |z| - 3 / 2
  else 0

end PeskirShiryaev.UltimateMaximum
-/


