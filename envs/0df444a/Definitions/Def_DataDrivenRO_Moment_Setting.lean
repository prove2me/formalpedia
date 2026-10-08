-- Prove2me | Definitions.Def_DataDrivenRO_Moment_Setting
-- name    : DataDrivenRO_Moment_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T14:03:26.77563+00:00
-- url     : https://prove2.me/theorems/492e8f73-a721-4a4e-80ca-0b6f51eb07dc
-- title:
--   The moment confidence region, its uncertainty set, and value at risk
-- statement:
--   Let $\tilde u\in\mathbb R^d$ have probability law $P$, and let $\|\cdot\|_2$ and $\|\cdot\|_F$ denote the Euclidean and Frobenius norms. Its mean and covariance are $m_P=\mathbb E_P[\tilde u]$ and $S_P=\mathbb E_P[\tilde u\tilde u^\top]-m_Pm_P^\top$. For a radius $R$, estimates $\hat\mu,\hat\Sigma$, and nonnegative thresholds $\Gamma_1,\Gamma_2$, the confidence region is
--
--   $$
--   \mathcal P^{CS}=\{P:\ P\text{ is a probability law carried by }\{u:\|u\|_2\le R\},\ \|m_P-\hat\mu\|_2\le\Gamma_1,\ \|S_P-\hat\Sigma\|_F\le\Gamma_2\}.
--   $$
--
--   Given a matrix $C$ and $0<\varepsilon<1$, the uncertainty set of (35) is
--
--   $$
--   \mathcal U^{CS}_{\varepsilon}=\{\hat\mu+y+C^\top w:\ \|y\|_2\le\Gamma_1,\ \|w\|_2\le\sqrt{1/\varepsilon-1}\}.
--   $$
--
--   The file also names the right side of (34) and defines $\operatorname{VaR}^P_\varepsilon(v)$ as the lower $(1-\varepsilon)$ quantile of $\tilde u^\top v$. These definitions provide the common model for the mission's theorems.
--
--   **Formalization Note** Coordinates are indexed from zero by `Fin d`. The ball support condition makes all coordinates and their products integrable. The thresholds are parameters so either the concentration thresholds of Theorem 9 or bootstrapped thresholds can be supplied. The real support function and Value-at-Risk definitions are imported published objects.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 9 and (33), p. 24; (34)–(35), p. 25

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RobustMDP_Shared_supportFunction

open MeasureTheory

namespace DataDrivenRO.Moment

/-- The Euclidean norm on the coordinate vector used in (34)–(35), not the sup norm
on Lean's function type. -/
noncomputable def enorm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  Real.sqrt (v ⬝ᵥ v)

/-- The Frobenius norm in the definition of the moment confidence region, p. 24. -/
noncomputable def frob {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (A i j) ^ 2)

/-- The mean vector of a probability law on the uncertain vector. -/
noncomputable def mean {d : ℕ} (P : Measure (Fin d → ℝ)) : Fin d → ℝ :=
  fun i => ∫ u, u i ∂P

/-- The covariance in Theorem 9, `E[uuᵀ] - E[u]E[u]ᵀ`. -/
noncomputable def cov {d : ℕ} (P : Measure (Fin d → ℝ)) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => (∫ u, u i * u j ∂P) - mean P i * mean P j

/-- The moment confidence region of Theorem 9, with thresholds supplied by the
sampling procedure. The probability law is carried by the Euclidean ball of radius `R`. -/
noncomputable def PCS {d : ℕ} (R Γ₁ Γ₂ : ℝ) (μhat : Fin d → ℝ)
    (Shat : Matrix (Fin d) (Fin d) ℝ) : Set (Measure (Fin d → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P {u | enorm u ≤ R}ᶜ = 0 ∧
    enorm (mean P - μhat) ≤ Γ₁ ∧ frob (cov P - Shat) ≤ Γ₂}

/-- The uncertainty set (35), with the bootstrapped threshold written as `Γ₁`. -/
noncomputable def UCS {d : ℕ} (μhat : Fin d → ℝ)
    (C : Matrix (Fin d) (Fin d) ℝ) (Γ₁ ε : ℝ) : Set (Fin d → ℝ) :=
  {u | ∃ y w : Fin d → ℝ,
    enorm y ≤ Γ₁ ∧ enorm w ≤ Real.sqrt (1 / ε - 1) ∧
    u = μhat + y + Matrix.mulVec C.transpose w}

/-- The right side of (34), with thresholds treated as parameters. -/
noncomputable def csValue {d : ℕ} (μhat : Fin d → ℝ)
    (Shat : Matrix (Fin d) (Fin d) ℝ) (Γ₁ Γ₂ ε : ℝ) (v : Fin d → ℝ) : ℝ :=
  μhat ⬝ᵥ v + Γ₁ * enorm v +
    Real.sqrt ((1 - ε) / ε) *
      Real.sqrt (v ⬝ᵥ (Matrix.mulVec (Shat + Γ₂ • (1 : Matrix (Fin d) (Fin d) ℝ)) v))

/-- Value at Risk (6) using the published risk functional. -/
noncomputable def VaR {d : ℕ} (P : Measure (Fin d → ℝ)) (ε : ℝ)
    (v : Fin d → ℝ) : ℝ :=
  MultistageStochastic.valueAtRisk P (fun u => u ⬝ᵥ v) (1 - ε)

end DataDrivenRO.Moment


