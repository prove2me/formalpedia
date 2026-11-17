-- Prove2me | Definitions.Def_PhysReaudit_Supplement_risk
-- name    : PhysReaudit_Supplement_risk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:25:08.283189+00:00
-- url     : https://prove2.me/theorems/566fe124-d0c5-45d1-a52c-de392a501f35
-- title:
--   Coherent reusable estimators and the weighted risk $\mathbb E_\theta L_A(\hat\theta,\theta)$ (App. D.1, (9))
-- statement:
--   This file defines estimators and their risk in the query model of Appendix D.1.
--
--   1. A **coherent reusable estimator** outputs one vector $\hat\theta\in\mathbb R^d$ computed from the complete stopped transcript: the randomization $u$, the queried coordinates and the observed values. It is measurable in $u$ and the observed values for each fixed sequence of queried coordinates.
--   2. The **outcome law**: $u\sim\rho$, independent of an i.i.d. $N(0,1)$ noise stream.
--   3. For $A=\operatorname{diag}(a_1,\dots,a_d)$ the **weighted squared loss** is
--   $$
--   L_A(\hat\theta,\theta)=\|A(\hat\theta-\theta)\|_2^2=\sum_{i=1}^d a_i^2(\hat\theta_i-\theta_i)^2 ,
--   $$
--   which by display (9) equals $\sup_{v\in V_A}|\langle v,\hat\theta-\theta\rangle|^2$ with $V_A=\{Au:\|u\|_2\le1\}$.
--   4. The **risk** $\mathbb E_\theta L_A(\hat\theta,\theta)$ of an estimator after a strategy at parameter $\theta$, valued in $[0,\infty]$.
--
--   **Formalization Note** The risk is a lower Lebesgue integral in $[0,\infty]$, so an estimator with infinite risk is allowed.
-- source:
--   Q. Li, When Can Physical Evidence Survive a World-Model Update? Finite-cost re-auditing and reusable policy certificates, review revision of 3 November 2026 (STOC 2027 submission, sha256 a20c437b34115b84982339e9a6fa319cb3a66f66d9d4c474465cbb954c79093d), App. D.1, p.21 (PDF p.22), display (9): "A coherent reusable estimator outputs one vector θ̂ and answers v by ⟨v, θ̂⟩. Its squared uniform loss is LA(θ̂, θ) = sup_{v∈VA} |⟨v, θ̂ − θ⟩|² = ‖A(θ̂ − θ)‖₂²"; App. D.3, p.23 (PDF p.24), display (14)

import Mathlib
import Definitions.Def_PhysReaudit_Supplement_Strategy

open MeasureTheory ProbabilityTheory

namespace PhysReaudit.Supplement

/-- A coherent reusable estimator (Q. Li, *When Can Physical Evidence Survive a World-Model Update?*,
review revision of 3 November 2026 (sha256 a20c437b…), App. D.1, p.21 (PDF p.22): "A coherent reusable
estimator outputs one vector θ̂"): a map from the complete stopped transcript (the randomization `u` and
the history of queried coordinates and observed values) to one vector `θ̂ ∈ ℝ^d`.

**Formalization Note** Measurability is required in `(u, observed values)` for each fixed list of queried
coordinates. -/
structure Estimator (d : ℕ) (U : Type) [MeasurableSpace U] where
  /-- The estimate `θ̂` computed from the randomization and the final history. -/
  est : U → List (Fin d × ℝ) → (Fin d → ℝ)
  /-- Measurability in the randomization and the observed values, for each list of queried coordinates. -/
  measurable_est : ∀ cs : List (Fin d),
    Measurable fun p : U × (Fin cs.length → ℝ) => est p.1 (mkHist cs p.2)

/-- The law of the outcome `(u, Z)`: the randomization `u ∼ ρ`, independent of an i.i.d. `N(0, 1)` noise
stream `Z` (App. D.1, display (8): "Z ∼ N(0, 1)… Noise variables are independent"). -/
noncomputable def noiseLaw {U : Type} [MeasurableSpace U] (ρ : Measure U) : Measure (U × (ℕ → ℝ)) :=
  ρ.prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)

/-- The weighted squared uniform loss `L_A(θ̂, θ) = ‖A(θ̂ − θ)‖₂² = Σ_i a_i² (θ̂_i − θ_i)²` with
`A = diag(a_1, …, a_d)` (App. D.1, p.21 (PDF p.22), display (9)). -/
noncomputable def lossA {d : ℕ} (a θhat θ : Fin d → ℝ) : ℝ :=
  ∑ i, a i ^ 2 * (θhat i - θ i) ^ 2

/-- The risk `E_θ L_A(θ̂, θ)` of the estimator `E` after the strategy `S` at parameter `θ`, with
randomization law `ρ` (App. D.3, p.23 (PDF p.24), display (14)), in `ℝ≥0∞`. -/
noncomputable def risk {d : ℕ} {U : Type} [MeasurableSpace U] (ρ : Measure U) (S : Strategy d U)
    (E : Estimator d U) (a θ : Fin d → ℝ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (lossA a (E.est ω.1 (finalHist S θ ω)) θ) ∂(noiseLaw ρ)

end PhysReaudit.Supplement


