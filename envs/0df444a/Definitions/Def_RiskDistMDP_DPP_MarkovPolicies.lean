-- Prove2me | Definitions.Def_RiskDistMDP_DPP_MarkovPolicies
-- name    : RiskDistMDP_DPP_MarkovPolicies
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:29.484319+00:00
-- url     : https://prove2.me/theorems/69fa3eb6-e6ca-439e-9fd9-d4dd6835653e
-- title:
--   Admissible randomized actions $\varpi_t(x)$ and Markovian policies $\Pi$
-- statement:
--   Let $\Lambda$ be the probability measures on $\mathbb A$. For $t\in\mathbb N$ and $x\in\mathbb X$, the **admissible randomized actions** are
--   $$\varpi_t(x):=\{\lambda\in\Lambda:\lambda(\mathcal A_t(x))=1\}.$$
--   A **Markovian policy** is a sequence $\mathfrak p=(\pi_t)_{t\in\mathbb N}$ of measurable maps $\pi_t:(\mathbb X,\mathcal B(\mathbb X))\to(\Lambda,\mathcal E(\Lambda))$ with $\pi_t(x)\in\varpi_t(x)$ for all $x$; $\Pi$ is the set of them. Optimal policies of the paper are chosen from $\Pi$.
--
--   **Formalization Note** $\mathcal E(\Lambda)$ is Mathlib's σ-algebra on `ProbabilityMeasure 𝔸`, the evaluation (Giry) σ-algebra. The module defines `varpi` and `MarkovPolicies`.
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, §2, p. 5

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_BorelMDP

set_option autoImplicit false

open MeasureTheory

namespace RiskDistMDP.DPP

/-- The admissible randomized actions `ϖ_t(x)` (arXiv:2203.09612v4, §2, p.5): the probability
measures `λ` on `ℬ(𝔸)` with `λ(𝒜_t(x)) = 1`. -/
def varpi {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] (M : BorelMDP 𝕏 𝔸) (t : ℕ)
    (x : 𝕏) : Set (ProbabilityMeasure 𝔸) :=
  {l | (l : Measure 𝔸) (M.adm t x) = 1}

/-- The **Markovian policies** `Π` (arXiv:2203.09612v4, §2, p.5): sequences `𝔭 = (π_t)_{t∈ℕ}` with
`π_t : (𝕏, ℬ(𝕏)) → (Λ, ℰ(Λ))` measurable and `π_t(x) ∈ ϖ_t(x)` for every `x`, where
`Λ = ProbabilityMeasure 𝔸`.

**Formalization Note** `ℰ(Λ)` is Mathlib's σ-algebra on `ProbabilityMeasure 𝔸` (the Giry,
evaluation σ-algebra). Only `t ≥ 1` is constrained; `𝔭 0` is unused. -/
def MarkovPolicies {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] (M : BorelMDP 𝕏 𝔸) :
    Set (ℕ → 𝕏 → ProbabilityMeasure 𝔸) :=
  {𝔭 | ∀ t, 1 ≤ t → Measurable (𝔭 t) ∧ ∀ x, 𝔭 t x ∈ varpi M t x}

end RiskDistMDP.DPP


