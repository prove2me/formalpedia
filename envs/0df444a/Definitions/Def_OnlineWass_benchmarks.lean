-- Prove2me | Definitions.Def_OnlineWass_benchmarks
-- name    : OnlineWass_benchmarks
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:46.555018+00:00
-- url     : https://prove2.me/theorems/4b3663dd-0886-483a-a64d-a9cda4e3aa65
-- title:
--   The offline value $R^*_T$ and the fluid value $R^{UB}_T$
-- statement:
--   For a profile $\mathcal H=(\theta_1,\dots,\theta_T)$ and a budget $c$, the offline value $R^*_T$ is the optimal value of
--
--   $$
--   \max\ \sum_{t=1}^T f(x_t;\theta_t)\quad\text{s.t.}\quad\sum_{t=1}^T g_i(x_t;\theta_t)\le c_i,\ i=1,\dots,m,\quad x_t\in\mathcal X .
--   $$
--
--   For a law $\mathcal P$, the deterministic upper bound (4) is
--
--   $$
--   R^{UB}_T=\max\ \sum_{t=1}^T\mathcal P_t f(x_t(\theta_t);\theta_t)\quad\text{s.t.}\quad\sum_{t=1}^T\mathcal P_t g_i(x_t(\theta_t);\theta_t)\le c_i,\ i=1,\dots,m,
--   $$
--
--   over measurable $x_t:\Theta\to\mathcal X$. The regret compares the online reward with $R^*_T$.
--
--   **Formalization Note** Both are real suprema. For $c\ge0$ the sets are nonempty, since $x\equiv0$ is feasible, and bounded by $T$ under Assumption 1 (a).
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, (PCP), p.8; R*_T, p.11; (4), p.13

import Mathlib
import Definitions.Def_OnlineWass_Model

open MeasureTheory

namespace OnlineWass

variable {k m T : ℕ} {Θ : Type*}

/-- **`R*_T`, p.11:** the optimal value of the offline problem (PCP), p.8, on the problem profile
`H = (θ₁, …, θ_T)`: the maximum of `Σₜ f(xₜ; θₜ)` over `xₜ ∈ 𝒳` with `Σₜ gᵢ(xₜ; θₜ) ≤ cᵢ` for every `i`.

**Formalization Note.** A real `sSup`. For `c ≥ 0` the set is nonempty (`x ≡ 0` is feasible), and it is
bounded by `T` under Assumption 1 (a); the supremum is attained by compactness. -/
noncomputable def offlineValue (M : Model k m Θ) (c : Fin m → ℝ) (H : Fin T → Θ) : ℝ :=
  sSup {v | ∃ x : Fin T → Fin k → ℝ, (∀ t, x t ∈ M.X) ∧
    (∀ i, ∑ t, M.g (x t) (H t) i ≤ c i) ∧ v = ∑ t, M.f (x t) (H t)}

/-- **`R^UB_T`, (4), p.13:** the maximum of `Σₜ 𝒫ₜ f(xₜ(θₜ); θₜ)` over measurable `xₜ : Θ → 𝒳` with
`Σₜ 𝒫ₜ gᵢ(xₜ(θₜ); θₜ) ≤ cᵢ` for every `i`.

**Formalization Note.** A real `sSup`. For `c ≥ 0` the set is nonempty (`x ≡ 0`) and bounded by `T`
under Assumption 1 (a). `Measurable (x t)` makes the Bochner integrals honest. -/
noncomputable def fluidValue [MeasurableSpace Θ] (M : Model k m Θ) (c : Fin m → ℝ)
    (P : Fin T → Measure Θ) : ℝ :=
  sSup {v | ∃ x : Fin T → Θ → Fin k → ℝ, (∀ t, Measurable (x t)) ∧ (∀ t θ, x t θ ∈ M.X) ∧
    (∀ i, ∑ t, ∫ θ, M.g (x t θ) θ i ∂P t ≤ c i) ∧ v = ∑ t, ∫ θ, M.f (x t θ) θ ∂P t}

end OnlineWass


