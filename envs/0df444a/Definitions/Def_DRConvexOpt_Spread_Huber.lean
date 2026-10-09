-- Prove2me | Definitions.Def_DRConvexOpt_Spread_Huber
-- name    : DRConvexOpt_Spread_Huber
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:39:04.59803+00:00
-- url     : https://prove2.me/theorems/e822e6d4-4525-4fbe-9996-c2a5ed49c034
-- title:
--   (8) p. 20, Proposition 3.3 p. 21 — the expected-Huber-loss set and its lifted ambiguity set on ℝ^P × ℝ⁵₊
-- statement:
--   For $\delta>0$ the **Huber loss** of (8) is
--
--   $$
--   H_\delta(z)=\begin{cases}\tfrac12 z^2 & |z|\le\delta,\\ \delta\big(|z|-\tfrac12\delta\big) & \text{otherwise,}\end{cases}
--   $$
--
--   taken from the published definition `GenEmpLik.Expansion.huber` (the same function, written $\delta|z|-\delta^2/2$ there). For $f\in\mathbb R^P$ and $g\ge0$ this file defines:
--
--   1. the **target set** $\{\mathbb Q\in\mathcal P_0(\mathbb R^P):\ \mathbb E_{\mathbb Q}[H_\delta(f^\top\tilde z)]\le g\}$, whose members are required to have $H_\delta(f^\top\tilde z)$ integrable;
--   2. the **lifted ambiguity set** $\mathcal P$ of probability distributions of $(\tilde z,\tilde u,\tilde v,\tilde w,\tilde s,\tilde t)$ on $\mathbb R^P\times\mathbb R^5$ with $\tilde w$ integrable, $\mathbb E_{\mathbb P}[\tilde w]=g$ and, with probability one, $\tilde u,\tilde v,\tilde w,\tilde s,\tilde t\ge0$ and
--
--   $$
--   \delta(\tilde u-\tilde s)+\frac{\tilde s^2}{2}+\delta(\tilde v-\tilde t)+\frac{\tilde t^2}{2}\le\tilde w,\qquad \tilde u\ge\tilde s,\quad \tilde v\ge\tilde t,\quad f^\top\tilde z=\tilde u-\tilde v .
--   $$
--
--   These are the objects of assertion 3 of Proposition 3, which shows that an expected Huber loss bound is a marginal of an instance of the standardized ambiguity set (4).
--
--   **Formalization Note** The auxiliary vector is `Fin 5 → ℝ` with components $0,\dots,4$ equal to $\tilde u,\tilde v,\tilde w,\tilde s,\tilde t$. The page's carrier $\mathbb R^P\times\mathbb R^5_+$ is encoded as almost-sure nonnegativity of the five auxiliary variables on $\mathbb R^P\times\mathbb R^5$. The Huber function is a total function of $(\delta,z)$; statements using it assume $\delta>0$. Integrability clauses encode the existence of the expectations the page writes.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 20, eq. (8), and p. 21, Proposition 3, assertion 3

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_huber

namespace DRConvexOpt.Spread

open MeasureTheory

/-- Proposition 3.3, p. 21, right-hand set (with `fᵀz̃` for the printed `tᵀz̃`): the probability
distributions `Q` on `ℝ^P` under which `H_δ(fᵀz̃)` is integrable and `E_Q[H_δ(fᵀz̃)] ≤ g`, where `H_δ`
is the Huber loss (8), p. 20 (`GenEmpLik.Expansion.huber δ`). -/
def huberSet {nP : ℕ} (f : Fin nP → ℝ) (δ g : ℝ) : Set (Measure (Fin nP → ℝ)) :=
  {ν | IsProbabilityMeasure ν ∧ Integrable (fun z => GenEmpLik.Expansion.huber δ (f ⬝ᵥ z)) ν ∧
    ∫ z, GenEmpLik.Expansion.huber δ (f ⬝ᵥ z) ∂ν ≤ g}

/-- Proposition 3.3, p. 21: the lifted ambiguity set `𝒫` of probability distributions of
`(z̃, ũ, ṽ, w̃, s̃, t̃)`, with the auxiliary vector `a = (ũ, ṽ, w̃, s̃, t̃) = (a 0, …, a 4) ∈ ℝ⁵`, such
that `E_P[w̃] = g` (`w̃` integrable) and, `P`-almost surely,
`δ(ũ − s̃) + s̃²/2 + δ(ṽ − t̃) + t̃²/2 ≤ w̃`, `ũ ≥ s̃`, `ṽ ≥ t̃`, `fᵀz̃ = ũ − ṽ`, and all five auxiliary
variables are nonnegative (the page's `𝒫₀(ℝ^P × ℝ⁵₊)`). -/
def liftedHuberSet {nP : ℕ} (f : Fin nP → ℝ) (δ g : ℝ) :
    Set (Measure ((Fin nP → ℝ) × (Fin 5 → ℝ))) :=
  {μ | IsProbabilityMeasure μ ∧ Integrable (fun ω => ω.2 2) μ ∧ ∫ ω, ω.2 2 ∂μ = g ∧
    μ {ω | δ * (ω.2 0 - ω.2 3) + ω.2 3 ^ 2 / 2 + δ * (ω.2 1 - ω.2 4) + ω.2 4 ^ 2 / 2 ≤ ω.2 2 ∧
      ω.2 3 ≤ ω.2 0 ∧ ω.2 4 ≤ ω.2 1 ∧ f ⬝ᵥ ω.1 = ω.2 0 - ω.2 1 ∧ ∀ k, 0 ≤ ω.2 k} = 1}

end DRConvexOpt.Spread


