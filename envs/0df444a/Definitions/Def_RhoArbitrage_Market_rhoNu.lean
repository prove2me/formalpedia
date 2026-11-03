-- Prove2me | Definitions.Def_RhoArbitrage_Market_rhoNu
-- name    : RhoArbitrage_Market_rhoNu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:44.663528+00:00
-- url     : https://prove2.me/theorems/12517718-6417-4cb7-bdab-82bee36846cd
-- title:
--   The minimal risk $\rho_\nu$ and the $\rho$-optimal portfolios $\Pi^\rho_\nu$
-- statement:
--   For $\nu\ge0$, a portfolio $\pi\in\Pi_\nu$ is **$\rho$-optimal for** $\nu$ if $\rho(X_\pi)<\infty$ and $\rho(X_\pi)\le\rho(X_{\pi'})$ for all $\pi'\in\Pi_\nu$. The set of these portfolios is $\Pi^\rho_\nu$, and
--
--   $$
--   \rho_\nu:=\inf\{\rho(X_\pi):\pi\in\Pi_\nu\}.
--   $$
--
--   The map $\nu\mapsto\rho_\nu$ is the $\rho$-optimal boundary with its axes reversed. Applied to $\rho^\infty$ the definition gives $\rho^\infty_\nu$, and the goal of the mission is about the sign of $\rho^\infty_1$.
--
--   **Formalization Note** The definitions take any functional in the place of $\rho$ and any real $\nu$. The infimum is in `EReal`, so $\inf\emptyset=+\infty$ and an infimum unbounded below is $-\infty$.
-- source:
--   Herdegen, Khan, ρ-arbitrage and ρ-consistent pricing for star-shaped risk measures, arXiv:2202.07610v3, Definition 3.2, p.6, display (3.1)

import Mathlib
import Definitions.Def_RhoArbitrage_Market

open MeasureTheory

namespace RhoArbitrage

namespace Market

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The value `ρ_ν`.** Herdegen–Khan, arXiv:2202.07610v3, Definition 3.2, p.6, display (3.1):
`ρ_ν := inf{ρ(X_π) : π ∈ Π_ν}`, for any functional `η` in the place of `ρ`, so that `ρ_ν` is
`M.rhoNu P ρ ν` and `ρ∞_ν` is `M.rhoNu P (rhoInf ρ) ν`.

**Formalization Note.** The infimum is in `EReal`, so `inf ∅ = +∞` and an infimum unbounded below
is `-∞`. -/
noncomputable def rhoNu (P : Measure Ω) (M : Market Ω) (η : (Ω → ℝ) → EReal) (ν : ℝ) : EReal :=
  sInf ((fun π => η (M.X π)) '' M.Pi P ν)

/-- **The set `Π^ρ_ν` of `ρ`-optimal portfolios.** Herdegen–Khan, arXiv:2202.07610v3,
Definition 3.2, p.6: `π ∈ Π_ν` is `ρ`-optimal for `ν` if `ρ(X_π) < ∞` and `ρ(X_π) ≤ ρ(X_π')` for
all `π' ∈ Π_ν`. -/
def optSet (P : Measure Ω) (M : Market Ω) (η : (Ω → ℝ) → EReal) (ν : ℝ) : Set (Fin M.d → ℝ) :=
  {π | π ∈ M.Pi P ν ∧ η (M.X π) < ⊤ ∧ ∀ π' ∈ M.Pi P ν, η (M.X π) ≤ η (M.X π')}

end Market

end RhoArbitrage


