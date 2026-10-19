-- Prove2me | Definitions.Def_DynkinIncInfo_Saddle_DynkinGame
-- name    : DynkinIncInfo_Saddle_DynkinGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:42.53626+00:00
-- url     : https://prove2.me/theorems/3c976042-e1a5-4b82-8136-919ca7313f5f
-- title:
--   pp. 2–3, (1.3)–(1.4) — a general continuous-time Dynkin game: payoff, expected payoff, upper and lower values, saddle points
-- statement:
--   A general zero-sum **Dynkin game** (optimal stopping game) in continuous time, with nonnegative payoffs.
--
--   Fix a probability space $(\Omega,\mathcal F,\mathbb P)$, a filtration $(\mathcal F_t)_{t\ge0}$ and two nonnegative (already discounted) payoff processes $L$ and $U$. Player 1 (the maximiser) chooses a stopping time $\tau$ and player 2 (the minimiser) a stopping time $\gamma$, both with values in $[0,\infty]$. The expected payoff is
--   $$M(\tau,\gamma)=\mathbb E\big[L_\tau\mathbf 1_{\{\tau\le\gamma\}}+U_\gamma\mathbf 1_{\{\gamma<\tau\}}\big],$$
--   with payoff $0$ on $\{\tau=\gamma=\infty\}$. The upper and lower values are
--   $$\overline V=\inf_\gamma\sup_\tau M(\tau,\gamma),\qquad \underline V=\sup_\tau\inf_\gamma M(\tau,\gamma),$$
--   and a pair $(\tau_*,\gamma_*)$ of stopping times is a **saddle point** (Nash equilibrium) if
--   $$M(\tau,\gamma_*)\le M(\tau_*,\gamma_*)\le M(\tau_*,\gamma)\quad\text{for all stopping times }\tau,\gamma.$$
--
--   This frame is independent of the underlying model and can be reused for any Dynkin game with nonnegative payoffs.
--
--   **Formalization Note.** $M$ is a Lebesgue integral of a nonnegative function, valued in $[0,\infty]$, so it needs no integrability assumption. Stopping times are Mathlib stopping times valued in `WithTop ℝ≥0`; on $\{\tau\le\gamma,\ \tau<\infty\}$ the payoff is $L_\tau$, on $\{\gamma<\tau\}$ it is $U_\gamma$, and otherwise ($\tau=\gamma=\infty$) it is $0$.
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, pp. 2–3, (1.3), the zero-payoff convention, (1.4) and the saddle-point definition

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

/-! A general zero-sum Dynkin game in continuous time with nonnegative payoffs (the abstract frame
of De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the
Return, arXiv:1705.07352v4, pp. 2–3, (1.3)–(1.4) and the saddle-point definition). Player 1 (the
maximiser) stops at `τ` and receives the discounted payoff `L_τ`; player 2 (the minimiser) stops
at `γ` and pays `U_γ`; if `τ ≤ γ` player 1's payoff is paid, if `γ < τ` player 2's. -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The realised payoff of a Dynkin game with (discounted, nonnegative) payoff processes `L`
(player 1, the maximiser, paid at `τ` on `{τ ≤ γ}`) and `U` (player 2, the minimiser, paid at `γ`
on `{γ < τ}`). Stopping times take values in `[0, ∞]`; on `{τ = γ = ∞}` the payoff is `0`
(the convention of p. 3, arXiv:1705.07352v4). -/
noncomputable def dynkinPayoff (L U : ℝ≥0 → Ω → ℝ≥0∞) (τ γ : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  if τ ω ≤ γ ω ∧ τ ω ≠ ⊤ then L (τ ω).untopA ω
  else if γ ω < τ ω then U (γ ω).untopA ω
  else 0

/-- The expected payoff `M(τ, γ) = E[L_τ 1{τ ≤ γ} + U_γ 1{γ < τ}]` of the Dynkin game, a Lebesgue
integral in `[0, ∞]` ((1.3), p. 2, arXiv:1705.07352v4). -/
noncomputable def dynkinM (P : Measure Ω) (L U : ℝ≥0 → Ω → ℝ≥0∞) (τ γ : Ω → WithTop ℝ≥0) :
    ℝ≥0∞ :=
  ∫⁻ ω, dynkinPayoff L U τ γ ω ∂P

/-- The upper value `inf_γ sup_τ M(τ, γ)` over `ℱ`-stopping times with values in `[0, ∞]`
((1.4), p. 3, arXiv:1705.07352v4). -/
noncomputable def dynkinUpper (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (P : Measure Ω)
    (L U : ℝ≥0 → Ω → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (γ : Ω → WithTop ℝ≥0) (_ : IsStoppingTime ℱ γ),
    ⨆ (τ : Ω → WithTop ℝ≥0) (_ : IsStoppingTime ℱ τ), dynkinM P L U τ γ

/-- The lower value `sup_τ inf_γ M(τ, γ)` over `ℱ`-stopping times with values in `[0, ∞]`
((1.4), p. 3, arXiv:1705.07352v4). -/
noncomputable def dynkinLower (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (P : Measure Ω)
    (L U : ℝ≥0 → Ω → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (τ : Ω → WithTop ℝ≥0) (_ : IsStoppingTime ℱ τ),
    ⨅ (γ : Ω → WithTop ℝ≥0) (_ : IsStoppingTime ℱ γ), dynkinM P L U τ γ

/-- A saddle point (Nash equilibrium) of the Dynkin game (p. 3, arXiv:1705.07352v4): `τs` and `γs`
are `ℱ`-stopping times and `M(τ, γs) ≤ M(τs, γs) ≤ M(τs, γ)` for all `ℱ`-stopping times `τ`, `γ`. -/
def IsDynkinSaddle (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (P : Measure Ω)
    (L U : ℝ≥0 → Ω → ℝ≥0∞) (τs γs : Ω → WithTop ℝ≥0) : Prop :=
  IsStoppingTime ℱ τs ∧ IsStoppingTime ℱ γs ∧
    ∀ τ γ : Ω → WithTop ℝ≥0, IsStoppingTime ℱ τ → IsStoppingTime ℱ γ →
      dynkinM P L U τ γs ≤ dynkinM P L U τs γs ∧ dynkinM P L U τs γs ≤ dynkinM P L U τs γ

end DynkinIncInfo.Saddle


