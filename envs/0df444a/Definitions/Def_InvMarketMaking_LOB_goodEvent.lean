-- Prove2me | Definitions.Def_InvMarketMaking_LOB_goodEvent
-- name    : InvMarketMaking_LOB_goodEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:21:21.865558+00:00
-- url     : https://prove2.me/theorems/5ce7d7aa-da8d-4e6b-92c9-849ed59a8dcd
-- title:
--   Full-feedback estimators $\widehat F_t,\widehat S_t$ (Eq. (12)) and the good event $\mathcal E_{\mathrm{good}}$ (Eq. (16))
-- statement:
--   The **full-feedback estimators** of $F$ and $S$ after $t$ rounds are
--   $$
--   \widehat F_t(b)=\frac1t\sum_{\tau=1}^t\mathbb I(V^{\mathrm{sell}}_\tau\le b),\qquad \widehat S_t(a)=\frac1t\sum_{\tau=1}^t\mathbb I(V^{\mathrm{buy}}_\tau\ge a).
--   $$
--   They are not observable under limit-order-book feedback. Given finite grids $\mathcal B^\circ,\mathcal A^\circ$ and radii $\psi_t(b),\psi_t(a)$, the **good event** up to the horizon $T$ is
--   $$
--   \mathcal E_{\mathrm{good}}=\bigcap_{t=1}^T\Big[\bigcap_{b\in\mathcal B^\circ}\big\{|F(b)-\widehat F_t(b)|\le\psi_t(b)\big\}\cap\bigcap_{a\in\mathcal A^\circ}\big\{|S(a)-\widehat S_t(a)|\le\psi_t(a)\big\}\Big].
--   $$
--   It is the event on which every confidence interval of the algorithm contains the true value, and all deterministic arguments of the analysis are carried out on it.
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Eq. (12), p. 33, and Definition 6.4, Eq. (16), p. 34

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_J
import Definitions.Def_InvMarketMaking_LOB_lobRound

namespace InvMarketMaking.LOB

open MeasureTheory

/-- The full-feedback empirical c.d.f. `F̂_t(b) = (1/t) Σ_{τ=1}^t I(V^sell_τ ≤ b)` (Maran, Restelli,
Stradi, arXiv:2610.24562v1, Eq. (12), p. 33). Not observable under LOB feedback. -/
noncomputable def empCdf {Ω : Type*} (M : Market Ω) (t : ℕ) (b : ℝ) (ω : Ω) : ℝ :=
  (∑ τ ∈ Finset.Icc 1 t, if M.Vs τ ω ≤ b then (1 : ℝ) else 0) / t

/-- The full-feedback empirical survival function `Ŝ_t(a) = (1/t) Σ_{τ=1}^t I(V^buy_τ ≥ a)`
(Eq. (12), p. 33). -/
noncomputable def empSurv {Ω : Type*} (M : Market Ω) (t : ℕ) (a : ℝ) (ω : Ω) : ℝ :=
  (∑ τ ∈ Finset.Icc 1 t, if a ≤ M.Vb τ ω then (1 : ℝ) else 0) / t

/-- The good event (Definition 6.4, Eq. (16), p. 34):
`𝓔_good = ⋂_{t=1}^T [⋂_{b ∈ B°} {|F(b) − F̂_t(b)| ≤ ψ_t(b)} ∩ ⋂_{a ∈ A°} {|S(a) − Ŝ_t(a)| ≤ ψ_t(a)}]`,
with `F̂_t, Ŝ_t` the full-feedback estimators of Eq. (12) and the radii and grids of `C`. -/
def goodEvent {Ω : Type*} (V : Measure (ℝ × ℝ)) (C : LOBConfig Ω) (M : Market Ω) (T : ℕ) :
    Set Ω :=
  {ω | ∀ t ∈ Finset.Icc 1 T,
    (∀ b ∈ C.Bg, |sellCdf V b - empCdf M t b ω| ≤ C.ψF t b ω) ∧
    (∀ a ∈ C.Ag, |buySurv V a - empSurv M t a ω| ≤ C.ψS t a ω)}

end InvMarketMaking.LOB


