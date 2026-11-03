-- Prove2me | Definitions.Def_RhoArbitrage_Market_AdmitsArbitrage
-- name    : RhoArbitrage_Market_AdmitsArbitrage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:52.310123+00:00
-- url     : https://prove2.me/theorems/e3dabcd7-eda5-4346-b5f1-3e2b00f85604
-- title:
--   $\rho$-arbitrage
-- statement:
--   The market $(S^0,S)$ **admits $\rho$-arbitrage** if there is a sequence of portfolios $(\pi_n)_{n\ge1}\subset\mathbb R^d$ such that
--
--   $$
--   \mathbb E[X_{\pi_n}]\uparrow\infty\quad\text{and}\quad\rho(X_{\pi_n})\le0\ \text{ for all }n.
--   $$
--
--   Such a market lets an agent earn arbitrarily large expected excess returns at no risk as measured by $\rho$, so the risk constraint is void. For $\rho$ the worst-case risk measure this is arbitrage of the first kind.
--
--   **Formalization Note** The definition takes any functional in the place of $\rho$, so $\rho^\infty$-arbitrage is the same definition applied to $\rho^\infty$. "$\uparrow\infty$" is read as nondecreasing and tending to $+\infty$.
-- source:
--   Herdegen, Khan, ρ-arbitrage and ρ-consistent pricing for star-shaped risk measures, arXiv:2202.07610v3, Definition 3.3, p.7

import Mathlib
import Definitions.Def_RhoArbitrage_Market

open MeasureTheory Filter

namespace RhoArbitrage

namespace Market

/-- **`ρ`-arbitrage.** Herdegen–Khan, arXiv:2202.07610v3, Definition 3.3, p.7: the market admits
`ρ`-arbitrage if there is a sequence of portfolios `(πₙ) ⊂ ℝ^d` with `E[X_{πₙ}] ↑ ∞` and
`ρ(X_{πₙ}) ≤ 0` for all `n`. The definition is stated for any functional `η` in the place of `ρ`;
`ρ∞`-arbitrage is `M.AdmitsArbitrage P (rhoInf ρ)`.

**Formalization Note.** "`↑ ∞`" is read as nondecreasing and tending to `+∞`. The strictly
increasing reading gives the same notion, since a sequence tending to `+∞` has a strictly
increasing subsequence. The paper indexes by `n ≥ 1`, Lean by `n : ℕ`. -/
def AdmitsArbitrage {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Market Ω)
    (η : (Ω → ℝ) → EReal) : Prop :=
  ∃ πs : ℕ → Fin M.d → ℝ,
    Monotone (fun n => ∫ ω, M.X (πs n) ω ∂P) ∧
    Tendsto (fun n => ∫ ω, M.X (πs n) ω ∂P) atTop atTop ∧
    ∀ n, η (M.X (πs n)) ≤ 0

end Market

end RhoArbitrage


