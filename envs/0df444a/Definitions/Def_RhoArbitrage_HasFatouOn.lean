-- Prove2me | Definitions.Def_RhoArbitrage_HasFatouOn
-- name    : RhoArbitrage_HasFatouOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:24:49.925204+00:00
-- url     : https://prove2.me/theorems/8d0e74a0-b4f1-4576-a05a-8af635aa1b85
-- title:
--   Fatou property on a subset $\mathcal Y\subset L$
-- statement:
--   A functional $\rho$ has the **Fatou property on** $\mathcal Y\subset L$ if, whenever $X_n,X\in\mathcal Y$ with $X_n\to X$ $\mathbb P$-a.s. and $|X_n|\le Y$ $\mathbb P$-a.s. for all $n$ and some $Y\in L$, then
--
--   $$
--   \rho(X)\le\liminf_{n\to\infty}\rho(X_n).
--   $$
--
--   The property says that risk is not underestimated by dominated approximations. The mission uses it on the space $\mathcal X$ of excess returns only.
--
--   **Formalization Note** The dominating $Y$ lies in $L$, not in $\mathcal Y$.
-- source:
--   Herdegen, Khan, ρ-arbitrage and ρ-consistent pricing for star-shaped risk measures, arXiv:2202.07610v3, §2.1, p.5

import Mathlib

open MeasureTheory Filter Topology

namespace RhoArbitrage

/-- **Fatou property on `𝒴 ⊂ L`.** Herdegen–Khan, arXiv:2202.07610v3, §2.1, p.5: "If `Xₙ → X`
`P`-a.s. for `Xₙ, X ∈ 𝒴` and `|Xₙ| ≤ Y` `P`-a.s. for some `Y ∈ L` then
`ρ(X) ≤ lim infₙ→∞ ρ(Xₙ)`."

**Formalization Note.** The dominating `Y` lies in `L`, not in `𝒴`. The `liminf` is in `EReal`. The
paper indexes sequences by `n ≥ 1`, Lean by `n : ℕ`. -/
def HasFatouOn {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (L 𝒴 : Set (Ω → ℝ))
    (ρ : (Ω → ℝ) → EReal) : Prop :=
  ∀ (Xs : ℕ → Ω → ℝ) (X Y : Ω → ℝ), (∀ n, Xs n ∈ 𝒴) → X ∈ 𝒴 → Y ∈ L →
    (∀ᵐ ω ∂P, Tendsto (fun n => Xs n ω) atTop (𝓝 (X ω))) →
    (∀ n, ∀ᵐ ω ∂P, |Xs n ω| ≤ Y ω) →
    ρ X ≤ liminf (fun n => ρ (Xs n)) atTop

end RhoArbitrage


