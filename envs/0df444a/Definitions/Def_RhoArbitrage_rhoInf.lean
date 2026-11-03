-- Prove2me | Definitions.Def_RhoArbitrage_rhoInf
-- name    : RhoArbitrage_rhoInf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:24:48.182858+00:00
-- url     : https://prove2.me/theorems/9965c4af-5fb6-4206-947c-18288b372d69
-- title:
--   The smallest positively homogeneous majorant $\rho^\infty$
-- statement:
--   For a risk functional $\rho$ on $L$ and $X\in L$, put
--
--   $$
--   \rho^\infty(X):=\lim_{t\to\infty}\frac{\rho(tX)}{t}.
--   $$
--
--   This is the smallest positively homogeneous majorant of $\rho$. It governs the behaviour of $\rho$ at large scales, and whether a market admits $\rho$-arbitrage is decided by $\rho^\infty$.
--
--   **Formalization Note** Lean defines $\rho^\infty(X)$ as $\sup_{t\ge1}\rho(tX)/t$ in the extended reals. For a star-shaped $\rho$ the quotient is nondecreasing in $t$, so this supremum equals the limit; the milestone `RhoArbitrage.display_2_1` states that the limit exists and equals it.
-- source:
--   Herdegen, Khan, ρ-arbitrage and ρ-consistent pricing for star-shaped risk measures, arXiv:2202.07610v3, §2.1, p.5, display (2.1)

import Mathlib

namespace RhoArbitrage

/-- **The functional `ρ∞`.** Herdegen–Khan, arXiv:2202.07610v3, §2.1, p.5, display (2.1):
`ρ∞(X) := lim_{t→∞} ρ(tX)/t`.

**Formalization Note.** Lean defines `ρ∞(X)` as `sup_{t ≥ 1} ρ(tX)/t`, with `ρ(tX)/t` written
`((t⁻¹ : ℝ) : EReal) * ρ (t • X)`. For a star-shaped `ρ` the map `t ↦ ρ(tX)/t` is nondecreasing on
`(0, ∞)`, so the supremum is the limit (2.1); the milestone `RhoArbitrage.display_2_1` states that
the limit exists and equals this supremum for every risk functional and every `X ∈ L`. -/
noncomputable def rhoInf {Ω : Type*} (ρ : (Ω → ℝ) → EReal) (X : Ω → ℝ) : EReal :=
  ⨆ (t : ℝ) (_ : 1 ≤ t), ((t⁻¹ : ℝ) : EReal) * ρ (t • X)

end RhoArbitrage


