-- Prove2me | Definitions.Def_InfluencerAuth_Switch_ClosedForms
-- name    : InfluencerAuth_Switch_ClosedForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:53.294989+00:00
-- url     : https://prove2.me/theorems/d11dc4b9-12c1-428e-871a-d7d444f052e8
-- title:
--   Lemma 3, (3), Condition 1 and footnote 4, pp. 6, 16 — the integrals V̲(A) and dV̲/dA, and Condition 1
-- statement:
--   This module defines the three closed-form objects of §3.3 that Proposition 1 refers to. Let $0<\gamma<1$, $\varphi>1$, $\beta>0$ and $r>0$, and write $s=u-t$ for the time elapsed since the current date.
--
--   1. The **value of always being inauthentic** at awareness $A\in(0,1)$, the right side of Lemma 3:
--   $$
--   \underline V(A)=\int_0^\infty \frac{e^{-rs}\,\gamma\varphi}{1+\frac{1-A}{A}\,e^{-\gamma\beta s}}\,ds .
--   $$
--   2. The **marginal value of awareness** under that policy, the right side of (3):
--   $$
--   m(A)=\int_0^\infty \frac{e^{-(\gamma\beta+r)s}\,\gamma\varphi}{\big[A+(1-A)e^{-\gamma\beta s}\big]^2}\,ds .
--   $$
--   3. **Condition 1**, in the form of footnote 4: it holds if either $\gamma\beta\ge r$ or
--   $$
--   \Big[\frac{\beta-\gamma\beta}{r-\gamma\beta}\Big]\gamma\varphi>\gamma\varphi-1 .
--   $$
--
--   Condition 1 compares the value of the extra awareness growth from a brief authentic spell at near-zero awareness with the extra profit per unit awareness from being inauthentic; Proposition 1 uses it to decide whether a small influencer ever starts out authentic, and $m$ to locate the awareness level at which she switches.
--
--   **Formalization Note** $\underline V(A)$ is only meaningful for $A>0$ and $m(A)$ for $A>0$ (at $A=0$ and $\gamma\beta\ge r$ the integrand of $m$ is not integrable); every statement of the mission evaluates them at $A\in(0,1)$ or lets $A\to0^+$. In Condition 1 the fraction is only consulted when $\gamma\beta<r$, so its denominator is positive; without the first disjunct the bracket would take Lean's junk value $x/0=0$ at $\gamma\beta=r$.
-- source:
--   Nistor, Selove, Villas-Boas, Management Science (Articles in Advance 2024), Lemma 3, (3), Condition 1, p. 6; footnote 4, p. 16

import Mathlib

open MeasureTheory Set

namespace InfluencerAuth.Switch

/-- Right side of Lemma 3 (p. 6) in the variable `s = u - t`, at awareness `A₀`:
`∫_0^∞ e^{-r s} γ φ / [1 + ((1 - A₀)/A₀) e^{-γ β s}] ds`.
Only meaningful for `0 < A₀`; every statement using it assumes `A₀ ∈ (0, 1)`. -/
noncomputable def inauthValue (γ φ β r A₀ : ℝ) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ),
    Real.exp (-r * s) * (γ * φ) / (1 + ((1 - A₀) / A₀) * Real.exp (-(γ * β) * s))

/-- Right side of (3) (p. 6) in the variable `s = u - t`, at awareness `A`:
`∫_0^∞ e^{-(γ β + r) s} γ φ / [A + (1 - A) e^{-γ β s}]^2 ds`.
Every statement using it evaluates it at `A ∈ (0, 1)` (or lets `A → 0⁺`). -/
noncomputable def margValue (γ φ β r A : ℝ) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ),
    Real.exp (-(γ * β + r) * s) * (γ * φ) / (A + (1 - A) * Real.exp (-(γ * β) * s)) ^ 2

/-- Condition 1 (p. 6) in the form of footnote 4 (p. 16): it holds if either `γ β ≥ r`
or `[(β - γ β)/(r - γ β)] γ φ > γ φ - 1`. The division is only reached when `γ β < r`. -/
def Condition1 (γ φ β r : ℝ) : Prop :=
  r ≤ γ * β ∨ (β - γ * β) / (r - γ * β) * (γ * φ) > γ * φ - 1

end InfluencerAuth.Switch


