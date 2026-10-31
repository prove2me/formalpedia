-- Prove2me | Definitions.Def_ScalarMultiRisk_HasFatou
-- name    : ScalarMultiRisk_HasFatou
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:54.104466+00:00
-- url     : https://prove2.me/theorems/7087e326-608a-47f6-9397-627927297560
-- title:
--   Definition 3.5 — Fatou property
-- statement:
--   A risk measure $\rho_t$ has the **Fatou property** if
--
--   $$\rho_t(X)\le\liminf_{n\to\infty}\rho_t(X_n)\quad\text{a.s.}$$
--
--   for every $\|\cdot\|_\infty$-bounded sequence $(X_n)$ converging to $X$ almost surely. It is the lower semicontinuity behind the dual representation.
--
--   **Formalization Note** The limit inferior is taken in the extended reals.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Definition 3.5, p.9

import Mathlib
import Definitions.Def_ScalarMultiRisk_LinftyFull

open MeasureTheory

namespace ScalarMultiRisk

/-- **Fatou property.** arXiv:1807.10694v5, Definition 3.5, p.9:
`ρ_t(X) ≤ lim inf_{n→∞} ρ_t(X_n)` a.s. for any `‖·‖_∞`-bounded sequence `X_n` converging to `X`
almost surely.

**Formalization Note.** The `lim inf` is taken in `EReal`, so it is meaningful for every
sequence of reals. -/
def HasFatou {Ω : Type*} [MeasurableSpace Ω] {T : ℕ} {E : Type*} [NormedAddCommGroup E]
    (B : FilteredSpace Ω T) (r : (Ω → E) → Ω → ℝ) : Prop :=
  ∀ X ∈ LinftyFull B (Fin.last T), ∀ Xn : ℕ → Ω → E,
    (∀ n, Xn n ∈ LinftyFull B (Fin.last T)) →
    (∃ C : ℝ, ∀ n, ∀ᵐ ω ∂B.P, ‖Xn n ω‖ ≤ C) →
    (∀ᵐ ω ∂B.P, Filter.Tendsto (fun n => Xn n ω) Filter.atTop (nhds (X ω))) →
    ∀ᵐ ω ∂B.P, (r X ω : EReal) ≤ Filter.liminf (fun n => (r (Xn n) ω : EReal)) Filter.atTop

end ScalarMultiRisk


