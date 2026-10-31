-- Prove2me | Definitions.Def_ScalarMultiRisk_TimeConsistent
-- name    : ScalarMultiRisk_TimeConsistent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:24.509401+00:00
-- url     : https://prove2.me/theorems/4f0ead64-8d1e-40fa-ab9f-4a293e0f801c
-- title:
--   Definition 4.13 — time consistency
-- statement:
--   A family $(r_t)_{t=0}^T$ of maps on $L^\infty(E)$ is **time consistent** if for all times $t<s$ and all $X,Y\in L^\infty(E)$,
--
--   $$r_s(X)\le r_s(Y)\ \Rightarrow\ r_t(X)\le r_t(Y),$$
--
--   all inequalities being almost sure. With $E=\mathbb R^d$ and $r=\pi^S$ this is Definition 4.13; with $E=\mathbb R$ and $r=\phi^S$ it is the usual univariate notion.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Definition 4.13, p.24

import Mathlib
import Definitions.Def_ScalarMultiRisk_LinftyFull

open MeasureTheory

namespace ScalarMultiRisk

/-- **Time consistency.** arXiv:1807.10694v5, Definition 4.13, p.24: for all times `t < s` and
`X, Y ∈ L∞(ℝ^d)`, `π^S_s(X) ≤ π^S_s(Y) ⇒ π^S_t(X) ≤ π^S_t(Y)`, the inequalities being a.s.

**Formalization Note.** Written for a family of `EReal`-valued maps on `L∞(E)`:
`E = Fin d → ℝ`, `r = π^S` is Definition 4.13, and `E = ℝ`, `r = φ^S` is the usual univariate
notion of Proposition 4.14. -/
def TimeConsistent {Ω : Type*} [MeasurableSpace Ω] {T : ℕ} {E : Type*} [NormedAddCommGroup E]
    (B : FilteredSpace Ω T) (r : Fin (T + 1) → (Ω → E) → Ω → EReal) : Prop :=
  ∀ t s : Fin (T + 1), t < s →
    ∀ X ∈ LinftyFull B (Fin.last T), ∀ Y ∈ LinftyFull B (Fin.last T),
      r s X ≤ᵐ[B.P] r s Y → r t X ≤ᵐ[B.P] r t Y

end ScalarMultiRisk


