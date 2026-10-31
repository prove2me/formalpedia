-- Prove2me | Definitions.Def_ScalarMultiRisk_QStar
-- name    : ScalarMultiRisk_QStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:21:10.964434+00:00
-- url     : https://prove2.me/theorems/bc16665e-d404-4b0a-98f1-629a634f6b94
-- title:
--   (4.9) — the set $\mathcal Q^*(S)$
-- statement:
--   $\mathcal Q^*(S)=\{\mathbb Q\in\mathcal Q^e(S)\mid\beta_0(\mathbb Q,S)<\infty\}$: the consistent equivalent martingale measures of finite penalty at time $0$.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, (4.9), p.24

import Mathlib
import Definitions.Def_ScalarMultiRisk_beta
import Definitions.Def_ScalarMultiRisk_Qe

open MeasureTheory

namespace ScalarMultiRisk

/-- **The set `Q*(S)`.** arXiv:1807.10694v5, (4.9), p.24:
`Q*(S) := {ℚ ∈ 𝒬^e(S) | β_0(ℚ,S) < ∞}`.

**Formalization Note.** `β_0(ℚ,S)` is `F₀`-measurable, hence a.s. a constant, and `< ∞` means
a.s. -/
def QStar {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} (A : Market Ω T d)
    (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ) (S : Fin (T + 1) → Ω → Fin d → ℝ) :
    Set (Measure Ω) :=
  {Q ∈ Qe A S | ∀ᵐ ω ∂A.P, beta A ρ 0 Q S ω < ⊤}

end ScalarMultiRisk


