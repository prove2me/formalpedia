-- Prove2me | Definitions.Def_ScalarMultiRisk_dualTerm
-- name    : ScalarMultiRisk_dualTerm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:21:18.125979+00:00
-- url     : https://prove2.me/theorems/c4bcc0b7-ffb9-4e9e-b498-d3891ea697af
-- title:
--   The dual term $-\beta_t(\mathbb Q,S)-\mathbb E^{\mathbb Q}[Z\mid\mathcal F_t]$
-- statement:
--   For a bounded random variable $Z$, the dual term is $-\beta_t(\mathbb Q,S)-\mathbb E^{\mathbb Q}[Z\mid\mathcal F_t]$. Where $\beta_t(\mathbb Q,S)=+\infty$ its value is $-\infty$. The dual representations are essential suprema of these terms.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, (4.4), p.18

import Mathlib
import Definitions.Def_ScalarMultiRisk_beta

open MeasureTheory

namespace ScalarMultiRisk

/-- **The dual term.** arXiv:1807.10694v5, (4.4), p.18, and Corollary 4.10(2), p.22:
`−β_t(ℚ,S) − 𝔼^ℚ[Z | F_t]` for a bounded random variable `Z`.

**Formalization Note.** `EReal` subtraction of a real: `β_t(ℚ,S) = +∞` gives `−∞`, as in the
paper's `L⁰_t(ℝ) ∪ {−∞}`. No `∞ − ∞` occurs because `Q[Z|F t]` is real. -/
noncomputable def dualTerm {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} (A : Market Ω T d)
    (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ) (S : Fin (T + 1) → Ω → Fin d → ℝ)
    (t : Fin (T + 1)) (Q : Measure Ω) (Z : Ω → ℝ) : Ω → EReal :=
  fun ω => -beta A ρ t Q S ω - ((Q[Z | A.F t] ω : ℝ) : EReal)

end ScalarMultiRisk


