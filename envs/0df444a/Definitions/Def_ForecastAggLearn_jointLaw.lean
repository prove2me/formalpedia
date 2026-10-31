-- Prove2me | Definitions.Def_ForecastAggLearn_jointLaw
-- name    : ForecastAggLearn_jointLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:15.933339+00:00
-- url     : https://prove2.me/theorems/8e5285e6-25ed-4f44-8520-3416db8a53f5
-- title:
--   Joint law of the state and the conditionally independent signals
-- statement:
--   The state is $\omega\in\Omega=\{0,1\}$ with prior $\mu=\mathbb P(\omega=1)$. Signal $j\in[m]$ takes values in a measurable space $S_j$ and has conditional laws $C_j^1$ (given $\omega=1$) and $C_j^0$ (given $\omega=0$). Given $\omega$, the signals are independent. The joint law $C$ of $(\omega,s)$, $s=(s_1,\dots,s_m)$, is
--
--   $$
--   C=\mu\,\delta_1\otimes\bigotimes_{j=1}^m C_j^1+(1-\mu)\,\delta_0\otimes\bigotimes_{j=1}^m C_j^0 .
--   $$
--
--   This is one period's **partial evidence information structure**; with the evidence matrix it determines every expert's forecast.
--
--   **Formalization Note** $\Omega$ is `Bool` with `true` for $\omega=1$; `P j true` is $C_j^1$ and `P j false` is $C_j^0$. The signal spaces are arbitrary measurable spaces. The theorems assume $0\le\mu\le1$ and that every $C_j^b$ is a probability measure, so $C$ is a probability measure.
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, §2, p.9

import Mathlib

namespace ForecastAggLearn

open MeasureTheory

/-- **Joint law of the state and the signal profile.**
Babichenko, Garber, arXiv:1802.07107v1, §2, p.9: "The unknown state of nature is Ω = {0, 1} with
the common prior µ = P(ω = 1). [...] The distribution C_j defines two conditional distributions
C_j^0 and C_j^1. We assume that conditioned on ω, C_j^ω is independent of C_{j'}^ω for j ≠ j'.
We denote by s = (s_1, ..., s_m) the profile of signals, and by C the joint distribution over
(ω, s)."

The measure `μ · δ_1 ⊗ (⊗_j C_j^1) + (1 − μ) · δ_0 ⊗ (⊗_j C_j^0)` on `Ω × S_1 × ⋯ × S_m`.

**Formalization Note.** Ω = {0, 1} is `Bool`, with `true` for ω = 1. `P j true` is `C_j^1` and
`P j false` is `C_j^0`; the signal spaces `S j` are arbitrary measurable spaces. The theorems
assume `0 ≤ μ ≤ 1` and that every `P j b` is a probability measure; then this is a probability
measure. Conditional independence given ω is the product `Measure.pi`. -/
noncomputable def jointLaw {m : ℕ} {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℝ) (P : (j : Fin m) → Bool → Measure (S j)) : Measure (Bool × ((j : Fin m) → S j)) :=
  ENNReal.ofReal μ • (Measure.dirac true).prod (Measure.pi fun j => P j true) +
    ENNReal.ofReal (1 - μ) • (Measure.dirac false).prod (Measure.pi fun j => P j false)

end ForecastAggLearn


