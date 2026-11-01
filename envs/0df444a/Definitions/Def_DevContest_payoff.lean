-- Prove2me | Definitions.Def_DevContest_payoff
-- name    : DevContest_payoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:52:03.862992+00:00
-- url     : https://prove2.me/theorems/dc24ee13-1e2e-4ec3-88f4-0459dd59a629
-- title:
--   The law of the contest, the expected lead time and the agents' expected utility
-- statement:
--   The draw $u\sim\nu$ and the four clocks, which are unit-exponential, are independent. Under this law:
--
--   1. the **expected lead time** is $\mathbb E[T]\in[0,\infty]$;
--   2. the **expected utility** of agent $i$ from time $0$, display (1) for the fixed reward $\bar R$, is
--   $$
--   \bar R\,\mathbb P(i\text{ wins})-c\,\mathbb E\int_0^T x^i_\tau\,d\tau ,
--   $$
--   where effort is evaluated along the realized record.
--
--   These are the two objectives of the paper: the principal's and the agents'.
--
--   **Formalization Note** The lead time is $\infty$ when the contest fails to end with positive probability, whereas (2) reads $\mathbb E[T\cdot 1\{i\text{ or }-i\text{ wins at }T\}]$, which agrees for contests that end. Utility is valued in the extended reals so that an infinite cost is $-\infty$; the reward term is finite, so no indeterminate form arises.
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, display (1), p.10; display (2), p.12; §5, p.17

import Mathlib
import Definitions.Def_DevContest_play

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace DevContest

/-- The joint law of the principal's randomization and the four unit-exponential clocks, which are
independent. -/
noncomputable def law {U M : Type} [MeasurableSpace U] (D : Policy U M) : Measure (U × Clocks) :=
  D.ν.prod (Measure.pi fun _ : Fin 2 × Fin 2 => expMeasure 1)

/-- The expected lead time of the contest, Khorasani, Körpeoğlu, Krishnan, *Dynamic Development
Contests*, author manuscript, display (2), p.12.

**Formalization Note.** The value is in `[0,∞]`: it is `∞` when the contest fails to end with
positive probability. The paper's `E[T · 1{i or -i wins at T}]` is this for contests that end; read
literally on a contest that may never end it would count those paths as `0`, and a contest in which
nobody works would be optimal. -/
noncomputable def leadTime (lam : ℝ) {U M : Type} [MeasurableSpace U] (D : Policy U M)
    (x : Fin 2 → Strategy U) : ℝ≥0∞ :=
  ∫⁻ ω : U × Clocks, (play lam x ω.1 ω.2).lead ∂(law D)

/-- The probability that agent `i` wins. -/
noncomputable def winProb (lam : ℝ) {U M : Type} [MeasurableSpace U] (D : Policy U M)
    (x : Fin 2 → Strategy U) (i : Fin 2) : ℝ :=
  (law D).real {ω : U × Clocks | (play lam x ω.1 ω.2).winner = some i}

/-- The expected total effort `E ∫_{[0,T)} x^i_τ dτ` of agent `i`, along the realized record. It is
`∞` when she works forever with positive probability. -/
noncomputable def expectedEffort (lam : ℝ) {U M : Type} [MeasurableSpace U] (D : Policy U M)
    (x : Fin 2 → Strategy U) (i : Fin 2) : ℝ≥0∞ :=
  ∫⁻ ω : U × Clocks, (∫⁻ τ in {τ : ℝ | 0 ≤ τ ∧ (τ.toNNReal : ℝ≥0∞) < (play lam x ω.1 ω.2).lead},
    ENNReal.ofReal (x i τ.toNNReal (trunc τ.toNNReal (play lam x ω.1 ω.2).first) ω.1)) ∂(law D)

/-- The expected utility of agent `i` from time `0`, display (1), p.10, for the fixed reward `Rbar`
(§5, p.17): `R̄ · P(i wins) − c · E ∫_{[0,T)} x^i_τ dτ`.

**Formalization Note.** The value is in `EReal`, so that an infinite cost is `-∞`. The reward term is
finite, so no `⊤ - ⊤` arises. -/
noncomputable def payoff (lam c Rbar : ℝ) {U M : Type} [MeasurableSpace U] (D : Policy U M)
    (x : Fin 2 → Strategy U) (i : Fin 2) : EReal :=
  ((Rbar * winProb lam D x i : ℝ) : EReal) - (c : EReal) * (expectedEffort lam D x i : EReal)

end DevContest


