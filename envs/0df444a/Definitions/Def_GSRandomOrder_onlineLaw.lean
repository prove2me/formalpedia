-- Prove2me | Definitions.Def_GSRandomOrder_onlineLaw
-- name    : GSRandomOrder_onlineLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:01.213924+00:00
-- url     : https://prove2.me/theorems/9bbd6a91-a919-4e56-a888-b5b834f7a78e
-- title:
--   Online law $L_{Q,t}$: the law of the accepted set on $Q$ with horizon $t$
-- statement:
--   For $Q\subseteq N$ and $t\in[1/e,1]$, $L_{Q,t}$ is the law of the accepted set when the survival algorithm runs on the items of $Q$ alone, with independent arrival times uniform on $[0,t]$. For a set $A$, $L_{Q,t}(A)$ is the probability that the final accepted set equals $A$.
--
--   Distribution matching says that this law equals the survival law $\mu^v_{Q,t}$.
--
--   **Formalization Note** The probability space is $\Omega_n$ with the product of uniform laws, arrival times $t\,r_g$ and one coin per item; the event is measurable, so the probability is its measure, converted to a real number (it is finite).
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §B.2, p.25

import Mathlib
import Definitions.Def_GSRandomOrder_runSurvival

set_option autoImplicit false

open MeasureTheory

namespace GSRandomOrder

/-- **The online law** `L_{Q,t}` (Paes Leme, Pál, Patel, *Gross Substitutes Welfare in Random
Order*, STOC 2027 submission, manuscript sha256 69787f50…, §B.2, p.25): for `Q ⊆ N` and
`t ∈ [1/e, 1]`, the law of the accepted set when the survival algorithm runs on the items of `Q`
alone, with independent arrival times uniform on `[0, t]`. `onlineLaw v Q t A` is the probability
that the final accepted set equals `A`.

**Formalization Note.** The probability space is `Ω n` with `volume` (independent uniform arrival
variables and coins); arrival times are `t · r_g`, so every item of `Q` has arrived by time `t`
and `runSurvival v Q t ω t` is the final state. The event is measurable (the run is a finite
composition of comparisons of measurable functions of `ω`), so `volume` is its probability; it is
finite, and `toReal` is exact. -/
noncomputable def onlineLaw {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (Q : Finset (Fin n))
    (t : ℝ) (A : Finset (Fin n)) : ℝ :=
  (volume {ω : Ω n | (runSurvival v Q t ω t).2 = A}).toReal

end GSRandomOrder


