-- Prove2me | Definitions.Def_KellyRSN_PartialBalance_IsNonExplosive
-- name    : KellyRSN_PartialBalance_IsNonExplosive
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:36:02.339998+00:00
-- url     : https://prove2.me/theorems/a389e7ee-fc37-4df4-8d38-10789dc06517
-- title:
--   Non-explosion: no infinitely many jumps in finite time
-- statement:
--   Transition rates $q$ on a countable state space $\mathcal S$ are **non-explosive** if, for every initial state $j$, almost every path $\omega$ of the jump chain started at $j$ satisfies
--   $$
--   \sum_{n=0}^{\infty} \frac{1}{q(\omega_n)} = \infty, \qquad q(i) = \sum_{k} q(i,k).
--   $$
--
--   This is the book's standing assumption that a Markov process "is incapable of passing through an infinite number of states in a finite time": given the jump chain, the holding times are independent exponential variables with means $1/q(\omega_n)$, and their sum is infinite almost surely exactly when the series above diverges almost surely (Norris, *Markov Chains*, Theorems 2.3.2 and 2.7.1).
--
--   **Formalization Note** An absorbing state ($q(i) = 0$) contributes $1/0 = \infty$.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 2-3 (PDF pp. 5-6), §1.1, standing assumption 'incapable of passing through an infinite number of states in a finite time'

import Mathlib
import Definitions.Def_KellyRSN_PartialBalance_jumpChainLaw

open MeasureTheory
open scoped ENNReal

namespace KellyRSN.PartialBalance

/-- **Non-explosion: the process cannot pass through infinitely many states in finite time.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, §1.1, pp. 2–3 (PDF pp. 5–6): "throughout
this work we shall assume that any continuous time Markov process with which we deal is … incapable
of passing through an infinite number of states in a finite time."

`IsNonExplosive q` says: for every initial state `j`, almost every path `ω` of the jump chain
started at `j` satisfies `Σ_n 1 / q(ω n) = ∞`, where `q(i) = Σ_k q(i, k)`.

**Formalization Note.** The process is represented by its rates. Given the jump chain
`J_0, J_1, …`, the holding times are independent exponentials `E_n / q(J_n)` (`E_n` i.i.d. Exp(1)),
and the time of the infinitely many jumps, `Σ_n E_n / q(J_n)`, is infinite almost surely iff
`Σ_n 1/q(J_n) = ∞` almost surely (Norris, *Markov Chains*, 1997, Theorems 2.3.2 and 2.7.1). An
absorbing state (`q(i) = 0`) contributes `1/0 = ∞`, so a path that is absorbed never explodes. -/
def IsNonExplosive {S : Type*} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (q : S → S → ℝ≥0∞) : Prop :=
  ∀ j, ∀ᵐ ω ∂ jumpChainLaw q j, ∑' n, (∑' k, q (ω n) k)⁻¹ = ⊤

end KellyRSN.PartialBalance


