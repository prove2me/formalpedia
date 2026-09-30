-- Prove2me | Definitions.Def_AlgMechDesign_Rounding_Mechanism
-- name    : AlgMechDesign_Rounding_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T22:02:54.669587+00:00
-- url     : https://prove2.me/theorems/53b2833d-61b4-4039-a554-e968877754f6
-- title:
--   The rounding mechanism: rounded-optimal allocation, exact compensation, rounded bonus
-- statement:
--   This file defines the **rounding mechanism** of Nisan–Ronen (Definition 34) for the bounded task scheduling problem with verification.
--
--   Fix a rounding step $\delta > 0$ and write $\hat\tau$ for a vector rounded up entrywise to integer multiples of $\delta$, and $\hat g(x,\tau) = g(x,\hat\tau)$.
--
--   1. **Allocation.** The allocation algorithm $x(\cdot)$ is specified by what the rounding algorithm of Horowitz and Sahni achieves: on every declaration profile $d \in [a,b]^{n\times k}$ it exactly solves the rounded problem,
--   $$g\big(x(d), \hat d\big) \le g(y, \hat d) \quad \text{for every allocation } y.$$
--   Ties are arbitrary.
--   2. **Compensation.** $c^i(d,\tilde t) = \sum_{j\in x^i(d)} \tilde t_j$, the exact actual times of agent $i$'s tasks.
--   3. **Bonus.** $b^i(d,\tilde t) = -\hat g\big(x(d), \mathrm{corr}^i(x(d), d, \tilde t)\big)$, the negated make-span of agent $i$'s corrected time vector after rounding.
--   4. **Payment.** $p^i = c^i + b^i$.
--
--   The file also names the class of strategies singled out in the proof of Theorem 5.9: agent $i$ of type $t^i$ declares some $d^i$ with $\hat d^i = \hat t^i$, and for every decision executes each own task $j$ in a time $\tilde t_j$ with $\hat{\tilde t}_j = \hat t^i_j$.
--
--   The mechanism pays exact compensation but computes the bonus from rounded quantities, which is what lets an approximation algorithm, rather than an exact optimizer, sit inside a truthful mechanism with verification.
--
--   **Formalization Note** The allocation algorithm is a parameter together with the hypothesis `IsRoundedOptimal a b δ alloc`; the dynamic program and its running time are not formalized. The paper prints the bonus as $-\hat g(x(\hat t), \widehat{\mathrm{corr}}^i(x(t),t,\tilde t))$; the allocation is written $x(\hat t)$ there, but the rounding algorithm is applied to the declarations $t$ and rounds them itself, so the allocation used is $x(t)$ throughout, and the hat on $\mathrm{corr}$ is absorbed by $\hat g$, which already rounds its argument.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 192, paragraph after Definition 33 and Notation; p. 193, Definition 34; p. 193, proof of Theorem 5.9 (strategy class)

import Mathlib
import Definitions.Def_AlgMechDesign_Rounding_Model

namespace AlgMechDesign.Rounding

open Finset

/-- The specification of the rounding algorithm of Horowitz and Sahni (§5.6, p. 192): on every
declaration profile `d` in `[a, b]` it exactly solves the rounded problem, i.e. its allocation has
the least make-span for the rounded declarations `d̂` (entries rounded up to multiples of `δ`)
among all allocations. Ties are arbitrary, and the allocation may depend on `d` itself, not only
on `d̂`. -/
def IsRoundedOptimal {n k : ℕ} [NeZero n] (a b δ : ℝ)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) : Prop :=
  ∀ d : Fin n → Fin k → ℝ, IsBoundedType a b d →
    ∀ y : Fin k → Fin n, makespan (roundType δ d) (alloc d) ≤ makespan (roundType δ d) y

/-- The compensation of agent `i` (Def. 34): `cⁱ(d, t̃) = ∑_{j ∈ xⁱ(d)} t̃_j`, the exact actual
times of its own tasks. -/
def compensation {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (tt : Fin k → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ univ.filter (fun j => alloc d j = i), tt j

/-- The rounded bonus of agent `i` (Def. 34): `bⁱ(d, t̃) = -ĝ(x, corrⁱ(x, d, t̃))` with
`x = alloc d`, where `ĝ(x, τ) = g(x, τ̂)` is the make-span of the rounded time vector. -/
noncomputable def roundedBonus {n k : ℕ} [NeZero n] (δ : ℝ)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (tt : Fin k → ℝ) (i : Fin n) : ℝ :=
  -gT (alloc d) (roundVec δ (corr i (alloc d) d tt))

/-- The payment of the rounding mechanism (Def. 34): `pⁱ(d, t̃) = cⁱ(d, t̃) + bⁱ(d, t̃)`, the
amount handed to agent `i`. The rounding mechanism is the pair `(alloc, roundingPay δ alloc)` with
`alloc` meeting `IsRoundedOptimal a b δ`. -/
noncomputable def roundingPay {n k : ℕ} [NeZero n] (δ : ℝ)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (tt : Fin k → ℝ) (i : Fin n) : ℝ :=
  compensation alloc d tt i + roundedBonus δ alloc d tt i

/-- The strategy class named in the proof of Theorem 5.9 (p. 193): agent `i` of true type `ti`
declares `di` with the same rounded value as `ti`, and for every decision `x` executes each of its
own tasks in a time whose rounded value equals the rounded true time, so that after rounding its
corrected time vector equals `corr*`. -/
def RoundsLikeTruth {n k : ℕ} (δ : ℝ) (i : Fin n) (ti di : Fin k → ℝ) (ei : ExecPlan n k) :
    Prop :=
  roundVec δ di = roundVec δ ti ∧
    ∀ (x : Fin k → Fin n) (j : Fin k), x j = i → roundUp δ (ei x j) = roundUp δ (ti j)

end AlgMechDesign.Rounding


