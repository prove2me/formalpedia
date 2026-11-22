-- Prove2me | Definitions.Def_SamplingLLL_Supplement_peelCore
-- name    : SamplingLLL_Supplement_peelCore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:55:39.891841+00:00
-- url     : https://prove2.me/theorems/03dc4f0f-c90f-4505-8a4b-8f3707c35ddc
-- title:
--   Random scopes with adversarial signs (Definition 2.17), peeling and closure, and the algorithm $A_k$
-- statement:
--   1. **The random model (Definition 2.17).** `scopeProb n m k E` is the probability of the event $E$ when $m$ clause scopes are chosen independently and uniformly from the $k$-subsets of $[n]$. The literal signs are assigned arbitrarily afterwards and are not part of the random choice.
--   2. **Peeling and closure (p.57).** From the input compute $\alpha=m/n$ and the seed threshold $\Delta=\lceil A_{\mathrm{seed}}(\alpha k+k\log k)\rceil$. Select every seed, i.e. every variable of degree at least $\Delta$. Whenever a clause contains at least two distinct selected variables, select all its variables; continue until no further selection is possible. $U$ is the set of selected variables.
--   3. **The algorithm $A_k$ (p.66).** Perform the peeling and closure and run the sampler and the FPRAS of Theorem F.6 on the resulting decomposition with $a_{\mathrm{blk}}=d/8$, $d=1+k\Delta$, and $\beta=4$.
--
--   **Formalization Note** $\log$ is the natural logarithm and $A_{\mathrm{seed}}$ a natural number. The closure is $n$ rounds of the one-round rule, which suffices because every effective round selects a new variable. The peeling and closure are charged $N_0^3$ ticks. `scopeProb` is a ratio of cardinalities and is $0$ when there is no $k$-subset.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Definition 2.17 and Theorem 2.18, p.10; F.6, p.57; proof of Theorem 2.18, pp.65–66

import Mathlib
import Definitions.Def_SamplingLLL_Supplement_coreSample

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL.Supplement

open Proc

/-! # Random scopes with adversarial signs: the model of Definition 2.17 and the algorithm `A_k`

Source: Achlioptas, *Counting and Sampling by Local Repair*, STOC 2027 submission (manuscript sha256
7a943167…), Definition 2.17 and Theorem 2.18, p.10; the peeling and closure of F.6, p.57; the proof of
Theorem 2.18, pp.65–66 ("The algorithm `A_k` computes `α = m/n` and `∆` from the input, performs the peeling
and closure, and runs the algorithms of Theorem F.6 with `a_blk = d/8` and `β = 4`"). -/

/-- Definition 2.17, p.10: the probability of an event under `m` clause scopes chosen independently and
uniformly from the `k`-subsets of `[n]`. The literal signs are not part of the random choice. -/
noncomputable def scopeProb (n m k : ℕ) (E : (Fin m → Finset (Fin n)) → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter fun scope : Fin m → Finset (Fin n) =>
      (∀ j, (scope j).card = k) ∧ E scope).card : ℝ) /
    (Finset.univ.filter fun scope : Fin m → Finset (Fin n) => ∀ j, (scope j).card = k).card

/-- The seed threshold `∆ = ⌈A_seed (αk + k log k)⌉` with `α = m/n` computed from the input (p.57, p.66);
`log` is the natural logarithm. -/
noncomputable def seedDelta (Aseed k n m : ℕ) : ℕ :=
  ⌈(Aseed : ℝ) * ((m : ℝ) / n * k + k * Real.log k)⌉₊

/-- One round of the closure (p.57): select all the variables of every clause containing at least two
distinct selected variables. -/
def closeStep {n m : ℕ} (scope : Fin m → Finset (Fin n)) (S : Finset (Fin n)) : Finset (Fin n) :=
  S ∪ (Finset.univ.filter fun c => 2 ≤ (scope c ∩ S).card).biUnion scope

/-- The peeling and closure of p.57: select every seed (a variable of degree at least `∆`), then close
until no further selection is possible (`n` rounds suffice, since every effective round selects a new
variable). The result is the decomposition with `U` the selected variables. -/
noncomputable def peelCore {n m : ℕ} (Aseed k : ℕ) (scope : Fin m → Finset (Fin n)) : Core n m where
  scope := scope
  U := (closeStep scope)^[n]
    (Finset.univ.filter fun v =>
      seedDelta Aseed k n m ≤ (Finset.univ.filter fun c => v ∈ scope c).card)

/-- `a_blk = d/8` with `d = 1 + k∆` (p.66). -/
noncomputable def akAblk (Aseed k n m : ℕ) : ℝ := (1 + (k : ℝ) * seedDelta Aseed k n m) / 8

/-- The sampler of `A_k` (p.66): compute `∆`, perform the peeling and closure (charged `N₀³`), and run the
sampler of Theorem F.6 with `β = 4`. -/
noncomputable def akSample {n m : ℕ} (k Aseed Ccore : ℕ) (scope : Fin m → Finset (Fin n))
    (sgn : Fin m → Fin n → Bool) (ε : ℚ) : Proc (kcnf scope sgn).toCSP.Config := do
  tick ((n + m + 2) ^ 3)
  (peelCore Aseed k scope).coreSample sgn k 4 Ccore Finset.univ ε

/-- The counter of `A_k` (p.66): compute `∆`, perform the peeling and closure (charged `N₀³`), and run the
FPRAS of Theorem F.6 with `a_blk = d/8` and `β = 4`. -/
noncomputable def akCount {n m : ℕ} (k Aseed Ccore K e : ℕ) (scope : Fin m → Finset (Fin n))
    (sgn : Fin m → Fin n → Bool) (ε : ℚ) : Proc ℚ := do
  tick ((n + m + 2) ^ 3)
  (peelCore Aseed k scope).coreCount sgn k (akAblk Aseed k n m) 4 Ccore K e ε

end SamplingLLL.Supplement


