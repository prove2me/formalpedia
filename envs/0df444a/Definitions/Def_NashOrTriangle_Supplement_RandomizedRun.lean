-- Prove2me | Definitions.Def_NashOrTriangle_Supplement_RandomizedRun
-- name    : NashOrTriangle_Supplement_RandomizedRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:47:13.458481+00:00
-- url     : https://prove2.me/theorems/c625e82c-2367-4c3b-b703-f4e993ea5f4b
-- title:
--   Random bits, failure reports and running time of randomized oracle algorithms
-- statement:
--   A **randomized algorithm** of the oracle model is a program of the published oracle machine that reads its input and an infinite sequence of random bits $\omega=(\omega_0,\omega_1,\dots)$ from memory: cell $0$ holds $r$, cell $1$ holds $k$, and cell $-(i+1)$ holds $\omega_i\in\{0,1\}$. The bits are independent fair coins; their law is the infinite product of the uniform distribution on $\{0,1\}$.
--
--   A halted run **reports failure** if the cell at its output address holds the tag $2$ (the tags $0$ and $1$ are a strategy pair and a triangle). The **running time** of a run is its number of executed instructions (oracle calls included) at the moment it halts, and $+\infty$ if it never halts.
--
--   These are the objects in which the Monte Carlo and Las Vegas guarantees of Theorem 5.1 are stated.
--
--   **Formalization Note** The running time is an extended natural number, so that its expectation is defined even when the run may fail to halt.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962cc2efb135d3833e902fa4e861e03acf9d2df3fe8140a50b646da66f7), Theorem 5.1, p.12 (PDF p.13) and its proof, p.16 (PDF p.17)

import Mathlib
import Definitions.Def_NashOrTriangle_OracleMachine

namespace NashOrTriangle.Supplement

open MeasureTheory

/-- The input memory of the randomized algorithms of Theorem 5.1: cell `0` holds `r`, cell `1`
holds `k`, and the random bits `ω 0, ω 1, …` are written to cells `−1, −2, …` (cell `−(i + 1)`
holds `1` if `ω i` and `0` otherwise); every other cell holds `0`.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Theorem 5.1, printed p. 12 (PDF p. 13):
"given integer r ≥ 0 and k ≥ 2"; printed p. 16 (PDF p. 17): "each perturbation exactly sampleable
using log2 L fair random bits".

**Formalization Note** The algorithm of the published oracle machine reads its random bits from
the memory; the bits are infinitely many, so a restart with fresh bits is possible. -/
noncomputable def inputRK (r k : ℕ) (ω : ℕ → Bool) : ℤ → ℝ :=
  fun i => if i = 0 then (r : ℝ) else if i = 1 then (k : ℝ) else
    if i < 0 then (if ω (-i - 1).toNat then 1 else 0) else 0

/-- The law of the random bits: independent fair coins, the infinite product of the uniform
measure on `Bool`.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), proof of Theorem 5.1, printed p. 16
(PDF p. 17): "fair random bits". -/
noncomputable def coinMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure

/-- The halted state reports **failure**: its output address holds the tag `2` (the published
`decode` reserves the tags `0` for a pair and `1` for a triangle).

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Theorem 5.1, printed p. 12 (PDF p. 13):
"or reports failure". -/
def IsFailureReport {A B : Type*} (s : State A B) : Prop :=
  ∃ base : ℤ, s.output = some base ∧ s.core.mem base = 2

/-- The running time of the run of `P` on game `M` with oracle `adv` from input `x`: the value of
the published counter `work` (every executed instruction, oracle calls included) at the first
halted state, and `⊤` if the run never halts.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Theorem 5.1, printed p. 12 (PDF p. 13):
"in expected time polynomial in r and k".

**Formalization Note** Halted states stutter with no further work, so the value is the work of
the whole run. -/
noncomputable def haltWork {A B : Type*} (P : Program) (M : A → B → ℚ) {δ : ℝ}
    (adv : BRAdversary M δ) (x : ℤ → ℝ) : ℕ∞ := by
  classical
  exact if h : ∃ n, (run P M adv x n).output.isSome then
    ((run P M adv x (Nat.find h)).work : ℕ∞) else ⊤

end NashOrTriangle.Supplement


