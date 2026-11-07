-- Prove2me | Definitions.Def_SubexpPrimes_RunsWithin
-- name    : SubexpPrimes_RunsWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:56:40.408701+00:00
-- url     : https://prove2.me/theorems/519dd13d-7199-4cd6-86d6-9adc10ce77c1
-- title:
--   A machine run within time $\tau$ and space $\sigma$
-- statement:
--   A machine $A$ **runs within** time $\tau$ and space $\sigma$ on an input, with a given output, if started on the input it reaches, after at most $\tau$ steps, a halted configuration whose designated tape holds exactly the output with the head on its first cell, and every configuration of the run has visited at most $\sigma$ cells in total.
--
--   This file also fixes the words of integers and dyadic numbers (a sign bit, then binary digits, least significant first), and the two bounds that read $\mathrm{poly}(u)$ and $\mathrm{poly}(u)\,E(s)$:
--
--   $$
--   K(u+1)^K,\qquad K(u+1)^K\,2^{Ks/\sqrt{\log_2 s}} .
--   $$
--
--   **Formalization Note** The model is the published `SubexponentialSAT` one: a deterministic multitape machine, whose space count includes the input tape. Since the bounds are used at $s\ge2$, the logarithm is at least $1$ there.
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Theorem 1, p.4; Theorem 2.5, p.15; Notation, p.13

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **A run within time `τ` and space `σ`** — the machine reading of "deterministically compute
… in time … and space …" in Gajulapalli, *Deterministic Construction of Primes in Subexponential
Time* (manuscript, sha256 6ad4d3de…), Theorem 1, p.4, and Theorem 2.5, p.15.

Started on `input`, the machine `A` reaches after some `time ≤ τ` steps a halted configuration
whose tape `out` holds exactly `output` (head on its first cell), and every configuration reached
in at most `time` steps has visited at most `σ` cells in total.

**Formalization Note.** The paper names no machine model. The model is the published
`SubexponentialSAT` one: `PrimitiveMachine` (a deterministic multitape machine over
`Option Bool`), `locatedStep`, and `visitedSpace`, which sums the visited cells of all tapes,
input tape included. So every space bound must cover the input length. -/
def RunsWithin (A : PrimitiveMachine) (out : Fin A.tapeCount) (input output : List Bool)
    (τ σ : ℝ) : Prop :=
  ∃ (time : ℕ) (final : LocatedCfg A),
    Trace (locatedStep A) time (locatedInit A input) final ∧
    (∃ b : Bool, final.config.state = Sum.inl b) ∧
    final.config.tapes out = Turing.Tape.mk₁ (output.map some) ∧
    (time : ℝ) ≤ τ ∧
    ∀ (k : ℕ) (c : LocatedCfg A), k ≤ time →
      Trace (locatedStep A) k (locatedInit A input) c → (visitedSpace c : ℝ) ≤ σ

/-- A polynomial bound with one constant: `K (u + 1)^K`, the reading of `poly(u)`. The `+ 1` keeps
it positive at `u = 0`. -/
noncomputable def polyBound (K u : ℕ) : ℝ := (K : ℝ) * ((u : ℝ) + 1) ^ K

/-- The running time `poly(u) E(s)`, where `E(s) = 2^{O(s/√log s)}` (p.13), with one constant:
`K (u + 1)^K 2^{K s / √(log₂ s)}`. It is used at `s ≥ 2`, where `log₂ s ≥ 1`. -/
noncomputable def subexpBound (K u s : ℕ) : ℝ :=
  (K : ℝ) * ((u : ℝ) + 1) ^ K * (2 : ℝ) ^ ((K : ℝ) * (s : ℝ) / Real.sqrt (Real.logb 2 (s : ℝ)))

/-- The output word of an integer: its sign bit (`true` when negative), then `|k|` in binary,
least significant bit first (`countWord`). -/
def intWord (k : ℤ) : List Bool := decide (k < 0) :: countWord k.natAbs

/-- The output word of the dyadic number `k / 2^j`: the integer `k` and the exponent `j`. -/
def dyadicWord (k : ℤ) (j : ℕ) : List Bool :=
  Encoding.encodeList id [intWord k, Encoding.encodeNat j]

end SubexpPrimes


