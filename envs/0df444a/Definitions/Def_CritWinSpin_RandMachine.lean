-- Prove2me | Definitions.Def_CritWinSpin_RandMachine
-- name    : CritWinSpin_RandMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:34:42.482647+00:00
-- url     : https://prove2.me/theorems/5cda6ee0-a131-4eea-870e-d8c821f8c55d
-- title:
--   Randomized multi-stack Turing machine with a worst-case step bound
-- statement:
--   A **randomized machine** is a deterministic Mathlib `TM2` machine over the alphabet $\{0,1\}$ together with functions $\mathrm{coins}$ and $\mathrm{time}$ on input strings. On input $x$ a uniformly random coin string $\omega\in\{0,1\}^{\mathrm{coins}(x)}$ is drawn; the machine started on the code of $(\omega,x)$ halts within $\mathrm{time}(x)$ steps, for **every** coin string. A second `TM2` machine computes $\mathrm{coins}(x)$ from $x$ within the same bound. The **output law** on input $x$, read through a decoder, is the uniform average over $\omega$.
--
--   This is the machine model of the sampling upper bound.
--
--   **Formalization Note** The paper names no machine model; polynomial simulations between models are absorbed by the polynomial factor of the running time, and its algorithm has no unbounded loop, so worst-case time is the right notion. The step count is Mathlib's `TM2OutputsInTime`. The second machine keeps the sampler uniform: the machine can read the length of its coin string, so an arbitrary function $\mathrm{coins}$ would otherwise act as advice.
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Theorem 1.1(i), p.2; §4.2, pp.16–17

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QuantumPRC_IsPolyFamily
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
set_option autoImplicit false

namespace CritWinSpin

/-- **A randomized multi-stack Turing machine with a worst-case step bound** (the machine model of
Theorem 1.1(i), p.2, and Theorem 4.4, p.17).

`tm` is a Mathlib `TM2` machine over the alphabet `Bool`. On input `x` the machine draws a uniformly
random coin string `ω ∈ {0,1}^{coins x}`, is started on `tupleCode [ω, x]`, and halts with output
`run (tupleCode [ω, x])` within `time x` steps, for **every** coin string. A second `TM2` machine
`coinTm` computes the number of coins from `x` within the same step bound.

Source: Liu–Zhang–Ren, STOC 2027 submission (manuscript sha256 f77584da…), Theorem 1.1(i), p.2;
§4.2, pp.16–17.

**Formalization Note.** The paper names no machine model. A randomized machine is a deterministic
`TM2` machine run on its input together with a uniformly random coin string; the step bound is
worst case over coin strings (the paper's algorithm runs `Q` trials of `T_Mix` steps with no
unbounded loop). Polynomial-time simulations between machine models are absorbed by the
`poly(N, B, η^{-1})` factor of (2). The step count is Mathlib's `TM2OutputsInTime`, so no
oracle and no hand-rolled clock is involved. `coinTm` keeps the machine uniform: the length of the
coin string is visible to `tm`, so an arbitrary function `coins` would otherwise act as advice
depending on `x`. -/
structure RandMachine where
  /-- The underlying `TM2` machine, with input and output alphabets identified with `Bool`. -/
  tm : Turing.TM2ComputableAux Bool Bool
  /-- The output on a given coins-and-input string. -/
  run : Str → Str
  /-- The number of coins drawn on input `x`. -/
  coins : Str → ℕ
  /-- The worst-case number of steps on input `x`. -/
  time : Str → ℕ
  /-- For every coin string of the right length, `tm` halts with output `run (tupleCode [ω, x])`
  within `time x` steps. -/
  halts : ∀ (x ω : Str), ω.length = coins x →
    Nonempty (Turing.TM2OutputsInTime tm.tm ((tupleCode [ω, x]).map tm.inputAlphabet.invFun)
      (some ((run (tupleCode [ω, x])).map tm.outputAlphabet.invFun)) (time x))
  /-- The machine that computes the number of coins. -/
  coinTm : Turing.TM2ComputableAux Bool Bool
  /-- `coinTm` outputs `coins x` in binary within `time x` steps. -/
  coins_computed : ∀ x : Str,
    Nonempty (Turing.TM2OutputsInTime coinTm.tm (x.map coinTm.inputAlphabet.invFun)
      (some ((encBin (coins x)).map coinTm.outputAlphabet.invFun)) (time x))
  /-- Reading the coins takes time. -/
  coins_le : ∀ x, coins x ≤ time x

open Classical in
/-- The output law of a randomized machine on input `x`, decoded by `dec`:
`P[dec(output) = y] = 2^{-coins x} · #{ω : dec(run(tupleCode [ω, x])) = y}`. -/
noncomputable def outLaw {β : Type} (M : RandMachine) (x : Str) (dec : Str → Option β)
    (y : Option β) : ℝ :=
  (1 / (2 : ℝ) ^ M.coins x) * ∑ ω : Fin (M.coins x) → Bool,
    if dec (M.run (tupleCode [List.ofFn ω, x])) = y then (1 : ℝ) else 0

end CritWinSpin


