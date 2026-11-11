-- Prove2me | Definitions.Def_RandKSATSample_Main_Sampler
-- name    : RandKSATSample_Main_Sampler
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:59:22.036207+00:00
-- url     : https://prove2.me/theorems/96b88f57-93d7-4a21-9d15-f0b2c6f979b2
-- title:
--   Samplers on the randomized log-cost RAM: the input encoding of Φ, the binary-digit oracle for ε with fair bits, the output encoding and the output law
-- statement:
--   Programs run on the published randomized log-cost oracle RAM (`PDSEquiv.Machine`). On input $(\Phi,\varepsilon)$:
--   - the formula is in memory as $[n,m,k]$ followed by the $km$ literals, clause by clause, the literal $(v,\text{sign})$ written as $2v+1$ if positive and $2v$ if negative;
--   - the tolerance $\varepsilon$ is read through the oracle: the query $[0,j]$ returns $[\lfloor 2^j\varepsilon\rfloor\bmod 2]$, the $j$-th binary digit of $\varepsilon$ after the binary point (terminating expansion for dyadic $\varepsilon$, as in §6.2); the query $[1]$ returns a fresh fair bit; any other query returns $[\,]$;
--   - an output assignment is the list of its $n$ values in $\{0,1\}$.
--
--   The output law of a program $P$ is
--   $$\mathrm{Law}(X)(\sigma)=\Pr[P\text{ halts on }(\Phi,\varepsilon)\text{ with output the encoding of }\sigma].$$
--
--   **Formalization Note.** Randomness comes only from the oracle's fair bits when the program is `GenCountSampleLLL.Admissible` (no exact-Bernoulli instruction). Every instruction, query and reply is charged by the bit lengths involved (log-cost), which is within polylogarithmic factors of the paper's count of bit operations (p. 40).
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), p. 5 (Theorem 1.1), p. 40, §6.2 p. 59, p. 63

import Mathlib
import Definitions.Def_RandKSATSample_Main_Formula
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_GenCountSampleLLL_csOracle

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace RandKSATSample.Main

noncomputable section

open Classical

/-!
# Samplers on the randomized log-cost RAM: input encoding, the `ε` oracle, the output law

He, Li, Yang, *Fast Almost-Uniform Sampling of Random k-SAT Solutions*, arXiv:2610.10474
(version not printed; file sha256 563a4d84…), p. 5 (Theorem 1.1: input `(Φ, ε)`), p. 40 (cost is
the number of bit operations), p. 59 (§6.2: `ε` in binary fractional notation, terminating
expansion for dyadic inputs), p. 63 (fair bits).

**Formalization Note.** Programs run on the published randomized log-cost oracle RAM
`PDSEquiv.Machine`. Randomness comes only from fair bits of the oracle (programs are
`GenCountSampleLLL.Admissible`: no exact-Bernoulli instruction). The formula is in memory,
explicitly encoded; the tolerance `ε` is read digit by digit from the oracle.
-/

variable {n m k : ℕ}

/-- The input encoding of `Φ`: `[n, m, k]` followed by the `km` literals, clause by clause and
position by position, the literal `(v, sign)` written as `2v + 1` if positive and `2v` if
negative. -/
def encFormula (Φ : Formula n m k) : List ℕ :=
  [n, m, k] ++ (List.ofFn fun a : Fin m =>
    List.ofFn fun i : Fin k => 2 * ((Φ a i).1 : ℕ) + if (Φ a i).2 then 1 else 0).flatten

/-- The oracle for the tolerance `ε`: the query `[0, j]` returns `[⌊2^j ε⌋ mod 2]`, the `j`-th
binary digit of `ε` after the binary point (the terminating expansion for dyadic `ε`); the query
`[1]` returns a fair bit `[0]` or `[1]`, fresh at every call; every other query returns `[]`. -/
def epsOracle (ε : ℝ) : PDSEquiv.Oracle := fun q =>
  match q with
  | [0, j] => PMF.pure [⌊(2 : ℝ) ^ j * ε⌋₊ % 2]
  | [1] => (PMF.uniformOfFintype Bool).map fun b => [if b then 1 else 0]
  | _ => PMF.pure []

/-- The output encoding of an assignment: its `n` values as `0/1`, variable `0` first. -/
def encAssign (σ : Assignment n) : List ℕ := List.ofFn fun v : Fin n => if σ v then 1 else 0

/-- The output law of program `P` on input `(Φ, ε)`: the probability that it halts with output
the encoding of `σ`. -/
def outLaw (P : PDSEquiv.Program) (ε : ℝ) (Φ : Formula n m k) (σ : Assignment n) : ℝ :=
  PDSEquiv.outMass P (epsOracle ε) (encFormula Φ) (encAssign σ)

end

end RandKSATSample.Main


