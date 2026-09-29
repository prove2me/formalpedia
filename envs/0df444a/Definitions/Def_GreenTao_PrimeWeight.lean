-- Prove2me | Definitions.Def_GreenTao_PrimeWeight
-- name    : GreenTao_PrimeWeight
-- status  : Definition
-- author  : @davidnet
-- created : 2026-09-06T02:29:08.094702+00:00
-- url     : https://prove2.me/theorems/5165fc0f-c142-4060-b305-371374476f55
-- title:
--   Scaled prime-only W-tricked weight on a short interval
-- statement:
--   For an integer $k$, put
--
--   $$\epsilon_k=\frac1{2^k(k+4)!},\qquad a_k=\frac1{k2^{k+5}}.$$
--
--   For a positive integer $m$, a natural number $W$, and $x\in\mathbb Z/m\mathbb Z$ with natural representative $\bar x\in\{0,\ldots,m-1\}$, define
--
--   $$F_{k,W,m}(x)=\begin{cases}a_k\dfrac{\phi(W)}W\log(W\bar x+1),&W\bar x+1\text{ is prime and }\epsilon_km\le\bar x\le2\epsilon_km,\\0,&\text{otherwise.}\end{cases}$$
--
--   Here $\phi$ is Euler's totient function. This is the weight used immediately after Proposition 9.1 to combine the prime majorant with relative Szemerédi. Prime powers other than primes receive zero weight. The definitions are total in Lean, while the applications assume $k\ge3$ and $W>0$.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §9, the displayed definition of the modified von Mangoldt function before Proposition 9.1; the constants in Proposition 9.1; and the definition of f at the start of the proof of Theorem 1.1 assuming Proposition 9.1.

import Definitions.Def_GreenTao_Pseudorandom
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace GreenTao

/-- The short-interval parameter in Green--Tao Proposition 9.1. -/
noncomputable def primeInterval (k : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ k * (Nat.factorial (k + 4) : ℝ))

/-- The scaling factor in Green--Tao Proposition 9.1. -/
noncomputable def primeScale (k : ℕ) : ℝ :=
  1 / ((k : ℝ) * (2 : ℝ) ^ (k + 5))

/-- The prime-only modified von Mangoldt weight from the start of §9,
scaled and restricted to the interval used after Proposition 9.1. -/
noncomputable def primeWeight (k W : ℕ) {m : ℕ+} (x : ZMod (m : ℕ)) : ℝ :=
  if Nat.Prime (W * x.val + 1) ∧
      primeInterval k * (m : ℝ) ≤ (x.val : ℝ) ∧
      (x.val : ℝ) ≤ 2 * primeInterval k * (m : ℝ) then
    primeScale k * ((Nat.totient W : ℝ) / (W : ℝ)) *
      Real.log (W * x.val + 1 : ℕ)
  else 0

end GreenTao


