-- Prove2me | Definitions.Def_Helfgott_MajorPrimeAccuracy
-- name    : Helfgott_MajorPrimeAccuracy
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-05T20:38:14.661713+00:00
-- url     : https://prove2.me/theorems/7859c6ce-e2a0-4750-a664-b9f586e1d17c
-- title:
--   Uniform actual prime-sum accuracy on the full coordinated major arcs
-- statement:
--   At scale $x$, this predicate states uniform rational-arc approximation estimates for the actual coordinated von Mangoldt exponential sums. It covers every odd denominator $q\le150000$, every even denominator $q\le300000$, every reduced residue $a$, and every scaled phase in $[-R_q,R_q]$, where $R_q=600000/q$ for odd $q$ and $1200000/q$ for even $q$. The reference main sum is $(\mu(q)/\varphi(q))x\widehat\eta(-\beta)$. The errors are at most $10^{-7}x$ for the actual band-limited smoothing $\eta_+$ and $2\cdot10^{-8}x$ for the actual Mellin smoothing $\eta_*$. All original infinite smoothing tails and prime powers remain. This is a pure predicate: it does not assert that the estimates hold. The estimates themselves are a separate numerical analytic obligation.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, §§3.4 and 7.1–7.2. These deliberately coarse tolerances define sufficient quantitative inputs for a direct reduction to the mission prime-major-model error. Written by Codex.

import Definitions.Def_Helfgott_ArcCounting
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.GCD.Basic

open MeasureTheory Set Finset
open scoped BigOperators

namespace Helfgott

noncomputable def majorPrimeAccuracy (x : ℝ) : Prop :=
  let D := (Finset.Icc 1 150000).filter (fun q => Odd q) ∪
    (Finset.Icc 1 300000).filter (fun q => Even q)
  let R : ℕ → ℝ := fun q => if Odd q then 600000/(q : ℝ) else 1200000/(q : ℝ)
  ∀ q ∈ D, ∀ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    ∀ β ∈ Icc (-(R q)) (R q),
      ‖coordinatedExpSum etaPlus x
        (((a : ℝ)/(q : ℝ)+β/x : ℝ) : AddCircle (1 : ℝ))-
        (((ArithmeticFunction.moebius q : ℤ) : ℂ)/(Nat.totient q : ℂ))*
          ((x : ℂ)*FourierTransform.fourier (fun t : ℝ => (etaPlus t : ℂ)) (-β))‖ ≤ x/10^7 ∧
      ‖coordinatedExpSum etaStar x
        (((a : ℝ)/(q : ℝ)+β/x : ℝ) : AddCircle (1 : ℝ))-
        (((ArithmeticFunction.moebius q : ℤ) : ℂ)/(Nat.totient q : ℂ))*
          ((x : ℂ)*FourierTransform.fourier (fun t : ℝ => (etaStar t : ℂ)) (-β))‖ ≤ 2*x/10^8

end Helfgott


