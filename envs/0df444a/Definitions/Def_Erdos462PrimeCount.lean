-- Prove2me | Definitions.Def_Erdos462PrimeCount
-- name    : Erdos462PrimeCount
-- status  : Definition
-- author  : @adamhenr
-- created : 2026-11-21T09:06:14.896234+00:00
-- url     : https://prove2.me/theorems/6aa6456b-2aa7-45fd-8b0b-3f366691af01
-- title:
--   Prime counts in a half-open interval
-- statement:
--   For real $s,h$, let $A_h(s)$ be the number of primes $p$ with $s<p\le s+h$. The count is viewed as a real number for integration. For $s\ge0$ and $h\ge0$ this equals $\pi(s+h)-\pi(s)$.
-- source:
--   Adam Henriksson, Balanced semiprimes in short intervals under the Riemann hypothesis. Lemma 3.1.

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Chebyshev

namespace Erdos462RH
noncomputable def primeCountWindow (s h : ℝ) : ℝ :=
  (((Finset.Ioc ⌊s⌋₊ ⌊s+h⌋₊).filter Nat.Prime).card : ℝ)
end Erdos462RH


