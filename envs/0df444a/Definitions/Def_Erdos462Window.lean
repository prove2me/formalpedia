-- Prove2me | Definitions.Def_Erdos462Window
-- name    : Erdos462Window
-- status  : Definition
-- author  : @adamhenr
-- created : 2026-11-21T09:05:30.63471+00:00
-- url     : https://prove2.me/theorems/6382b925-8845-4762-9cbe-28fe5f4e488b
-- title:
--   Short windows and least-prime-factor mass
-- statement:
--   For $C>0$ and $x>1$, put $H_C(x)=C\sqrt{x}(\log x)^2$. The integer window includes both endpoints. For composite $n$ its weight is $P^-(n)/n$, where $P^-(n)$ is its least prime factor. The sum of these weights over the window is $\mu_C(x)$.
-- source:
--   Adam Henriksson, Balanced semiprimes in short intervals under the Riemann hypothesis. Section 1, definition of the composite sum.

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Chebyshev

namespace Erdos462RH
open scoped BigOperators
noncomputable def width (C x : ℝ) : ℝ := C * Real.sqrt x * (Real.log x)^2
noncomputable def window (C x : ℝ) : Finset ℕ :=
  Finset.Icc ⌈x⌉₊ ⌊x + width C x⌋₊
noncomputable def weight (n : ℕ) : ℝ := (n.minFac : ℝ) / n
def Composite (n : ℕ) : Prop := 2 ≤ n ∧ ¬ n.Prime
noncomputable def composites (C x : ℝ) : Finset ℕ := by
  classical exact (window C x).filter Composite
noncomputable def compositeMass (C x : ℝ) : ℝ :=
  ∑ n ∈ composites C x, weight n
end Erdos462RH


