-- Prove2me | Definitions.Def_Erdos462Selberg
-- name    : Erdos462Selberg
-- status  : Definition
-- author  : @adamhenr
-- created : 2026-11-21T09:06:03.252197+00:00
-- url     : https://prove2.me/theorems/e2087ed7-d20f-42ca-8ab1-599a267f13f8
-- title:
--   The relative Selberg integral and its two factor scales
-- statement:
--   For the Chebyshev function $\theta$, put $J_\theta(Y,d)=\int_1^Y(\theta((1+d)v)-\theta(v)-dv)^2\,dv$. The published estimate bounds this quantity for $Y\ge10^{13}$ and $0<d\le 10^{-13}$. The two-scale estimate specializes to $d=512(\log N)^2/N$ and $Y\in\{2N,2N/3\}$.
-- source:
--   Adam Henriksson, Balanced semiprimes in short intervals under the Riemann hypothesis. Section 2, equations (1)–(2). A. Chirre and M. V. Hagen, On Goldbach numbers in short intervals, Theorem 3, https://doi.org/10.1007/s40993-026-00767-6.

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Chebyshev

namespace Erdos462RH
noncomputable def squareError (d v : ℝ) : ℝ :=
  (Chebyshev.theta ((1+d)*v) - Chebyshev.theta v - d*v)^2
noncomputable def Jtheta (Y d : ℝ) : ℝ := ∫ v in (1 : ℝ)..Y, squareError d v
def SelbergBound : Prop :=
  ∀ Y d : ℝ, 10^13 ≤ Y → 0 < d → d ≤ 1/10^13 →
    Jtheta Y d ≤ (25571/10000 : ℝ) * d * Y^2 * Real.log ((20001/10000 : ℝ)/d)^2
noncomputable def delta (N : ℝ) : ℝ := 512*(Real.log N)^2/N
def TwoScaleBound : Prop := ∀ N : ℝ, 9797*10^15 ≤ N →
  ∀ Y ∈ ({2*N, 2*N/3} : Set ℝ),
    Jtheta Y (delta N) ≤ 3*(delta N)*Y^2*(Real.log N)^2
end Erdos462RH


