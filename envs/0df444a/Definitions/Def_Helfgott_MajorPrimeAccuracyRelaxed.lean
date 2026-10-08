-- Prove2me | Definitions.Def_Helfgott_MajorPrimeAccuracyRelaxed
-- name    : Helfgott_MajorPrimeAccuracyRelaxed
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-06T02:39:21.852449+00:00
-- url     : https://prove2.me/theorems/6338d316-6b71-4a8b-85b4-4dd9467a2545
-- title:
--   Actual Goldbach major-arc prime accuracy with a seventeenfold etaPlus allowance
-- statement:
--   Let $N\ge10^{27}$ and $x=N/(2+9/(196\sqrt{2\pi}))$. On every full actual major arc assume that the $\eta_+$ prime sum differs from its exact rational Fourier main term by at most $17\cdot10^{-7}x$, and the $\eta_*$ sum by at most $2\cdot10^{-8}x$. Then the original three-prime mission error satisfies
--   $$\left|\int_{\mathfrak M(8,150000,x)}S_{\eta_+}(\alpha,x)^2S_{\eta_*}(\alpha,x)e(-N\alpha)\,d\alpha-x^2M_{N,150000}\!\left(2+\frac9{196\sqrt{2\pi}}\right)\right|\le\frac{0.013}{49}x^2.$$
--   The full odd/even denominator and radius ranges are included. This improves the sufficient $\eta_+$ accuracy allowance by a factor of seventeen while preserving the original challenge conclusion. The remaining actual prime approximation is an explicit hypothesis, not asserted as proved.
-- source:
--   Helfgott, Major arcs for Goldbach, https://arxiv.org/abs/1305.2897. Sharper complete dyadic arithmetic moments and direct integrated cubic error. Written by Codex.

import Definitions.Def_Helfgott_ArcCounting
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.GCD.Basic

open MeasureTheory Set Finset
open scoped BigOperators

namespace Helfgott

noncomputable def majorPrimeAccuracyRelaxed (x : ℝ) : Prop :=
  let D := (Finset.Icc 1 150000).filter (fun q => Odd q) ∪
    (Finset.Icc 1 300000).filter (fun q => Even q)
  let R : ℕ → ℝ := fun q => if Odd q then 600000/(q : ℝ) else 1200000/(q : ℝ)
  ∀ q ∈ D, ∀ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    ∀ β ∈ Icc (-(R q)) (R q),
      ‖coordinatedExpSum etaPlus x
        (((a : ℝ)/(q : ℝ)+β/x : ℝ) : AddCircle (1 : ℝ))-
        (((ArithmeticFunction.moebius q : ℤ) : ℂ)/(Nat.totient q : ℂ))*
          ((x : ℂ)*FourierTransform.fourier (fun t : ℝ => (etaPlus t : ℂ)) (-β))‖ ≤ 17*x/10^7 ∧
      ‖coordinatedExpSum etaStar x
        (((a : ℝ)/(q : ℝ)+β/x : ℝ) : AddCircle (1 : ℝ))-
        (((ArithmeticFunction.moebius q : ℤ) : ℂ)/(Nat.totient q : ℂ))*
          ((x : ℂ)*FourierTransform.fourier (fun t : ℝ => (etaStar t : ℂ)) (-β))‖ ≤ 2*x/10^8

end Helfgott


