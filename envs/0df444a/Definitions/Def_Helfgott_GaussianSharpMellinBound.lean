-- Prove2me | Definitions.Def_Helfgott_GaussianSharpMellinBound
-- name    : Helfgott_GaussianSharpMellinBound
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-06T01:03:16.570846+00:00
-- url     : https://prove2.me/theorems/91f3c140-1e34-45fd-9318-e9a7a4abfca9
-- title:
--   Sharp full contour bound for the actual phase-twisted Gaussian Mellin transform
-- statement:
--   Let $\phi(u)=u^2\exp(-u^2/2)$, $-3/2\le\sigma\le0$, $\omega,t\in\mathbb R$, $0\le\theta\le1/4$ and $4/5\le c\le\cos(2\theta)$. Then
--   $$|\mathcal M[\phi(u)\exp(i\omega u)](\sigma+it)|\le\left(5+\frac{3|\omega|\theta}{c}\right)\exp\left(-\theta|t|+\frac{\omega^2\theta^2}{2c}\right).$$
--   The bound retains the complete Gaussian tails. It supplies the sharp Gaussian estimate underlying the actual etaPlus conductor-dependent high-zero proof.
-- source:
--   Helfgott, Major arcs for Goldbach, https://arxiv.org/abs/1305.2897. Original complete numerical and analytic bounds built on Mathlib Gaussian, Fourier and Mellin analysis. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.MellinTransform
open MeasureTheory Set Complex

namespace Helfgott

def GaussianSharpMellinBound : Prop :=
  ∀ (σ ω t θ c : ℝ)
    (hσl : -(3/2 : ℝ)≤σ) (hσu : σ≤0) (hθ0 : 0≤θ) (hθ : θ≤1/4)
    (hc : (4/5 : ℝ)≤c) (hcos : c≤Real.cos (2*θ)),
    ‖mellin (fun u : ℝ => (phi u : ℂ)*Complex.exp (I*(ω : ℂ)*(u : ℂ)))
      ((σ : ℂ)+(t : ℂ)*I)‖≤
      (5+3*|ω| *θ/c)*Real.exp (-θ*|t|+ω^2*θ^2/(2*c))

end Helfgott


