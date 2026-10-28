-- Prove2me | Definitions.Def_TaoFivePrimes_RHDirectOscillatoryQuadrature
-- name    : TaoFivePrimes_RHDirectOscillatoryQuadrature
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:25:35.418009+00:00
-- url     : https://prove2.me/theorems/804b334a-c415-41ec-9b5c-afb0edcde181
-- title:
--   Exact direct oscillatory theta quadrature
-- statement:
--   For real $\tau$ and an integer $k\ge0$, set
--
--   $$
--   K_{\tau,k}(z)=2e^{z/4}\frac{z^k}{k!}e^{i\tau z}
--   \sum_{n=1}^{8}e^{-\pi n^2 e^z},\qquad
--   I_{\tau,k}=\int_1^\infty t^{-3/4}\frac{(\log t)^k}{k!}
--   (\theta(t)-1)e^{i\tau\log t}\,dt,
--   $$
--
--   where $\theta(t)=\sum_{n\in\mathbb Z}e^{-\pi n^2t}$. Divide $[0,6]$ into sixteen equal panels with midpoints $c_i=3(2i+1)/16$ and half-width $h=3/16$. Define the exact Taylor-panel sum
--
--   $$
--   Q_{\tau,k}=\sum_{i=0}^{15}\sum_{m=0}^{183}
--   \frac{K_{\tau,k}^{(m)}(c_i)}{m!}
--   \frac{h^{m+1}-(-h)^{m+1}}{m+1}.
--   $$
--
--   These are exact analytic definitions, not rational coefficient evaluations or an error estimate.
-- source:
--   Direct oscillatory extension of the theta/Mellin framework due to Gabewhigham and the 16-panel, 184-jet quadrature framework due to sometik179.

/- Exact direct oscillatory theta/Mellin quadrature.
The underlying theta/Mellin framework is due to Gabewhigham; the 16-panel,
184-jet quadrature framework is from sometik179. This definition makes no
numerical-error or zero-location assertion. -/
import Definitions.Def_TaoFivePrimes_RH14To100MomentModel
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false
open Complex Finset MeasureTheory Set

namespace RHDirectOscillatory

noncomputable def kernel (τ : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  2 * Complex.exp (z/4) * (z^k/(k.factorial:ℂ)) *
    Complex.exp (Complex.I*(τ:ℂ)*z) *
    ∑ n ∈ Finset.range 8, Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)

noncomputable def rawIntegral (τ : ℝ) (k : ℕ) : ℂ :=
  ∫ t in Set.Ioi (1:ℝ),
    ((CertifiedZetaQuadrature.momentWeight 1 k t *
      (HurwitzZeta.evenKernel 0 t-1):ℝ):ℂ) *
        Complex.exp (Complex.I*(τ:ℂ)*(Real.log t:ℂ))

noncomputable def panel (τ : ℝ) (k : ℕ) (c : ℝ) : ℂ :=
  ∑ n ∈ Finset.range 184,
    (iteratedDeriv n (kernel τ k) (c:ℂ)/(n.factorial:ℂ)) *
      (((3/16:ℂ)^(n+1)-(-(3/16:ℂ))^(n+1))/(n+1))

noncomputable def panelSum (τ : ℝ) (k : ℕ) : ℂ :=
  ∑ i ∈ Finset.range 16, panel τ k (3*(2*(i:ℝ)+1)/16)

end RHDirectOscillatory


