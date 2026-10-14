-- Prove2me | Definitions.Def_TaoFivePrimes_RH100To1000MellinModel
-- name    : TaoFivePrimes_RH100To1000MellinModel
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-14T04:33:28.764962+00:00
-- url     : https://prove2.me/theorems/4a4545e5-4a5b-4cab-8b6a-daff74bf19e9
-- title:
--   Direct Mellin quadrature model for zeta heights through 1000
-- statement:
--   Transparent mathematical definitions of the twisted theta/Mellin integrand and its finite, exact Taylor quadrature rule. The theta truncation has 20 terms and the rule has 16 logarithmic panels with 1024 Taylor coefficients each. No approximation, numerical evaluation or RH assertion is included.
-- source:
--   Transparent definitions extending sometik179's theta/Mellin and Taylor quadrature method (original c9908072-d99a-4431-aad8-a72c6352619a, ordinary-syntax accepted pilot 30db8e24-e604-49d7-ab5c-f7b6f516651a). Theta/Mellin foundations attributed to Gabewhigham. The true integrand is retained; the finite rule now has 20 theta terms and 1024 Taylor terms on each of 16 logarithmic panels. This definition asserts no approximation or RH conclusion.

/- Direct Mellin quadrature model for the height-100–1000 continuation.
Original theta/Mellin method: sometik179; foundations: Gabewhigham.
Transparent functions only; no approximation or RH assertion. -/
import Definitions.Def_TaoFivePrimes_RH14To100MomentModel
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Log
open Complex MeasureTheory Set Finset
namespace RH1000Mellin
noncomputable def theta20 (z : ℂ) : ℂ :=
  ∑ n ∈ range 20, Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)
noncomputable def kernel (a : ℕ) (τ : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  2*Complex.exp (z/4)*(((a:ℂ)*z)^k/(k.factorial:ℂ))*
    Complex.exp (Complex.I*(τ:ℂ)*z)*theta20 z
noncomputable def raw (a : ℕ) (τ : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  (CertifiedZetaQuadrature.momentWeight a k t*(HurwitzZeta.evenKernel 0 t-1):ℝ)*
    Complex.exp (Complex.I*(τ:ℂ)*(Real.log t:ℂ))
noncomputable def coefficient (f : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f c/(n.factorial:ℂ)
noncomputable def panel (f : ℂ → ℂ) (c : ℂ) (h : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ range N, coefficient f c n*
    (((h:ℂ)^(n+1)-(-h:ℂ)^(n+1))/(n+1))
noncomputable def center (i : ℕ) : ℝ := 3*(2*(i:ℝ)+1)/16
end RH1000Mellin
noncomputable def TaoFivePrimes_RH100To1000MellinModel (a : ℕ) (τ : ℝ) (k : ℕ) : ℂ :=
  ∑ i ∈ Finset.range 16, RH1000Mellin.panel (RH1000Mellin.kernel a τ k)
    (RH1000Mellin.center i) (3/16) 1024


