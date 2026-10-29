-- Prove2me | Definitions.Def_PeskirShiryaev_AmericanPut_Kernels
-- name    : PeskirShiryaev_AmericanPut_Kernels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:27:26.797206+00:00
-- url     : https://prove2.me/theorems/2871a65c-0eae-440a-9101-797950604231
-- title:
--   Gaussian kernels and the nonlinear Volterra boundary equation
-- statement:
--   Let $\Phi(a)=(2\pi)^{-1/2}\int_{-\infty}^a e^{-z^2/2}\,dz$ and put $\gamma=r-\sigma^2/2$. For elapsed time $u>0$ and $x,y>0$, the geometric Brownian transition distribution is
--   $$F(u,x,y)=\Phi\!\left(\frac{\log(y/x)-\gamma u}{\sigma\sqrt u}\right).$$
--   At $u=0$ use $F(0,x,y)=\mathbf1_{\{x\le y\}}$. For $u>0$, the extension at $x=0$ is $\mathbf1_{\{0\le y\}}$, while $F(u,x,y)=0$ for $x>0$ and $y\le0$. Define
--   $$E(t,x)=e^{-r(T-t)}\int_0^K F(T-t,x,K-z)\,dz,$$
--   $$P_c(t,x)=rK\int_0^{T-t}e^{-ru}F(u,x,c(t+u))\,du.$$
--   A boundary $c$ solves the equation when
--   $$K-c(t)=E(t,c(t))+P_c(t,c(t)),\qquad 0\le t\le T.$$
--   This is the two-integral form of Eq. (25.2.39), with its terminal and zero-stock cases made explicit.
--
--   **Formalization Note** No endpoint is defined by division by zero or by $\log0$. For completeness outside the financial domain, the kernel for $x<0,y<0,u>0$ uses $1-\Phi((\log(y/x)-\gamma u)/(\sigma\sqrt u))$, and for $x<0\le y$ it is one; nonpositive elapsed times use the deterministic indicator. Candidate boundaries have nonnegative endpoints by continuity, so the negative-stock branches do not enter the target theorem. At $y=0$ with positive stock, the CDF is zero. All displayed integrals are real integrals.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 385–386 (PDF 401–402), Eqs. (25.2.38)–(25.2.42)

import Definitions.Def_PeskirShiryaev_AmericanPut_Boundary

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace PeskirShiryaev.AmericanPut

noncomputable def normalCDF (a : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * ∫ z in Set.Iic a, Real.exp (-z ^ 2 / 2)

noncomputable def Model.transitionCDF {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (u x y : ℝ) : ℝ := by
  classical
  exact if u ≤ 0 then (if x ≤ y then 1 else 0)
    else if x = 0 then (if 0 ≤ y then 1 else 0)
    else if 0 < x then
      (if 0 < y then normalCDF ((Real.log (y / x) - (M.r - M.sigma ^ 2 / 2) * u) /
        (M.sigma * Real.sqrt u)) else 0)
    else (if y < 0 then 1 - normalCDF
      ((Real.log (y / x) - (M.r - M.sigma ^ 2 / 2) * u) / (M.sigma * Real.sqrt u))
      else 1)

noncomputable def Model.european {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (t x : ℝ) : ℝ :=
  Real.exp (-M.r * (M.T - t)) *
    (∫ z in (0 : ℝ)..M.K, M.transitionCDF (M.T - t) x (M.K - z))

noncomputable def Model.premium {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (c : ℝ → ℝ) (t x : ℝ) : ℝ :=
  M.r * M.K * (∫ u in (0 : ℝ)..(M.T - t),
    Real.exp (-M.r * u) * M.transitionCDF u x (c (t + u)))

def Model.Solves {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (c : ℝ → ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 M.T, M.K - c t = M.european t (c t) + M.premium c t (c t)

end PeskirShiryaev.AmericanPut


