-- Prove2me | Definitions.Def_ZudilinZetaContourKernel
-- name    : ZudilinZetaContourKernel
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-02T08:52:07.670319+00:00
-- url     : https://prove2.me/theorems/1c8bcbcb-544d-4040-8501-2be5aa5547c0
-- title:
--   The reflected Gamma kernel for Zudilin's concrete parameters
-- statement:
--   Fix $\eta_0=91$, $\eta_1=\eta_2=\eta_3=27$, and $\eta_j=25+j$ for $4\le j\le13$. For an integer $n\ge2$, define the reflected Gamma kernel
--   $$
--   K_n(z)=(91n+2-2nz)
--   \frac{\Gamma(nz)^3\Gamma(n(91-z)+2)^3}{\Gamma(27n+1)^6}
--   \prod_{j=1}^{13}\frac{\Gamma(n(z-91+\eta_j)-1)}{\Gamma(n(z-\eta_j))}
--   \prod_{j=4}^{13}\Gamma(n(91-2\eta_j)+1).
--   $$
--   Its vertical integral is
--   $$
--   J_n(\tau)=\int_{\mathbb R}K_n(\tau+it)e^{-n\pi i(\tau+it)}\,dt.
--   $$
--   The intended contour strip is $87\le\operatorname{Re}\tau\le87.5$. These definitions isolate the concrete analytic integral used in the saddle argument for Zudilin's linear forms.
--
--   **Formalization Note.** The Gamma product is encoded by 39 factors with integer exponents, and the integral is the complex Bochner integral with respect to Lebesgue measure. The definitions are total; analytic statements impose the strip and integer bounds separately.
-- source:
--   Derived specialization of W. Zudilin, One of the numbers zeta(5), zeta(7), zeta(9), zeta(11) is irrational, Russian Math. Surveys 56:4 (2001), pp.774-775, the displayed rational function and equation (2), and the parameter choice on p.775, https://www.math.ru.nl/~zudilin/PS/zeta5-11%24.pdf. The contour argument is adapted from W. Zudilin, Irrationality of values of the Riemann zeta function, Izvestiya Math.66:3 (2002), Lemmas 2.3-2.4, pp.497-499, especially (2.5), (2.8)-(2.10), https://www.math.ru.nl/~zudilin/PS/zete_main.pdf. The present eta-parameter kernel and absolute-value normalization are a derived specialization, not a verbatim statement of Lemma 2.4.

import Definitions.Def_ZudilinZetaParams13

/-!
Concrete reflected Gamma kernel for the parameters in Zudilin's 2001 note,
p.774, rational-function formula and (2), with the parameter choice on p.775.
The indices encode a finite product; no contour identity is asserted here.
-/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
namespace ZudilinZeta

def params13GammaSlope (i : ℕ) : ℝ :=
  if i = 0 then 1 else if i = 1 then -1 else if 3 ≤ i ∧ i < 29 then 1 else 0

def params13GammaOffset (i : ℕ) : ℝ :=
  if i = 0 then 0 else if i = 1 then 91 else if i = 2 then 27
  else if i < 16 then -91 + (eta13 (i - 2) : ℝ)
  else if i < 29 then -(eta13 (i - 15) : ℝ)
  else 91 - 2 * (eta13 (i - 25) : ℝ)

def params13GammaBase (z : ℂ) (i : ℕ) : ℂ :=
  (params13GammaSlope i : ℂ) * z + (params13GammaOffset i : ℂ)

def params13GammaWeight (i : ℕ) : ℤ :=
  if i = 0 ∨ i = 1 then 3 else if i = 2 then -6
  else if i < 16 then 1 else if i < 29 then -1 else 1

def params13GammaShiftIndex (i : ℕ) : ℤ :=
  if i = 1 then 2 else if i = 2 then 1 else if i < 3 then 0
  else if i < 16 then -1 else if i < 29 then 0 else 1

def params13GammaKernel (n : ℕ) (z : ℂ) : ℂ :=
  (91 * (n : ℂ) + 2 - 2 * (n : ℂ) * z) *
    ∏ i ∈ Finset.range 39,
      Complex.Gamma ((n : ℂ) * params13GammaBase z i + (params13GammaShiftIndex i : ℂ)) ^
        params13GammaWeight i

def params13KernelIntegral (n : ℕ) (τ : ℂ) : ℂ :=
  ∫ t : ℝ, params13GammaKernel n (τ + (t : ℂ) * I) *
    Complex.exp (-(n : ℂ) * (Real.pi : ℂ) * I * (τ + (t : ℂ) * I))

end ZudilinZeta
end


