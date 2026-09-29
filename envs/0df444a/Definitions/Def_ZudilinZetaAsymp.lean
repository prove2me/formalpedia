-- Prove2me | Definitions.Def_ZudilinZetaAsymp
-- name    : ZudilinZetaAsymp
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-22T17:42:59.548533+00:00
-- url     : https://prove2.me/theorems/117722ec-95c5-43ed-a937-9f816689e3a2
-- title:
--   Saddle points, the auxiliary function $f_0$, and the constants $C_0$, $C_1$
-- statement:
--   The asymptotic layer of Zudilin's note.
--
--   `charPoly P τ` is the polynomial whose zeros are the saddle points,
--   $$(\tau-\eta_0)^r(\tau-\eta_1)\cdots(\tau-\eta_q) - \tau^r(\tau-\eta_0+\eta_1)\cdots(\tau-\eta_0+\eta_q).$$
--
--   `f0 P τ` is the auxiliary function
--   $$f_0(\tau) = r\eta_0\log(\eta_0-\tau) + \sum_{j=1}^{q}\big(\eta_j\log(\tau-\eta_j) - (\eta_0-\eta_j)\log(\tau-\eta_0+\eta_j)\big) - 2\sum_{j=1}^{r}\eta_j\log\eta_j + \sum_{j=r+1}^{q}(\eta_0-2\eta_j)\log(\eta_0-2\eta_j),$$
--   with the principal branch of the complex logarithm.
--
--   `digamma` is $\psi = (\log \Gamma)'$, `C0 P τ₀` is $C_0 = -\operatorname{Re} f_0(\tau_0)$, and `C1 P` is
--   $$C_1 = rm_1 + m_2 + \dots + m_{q-r} - \Big(\int_0^1 \varphi(x)\,\mathrm{d}\psi(x) - \int_0^{1/m_{q-r}}\varphi(x)\,\frac{\mathrm{d}x}{x^2}\Big),$$
--   the Stieltjes integral being written as $\int_0^1 \varphi(x)\psi'(x)\,\mathrm{d}x$, which agrees with the Riemann–Stieltjes integral because $\psi$ is continuously differentiable on $(0,1]$.
-- source:
--   W. V. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Uspekhi Mat. Nauk 56:4 (2001), 149–150, https://doi.org/10.4213/rm427 (English transl.: Russian Math. Surveys 56:4 (2001), 774–776)

import Definitions.Def_ZudilinZetaArith

/-!
# Zudilin (2001): the auxiliary function `f₀`, the saddle-point equation, and `C₀`, `C₁`

Third definition layer for

  W. V. Zudilin, *One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational*,
  Uspekhi Mat. Nauk 56:4 (2001), 149–150.
-/

namespace ZudilinZeta

/-- The polynomial whose zeros are the saddle points of Zudilin's note:

`(τ - η₀)^r (τ - η₁) ⋯ (τ - η_q) - τ^r (τ - η₀ + η₁) ⋯ (τ - η₀ + η_q)`. -/
noncomputable def charPoly (P : Params) (τ : ℂ) : ℂ :=
  (τ - (P.eta 0 : ℂ)) ^ P.r * ∏ j ∈ Finset.Icc 1 P.q, (τ - (P.eta j : ℂ))
    - τ ^ P.r * ∏ j ∈ Finset.Icc 1 P.q, (τ - (P.eta 0 : ℂ) + (P.eta j : ℂ))

/-- The auxiliary function

`f₀(τ) = r η₀ log(η₀ - τ) + ∑_{j=1}^q (η_j log(τ - η_j) - (η₀ - η_j) log(τ - η₀ + η_j))`
`       - 2 ∑_{j=1}^r η_j log η_j + ∑_{j=r+1}^q (η₀ - 2η_j) log(η₀ - 2η_j)`,

with the principal branch of the complex logarithm. -/
noncomputable def f0 (P : Params) (τ : ℂ) : ℂ :=
  (P.r : ℂ) * (P.eta 0 : ℂ) * Complex.log ((P.eta 0 : ℂ) - τ)
    + (∑ j ∈ Finset.Icc 1 P.q,
        ((P.eta j : ℂ) * Complex.log (τ - (P.eta j : ℂ))
          - ((P.eta 0 : ℂ) - (P.eta j : ℂ)) * Complex.log (τ - (P.eta 0 : ℂ) + (P.eta j : ℂ))))
    - 2 * (∑ j ∈ Finset.Icc 1 P.r, (P.eta j : ℂ) * Complex.log (P.eta j : ℂ))
    + ∑ j ∈ Finset.Icc (P.r + 1) P.q,
        ((P.eta 0 : ℂ) - 2 * (P.eta j : ℂ)) * Complex.log ((P.eta 0 : ℂ) - 2 * (P.eta j : ℂ))

/-- The logarithmic derivative `ψ` of the gamma function (the digamma function). -/
noncomputable def digamma (x : ℝ) : ℝ := deriv (fun t : ℝ => Real.log (Real.Gamma t)) x

/-- `C₀ = - Re f₀(τ₀)`. -/
noncomputable def C0 (P : Params) (τ₀ : ℂ) : ℝ := -(f0 P τ₀).re

/-- `C₁ = r m₁ + m₂ + ⋯ + m_{q-r} - (∫₀¹ φ(x) dψ(x) - ∫₀^{1/m_{q-r}} φ(x) dx/x²)`,
the Stieltjes integral against the digamma function `ψ` being written as
`∫₀¹ φ(x) ψ'(x) dx`. -/
noncomputable def C1 (P : Params) : ℝ :=
  ((P.r : ℝ) * (m P 1 : ℝ) + ∑ j ∈ Finset.Icc 2 (P.q - P.r), (m P j : ℝ))
    - ((∫ x in (0 : ℝ)..1, (phi P x : ℝ) * deriv digamma x)
        - ∫ x in (0 : ℝ)..(1 / (m P (P.q - P.r) : ℝ)), (phi P x : ℝ) / x ^ 2)

end ZudilinZeta


