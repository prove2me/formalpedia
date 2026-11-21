-- Prove2me | Definitions.Def_FractionalCalc_mittagLeffler
-- name    : FractionalCalc_mittagLeffler
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T16:38:42.476933+00:00
-- url     : https://prove2.me/theorems/0fc589d1-1414-4c5c-9823-b7c3531d049b
-- title:
--   Mittag-Leffler functions $E_{\alpha,\beta}$, $E_\alpha$ and Prabhakar $E_{\alpha,\beta}^{\gamma}$
-- statement:
--   The **Mittag-Leffler functions** are the special functions of fractional calculus, generalizing the exponential:
--   $$E_{\alpha,\beta}(x)=\sum_{k=0}^{\infty}\frac{x^k}{\Gamma(\alpha k+\beta)},\qquad E_\alpha(x)=E_{\alpha,1}(x),\qquad E_{\alpha,\beta}^{\gamma}(x)=\sum_{k=0}^{\infty}\frac{(\gamma)_k\,x^k}{k!\,\Gamma(\alpha k+\beta)},$$
--   where $(\gamma)_k=\gamma(\gamma+1)\cdots(\gamma+k-1)$ is the rising factorial. $E_{\alpha,\beta}$ and $E_\alpha$ are used throughout the source (Eqs. 11, 16, 25–26, 46 and §5.2); the three-parameter (Prabhakar) function $E_{\alpha,\beta}^{\gamma}$ appears in Eq. (27). For $\alpha,\beta>0$ the series converge for every $x$ (the functions are entire).
--
--   **Formalization Note** Real-valued versions are defined by `tsum`; the rising factorial is the finite product $\prod_{j<k}(\gamma+j)$. The series is summable for $\alpha,\beta>0$; theorems assume these bounds.
-- source:
--   F. G. Rodrigues & E. C. de Oliveira, Rev. Bras. Ens. Fís. 37(3), 3305 (2015), https://doi.org/10.1590/S1806-11173731842, §4 Eqs. (25)–(27) and §5.2; series representations as in Gorenflo–Kilbas–Mainardi–Rogosin (2014), reference [17] of the source (footnote 5).

import Mathlib
open Classical
namespace FractionalCalc
/-- Two-parameter Mittag-Leffler function `E_{α,β}(x) = ∑' k, x^k / Γ(α k + β)`. -/
noncomputable def mittagLeffler (α β : ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, x ^ k / Real.Gamma (α * k + β)
/-- One-parameter Mittag-Leffler function `E_α(x) = E_{α,1}(x)`. -/
noncomputable def mittagLefflerOne (α : ℝ) (x : ℝ) : ℝ := mittagLeffler α 1 x
/-- Three-parameter (Prabhakar) Mittag-Leffler function. -/
noncomputable def prabhakar (α β γ : ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, (Finset.prod (Finset.range k) (fun j => γ + j)) * x ^ k / ((k.factorial : ℝ) * Real.Gamma (α * k + β))
end FractionalCalc


