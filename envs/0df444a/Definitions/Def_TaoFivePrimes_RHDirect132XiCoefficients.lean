-- Prove2me | Definitions.Def_TaoFivePrimes_RHDirect132XiCoefficients
-- name    : TaoFivePrimes_RHDirect132XiCoefficients
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:56:20.763508+00:00
-- url     : https://prove2.me/theorems/4e1acef2-3471-430f-a45c-51be679e306f
-- title:
--   Local xi coefficient candidates from height-132 quadrature
-- statement:
--   For the published Gaussian-rational quadrature values $R_n$, put
--
--   $$
--   L_n=\frac{R_n+(-1)^n\overline{R_n}}{2^{n+1}},
--   \qquad
--   X_n=\frac{\mathbf1_{n=0}}2-\frac{69697}{8}L_n
--   +132i\,\mathbf1_{n\ge1}L_{n-1}
--   +\frac12\mathbf1_{n\ge2}L_{n-2}.
--   $$
--
--   Define $C_n=10^{43}i^nX_n$. These Gaussian-rational expressions are proposed local xi coefficients at $1/2+132i$ in the variable $-i(s-1/2-132i)$. This definition alone asserts no error bound or equality with the stored rounded polynomial coefficients.
-- source:
--   Finite oscillatory theta quadrature based on the Mellin/theta-jet framework due to Gabewhigham and sometik179.

/- Candidate local xi coefficients from the finite height-132 quadrature.
The underlying theta/Mellin framework is due to Gabewhigham and sometik179.
The definitions assert no analytic error or rounding certificate. -/
import Definitions.Def_TaoFivePrimes_RHDirect132Rule
import Mathlib.Data.Complex.Basic

set_option autoImplicit false
open Complex

namespace RHDirect132XiCoefficients

noncomputable def lambda (n : ℕ) : ℂ :=
  (RHDirect132Rule.rule n+(-1:ℂ)^n*star (RHDirect132Rule.rule n))/(2:ℂ)^(n+1)

noncomputable def xi (n : ℕ) : ℂ :=
  (if n=0 then (1/2:ℂ) else 0) + (-(69697/8:ℂ))*lambda n +
    (if 1≤n then Complex.I*(132:ℂ)*lambda (n-1) else 0) +
    (if 2≤n then (1/2:ℂ)*lambda (n-2) else 0)

noncomputable def scaled (n : ℕ) : ℂ := (10^43:ℂ)*Complex.I^n*xi n

end RHDirect132XiCoefficients


