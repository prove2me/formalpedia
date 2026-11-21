-- Prove2me | Definitions.Def_FractionalCalc_caputoDeriv
-- name    : FractionalCalc_caputoDeriv
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T16:38:28.659163+00:00
-- url     : https://prove2.me/theorems/f224032a-f6f5-470e-86c2-7878818d52a9
-- title:
--   Left Caputo fractional derivative ${}^{C}D_{a+}^{\nu}f$
-- statement:
--   With $n=\lceil\nu\rceil$, the **left Caputo fractional derivative** of order $\nu$ is
--   $${}^{C}D_{a+}^{\nu}f(x)=I_{a+}^{\,n-\nu}\big(f^{(n)}\big)(x)=\frac{1}{\Gamma(n-\nu)}\int_a^x (x-t)^{n-\nu-1}f^{(n)}(t)\,dt,$$
--   the Caputo derivative of Definition 2.3. This is the integral form used in the paper's Laplace-transform derivation (Eqs. 22–23); for $f\in AC^n$ it equals $D_{a+}^{\nu}\big(f-\sum_{k<n}f^{(k)}(a)(\cdot-a)^k/k!\big)$. For integer $\nu=m$ it reduces to $f^{(m)}$, so initial conditions have their classical meaning.
--
--   **Formalization Note** $n=\lceil\nu\rceil$ gives $n=\nu$ at integer orders and $n=\lfloor\nu\rfloor+1$ otherwise; $I^0=\mathrm{id}$ handles the integer case. Theorems assume $\nu>0$ and the regularity they need.
-- source:
--   F. G. Rodrigues & E. C. de Oliveira, Rev. Bras. Ens. Fís. 37(3), 3305 (2015), https://doi.org/10.1590/S1806-11173731842, §2, Definition 2.3 (left Caputo), in the integral form used at Eqs. (22)–(23); equivalent to Eq. (5) for $f\in AC^n$.

import Mathlib
import Definitions.Def_FractionalCalc_rlIntegral
open Classical
namespace FractionalCalc
/-- Left Caputo fractional derivative `{}^C D_{a+}^ν f = I_{a+}^{n-ν} f^{(n)}`, `n=⌈ν⌉`. -/
noncomputable def caputoDeriv (a ν : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  let n : ℕ := Nat.ceil ν
  rlIntegral a ((n : ℝ) - ν) (iteratedDeriv n f) x
end FractionalCalc


