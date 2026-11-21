-- Prove2me | Definitions.Def_FractionalCalc_rlDeriv
-- name    : FractionalCalc_rlDeriv
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T16:38:03.169151+00:00
-- url     : https://prove2.me/theorems/7017a6fa-b6cc-48e8-a343-6e4b560eccb0
-- title:
--   Left Riemann–Liouville fractional derivative $D_{a+}^{\nu}f$
-- statement:
--   With $n=\lfloor\nu\rfloor+1$, the **left Riemann–Liouville fractional derivative** of order $\nu$ is
--   $$D_{a+}^{\nu}f(x)=\frac{d^n}{dx^n}\,I_{a+}^{\,n-\nu}f(x),$$
--   Definition 2.2, Eq. (3) of the source: differentiate $n$ times the fractional integral of order $n-\nu$. For integer $\nu=m$ this reduces to the ordinary $m$-th derivative.
--
--   **Formalization Note** The $n$-th derivative is `iteratedDeriv n`, and $I_{a+}^{\,n-\nu}$ is `rlIntegral`. The definition is total; theorems assume $\nu>0$ and the differentiability they need.
-- source:
--   F. G. Rodrigues & E. C. de Oliveira, Rev. Bras. Ens. Fís. 37(3), 3305 (2015), https://doi.org/10.1590/S1806-11173731842, §2, Definition 2.2, Eq. (3) (left-sided), $n=[\nu]+1$.

import Mathlib
import Definitions.Def_FractionalCalc_rlIntegral
open Classical
namespace FractionalCalc
/-- Left Riemann–Liouville fractional derivative `D_{a+}^ν f = d^n/dx^n I_{a+}^{n-ν} f`, `n=⌊ν⌋+1`. -/
noncomputable def rlDeriv (a ν : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  let n : ℕ := Nat.floor ν + 1
  iteratedDeriv n (rlIntegral a ((n : ℝ) - ν) f) x
end FractionalCalc


