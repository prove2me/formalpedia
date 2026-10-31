-- Prove2me | Definitions.Def_RecursiveStopping_Finite_wnorm
-- name    : RecursiveStopping_Finite_wnorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:23.713024+00:00
-- url     : https://prove2.me/theorems/3d60f680-7c8f-4708-ac23-713677f9f50f
-- title:
--   The finite-horizon weighted norm $\|f\|_{\mathcal A_d}$
-- statement:
--   For a real function $f$ on $\mathbb R\times\mathbb R^m$ ($m=d-1$),
--
--   $$
--   \|f\|_{\mathcal A_d}^2:=\sup_{(t,x)\in[0,T]\times\mathbb R^{d-1}}\frac{|f(t,x)|^2}{1+|x|_{d-1}^2},
--   $$
--
--   so only values on $[0,T]\times\mathbb R^{d-1}$ enter and the weight involves the spatial coordinate only.
--
--   **Formalization Note** The norm is valued in $[0,\infty]$.
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, §2.2, p.10

import Mathlib
import Definitions.Def_RecursiveStopping_Finite_Dom

open scoped NNReal ENNReal

namespace RecursiveStopping.Finite

/-- The finite-horizon weighted norm of Colaneri & De Angelis, arXiv:1905.02650v4, p.10:
$$\|f\|_{A_d}^2 := \sup_{(t,x)\in[0,T]\times\mathbb R^{d-1}}\frac{|f(t,x)|^2}{1+|x|_{d-1}^2},$$
i.e. `sup_{(t,x)} |f(t,x)| / (1 + |x|_{d−1}²)^{1/2}` with the spatial weight only.

**Formalization Note** `m = d − 1`; `ℝ^m` is `EuclideanSpace ℝ (Fin m)`. Values of `f` outside
`[0, T] × ℝ^m` do not enter. The value is in `[0, ∞]`. -/
noncomputable def wnorm {m : ℕ} (T : ℝ) (f : ℝ × EuclideanSpace ℝ (Fin m) → ℝ) : ℝ≥0∞ :=
  ⨆ z ∈ Dom m T, ENNReal.ofReal (|f z| / Real.sqrt (1 + ‖z.2‖ ^ 2))

end RecursiveStopping.Finite


