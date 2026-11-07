-- Prove2me | Definitions.Def_CubicProductLB_cubeAvg
-- name    : CubicProductLB_cubeAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:18:43.558206+00:00
-- url     : https://prove2.me/theorems/95c17acd-dd07-4d69-b5a9-2d202cb16afb
-- title:
--   The uniform average $\mathbb E_{x \in X_n}$ over the sign cube
-- statement:
--   For a complex-valued function $f$, the average over independent uniform signs is
--   $$\mathbb E_{x \in X_n} f(x) = 2^{-n} \sum_{x \in X_n} f(x).$$
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Section 5, p.8

import Mathlib
import Definitions.Def_CubicProductLB_signPt

namespace CubicProductLB

/-- The uniform average `E_{x ∈ X_n} f(x)` of a complex function over the sign cube
(Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Section 5, p.8). -/
noncomputable def cubeAvg (n : ℕ) (f : (Fin n → ZMod 3) → ℂ) : ℂ :=
  ((2 : ℂ) ^ n)⁻¹ * ∑ z : Fin n → Bool, f (signPt z)

end CubicProductLB


