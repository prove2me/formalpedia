-- Prove2me | Definitions.Def_TightCoreset2027_Euclidean_Supplement_sizeScales
-- name    : TightCoreset2027_Euclidean_Supplement_sizeScales
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:08:55.346564+00:00
-- url     : https://prove2.me/theorems/ea1863b2-9f70-430d-a9ba-fa27307779fe
-- title:
--   Doubling coreset size scales and the permitted polylogarithms
-- statement:
--   For real z, ε, D and integer k, define the size scales
--
--   $$F(z,k,\varepsilon,D)=kD\min\{k^{1-2/z}\varepsilon^{-2},\varepsilon^{-z}\},$$
--   $$U(z,k,\varepsilon,D)=k^{2-2/z}\varepsilon^{-2}[D\log(2/\varepsilon)+\log(2k)].$$
--
--   For natural numbers a,b define
--
--   $$L_{a,b}(k,\varepsilon)=\log(2+k)^a\log(2+1/\varepsilon)^b.$$
--
--   All noninteger powers use real powers and all logarithms are natural. The using theorems require z≥2, k≥1, ε>0 and the source's upper accuracy and dimension restrictions, so every denominator and logarithm has its intended domain. F is the scale in (20) and Theorem 1.4; U is precisely (31). L expresses footnote 1 with finite degrees chosen before k, ε, D and all input data. No dependence on input size or on D is hidden in L.
-- source:
--   Junqiu Hu, Lingxiao Huang, Jian Li, Baoduo Xu, STOC 2027 submission #879 (October 2026), footnote 1, Theorem 1.4, equations (20) and (31), printed p. 1, 3, 21, 28 / PDF p. 3, 5, 23, 30; canonical source.pdf SHA256 9c247b18d4e2080420cb421dad0fe6c53b99885cef599b8f8e3cd8d639e13d5f.

import Mathlib
set_option autoImplicit false

namespace TightCoreset2027.Euclidean.Supplement

/-- The full scale in (20) and Theorem 1.4, with both branches and real powers. -/
noncomputable def doublingSizeScale (z : ℝ) (k : ℕ) (ε D : ℝ) : ℝ :=
  (k : ℝ) * D * min (Real.rpow (k : ℝ) (1 - 2 / z) * Real.rpow ε (-2))
    (Real.rpow ε (-z))

/-- The precise upper-bound scale (31), with no hidden input-size logarithm. -/
noncomputable def upperSizeScale (z : ℝ) (k : ℕ) (ε D : ℝ) : ℝ :=
  Real.rpow (k : ℝ) (2 - 2 / z) * Real.rpow ε (-2) *
    (D * Real.log (2 / ε) + Real.log (2 * (k : ℝ)))

/-- Footnote 1: finite natural degrees, only in k and inverse accuracy. -/
noncomputable def polylogFactor (a b : ℕ) (k : ℕ) (ε : ℝ) : ℝ :=
  Real.log (2 + (k : ℝ)) ^ a * Real.log (2 + 1 / ε) ^ b

end TightCoreset2027.Euclidean.Supplement


