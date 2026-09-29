-- Prove2me | Definitions.Def_Freiman_cF
-- name    : Freiman_cF
-- status  : Definition
-- author  : @tp
-- created : 2026-09-08T23:20:38.174481+00:00
-- url     : https://prove2.me/theorems/116246bf-cf19-4c5c-8873-5e1fa9a1ae22
-- title:
--   Freiman's constant
-- statement:
--   Define the real number
--
--   $$
--   c_F=\frac{2221564096+283748\sqrt{462}}{491993569},
--   $$
--
--   where the square root is nonnegative. This constant will be used to state the endpoint of the maximal Hall ray.
-- source:
--   C. G. Moreira, Geometric properties of the Markov and Lagrange spectra, Annals of Mathematics 188 (2018), 145–170, p. 146, unnumbered displayed formula for c. https://doi.org/10.4007/annals.2018.188.1.3

import Mathlib.Analysis.Real.Sqrt

namespace Freiman

noncomputable def cF : ℝ :=
  (2221564096 + 283748 * Real.sqrt 462) / 491993569

end Freiman


