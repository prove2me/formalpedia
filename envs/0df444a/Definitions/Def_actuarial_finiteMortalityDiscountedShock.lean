-- Prove2me | Definitions.Def_actuarial_finiteMortalityDiscountedShock
-- name    : actuarial_finiteMortalityDiscountedShock
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T07:06:17.592975+00:00
-- url     : https://prove2.me/theorems/85d75e34-314d-473d-9d4c-1919dd04508a
-- title:
--   Finite discounted sum of annual mortality innovations
-- statement:
--   Discounted net-amount-at-risk coefficients rho(t) weight the annual mortality innovations through n years.
--
--   **Mathematical statement**
--
--   $$
--   Z_n=\sum_{t<n}\rho_t I_t
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, equations (1)-(3), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, 3rd ed., Ch.6 Sec.6.7; Gerber Leung Shiu (2003), Indicator Function and Hattendorff Theorem, https://doi.org/10.1080/10920277.2003.10596075

import Mathlib
import Definitions.Def_actuarial_finiteMortalityInnovation
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteMortalityDiscountedShock {Ω : Type*} [Fintype Ω]
  (w : Ω → ℝ) (K : Ω → ℕ) (ρ : ℕ → ℝ)
  (n : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range n, ρ t * finiteMortalityInnovation w K t ω

end ActuarialValuation


