-- Prove2me | Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
-- name    : CollatzEndpointTransport_Common_QuantitativeDensityConstants
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:14:55.461916+00:00
-- url     : https://prove2.me/theorems/5ca5d450-4ef0-53fc-a522-0993037a7ef5
-- title:
--   Quantitative Density Constants
-- statement:
--   Definitions and structural lemmas for Quantitative Density Constants, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensityConstants.lean

import Mathlib
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace QuantitativeDensity
noncomputable def lg3 : ℝ := Real.logb 2 3
noncomputable def a0 : ℝ := lg3 / 2
noncomputable def bConst : ℝ := 1 - a0
noncomputable def kappa : ℝ := 1 / (8 * (2 + lg3))
noncomputable def L0 : ℝ := 1 / (4 * (1 + 1 / bConst))
noncomputable def cq (q : ℝ) : ℝ := (q - a0) / (4 * kappa * q)
noncomputable def admissibleExponent (q : ℝ) : ℝ :=
  Real.log (1 / q) / Real.log 3
noncomputable def headlineExponent : ℝ :=
  admissibleExponent a0
noncomputable def gammaExponent (q : ℝ) : ℝ :=
  Real.log 3 / Real.log (1 / q)
end QuantitativeDensity
namespace Terras
end Terras
end CollatzEndpointTransport


