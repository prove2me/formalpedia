-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
-- name    : CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:37:08.877905+00:00
-- url     : https://prove2.me/theorems/5760fe0a-65f7-57c2-9789-79953b0e23f4
-- title:
--   Optimized Linear Pullback Constants
-- statement:
--   Definitions and structural lemmas for Optimized Linear Pullback Constants, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/OptimizedLinearPullbackConstants.lean

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Mathlib.Analysis.Calculus.Deriv.Slope
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace OptimizedLinearPullback
open scoped Real Topology
noncomputable section
def psi (D : ℝ) : ℝ :=
  -Real.log ((1 + Real.exp (-D * Real.log 3)) / 2)
def uniformRateLimit : ℝ :=
  Real.log (3 / 2) / (3 * Real.log 2)
def asymptoticRateLimit : ℝ :=
  Real.log 3 / (6 * Real.log 2)
def KappaAdmissible (kappa : ℝ) : Prop :=
  0 < kappa ∧ 2 * kappa + kappa ^ 2 < 1
def cq (kappa q : ℝ) : ℝ :=
  (q - QuantitativeDensity.a0) / (4 * kappa * q)
def beta
    (q kappa transport : ℝ) : ℝ :=
  2 +
    Real.log (1 / (transport * kappa ^ 2)) /
      Real.log (1 / q)
def delta
    (q kappa transport : ℝ) : ℝ :=
  1 / (beta q kappa transport + 1)
end
end OptimizedLinearPullback
end CollatzEndpointTransport


