-- Prove2me | Definitions.Def_Transport_Endpoint
-- name    : Transport_Endpoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:12.069206+00:00
-- url     : https://prove2.me/theorems/ac43268e-1c70-41cb-b37a-ff96074ac132
-- title:
--   Endpoint
-- statement:
--   Definitions and structural lemmas for Endpoint, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Endpoint.lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace RH.Transport.Endpoint
noncomputable section
def perturbation : ℝ := 68479 / 400000000
def boundary : ℝ := 7 / 8 - perturbation / 4
def ell : ℝ := 1 / 6 + perturbation
def ly : ℝ := 23 / 48 - perturbation / 2
def h : ℝ := 13 / 16 + 3 * perturbation / 2
def saving : ℝ := 1 / 40000000000
def countDenominator (δ x : ℝ) : ℝ :=
  (5 / 6 - δ) * (3 - 17 * x / 9) + δ * ((2 - 8 * x / 9) * (1 - x))
def adaptiveCount (δ x : ℝ) : ℝ :=
  1 - δ + (5 / 6 - δ) * δ * ((2 - 8 * x / 9) * (1 - x)) /
    (2 * countDenominator δ x)
def endpointExponent (δ x : ℝ) : ℝ :=
  (1 + δ) / 2 - boundary + h * (17 / 50 - 1 / 6) -
    ((1 + δ) / 2) * ly - ell / 2 + δ * x * ell +
    h * (adaptiveCount δ x + δ / 2 - 17 / 50)
def certificatePolynomial (δ x : ℝ) : ℝ :=
  ((618580093 : ℝ) / 12000000000) +
    ((-10515861581 : ℝ) / 324000000000) * x +
    ((-9993580093 : ℝ) / 30000000000) * δ +
    ((251842900489 : ℝ) / 810000000000) * δ * x +
    ((-32525679661 : ℝ) / 1620000000000) * δ * x ^ 2 +
    ((800205437 : ℝ) / 1200000000) * δ ^ 2 +
    ((-830205437 : ℝ) / 720000000) * δ ^ 2 * x +
    ((7103903303 : ℝ) / 10800000000) * δ ^ 2 * x ^ 2 +
    ((-200205437 : ℝ) / 1350000000) * δ ^ 2 * x ^ 3
def generalEndpointExponent (p δ x : ℝ) : ℝ :=
  (1 + δ) / 2 - (7 / 8 - p / 4) +
    (13 / 16 + 3 * p / 2) * (17 / 50 - 1 / 6) -
    ((1 + δ) / 2) * (23 / 48 - p / 2) - (1 / 6 + p) / 2 +
    δ * x * (1 / 6 + p) +
    (13 / 16 + 3 * p / 2) * (adaptiveCount δ x + δ / 2 - 17 / 50)
def witnessDelta : ℝ := 38668853 / 100000000
def screenUpper : ℝ := 171197539 / 1000000000000
end
end RH.Transport.Endpoint


