-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
-- name    : CollatzEndpointTransport_Linear_FractionalBinomialMass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:43:21.447865+00:00
-- url     : https://prove2.me/theorems/1414c398-5395-4ec1-b1cb-33b3d759e527
-- title:
--   Fractional Binomial Mass
-- statement:
--   Definitions and structural lemmas for Fractional Binomial Mass, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean

import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Mathlib.Analysis.Real.Sqrt
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 200000
def symmetricBinomialMass (H k : ℕ) : ℝ :=
  (H.choose k : ℝ) / (2 : ℝ) ^ H
def binomialCenterDistance (H k : ℕ) : ℕ :=
  if k ≤ H / 2 then H / 2 - k else k - H / 2
def binomialAnnulusWidth (H : ℕ) : ℕ := Nat.sqrt H + 3
def binomialAnnulus (H j : ℕ) : Finset ℕ :=
  (Finset.range (H + 1)).filter fun k =>
    j * binomialAnnulusWidth H ≤ binomialCenterDistance H k ∧
      binomialCenterDistance H k < (j + 1) * binomialAnnulusWidth H
def binomialAnnulusCode (H k : ℕ) : Bool × ℕ :=
  (decide (k ≤ H / 2), binomialCenterDistance H k)
def binomialAnnulusCutoff (H j : ℕ) : ℕ :=
  H / 2 + 1 - j * binomialAnnulusWidth H
end
end FixedTotal
end CollatzEndpointTransport


