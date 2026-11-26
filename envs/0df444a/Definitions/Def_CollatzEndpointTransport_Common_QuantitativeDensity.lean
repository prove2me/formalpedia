-- Prove2me | Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensity
-- name    : CollatzEndpointTransport_Common_QuantitativeDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:06:51.168653+00:00
-- url     : https://prove2.me/theorems/4118c922-7ccf-5569-840d-db0de23d4461
-- title:
--   Quantitative Density
-- statement:
--   Definitions and structural lemmas for Quantitative Density, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensity.lean

import Mathlib
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace QuantitativeDensity
open scoped Real
noncomputable section
def positivePrefix (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 N
def badPrefix (S : Set ℕ) (N : ℕ) : Finset ℕ := by
    classical
    exact (positivePrefix N).filter (fun n => n ∉ S)
def IsCDDense (S : Set ℕ) (C D : ℝ) : Prop :=
  0 < C ∧ 0 < D ∧ D ≤ 1 ∧
    ∀ N : ℕ, 0 < N →
      ((badPrefix S N).card : ℝ) ≤ C * (N : ℝ) ^ (1 - D)
end
end QuantitativeDensity
end CollatzEndpointTransport


