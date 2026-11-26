-- Prove2me | Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity
-- name    : CollatzEndpointTransport_Common_AffineCorrectionDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:10:07.288882+00:00
-- url     : https://prove2.me/theorems/9951883c-d16c-5b79-9332-34e3ec8ba6fc
-- title:
--   Affine Correction Density
-- statement:
--   Definitions and structural lemmas for Affine Correction Density, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/AffineCorrectionDensity.lean

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Definitions.Def_CollatzEndpointTransport_Common_ShellToGlobalDensity
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace Terras
open Nat Finset
open scoped Real
noncomputable section
def affineCorrectionGood (t : ℝ) : Set ℕ :=
  {n | ∀ k : ℕ, k ≤ Nat.log 2 n →
    affineCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2) < (n : ℝ) ^ t}
end
end Terras
end CollatzEndpointTransport


