-- Prove2me | Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
-- name    : CollatzEndpointTransport_Common_AffineCorrection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:08:05.88634+00:00
-- url     : https://prove2.me/theorems/b345fdc2-87dd-576a-97e5-65c3905d9f9c
-- title:
--   Affine Correction
-- statement:
--   Definitions and structural lemmas for Affine Correction, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/AffineCorrection.lean

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace Terras
open Nat Finset
def parityDigitR (n i : ℕ) : ℝ :=
  if parityBit ((T^[i]) n) then 1 else 0
noncomputable def affineCorrectionTerm (k n i : ℕ) : ℝ :=
  parityDigitR n i /
    ((3 : ℝ) ^ oddCount (i + 1) n * (2 : ℝ) ^ (k - i))
noncomputable def affineCorrection (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, affineCorrectionTerm k n i
end Terras
end CollatzEndpointTransport


