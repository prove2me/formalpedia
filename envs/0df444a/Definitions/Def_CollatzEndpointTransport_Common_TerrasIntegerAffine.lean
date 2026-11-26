-- Prove2me | Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
-- name    : CollatzEndpointTransport_Common_TerrasIntegerAffine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:19:24.78477+00:00
-- url     : https://prove2.me/theorems/28272b1e-398e-4d4c-b634-e4f5987f6ea1
-- title:
--   Terras Integer Affine
-- statement:
--   Definitions and structural lemmas for Terras Integer Affine, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasIntegerAffine.lean

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace Terras
open Nat Finset
def integerCorrection : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n =>
      if parityBit ((T^[k]) n) then
        3 * integerCorrection k n + 2 ^ k
      else
        integerCorrection k n
end Terras
end CollatzEndpointTransport


