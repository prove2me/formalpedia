-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalOddCountMGF
-- name    : CollatzEndpointTransport_Linear_FixedTotalOddCountMGF
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:56:28.398191+00:00
-- url     : https://prove2.me/theorems/aeab26ad-4055-49de-b342-41ce2230db8f
-- title:
--   Fixed Total Odd Count MGF
-- statement:
--   Definitions and structural lemmas for Fixed Total Odd Count MGF, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalOddCountMGF.lean

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalShellCoding
import Mathlib.Data.Nat.Choose.Sum
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
noncomputable section
def sourceOddLevel (M s : ℕ) : Finset (SourceCode M) :=
  Finset.univ.filter fun x => sourceCodeOddCount x = s
end
end FixedTotal
end CollatzEndpointTransport


