-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
-- name    : CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:39:13.119442+00:00
-- url     : https://prove2.me/theorems/8579825b-9ca7-4562-9b9a-d16d379ca9cd
-- title:
--   Fixed Size Separator Reverse
-- statement:
--   Definitions and structural lemmas for Fixed Size Separator Reverse, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorReverse.lean

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
open scoped Real
noncomputable section
def fixedReverseSpendSum
    (N s : ℕ) (theta : ℝ) (D : ℕ) : ℝ :=
  ∑ r ∈ Ico 1 s,
    ∑ d ∈ terminalPatternSet N s r D,
      (terminalFiber N s r d).card *
        realTerminalPatternTerm theta r d
def fixedSizeReverseRatio (theta pi : ℝ) : ℝ :=
  (1 + pi * ((3 : ℝ) ^ theta - 1)) / (2 : ℝ) ^ theta
end
end FixedTotal
end CollatzEndpointTransport


