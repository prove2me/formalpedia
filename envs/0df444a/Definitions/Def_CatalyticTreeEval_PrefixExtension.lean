-- Prove2me | Definitions.Def_CatalyticTreeEval_PrefixExtension
-- name    : CatalyticTreeEval_PrefixExtension
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T02:22:57.917276+00:00
-- url     : https://prove2.me/theorems/b289c95d-c7d6-46e6-aab3-eab7b083efe1
-- title:
--   Extension by arbitrary unused catalyst bits
-- statement:
--   Extend a native configuration by appending arbitrary bits beyond its current catalyst. The control state, all three heads, work tape and existing output are unchanged. Step and trajectory preservation under a strict prefix bound are subsequent proof obligations.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Section 3 machine model and Corollary 4.2.

import Definitions.Def_CatalyticTreeEval_MachineContracts

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.PrefixExtension

open CatalyticMatching.General

/-- Add untouched arbitrary bits beyond a configuration's current catalyst. -/
def extend {M : Machine} (suffix : List Bool) (c : Configuration M) : Configuration M :=
  { c with catalyst := c.catalyst ++ suffix }

end CatalyticTreeEval.Contracts.PrefixExtension


