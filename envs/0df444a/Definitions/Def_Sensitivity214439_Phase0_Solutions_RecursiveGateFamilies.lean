-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_RecursiveGateFamilies
-- name    : Sensitivity214439_Phase0_Solutions_RecursiveGateFamilies
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:06:34.429189+00:00
-- url     : https://prove2.me/theorems/a18de829-cab0-4be2-b590-85352db1e9d2
-- title:
--   A finite nonempty gate stage
-- statement:
--   A gate stage specifies a finite nonempty row type, a finite nonempty socket-side type, a guard family on those row-side sockets, and a recipe with $L$ ranks. It also contains the proof that its guards never inspect a socket belonging to their own source row.
--
--   The stage packages the combinatorial ingredients needed to apply one recursive Boolean construction step; further nesting and profile hypotheses are supplied by separate theorems.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/RecursiveGateFamilies.lean lines 18–27; SHA256 0fdb26aba8dd8c6341b214c6e52e94b662872253927780d0d80c265e306a8420; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod

namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-!
# Recursive actual Boolean families

The finite input and color types change at every stage. `BuiltFamily` packages
these types together with an actual row predicate and the canonical blocks
proved in the previous modules. No sensitivity upper bound is a field of this
structure. The recursive construction below proves both lower bounds outright
from the one-bit leaf and the stage definitions.
-/

namespace SensitivityRankedConstruction

noncomputable section
open scoped Classical

structure GateStage (L : ℕ) where
  Row : Type
  rowFinite : Fintype Row
  rowNonempty : Nonempty Row
  Socket : Type
  socketFinite : Fintype Socket
  socketNonempty : Nonempty Socket
  guards : GuardFamily Row Socket
  recipe : GateRecipe Socket L
  noSelf : NoSelfGuards guards




















































end
end SensitivityRankedConstruction


