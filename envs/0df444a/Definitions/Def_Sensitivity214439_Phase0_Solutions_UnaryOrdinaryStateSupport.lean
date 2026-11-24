-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryOrdinaryStateSupport
-- name    : Sensitivity214439_Phase0_Solutions_UnaryOrdinaryStateSupport
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:52:57.147039+00:00
-- url     : https://prove2.me/theorems/70f89c71-3eae-4c9e-8e54-4e46e16211ff
-- title:
--   Population statistics extracted from an ordinary context
-- statement:
--   The finite numerical state of an actual ordinary context is
--   $$
--   (t,g,e)=\bigl(|T|,|G|,|E|\bigr),
--   $$
--   where $T$ is the high-target set, $G$ the high-guard set, and $E$ the external-donor set. Its active head set is the union of all high operative rows and external donors. These definitions connect actual Boolean event accounting with the finite ordinary population enumeration.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryOrdinaryStateSupport.lean lines 19–21; SHA256 634df80949d2ef4f92b6b331262b8648d2ccdb49d2458de28383fec9038e9bb8; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryOrdinaryContext
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryOrdinaryGlobalNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityLocalNumericSemantics
end SensitivityLocalNumericSemantics
namespace SensitivityOperativeHeads
end SensitivityOperativeHeads
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivityUnaryGainSemantics
end SensitivityUnaryGainSemantics
namespace SensitivityUnaryOrdinaryContext
end SensitivityUnaryOrdinaryContext
namespace SensitivityUnaryOrdinaryContext.Context
end SensitivityUnaryOrdinaryContext.Context
namespace SensitivityUnaryOrdinaryGeometry
end SensitivityUnaryOrdinaryGeometry
namespace SensitivityUnaryOrdinaryGlobalNumeric
end SensitivityUnaryOrdinaryGlobalNumeric
namespace SensitivityUnaryPopulationSupport
end SensitivityUnaryPopulationSupport
namespace SensitivityUnaryTournamentEvents
end SensitivityUnaryTournamentEvents



/-! Actual ordinary unary heads and their positive donor set form one of
the finite states whose prices are checked by the certificate. -/
namespace SensitivityUnaryOrdinaryContext

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGuardEvents
open SensitivityOperativeHeads SensitivityUnaryTournamentEvents SensitivityUnaryPopulationSupport
open SensitivityUnaryOrdinaryGlobalNumeric SensitivityUnaryOrdinaryGeometry
open SensitivityLocalNumericSemantics SensitivityUnaryGainSemantics
set_option autoImplicit false

variable {V I Color : Type} [Fintype V] [Fintype I]

namespace Context

def state (c : Context V I Color) : State :=
  ⟨c.targets.card,c.guardHeads.card,c.external.card⟩
def activeSet (c : Context V I Color) : Finset V := c.high ∪ c.external






















end Context
end
end SensitivityUnaryOrdinaryContext


