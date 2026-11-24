-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainSemanticBridge
-- name    : Sensitivity214439_Phase0_Solutions_UnaryGainSemanticBridge
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:19:39.320873+00:00
-- url     : https://prove2.me/theorems/f9baf3b8-3daa-4809-9b6c-145f51e3337a
-- title:
--   Actual unary recipe and height-state interpretation
-- statement:
--   The actual recipe associated with the numerical unary gain recipe is the one-side gate recipe with the same soft and hard cutoffs, allowance, and target function.
--
--   At a parent row $v$, input $x$, and recording cutoff $a$, its actual numerical state is
--   $$
--   \left(h_F(x_v),\
--   \bigl(h_Q(x):Q\in\mathcal G_v\text{ active at }a\bigr)\right).
--   $$
--   The second component records one entry per occupied check. The recipe and state aliases identify the finite gain model used by the subsequent semantic lemmas.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryGainSemanticBridge.lean lines 15–25; SHA256 054e30f0441976a3a16e1651d3595330566934f9379483807bb7f2ef8d0a2a01; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_FiniteRanks
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainNumeric
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
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityFiniteRanks
end SensitivityFiniteRanks
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityOperativeHeads
end SensitivityOperativeHeads
namespace SensitivityOwnTargetBounds
end SensitivityOwnTargetBounds
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivitySocketEventSupport
end SensitivitySocketEventSupport
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates
namespace SensitivityUnaryGainSemantics
end SensitivityUnaryGainSemantics



/-! The full ordinary/firm unary recipe, represented by actual finite heights. -/
namespace SensitivityUnaryGainSemantics

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGuardEvents
open SensitivityFiniteRanks SensitivityStrictGateStates SensitivitySocketEventSupport
open SensitivityOperativeHeads SensitivityOwnTargetBounds
set_option autoImplicit false

abbrev GainRecipe := SensitivityUnaryGainNumeric.Recipe
abbrev GainState := SensitivityUnaryGainNumeric.State

variable {V S I Color : Type}

def actualRecipe (r : GainRecipe) : GateRecipe Unit 12 :=
  unaryRecipe r.soft r.hard r.allowance r.target

def actualState (row : RowFamily I Color 12) (guards : GuardFamily V Unit)
    (v : V) (cutoff : Fin 12) (x : ((V × Unit) × I) → Bool) : GainState :=
  ⟨rankHeight row (socketInput x (v,())),occupiedGuardHeights row guards v cutoff x⟩



















end
end SensitivityUnaryGainSemantics


