-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryTournamentEvents
-- name    : Sensitivity214439_Phase0_Solutions_UnaryTournamentEvents
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:06:40.373707+00:00
-- url     : https://prove2.me/theorems/93cbfa77-fd54-4d90-ba04-cbbce55e8fce
-- title:
--   Positive unary rows and donor destinations
-- statement:
--   At a chosen cutoff $a$, positive unary rows are those whose own child passes that cutoff:
--   $$
--   P_a(x)=\{v:F\text{ passes }a\text{ at socket }(v,\ast)\}.
--   $$
--   For a positive set $P$ and source-head set $G$, the donor set is
--   $$
--   D(P,G)=\{w\in P:\exists v\in G,\ v\to w\}.
--   $$
--   It counts distinct positive destination rows even when several source heads inspect the same donor.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryTournamentEvents.lean lines 16–105; SHA256 513797ea1b260c6c08b2aeb39d98782743440469562854150d6af0b35789db48; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
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
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityOperativeHeads
end SensitivityOperativeHeads
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivityUnaryPopulationSupport
end SensitivityUnaryPopulationSupport
namespace SensitivityUnaryTournamentEvents
end SensitivityUnaryTournamentEvents



/-! Actual singleton tournament guards and the destination of a hard repair. -/
namespace SensitivityUnaryTournamentEvents

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGuardEvents
open SensitivityOperativeHeads SensitivityUnaryPopulationSupport
open SensitivityHighHeadGuardBridge
set_option autoImplicit false

variable {V I Color : Type} {L : ℕ} [Fintype V]

def positiveRows (row : RowFamily I Color L) (cutoff : ℕ)
    (x : ((V × Unit) × I) → Bool) : Finset V :=
  Finset.univ.filter fun v => passes row cutoff (socketInput x (v,()))













def hardDonors (arc : V → V → Prop) (P G : Finset V) : Finset V :=
  P.filter fun w => ∃ v ∈ G, arc v w







end
end SensitivityUnaryTournamentEvents


