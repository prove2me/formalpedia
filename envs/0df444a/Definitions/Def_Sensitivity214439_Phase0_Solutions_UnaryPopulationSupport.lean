-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryPopulationSupport
-- name    : Sensitivity214439_Phase0_Solutions_UnaryPopulationSupport
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:33:13.869812+00:00
-- url     : https://prove2.me/theorems/7ff33461-1f48-4104-a3dc-e36314950219
-- title:
--   Incoming-prefix populations and loopless unary indexing
-- statement:
--   For a finite head set $H$ and tolerance $q$, define
--   $$
--   \operatorname{incomingPopulation}(H,q)
--   =\{v\notin H:\ |\{w\in H:w\to v\}|\ge |H|-q\}.
--   $$
--   Subtraction is truncated in the natural numbers. In a tournament this means that the outside vertex has at most $q$ outgoing neighbors in $H$.
--
--   For a loopless relation, the unary guard indexing assigns the singleton destination socket directly to each arc, with no additional self-loop exclusion in the indexed relation. The loopless hypothesis supplies that exclusion automatically.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryPopulationSupport.lean lines 22–48; SHA256 1a8d44360e513718921d17aaa75cd64c87380d239bf0b0534756900d5184b35e; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentSocketGuards
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

namespace Sensitivity213981Formal
end Sensitivity213981Formal
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



/-!
Actual low rows are among the orientation populations bounded by the Paley
character estimates.  This module also proves the exact cumulative-count
formula used to price several affordable guard counts at once.
-/
namespace SensitivityUnaryPopulationSupport

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGuardEvents
open SensitivityOperativeHeads SensitivityHighHeadGuardBridge
open Sensitivity213981Formal
set_option autoImplicit false

variable {V S I Color : Type} {L : ℕ}

def unaryLooplessIndexing [Fintype V] (arc : V → V → Prop)
    (hloop : ∀ v, ¬ arc v v) : GuardIndexing (unaryTournamentGuards arc) arc where
  check := fun _ w => {(w,())}
  member := by
    intro v w hvw
    exact (unaryIndexing arc).member v w ⟨fun h => hloop v (h ▸ hvw),hvw⟩
  nonempty := by intro v w _; exact Finset.singleton_nonempty _
  destination := by
    intro v w socket hs
    exact congrArg Prod.fst (Finset.mem_singleton.mp hs)
  complete := by
    intro v check hc
    obtain ⟨w,hw,hc⟩ := (unaryIndexing arc).complete v check hc
    exact ⟨w,hw.2,hc⟩



def incomingPopulation [Fintype V] (arc : V → V → Prop) (H : Finset V) (q : ℕ) : Finset V :=
  Finset.univ.filter fun v => v ∉ H ∧ H.card-q ≤ (H.filter fun w => arc w v).card
















end
end SensitivityUnaryPopulationSupport


