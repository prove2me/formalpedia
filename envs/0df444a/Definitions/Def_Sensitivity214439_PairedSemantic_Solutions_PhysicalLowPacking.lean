-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PhysicalLowPacking
-- name    : Sensitivity214439_PairedSemantic_Solutions_PhysicalLowPacking
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:45:51.616608+00:00
-- url     : https://prove2.me/theorems/7d2a4edf-fa5a-4ef6-b7d7-496d6ee4bc87
-- title:
--   Physical row fibers and macro conflict multiplicities
-- statement:
--   For a finite physical row set $S\subseteq M\times B$, define the fiber $S_m=\{b:(m,b)\in S\}$ and macro count $n_m=|S_m|$. Given a side pin $p(m)$ for each macro, an external macro conflict $m\rightsquigarrow n$ means $m\ne n$, a macro arc from $m$ to $n$, and an arc label equal to $p(n)$. Each such conflict contributes the full destination multiplicity $n_n$ to the source's guard load.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/PhysicalLowPacking.lean lines 19–24; SHA256 348c258835353412d18067155d9c52fff6f08e2b0ddfd7b4efe14d9348432e4c; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

namespace Sensitivity213981Formal.TournamentHighRows
end Sensitivity213981Formal.TournamentHighRows
namespace SensitivityActiveSocketGeometry
end SensitivityActiveSocketGeometry
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityLowPacking
end SensitivityLowPacking
namespace SensitivityMarkedSocketPopulation
end SensitivityMarkedSocketPopulation
namespace SensitivityPhysicalLowPacking
end SensitivityPhysicalLowPacking
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivityTournamentBudgets
end SensitivityTournamentBudgets



/-! Exact passage from low physical rows to the macro multiplicity packing.
The loss of an internal tournament edge costs one guard at its source, while an
external macro conflict costs every occupied physical row at its destination. -/
namespace SensitivityPhysicalLowPacking

noncomputable section
open scoped Classical BigOperators
open SensitivityLowPacking SensitivityRankedConstruction SensitivityHighHeadGuardBridge
open SensitivityActiveSocketGeometry SensitivityMarkedSocketPopulation
open Sensitivity213981Formal.TournamentHighRows SensitivityTournamentBudgets
set_option autoImplicit false

variable {M B I Color : Type} [Fintype M] [Fintype B] {L : ℕ}

def fiber (rows : Finset (M × B)) (m : M) : Finset B := Finset.univ.filter fun b => (m, b) ∈ rows

def macroCount (rows : Finset (M × B)) (m : M) : ℕ := (fiber rows m).card

def macroConflict (macroArc : M → M → Prop) (label : M → M → Bool) (pin : M → Bool)
    (m n : M) : Prop := n ≠ m ∧ macroArc m n ∧ label m n = pin n



























end
end SensitivityPhysicalLowPacking


