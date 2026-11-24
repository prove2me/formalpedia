-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_ActualLowPopulations
-- name    : Sensitivity214439_PairedSemantic_Solutions_ActualLowPopulations
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:56:32.566792+00:00
-- url     : https://prove2.me/theorems/390199f2-eca6-4d6a-aec7-ae823980562f
-- title:
--   Actual low populations by exact guard count
-- statement:
--   Defines the population vector of a finite candidate set by counting candidates at each exact guard-count grade. Prefix cardinalities and prefix budgets used by the numerical population inequalities are computed from these exact-count entries.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/ActualLowPopulations.lean lines 16–17; SHA256 d35ce783f26ec323d60b57d38df5139dc0b171fbdfafd1ff8b980a54e3c80a43; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PairedPopulationConstraints
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
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityActualLowPopulations
end SensitivityActualLowPopulations
namespace SensitivityOperativeHeads
end SensitivityOperativeHeads
namespace SensitivityPairedPopulation
end SensitivityPairedPopulation
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-! The four integer population variables are exact counts of actual
operative low rows. Their prefixes and spent budgets equal the sets and
finite sums used by the semantic graph inequalities. -/
namespace SensitivityActualLowPopulations

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityOperativeHeads SensitivityPairedPopulation
set_option autoImplicit false

variable {V S I Color : Type} {L : ℕ}

def population (candidates : Finset V) (count : V → ℕ) : Population :=
  fun grade => (candidates.filter fun v => count v = grade.val).card
























end
end SensitivityActualLowPopulations


