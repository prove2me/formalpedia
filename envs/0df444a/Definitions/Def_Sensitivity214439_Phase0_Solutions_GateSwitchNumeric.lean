-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_GateSwitchNumeric
-- name    : Sensitivity214439_Phase0_Solutions_GateSwitchNumeric
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:39:47.179952+00:00
-- url     : https://prove2.me/theorems/8fe6d393-b5c2-47cd-8dcb-8a54b52ceffd
-- title:
--   Numerical color-switch entries and fees
-- statement:
--   The switch block of a flattened twelve-rank profile begins at offset $312$, with entry $W(i,j)$ stored at $312+12i+j$. For guard and target rank functions $g,t$, the numerical switching fee is
--   $$
--   \max\!\left\{B(g_j,t_i),\
--   \begin{cases}
--   A(g_i,t_j),&\text{unary gate},\\
--   C(g_i,t_j),&\text{paired gate}.
--   \end{cases}\right\}.
--   $$
--   It covers the two possible orientations of the separating guard between an old accepted row and a newly accepted row.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/GateSwitchNumeric.lean lines 13–19; SHA256 c2e294a733cee6a4cbdfb63f2a4966043c9fec93c4dc86608bdb4a326f34fa36; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericSemanticBridge
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityGateSwitchBounds
end SensitivityGateSwitchBounds
namespace SensitivityGateSwitchNumeric
end SensitivityGateSwitchNumeric
namespace SensitivityLocalNumericSemantics
end SensitivityLocalNumericSemantics
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-! Exact array certificates for the strict winner-switch coordinate. -/
namespace SensitivityGateSwitchNumeric

noncomputable section
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGateSwitchBounds
open SensitivityLocalNumericSemantics

variable {V I Color : Type} [Fintype V] [Fintype I]

def switchEntry (values : Array ℕ) (i j : Fin 12) : ℕ :=
  values[312 + i.val * 12 + j.val]?.getD 0

def switchFee (unary : Bool) (v : NumericBounds)
    (guard target : Fin 12 → Fin 12) (i j : Fin 12) : ℕ :=
  max (SensitivityLocalNumeric.entry v.profile 1 (guard j).val (target i).val)
    (SensitivityLocalNumeric.entry v.profile (if unary then 0 else 3) (guard i).val (target j).val)
















end
end SensitivityGateSwitchNumeric


