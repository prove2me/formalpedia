-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineSourceCover
-- name    : Sensitivity214439_Phase0_Solutions_BaselineSourceCover
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:06:27.793553+00:00
-- url     : https://prove2.me/theorems/9a3f6849-f436-4d6f-9ee4-24642b5b4377
-- title:
--   Finite recipe conditions for baseline source-state coverage
-- statement:
--   The baseline source-cover conditions require allowances below eight, soft cutoffs antitone in rank, and legal target ranks ordered above core $5$:
--   $$
--   \ell_j(f)\ge5,\qquad \ell_j(f)\le u_j(f)
--   \qquad(f\le q_j).
--   $$
--   Both target functions must be monotone in the legal failure count. The numerical recipe type is the baseline-loss recipe, and the finite range of these conditions gives a decidable predicate.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineSourceCover.lean lines 14–26; SHA256 022ac43a7514e3c24f4dd4ef88be69994f6bdf500cb41bc3f7f8b4bdbbd1605d; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
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

namespace SensitivityBaselineGuardStates
end SensitivityBaselineGuardStates
namespace SensitivityBaselineSourceCover
end SensitivityBaselineSourceCover
namespace SensitivityFiniteRanks
end SensitivityFiniteRanks
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityLocalNumericSemantics
end SensitivityLocalNumericSemantics
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates



/-! Actual exact-source rows reach the sorted finite baseline certificate states. -/
namespace SensitivityBaselineSourceCover

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGuardEvents
open SensitivityFiniteRanks SensitivityStrictGateStates SensitivityLocalNumericSemantics
open SensitivityBaselineGuardStates

abbrev NumericRecipe := SensitivityBaselineLossNumeric.Recipe


def Conditions (r : NumericRecipe) : Prop :=
  (∀ j, r.allowance j < 8) ∧
  (∀ i j, i ≤ j → r.soft j ≤ r.soft i) ∧
  (∀ j (f : Fin 8), f.val ≤ r.allowance j → 5 ≤ (r.lo j f.val).val ∧ r.lo j f.val ≤ r.hi j f.val) ∧
  (∀ j (f g : Fin 8), f ≤ g → g.val ≤ r.allowance j →
    r.lo j f.val ≤ r.lo j g.val ∧ r.hi j f.val ≤ r.hi j g.val)

instance (r : NumericRecipe) : Decidable (Conditions r) := by
  unfold Conditions
  infer_instance









variable {V I Color : Type}









end
end SensitivityBaselineSourceCover


