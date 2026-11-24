-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineNumericProperties
-- name    : Sensitivity214439_Phase0_Solutions_BaselineNumericProperties
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:06:20.034892+00:00
-- url     : https://prove2.me/theorems/6db11bc9-0fe4-4e7b-bc85-905dc9989842
-- title:
--   Monotonicity of numerical matching targets
-- statement:
--   A baseline recipe is target-monotone when, at every rank $j$, increasing the legal failure count can only increase each required target rank:
--   $$
--   f\le g\le q_j
--   \quad\Longrightarrow\quad
--   \ell_j(f)\le\ell_j(g)\ \land\ u_j(f)\le u_j(g).
--   $$
--   This property applies separately to the lower and upper members of the matching pair.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineNumericProperties.lean lines 10–12; SHA256 20b62da10ce872e52f749fd179607f55d40ba042872fd18601f489156a844cf8; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.List.Range

namespace SensitivityBaselineLossNumeric
end SensitivityBaselineLossNumeric



/-! Mathematical coverage facts for the baseline loss certificate states. -/
namespace SensitivityBaselineLossNumeric

def TargetMonotone (r : Recipe) : Prop :=
  ∀ j f g, f ≤ g → g ≤ r.allowance j →
    r.lo j f ≤ r.lo j g ∧ r.hi j f ≤ r.hi j g












end SensitivityBaselineLossNumeric


