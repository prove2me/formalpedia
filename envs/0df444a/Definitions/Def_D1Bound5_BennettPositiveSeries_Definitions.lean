-- Prove2me | Definitions.Def_D1Bound5_BennettPositiveSeries_Definitions
-- name    : D1Bound5_BennettPositiveSeries_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:23:49.646195+00:00
-- url     : https://prove2.me/theorems/530aa393-595e-400d-9037-86b922739d54
-- title:
--   Bennett Positive Series
-- statement:
--   The coefficientwise absolute majorant of an actual local pole factor. Writing the coefficients explicitly avoids any implicit choice of signs. The named objects in this bundle include `bennettPoleMajorant`.
-- source:
--   D1Bound5/BennettPositiveSeries.lean, lines 11-14, SHA-256 97c8e1703cfe77445d9777396cd5b2920aa185f7c75649ef58d66b03bb6b026f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order

section
open Finset

namespace D1Bound5

/-- The coefficientwise absolute majorant of an actual local pole factor.
Writing the coefficients explicitly avoids any implicit choice of signs. -/
noncomputable def bennettPoleMajorant (d : ℝ) (p : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (fun n => |Ring.choose (-(p : ℝ)) n| * (d⁻¹) ^ (p + n))



















end D1Bound5
end


