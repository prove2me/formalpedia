-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:15.21875+00:00
-- url     : https://prove2.me/theorems/190eceb2-920d-46e0-93a8-0c5108eb4fa8
-- title:
--   Dim Statement
-- statement:
--   Definitions and structural lemmas for Dim Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/DimStatement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsPairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
def DimStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (Y : GT ι) (q : ℕ), 1 ≤ q →
    FiniteDimensional ℂ (Y.Sec q) ∧ Module.finrank ℂ (Y.Sec q) ≤ q ^ Fintype.card ι
end
end ReciprocityTheory.ChartRestriction.G.I2


