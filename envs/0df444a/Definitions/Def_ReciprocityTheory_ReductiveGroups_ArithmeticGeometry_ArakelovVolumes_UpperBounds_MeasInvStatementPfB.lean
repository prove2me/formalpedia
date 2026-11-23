-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:54:02.23681+00:00
-- url     : https://prove2.me/theorems/f30caba1-70fe-4b00-b911-fc12d4629a56
-- title:
--   Meas Inv Statement Pf B
-- statement:
--   Definitions and structural lemmas for Meas Inv Statement Pf B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_Lemmata_GeneralBFactForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
noncomputable section
section Mat
variable {n : ℕ}
end Mat
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
def Mt (v : Ix ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => v (τ, a, b)
def BC (ι : Type*) [Fintype ι] (r : ℕ) : Set (Ix ι r → ℂ) := {v | ∀ τ, ∀ i : Fin (r + 1), lminor (Mt v τ) i ≠ 0}
def sS (ι : Type*) (r : ℕ) : Set (Ix ι r → ℂ) := {w | ∀ τ b, w (τ, b, b) ≠ 0}
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI


