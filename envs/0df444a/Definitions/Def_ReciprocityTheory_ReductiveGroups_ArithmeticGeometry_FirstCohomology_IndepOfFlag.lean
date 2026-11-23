-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IndepOfFlag
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IndepOfFlag
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:58.116332+00:00
-- url     : https://prove2.me/theorems/906b010c-7b30-4caf-9248-fdb75e8bb4d2
-- title:
--   Indep Of Flag
-- statement:
--   Definitions and structural lemmas for Indep Of Flag, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/IndepOfFlag.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ReducedBasisStatement
import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.H1.RB
open Finset InnerProductSpace Submodule Module ReciprocityTheory.ReducedBases.T2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def V {d : ℕ} (u : Fin d → E) (n : ℕ) : Submodule ℝ E := span ℝ (u '' {l | l.val < n})
def phi {d : ℕ} (u : Fin d → E) (k : Fin d) (x : E) : ℝ := ⟪gs u k, x⟫_ℝ / ‖gs u k‖ ^ 2
section phi
variable {d : ℕ} (u : Fin d → E) (k : Fin d)
end phi
end ReciprocityTheory.ChartRestriction.G.H1.RB


