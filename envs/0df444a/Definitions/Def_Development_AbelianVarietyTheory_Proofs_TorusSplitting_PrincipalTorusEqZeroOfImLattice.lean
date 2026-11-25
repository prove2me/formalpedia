-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_PrincipalTorusEqZeroOfImLattice
-- name    : Development_AbelianVarietyTheory_Proofs_TorusSplitting_PrincipalTorusEqZeroOfImLattice
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:51:39.4268+00:00
-- url     : https://prove2.me/theorems/8f8d133e-90d7-4c6c-a333-2c2c3447db1f
-- title:
--   Principal Torus Eq Zero Of Im Lattice
-- statement:
--   Definitions and structural lemmas for Principal Torus Eq Zero Of Im Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/PrincipalTorusEqZeroOfImLattice.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace
namespace GlobalTheory
noncomputable section
variable {E : Type} [Field E] [NumberField E]
end
end GlobalTheory


