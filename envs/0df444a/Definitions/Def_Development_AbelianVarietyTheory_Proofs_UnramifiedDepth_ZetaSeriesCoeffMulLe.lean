-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ZetaSeriesCoeffMulLe
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ZetaSeriesCoeffMulLe
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:44:24.512815+00:00
-- url     : https://prove2.me/theorems/ccfb5a90-4d96-4aa3-8915-a3a689274209
-- title:
--   Zeta Series Coeff Mul Le
-- statement:
--   Definitions and structural lemmas for Zeta Series Coeff Mul Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ZetaSeriesCoeffMulLe.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAddStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
namespace GlobalTheory
section Ord
open MvPowerSeries
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ)) {M : ℕ} (ρ : Fin M → ℝ)
end Ord
end GlobalTheory


