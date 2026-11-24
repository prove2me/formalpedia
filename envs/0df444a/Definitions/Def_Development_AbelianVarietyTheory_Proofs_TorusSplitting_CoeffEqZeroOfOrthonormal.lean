-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
-- name    : Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:44.529622+00:00
-- url     : https://prove2.me/theorems/6a27558b-ba02-41da-bd79-17f505f43ac0
-- title:
--   Coeff Eq Zero Of Orthonormal
-- statement:
--   Definitions and structural lemmas for Coeff Eq Zero Of Orthonormal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/CoeffEqZeroOfOrthonormal.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
noncomputable section
namespace GlobalTheory.ThetaExist
variable {ι : Type} [Fintype ι]
def expH (w : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι → ℂ := fun v => cexp (Real.pi * Hf v w)
end GlobalTheory.ThetaExist


