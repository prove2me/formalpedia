-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaFunctionIsogenyRestriction
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaFunctionIsogenyRestriction
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T16:13:43.626318+00:00
-- url     : https://prove2.me/theorems/f7892909-7c71-4abe-a3c2-8c43d167d1e7
-- title:
--   Theta Function Isogeny Restriction
-- statement:
--   Definitions and structural lemmas for Theta Function Isogeny Restriction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaFunctionIsogenyRestriction.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ReciprocityTheory.ChartRestriction.G.I2
open scoped ComplexOrder
namespace GlobalTheory.ThetaTranslJet
noncomputable def pairing {σ : Type} [Fintype σ] (P : MvPolynomial σ ℂ) :
    MvPowerSeries σ ℂ →ₗ[ℂ] ℂ :=
  ∑ m ∈ P.support, (P.coeff m * ((∏ i, (m i).factorial : ℕ) : ℂ)) • MvPowerSeries.coeff m
variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
end GlobalTheory.ThetaTranslJet


