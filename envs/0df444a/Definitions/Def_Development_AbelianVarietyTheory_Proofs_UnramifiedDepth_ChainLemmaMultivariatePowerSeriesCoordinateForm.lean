-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:30:48.082909+00:00
-- url     : https://prove2.me/theorems/cba32eab-8b28-4478-a0f7-fac8e2267eb2
-- title:
--   Chain Lemma Multivariate Power Series Coordinate Form
-- statement:
--   Definitions and structural lemmas for Chain Lemma Multivariate Power Series Coordinate Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainLemmaMultivariatePowerSeriesCoordinateForm.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PsWeightCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh MvPowerSeries
namespace GlobalTheory.ChainCoord
section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ}
end
section
variable {C : Type} [Field C]
noncomputable def kap (C : Type) [Field C] (l s : ℕ) : C :=
  (-1) ^ s * ((l : C) ^ (∑ u ∈ Finset.range s, (l ^ 2) ^ u))⁻¹
noncomputable def pure {d M : ℕ} (l : ℕ) (π : ℕ → Fin d → Fin M → C) (s : ℕ) (c : Fin d) :
    MvPowerSeries (Fin M) C :=
  ∑ j, MvPowerSeries.C (R := C) (kap C l s * π s c j) *
    (X j : MvPowerSeries (Fin M) C) ^ ((l ^ 2) ^ s)
end
end GlobalTheory.ChainCoord


