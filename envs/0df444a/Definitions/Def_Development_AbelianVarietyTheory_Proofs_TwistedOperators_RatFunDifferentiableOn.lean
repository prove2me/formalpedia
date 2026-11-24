-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RatFunDifferentiableOn
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_RatFunDifferentiableOn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:23.759967+00:00
-- url     : https://prove2.me/theorems/14175911-f468-4cf1-ad3a-ad1481bd1470
-- title:
--   Rat Fun Differentiable On
-- statement:
--   Definitions and structural lemmas for Rat Fun Differentiable On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RatFunDifferentiableOn.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BorelParam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
noncomputable section
namespace GlobalTheory.DoublingSeries
def ratFun (q N : ℕ) (α : Fin N → ℂˣ) (X : ℂ) : ℂ :=
  (∏ i, (1 - (α i : ℂ) * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X)⁻¹) *
    (∏ i, (1 - (((α i)⁻¹ : ℂˣ) : ℂ) * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X)⁻¹) *
      ∏ i ∈ Finset.Icc 1 N, (1 - (q : ℂ) ^ (-(i : ℂ)) * X ^ 2)
end GlobalTheory.DoublingSeries


