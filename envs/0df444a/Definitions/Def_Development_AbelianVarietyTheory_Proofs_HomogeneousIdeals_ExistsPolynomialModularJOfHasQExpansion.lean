-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:41.687798+00:00
-- url     : https://prove2.me/theorems/9bf77aeb-0932-4d03-8d51-6e8b81094f6f
-- title:
--   Exists Polynomial Modular JOf Has QExpansion
-- statement:
--   Definitions and structural lemmas for Exists Polynomial Modular JOf Has QExpansion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsPolynomialModularJOfHasQExpansion.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real ArithmeticFunction.sigma
noncomputable section
namespace GlobalTheory
local notation "𝕢" => Function.Periodic.qParam
def modularJ (τ : ℍ) : ℂ := E₄ τ ^ 3 / discriminant τ
end GlobalTheory


