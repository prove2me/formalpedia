-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ModOne
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ModOne
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:59:03.259829+00:00
-- url     : https://prove2.me/theorems/a29c9198-a090-46ef-a882-3c85261e2ac7
-- title:
--   Mod One
-- statement:
--   Definitions and structural lemmas for Mod One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ModOne.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal Pointwise
noncomputable section
namespace PI.ScMuExists.UnitaryGroupMassFormula
section Conj
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def conjSub (N : Subgroup G) (g : G) (h1 : ∀ x ∈ N, g * x * g⁻¹ ∈ N) (h2 : ∀ x ∈ N, g⁻¹ * x * g ∈ N) :
    N ≃* N where
  toFun x := ⟨g * x * g⁻¹, h1 x x.2⟩
  invFun x := ⟨g⁻¹ * x * g, h2 x x.2⟩
  left_inv x := Subtype.ext (show g⁻¹ * (g * (x : G) * g⁻¹) * g = x by group)
  right_inv x := Subtype.ext (show g * (g⁻¹ * (x : G) * g) * g⁻¹ = x by group)
  map_mul' x y := Subtype.ext (show g * ((x : G) * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group)
variable [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
end Conj
end PI.ScMuExists.UnitaryGroupMassFormula


