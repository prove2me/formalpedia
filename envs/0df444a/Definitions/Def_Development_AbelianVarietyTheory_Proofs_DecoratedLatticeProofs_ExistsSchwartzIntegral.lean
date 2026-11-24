-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSchwartzIntegral
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSchwartzIntegral
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T16:10:42.508284+00:00
-- url     : https://prove2.me/theorems/183e343d-16d6-47cc-a01e-1484a5efe393
-- title:
--   Exists Schwartz Integral
-- statement:
--   Definitions and structural lemmas for Exists Schwartz Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchwartzIntegral.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff Classical
namespace GlobalTheory.CompactAvgSchwartz
section Real
variable {S V : Type} [TopologicalSpace S] [CompactSpace S] [NormedAddCommGroup V] [NormedSpace ℝ V]
end Real
section Fin
variable {S Y : Type} [TopologicalSpace S] [TopologicalSpace Y] {a b : S → Y → Y} {g : Y → ℂ}
end Fin
def lmul {ι : Type} [Fintype ι] {m : ℕ} (n : ℕ) (A : ι → Matrix (Fin m) (Fin m) ℂ) :
    (ι → Fin m → Fin n → ℂ) →L[ℝ] (ι → Fin m → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X τ i j => ∑ c, A τ i c * X τ c j
      map_add' := fun X X' => by
        funext τ i j
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r X => by
        funext τ i j
        simp [Finset.mul_sum, mul_left_comm] }
end GlobalTheory.CompactAvgSchwartz
end


