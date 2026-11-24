-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAn
-- name    : Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:09.95996+00:00
-- url     : https://prove2.me/theorems/6d4ecfe0-8075-4b71-8a28-07d47446cbeb
-- title:
--   Siegel Transport An
-- statement:
--   Definitions and structural lemmas for Siegel Transport An, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAn.lean

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
namespace PositivityTheory.ThK.SiegelT
open Matrix GlobalTheory.WeilM Topology Filter
variable {R : Type} [TopologicalSpace R] [T2Space R] {κ κ' : Type}
def conjL {X : Type} (l : (X → ℂ) →ₗ[ℂ] ℂ) : (X → ℂ) →ₗ[ℂ] ℂ where
  toFun φ := star (l (star φ))
  map_add' φ φ' := by rw [star_add, map_add, star_add]
  map_smul' a φ := by rw [star_smul, map_smul, star_smul, star_star]; rfl
def boxL {A : Type} (l : ((κ → A) → ℂ) →ₗ[ℂ] ℂ) (l' : ((κ' → A) → ℂ) →ₗ[ℂ] ℂ) : ((κ ⊕ κ' → A) → ℂ) →ₗ[ℂ] ℂ where
  toFun Φ := l' fun y => l fun x => Φ (Sum.elim x y)
  map_add' Φ Ψ := by
    rw [← map_add]
    congr 1
    funext y
    rw [Pi.add_apply, ← map_add]
    rfl
  map_smul' a Φ := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    funext y
    rw [Pi.smul_apply, ← map_smul]
    rfl
end PositivityTheory.ThK.SiegelT


