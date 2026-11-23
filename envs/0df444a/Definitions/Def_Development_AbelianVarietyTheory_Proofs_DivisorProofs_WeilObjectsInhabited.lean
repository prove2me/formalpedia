-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:41.839741+00:00
-- url     : https://prove2.me/theorems/8b088931-dbe8-4683-85fd-99c3e6e5aa84
-- title:
--   Weil Objects Inhabited
-- statement:
--   Definitions and structural lemmas for Weil Objects Inhabited, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilObjectsInhabited.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Theorems.Thm_GlobalTheory_WeilM_splitOm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Kronecker
namespace GlobalTheory.WeilM
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {α β κ : Type}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] [Invertible (2 : F)]
section Pair
variable {R : Type} [CommRing R]
omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] in
theorem flat_transpose (σ : κ ≃ α × β) (X : Matrix α β R) : flat (σ.trans (Equiv.prodComm α β)) Xᵀ = flat σ X := rfl
omit [DecidableEq β] [Fintype κ] in
theorem splitOm_swap_apply (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle) (J : Matrix α α (R × R)) (σ : κ ≃ α × β)
    (g : UG (swapA R) J) (φ : (κ → R) → ℂ) (X : Matrix α β R) :
    splitOm m χ J (σ.trans (Equiv.prodComm α β)) g φ (flat σ X) =
      splitChar m χ (Fintype.card β) (GeneralLinearGroup.det (ugFst J g)) * φ (flat σ (((ugFst J g)⁻¹).val * X)) := by
  rw [splitOm_apply, ← flat_transpose σ X, LinearEquiv.symm_apply_apply, ← transpose_mul, flat_transpose]
def splitPair (m : Rˣ →* ℝ≥0) (χA χB : (R × R)ˣ →* Circle) (JA : Matrix α α (R × R)) (JB : Matrix β β (R × R))
    (σ : κ ≃ α × β) : UG (swapA R) JA × UG (swapA R) JB →* Module.End ℂ ((κ → R) → ℂ) :=
  (splitOm m χB JA (σ.trans (Equiv.prodComm α β))).noncommCoprod (splitOm m χA JB σ) fun g h => by
    refine LinearMap.ext fun φ => funext fun u => ?_
    obtain ⟨X, rfl⟩ := (flat σ).surjective u
    rw [Module.End.mul_apply, Module.End.mul_apply, splitOm_swap_apply, splitOm_apply, splitOm_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, splitOm_swap_apply, Matrix.mul_assoc, mul_left_comm]
end Pair
end GlobalTheory.WeilM
end


