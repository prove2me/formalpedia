-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_UniformCoefficientBounds_CoefBoundUniform
-- name    : CompanionTheory_HarishChandraModules_BesselParameterIntegrals_UniformCoefficientBounds_CoefBoundUniform
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T02:26:14.95425+00:00
-- url     : https://prove2.me/theorems/6e1ea928-7012-424f-a464-d3b6a0c8ba40
-- title:
--   Coef Bound Uniform
-- statement:
--   Definitions and structural lemmas for Coef Bound Uniform, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/UniformCoefficientBounds/CoefBoundUniform.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff InnerProductSpace
noncomputable section
namespace CompanionTheory.D.Upq.Sm
open PI
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {G K : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
def smSub (G : Set (Mat n)) (σ : Mat n → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {v | IsSm G σ v}
  add_mem' := IsSm.add
  zero_mem' := IsSm.zero
  smul_mem' c _ hv := IsSm.smul hv c
structure GoodSub (G K : Set (Mat n)) (σ : Mat n → (H →L[ℂ] H)) (T : Submodule ℂ H) : Prop where
  fin : FiniteDimensional ℂ T
  sm : ∀ v ∈ T, IsSm G σ v
  stab : ∀ k ∈ K, ∀ v ∈ T, σ k v ∈ T
end CompanionTheory.D.Upq.Sm
end


