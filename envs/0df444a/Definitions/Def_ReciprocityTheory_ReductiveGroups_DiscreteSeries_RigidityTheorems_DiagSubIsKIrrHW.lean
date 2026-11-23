-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_DiagSubIsKIrrHW
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_DiagSubIsKIrrHW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:39:44.599796+00:00
-- url     : https://prove2.me/theorems/d985307c-91bb-4de7-a1b5-9a69da277d69
-- title:
--   Diag Sub Is KIrr HW
-- statement:
--   Definitions and structural lemmas for Diag Sub Is KIrr HW, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/DiagSubIsKIrrHW.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_InKRealSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix WithLp
namespace ReciprocityTheory.ChartRestriction.DS
namespace USum
variable {n : ℕ} {ε : Fin n → Bool}
variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {E₂ : Fin n → Fin n → Module.End ℂ D₂}
  {V₁ : Submodule ℂ D₁} {V₂ : Submodule ℂ D₂}
def diagι (φ : V₁ →ₗ[ℂ] V₂) : V₁ →ₗ[ℂ] sD D₁ D₂ :=
  ofP ∘ₗ (V₁.subtype.prod (V₂.subtype ∘ₗ φ))
def diagSub (φ : V₁ →ₗ[ℂ] V₂) : Submodule ℂ (sD D₁ D₂) := LinearMap.range (diagι φ)
end USum
end ReciprocityTheory.ChartRestriction.DS


