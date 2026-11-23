-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:29:32.602296+00:00
-- url     : https://prove2.me/theorems/bc27c176-c8a3-459d-8696-af8f75d8f537
-- title:
--   Tensor V
-- statement:
--   Definitions and structural lemmas for Tensor V, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/TensorV.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
def coordV (c : Fin n) : (Fin n → M) →ₗ[ℂ] M := LinearMap.proj c
def tensV (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun c => (E a b).comp (coordV c) + if c = a then coordV b else 0
def tensVd (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun c => (E a b).comp (coordV c) - if c = b then coordV a else 0
def eeV (E : Fin n → Fin n → Module.End ℂ M) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun s => ∑ r, (E r s).comp (coordV r)
def eeVd (E : Fin n → Fin n → Module.End ℂ M) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun r => -∑ s, (E r s).comp (coordV s)
def diagOp (A : Module.End ℂ M) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun c => A.comp (coordV c)
end ReciprocityTheory.ChartRestriction.DS


