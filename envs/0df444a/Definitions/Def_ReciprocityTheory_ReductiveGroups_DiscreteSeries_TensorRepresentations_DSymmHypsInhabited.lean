-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:31.36641+00:00
-- url     : https://prove2.me/theorems/f47bdf5a-bdd6-4dc3-a17a-637f7f21e8ad
-- title:
--   DSymm Hyps Inhabited
-- statement:
--   Definitions and structural lemmas for DSymm Hyps Inhabited, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DSymmHypsInhabited.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA
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
variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]
def eT (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n) : Module.End ℂ (TensorProduct ℂ N (Fock n)) :=
  TensorProduct.map (E a b) LinearMap.id
def cpT (i a : Fin n) : Module.End ℂ (TensorProduct ℂ N (Fock n)) := TensorProduct.map LinearMap.id (cpFock i a)
def cmT (i a : Fin n) : Module.End ℂ (TensorProduct ℂ N (Fock n)) := TensorProduct.map LinearMap.id (cmFock i a)
def gradT : Module.End ℂ (TensorProduct ℂ N (Fock n)) :=
  TensorProduct.map LinearMap.id (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap
def physicalSubspace (ε : Fin n → Bool) : Submodule ℂ (TensorProduct ℂ N (Fock n)) :=
  ⨅ i : Fin n, ⨅ a : Fin n, ⨅ (_ : ¬ (ε i = true ∧ ε a = false)), LinearMap.ker (cmT (N := N) i a)
def tensFock (V : Submodule ℂ N) : Submodule ℂ (TensorProduct ℂ N (Fock n)) :=
  LinearMap.range (TensorProduct.map V.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n))
end ReciprocityTheory.ChartRestriction.DS


