-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TotallyDisconnectedSpaceRestrictedProduct
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_TotallyDisconnectedSpaceRestrictedProduct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:24.905576+00:00
-- url     : https://prove2.me/theorems/297db2bd-a1e7-47cd-8966-8a2f31502625
-- title:
--   Totally Disconnected Space Restricted Product
-- statement:
--   Definitions and structural lemmas for Totally Disconnected Space Restricted Product, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/TotallyDisconnectedSpaceRestrictedProduct.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
namespace RestrictedTensor
open Filter Function Set Topology
open scoped RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  {K : ∀ v, Subgroup (G v)}
instance totallyDisconnectedSpace_restrictedProduct [∀ v, TotallyDisconnectedSpace (G v)] :
    TotallyDisconnectedSpace (Πʳ v, [G v, K v]) :=
  ⟨fun s _ hs => Set.subsingleton_of_image
    (f := ((↑) : (Πʳ v, [G v, K v]) → ∀ v, G v)) (fun x y h => Subtype.ext h)
    s (isTotallyDisconnected_of_totallyDisconnectedSpace _ _ (Set.subset_univ _)
      (hs.image _ RestrictedProduct.continuous_coe.continuousOn))⟩
variable (K) in

def boxSubgroup (K' : ∀ v, Subgroup (G v)) : Subgroup (Πʳ v, [G v, K v]) where
  carrier := {g | ∀ v, g v ∈ K' v}
  mul_mem' {a b} ha hb v := by
    rw [RestrictedProduct.mul_apply]
    exact (K' v).mul_mem (ha v) (hb v)
  one_mem' v := by
    rw [RestrictedProduct.one_apply]
    exact (K' v).one_mem
  inv_mem' {a} ha v := by
    rw [RestrictedProduct.inv_apply]
    exact (K' v).inv_mem (ha v)
end RestrictedTensor
end GroundTheory.Automorphic


