-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_Places
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:43:08.747429+00:00
-- url     : https://prove2.me/theorems/23a4b84e-8e0a-4d58-9202-72bbcf26ef3a
-- title:
--   Places
-- statement:
--   Definitions and structural lemmas for Places, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Places.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isOpen_boxSubgroup

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
open Filter Function Module Set
open scoped RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] {K : ∀ v, Subgroup (G v)}
section Group
variable [DecidableEq ι]
variable (K) in

def singleHom (v : ι) : G v →* Πʳ w, [G w, K w] where
  toFun := RestrictedProduct.mulSingle K v
  map_one' := RestrictedProduct.mulSingle_one K v
  map_mul' x y := RestrictedProduct.mulSingle_mul K v x y
def eraseAt (v : ι) (g : Πʳ w, [G w, K w]) : Πʳ w, [G w, K w] :=
  (singleHom K v (g v))⁻¹ * g
end Group
variable [∀ v, TopologicalSpace (G v)] [∀ v, IsTopologicalGroup (G v)]
  [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)] [∀ v, TotallyDisconnectedSpace (G v)]
  [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))] [hKc : ∀ v, CompactSpace (K v)]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (Πʳ v, [G v, K v]) V}
  (hρ : IsSmooth ρ) {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
  (hK'o : ∀ v, IsOpen (K' v : Set (G v))) (hK'e : ∀ᶠ v in cofinite, K' v = K v)
section Window
variable [DecidableEq ι]
def placeOps (v : ι) : Set (End ℂ (fixedVectors ρ (boxSubgroup K K'))) :=
  range fun x : G v => heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e)
    (isOpen_boxSubgroup hK'o hK'e) (singleHom K v x)
end Window
end RestrictedTensor
end GroundTheory.Automorphic


