-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_JoinCoordAssocVar
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_JoinCoordAssocVar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:13.782804+00:00
-- url     : https://prove2.me/theorems/9cafb84c-64a6-47e4-acf9-e88728b16ea5
-- title:
--   Join Coord Assoc Var
-- statement:
--   Definitions and structural lemmas for Join Coord Assoc Var, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/JoinCoordAssocVar.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type}
def assocDeg (a : K ⊕ K' → ℤ) : K ⊕ (K' ⊕ K₂) → ℤ :=
  Sum.elim (fun k => a (.inl k)) (Sum.elim (fun k => a (.inr k)) 0)
def assocVar (ι₂ : K₂ → Type) :
    (Σ k : K ⊕ K', Sum.elim ι ι' k) → (Σ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k)
  | ⟨.inl k, i⟩ => ⟨.inl k, i⟩
  | ⟨.inr k, i⟩ => ⟨.inr (.inl k), i⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles


