-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_JoinCoordMidVar
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_JoinCoordMidVar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:23.036385+00:00
-- url     : https://prove2.me/theorems/5ec8d825-704b-4464-ac20-1014c9bbbf9a
-- title:
--   Join Coord Mid Var
-- statement:
--   Definitions and structural lemmas for Join Coord Mid Var, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/JoinCoordMidVar.lean

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
def midDeg (a : K ⊕ K' → ℤ) : K ⊕ (K₂ ⊕ K') → ℤ :=
  Sum.elim (fun k => a (.inl k)) (Sum.elim 0 (fun k => a (.inr k)))
def midVar (ι₂ : K₂ → Type) :
    (Σ k : K ⊕ K', Sum.elim ι ι' k) → (Σ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k)
  | ⟨.inl k, i⟩ => ⟨.inl k, i⟩
  | ⟨.inr k, i⟩ => ⟨.inr (.inr k), i⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles


