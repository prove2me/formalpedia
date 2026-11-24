-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpModel
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpModel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:35.822814+00:00
-- url     : https://prove2.me/theorems/9904b18e-7c22-43eb-92e3-c492461cf310
-- title:
--   PBlow Up Model
-- statement:
--   Definitions and structural lemmas for PBlow Up Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpModel.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsReesAlgebraDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
section Graded
variable {σ : Type*} {R : Type*} [CommRing R]
end Graded
section BlowUp
variable {K : Type*} [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*} [CommRing R]
def blowUpAtOne (u : J → MRing ι R) : (Σ o, extIdx ι J o) → MRing ι R
  | ⟨none, j⟩ => u j
  | ⟨some k, i⟩ => X ⟨k, i⟩
def blowUpDegMap (N : K → ℕ) : (Option K → ℕ) →+ (K → ℕ) where
  toFun m k := m (some k) + m none * N k
  map_zero' := by
    funext k
    simp
  map_add' m m' := by
    funext k
    simp only [Pi.add_apply]
    ring
end BlowUp
end
end GroundTheory.Heights₂.Heights.NumbersDVR


