-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCoordEmbedBasis
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCoordEmbedBasis
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:48:59.779807+00:00
-- url     : https://prove2.me/theorems/d7661ea8-20b2-5d94-9d64-553ea52e02b2
-- title:
--   PCoord Embed Basis
-- statement:
--   Definitions and structural lemmas for PCoord Embed Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PCoordEmbedBasis.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StCoordEmbedBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField Module NumberField.InfinitePlace NumberField.mixedEmbedding
noncomputable section
variable (E : Type*) [Field E] [NumberField E] (ι : Type*) [Fintype ι]
def mixedSpaceEquivPiOfTotallyComplex [IsTotallyComplex E] :
    mixedSpace E ≃ₗ[ℝ] (InfinitePlace E → ℂ) where
  toFun p w := p.2 ⟨w, IsTotallyComplex.isComplex w⟩
  invFun g := (0, fun w => g w.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv p := by
    obtain ⟨x, y⟩ := p
    refine Prod.ext ?_ rfl
    funext w
    exact absurd w.2 (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1))
  right_inv _ := rfl
def embeddingBasisOfTotallyComplex [IsTotallyComplex E] :
    Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (InfinitePlace E → ℂ) :=
  (latticeBasis E).map (mixedSpaceEquivPiOfTotallyComplex E)
def piSwapEquiv : (ι → InfinitePlace E → ℂ) ≃ₗ[ℝ] (InfinitePlace E → ι → ℂ) :=
  { Equiv.piComm (fun (_ : ι) (_ : InfinitePlace E) => ℂ) with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


