-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdGenDeg
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdGenDeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:32.252887+00:00
-- url     : https://prove2.me/theorems/406fb20a-22f7-484d-9053-0aecf6665d06
-- title:
--   PDual Std Gen Deg
-- statement:
--   Definitions and structural lemmas for PDual Std Gen Deg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdGenDeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsFurther
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial
namespace DualStdGenDeg
def fibreBlk₀ : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit) :=
  ⟨Sum.inl (), fun ⟨_, h⟩ => Sum.inr_ne_inl h⟩
def fibreCoord {T : Type} {i : ℕ} (c : T) :
    ∀ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit), fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr k
  | ⟨Sum.inl (), _⟩ => c
  | ⟨Sum.inr (), h⟩ => absurd ⟨(), rfl⟩ h
end DualStdGenDeg
end GroundTheory.Heights₂.Heights


