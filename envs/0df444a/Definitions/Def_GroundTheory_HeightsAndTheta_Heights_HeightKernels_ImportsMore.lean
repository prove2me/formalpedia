-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsMore
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsMore
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T10:28:14.550002+00:00
-- url     : https://prove2.me/theorems/59621364-38f5-460a-80c8-713bab180f46
-- title:
--   Imports More
-- statement:
--   Definitions and structural lemmas for Imports More, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ImportsMore.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_LatticeBundleObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors ComplexOrder
noncomputable section
def S6.MatrixSubDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) (M : Submodule (𝓞 K) (Fin N → K))
    [Module.Finite (𝓞 K) M] (H : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (hH : ∀ σ, (H σ).PosDef)
    (hconj : ∀ σ, H (conjugate σ) = (H σ).map (starRingEnd ℂ)),
    Submodule.span K (M : Set (Fin N → K)) = ⊤ →
    ∀ (r : ℕ) (u : Fin r → Fin N → K), LinearIndependent K u →
      (matrixBundle M H hH hconj).rank (satSub M u) = r ∧
        (matrixBundle M H hH hconj).degree (satSub M u) = subDegree M H u
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels


