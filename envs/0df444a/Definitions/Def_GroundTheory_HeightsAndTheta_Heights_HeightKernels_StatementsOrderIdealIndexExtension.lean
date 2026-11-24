-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsOrderIdealIndexExtension
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsOrderIdealIndexExtension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:23.786873+00:00
-- url     : https://prove2.me/theorems/1760031a-3e87-47c7-b8e3-37f237d6aacc
-- title:
--   Statements Order Ideal Index Extension
-- statement:
--   Definitions and structural lemmas for Statements Order Ideal Index Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsOrderIdealIndexExtension.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsInvertibleIdealIndex
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
open NumberField
noncomputable section
def OrderIdealIndexExtension.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : Subring L), Module.Finite ℤ B →
    ∃ (r : ℕ) (s : B), s ≠ 0 ∧ Module.finrank ℚ L = r * Module.finrank ℤ B ∧
      (∀ I : Ideal B, I ≠ ⊥ → I.toAddSubgroup.index ≠ 0) ∧
      ∀ I : Ideal B, I ≠ ⊥ → (I.IsPrincipal ∨ I ⊔ Ideal.span {s} = ⊤) →
        (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B))).toAddSubgroup.relIndex
            (1 : Submodule (𝓞 L) L).toAddSubgroup = I.toAddSubgroup.index ^ r
end
end GroundTheory.Heights₂.Heights


