-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_TwoStepUnipotentCompactModSubring
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_TwoStepUnipotentCompactModSubring
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:30.117868+00:00
-- url     : https://prove2.me/theorems/6593f497-ef51-4bbf-adc0-f16e55bc80b8
-- title:
--   Two Step Unipotent Compact Mod Subring
-- statement:
--   Definitions and structural lemmas for Two Step Unipotent Compact Mod Subring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/TwoStepUnipotentCompactModSubring.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
namespace GlobalTheory.TwoStepUnipotent
section
variable {S : Type} [Ring S] (st : S →+ S) (e₁ e₃ h : S)
def elt (b w : S) : S := 1 - st b + b + (w - h * (st b * b))
variable {st e₁ e₃ h}
end
end GlobalTheory.TwoStepUnipotent


