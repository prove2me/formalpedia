-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StMatSpec
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_StMatSpec
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:33:32.336476+00:00
-- url     : https://prove2.me/theorems/6bf70200-91b9-452f-a184-a22abe661204
-- title:
--   St Mat Spec
-- statement:
--   Definitions and structural lemmas for St Mat Spec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StMatSpec.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField GlobalTheory.HL
open scoped Classical
noncomputable section
namespace GlobalTheory.HL.TraceConjugationCover
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ}
def stMat (G : GFrames A r k) (x : G.GLV) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  if h : ∃ B : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ∀ b, x (G.f' b) = ∑ a, B a b • G.f' a then h.choose else 0
end GlobalTheory.HL.TraceConjugationCover
end


