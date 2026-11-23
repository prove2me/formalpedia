-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_WeilPairs_EtaDef
-- name    : Development_WeilBound_ThetaLifts_Reductions_WeilPairs_EtaDef
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:02.004883+00:00
-- url     : https://prove2.me/theorems/17d45070-0605-4382-9347-f485498f7b73
-- title:
--   Eta Def
-- statement:
--   Definitions and structural lemmas for Eta Def, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/WeilPairs/EtaDef.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HasInfExpF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF Formalism.IndefR.LiftF
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def UnramInert (σ : E →ₐ[F] E) (η : (AF F ⊗[F] E)ˣ →* Circle) : Prop :=
  ∀ x : (AEF F E)ˣ, infPartF F E (x : AEF F E) = 1 → (∀ e, IsSplitIdemF σ e → e * (x : AEF F E) = e) →
    finPartF F E (x : AEF F E) ∈ intAEF F E → finPartF F E ((x⁻¹ : (AEF F E)ˣ) : AEF F E) ∈ intAEF F E → η x = 1
end PositivityTheory.ThKW
end


