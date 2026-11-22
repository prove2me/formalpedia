-- Prove2me | Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
-- name    : Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:44:46.496228+00:00
-- url     : https://prove2.me/theorems/028ecfc2-a02c-437d-81eb-fe8eca2c4670
-- title:
--   Thick Average
-- statement:
--   Definitions and structural lemmas for Thick Average, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/ThickAverage.lean

import Definitions.Def_Formalism_ThickAverageLoss_ParametersAveragedDifferenceBound
import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
def e10 : E0 × H := (((1 : ZMod 2), (0 : ZMod 2)), 0)
def e01 : E0 × H := (((0 : ZMod 2), (1 : ZMod 2)), 0)
def TrivH (ψ : AddChar (E0 × H) ℂ) : Prop := ∀ h : H, ψ ((0, 0), h) = 1
def thickZ {m : ℕ} (Hs : CycHost H) (Nd : Nodes H m) (u0 t : H) (j : Fin m) : ℂ :=
  (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ s ∈ Nd.T2, ∑ ψ : AddChar (E0 × H) ℂ,
    ψ (-((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H)) * ((Nd.bj j : ℝ) : ℂ)
      * GC Hs ψ (Nd.a t / Nd.bj j)
end
end Formalism.D5


