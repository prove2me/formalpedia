-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:26:37.878211+00:00
-- url     : https://prove2.me/theorems/f9238d8e-80bd-4c50-94ed-1cce6287eb04
-- title:
--   Hurwitz B
-- statement:
--   Definitions and structural lemmas for Hurwitz B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/HurwitzB.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.L2.Th1.G
open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral)
namespace HurwitzJetIntegrality
end HurwitzJetIntegrality
open HurwitzJetIntegrality
namespace HurwitzJetIntegrality
def blockEmb (B ι : Type) (k : B) : ι ↪ B × ι := ⟨fun i => (k, i), fun _ _ h => (Prod.mk.inj h).2⟩
def rep (B : Type) [Fintype B] {ι : Type} (m : B → ι →₀ ℕ) : B × ι →₀ ℕ :=
  ∑ k : B, Finsupp.embDomain (blockEmb B ι k) (m k)
end HurwitzJetIntegrality
end Formalism.L2.Th1.G


