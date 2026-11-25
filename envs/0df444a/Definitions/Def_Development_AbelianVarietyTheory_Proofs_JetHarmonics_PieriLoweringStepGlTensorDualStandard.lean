-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PieriLoweringStepGlTensorDualStandard
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_PieriLoweringStepGlTensorDualStandard
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:41:03.870702+00:00
-- url     : https://prove2.me/theorems/7722e418-834f-5409-9846-56e78ad966b8
-- title:
--   Pieri Lowering Step Gl Tensor Dual Standard
-- statement:
--   Definitions and structural lemmas for Pieri Lowering Step Gl Tensor Dual Standard, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PieriLoweringStepGlTensorDualStandard.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IrreducibleCapelliModules
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirEigenspaceIrreducibleDualStandardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReducedWignerCoefficientLoweringStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WignerExtremeNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
noncomputable section
namespace GlobalTheory.WigSh
def splitCasimirDual {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) :
    Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)) where
  toFun y := WithLp.toLp 2 (fun a => ∑ c, E a c (y c))
  map_add' x y := by
    ext a
    simp [Finset.sum_add_distrib]
  map_smul' t y := by
    ext a
    simp [Finset.smul_sum]
end GlobalTheory.WigSh


