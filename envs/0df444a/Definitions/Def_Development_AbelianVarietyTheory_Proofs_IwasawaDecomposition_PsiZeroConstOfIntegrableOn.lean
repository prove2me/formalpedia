-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PsiZeroConstOfIntegrableOn
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PsiZeroConstOfIntegrableOn
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T22:43:32.452187+00:00
-- url     : https://prove2.me/theorems/052c6adc-69d6-4fa1-b178-129dd902b3c6
-- title:
--   Psi Zero Const Of Integrable On
-- statement:
--   Definitions and structural lemmas for Psi Zero Const Of Integrable On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PsiZeroConstOfIntegrableOn.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction Filter Topology MeasureTheory Asymptotics
open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2
noncomputable section
namespace GlobalTheory.Mem.An.PsiZero
def err (u : ℝ) : ℝ := (psumR (fun n => Λ n) u - u) / u ^ 2
end GlobalTheory.Mem.An.PsiZero


