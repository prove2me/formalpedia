-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommonEigenvectors
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CommonEigenvectors
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T16:33:49.995016+00:00
-- url     : https://prove2.me/theorems/79e3c907-7240-4e3a-93ab-50f7271e72df
-- title:
--   Common Eigenvectors
-- statement:
--   Definitions and structural lemmas for Common Eigenvectors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommonEigenvectors.lean

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P.CommonEigenvectors
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
def hop {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ V :=
  ∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) • E c c
end Formalism.FourierDecayAlt.P.CommonEigenvectors
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr CommonEigenvectors
end Formalism.FourierDecayAlt.P


