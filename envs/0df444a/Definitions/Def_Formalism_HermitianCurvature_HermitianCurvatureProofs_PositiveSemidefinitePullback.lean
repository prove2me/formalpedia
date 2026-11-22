-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveSemidefinitePullback
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveSemidefinitePullback
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:21:15.480955+00:00
-- url     : https://prove2.me/theorems/b12fe94f-2531-46b8-b6e8-f3da4b35f042
-- title:
--   Positive Semidefinite Pullback
-- statement:
--   Definitions and structural lemmas for Positive Semidefinite Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveSemidefinitePullback.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
noncomputable section
open Classical
def ind {α : Type} (Y A : Finset α) : Y → ℂ := fun p => if (p : α) ∈ A then 1 else 0
variable {E W : Type} [Field E]
end
end Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
namespace Formalism.FourierDecayAlt.P
open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
end Formalism.FourierDecayAlt.P


