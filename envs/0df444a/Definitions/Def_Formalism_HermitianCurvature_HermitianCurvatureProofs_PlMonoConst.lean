-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlMonoConst
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_PlMonoConst
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T20:36:32.685254+00:00
-- url     : https://prove2.me/theorems/fdb29588-81c3-42f4-b03d-497bb9e7452d
-- title:
--   Pl Mono Const
-- statement:
--   Definitions and structural lemmas for Pl Mono Const, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlMonoConst.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightDerivativeRulePsi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
section poly
variable {A : Type} [Ring A] [Algebra ℂ A]
def PolyLe (t : ℕ) (f : ℂ → A) : Prop :=
  ∃ C : Fin t → A, ∀ u, f u = ∑ l : Fin t, algebraMap ℂ A (u ^ (l : ℕ)) * C l
end poly
end Formalism.FourierDecayAlt.P.SignAntidiagonal


