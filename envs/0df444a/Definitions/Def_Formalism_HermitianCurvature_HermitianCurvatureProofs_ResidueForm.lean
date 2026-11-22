-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:40:29.16102+00:00
-- url     : https://prove2.me/theorems/a9090c01-e28d-4d11-b46f-6eff671aae0a
-- title:
--   Residue Form
-- statement:
--   Definitions and structural lemmas for Residue Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.Fr11
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
noncomputable section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
def dg (g : Ix S → ℂ) : SlopeTestRemainingChoices S A := Matrix.diagonal fun e => algebraMap ℂ A (g e)
def Ph {B : Type} [Ring B] [Algebra ℂ B] (p0 p1 : B) (c : ℂ) (U V : B) : B :=
  p0 * (U - c • (U - V)) + p1 * (U + c • (U - V))
section PhLemmas
variable {B : Type} [Ring B] [Algebra ℂ B] (p0 p1 : B) (c : ℂ)
end PhLemmas
section Points
variable {r : ℕ} (L : LevelData A r) (st : Start A)
end Points
end
end Formalism.FourierDecayAlt.P.Fr11
namespace Formalism.FourierDecayAlt.P
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.Fr11
end Formalism.FourierDecayAlt.P


