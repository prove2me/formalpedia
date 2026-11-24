-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T15:12:01.040027+00:00
-- url     : https://prove2.me/theorems/dad1f4db-dda5-46a2-8ec0-98fda66e5996
-- title:
--   Bessel Domain Measurable
-- statement:
--   Definitions and structural lemmas for Bessel Domain Measurable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselDomainMeasurable.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JDomBoundOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.JFxDs3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
section meas
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
def adM (p : SS k r) (x : Bool × Mat k r) : Bool × Mat k r := (x.1, cond x.1 (AdL p x.2) (AdR p x.2))
end meas
end Formalism.FourierDecayAlt.P.JFxDs3


