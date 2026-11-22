-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SlopeBoundSaturation
-- name    : Formalism_GaussJetBounds_GaussJetProofs_SlopeBoundSaturation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:34.375713+00:00
-- url     : https://prove2.me/theorems/9bf9eae9-cc44-459b-ba45-246dd65ece28
-- title:
--   Slope Bound Saturation
-- statement:
--   Definitions and structural lemmas for Slope Bound Saturation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
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
open MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
open Formalism.GradedWeylDivisibility
def satMinor (R : Type) [CommRing R] (r n : ℕ) (x : (j : ℕ) × (Fin j → Fin r)) :
    MvPolynomial (Fin r × Fin n) R :=
  if h : x.1 ≤ n then initMinor R x.2 h else 1
def satEmb (d N0 : ℕ) (s : ZMod d) (v : Fin N0 × Fin N0) : ZMod d × Fin N0 × Fin N0 := (s, v.2, v.1)
end Formalism.DworkPowerSeriesWeights


