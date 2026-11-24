-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InnerDensityOfAveraging
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_InnerDensityOfAveraging
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T15:14:43.047985+00:00
-- url     : https://prove2.me/theorems/f9425e8b-4646-4020-94d7-ac52a4505f82
-- title:
--   Inner Density Of Averaging
-- statement:
--   Definitions and structural lemmas for Inner Density Of Averaging, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InnerDensityOfAveraging.lean

import Definitions.Def_Formalism_HermitianCurvature_LemmaDensOfSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
def averagingDatumInhabited {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) : Formalism.FourierDecayAlt.DensityAveraging.AvgDatum D F' γ where
  V := ℂ
  p := normSeminorm ℂ ℂ
  β := 1
  β_ne := one_ne_zero
  s := 1
  w := fun _ => 0
  w_inj := fun i j _ => Subsingleton.elim i j
  a := fun _ => 1
  k₀ := 0
  tie := fun h => absurd h (by simp)
end Formalism.FourierDecayAlt.P


