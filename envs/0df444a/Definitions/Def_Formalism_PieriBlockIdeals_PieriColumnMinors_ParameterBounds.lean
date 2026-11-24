-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
-- name    : Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:37:21.79579+00:00
-- url     : https://prove2.me/theorems/c7c2e7ad-b6f5-4868-a1b5-87cf97cdd6a4
-- title:
--   Parameter Bounds
-- statement:
--   Definitions and structural lemmas for Parameter Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
def lstarDenom (P : Par) : ℝ :=
  (P.n : ℝ) * (P.t : ℝ) ^ 2 * (P.N + (P.t : ℝ)) * P.L ^ 2
      + (P.k : ℝ) * (P.n : ℝ) ^ 2 * (P.S + (P.t : ℝ) + P.L)
structure NatBounds (P : Par) : Prop where
  m1 : (1 : ℝ) ≤ P.m
  n1 : (1 : ℝ) ≤ P.n
  f1 : (1 : ℝ) ≤ P.f
  k1 : (1 : ℝ) ≤ P.k
  mlek : (P.m : ℝ) ≤ P.k
  kt : (P.k : ℝ) + P.m + 4 ≤ P.t
  mt : 3 * (P.m : ℝ) < P.t
  t6 : (6 : ℝ) ≤ P.t
  nr : (P.Nr : ℝ) + 1 = P.k + P.m + P.t
  nr2 : (P.Nr : ℝ) ≤ 2 * P.t - 5
def indexDenominator (P : Par) : ℝ := (P.k : ℝ) * ((P.m : ℝ) + (P.t : ℝ)) * Real.log (3 * P.h)
def gatedCoefficientTerm {ι : Type} (D : SizeData₂ ι) (P : Par) (τ : ι) (l : ℕ) : ℝ :=
  if ((d0 l (D.xlo τ - D.maxB τ) : ℕ) : ℤ) < D.xlo τ - D.maxB τ then
    min (min (P.k : ℝ) (P.t : ℝ)) ((D.q τ : ℝ) * P.h / (d0 l (D.xlo τ - D.maxB τ) : ℝ)) else 0
end Formalism.CohomologicalDescent.LogSmallConstantBounds


