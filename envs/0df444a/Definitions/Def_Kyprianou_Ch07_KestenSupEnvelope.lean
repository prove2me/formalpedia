-- Prove2me | Definitions.Def_Kyprianou_Ch07_KestenSupEnvelope
-- name    : Kyprianou_Ch07_KestenSupEnvelope
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T23:31:52.248684+00:00
-- url     : https://prove2.me/theorems/fafb163d-e28d-4648-b002-adb63856a966
-- title:
--   Kesten supremum of each n-fold convolution upper-tail ratio
-- statement:
--   Kesten’s envelope ξ_n is the real supremum, over every positive threshold x, of the n-fold convolution upper-tail divided by the original upper tail. Under the source asymptotics each fixed n has a finite upper bound, already proved independently. The definition uses exact original Chapter 7 sum-convolution powers.
-- source:
--   Kyprianou (2006), Chapter 7, proof of Lemma 7.14, printed p.201, original PDF p.210, definition of ξ_n as supremum of convolution-tail ratios.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- For each n, the supremum over all positive thresholds of the n-fold
upper-tail ratio used in Kyprianou's Kesten induction. -/
noncomputable def kestenSupEnvelope (G : Measure Real) (n : Nat) : Real :=
  sSup {y : Real | ∃ x : Real, 0 < x ∧
    y = ((convolutionPower G n) (Set.Ioi x)).toReal /
      (G (Set.Ioi x)).toReal}

end Kyprianou.Ch07


