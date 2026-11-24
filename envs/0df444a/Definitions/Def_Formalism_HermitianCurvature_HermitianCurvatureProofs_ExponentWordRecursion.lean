-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:30:44.2933+00:00
-- url     : https://prove2.me/theorems/a95e4a69-3436-4212-a6bb-a48b0ad72a42
-- title:
--   Exponent Word Recursion
-- statement:
--   Definitions and structural lemmas for Exponent Word Recursion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExponentWordRecursion.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.ListSumInequalities
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
def expW : List (Bool × Mat k r) → List (ℝ × List (Bool × Mat k r))
  | [] => [(1, [])]
  | x :: w => (expW w).flatMap fun p =>
      (Finset.univ.toList : List (J k r)).map fun i => (kc i x.2 * p.1, (x.1, Lt i) :: p.2)
def bw : List Bool → List (List (Bool × Mat k r))
  | [] => [[]]
  | b :: τ => (bw τ).flatMap fun w => (Finset.univ.toList : List (J k r)).map fun i => (b, Lt i) :: w
def Kc (k r : ℕ) : ℝ := 1 + ∑ i : J k r, ‖prj (Eb i)‖
end Formalism.FourierDecayAlt.P.ListSumInequalities
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


