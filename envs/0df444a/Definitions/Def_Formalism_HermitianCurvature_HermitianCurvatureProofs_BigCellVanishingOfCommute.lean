-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingOfCommute
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingOfCommute
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T15:13:00.486843+00:00
-- url     : https://prove2.me/theorems/ffb66830-8237-445b-9041-30874e23adeb
-- title:
--   Big Cell Vanishing Of Commute
-- statement:
--   Definitions and structural lemmas for Big Cell Vanishing Of Commute, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellVanishingOfCommute.lean

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Mathlib.Topology.Algebra.MvPolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
section ops
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def idTerm (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : B.DTerm k r Wp Wq where
  coef := fun _ => ContinuousLinearMap.id ℂ _
  coefAdj := fun _ => ContinuousLinearMap.id ℂ _
  word := []
  word_lie := by simp
  adj_id := by intros; rfl
end ops
end Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
namespace Formalism.FourierDecayAlt.P
open DifferentialOperatorClasses
end Formalism.FourierDecayAlt.P


