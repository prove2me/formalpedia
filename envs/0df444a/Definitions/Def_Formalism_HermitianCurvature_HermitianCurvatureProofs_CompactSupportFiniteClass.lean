-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactSupportFiniteClass
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactSupportFiniteClass
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T17:59:48.361342+00:00
-- url     : https://prove2.me/theorems/21c3ef79-c105-4bf7-82a5-ff62f4647e21
-- title:
--   Compact Support Finite Class
-- statement:
--   Definitions and structural lemmas for Compact Support Finite Class, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactSupportFiniteClass.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaConjOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.JFxG
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def mulRb (k r : ℕ) : Mat k r →L[ℝ] Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)
      map_add' := fun X Y => by ext g : 1; simp [Matrix.mul_add]
      map_smul' := fun c X => by ext g : 1; simp }
def mulLb (k r : ℕ) : Mat k r →L[ℝ] Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)
      map_add' := fun X Y => by ext g : 1; simp [Matrix.add_mul]
      map_smul' := fun c X => by ext g : 1; simp }
def Phi (F' : Mat k r → E) : (j : ℕ) → (Fin j → Bool) → (Fin j → Mat k r) × Mat k r → E
  | 0, _, q => F' q.2
  | j + 1, bs, q => fderiv ℝ (fun g => Phi F' j (fun i => bs i.succ) ((fun i => q.1 i.succ), g)) q.2
      (vf (bs 0) (q.1 0) q.2)
end Formalism.FourierDecayAlt.P.JFxG
namespace Formalism.FourierDecayAlt.P.JFxG
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def Box (k r : ℕ) : Set (Mat k r) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 1
end Formalism.FourierDecayAlt.P.JFxG
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.JFxG
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P


