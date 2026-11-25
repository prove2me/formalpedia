-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightTypeAction
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_RightTypeAction
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:27:04.808119+00:00
-- url     : https://prove2.me/theorems/80bd9716-87dc-43c1-94ea-1c3cdc28b813
-- title:
--   Right Type Action
-- statement:
--   Definitions and structural lemmas for Right Type Action, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightTypeAction.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneParameterDifferentiable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace QrD
section Geometry
variable {k r : ℕ}
def InLieW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (X : Mx k r) : Prop :=
  inLieLev k r (Fin.last r) X ∧ X *ᵥ z = 0
end Geometry
section Rep
variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
def dOp (π : Mx k r → (W →L[ℂ] W)) (X : Mx k r) : W →L[ℂ] W :=
  deriv (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) 0
def ecOp (π : Mx k r → (W →L[ℂ] W)) (Z : Mx k r) : W →L[ℂ] W :=
  dOp π (hpart1 (Hpk k r) Z) + Complex.I • dOp π (hpart2 (Hpk k r) Z)
variable [FiniteDimensional ℂ W] {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}
end Rep
section Right
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}
end Right
end QrD
end Formalism.FourierDecayAlt.P


