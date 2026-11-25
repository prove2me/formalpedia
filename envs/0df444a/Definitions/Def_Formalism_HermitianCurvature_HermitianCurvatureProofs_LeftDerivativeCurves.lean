-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:09:47.619293+00:00
-- url     : https://prove2.me/theorems/ba6203a6-cb4c-4c3f-a0b0-1ec25e60baf8
-- title:
--   Left Derivative Curves
-- statement:
--   Definitions and structural lemmas for Left Derivative Curves, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftDerivativeCurves.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
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
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace LeftDerivativeCurves
open Qx2 (Good)
section Analysis
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
def mulL {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)
end Analysis
section Comm
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
def Comm (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (T S : (Mx k r → E) → Mx k r → E) : Prop :=
  ∀ f, SmoothLev k r i D f → ∀ x ∈ Glev k r i ∩ D, T (S f) x = S (T f) x
def rop (k r : ℕ) (c : ℂ) (Z : Mx k r) (f : Mx k r → E) : Mx k r → E := fun x => RZ (Hpk k r) Z f x + c • f x
def lop (k r : ℕ) (c : ℂ) (Z : Mx k r) (f : Mx k r → E) : Mx k r → E := fun x => LZ (Hpk k r) Z f x + c • f x
end Comm
section Conj
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)}
end Conj
end LeftDerivativeCurves
end Formalism.FourierDecayAlt.P


