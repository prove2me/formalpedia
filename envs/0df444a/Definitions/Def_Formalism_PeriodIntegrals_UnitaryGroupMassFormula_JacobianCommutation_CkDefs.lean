-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_CkDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_CkDefs
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T09:58:26.863053+00:00
-- url     : https://prove2.me/theorems/535816e1-b487-5d46-88ef-ddeb4e330b11
-- title:
--   Ck Defs
-- statement:
--   Definitions and structural lemmas for Ck Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianCommutation/CkDefs.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_CutDefs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace PI.UnitaryGroupMassFormula.JCC.Ck
def PartialsContinuousDifferentiable : Prop :=
  ∀ (d : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Set (Fin d → ℝ))
    (F : (Fin d → ℝ) → E) (D : Fin d → (Fin d → ℝ) → E),
    IsOpen V → (∀ i, ContinuousOn (D i) V) →
    (∀ y ∈ V, ∀ i, HasDerivAt (fun t : ℝ => F (y + t • Pi.single i (1 : ℝ))) (D i y) 0) →
    ∀ y ∈ V, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (D i y)) y
def ChartEx : Prop :=
  ∀ (k r : ℕ) (O : Set (B.Mat k r)), IsOpen O → ∀ g₀ ∈ O ∩ B.GV k r,
    ∃ (d : ℕ) (Eb : Fin d → B.Mat k r) (c : Fin d → (B.Mat k r →L[ℝ] ℝ))
      (φ : (Fin d → ℝ) → B.Mat k r) (X : Fin d → (Fin d → ℝ) → B.Mat k r)
      (V : Set (Fin d → ℝ)) (U : Set (B.Mat k r)) (π : B.Mat k r → (Fin d → ℝ)),
      (∀ a, B.inLie k r (Eb a)) ∧ (∀ Y, B.inLie k r Y → Y = ∑ a, (c a Y : ℝ) • Eb a) ∧
      IsOpen V ∧ IsOpen U ∧ g₀ ∈ U ∧ ContinuousOn φ V ∧
      (∀ y ∈ V, φ y ∈ O ∩ B.GV k r ∧ φ y ∈ U ∧ π (φ y) = y) ∧
      (∀ (n : ℕ) (i : Fin d), ContDiffOn ℝ n (X i) V) ∧ (∀ i, ∀ y ∈ V, B.inLie k r (X i y)) ∧
      (∀ i, ∀ y ∈ V, ∀ t : ℝ, φ (y + t • Pi.single i (1 : ℝ)) = φ y * NormedSpace.exp ((t : ℂ) • X i y)) ∧
      (∀ n : ℕ, ContDiffOn ℝ n π U) ∧ Set.MapsTo π U V ∧ (∀ g ∈ U, g ∈ B.GV k r → φ (π g) = g)
end PI.UnitaryGroupMassFormula.JCC.Ck


