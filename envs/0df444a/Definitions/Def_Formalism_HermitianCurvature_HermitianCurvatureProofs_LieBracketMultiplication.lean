-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieBracketMultiplication
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LieBracketMultiplication
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:27:27.837496+00:00
-- url     : https://prove2.me/theorems/db88c2a2-c3ac-5cb7-ba98-68b6d210293a
-- title:
--   Lie Bracket Multiplication
-- statement:
--   Definitions and structural lemmas for Lie Bracket Multiplication, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieBracketMultiplication.lean

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_Comm_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_Ent_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at

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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace LieBracketMultiplication
section Geometry
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
theorem lie_zero : InLieW k r z (0 : Mx k r) := by
  unfold InLieW inLieLev
  refine ⟨?_, by simp⟩
  simp
theorem lie_add {X Y : Mx k r} (hX : InLieW k r z X) (hY : InLieW k r z Y) : InLieW k r z (X + Y) := by
  unfold InLieW inLieLev at *
  obtain ⟨⟨h1, h1'⟩, h2⟩ := hX
  obtain ⟨⟨h3, h3'⟩, h4⟩ := hY
  refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [Matrix.conjTranspose_add, add_mul, mul_add]
    calc Xᴴ * Hpk k r + Yᴴ * Hpk k r + (Hpk k r * X + Hpk k r * Y)
        = (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
      _ = 0 := by rw [h1, h3, add_zero]
  · rw [Matrix.add_mulVec, (h1' a ha).1, (h3' a ha).1, add_zero]
  · rw [Matrix.add_mulVec, (h1' a ha).2, (h3' a ha).2, add_zero]
  · rw [Matrix.add_mulVec, h2, h4, add_zero]
theorem lie_smul {X : Mx k r} (hX : InLieW k r z X) (s : ℝ) : InLieW k r z ((s : ℂ) • X) := by
  unfold InLieW inLieLev at *
  obtain ⟨⟨h1, h1'⟩, h2⟩ := hX
  have hs : star (s : ℂ) = (s : ℂ) := Complex.conj_ofReal s
  refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  · first
    | rw [Matrix.smul_mulVec, (h1' a ha).1, smul_zero]
    | simp [(h1' a ha).1]
  · first
    | rw [Matrix.smul_mulVec, (h1' a ha).2, smul_zero]
    | simp [(h1' a ha).2]
  · first
    | rw [Matrix.smul_mulVec, h2, smul_zero]
    | simp [h2]
end Geometry
section Rep
variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}
end Rep
end LieBracketMultiplication
namespace LieBracketMultiplication
section Add
variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}
end Add
end LieBracketMultiplication
namespace LieBracketMultiplication
section Bracket
variable {k r : ℕ}
theorem real_smul (s : ℝ) (X : Mx k r) : s • X = (s : ℂ) • X := by
  first
  | exact (Complex.coe_smul s X).symm
  | simp [Complex.coe_smul]
def lieSub (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Submodule ℝ (Mx k r) where
  carrier := {X | InLieW k r z X}
  add_mem' := fun hX hY => lie_add hX hY
  zero_mem' := lie_zero
  smul_mem' := fun s X hX => by
    show InLieW k r z (s • X)
    rw [real_smul]
    exact lie_smul hX s
def mulB (k r : ℕ) : Mx k r →L[ℝ] Mx k r →L[ℝ] Mx k r :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Mx k r →ₗ[ℝ] Mx k r) ≃ₗ[ℝ] (Mx k r →L[ℝ] Mx k r)).toLinearMap ∘ₗ
      LinearMap.mul ℝ (Mx k r))
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
end Bracket
end LieBracketMultiplication
end Formalism.FourierDecayAlt.P


