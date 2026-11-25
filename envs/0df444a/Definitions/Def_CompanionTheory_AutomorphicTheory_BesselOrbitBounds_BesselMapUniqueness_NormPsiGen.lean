-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_NormPsiGen
-- name    : CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_NormPsiGen
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:16:53.278779+00:00
-- url     : https://prove2.me/theorems/598dd2fd-8afe-488e-a14f-1741b694ee6d
-- title:
--   Norm Psi Gen
-- statement:
--   Definitions and structural lemmas for Norm Psi Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselOrbitBounds/BesselMapUniqueness/NormPsiGen.lean

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Theorems.Thm_CCRuleCW_lie_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
namespace CompanionTheory.Bmu
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
theorem lie_add {n : ℕ} {Hm X Y : Mat n} (hX : Lie Hm X) (hY : Lie Hm Y) : Lie Hm (X + Y) := by
  unfold Lie at *
  rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
  calc Xᴴ * Hm + Yᴴ * Hm + (Hm * X + Hm * Y) = (Xᴴ * Hm + Hm * X) + (Yᴴ * Hm + Hm * Y) := by abel
    _ = 0 := by rw [hX, hY, add_zero]
theorem lie_smul {n : ℕ} {Hm X : Mat n} (c : ℝ) (hX : Lie Hm X) : Lie Hm (c • X) := by
  unfold Lie at *
  rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]
theorem lie_zero {n : ℕ} (Hm : Mat n) : Lie Hm 0 := by simp [Lie]
variable {k r : ℕ}
def sUw (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Submodule ℝ (Mat (2 * r + k + 1)) where
  carrier := {X | InUw k r z X}
  zero_mem' := ⟨lie_zero _, fun _ => ⟨zero_mulVec _, zero_mulVec _⟩, zero_mulVec _⟩
  add_mem' := fun {X Y} hX hY => ⟨lie_add hX.1 hY.1, fun a =>
    ⟨by rw [add_mulVec, (hX.2.1 a).1, (hY.2.1 a).1, add_zero], by rw [add_mulVec, (hX.2.1 a).2, (hY.2.1 a).2, add_zero]⟩,
    by rw [add_mulVec, hX.2.2, hY.2.2, add_zero]⟩
  smul_mem' := fun c X hX => ⟨lie_smul c hX.1, fun a =>
    ⟨by rw [smul_mulVec, (hX.2.1 a).1, smul_zero], by rw [smul_mulVec, (hX.2.1 a).2, smul_zero]⟩,
    by rw [smul_mulVec, hX.2.2, smul_zero]⟩
def sN (k r : ℕ) : Submodule ℝ (Mat (2 * r + k + 1)) where
  carrier := {X | InN k r X}
  zero_mem' := ⟨lie_zero _, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  add_mem' := fun {X Y} hX hY => ⟨lie_add hX.1 hY.1, fun a i h => by
    rw [Matrix.add_apply, hX.2.1 a i h, hY.2.1 a i h, add_zero], fun i j h1 h2 h3 => by
    rw [Matrix.add_apply, hX.2.2 i j h1 h2 h3, hY.2.2 i j h1 h2 h3, add_zero]⟩
  smul_mem' := fun c X hX => ⟨lie_smul c hX.1, fun a i h => by
    rw [Matrix.smul_apply, hX.2.1 a i h, smul_zero], fun i j h1 h2 h3 => by
    rw [Matrix.smul_apply, hX.2.2 i j h1 h2 h3, smul_zero]⟩
def sQ (k r : ℕ) (Γ : Mat (2 * r + k + 1)) : Submodule ℝ (Mat (2 * r + k + 1)) where
  carrier := {X | InQ k r Γ X}
  zero_mem' := ⟨lie_zero _, fun _ _ _ => by simp⟩
  add_mem' := fun {X Y} hX hY => ⟨lie_add hX.1 hY.1, fun i j h => by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, hX.2 i j h, hY.2 i j h, add_zero]⟩
  smul_mem' := fun c X hX => ⟨lie_smul c hX.1, fun i j h => by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, hX.2 i j h, smul_zero]⟩
end CompanionTheory.Bmu


