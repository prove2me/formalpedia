-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsInducingCoeMatrix
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsInducingCoeMatrix
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:00.597568+00:00
-- url     : https://prove2.me/theorems/76fee03b-c2d0-4f99-9a10-4de8430fd60b
-- title:
--   Is Inducing Coe Matrix
-- statement:
--   Definitions and structural lemmas for Is Inducing Coe Matrix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsInducingCoeMatrix.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Qk27.Jm :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
    fun {n : ℕ} (ε : Fin n → Bool) ↦ Matrix.diagonal fun (a : Fin n) ↦ if ε a = Bool.true then (1 : ℂ) else (-1 : ℂ)
noncomputable def UpperTheory.Reformulated.B.Qk27.inUJ :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
    fun {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) ↦
      g.conjTranspose * UpperTheory.Reformulated.B.Qk27.Jm ε * g = UpperTheory.Reformulated.B.Qk27.Jm ε
theorem UpperTheory.Reformulated.B.Qk27.aux3 :
    ∀ {n : ℕ} (ε : Fin n → Bool) {g h : (Matrix (Fin n) (Fin n) ℂ)ˣ},
      g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk27.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} →
        h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk27.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} →
          g * h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk27.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} := by
  intro n ε g h hg hh
  simp only [Set.mem_setOf_eq, UpperTheory.Reformulated.B.Qk27.inUJ] at hg hh ⊢
  rw [Units.val_mul, Matrix.conjTranspose_mul]
  calc _ = (h : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
        ((g : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Qk27.Jm ε * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, hh]
theorem UpperTheory.Reformulated.B.Qk27.aux4 :
    ∀ {n : ℕ} (ε : Fin n → Bool),
      (↑(1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Qk27.Jm ε *
          (↑(1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
        UpperTheory.Reformulated.B.Qk27.Jm ε := by
  intro n ε
  rw [Units.val_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
theorem UpperTheory.Reformulated.B.Qk27.aux5 :
    ∀ {n : ℕ} (ε : Fin n → Bool) {g : (Matrix (Fin n) (Fin n) ℂ)ˣ},
      g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk27.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} →
        g⁻¹ ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk27.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} := by
  intro n ε g hg
  simp only [Set.mem_setOf_eq, UpperTheory.Reformulated.B.Qk27.inUJ] at hg ⊢
  have h1 : (g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Units.mul_inv g
  generalize ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = b at h1 ⊢
  calc _ = b.conjTranspose *
        ((g : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Qk27.Jm ε * g) * b := by rw [hg]
    _ = ((g : Matrix (Fin n) (Fin n) ℂ) * b).conjTranspose * UpperTheory.Reformulated.B.Qk27.Jm ε *
          ((g : Matrix (Fin n) (Fin n) ℂ) * b) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
noncomputable def UpperTheory.Reformulated.B.Qk27.UJ :
    {n : ℕ} → (Fin n → Bool) → Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    fun {n : ℕ} (ε : Fin n → Bool) ↦
      { carrier := {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk27.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)},
        mul_mem' := @UpperTheory.Reformulated.B.Qk27.aux3 n ε, one_mem' := UpperTheory.Reformulated.B.Qk27.aux4 ε,
        inv_mem' := @UpperTheory.Reformulated.B.Qk27.aux5 n ε : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ }
noncomputable def UpperTheory.Reformulated.B.Qk27.coeMatrixAlt :
    {n : ℕ} → (ε : Fin n → Bool) → ↥(UpperTheory.Reformulated.B.Qk27.UJ ε) → Matrix (Fin n) (Fin n) ℂ :=
    fun {n : ℕ} (ε : Fin n → Bool) (g : ↥(UpperTheory.Reformulated.B.Qk27.UJ ε)) ↦
      (↑(↑g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)


