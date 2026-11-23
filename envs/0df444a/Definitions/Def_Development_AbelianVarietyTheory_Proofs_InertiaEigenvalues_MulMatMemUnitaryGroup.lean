-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:07.268102+00:00
-- url     : https://prove2.me/theorems/67e0632f-3637-4758-bb7b-1656729d7825
-- title:
--   Mul Mat Mem Unitary Group
-- statement:
--   Definitions and structural lemmas for Mul Mat Mem Unitary Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MulMatMemUnitaryGroup.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR.Et
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E)
def mulMat {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y : A.L) : Matrix (Fin r) (Fin r) E :=
  LinearMap.toMatrix' ((j : A.L →ₗ[E] (Fin r → E)) ∘ₗ LinearMap.mulLeft E y ∘ₗ (j.symm : (Fin r → E) →ₗ[E] A.L))
theorem mulMat_mulVec {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y : A.L) (v : Fin r → E) :
    A.mulMat j y *ᵥ v = j (y * j.symm v) := by
  simp [mulMat, LinearMap.toMatrix'_mulVec]
theorem mulMat_mulVec_apply {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y z : A.L) :
    A.mulMat j y *ᵥ j z = j (y * z) := by
  simp [mulMat_mulVec]
theorem mulMat_mul {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y y' : A.L) :
    A.mulMat j (y * y') = A.mulMat j y * A.mulMat j y' := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, mulMat_mulVec, LinearEquiv.symm_apply_apply, mul_assoc]
theorem mulMat_one {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) : A.mulMat j 1 = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simp [mulMat_mulVec]
theorem mulMat_mem_unitaryGroup {r : ℕ} {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j)
    (t : unitary A.L) : A.mulMat j t ∈ Matrix.unitaryGroup (Fin r) E := by
  rw [Matrix.mem_unitaryGroup_iff']
  set N := star (A.mulMat j t) * A.mulMat j t
  have key : ∀ v w : Fin r → E, star v ⬝ᵥ (N *ᵥ w) = star v ⬝ᵥ w := by
    intro v w
    obtain ⟨a, rfl⟩ := j.surjective v
    obtain ⟨b, rfl⟩ := j.surjective w
    have h1 : star (j a) ⬝ᵥ (N *ᵥ j b) = star (A.mulMat j t *ᵥ j a) ⬝ᵥ (A.mulMat j t *ᵥ j b) := by
      simp only [N, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.star_eq_conjTranspose]
    rw [h1, mulMat_mulVec_apply, mulMat_mulVec_apply, hx, hx]
    congr 1
    have ht : star (t : A.L) * t = 1 := Unitary.star_mul_self_of_mem t.2
    calc algebraMap A.K A.L x * star ((t : A.L) * a) * ((t : A.L) * b)
        = algebraMap A.K A.L x * star a * b * (star (t : A.L) * t) := by rw [star_mul]; ring
      _ = _ := by rw [ht, mul_one]
  have hw : ∀ w, N *ᵥ w = w := by
    intro w
    funext i
    have := key (Pi.single i 1) w
    simpa [single_dotProduct] using this
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  simp [hw]
def uHom {r : ℕ} {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j) :
    unitary A.L →* Matrix.unitaryGroup (Fin r) E where
  toFun t := ⟨A.mulMat j t, A.mulMat_mem_unitaryGroup hx t⟩
  map_one' := by ext1; simp [mulMat_one]
  map_mul' t t' := by ext1; simp [mulMat_mul]
def descFn {r : ℕ} (M : GlobalTheory.JR.Meas r F E) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (j : A.L ≃ₗ[E] (Fin r → E))
    (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ) (f : Hn r F E → ℂ) (y : A.L) : ℂ :=
  letI := M.mU
  ∫ g, f (actU g (Ax, j y, lam)) * (α g : ℂ) ∂M.μU
end GlobalTheory.JR.Et


