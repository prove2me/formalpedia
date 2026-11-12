-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterConjugate
-- name    : OddOrder_GroupTheory_RepresentationTheory_CharacterConjugate
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:16.093669+00:00
-- url     : https://prove2.me/theorems/2c627ede-8b04-4c0f-8197-a313f93980fa
-- title:
--   Conjugate of a character: $\chi(g^{-1})=\overline{\chi(g)}$
-- statement:
--   For a finite-dimensional complex representation $\rho$ of a finite group $G$, the character at $g^{-1}$ is the complex conjugate of its value at $g$. The proof avoids eigenvalues: it uses the group-averaged Gram matrix $S=\sum_h M_h^{H}M_h$, which is positive definite, to show $M_g^{-1}=S^{-1}M_g^{H}S$ and then uses cyclicity of the trace.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CharacterConjugate.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CharacterConjugate.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace OddOrder.RepresentationTheory

open Matrix

open scoped ComplexOrder

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- For a finite-dimensional complex representation of a finite group,
`χ(g⁻¹) = conj (χ(g))`. -/
theorem character_inv (ρ : Representation ℂ G V) (g : G) :
    ρ.character g⁻¹ = star (ρ.character g) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  let b := Module.Free.chooseBasis ℂ V
  let Mat : G → Matrix (Module.Free.ChooseBasisIndex ℂ V) (Module.Free.ChooseBasisIndex ℂ V) ℂ :=
    fun h => LinearMap.toMatrix b b (ρ h)
  have hmul : ∀ h₁ h₂ : G, Mat (h₁ * h₂) = Mat h₁ * Mat h₂ := by
    intro h₁ h₂
    change LinearMap.toMatrix b b (ρ (h₁ * h₂)) = _
    rw [map_mul, LinearMap.toMatrix_mul]
  have hone : Mat 1 = 1 := by
    change LinearMap.toMatrix b b (ρ 1) = 1
    rw [map_one, LinearMap.toMatrix_one]
  have hchar : ∀ h : G, ρ.character h = (Mat h).trace := by
    intro h
    change LinearMap.trace ℂ V (ρ h) = _
    rw [LinearMap.trace_eq_matrix_trace ℂ b]
  -- every `Mat h` is invertible
  have hMatUnit : ∀ h : G, IsUnit (Mat h) := fun h =>
    IsUnit.of_mul_eq_one (b := Mat h⁻¹) (by rw [← hmul h h⁻¹, mul_inv_cancel, hone])
  set M := Mat g with hMdef
  -- `Mat g⁻¹` is the two-sided inverse of `M`.
  have hLinv : Mat g⁻¹ * M = 1 := by rw [hMdef, ← hmul g⁻¹ g, inv_mul_cancel, hone]
  have hRinv : M * Mat g⁻¹ = 1 := by rw [hMdef, ← hmul g g⁻¹, mul_inv_cancel, hone]
  have hMdet : IsUnit M.det :=
    IsUnit.of_mul_eq_one (b := (Mat g⁻¹).det)
      (by rw [← Matrix.det_mul, hRinv, Matrix.det_one])
  have hMinv : M⁻¹ = Mat g⁻¹ := Matrix.inv_eq_left_inv hLinv
  -- the group-averaged Gram matrix is positive definite, hence invertible
  set S : Matrix (Module.Free.ChooseBasisIndex ℂ V) (Module.Free.ChooseBasisIndex ℂ V) ℂ :=
    ∑ h : G, (Mat h)ᴴ * Mat h with hSdef
  have hSpd : S.PosDef := by
    rw [hSdef]
    refine Matrix.posDef_sum Finset.univ_nonempty (fun h _ => ?_)
    exact Matrix.PosDef.conjTranspose_mul_self (Mat h)
      (Matrix.mulVec_injective_of_isUnit (hMatUnit h))
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSpd.isUnit
  -- invariance `Mᴴ S M = S` from reindexing the sum by `h ↦ h · g`
  have hterm : ∀ h : G, Mᴴ * ((Mat h)ᴴ * Mat h) * M = (Mat (h * g))ᴴ * Mat (h * g) := by
    intro h
    rw [hmul h g, Matrix.conjTranspose_mul, hMdef]
    simp only [Matrix.mul_assoc]
  have hSinv : Mᴴ * S * M = S := by
    rw [hSdef, Finset.mul_sum, Finset.sum_mul, Finset.sum_congr rfl (fun h _ => hterm h)]
    exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun x => by rw [Equiv.coe_mulRight])
  -- `M⁻¹ = S⁻¹ Mᴴ S`.
  have hMinv2 : M⁻¹ = S⁻¹ * Mᴴ * S := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc (S⁻¹ * Mᴴ) S M, Matrix.mul_assoc S⁻¹ Mᴴ (S * M),
      ← Matrix.mul_assoc Mᴴ S M, hSinv, Matrix.nonsing_inv_mul S hSdet]
  -- conclude
  rw [hchar g⁻¹, hchar g, ← hMinv, hMinv2, Matrix.trace_mul_cycle,
    Matrix.mul_nonsing_inv S hSdet, Matrix.one_mul, Matrix.trace_conjTranspose]

end OddOrder.RepresentationTheory


