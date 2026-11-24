-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:27.73067+00:00
-- url     : https://prove2.me/theorems/1685f99f-45f1-470d-8f71-1c00762522d4
-- title:
--   Valuation Products Components
-- statement:
--   Definitions and structural lemmas for Valuation Products Components, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ValuationProductsComponents.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_genMat_inv_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_genMat_mul_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace A0
def trInv {R : Type*} [CommRing R] {n : ℕ} (m : (Matrix (Fin n) (Fin n) R)ˣ) : (Matrix (Fin n) (Fin n) R)ˣ :=
  ⟨(↑m⁻¹ : Matrix _ _ R).transpose, (↑m : Matrix _ _ R).transpose,
    by rw [← Matrix.transpose_mul]; simp, by rw [← Matrix.transpose_mul]; simp⟩
end A0
namespace A0
end A0
namespace A0
end A0
namespace A0
section Weights
variable {ι ζ : Type*} {n : ℕ} {L : Type*} [CommRing L] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
def WGe (last : Bool) (s : ℤ) (H : MvPolynomial (LVar ι ζ n) L) (a : ℤ) : Prop :=
  ∀ e ∈ H.support, a ≤ s * wExp isVec S last e
variable {isVec S} {last : Bool} {s : ℤ}
end Weights
def sgn (last : Bool) : ℤ := if last then 1 else -1
def bc (c x : ℤ) : ℤ := if 1 ≤ c then (if c ≤ x then (1 : ℤ) else 0) else (if x < c then -1 else 0)
section Gen
variable (k : Type) [Field k] {n : ℕ} (isVec : ℕ → Bool) (S : Set ℕ) [DecidablePred (· ∈ S)]
def gH : MvPolynomial (ℕ × Fin n) k →+* MvPolynomial (LVar ℕ Empty n) (GenField k n) :=
  ((sharpHom isVec S (genMat k n)⁻¹ (genMat k n)).toRingHom.comp (MvPolynomial.map (genφ k n))).comp
    (rename Sum.inl : MvPolynomial (ℕ × Fin n) k →ₐ[k] MvPolynomial (LVar ℕ Empty n) k).toRingHom
def gam (n : ℕ) (τ : Type) : (Matrix (Fin n) (Fin n) (MvPolynomial τ (GenField k n)))ˣ :=
  ⟨(genMat k n)⁻¹.map C, (genMat k n).map C,
    by rw [← Matrix.map_mul, genMat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)],
    by rw [← Matrix.map_mul, genMat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]⟩
variable {k isVec S}
end Gen
end A0
namespace A0
section Jacobi
variable {R : Type} [CommRing R] {n : ℕ}
def eps (I : Finset (Fin n)) : ℤ := ∏ a ∈ I, (-1) ^ (a.val + n + 1)
def dualF (K : Form R n) : Form R n := fun J => ((eps Jᶜ : ℤ) : R) * K Jᶜ
end Jacobi
end A0
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


