-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
-- name    : GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:15.350999+00:00
-- url     : https://prove2.me/theorems/4b9303ee-646b-4e5d-93fe-d51599b39d37
-- title:
--   Herm Trace Self Of Herm Value
-- statement:
--   Definitions and structural lemmas for Herm Trace Self Of Herm Value, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/HermTraceSelfOfHermValue.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply


set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open Module Matrix TensorProduct
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι E)
section Trace
variable (K E) (R : Type*) [CommRing R] [Algebra K R]
def baseTrace : R ⊗[K] E →ₗ[R] R :=
  (Algebra.TensorProduct.rid K R R).toLinearMap ∘ₗ (Algebra.trace K E).baseChange R
variable {K E R}
end Trace
section Pairing
variable (K) (R : Type*) [CommRing R] [Algebra K R]
def hermPair (x y : ι → R ⊗[K] E) : R ⊗[K] E :=
  (fun i => conjBase K E R (x i)) ⬝ᵥ (baseMatrix K H R *ᵥ y)
def hermTrace (x y : ι → R ⊗[K] E) : R := baseTrace K E R (hermPair K H R x y)
variable {K H R}
omit [Fintype ι] in
theorem conjBase_vec_add (x x' : ι → R ⊗[K] E) :
    (fun i => conjBase K E R ((x + x') i)) =
      (fun i => conjBase K E R (x i)) + fun i => conjBase K E R (x' i) :=
  funext fun _ => map_add _ _ _
theorem hermPair_add_left (x x' y : ι → R ⊗[K] E) :
    hermPair K H R (x + x') y = hermPair K H R x y + hermPair K H R x' y := by
  unfold hermPair
  rw [conjBase_vec_add, add_dotProduct]
theorem hermPair_add_right (x y y' : ι → R ⊗[K] E) :
    hermPair K H R x (y + y') = hermPair K H R x y + hermPair K H R x y' := by
  unfold hermPair
  rw [mulVec_add, dotProduct_add]
theorem hermPair_smul_left (c : R ⊗[K] E) (x y : ι → R ⊗[K] E) :
    hermPair K H R (c • x) y = conjBase K E R c * hermPair K H R x y := by
  unfold hermPair
  have : (fun i => conjBase K E R ((c • x) i)) = conjBase K E R c • fun i => conjBase K E R (x i) :=
    funext fun i => by simp [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [this, smul_dotProduct, smul_eq_mul]
theorem hermPair_smul_right (c : R ⊗[K] E) (x y : ι → R ⊗[K] E) :
    hermPair K H R x (c • y) = c * hermPair K H R x y := by
  unfold hermPair
  rw [mulVec_smul, dotProduct_smul, smul_eq_mul]
theorem conjBase_algebraMap (c : R) :
    conjBase K E R (algebraMap R (R ⊗[K] E) c) = algebraMap R (R ⊗[K] E) c := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    conjBase_tmul, map_one]
theorem hermTrace_add_left (x x' y : ι → R ⊗[K] E) :
    hermTrace K H R (x + x') y = hermTrace K H R x y + hermTrace K H R x' y := by
  rw [hermTrace, hermPair_add_left, map_add]; rfl
theorem hermTrace_add_right (x y y' : ι → R ⊗[K] E) :
    hermTrace K H R x (y + y') = hermTrace K H R x y + hermTrace K H R x y' := by
  rw [hermTrace, hermPair_add_right, map_add]; rfl
theorem hermTrace_smul_left (c : R) (x y : ι → R ⊗[K] E) :
    hermTrace K H R (c • x) y = c * hermTrace K H R x y := by
  rw [hermTrace, ← algebraMap_smul (R ⊗[K] E) c x, hermPair_smul_left, conjBase_algebraMap,
    ← Algebra.smul_def, map_smul, smul_eq_mul]; rfl
theorem hermTrace_smul_right (c : R) (x y : ι → R ⊗[K] E) :
    hermTrace K H R x (c • y) = c * hermTrace K H R x y := by
  rw [hermTrace, ← algebraMap_smul (R ⊗[K] E) c y, hermPair_smul_right, ← Algebra.smul_def,
    map_smul, smul_eq_mul]; rfl
variable (K H R) in

def hermTraceBilin : (ι → R ⊗[K] E) →ₗ[R] (ι → R ⊗[K] E) →ₗ[R] R :=
  LinearMap.mk₂ R (hermTrace K H R) hermTrace_add_left hermTrace_smul_left hermTrace_add_right
    hermTrace_smul_right
section Invariance
variable [DecidableEq ι]
end Invariance
end Pairing
section Coordinates
variable [DecidableEq ι] (R : Type*) [CommRing R] [Algebra K R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
def vecCoords (x : ι → R ⊗[K] E) (a : ι × κ) : R :=
  (Algebra.TensorProduct.basis R b).repr (x a.1) a.2
def stdVec (a : ι × κ) : ι → R ⊗[K] E := Pi.single a.1 ((1 : R) ⊗ₜ b a.2)
variable {R}
end Coordinates
end GroundTheory.Automorphic


