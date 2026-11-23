-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_VecMulVecComm
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_VecMulVecComm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:00.390803+00:00
-- url     : https://prove2.me/theorems/01e66132-306c-4825-b3cb-8eb805a811f4
-- title:
--   Vec Mul Vec Comm
-- statement:
--   Definitions and structural lemmas for Vec Mul Vec Comm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/VecMulVecComm.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
namespace GlobalTheory.GrassModel
variable (n : ℕ)
abbrev Ext : Type := ExteriorAlgebra ℂ (Fin n → ℂ)
abbrev Big : Type := Ext n ⊗[ℂ] Ext n
def vec (a : Fin n) : Ext n := ExteriorAlgebra.ι ℂ (Pi.single a 1 : Fin n → ℂ)
def gen (x : Fin n × Fin n) : Big n := vec n x.1 ⊗ₜ vec n x.2
theorem vec_mul_vec_comm (a b : Fin n) : vec n a * vec n b = -(vec n b * vec n a) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
theorem gen_comm : ∀ u ∈ Set.range (gen n), ∀ v ∈ Set.range (gen n), u * v = v * u := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  simp only [gen, Algebra.TensorProduct.tmul_mul_tmul, vec_mul_vec_comm n x.1, vec_mul_vec_comm n x.2,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_neg]
abbrev EvenPart : Subalgebra ℂ (Big n) := Algebra.adjoin ℂ (Set.range (gen n))
open scoped IsMulCommutative in
instance : CommRing (EvenPart n) :=
  have := Algebra.isMulCommutative_adjoin ℂ (gen_comm n)
  inferInstance
def toEven : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] EvenPart n :=
  aeval fun x => ⟨gen n x, Algebra.subset_adjoin ⟨x, rfl⟩⟩
open Classical in

def topForm (i : ℕ) : (Fin n → ℂ) [⋀^Fin i]→ₗ[ℂ] ℂ :=
  if h : i = n then (Pi.basisFun ℂ (Fin n)).det.domDomCongr (finCongr h.symm) else 0
def topExt : Ext n →ₗ[ℂ] ℂ := ExteriorAlgebra.liftAlternating (topForm n)
def topBig : Big n →ₗ[ℂ] ℂ := TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₂ (topExt n) ∘ₗ topExt n)
variable {n} {p q : ℕ}
def blockPoly (e : Fin p × Fin q → Fin n) : Matrix (Fin p) (Fin p) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => ∑ b, X (e (i, b), e (j, b))
def blockPolyBar (e : Fin p × Fin q → Fin n) : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun b b' => ∑ i, X (e (i, b), e (i, b'))
end GlobalTheory.GrassModel


