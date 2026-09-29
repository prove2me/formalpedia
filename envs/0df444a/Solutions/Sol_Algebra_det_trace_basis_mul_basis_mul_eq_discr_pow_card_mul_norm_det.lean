-- Prove2me | solution 1 for Algebra.det_trace_basis_mul_basis_mul_eq_discr_pow_card_mul_norm_det
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/871a1b94-166e-5466-be46-322aad725d37

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_det_trace_basis_mul_basis_mul_eq_discr_pow_card_mul_norm_det

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "Matrix Module Matrix.Module"

namespace DiscTower

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def traceDot (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (κ : Type*) [Fintype κ] :
    LinearMap.BilinForm R (κ → S) :=
  LinearMap.mk₂ R (fun x y : κ → S => Algebra.trace R S (∑ i, x i * y i))
    (fun x x' y => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add])
    (fun r x y => by
      simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul])
    (fun x y y' => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add])
    (fun r x y => by
      simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul])

@[scoped simp] theorem traceDot_apply (x y : κ → S) :
    traceDot R S κ x y = Algebra.trace R S (∑ i, x i * y i) := rfl

noncomputable def β (b : Basis ι R S) : Basis (ι × κ) R (κ → S) :=
  b.smulTower (Pi.basisFun S κ)

theorem β_apply (b : Basis ι R S) (p : ι × κ) : β (κ := κ) b p = Pi.single p.2 (b p.1) := by
  ext k
  rw [β, Basis.smulTower_apply, Pi.basisFun_apply, Pi.smul_apply, Pi.single_apply, Pi.single_apply]
  split_ifs <;> simp

theorem sum_single_mul_single (i j : κ) (s t : S) :
    (∑ k, (Pi.single i s : κ → S) k * (Pi.single j t : κ → S) k) = if i = j then s * t else 0 := by
  classical
  have : ∀ k, (Pi.single i s : κ → S) k * (Pi.single j t : κ → S) k =
      if k = i then (if i = j then s * t else 0) else 0 := by
    intro k
    by_cases hki : k = i
    · subst hki
      by_cases hij : k = j
      · subst hij; simp
      · simp [hij]
    · simp [hki]
  rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_ite_eq' Finset.univ i]
  simp

theorem toMatrix_traceDot (b : Basis ι R S) :
    LinearMap.BilinForm.toMatrix (β b) (traceDot R S κ) =
      Matrix.blockDiagonal fun _ : κ => Algebra.traceMatrix R b := by
  ext p q
  rw [LinearMap.BilinForm.toMatrix_apply, traceDot_apply, β_apply, β_apply, sum_single_mul_single,
    Matrix.blockDiagonal_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  by_cases h : p.2 = q.2
  · simp [h]
  · simp [h]

theorem det_toMatrix_traceDot (b : Basis ι R S) :
    (LinearMap.BilinForm.toMatrix (β b) (traceDot R S κ)).det = Algebra.discr R b ^ Fintype.card κ := by
  rw [toMatrix_traceDot, Matrix.det_blockDiagonal, Finset.prod_const, Finset.card_univ, Algebra.discr_def]

noncomputable def mulVecR (R : Type*) [CommRing R] [Algebra R S] (G : Matrix κ κ S) : (κ → S) →ₗ[R] (κ → S) :=
  (Matrix.toLin' G).restrictScalars R

theorem mulVecR_apply (G : Matrix κ κ S) (y : κ → S) : mulVecR R G y = G *ᵥ y := by
  simp [mulVecR]

theorem det_mulVecR (b : Basis ι R S) (G : Matrix κ κ S) :
    LinearMap.det (mulVecR R G) = Algebra.norm R G.det := by
  haveI : Module.Free R S := Module.Free.of_basis b
  rw [mulVecR, LinearMap.det_restrictScalars, LinearMap.det_toLin']

theorem toMatrix_compRight_apply (b : Basis ι R S) (G : Matrix κ κ S) (p q : ι × κ) :
    LinearMap.BilinForm.toMatrix (β b) ((traceDot R S κ).compRight (mulVecR R G)) p q =
      Algebra.trace R S (b p.1 * b q.1 * G p.2 q.2) := by
  rw [LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.compRight_apply, traceDot_apply, mulVecR_apply,
    β_apply, β_apply]
  congr 1
  have hG : ∀ k, (G *ᵥ (Pi.single q.2 (b q.1) : κ → S)) k = G k q.2 * b q.1 := by
    intro k
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  simp_rw [hG]
  have : ∀ k, (Pi.single p.2 (b p.1) : κ → S) k * (G k q.2 * b q.1) =
      if k = p.2 then b p.1 * b q.1 * G p.2 q.2 else 0 := by
    intro k
    by_cases hk : k = p.2
    · subst hk; simp; ring
    · simp [hk]
  rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_ite_eq' Finset.univ p.2]
  simp

theorem det_trace_mul_mul_eq (b : Basis ι R S) (G : Matrix κ κ S) :
    (Matrix.of fun p q : ι × κ => Algebra.trace R S (b p.1 * b q.1 * G p.2 q.2)).det =
      Algebra.discr R b ^ Fintype.card κ * Algebra.norm R G.det := by
  have hM : (Matrix.of fun p q : ι × κ => Algebra.trace R S (b p.1 * b q.1 * G p.2 q.2)) =
      LinearMap.BilinForm.toMatrix (β b) ((traceDot R S κ).compRight (mulVecR R G)) := by
    ext p q
    rw [Matrix.of_apply, toMatrix_compRight_apply]
  rw [hM, LinearMap.BilinForm.toMatrix_compRight, Matrix.det_mul, det_toMatrix_traceDot, LinearMap.det_toMatrix,
    det_mulVecR b]

end DiscTower
p2m_reactivate "P2MW.S_Algebra_det_trace_basis_mul_basis_mul_eq_discr_pow_card_mul_norm_det.DiscTower"

theorem solution
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι R S) (G : Matrix κ κ S) :
    (Matrix.of fun p q : ι × κ => Algebra.trace R S (b p.1 * b q.1 * G p.2 q.2)).det =
      Algebra.discr R b ^ Fintype.card κ * Algebra.norm R G.det :=
  DiscTower.det_trace_mul_mul_eq b G

end S_Algebra_det_trace_basis_mul_basis_mul_eq_discr_pow_card_mul_norm_det
end P2MW
export P2MW.S_Algebra_det_trace_basis_mul_basis_mul_eq_discr_pow_card_mul_norm_det (solution)
