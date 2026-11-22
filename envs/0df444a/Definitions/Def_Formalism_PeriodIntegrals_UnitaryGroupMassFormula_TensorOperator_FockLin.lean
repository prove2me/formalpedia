-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:08.47818+00:00
-- url     : https://prove2.me/theorems/5106f4fc-a9ea-48c2-8b8a-4cd11aac5ed5
-- title:
--   Fock Lin
-- statement:
--   Definitions and structural lemmas for Fock Lin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FockLin.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace PI.TOW
open PI.TO
section Fock
variable {σ R : Type*} [CommRing R]
theorem fockR_eq_sum (f g : MvPolynomial σ R) (T : Finset (σ →₀ ℕ)) (hT : f.support ⊆ T) :
    fockR f g = ∑ m ∈ T, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) := by
  classical
  unfold fockR
  refine Finset.sum_subset hT fun m _ hm => ?_
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  rw [hm, zero_mul, zero_mul]
theorem fockR_add_left (f₁ f₂ g : MvPolynomial σ R) : fockR (f₁ + f₂) g = fockR f₁ g + fockR f₂ g := by
  classical
  rw [fockR_eq_sum (f₁ + f₂) g (f₁.support ∪ f₂.support) MvPolynomial.support_add,
    fockR_eq_sum f₁ g _ Finset.subset_union_left, fockR_eq_sum f₂ g _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_add]
  ring
theorem fockR_smul_left (a : R) (f g : MvPolynomial σ R) : fockR (a • f) g = a * fockR f g := by
  rw [fockR_eq_sum (a • f) g f.support MvPolynomial.support_smul]
  unfold fockR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]
  ring
theorem fockR_add_right (f g₁ g₂ : MvPolynomial σ R) : fockR f (g₁ + g₂) = fockR f g₁ + fockR f g₂ := by
  unfold fockR
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_add]
  ring
theorem fockR_smul_right (a : R) (f g : MvPolynomial σ R) : fockR f (a • g) = a * fockR f g := by
  unfold fockR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]
  ring
def fockB (σ R : Type*) [CommRing R] : MvPolynomial σ R →ₗ[R] MvPolynomial σ R →ₗ[R] R :=
  LinearMap.mk₂ R fockR fockR_add_left (fun a f g => by rw [fockR_smul_left, smul_eq_mul])
    fockR_add_right (fun a f g => by rw [fockR_smul_right, smul_eq_mul])
end Fock
section Words
variable {K : Type} [CommRing K] {n' k : ℕ}
theorem opWord_cons (y : Fin n' × (Fin k × Fin k)) (l : List (Fin n' × (Fin k × Fin k)))
    (f : MvPolynomial (Fin n' × Fin k) K) :
    opWord (y :: l) f = X (y.1, y.2.1) * pderiv (y.1, y.2.2) (opWord l f) := rfl
theorem opWord_add (l : List (Fin n' × (Fin k × Fin k))) (f g : MvPolynomial (Fin n' × Fin k) K) :
    opWord l (f + g) = opWord l f + opWord l g := by
  induction l with
  | nil => rfl
  | cons y l ih => rw [opWord_cons, opWord_cons, opWord_cons, ih, map_add, mul_add]
theorem opWord_smul (l : List (Fin n' × (Fin k × Fin k))) (a : K) (f : MvPolynomial (Fin n' × Fin k) K) :
    opWord l (a • f) = a • opWord l f := by
  induction l with
  | nil => rfl
  | cons y l ih => rw [opWord_cons, opWord_cons, ih, Derivation.map_smul, mul_smul_comm]
def opWordL (l : List (Fin n' × (Fin k × Fin k))) :
    MvPolynomial (Fin n' × Fin k) K →ₗ[K] MvPolynomial (Fin n' × Fin k) K where
  toFun := opWord l
  map_add' := opWord_add l
  map_smul' a f := opWord_smul l a f
theorem combo_add_fun (f : List (Fin n' × (Fin k × Fin k)) →₀ K) (G₁ G₂ : MvPolynomial (Fin n' × Fin k) K) :
    combo f (G₁ + G₂) = combo f G₁ + combo f G₂ := by
  unfold combo
  rw [← Finsupp.sum_add]
  exact Finsupp.sum_congr fun l _ => by rw [opWord_add, smul_add]
theorem combo_smul_fun (f : List (Fin n' × (Fin k × Fin k)) →₀ K) (a : K) (G : MvPolynomial (Fin n' × Fin k) K) :
    combo f (a • G) = a • combo f G := by
  unfold combo
  rw [Finsupp.smul_sum]
  exact Finsupp.sum_congr fun l _ => by rw [opWord_smul, smul_comm]
def comboL (f : List (Fin n' × (Fin k × Fin k)) →₀ K) :
    MvPolynomial (Fin n' × Fin k) K →ₗ[K] MvPolynomial (Fin n' × Fin k) K where
  toFun := combo f
  map_add' := combo_add_fun f
  map_smul' a G := combo_smul_fun f a G
end Words
end PI.TOW


