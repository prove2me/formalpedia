-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
-- name    : GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:09.6068+00:00
-- url     : https://prove2.me/theorems/f06f0fda-562c-4231-a620-c35e8b5d1910
-- title:
--   Fischer
-- statement:
--   Definitions and structural lemmas for Fischer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_left
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_right
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_left
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_right


set_option autoImplicit false
namespace GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {n : ℕ}
noncomputable def rowDer (i j : Fin n) : Derivation ℂ (Poly n) (Poly n) :=
  Derivation.mk' (rowOp i j) fun a b => by
    rw [rowOp_apply, rowOp_apply, rowOp_apply, smul_eq_mul, smul_eq_mul, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
@[simp] theorem rowDer_coe (i j : Fin n) : (rowDer i j : Module.End ℂ (Poly n)) = rowOp i j := rfl
def rowWt (m : Fin n × Fin n →₀ ℕ) (i : Fin n) : ℕ := ∑ k, m (i, k)
noncomputable def wtProj (μ : Fin n → ℕ) : Module.End ℂ (Poly n) where
  toFun f := ∑ m ∈ f.support with rowWt m = μ, monomial m (coeff m f)
  map_add' f g := by
    classical
    ext m
    simp only [coeff_sum, coeff_monomial, coeff_add]
    simp only [Finset.sum_ite_eq', Finset.mem_filter, MvPolynomial.mem_support_iff, coeff_add]
    by_cases hm : rowWt m = μ <;> simp only [hm, and_true, and_false, if_false]
    · by_cases h1 : coeff m f = 0 <;> by_cases h2 : coeff m g = 0 <;> by_cases h3 : coeff m f + coeff m g = 0 <;>
        simp_all
    · simp
  map_smul' c f := by
    classical
    ext m
    simp only [coeff_sum, coeff_monomial, coeff_smul, smul_eq_mul, RingHom.id_apply]
    simp only [Finset.sum_ite_eq', Finset.mem_filter, MvPolynomial.mem_support_iff, coeff_smul,
      smul_eq_mul]
    by_cases hm : rowWt m = μ <;> simp only [hm, and_true, and_false, if_false]
    · by_cases h1 : coeff m f = 0 <;> by_cases h2 : c * coeff m f = 0 <;> simp_all
    · simp
def wtHeight (μ : Fin n → ℕ) : ℤ := ∑ a, ((n : ℤ) - a) * μ a
end GroundTheory.Automorphic.HarishChandra


