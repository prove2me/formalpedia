-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LinearIndependentC
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LinearIndependentC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:14.533088+00:00
-- url     : https://prove2.me/theorems/8aa26d07-c29d-4527-9263-db07dc56599e
-- title:
--   Linear Independent C
-- statement:
--   Definitions and structural lemmas for Linear Independent C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/LinearIndependentC.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0.PolynomialCoordinateBasis
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {L E : Type} [Field L] [Field E] [Algebra L E] {σ : Type}
lemma coeff_smul_C (q : MvPolynomial σ L) (e : E) (m : σ →₀ ℕ) :
    coeff m (q • C e : MvPolynomial σ E) = algebraMap L E (coeff m q) * e := by
  rw [Algebra.smul_def, algebraMap_def, mul_comm, coeff_C_mul, coeff_map, mul_comm]
variable {n : Type} [Fintype n] (b : Module.Basis n L E)
noncomputable def crd (p : MvPolynomial σ E) (i : n) : MvPolynomial σ L :=
  ∑ m ∈ p.support, monomial m (b.repr (coeff m p) i)
lemma coeff_crd (p : MvPolynomial σ E) (i : n) (m : σ →₀ ℕ) :
    coeff m (crd b p i) = b.repr (coeff m p) i := by
  classical
  rw [crd, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero, Finsupp.zero_apply]
lemma eq_sum_crd (p : MvPolynomial σ E) : p = ∑ i, crd b p i • (C (b i) : MvPolynomial σ E) := by
  ext m
  rw [coeff_sum]
  simp only [coeff_smul_C, coeff_crd, ← Algebra.smul_def]
  exact (b.sum_repr (coeff m p)).symm
lemma linearIndependent_C : LinearIndependent (MvPolynomial σ L) (fun i => (C (b i) : MvPolynomial σ E)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  ext m
  have h := congrArg (coeff m) hg
  rw [coeff_sum, coeff_zero] at h
  simp only [coeff_smul_C, ← Algebra.smul_def] at h
  have := (Fintype.linearIndependent_iff.1 b.linearIndependent) (fun i => coeff m (g i)) h i
  rw [this, coeff_zero]
noncomputable def polyBasis : Module.Basis n (MvPolynomial σ L) (MvPolynomial σ E) :=
  Module.Basis.mk (linearIndependent_C b) (fun p _ => by
    rw [eq_sum_crd b p]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
end ReciprocityTheory.ChartRestriction.G.T0.PolynomialCoordinateBasis


