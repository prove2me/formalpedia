-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormPderivIterLeOfAnalyticAt
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormPderivIterLeOfAnalyticAt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:24:22.505398+00:00
-- url     : https://prove2.me/theorems/792b2def-7532-4434-9651-30aa23943d72
-- title:
--   Norm Pderiv Iter Le Of Analytic At
-- statement:
--   Definitions and structural lemmas for Norm Pderiv Iter Le Of Analytic At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormPderivIterLeOfAnalyticAt.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero


set_option autoImplicit false
open Filter Topology
namespace GlobalTheory
section Def
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
noncomputable def pderivList (l : List ι) (F : (ι → 𝕜) → V) : (ι → 𝕜) → V :=
  lineDerivList 𝕜 (l.map fun k => Pi.single k (1 : 𝕜)) F
noncomputable def pderivIter (α : ι →₀ ℕ) (F : (ι → 𝕜) → V) : (ι → 𝕜) → V :=
  pderivList α.toMultiset.toList F
noncomputable def polyDeriv (P : MvPolynomial ι 𝕜) (F : (ι → 𝕜) → V) (a : ι → 𝕜) : V :=
  ∑ α ∈ P.support, P.coeff α • pderivIter α F a
@[simp] theorem pderivList_nil (F : (ι → 𝕜) → V) : pderivList [] F = F := rfl
@[simp] theorem pderivIter_zero (F : (ι → 𝕜) → V) : pderivIter 0 F = F := by
  simp [pderivIter]
@[simp] theorem pderivIter_zero_fun (α : ι →₀ ℕ) :
    pderivIter α (fun _ : ι → 𝕜 => (0 : V)) = fun _ => 0 :=
  lineDerivList_zero _
theorem polyDeriv_eq_sum_of_subset (P : MvPolynomial ι 𝕜) {s : Finset (ι →₀ ℕ)}
    (hs : P.support ⊆ s) (F : (ι → 𝕜) → V) (a : ι → 𝕜) :
    polyDeriv P F a = ∑ α ∈ s, P.coeff α • pderivIter α F a := by
  refine Finset.sum_subset hs fun α _ hα => ?_
  rw [MvPolynomial.notMem_support_iff.1 hα, zero_smul]
noncomputable def polyDerivLinear (F : (ι → 𝕜) → V) (a : ι → 𝕜) : MvPolynomial ι 𝕜 →ₗ[𝕜] V where
  toFun P := polyDeriv P F a
  map_add' P Q := by
    classical
    rw [polyDeriv_eq_sum_of_subset (P + Q) (s := P.support ∪ Q.support) MvPolynomial.support_add,
      polyDeriv_eq_sum_of_subset P (s := P.support ∪ Q.support) Finset.subset_union_left,
      polyDeriv_eq_sum_of_subset Q (s := P.support ∪ Q.support) Finset.subset_union_right,
      ← Finset.sum_add_distrib]
    simp only [MvPolynomial.coeff_add, add_smul]
  map_smul' c P := by
    rw [polyDeriv_eq_sum_of_subset (c • P) (s := P.support) MvPolynomial.support_smul,
      polyDeriv, Finset.smul_sum]
    simp only [MvPolynomial.coeff_smul, smul_eq_mul, mul_smul, RingHom.id_apply]
end Def
section Analytic
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι] [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [CompleteSpace V]
end Analytic
section Polynomial
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι]
end Polynomial
section Cauchy
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
end Cauchy
end GlobalTheory


