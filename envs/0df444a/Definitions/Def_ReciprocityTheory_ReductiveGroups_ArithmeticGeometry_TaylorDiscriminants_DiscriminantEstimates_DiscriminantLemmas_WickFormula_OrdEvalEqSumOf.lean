-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:38:17.339699+00:00
-- url     : https://prove2.me/theorems/aa722ae6-241a-44d5-b146-23f1d243665a
-- title:
--   Ord Eval Eq Sum Of
-- statement:
--   Definitions and structural lemmas for Ord Eval Eq Sum Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/OrdEvalEqSumOf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace PI.WickFormula
section lprod
variable {AA : Type} [Ring AA]
def lprod {n : ℕ} (c : Fin n → AA) (e : Fin n → ℕ) : AA := (List.ofFn fun i => c i ^ e i).prod
end lprod
section ord
variable {k AA : Type} [CommRing k] [Ring AA] [Algebra k AA] {r s : ℕ}
def omon (a : Fin r → AA) (a' : Fin s → AA) (m : Fin r ⊕ Fin s →₀ ℕ) : AA :=
  lprod a (fun i => m (Sum.inl i)) * lprod a' (fun j => m (Sum.inr j))
theorem ordEval_eq (a : Fin r → AA) (a' : Fin s → AA) (P : MvPolynomial (Fin r ⊕ Fin s) k) :
    ordEval a a' P = ∑ m ∈ P.support, P.coeff m • omon a a' m := rfl
theorem ordEval_eq_sum_of (a : Fin r → AA) (a' : Fin s → AA) (P : MvPolynomial (Fin r ⊕ Fin s) k)
    (t : Finset (Fin r ⊕ Fin s →₀ ℕ)) (ht : P.support ⊆ t) :
    ordEval a a' P = ∑ m ∈ t, P.coeff m • omon a a' m := by
  rw [ordEval_eq]
  refine Finset.sum_subset ht fun m _ hm => ?_
  have h0 : P.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  rw [h0, zero_smul]
theorem ordEval_add (a : Fin r → AA) (a' : Fin s → AA) (P Q : MvPolynomial (Fin r ⊕ Fin s) k) :
    ordEval a a' (P + Q) = ordEval a a' P + ordEval a a' Q := by
  rw [ordEval_eq_sum_of a a' (P + Q) (P.support ∪ Q.support) MvPolynomial.support_add,
    ordEval_eq_sum_of a a' P _ (fun x hx => Finset.mem_union_left _ hx),
    ordEval_eq_sum_of a a' Q _ (fun x hx => Finset.mem_union_right _ hx), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, add_smul]
theorem ordEval_smul (a : Fin r → AA) (a' : Fin s → AA) (c : k) (P : MvPolynomial (Fin r ⊕ Fin s) k) :
    ordEval a a' (c • P) = c • ordEval a a' P := by
  rw [ordEval_eq_sum_of a a' (c • P) P.support MvPolynomial.support_smul, ordEval_eq, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_smul]
noncomputable def ordL (k : Type) [CommRing k] [Algebra k AA] (a : Fin r → AA) (a' : Fin s → AA) :
    MvPolynomial (Fin r ⊕ Fin s) k →ₗ[k] AA where
  toFun := ordEval a a'
  map_add' := ordEval_add a a'
  map_smul' := ordEval_smul a a'
end ord
end PI.WickFormula


