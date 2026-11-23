-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:22.842146+00:00
-- url     : https://prove2.me/theorems/497801da-f673-47f3-ade1-2b4ba3c5b575
-- title:
--   Pred Mul Sum Padic Val Nat Factorial Add Card Le
-- statement:
--   Definitions and structural lemmas for Pred Mul Sum Padic Val Nat Factorial Add Card Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PredMulSumPadicValNatFactorialAddCardLe.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open Finsupp
section Words
variable {R : Type*} [CommRing R] {Λ : Type*} {B : Type*} [Ring B] [Algebra R B]
def opWord (D : Λ → B) (w : List Λ) : B := (w.map D).prod
@[simp] theorem opWord_nil (D : Λ → B) : opWord D [] = 1 := rfl
@[simp] theorem opWord_cons (D : Λ → B) (l : Λ) (w : List Λ) :
    opWord D (l :: w) = D l * opWord D w := by simp [opWord]
theorem opWord_append (D : Λ → B) (w w' : List Λ) :
    opWord D (w ++ w') = opWord D w * opWord D w' := by simp [opWord]
theorem opWord_perm {D : Λ → B} (hD : ∀ l l', Commute (D l) (D l')) {w w' : List Λ}
    (h : w.Perm w') : opWord D w = opWord D w' := by
  induction h with
  | nil => rfl
  | cons l _ ih => simp [ih]
  | swap l l' w => simp only [opWord_cons, ← mul_assoc, (hD l l').eq]
  | trans _ _ h₁ h₂ => exact h₁.trans h₂
def IsOrderingRule (ord : (Λ →₀ ℕ) → List Λ) : Prop :=
  ∀ α, (ord α : Multiset Λ) = Finsupp.toMultiset α
theorem isOrderingRule_toList :
    IsOrderingRule (fun α : Λ →₀ ℕ => (Finsupp.toMultiset α).toList) :=
  fun _ => Multiset.coe_toList _
noncomputable def opPoly (D : Λ → B) (ord : (Λ →₀ ℕ) → List Λ) : MvPolynomial Λ R →ₗ[R] B :=
  (MvPolynomial.basisMonomials Λ R).constr R (fun α => opWord D (ord α))
theorem opPoly_monomial (D : Λ → B) (ord : (Λ →₀ ℕ) → List Λ) (α : Λ →₀ ℕ) (c : R) :
    opPoly D ord (MvPolynomial.monomial α c) = c • opWord D (ord α) := by
  have h : MvPolynomial.monomial α c = c • MvPolynomial.basisMonomials Λ R α := by
    simp [MvPolynomial.smul_monomial]
  rw [h, map_smul, opPoly, Module.Basis.constr_basis]
theorem opPoly_mul_of_commute {D : Λ → B} (hD : ∀ l l', Commute (D l) (D l'))
    {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) (P Q : MvPolynomial Λ R) :
    opPoly D ord (P * Q) = opPoly D ord P * opPoly D ord Q := by
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [add_mul, map_add, hp, hq]
  | monomial α a =>
    induction Q using MvPolynomial.induction_on' with
    | add p q hp hq => simp only [mul_add, map_add, hp, hq]
    | monomial β b =>
      have hp : (ord (α + β)).Perm (ord α ++ ord β) := by
        rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, h, h, h, map_add]
      rw [MvPolynomial.monomial_mul, opPoly_monomial, opPoly_monomial, opPoly_monomial,
        opWord_perm hD hp, opWord_append, smul_mul_smul_comm]
theorem IsOrderingRule.ord_zero {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) :
    ord 0 = [] := by
  have := h 0
  simpa using this
theorem IsOrderingRule.ord_single {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) (l : Λ) :
    ord (single l 1) = [l] := by
  have := h (single l 1)
  rw [Finsupp.toMultiset_single, one_smul] at this
  exact List.perm_singleton.mp (Multiset.coe_eq_coe.mp this)
theorem opPoly_C (D : Λ → B) {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) (c : R) :
    opPoly D ord (MvPolynomial.C c) = algebraMap R B c := by
  rw [MvPolynomial.C_apply, opPoly_monomial, h.ord_zero, opWord_nil, Algebra.algebraMap_eq_smul_one]
theorem opPoly_X (D : Λ → B) {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) (l : Λ) :
    opPoly D ord (MvPolynomial.X l : MvPolynomial Λ R) = D l := by
  rw [MvPolynomial.X, opPoly_monomial, h.ord_single]
  simp
noncomputable def commEval (D : Λ → B) (hD : ∀ l l', Commute (D l) (D l')) :
    MvPolynomial Λ R →ₐ[R] B :=
  AlgHom.ofLinearMap (opPoly D fun α => (Finsupp.toMultiset α).toList)
    (by rw [← MvPolynomial.C_1, opPoly_C D isOrderingRule_toList, map_one])
    (opPoly_mul_of_commute hD isOrderingRule_toList)
@[simp] theorem commEval_X (D : Λ → B) (hD : ∀ l l', Commute (D l) (D l')) (l : Λ) :
    commEval D hD (MvPolynomial.X l : MvPolynomial Λ R) = D l :=
  opPoly_X D isOrderingRule_toList l
end Words
section General
variable {R A M Λ : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M]
end General
section Constant
open MvPolynomial
variable {R σ Λ : Type*} [CommRing R]
noncomputable def constDeriv (v : σ → R) : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  mkDerivation R fun i => C (v i)
@[simp] theorem constDeriv_X (v : σ → R) (i : σ) : constDeriv v (X i) = C (v i) :=
  mkDerivation_X _ _ _
theorem constDeriv_single [DecidableEq σ] (i : σ) :
    constDeriv (Pi.single i (1 : R)) = pderiv i := by
  refine derivation_ext fun j => ?_
  rw [constDeriv_X, pderiv_X]
  by_cases h : j = i
  · subst h; simp
  · simp [h]
theorem constDeriv_commute (v v' : σ → R) :
    Commute ((constDeriv v).toLinearMap : Module.End R (MvPolynomial σ R))
      (constDeriv v').toLinearMap := by
  have h : ⁅constDeriv v, constDeriv v'⁆ = 0 :=
    derivation_ext fun j => by simp [Derivation.commutator_apply]
  refine LinearMap.ext fun p => ?_
  have := congrArg (fun D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) => D p) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using this
theorem pderiv_commute (i j : σ) :
    Commute ((pderiv i).toLinearMap : Module.End R (MvPolynomial σ R)) (pderiv j).toLinearMap := by
  classical
  rw [← constDeriv_single, ← constDeriv_single]
  exact constDeriv_commute _ _
noncomputable def pderivEval : MvPolynomial σ R →ₐ[R] Module.End R (MvPolynomial σ R) :=
  commEval (fun i => (pderiv i).toLinearMap) pderiv_commute
noncomputable def constDerivEval (v : Λ → σ → R) :
    MvPolynomial Λ R →ₐ[R] Module.End R (MvPolynomial σ R) :=
  commEval (fun l => (constDeriv (v l)).toLinearMap) fun _ _ => constDeriv_commute _ _
def multiFactorial (α : σ →₀ ℕ) : ℕ := α.prod fun _ n => n.factorial
end Constant
section Series
open MvPowerSeries
variable {R σ Λ M : Type*} [CommRing R]
noncomputable abbrev germIdeal (σ R : Type*) [CommRing R] : Ideal (MvPowerSeries σ R) :=
  RingHom.ker (constantCoeff : MvPowerSeries σ R →+* R)
variable [Finite σ]
noncomputable def leadingForm (N : ℕ) : MvPowerSeries σ R →ₗ[R] MvPolynomial σ R :=
  MvPolynomial.homogeneousComponent N ∘ₗ truncTotal (N + 1)
noncomputable def derivAtOrigin (D : Derivation R (MvPowerSeries σ R) (MvPowerSeries σ R)) :
    σ → R := fun i => constantCoeff (D (X i))
end Series
section Symbol
open MvPowerSeries
variable {R σ Λ M : Type*} [CommRing R] [Finite σ] [AddCommGroup M] [Module R M]
  [Module (MvPowerSeries σ R) M]
variable [IsScalarTower R (MvPowerSeries σ R) M]
end Symbol
section Example
open MvPowerSeries
end Example
section Legendre
variable {l : ℕ} [hl : Fact l.Prime]
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
end Legendre
end GlobalTheory


