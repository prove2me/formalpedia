-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:24:22.788343+00:00
-- url     : https://prove2.me/theorems/1aa2e2a8-2cd6-4c00-94dc-941e70286168
-- title:
--   LPSOriginal Relative Gauss Branches
-- statement:
--   Definitions and structural lemmas for LPSOriginal Relative Gauss Branches, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
def lpsOriginalCoprimeAdjoinRootEquiv
    {R : Type*} [CommRing R] (P Q : Polynomial R) (h : IsCoprime P Q) :
    AdjoinRoot (P*Q) ≃+* AdjoinRoot P × AdjoinRoot Q :=
  (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton P Q).symm).trans
    (Ideal.quotientMulEquivQuotientProd (Ideal.span {P}) (Ideal.span {Q})
      ((Ideal.isCoprime_span_singleton_iff P Q).mpr h))
lemma lpsOriginalCoprimeAdjoinRootEquiv_mk
    {R : Type*} [CommRing R] (P Q : Polynomial R) (h : IsCoprime P Q)
    (f : Polynomial R) :
    lpsOriginalCoprimeAdjoinRootEquiv P Q h (AdjoinRoot.mk (P*Q) f) =
      (AdjoinRoot.mk P f,AdjoinRoot.mk Q f) := by
  dsimp only [lpsOriginalCoprimeAdjoinRootEquiv]
  erw [RingEquiv.trans_apply,Ideal.quotEquivOfEq_mk]
  apply Prod.ext
  · erw [Ideal.quotientMulEquivQuotientProd_fst]
  · erw [Ideal.quotientMulEquivQuotientProd_snd]
lemma lpsOriginalRelativeGaussHeckeResidueFactors_coprime
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    IsCoprime
      ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q)) -
        Polynomial.C ((lpsOriginalGaussMaximalResidueJN N hN p q)^p))
      (Polynomial.X^p - Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)) := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  have hi := lpsOriginalRelativeGaussHeckeInseparableFactor_irreducible N hN p hpN q
  apply IsCoprime.symm
  apply hi.coprime_iff_not_dvd.mpr
  intro hdiv
  have hdeg := Polynomial.natDegree_le_of_dvd hdiv
    (Polynomial.X_sub_C_ne_zero ((lpsOriginalGaussMaximalResidueJN N hN p q)^p))
  rw [Polynomial.natDegree_X_pow_sub_C,Polynomial.natDegree_X_sub_C] at hdeg
  exact (Nat.not_le_of_gt (Fact.out : p.Prime).one_lt) hdeg
abbrev LPSOriginalRelativeGaussInseparableBranch
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) :=
  AdjoinRoot ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
    Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))
@[instance_reducible]
def lpsOriginalRelativeGaussInseparableBranch_field
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Field (LPSOriginalRelativeGaussInseparableBranch N hN p q) := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let : Fact (Irreducible
      ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
        Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))) :=
    ⟨lpsOriginalRelativeGaussHeckeInseparableFactor_irreducible N hN p hpN q⟩
  infer_instance
def lpsOriginalRelativeGaussResiduePolynomialEquiv
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    AdjoinRoot ((lpsOriginalRelativeGaussHeckePolynomial N hN p).map
      (Ideal.Quotient.mk q)) ≃+*
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) ×
        LPSOriginalRelativeGaussInseparableBranch N hN p q := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let a := lpsOriginalGaussMaximalResidueJN N hN p q
  let P : Polynomial K := Polynomial.X - Polynomial.C (a^p)
  let Q : Polynomial K := Polynomial.X^p - Polynomial.C a
  let e : AdjoinRoot ((lpsOriginalRelativeGaussHeckePolynomial N hN p).map
      (Ideal.Quotient.mk q)) ≃+* AdjoinRoot (P*Q) :=
    Ideal.quotEquivOfEq (congrArg (fun f : Polynomial K => Ideal.span {f})
      (lpsOriginalRelativeGaussHeckePolynomial_residue N hN p q))
  exact e.trans ((lpsOriginalCoprimeAdjoinRootEquiv P Q
    (lpsOriginalRelativeGaussHeckeResidueFactors_coprime N hN p hpN q)).trans
      (RingEquiv.prodCongr (Polynomial.quotientSpanXSubCAlgEquiv (a^p)).toRingEquiv
        (RingEquiv.refl (AdjoinRoot Q))))
def lpsOriginalRelativeGaussHeckeFiberEquiv
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeOrder N hN p ⧸ q.map
      (algebraMap (LPSOriginalGaussAffineOrder N hN p)
        (LPSOriginalRelativeGaussHeckeOrder N hN p))) ≃+*
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) ×
        LPSOriginalRelativeGaussInseparableBranch N hN p q :=
  (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot q
    (lpsOriginalRelativeGaussHeckePolynomial N hN p)).trans
      (lpsOriginalRelativeGaussResiduePolynomialEquiv N hN p hpN q)
lemma lpsOriginalRelativeGaussResiduePolynomialEquiv_mk
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (f : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q)) :
    lpsOriginalRelativeGaussResiduePolynomialEquiv N hN p hpN q
      (AdjoinRoot.mk ((lpsOriginalRelativeGaussHeckePolynomial N hN p).map
        (Ideal.Quotient.mk q)) f) =
      (f.eval ((lpsOriginalGaussMaximalResidueJN N hN p q)^p),
        AdjoinRoot.mk ((Polynomial.X : Polynomial
          (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
            Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)) f) := by
  dsimp only [lpsOriginalRelativeGaussResiduePolynomialEquiv]
  erw [RingEquiv.trans_apply,Ideal.quotEquivOfEq_mk,RingEquiv.trans_apply,
    lpsOriginalCoprimeAdjoinRootEquiv_mk]
  rfl
lemma lpsOriginalRelativeGaussHeckeFiberEquiv_mk
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (f : Polynomial (LPSOriginalGaussAffineOrder N hN p)) :
    lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q
      (Ideal.Quotient.mk (q.map (AdjoinRoot.of
        (lpsOriginalRelativeGaussHeckePolynomial N hN p)))
        (AdjoinRoot.mk (lpsOriginalRelativeGaussHeckePolynomial N hN p) f)) =
      ((f.map (Ideal.Quotient.mk q)).eval
        ((lpsOriginalGaussMaximalResidueJN N hN p q)^p),
        AdjoinRoot.mk ((Polynomial.X : Polynomial
          (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
            Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))
              (f.map (Ideal.Quotient.mk q))) := by
  change lpsOriginalRelativeGaussResiduePolynomialEquiv N hN p hpN q
    (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot q
      (lpsOriginalRelativeGaussHeckePolynomial N hN p)
      (Ideal.Quotient.mk _ (AdjoinRoot.mk _ f))) = _
  rw [AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of]
  exact lpsOriginalRelativeGaussResiduePolynomialEquiv_mk N hN p hpN q _
lemma lpsOriginalRelativeGaussHeckeFiberEquiv_base
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (c : LPSOriginalGaussAffineOrder N hN p) :
    lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q
      (Ideal.Quotient.mk (q.map (AdjoinRoot.of
        (lpsOriginalRelativeGaussHeckePolynomial N hN p)))
        (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p) c)) =
      (Ideal.Quotient.mk q c,
        AdjoinRoot.of ((Polynomial.X : Polynomial
          (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
            Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))
              (Ideal.Quotient.mk q c)) := by
  simpa only [Polynomial.map_C,Polynomial.eval_C,AdjoinRoot.of,RingHom.comp_apply] using
    lpsOriginalRelativeGaussHeckeFiberEquiv_mk N hN p hpN q (Polynomial.C c)
def lpsOriginalRelativeGaussHeckeBranchMap
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    LPSOriginalRelativeGaussHeckeOrder N hN p →+*
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) ×
        LPSOriginalRelativeGaussInseparableBranch N hN p q :=
  (lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q).toRingHom.comp
    (Ideal.Quotient.mk (q.map (AdjoinRoot.of
      (lpsOriginalRelativeGaussHeckePolynomial N hN p))))
lemma lpsOriginalRelativeGaussHeckeBranchMap_surjective
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Function.Surjective (lpsOriginalRelativeGaussHeckeBranchMap N hN p hpN q) :=
  (lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q).surjective.comp
    Ideal.Quotient.mk_surjective
def lpsOriginalRelativeGaussHeckeLinearBranchMap
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    LPSOriginalRelativeGaussHeckeOrder N hN p →+*
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) :=
  (RingHom.fst _ _).comp (lpsOriginalRelativeGaussHeckeBranchMap N hN p hpN q)
def lpsOriginalRelativeGaussHeckeInseparableBranchMap
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    LPSOriginalRelativeGaussHeckeOrder N hN p →+*
      LPSOriginalRelativeGaussInseparableBranch N hN p q :=
  (RingHom.snd _ _).comp (lpsOriginalRelativeGaussHeckeBranchMap N hN p hpN q)
abbrev LPSOriginalRelativeGaussHeckeLinearBranchIdeal
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :=
  RingHom.ker (lpsOriginalRelativeGaussHeckeLinearBranchMap N hN p hpN q)
abbrev LPSOriginalRelativeGaussHeckeInseparableBranchIdeal
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :=
  RingHom.ker (lpsOriginalRelativeGaussHeckeInseparableBranchMap N hN p hpN q)
lemma lpsOriginalRelativeGaussHeckeLinearBranchMap_surjective
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Function.Surjective (lpsOriginalRelativeGaussHeckeLinearBranchMap N hN p hpN q) := by
  intro y
  obtain ⟨x,hx⟩ := lpsOriginalRelativeGaussHeckeBranchMap_surjective N hN p hpN q (y,0)
  exact ⟨x,congrArg Prod.fst hx⟩
lemma lpsOriginalRelativeGaussHeckeInseparableBranchMap_surjective
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Function.Surjective (lpsOriginalRelativeGaussHeckeInseparableBranchMap N hN p hpN q) := by
  intro y
  obtain ⟨x,hx⟩ := lpsOriginalRelativeGaussHeckeBranchMap_surjective N hN p hpN q (0,y)
  exact ⟨x,congrArg Prod.snd hx⟩
lemma lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_maximal
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q).IsMaximal := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
  exact RingHom.ker_isMaximal_of_surjective _
    (lpsOriginalRelativeGaussHeckeInseparableBranchMap_surjective N hN p hpN q)
lemma lpsOriginalRelativeGaussHeckeLinearBranchIdeal_contract
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q).comap
      (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p)) = q := by
  ext c
  change (lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q
    (Ideal.Quotient.mk _ (AdjoinRoot.of
      (lpsOriginalRelativeGaussHeckePolynomial N hN p) c))).1 = 0 ↔ c ∈ q
  erw [congrArg Prod.fst (lpsOriginalRelativeGaussHeckeFiberEquiv_base N hN p hpN q c)]
  exact Ideal.Quotient.eq_zero_iff_mem
lemma lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_contract
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q).comap
      (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p)) = q := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let Q : Polynomial K := Polynomial.X^p -
    Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)
  let : Field K := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
  have hi : Function.Injective (AdjoinRoot.of Q) := (algebraMap K (AdjoinRoot Q)).injective
  ext c
  change (lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q
    (Ideal.Quotient.mk _ (AdjoinRoot.of
      (lpsOriginalRelativeGaussHeckePolynomial N hN p) c))).2 = 0 ↔ c ∈ q
  erw [congrArg Prod.snd (lpsOriginalRelativeGaussHeckeFiberEquiv_base N hN p hpN q c)]
  rw [← map_zero (AdjoinRoot.of Q),hi.eq_iff,Ideal.Quotient.eq_zero_iff_mem]
lemma lpsOriginalRelativeGaussHeckeLinearBranchIdeal_liesOver
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q).LiesOver q := by
  constructor
  exact (lpsOriginalRelativeGaussHeckeLinearBranchIdeal_contract N hN p hpN q).symm
lemma lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_liesOver
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q).LiesOver q := by
  constructor
  exact (lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_contract N hN p hpN q).symm
def lpsOriginalRelativeGaussHeckeLinearBranchResidueEquiv
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussHeckeLinearBranchIdeal_liesOver N hN p hpN q
    (LPSOriginalRelativeGaussHeckeOrder N hN p ⧸
      LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q) ≃ₐ[
        LPSOriginalGaussAffineOrder N hN p ⧸ q] (LPSOriginalGaussAffineOrder N hN p ⧸ q) := by
  let := lpsOriginalRelativeGaussHeckeLinearBranchIdeal_liesOver N hN p hpN q
  refine { (RingHom.quotientKerEquivOfSurjective
      (lpsOriginalRelativeGaussHeckeLinearBranchMap_surjective N hN p hpN q)) with
    commutes' := ?_ }
  intro c
  obtain ⟨c,rfl⟩ := Ideal.Quotient.mk_surjective c
  change lpsOriginalRelativeGaussHeckeLinearBranchMap N hN p hpN q
    (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p) c) = Ideal.Quotient.mk q c
  exact congrArg Prod.fst (lpsOriginalRelativeGaussHeckeFiberEquiv_base N hN p hpN q c)
def lpsOriginalRelativeGaussHeckeInseparableBranchResidueEquiv
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_liesOver N hN p hpN q
    (LPSOriginalRelativeGaussHeckeOrder N hN p ⧸
      LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q) ≃ₐ[
        LPSOriginalGaussAffineOrder N hN p ⧸ q]
      LPSOriginalRelativeGaussInseparableBranch N hN p q := by
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_liesOver N hN p hpN q
  refine { (RingHom.quotientKerEquivOfSurjective
      (lpsOriginalRelativeGaussHeckeInseparableBranchMap_surjective N hN p hpN q)) with
    commutes' := ?_ }
  intro c
  obtain ⟨c,rfl⟩ := Ideal.Quotient.mk_surjective c
  change lpsOriginalRelativeGaussHeckeInseparableBranchMap N hN p hpN q
    (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p) c) =
      AdjoinRoot.of ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
        Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)) (Ideal.Quotient.mk q c)
  exact congrArg Prod.snd (lpsOriginalRelativeGaussHeckeFiberEquiv_base N hN p hpN q c)
end
end QEC.Coding.TannerLiftedProduct


