-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:54:00.578261+00:00
-- url     : https://prove2.me/theorems/06bd1824-958a-4e5e-9261-953d02f78e2d
-- title:
--   LPSOriginal Relative Gauss Frobenius Descent
-- statement:
--   Definitions and structural lemmas for LPSOriginal Relative Gauss Frobenius Descent, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFrobeniusDescent.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondBranches
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalSubfield_eval__mem_0d401beef6d5
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAdjoinRoot_surjective_subfield_eq_top
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_charP
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_integerBaseEval
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLocalization_subfield_mem
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationInseparableBranchMap_secondJ
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
def lpsOriginalAdjoinRootPrimePowerFrobeniusDescent
    {K : Type*} [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (a : K) :
    AdjoinRoot ((Polynomial.X : Polynomial K)^p - Polynomial.C a) →+* K :=
  AdjoinRoot.lift (frobenius K p) a (by simp [frobenius_def])
lemma lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_of
    {K : Type*} [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (a u : K) :
    lpsOriginalAdjoinRootPrimePowerFrobeniusDescent p a
      (AdjoinRoot.of ((Polynomial.X : Polynomial K)^p - Polynomial.C a) u) = u^p := by
  simp [lpsOriginalAdjoinRootPrimePowerFrobeniusDescent, AdjoinRoot.lift_of, frobenius_def]
lemma lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_root
    {K : Type*} [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (a : K) :
    lpsOriginalAdjoinRootPrimePowerFrobeniusDescent p a
      (AdjoinRoot.root ((Polynomial.X : Polynomial K)^p - Polynomial.C a)) = a := by
  simp [lpsOriginalAdjoinRootPrimePowerFrobeniusDescent, AdjoinRoot.lift_root]
lemma lpsOriginalGaussMaximalResidue_subfield_eq_top
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    ∀ S : Subfield (LPSOriginalGaussAffineOrder N hN p ⧸ q),
      lpsOriginalGaussMaximalResidueJ N hN p q ∈ S →
      lpsOriginalGaussMaximalResidueJN N hN p q ∈ S → S = ⊤ := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  intro S hj hn
  let g : LPSOriginalGaussBase p →+* K :=
    (Ideal.Quotient.mk q).comp (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p))
  have hc : ∀ a : LPSOriginalGaussBase p, g a ∈ S := by
    intro a
    apply lpsOriginalLocalization_subfield_mem (Polynomial ℤ) (LPSOriginalGaussBase p)
      K (lpsOriginalGaussPrime p).primeCompl g S _ a
    intro P
    change (g.comp (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p))) P ∈ S
    rw [lpsOriginalGaussMaximalResidue_integerBaseEval]
    exact lpsOriginalSubfield_eval₂_mem ℤ K (Int.castRingHom K) S
      (fun z => S.intCast_mem z) _ hj P
  exact lpsOriginalAdjoinRoot_surjective_subfield_eq_top (LPSOriginalGaussBase p) K
    (lpsOriginalGaussPolynomial N hN p) (Ideal.Quotient.mk q)
    (Ideal.Quotient.mk_surjective) S hc hn
def lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    LPSOriginalRelativeGaussInseparableBranch N hN p q →+*
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
    lpsOriginalGaussMaximalResidue_charP N hN p q
  exact lpsOriginalAdjoinRootPrimePowerFrobeniusDescent p
    (lpsOriginalGaussMaximalResidueJN N hN p q)
lemma lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent_secondJ
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent N hN p q
      (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
        (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN)) =
      lpsOriginalGaussMaximalResidueJ N hN p q := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let f := lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent N hN p q
  have h := congrArg f
    (lpsOriginalRelativeGaussNormalizationInseparableBranchMap_secondJ
      N p hNp h4N hN hpN q)
  rw [map_pow] at h
  have hc : f (AdjoinRoot.of ((Polynomial.X : Polynomial K)^p -
      Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))
      (lpsOriginalGaussMaximalResidueJ N hN p q)) =
      (lpsOriginalGaussMaximalResidueJ N hN p q)^p :=
    lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_of p _ _
  rw [hc] at h
  exact (frobenius K p).injective h
lemma lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent_surjective
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    Function.Surjective (lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent N hN p q) := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let T := LPSOriginalRelativeGaussInseparableBranch N hN p q
  let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
  let f : T →+* K := lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent N hN p q
  let L : Subfield K := f.fieldRange
  have hj : lpsOriginalGaussMaximalResidueJ N hN p q ∈ L := by
    refine ⟨lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN), ?_⟩
    exact lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent_secondJ N p hNp h4N hN hpN q
  have hn : lpsOriginalGaussMaximalResidueJN N hN p q ∈ L := by
    refine ⟨AdjoinRoot.root ((Polynomial.X : Polynomial K)^p -
      Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)), ?_⟩
    exact lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_root p _
  have hs : L = ⊤ := lpsOriginalGaussMaximalResidue_subfield_eq_top N hN p q L hj hn
  exact RingHom.fieldRange_eq_top_iff.mp hs
def lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    LPSOriginalRelativeGaussInseparableBranch N hN p q ≃+*
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let T := LPSOriginalRelativeGaussInseparableBranch N hN p q
  let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
  let f : T →+* K := lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent N hN p q
  exact RingEquiv.ofBijective f ⟨f.injective,
    lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent_surjective N p hNp h4N hN hpN q⟩
def lpsOriginalRelativeGaussInseparableBranchFrobeniusAlgEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    letI : Field K := Ideal.Quotient.field q
    letI : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
    let T := LPSOriginalRelativeGaussInseparableBranch N hN p q
    letI : Algebra K T := inferInstance
    letI : Algebra K K := (frobenius K p).toAlgebra
    T ≃ₐ[K] K := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let T := LPSOriginalRelativeGaussInseparableBranch N hN p q
  let : Algebra K T := inferInstance
  let : Algebra K K := (frobenius K p).toAlgebra
  let e := lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q
  apply AlgEquiv.ofRingEquiv (f := e)
  intro u
  change lpsOriginalAdjoinRootPrimePowerFrobeniusDescent p
    (lpsOriginalGaussMaximalResidueJN N hN p q)
    (AdjoinRoot.of ((Polynomial.X : Polynomial K)^p -
      Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)) u) = u^p
  exact lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_of p _ u
end
end QEC.Coding.TannerLiftedProduct


