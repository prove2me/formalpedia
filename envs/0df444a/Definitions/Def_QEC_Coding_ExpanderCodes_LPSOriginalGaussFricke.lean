-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFricke
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalGaussFricke
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T11:14:52.922536+00:00
-- url     : https://prove2.me/theorems/169a00f3-4f8d-419f-af5c-3cc73a5903ff
-- title:
--   LPSOriginal Gauss Fricke
-- statement:
--   Definitions and structural lemmas for LPSOriginal Gauss Fricke, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussFricke.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_eval__hom_5c9005d9bf86
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_gaussDualRoot
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
lemma lpsOriginalGaussMaximalResidueJN_integerPolynomial_isUnit
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (P : Polynomial ℤ) (hP : P ∉ lpsOriginalGaussPrime p) :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    IsUnit (P.eval₂ (Int.castRingHom (LPSOriginalGaussAffineOrder N hN p ⧸ q))
      (lpsOriginalGaussMaximalResidueJN N hN p q)) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueConstantMap N hN p q).toAlgebra
  let f : Polynomial (ZMod p) →+* K :=
    Polynomial.eval₂RingHom (lpsOriginalGaussMaximalResidueConstantMap N hN p q)
      (lpsOriginalGaussMaximalResidueJN N hN p q)
  have hi : Function.Injective f := transcendental_iff_injective.mp
    (lpsOriginalGaussMaximalResidueJN_transcendental N hN p hpN q)
  have hn : P.map (Int.castRingHom (ZMod p)) ≠ 0 := by
    intro h
    exact hP h
  have hx : f (P.map (Int.castRingHom (ZMod p))) =
      P.eval₂ (Int.castRingHom K) (lpsOriginalGaussMaximalResidueJN N hN p q) := by
    change (P.map (Int.castRingHom (ZMod p))).eval₂
      (lpsOriginalGaussMaximalResidueConstantMap N hN p q)
      (lpsOriginalGaussMaximalResidueJN N hN p q) = _
    rw [Polynomial.eval₂_map]
    have hc : (lpsOriginalGaussMaximalResidueConstantMap N hN p q).comp
        (Int.castRingHom (ZMod p)) = Int.castRingHom K := by
      ext z
      simp
    rw [hc]
  apply isUnit_iff_ne_zero.mpr
  rw [← hx]
  intro h
  exact hn (hi (h.trans (map_zero f).symm))
lemma lpsOriginalGaussAffineOrder_rootInteger_isUnit
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (P : Polynomial ℤ) (hP : P ∉ lpsOriginalGaussPrime p) :
    IsUnit (P.eval₂ (Int.castRingHom (LPSOriginalGaussAffineOrder N hN p))
      (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))) := by
  by_contra hu
  obtain ⟨q, hq, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
  let : q.IsMaximal := hq
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  have hunit : IsUnit (Ideal.Quotient.mk q
      (P.eval₂ (Int.castRingHom (LPSOriginalGaussAffineOrder N hN p))
        (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)))) := by
    rw [lpsOriginalIntegerPolynomial_eval₂_hom]
    exact lpsOriginalGaussMaximalResidueJN_integerPolynomial_isUnit N hN p hpN q P hP
  have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [hzero] at hunit
  exact not_isUnit_zero hunit
def lpsOriginalGaussFrickeBaseMap
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    LPSOriginalGaussBase p →+* LPSOriginalGaussAffineOrder N hN p := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  exact IsLocalization.lift (M := (lpsOriginalGaussPrime p).primeCompl) (S := LPSOriginalGaussBase p)
    (g := Polynomial.eval₂RingHom (Int.castRingHom _) (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)))
    (fun s => lpsOriginalGaussAffineOrder_rootInteger_isUnit N hN p hpN s s.property)
lemma lpsOriginalGaussFrickeBaseMap_integer
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (P : Polynomial ℤ) :
    lpsOriginalGaussFrickeBaseMap N hN p hpN
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) P) =
        P.eval₂ (Int.castRingHom _) (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)) := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  dsimp only [lpsOriginalGaussFrickeBaseMap]
  exact IsLocalization.lift_eq _ P
lemma lpsOriginalGaussFrickeBaseMap_integer_comp
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    (lpsOriginalGaussFrickeBaseMap N hN p hpN).comp
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p)) =
        Polynomial.eval₂RingHom (Int.castRingHom _) (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)) := by
  apply RingHom.ext
  intro P
  exact lpsOriginalGaussFrickeBaseMap_integer N hN p hpN P
lemma lpsOriginalGaussFrickeBaseMap_levelRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    (lpsOriginalGaussPolynomial N hN p).eval₂
      (lpsOriginalGaussFrickeBaseMap N hN p hpN)
      (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)) = 0 := by
  change ((lpsOriginalIntegerPolynomial N hN).map
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p))).eval₂ _ _ = 0
  rw [Polynomial.eval₂_map, lpsOriginalGaussFrickeBaseMap_integer_comp]
  exact lpsOriginalIntegerPolynomial_gaussDualRoot N hN p hpN
def lpsOriginalGaussFrickeOrderMap
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    LPSOriginalGaussAffineOrder N hN p →+* LPSOriginalGaussAffineOrder N hN p :=
  AdjoinRoot.lift (lpsOriginalGaussFrickeBaseMap N hN p hpN)
    (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)) (lpsOriginalGaussFrickeBaseMap_levelRoot N hN p hpN)
lemma lpsOriginalGaussFrickeOrderMap_root
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    lpsOriginalGaussFrickeOrderMap N hN p hpN (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)) =
      AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X) :=
  AdjoinRoot.lift_root _
lemma lpsOriginalGaussFrickeOrderMap_base
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (x : LPSOriginalGaussBase p) :
    lpsOriginalGaussFrickeOrderMap N hN p hpN
      (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p) x) =
        lpsOriginalGaussFrickeBaseMap N hN p hpN x :=
  AdjoinRoot.lift_of _
lemma lpsOriginalGaussFrickeOrderMap_j
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    lpsOriginalGaussFrickeOrderMap N hN p hpN (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)) = AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p) := by
  rw [lpsOriginalGaussFrickeOrderMap_base,
    lpsOriginalGaussFrickeBaseMap_integer, Polynomial.eval₂_X]
lemma lpsOriginalGaussFrickeOrderMap_squared
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    (lpsOriginalGaussFrickeOrderMap N hN p hpN).comp
      (lpsOriginalGaussFrickeOrderMap N hN p hpN) =
        RingHom.id (LPSOriginalGaussAffineOrder N hN p) := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  apply AdjoinRoot.ringHom_ext
  · apply IsLocalization.ringHom_ext (lpsOriginalGaussPrime p).primeCompl
    apply Polynomial.ringHom_ext
    · intro z
      simp
    · change lpsOriginalGaussFrickeOrderMap N hN p hpN
        (lpsOriginalGaussFrickeOrderMap N hN p hpN (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X))) = AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)
      rw [lpsOriginalGaussFrickeOrderMap_j, lpsOriginalGaussFrickeOrderMap_root]
  · change lpsOriginalGaussFrickeOrderMap N hN p hpN
      (lpsOriginalGaussFrickeOrderMap N hN p hpN (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))) = AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)
    rw [lpsOriginalGaussFrickeOrderMap_root, lpsOriginalGaussFrickeOrderMap_j]
def lpsOriginalGaussFrickeRingEquiv
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    LPSOriginalGaussAffineOrder N hN p ≃+* LPSOriginalGaussAffineOrder N hN p := by
  have h : Function.Involutive (lpsOriginalGaussFrickeOrderMap N hN p hpN) := by
    intro x
    exact congrArg (fun f : LPSOriginalGaussAffineOrder N hN p →+* LPSOriginalGaussAffineOrder N hN p => f x)
      (lpsOriginalGaussFrickeOrderMap_squared N hN p hpN)
  exact RingEquiv.ofBijective (lpsOriginalGaussFrickeOrderMap N hN p hpN) h.bijective
end
end QEC.Coding.TannerLiftedProduct


