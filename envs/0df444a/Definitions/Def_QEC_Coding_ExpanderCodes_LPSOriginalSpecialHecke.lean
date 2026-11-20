-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialHecke
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalSpecialHecke
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T09:04:57.268966+00:00
-- url     : https://prove2.me/theorems/0d50c63c-af25-4933-aa71-a1937e95f740
-- title:
--   LPSOriginal Special Hecke
-- statement:
--   Definitions and structural lemmas for LPSOriginal Special Hecke, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialHecke.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedForgetLevel_toSpecZ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedFricke_overSpecZ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedSecondLevelMap_overSpecZ
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
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section
def lpsOriginalSpecialFibreLift (l N M : ℕ) [Fact l.Prime]
    (hN : 0 < N) (hM : 0 < M)
    (a : lpsOriginalIntegerNormalGluedScheme M hM ⟶ lpsOriginalIntegerNormalGluedScheme N hN)
    (ha : a ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN =
      lpsOriginalIntegerNormalGluedToSpecZ M hM) :
    lpsOriginalSpecialFibre l M hM ⟶ lpsOriginalSpecialFibre l N hN :=
  pullback.lift
    (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ M hM)
      (lpsOriginalPrimeSpecToInteger l) ≫ a)
    (lpsOriginalSpecialFibreToPrimeField l M hM)
    (by
      rw [Category.assoc, ha]
      exact pullback.condition)
lemma lpsOriginalSpecialFibreLift_fst (l N M : ℕ) [Fact l.Prime]
    (hN : 0 < N) (hM : 0 < M)
    (a : lpsOriginalIntegerNormalGluedScheme M hM ⟶ lpsOriginalIntegerNormalGluedScheme N hN)
    (ha : a ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN =
      lpsOriginalIntegerNormalGluedToSpecZ M hM) :
    lpsOriginalSpecialFibreLift l N M hN hM a ha ≫
      pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger l) =
    pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ M hM) (lpsOriginalPrimeSpecToInteger l) ≫ a :=
  pullback.lift_fst _ _ _
lemma lpsOriginalSpecialFibreLift_overPrimeField (l N M : ℕ) [Fact l.Prime]
    (hN : 0 < N) (hM : 0 < M)
    (a : lpsOriginalIntegerNormalGluedScheme M hM ⟶ lpsOriginalIntegerNormalGluedScheme N hN)
    (ha : a ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN =
      lpsOriginalIntegerNormalGluedToSpecZ M hM) :
    lpsOriginalSpecialFibreLift l N M hN hM a ha ≫
      lpsOriginalSpecialFibreToPrimeField l N hN =
    lpsOriginalSpecialFibreToPrimeField l M hM :=
  pullback.lift_snd _ _ _
def lpsOriginalSpecialFibreFricke (l N : ℕ) [Fact l.Prime] [NeZero N] (hN : 0 < N) :
    lpsOriginalSpecialFibre l N hN ⟶ lpsOriginalSpecialFibre l N hN :=
  lpsOriginalSpecialFibreLift l N N hN hN (lpsOriginalIntegerNormalGluedFricke N hN)
    (lpsOriginalIntegerNormalGluedFricke_overSpecZ N hN)
lemma lpsOriginalSpecialFibreFricke_overPrimeField
    (l N : ℕ) [Fact l.Prime] [NeZero N] (hN : 0 < N) :
    lpsOriginalSpecialFibreFricke l N hN ≫ lpsOriginalSpecialFibreToPrimeField l N hN =
      lpsOriginalSpecialFibreToPrimeField l N hN :=
  lpsOriginalSpecialFibreLift_overPrimeField _ _ _ _ _ _ _
lemma lpsOriginalSpecialFibreFricke_involutive
    (l N : ℕ) [Fact l.Prime] [NeZero N] (hN : 0 < N) :
    lpsOriginalSpecialFibreFricke l N hN ≫ lpsOriginalSpecialFibreFricke l N hN =
      𝟙 (lpsOriginalSpecialFibre l N hN) := by
  apply pullback.hom_ext
  · simp only [lpsOriginalSpecialFibreFricke,Category.assoc,lpsOriginalSpecialFibreLift_fst]
    rw [← Category.assoc,lpsOriginalSpecialFibreLift_fst,Category.assoc,
      lpsOriginalIntegerNormalGluedFricke_involutive,Category.comp_id,Category.id_comp]
  · change (lpsOriginalSpecialFibreFricke l N hN ≫ lpsOriginalSpecialFibreFricke l N hN) ≫
      lpsOriginalSpecialFibreToPrimeField l N hN = lpsOriginalSpecialFibreToPrimeField l N hN
    rw [Category.assoc,lpsOriginalSpecialFibreFricke_overPrimeField,
      lpsOriginalSpecialFibreFricke_overPrimeField]
def lpsOriginalSpecialFibreFrickeIso
    (l N : ℕ) [Fact l.Prime] [NeZero N] (hN : 0 < N) :
    lpsOriginalSpecialFibre l N hN ≅ lpsOriginalSpecialFibre l N hN where
  hom := lpsOriginalSpecialFibreFricke l N hN
  inv := lpsOriginalSpecialFibreFricke l N hN
  hom_inv_id := lpsOriginalSpecialFibreFricke_involutive l N hN
  inv_hom_id := lpsOriginalSpecialFibreFricke_involutive l N hN
def lpsOriginalSpecialFibreForgetLevel
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalSpecialFibre l M hM ⟶ lpsOriginalSpecialFibre l N hN :=
  lpsOriginalSpecialFibreLift l N M hN hM
    (lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM)
    (lpsOriginalIntegerNormalGluedForgetLevel_toSpecZ N M hNM h4N hN hM)
lemma lpsOriginalSpecialFibreForgetLevel_overPrimeField
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalSpecialFibreForgetLevel l N M hNM h4N hN hM ≫
      lpsOriginalSpecialFibreToPrimeField l N hN = lpsOriginalSpecialFibreToPrimeField l M hM :=
  lpsOriginalSpecialFibreLift_overPrimeField _ _ _ _ _ _ _
def lpsOriginalSpecialFibreSecondLevelMap
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalSpecialFibre l M hM ⟶ lpsOriginalSpecialFibre l N hN :=
  lpsOriginalSpecialFibreLift l N M hN hM
    (lpsOriginalIntegerNormalGluedSecondLevelMap N M hNM h4N hN hM)
    (lpsOriginalIntegerNormalGluedSecondLevelMap_overSpecZ N M hNM h4N hN hM)
lemma lpsOriginalSpecialFibreSecondLevelMap_overPrimeField
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalSpecialFibreSecondLevelMap l N M hNM h4N hN hM ≫
      lpsOriginalSpecialFibreToPrimeField l N hN = lpsOriginalSpecialFibreToPrimeField l M hM :=
  lpsOriginalSpecialFibreLift_overPrimeField _ _ _ _ _ _ _
def lpsOriginalSpecialFibreHeckePair
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalSpecialFibre l M hM ⟶
      pullback (lpsOriginalSpecialFibreToPrimeField l N hN)
        (lpsOriginalSpecialFibreToPrimeField l N hN) :=
  pullback.lift (lpsOriginalSpecialFibreForgetLevel l N M hNM h4N hN hM)
    (lpsOriginalSpecialFibreSecondLevelMap l N M hNM h4N hN hM)
    ((lpsOriginalSpecialFibreForgetLevel_overPrimeField l N M hNM h4N hN hM).trans
      (lpsOriginalSpecialFibreSecondLevelMap_overPrimeField l N M hNM h4N hN hM).symm)
end
end QEC.Coding.TannerLiftedProduct


