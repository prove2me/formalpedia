-- Prove2me | Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebraCore
-- name    : LowRankUnivariateSOS_UnivariateAlgebraCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:58:10.628954+00:00
-- url     : https://prove2.me/theorems/427bbcd2-2876-45a2-af71-e7f11cd07d76
-- title:
--   Univariate Algebra Core
-- statement:
--   Definitions and structural lemmas for Univariate Algebra Core, from Chenyang Yuan (yuanchenyang/lean_low_rank_univariate_sos; formalizing Legat, Yuan, and Parrilo, SIAM J. Optim. 2023; see pinned Apache-2.0 LICENSE and README.md)'s pinned Low-rank univariate sum of squares has no spurious second-order critical points (rank 2) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/UnivariateAlgebraCore.lean

import Definitions.Def_LowRankUnivariateSOS_H1Case
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.EuclideanDomain
import Theorems.Thm_LowRankUnivariateSOS_A_scalePair_left
import Theorems.Thm_LowRankUnivariateSOS_A_smul_right
import Theorems.Thm_LowRankUnivariateSOS_UPair_ext
import Theorems.Thm_LowRankUnivariateSOS_perpPair_fst
import Theorems.Thm_LowRankUnivariateSOS_perpPair_snd
import Theorems.Thm_LowRankUnivariateSOS_scalePair_fst
import Theorems.Thm_LowRankUnivariateSOS_scalePair_snd
import Theorems.Thm_LowRankUnivariateSOS_sigma2_perpPair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_scalePair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_smul
import Theorems.Thm_LowRankUnivariateSOS_smul_fst
import Theorems.Thm_LowRankUnivariateSOS_smul_snd
attribute [local simp] LowRankUnivariateSOS.A_scalePair_left
attribute [local simp] LowRankUnivariateSOS.A_smul_right
attribute [local simp] LowRankUnivariateSOS.perpPair_fst
attribute [local simp] LowRankUnivariateSOS.perpPair_snd
attribute [local simp] LowRankUnivariateSOS.scalePair_fst
attribute [local simp] LowRankUnivariateSOS.scalePair_snd
attribute [local simp] LowRankUnivariateSOS.sigma2_perpPair
attribute [local simp] LowRankUnivariateSOS.sigma2_scalePair
attribute [local simp] LowRankUnivariateSOS.sigma2_smul
attribute [local simp] LowRankUnivariateSOS.smul_fst
attribute [local simp] LowRankUnivariateSOS.smul_snd


set_option autoImplicit true
noncomputable section
namespace LowRankUnivariateSOS
structure ReducedFactorization (u : UPair) where
  a : Poly
  u0 : UPair
  eq_scale : u = scalePair a u0
  reduced_coprime : IsCoprime u0.fst u0.snd
def SigmaReducedNoRealRoots (u0 : UPair) : Prop :=
  ∀ x : ℝ, ¬ Polynomial.IsRoot (sigma2 u0) x
def gcd_sigma_decomposition
    (u : UPair) :
    ReducedFactorization u := by
  by_cases hsnd : u.snd = 0
  · refine
      { a := u.fst
        u0 := ⟨1, 0⟩
        eq_scale := ?_
        reduced_coprime := ?_ }
    · apply UPair.ext <;> simp [scalePair, hsnd]
    · simpa using (isCoprime_one_left : IsCoprime (1 : Poly) 0)
  · refine
      { a := gcd u.fst u.snd
        u0 := ⟨u.fst / gcd u.fst u.snd, u.snd / gcd u.fst u.snd⟩
        eq_scale := ?_
        reduced_coprime := ?_ }
    · apply UPair.ext
      · simpa [scalePair] using
          (EuclideanDomain.mul_div_cancel'
            (gcd_ne_zero_of_right hsnd) (gcd_dvd_left u.fst u.snd)).symm
      · simpa [scalePair] using
          (EuclideanDomain.mul_div_cancel'
            (gcd_ne_zero_of_right hsnd) (gcd_dvd_right u.fst u.snd)).symm
    · simpa using (isCoprime_div_gcd_div_gcd hsnd :
          IsCoprime (u.fst / gcd u.fst u.snd) (u.snd / gcd u.fst u.snd))
end LowRankUnivariateSOS


