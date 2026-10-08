-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianFieldEquiv_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianFieldEquiv_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:12:59.169986+00:00
-- url     : https://prove2.me/theorems/03741d2d-98da-46ff-b323-5fe4a549c6a7
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianFieldEquiv source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianFieldEquiv

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianFieldEquiv
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianCubicField_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianFractionField_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianCubic_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SexticIrreducible_p0

set_option autoImplicit false




/-!
# Equivalence of the sextic and Gaussian-cubic N13 fields

The root `α` of the translated Gaussian cubic gives

`θ = α + 9`.

This file proves that sending the sextic generator to this element is an
isomorphism from the original degree-six algebra to the Gaussian cubic
number field.  Equal absolute dimensions make the injective field map
surjective; no inverse polynomial is searched for.

The intrinsic order-four element of the sextic field maps to the Gaussian
unit `i`.  Consequently the short formulas for the descent generators show
directly that all of them are algebraic integers in the structural absolute
ring of integers.
-/

open Algebra Module Polynomial

namespace MazurProof.N13GaussianFieldEquiv

noncomputable section

open N13GaussianGlobalArithmetic

abbrev K := N13GaussianCubicField.K
abbrev Lg := N13GaussianCubicField.L
abbrev Ls := N13SexticSquareclass.SexticAlgebra

local instance fieldLg : Field Lg :=
  N13GaussianCubicField.cubicField

local instance fieldLs : Field Ls :=
  N13SexticIrreducible.sexticAlgebraField

local instance finiteKL : Module.Finite K Lg :=
  N13GaussianCubicField.powerBasis.finite

local instance finiteQL : Module.Finite ℚ Lg :=
  Module.Finite.trans K Lg

def gaussianI : Lg :=
  algebraMap K Lg
    (algebraMap GI K N13GaussianGlobalArithmetic.i)

def gaussianTheta : Lg :=
  N13GaussianCubicField.alpha + 9

@[simp] theorem gaussianI_sq :
    gaussianI ^ 2 = -1 := by
  change
    (algebraMap K Lg
      (algebraMap GI K N13GaussianGlobalArithmetic.i)) ^ 2 = -1
  rw [← map_pow, ← map_pow,
    N13GaussianGlobalArithmetic.i_sq, map_neg, map_one,
    map_neg, map_one]

theorem alpha_root_h :
    eval₂ (algebraMap GI Lg)
      N13GaussianCubicField.alpha
      N13GaussianGlobalArithmetic.h = 0 := by
  have hmap :
      algebraMap GI Lg =
        (algebraMap K Lg).comp (algebraMap GI K) :=
    IsScalarTower.algebraMap_eq GI K Lg
  rw [hmap, ← Polynomial.eval₂_map]
  exact AdjoinRoot.eval₂_root N13GaussianCubicField.hK

theorem gaussianTheta_root_g :
    eval₂ (algebraMap GI Lg) gaussianTheta
      N13GaussianGlobalArithmetic.g = 0 := by
  have h := alpha_root_h
  rw [N13GaussianGlobalArithmetic.h,
    Polynomial.eval₂_comp] at h
  simpa only [gaussianTheta, eval₂_add, eval₂_X,
    eval₂_ofNat, map_ofNat] using h

theorem gaussianTheta_root_n13F :
    eval₂ (algebraMap GI Lg) gaussianTheta
      N13GaussianGlobalArithmetic.n13F = 0 := by
  rw [← N13GaussianGlobalArithmetic.g_mul_conj,
    Polynomial.eval₂_mul, gaussianTheta_root_g, zero_mul]

theorem gaussianTheta_root_sextic :
    eval₂ (algebraMap ℚ Lg) gaussianTheta
      N13SexticSquareclass.f = 0 := by
  simpa [N13SexticSquareclass.f, N13Mumford.f,
    N13GaussianGlobalArithmetic.n13F] using
    gaussianTheta_root_n13F

def sexticToGaussian : Ls →ₐ[ℚ] Lg :=
  AdjoinRoot.liftAlgHom
    N13SexticSquareclass.f
    (Algebra.ofId ℚ Lg)
    gaussianTheta
    gaussianTheta_root_sextic

@[simp] theorem sexticToGaussian_theta :
    sexticToGaussian N13GaussianCubic.theta =
      gaussianTheta :=
  AdjoinRoot.liftAlgHom_root
    N13SexticSquareclass.f
    (Algebra.ofId ℚ Lg)
    gaussianTheta
    gaussianTheta_root_sextic

theorem finrank_Ls :
    Module.finrank ℚ Ls = 6 := by
  change
    Module.finrank ℚ
      (AdjoinRoot N13SexticSquareclass.f) = 6
  rw [(AdjoinRoot.powerBasis
    (by
      simpa [N13SexticSquareclass.f] using
        (N13Mumford.f_monic (K := ℚ)).ne_zero)).finrank]
  change N13SexticSquareclass.f.natDegree = 6
  simpa [N13SexticSquareclass.f] using
    (N13Mumford.f_natDegree (K := ℚ))

theorem finrank_Lg :
    Module.finrank ℚ Lg = 6 := by
  calc
    Module.finrank ℚ Lg =
        Module.finrank ℚ K * Module.finrank K Lg :=
      (Module.finrank_mul_finrank ℚ K Lg).symm
    _ = 2 * 3 := by
      rw [N13GaussianFractionField.finrank_K]
      congr 1
      rw [Module.finrank_eq_card_basis
        N13GaussianCubicField.powerBasis.basis]
      simp [N13GaussianCubicField.powerBasis_dim]
    _ = 6 := by norm_num

theorem sexticToGaussian_bijective :
    Function.Bijective sexticToGaussian := by
  constructor
  · exact sexticToGaussian.injective
  · apply
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := sexticToGaussian.toLinearMap) ?_).mp
    · exact sexticToGaussian.injective
    · rw [finrank_Ls, finrank_Lg]

def sexticEquivGaussian : Ls ≃ₐ[ℚ] Lg :=
  AlgEquiv.ofBijective sexticToGaussian
    sexticToGaussian_bijective

@[simp] theorem sexticEquivGaussian_theta :
    sexticEquivGaussian N13GaussianCubic.theta =
      gaussianTheta :=
  sexticToGaussian_theta

@[simp] theorem sexticEquivGaussian_ofPoly
    (p : ℚ[X]) :
    sexticEquivGaussian
        (N13SexticSquareclass.ofPoly p) =
      eval₂ (algebraMap ℚ Lg) gaussianTheta p := by
  change
    sexticToGaussian
        (AdjoinRoot.mk N13SexticSquareclass.f p) =
      eval₂ (algebraMap ℚ Lg) gaussianTheta p
  exact AdjoinRoot.liftAlgHom_mk
    N13SexticSquareclass.f
    (Algebra.ofId ℚ Lg)
    gaussianTheta
    gaussianTheta_root_sextic p

theorem gaussianTheta_gaussian_cubic :
    gaussianTheta ^ 3 + 2 * gaussianTheta ^ 2 -
        gaussianTheta - 1 -
      gaussianI * (2 * gaussianTheta * (gaussianTheta + 1)) = 0 := by
  have hi :
      algebraMap GI Lg N13GaussianGlobalArithmetic.i =
        gaussianI := by
    rw [gaussianI,
      IsScalarTower.algebraMap_apply GI K Lg]
  have hg :
      gaussianTheta ^ 3 +
          (2 - 2 * gaussianI) * gaussianTheta ^ 2 +
          (-1 - 2 * gaussianI) * gaussianTheta - 1 = 0 := by
    simpa [N13GaussianGlobalArithmetic.g, hi,
      map_add, map_sub, map_mul, map_neg, map_one,
      map_ofNat] using gaussianTheta_root_g
  linear_combination hg

theorem gaussianTheta_mul_inverse :
    gaussianTheta *
        (gaussianTheta ^ 2 +
          (2 - 2 * gaussianI) * gaussianTheta +
          (-1 - 2 * gaussianI)) = 1 := by
  linear_combination gaussianTheta_gaussian_cubic

theorem gaussianTheta_isUnit :
    IsUnit gaussianTheta :=
  isUnit_iff_exists_inv.mpr
    ⟨gaussianTheta ^ 2 +
      (2 - 2 * gaussianI) * gaussianTheta +
      (-1 - 2 * gaussianI),
      gaussianTheta_mul_inverse⟩

theorem gaussianTheta_add_one_mul_inverse :
    (gaussianTheta + 1) *
        (-(gaussianTheta ^ 2 +
          (1 - 2 * gaussianI) * gaussianTheta - 2)) = 1 := by
  linear_combination -gaussianTheta_gaussian_cubic

theorem gaussianTheta_add_one_isUnit :
    IsUnit (gaussianTheta + 1) :=
  isUnit_iff_exists_inv.mpr
    ⟨-(gaussianTheta ^ 2 +
        (1 - 2 * gaussianI) * gaussianTheta - 2),
      gaussianTheta_add_one_mul_inverse⟩

theorem gaussianCubicImaginaryFactor_isUnit :
    IsUnit (2 * gaussianTheta * (gaussianTheta + 1)) :=
  ((isUnit_iff_ne_zero.mpr
      (by
        intro htwo
        have htwoK : (2 : K) = 0 :=
          (algebraMap K Lg).injective (by
            simpa only [map_ofNat, map_zero] using htwo)
        norm_num at htwoK)).mul
    gaussianTheta_isUnit).mul gaussianTheta_add_one_isUnit

@[simp] theorem sexticEquivGaussian_zeta :
    sexticEquivGaussian N13SexticSquareclass.zeta =
      gaussianI := by
  let zI : Lg :=
    sexticEquivGaussian N13SexticSquareclass.zeta
  let Bθ : Lg :=
    2 * gaussianTheta * (gaussianTheta + 1)
  have hz :
      gaussianTheta ^ 3 + 2 * gaussianTheta ^ 2 -
          gaussianTheta - 1 - zI * Bθ = 0 := by
    simpa only [map_add, map_sub, map_mul, map_pow,
      map_ofNat, map_one, map_zero, sexticEquivGaussian_theta]
      using
        congrArg sexticEquivGaussian
          N13GaussianCubic.gaussian_cubic
  have hi :
      gaussianTheta ^ 3 + 2 * gaussianTheta ^ 2 -
          gaussianTheta - 1 - gaussianI * Bθ = 0 := by
    simpa only [Bθ] using gaussianTheta_gaussian_cubic
  apply gaussianCubicImaginaryFactor_isUnit.mul_right_cancel
  calc
    zI * Bθ =
        gaussianTheta ^ 3 + 2 * gaussianTheta ^ 2 -
          gaussianTheta - 1 :=
      (sub_eq_zero.mp hz).symm
    _ = gaussianI * Bθ :=
      sub_eq_zero.mp hi

@[simp] theorem sexticEquivGaussian_e1 :
    sexticEquivGaussian N13SexticSquareclass.e1 =
      1 - gaussianTheta ^ 2 +
        (gaussianI - 1) * gaussianTheta := by
  simpa only [map_add, map_sub, map_mul, map_pow,
    map_one, sexticEquivGaussian_theta,
    sexticEquivGaussian_zeta] using
    congrArg sexticEquivGaussian
      N13GaussianCubic.e1_short

@[simp] theorem sexticEquivGaussian_e2 :
    sexticEquivGaussian N13SexticSquareclass.e2 =
      1 + gaussianI * gaussianTheta ^ 2 +
        (1 + 2 * gaussianI) * gaussianTheta := by
  simpa only [map_add, map_mul, map_pow, map_ofNat,
    map_one, sexticEquivGaussian_theta,
    sexticEquivGaussian_zeta] using
    congrArg sexticEquivGaussian
      N13GaussianCubic.e2_short

@[simp] theorem sexticEquivGaussian_primeA :
    sexticEquivGaussian N13SexticSquareclass.primeA =
      1 - gaussianI * gaussianTheta ^ 2 -
        (1 + gaussianI) * gaussianTheta := by
  simpa only [map_add, map_sub, map_mul, map_pow,
    map_one, sexticEquivGaussian_theta,
    sexticEquivGaussian_zeta] using
    congrArg sexticEquivGaussian
      N13GaussianCubic.primeA_short

@[simp] theorem sexticEquivGaussian_primeQ :
    sexticEquivGaussian N13SexticSquareclass.primeQ =
      2 - 3 * gaussianI := by
  simpa only [map_sub, map_mul, map_ofNat,
    sexticEquivGaussian_zeta] using
    congrArg sexticEquivGaussian
      N13GaussianCubic.primeQ_short

/-! ## Integrality of the structural generators -/

theorem gaussianI_integral :
    IsIntegral ℤ gaussianI := by
  have hi :
      IsIntegral ℤ
        (algebraMap GI Lg
          N13GaussianGlobalArithmetic.i) :=
    N13GaussianFractionField.i_integral.algebraMap
  simpa only [gaussianI,
    IsScalarTower.algebraMap_apply GI K Lg] using hi

private theorem lg_natCast_integral (n : ℕ) :
    IsIntegral ℤ (n : Lg) := by
  have h :
      IsIntegral ℤ
        (algebraMap ℤ Lg (n : ℤ)) :=
    isIntegral_algebraMap
  rw [map_natCast (algebraMap ℤ Lg) n] at h
  exact h

theorem gaussianTheta_integral :
    IsIntegral ℤ gaussianTheta := by
  have ha :
      IsIntegral ℤ N13GaussianCubicField.alpha :=
    isIntegral_trans
      N13GaussianCubicField.alpha
      N13GaussianCubicField.alpha_integral
  exact ha.add (lg_natCast_integral 9)

theorem sexticEquivGaussian_zeta_integral :
    IsIntegral ℤ
      (sexticEquivGaussian
        N13SexticSquareclass.zeta) := by
  rw [sexticEquivGaussian_zeta]
  exact gaussianI_integral

theorem sexticEquivGaussian_e1_integral :
    IsIntegral ℤ
      (sexticEquivGaussian
        N13SexticSquareclass.e1) := by
  rw [sexticEquivGaussian_e1]
  exact
    (isIntegral_one.sub
      (gaussianTheta_integral.pow 2)).add
      ((gaussianI_integral.sub isIntegral_one).mul
        gaussianTheta_integral)

theorem sexticEquivGaussian_e2_integral :
    IsIntegral ℤ
      (sexticEquivGaussian
        N13SexticSquareclass.e2) := by
  rw [sexticEquivGaussian_e2]
  exact
    (isIntegral_one.add
      (gaussianI_integral.mul
        (gaussianTheta_integral.pow 2))).add
      ((isIntegral_one.add
        ((lg_natCast_integral 2).mul
          gaussianI_integral)).mul
        gaussianTheta_integral)

theorem sexticEquivGaussian_primeA_integral :
    IsIntegral ℤ
      (sexticEquivGaussian
        N13SexticSquareclass.primeA) := by
  rw [sexticEquivGaussian_primeA]
  exact
    (isIntegral_one.sub
      (gaussianI_integral.mul
        (gaussianTheta_integral.pow 2))).sub
      ((isIntegral_one.add gaussianI_integral).mul
        gaussianTheta_integral)

theorem sexticEquivGaussian_primeQ_integral :
    IsIntegral ℤ
      (sexticEquivGaussian
        N13SexticSquareclass.primeQ) := by
  rw [sexticEquivGaussian_primeQ]
  exact
    (lg_natCast_integral 2).sub
      ((lg_natCast_integral 3).mul
        gaussianI_integral)

end

end MazurProof.N13GaussianFieldEquiv


