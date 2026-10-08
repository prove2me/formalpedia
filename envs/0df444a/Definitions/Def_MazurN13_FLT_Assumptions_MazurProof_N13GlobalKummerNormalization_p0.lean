-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GlobalKummerNormalization_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GlobalKummerNormalization_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:21:15.531831+00:00
-- url     : https://prove2.me/theorems/37a3e957-2a4f-4b48-8689-0e0f48958388
-- title:
--   FLT.Assumptions.MazurProof.N13GlobalKummerNormalization source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GlobalKummerNormalization

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GlobalKummerNormalization
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianFieldEquiv_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13LowDegreeKummerHom_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerNorm_p0
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

set_option autoImplicit false




/-!
# Global primitive normalization of N13 Kummer values

A rational Mumford polynomial need not have integral coefficients.  We clear
all denominators simultaneously over `ℤ`, remove the polynomial content, and
evaluate the resulting primitive polynomial at the integral Gaussian-cubic
generator `α + 9`.

The resulting element lies in the actual absolute ring of integers and
differs from the original Kummer value by one nonzero rational scalar.
Primitivity and the degree bound are retained, and the norm of the integral
representative remains a rational square.  Thus denominator clearing is
separated cleanly from the subsequent ideal factorization.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13GlobalKummerNormalization

noncomputable section

open N13GaussianFieldEquiv

abbrev L := N13GaussianCubicField.L

local instance fieldL : Field L :=
  N13GaussianCubicField.cubicField

local instance intNormalizationMonoid :
    StrongNormalizationMonoid ℤ :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

local instance intNormalizedGCDMonoid :
    NormalizedGCDMonoid ℤ :=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid ℤ

/-- Clear all rational denominators. -/
def integralNormalization (p : ℚ[X]) : ℤ[X] :=
  IsLocalization.integerNormalization
    (nonZeroDivisors ℤ) p

/-- The primitive integral representative of a rational polynomial,
well-defined up to sign. -/
def primitiveNormalization (p : ℚ[X]) : ℤ[X] :=
  (integralNormalization p).primPart

theorem integralNormalization_ne_zero
    {p : ℚ[X]} (hp : p ≠ 0) :
    integralNormalization p ≠ 0 := by
  exact
    (IsFractionRing.integerNormalization_eq_zero_iff
      (A := ℤ) (K := ℚ)).not.mpr hp

theorem integralNormalization_content_ne_zero
    {p : ℚ[X]} (hp : p ≠ 0) :
    (integralNormalization p).content ≠ 0 := by
  exact
    Polynomial.content_eq_zero_iff.not.mpr
      (integralNormalization_ne_zero hp)

theorem primitiveNormalization_spec
    {p : ℚ[X]} (hp : p ≠ 0) :
    ∃ c : ℚ, c ≠ 0 ∧
      (primitiveNormalization p).map
          (algebraMap ℤ ℚ) =
        C c * p := by
  let U₀ : ℤ[X] := integralNormalization p
  let U : ℤ[X] := primitiveNormalization p
  obtain ⟨b, hb, hclear⟩ :=
    IsLocalization.integerNormalization_spec
      (nonZeroDivisors ℤ) p
  have hb0 : b ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbc :
      algebraMap ℤ ℚ b ≠ 0 :=
    (IsFractionRing.injective ℤ ℚ).ne hb0
  have hcontent :
      algebraMap ℤ ℚ U₀.content ≠ 0 :=
    (IsFractionRing.injective ℤ ℚ).ne
      (integralNormalization_content_ne_zero hp)
  let c : ℚ :=
    (algebraMap ℤ ℚ U₀.content)⁻¹ *
      algebraMap ℤ ℚ b
  refine
    ⟨c, mul_ne_zero (inv_ne_zero hcontent) hbc, ?_⟩
  have hdecomp :
      U₀.map (algebraMap ℤ ℚ) =
        C (algebraMap ℤ ℚ U₀.content) *
          U.map (algebraMap ℤ ℚ) := by
    simpa only [U₀, U, integralNormalization,
      primitiveNormalization, Polynomial.map_mul,
      Polynomial.map_C] using
      congrArg (Polynomial.map (algebraMap ℤ ℚ))
        U₀.eq_C_content_mul_primPart
  have hcleared :
      U₀.map (algebraMap ℤ ℚ) =
        C (algebraMap ℤ ℚ b) * p := by
    simpa only [U₀, integralNormalization,
      Algebra.smul_def, Polynomial.algebraMap_apply] using
      hclear
  calc
    U.map (algebraMap ℤ ℚ) =
        1 * U.map (algebraMap ℤ ℚ) := by rw [one_mul]
    _ =
        (C (algebraMap ℤ ℚ U₀.content)⁻¹ *
            C (algebraMap ℤ ℚ U₀.content)) *
          U.map (algebraMap ℤ ℚ) := by
      rw [← C_mul, inv_mul_cancel₀ hcontent,
        C_1, one_mul]
    _ =
        C (algebraMap ℤ ℚ U₀.content)⁻¹ *
          (C (algebraMap ℤ ℚ U₀.content) *
            U.map (algebraMap ℤ ℚ)) := by ring
    _ =
        C (algebraMap ℤ ℚ U₀.content)⁻¹ *
          (C (algebraMap ℤ ℚ b) * p) := by
      rw [← hdecomp, hcleared]
    _ =
        (C (algebraMap ℤ ℚ U₀.content)⁻¹ *
          C (algebraMap ℤ ℚ b)) * p := by ring
    _ = C c * p := by rw [← C_mul]

theorem primitiveNormalization_natDegree_le
    {p : ℚ[X]} (hdeg : p.natDegree ≤ 2) :
    (primitiveNormalization p).natDegree ≤ 2 := by
  rw [primitiveNormalization,
    Polynomial.natDegree_primPart]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_contra hcoeff
  have hnU :
      n ∈ (integralNormalization p).support :=
    Polynomial.mem_support_iff.mpr hcoeff
  have hnp :
      n ∈ p.support :=
    IsLocalization.integerNormalization_support
      (nonZeroDivisors ℤ) p hnU
  have hnle :
      n ≤ 2 :=
    (Polynomial.le_natDegree_of_mem_supp n hnp).trans
      hdeg
  omega

theorem primitiveNormalization_isPrimitive
    (p : ℚ[X]) :
    (primitiveNormalization p).IsPrimitive :=
  (integralNormalization p).isPrimitive_primPart

/-- The integral point corresponding to the sextic generator. -/
def integralTheta : integralClosure ℤ L :=
  ⟨gaussianTheta, gaussianTheta_integral⟩

/-- Evaluate an integral polynomial inside the actual absolute ring of
integers. -/
def integralEval (U : ℤ[X]) :
    integralClosure ℤ L :=
  aeval integralTheta U

@[simp] theorem coe_integralEval (U : ℤ[X]) :
    ((integralEval U : integralClosure ℤ L) : L) =
      eval₂ (algebraMap ℤ L) gaussianTheta U := by
  change
    (Subalgebra.val (integralClosure ℤ L))
        (eval₂
          (algebraMap ℤ (integralClosure ℤ L))
          integralTheta U) =
      eval₂ (algebraMap ℤ L) gaussianTheta U
  have h :=
    Polynomial.hom_eval₂ U
      (algebraMap ℤ (integralClosure ℤ L))
      (Subalgebra.val (integralClosure ℤ L)).toRingHom
      integralTheta
  have hmaps :
      (Subalgebra.val
          (integralClosure ℤ L)).toRingHom.comp
          (algebraMap ℤ (integralClosure ℤ L)) =
        algebraMap ℤ L :=
    RingHom.ext_int _ _
  calc
    (Subalgebra.val (integralClosure ℤ L))
        (eval₂
          (algebraMap ℤ (integralClosure ℤ L))
          integralTheta U) =
        eval₂
          ((Subalgebra.val
              (integralClosure ℤ L)).toRingHom.comp
            (algebraMap ℤ (integralClosure ℤ L)))
          ((Subalgebra.val
            (integralClosure ℤ L)) integralTheta) U :=
      h
    _ =
        eval₂ (algebraMap ℤ L) gaussianTheta U := by
      rw [hmaps]
      rfl

theorem integralEval_primitiveNormalization_spec
    {p : ℚ[X]} (hp : p ≠ 0) :
    ∃ c : ℚ, c ≠ 0 ∧
      ((integralEval (primitiveNormalization p) :
          integralClosure ℤ L) : L) =
        algebraMap ℚ L c *
          eval₂ (algebraMap ℚ L) gaussianTheta p := by
  obtain ⟨c, hc, hpoly⟩ :=
    primitiveNormalization_spec hp
  refine ⟨c, hc, ?_⟩
  calc
    ((integralEval (primitiveNormalization p) :
        integralClosure ℤ L) : L) =
        eval₂ (algebraMap ℤ L) gaussianTheta
          (primitiveNormalization p) := by
      rw [coe_integralEval]
    _ =
        eval₂ (algebraMap ℚ L) gaussianTheta
          ((primitiveNormalization p).map
            (algebraMap ℤ ℚ)) := by
      rw [Polynomial.eval₂_map,
        IsScalarTower.algebraMap_eq ℤ ℚ L]
    _ =
        eval₂ (algebraMap ℚ L) gaussianTheta
          (C c * p) := by rw [hpoly]
    _ =
        algebraMap ℚ L c *
          eval₂ (algebraMap ℚ L) gaussianTheta p := by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C]

/-- The global integral representative of a low-degree Kummer value. -/
def normalizedKummerInteger
    (D : N13LowDegreeKummerHom.LowRep) :
    integralClosure ℤ L :=
  integralEval
    (primitiveNormalization D.toSemi.u)

theorem normalizedKummerInteger_spec
    (D : N13LowDegreeKummerHom.LowRep) :
    ∃ c : ℚ, c ≠ 0 ∧
      ((normalizedKummerInteger D :
          integralClosure ℤ L) : L) =
        algebraMap ℚ L c *
          sexticEquivGaussian
            (N13MumfordKummerValue.uTheta
              (N13LowDegreeKummerHom.asMumford D)) := by
  have hu : D.toSemi.u ≠ 0 :=
    D.toSemi.u_monic.ne_zero
  obtain ⟨c, hc, hspec⟩ :=
    integralEval_primitiveNormalization_spec hu
  refine ⟨c, hc, ?_⟩
  rw [normalizedKummerInteger]
  rw [N13MumfordKummerValue.uTheta_eq_mk]
  change
    ((integralEval
        (primitiveNormalization D.toSemi.u) :
        integralClosure ℤ L) : L) =
      algebraMap ℚ L c *
        sexticEquivGaussian
          (N13SexticSquareclass.ofPoly D.toSemi.u)
  rw [sexticEquivGaussian_ofPoly]
  exact hspec

theorem normalizedKummerInteger_degree
    (D : N13LowDegreeKummerHom.LowRep) :
    (primitiveNormalization D.toSemi.u).natDegree ≤ 2 :=
  primitiveNormalization_natDegree_le D.degree_le_two

/-- The integral representative retains the square-norm condition; its
square root is simply rescaled by the cube of the rational normalization
factor. -/
theorem normalizedKummerInteger_norm_isSquare
    (D : N13LowDegreeKummerHom.LowRep) :
    ∃ s : ℚ,
      Algebra.norm ℚ
          (((normalizedKummerInteger D :
              integralClosure ℤ L) : L)) =
        s ^ 2 := by
  obtain ⟨c, hc, hspec⟩ :=
    normalizedKummerInteger_spec D
  refine
    ⟨c ^ 3 * N13MumfordKummerNorm.normRoot D, ?_⟩
  have hnorm :
      Algebra.norm ℚ
          (N13MumfordKummerValue.uTheta
            (N13LowDegreeKummerHom.asMumford D)) =
        N13MumfordKummerNorm.normRoot D ^ 2 :=
    N13MumfordKummerNorm.norm_uTheta_eq_normRoot_sq D
  have hnormGaussian :
      Algebra.norm ℚ
          (N13GaussianFieldEquiv.sexticEquivGaussian
            (N13MumfordKummerValue.uTheta
              (N13LowDegreeKummerHom.asMumford D))) =
        N13MumfordKummerNorm.normRoot D ^ 2 := by
    calc
      Algebra.norm ℚ
          (N13GaussianFieldEquiv.sexticEquivGaussian
            (N13MumfordKummerValue.uTheta
              (N13LowDegreeKummerHom.asMumford D))) =
          Algebra.norm ℚ
            (N13MumfordKummerValue.uTheta
              (N13LowDegreeKummerHom.asMumford D)) :=
        Algebra.norm_eq_of_algEquiv
          N13GaussianFieldEquiv.sexticEquivGaussian _
      _ = _ := hnorm
  rw [hspec, map_mul, Algebra.norm_algebraMap,
    N13GaussianFieldEquiv.finrank_Lg,
    hnormGaussian]
  ring

end

end MazurProof.N13GlobalKummerNormalization


