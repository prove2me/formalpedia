-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GlobalKummerIdealSquare_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GlobalKummerIdealSquare_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T23:17:32.239859+00:00
-- url     : https://prove2.me/theorems/fba07589-cd17-4615-a163-552cdd29784b
-- title:
--   FLT.Assumptions.MazurProof.N13GlobalKummerIdealSquare source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GlobalKummerIdealSquare

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GlobalKummerIdealSquare
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GlobalKummerNormalization_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerIdealSquare_p0
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.RingTheory.Localization.Ideal

set_option autoImplicit false




/-!
# The good-locus square ideal of a normalized N13 Kummer value

Primitive normalization removes the arbitrary content of a rational
Mumford polynomial, but it does not make the other polynomial in the
Mumford pair integral.  We clear those remaining denominators
*homogeneously*: if

`f - v² = u w`

and `U = c u` is the primitive integral normalization, then a single
nonzero integer `d` can be chosen together with integral `V,W` so that

`d² f - V² = U W`.

After evaluating at the integral branch point and inverting the derivative
of `d² f`, the branch ideal `(U(θ),V(θ))` squares to `(U(θ))`.  This is the
principal ideal of the previously constructed `normalizedKummerInteger`.
Thus every denominator and bad-reduction prime is isolated in one
canonical localization; no prime factorization or valuation enumeration is
used.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13GlobalKummerIdealSquare

noncomputable section

open N13GaussianFieldEquiv
open N13GlobalKummerNormalization

abbrev L := N13GaussianCubicField.L

local instance fieldL : Field L :=
  N13GaussianCubicField.cubicField

abbrev O := integralClosure ℤ L

/-- Every rational polynomial has a nonzero integral scalar multiple with
integral coefficients. -/
theorem exists_integral_scalar_multiple (p : ℚ[X]) :
    ∃ b : ℤ, b ≠ 0 ∧ ∃ P : ℤ[X],
      P.map (algebraMap ℤ ℚ) =
        C (algebraMap ℤ ℚ b) * p := by
  obtain ⟨b, hb, hP⟩ :=
    IsLocalization.integerNormalization_spec
      (nonZeroDivisors ℤ) p
  exact
    ⟨b, mem_nonZeroDivisors_iff_ne_zero.mp hb,
      IsLocalization.integerNormalization
        (nonZeroDivisors ℤ) p, by
          simpa only [Algebra.smul_def,
            Polynomial.algebraMap_apply] using hP⟩

/-- Integral homogeneous Mumford data whose first polynomial is exactly the
primitive normalization used by `normalizedKummerInteger`. -/
structure ScaledIntegralMumford
    (D : N13LowDegreeKummerHom.LowRep) where
  scale : ℤ
  scale_ne_zero : scale ≠ 0
  v : ℤ[X]
  w : ℤ[X]
  curve :
    C (scale ^ 2) * N13SexticIrreducible.fInt -
        v ^ 2 =
      primitiveNormalization D.toSemi.u * w

/-- Simultaneous denominator clearing preserves the Mumford equation in
homogeneous form. -/
theorem exists_scaledIntegralMumford
    (D : N13LowDegreeKummerHom.LowRep) :
    Nonempty (ScaledIntegralMumford D) := by
  obtain ⟨w, hw⟩ := D.toSemi.curve_dvd
  change
    N13Mumford.f ℚ - D.toSemi.v ^ 2 =
      D.toSemi.u * w at hw
  obtain ⟨c, hc, hU⟩ :=
    primitiveNormalization_spec D.toSemi.u_monic.ne_zero
  obtain ⟨bV, hbV, V₀, hV₀⟩ :=
    exists_integral_scalar_multiple D.toSemi.v
  obtain ⟨bW, hbW, W₀, hW₀⟩ :=
    exists_integral_scalar_multiple (C c⁻¹ * w)
  let d : ℤ := bV * bW
  let V : ℤ[X] := C bW * V₀
  let W : ℤ[X] := (C bV) ^ 2 * C bW * W₀
  have hd : d ≠ 0 :=
    mul_ne_zero hbV hbW
  have hV :
      V.map (algebraMap ℤ ℚ) =
        C (algebraMap ℤ ℚ d) * D.toSemi.v := by
    simp only [V, d, Polynomial.map_mul, Polynomial.map_C,
      hV₀, map_mul]
    ring
  have hW :
      W.map (algebraMap ℤ ℚ) =
        C ((algebraMap ℤ ℚ d) ^ 2 * c⁻¹) * w := by
    simp only [W, d, Polynomial.map_mul, Polynomial.map_C,
      hW₀, map_mul, map_pow]
    rw [Polynomial.map_pow, Polynomial.map_C]
    ring
  refine ⟨⟨d, hd, V, W, ?_⟩⟩
  apply Polynomial.map_injective
    (f := algebraMap ℤ ℚ)
    (IsFractionRing.injective ℤ ℚ)
  simp only [Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, hV, hW, hU,
    map_pow]
  rw [N13SexticIrreducible.fInt_map_rat]
  have hcInv : c * c⁻¹ = 1 :=
    mul_inv_cancel₀ hc
  have hscalar :
      C c * C ((algebraMap ℤ ℚ d) ^ 2 * c⁻¹) =
        C (algebraMap ℤ ℚ d) ^ 2 := by
    rw [← C_mul, ← C_pow]
    congr 1
    calc
      c * ((algebraMap ℤ ℚ d) ^ 2 * c⁻¹) =
          (c * c⁻¹) * (algebraMap ℤ ℚ d) ^ 2 := by ring
      _ = _ := by rw [hcInv, one_mul]
  rw [show
    C (algebraMap ℤ ℚ d) ^ 2 *
          N13Mumford.f ℚ -
        (C (algebraMap ℤ ℚ d) * D.toSemi.v) ^ 2 =
      C (algebraMap ℤ ℚ d) ^ 2 *
        (N13Mumford.f ℚ - D.toSemi.v ^ 2) by ring,
    hw]
  rw [← hscalar]
  ring

/-- A fixed structural choice of the homogeneous integral Mumford data. -/
def scaledIntegralMumford
    (D : N13LowDegreeKummerHom.LowRep) :
    ScaledIntegralMumford D :=
  Classical.choice (exists_scaledIntegralMumford D)

/-- The homogeneously scaled integral curve polynomial. -/
def scaledCurve
    (D : N13LowDegreeKummerHom.LowRep) : ℤ[X] :=
  C ((scaledIntegralMumford D).scale ^ 2) *
    N13SexticIrreducible.fInt

theorem scaledCurve_relation
    (D : N13LowDegreeKummerHom.LowRep) :
    scaledCurve D -
        (scaledIntegralMumford D).v ^ 2 =
      primitiveNormalization D.toSemi.u *
        (scaledIntegralMumford D).w :=
  (scaledIntegralMumford D).curve

/-- The integral branch point is a root of the original sextic. -/
@[simp] theorem integralTheta_root_fInt :
    aeval integralTheta N13SexticIrreducible.fInt = 0 := by
  change
    integralEval N13SexticIrreducible.fInt = 0
  apply Subtype.ext
  have hrat :
      eval₂ (algebraMap ℚ L) gaussianTheta
        (N13SexticIrreducible.fInt.map
          (algebraMap ℤ ℚ)) = 0 := by
    rw [N13SexticIrreducible.fInt_map_rat]
    exact gaussianTheta_root_sextic
  rw [coe_integralEval]
  change
    eval₂ (algebraMap ℤ L) gaussianTheta
      N13SexticIrreducible.fInt = (0 : L)
  simpa only [eval₂_map,
      IsScalarTower.algebraMap_eq ℤ ℚ L] using hrat

/-- The derivative whose nonvanishing defines the good locus for this
normalized representative.  Its two factors are the denominator scale and
the ordinary different generator. -/
def badGenerator
    (D : N13LowDegreeKummerHom.LowRep) : O :=
  integralEval (scaledCurve D).derivative

theorem badGenerator_eq_scale_mul_different
    (D : N13LowDegreeKummerHom.LowRep) :
    badGenerator D =
      algebraMap ℤ O ((scaledIntegralMumford D).scale ^ 2) *
        integralEval N13SexticIrreducible.fInt.derivative := by
  simp only [badGenerator, scaledCurve, derivative_mul,
    derivative_C, zero_mul, zero_add, integralEval, map_mul,
    aeval_C]

theorem differentInteger_ne_zero :
    integralEval
      N13SexticIrreducible.fInt.derivative ≠ 0 := by
  have hrootQ :
      eval₂ (algebraMap ℚ L) gaussianTheta
        (N13Mumford.f ℚ) = 0 := by
    simpa [N13SexticSquareclass.f] using
      gaussianTheta_root_sextic
  have hderivQ :
      eval₂ (algebraMap ℚ L) gaussianTheta
        (N13Mumford.f ℚ).derivative ≠ 0 :=
    (N13Mumford.f_separable ℚ).eval₂_derivative_ne_zero
      (algebraMap ℚ L) hrootQ
  intro hzero
  apply hderivQ
  have hcoe :
      eval₂
          (algebraMap ℤ
            N13GlobalKummerNormalization.L)
          gaussianTheta
        N13SexticIrreducible.fInt.derivative = 0 := by
    calc
      eval₂
          (algebraMap ℤ
            N13GlobalKummerNormalization.L)
          gaussianTheta
          N13SexticIrreducible.fInt.derivative =
        ((integralEval
          N13SexticIrreducible.fInt.derivative : O) :
            N13GlobalKummerNormalization.L) :=
              (coe_integralEval _).symm
      _ = ((0 : O) :
          N13GlobalKummerNormalization.L) := by rw [hzero]
      _ = 0 := by rfl
  have hmaps :
      (algebraMap ℚ L).comp (algebraMap ℤ ℚ) =
        algebraMap ℤ
          N13GlobalKummerNormalization.L :=
    RingHom.ext_int _ _
  calc
    eval₂ (algebraMap ℚ L) gaussianTheta
        (N13Mumford.f ℚ).derivative =
      eval₂ (algebraMap ℚ L) gaussianTheta
        (N13SexticIrreducible.fInt.map
          (algebraMap ℤ ℚ)).derivative := by
            rw [N13SexticIrreducible.fInt_map_rat]
    _ =
      eval₂ (algebraMap ℚ L) gaussianTheta
        (N13SexticIrreducible.fInt.derivative.map
          (algebraMap ℤ ℚ)) := by
            rw [derivative_map]
    _ =
      eval₂
          (algebraMap ℤ
            N13GlobalKummerNormalization.L)
          gaussianTheta
        N13SexticIrreducible.fInt.derivative := by
            rw [eval₂_map, hmaps]
    _ = 0 := hcoe

theorem badGenerator_ne_zero
    (D : N13LowDegreeKummerHom.LowRep) :
    badGenerator D ≠ 0 := by
  rw [badGenerator_eq_scale_mul_different]
  have hOinj :
      Function.Injective (algebraMap ℤ O) := by
    intro a b hab
    have habL :=
      congrArg
        (Subalgebra.val
          (integralClosure ℤ L)).toRingHom hab
    have hmapO :
        (Subalgebra.val
            (integralClosure ℤ L)).toRingHom.comp
            (algebraMap ℤ O) =
          algebraMap ℤ L :=
      RingHom.ext_int _ _
    have habZL :
        algebraMap ℤ L a = algebraMap ℤ L b := by
      rw [← hmapO]
      exact habL
    have hmapZL :
        algebraMap ℤ L =
          (algebraMap ℚ L).comp (algebraMap ℤ ℚ) :=
      RingHom.ext_int _ _
    rw [hmapZL] at habZL
    exact
      (IsFractionRing.injective ℤ ℚ)
        ((algebraMap ℚ L).injective habZL)
  have hscale :
      algebraMap ℤ O
          ((scaledIntegralMumford D).scale ^ 2) ≠ 0 := by
    simpa only [map_zero] using
      hOinj.ne
        (pow_ne_zero 2
          (scaledIntegralMumford D).scale_ne_zero)
  exact mul_ne_zero hscale differentInteger_ne_zero

/-- A prime can meet the excluded locus only through the denominator scale
or the different. -/
theorem mem_scale_or_different_of_badGenerator_mem
    (D : N13LowDegreeKummerHom.LowRep)
    (P : Ideal O) (hP : P.IsPrime)
    (hbad : badGenerator D ∈ P) :
    algebraMap ℤ O (scaledIntegralMumford D).scale ∈ P ∨
      integralEval N13SexticIrreducible.fInt.derivative ∈ P := by
  rw [badGenerator_eq_scale_mul_different] at hbad
  rcases hP.mem_or_mem hbad with hscale | hdifferent
  · left
    rw [map_pow] at hscale
    exact hP.mem_of_pow_mem 2 hscale
  · exact Or.inr hdifferent

/-- The ring obtained by removing exactly the denominator and different
locus attached to a normalized Mumford representative. -/
abbrev GoodOrder
    (D : N13LowDegreeKummerHom.LowRep) : Type :=
  Localization.Away (badGenerator D)

local instance goodOrderIsDomain
    (D : N13LowDegreeKummerHom.LowRep) :
    IsDomain (GoodOrder D) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors
    (GoodOrder D)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (badGenerator_ne_zero D))

/-- The integral branch point in the good-locus order. -/
def goodTheta
    (D : N13LowDegreeKummerHom.LowRep) :
    GoodOrder D :=
  algebraMap O (GoodOrder D) integralTheta

theorem aeval_goodTheta
    (D : N13LowDegreeKummerHom.LowRep)
    (p : ℤ[X]) :
    aeval (goodTheta D) p =
      algebraMap O (GoodOrder D) (integralEval p) := by
  rw [aeval_def]
  change
    eval₂ (algebraMap ℤ (GoodOrder D))
        (algebraMap O (GoodOrder D) integralTheta) p =
      algebraMap O (GoodOrder D)
        (eval₂ (algebraMap ℤ O) integralTheta p)
  have h :=
    (Polynomial.hom_eval₂ p
      (algebraMap ℤ O)
      (algebraMap O (GoodOrder D))
      integralTheta).symm
  simpa only [
    IsScalarTower.algebraMap_eq ℤ O (GoodOrder D)] using h

@[simp] theorem goodTheta_root
    (D : N13LowDegreeKummerHom.LowRep) :
    aeval (goodTheta D) (scaledCurve D) = 0 := by
  rw [aeval_goodTheta]
  have hzero :
      integralEval (scaledCurve D) = 0 := by
    simp only [integralEval, scaledCurve, map_mul,
      aeval_C, integralTheta_root_fInt, mul_zero]
  rw [hzero, map_zero]

theorem goodTheta_derivative_isUnit
    (D : N13LowDegreeKummerHom.LowRep) :
    IsUnit
      (aeval (goodTheta D) (scaledCurve D).derivative) := by
  rw [aeval_goodTheta]
  exact
    IsLocalization.Away.algebraMap_isUnit
      (badGenerator D)

/-- The branch ideal attached to the normalized integral Kummer value on
the good locus. -/
def goodBranchIdeal
    (D : N13LowDegreeKummerHom.LowRep) :
    Ideal (GoodOrder D) :=
  Ideal.span
    ({aeval (goodTheta D)
        (primitiveNormalization D.toSemi.u),
      aeval (goodTheta D)
        (scaledIntegralMumford D).v} :
      Set (GoodOrder D))

theorem good_normalizedKummerInteger
    (D : N13LowDegreeKummerHom.LowRep) :
    aeval (goodTheta D)
        (primitiveNormalization D.toSemi.u) =
      algebraMap O (GoodOrder D)
        (normalizedKummerInteger D) := by
  rw [aeval_goodTheta]
  rfl

/-- The global normalized Kummer value generates a square ideal after
removing its denominator scale and the different. -/
theorem goodBranchIdeal_sq
    (D : N13LowDegreeKummerHom.LowRep) :
    goodBranchIdeal D ^ 2 =
      Ideal.span
        ({algebraMap O (GoodOrder D)
            (normalizedKummerInteger D)} :
          Set (GoodOrder D)) := by
  have h :=
    N13MumfordKummerIdealSquare.mumfordBranchIdeal_sq
      (scaledCurve D)
      (primitiveNormalization D.toSemi.u)
      (scaledIntegralMumford D).v
      (scaledIntegralMumford D).w
      (goodTheta D)
      (goodTheta_root D)
      (scaledCurve_relation D)
      (goodTheta_derivative_isUnit D)
  simpa only [goodBranchIdeal,
    good_normalizedKummerInteger] using h

/-! ## The principal-ideal endpoint -/

/-- Localization preserves principality when the base ring is a principal
ideal ring. -/
theorem ideal_isPrincipal_of_base
    {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {M : Submonoid R}
    [IsLocalization M S] [IsPrincipalIdealRing R]
    (J : Ideal S) :
    Submodule.IsPrincipal J := by
  obtain ⟨x, hx⟩ :=
    Submodule.IsPrincipal.principal
      (J.under R : Submodule R R)
  have hxIdeal :
      J.under R = Ideal.span ({x} : Set R) :=
    hx
  refine ⟨algebraMap R S x, ?_⟩
  calc
    J =
        Ideal.map (algebraMap R S) (J.under R) :=
      (IsLocalization.map_under M S J).symm
    _ =
        Ideal.map (algebraMap R S)
          (Ideal.span ({x} : Set R)) := by
            rw [hxIdeal]
    _ =
        Ideal.span ({algebraMap R S x} : Set S) := by
          rw [Ideal.map_span, Set.image_singleton]

/-- With principality supplied as an explicit parameter, the good-locus
Kummer value is associated to an actual square. -/
theorem normalizedKummerInteger_associated_square_of_principal
    (D : N13LowDegreeKummerHom.LowRep)
    (hprincipal :
      Submodule.IsPrincipal (goodBranchIdeal D)) :
    ∃ z : GoodOrder D,
      Associated
        (algebraMap O (GoodOrder D)
          (normalizedKummerInteger D))
        (z ^ 2) := by
  letI :
      Submodule.IsPrincipal
        (goodBranchIdeal D : Submodule (GoodOrder D) (GoodOrder D)) :=
    hprincipal
  obtain ⟨z, hz⟩ :=
    Submodule.IsPrincipal.principal
      (goodBranchIdeal D :
        Submodule (GoodOrder D) (GoodOrder D))
  refine ⟨z, Ideal.span_singleton_eq_span_singleton.mp ?_⟩
  calc
    Ideal.span
        ({algebraMap O (GoodOrder D)
            (normalizedKummerInteger D)} :
          Set (GoodOrder D)) =
        goodBranchIdeal D ^ 2 :=
      (goodBranchIdeal_sq D).symm
    _ =
        Ideal.span ({z} : Set (GoodOrder D)) ^ 2 := by
          rw [hz]
    _ =
        Ideal.span ({z ^ 2} : Set (GoodOrder D)) := by
          rw [Ideal.span_singleton_pow]

/-- Class number one of the absolute ring of integers is the only global
input needed to turn the good branch ideal into an element square. -/
theorem normalizedKummerInteger_associated_square
    (D : N13LowDegreeKummerHom.LowRep)
    [IsPrincipalIdealRing O] :
    ∃ z : GoodOrder D,
      Associated
        (algebraMap O (GoodOrder D)
          (normalizedKummerInteger D))
        (z ^ 2) := by
  apply
    normalizedKummerInteger_associated_square_of_principal
      D
  exact
    ideal_isPrincipal_of_base
      (R := O) (S := GoodOrder D)
      (M := Submonoid.powers (badGenerator D))
      (goodBranchIdeal D)

end

end MazurProof.N13GlobalKummerIdealSquare


