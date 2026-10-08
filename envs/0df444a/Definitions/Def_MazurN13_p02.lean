-- Prove2me | Definitions.Def_MazurN13_p02
-- name    : MazurN13_p02
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-08T00:03:03.320821+00:00
-- url     : https://prove2.me/theorems/4d6c5d74-cd64-4db0-aa0c-70fe5657ea4d
-- title:
--   Mazur order 13 (Huang FLT port), part 2/33
-- statement:
--   Part 2 of 33 of a machine-checked Lean proof that no elliptic curve over $\mathbb{Q}$ has a rational point of exact order $13$ (the case $N=13$ of Mazur's torsion theorem). The chain as a whole proves that the only rational affine points of the genus-two curve $Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$ (a model of $X_1(13)$) have $X\in\{0,-1\}$ (cusps); the final result is `MazurProof.N13ConstructedRationalPointTheorem.affine_x_is_cuspidal` in part {N}.
--
--   This part is not a single definition: it is a verbatim, sorry-free slice of Xiang Huang's Lean development, ported to this Mathlib and split into compile-sized pieces, each importing the previous part. It contains the modules:
--
--   - `FLT.Assumptions.MazurProof.N13Infinity`
--   - `FLT.Assumptions.MazurProof.SexticMumfordBasis`
--   - `FLT.Assumptions.MazurProof.SexticMumfordNormalForm`
--   - `FLT.Assumptions.MazurProof.SexticMumfordIdeal`
--   - `FLT.Assumptions.MazurProof.SexticMumfordUnit`
--   - `FLT.Assumptions.MazurProof.SexticOrientedPic`
--   - `FLT.Assumptions.MazurProof.SexticMumfordNorm`
--   - `FLT.Assumptions.MazurProof.SexticMumfordRepresentative`
--   - `FLT.Assumptions.MazurProof.N13IntegralModelContraction`
--   - `FLT.Assumptions.MazurProof.N13IntegralFractionalHull`
--   - `FLT.Assumptions.MazurProof.N13IntegralGraphContraction`
--   - `FLT.Assumptions.MazurProof.N13SpecialDualFrame`
--   - `FLT.Assumptions.MazurProof.N13SpecialQuotientBasis`
--   - `FLT.Assumptions.MazurProof.N13SpecialGraphDivisor`
--
--   Port notes: API drift fixes only (transparency options, renamed lemmas, explicit instances); local notations expanded, `private` removed.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT commit 51bbb4f, directory FLT/Assumptions/MazurProof (N13* and SexticMumford* modules and their dependencies)

import Mathlib
import Definitions.Def_MazurN13_p01
set_option maxHeartbeats 1000000

-- module FLT.Assumptions.MazurProof.N13Infinity
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13Infinity =====
section

/-!
# The positive infinity of the N13 genus-two curve

We construct the chosen branch at infinity inside `K((s))`.  With `x=s⁻¹`,
the equation becomes

`(s³ y)² = 1 + 4s + 6s² + 2s³ + s⁴ + 2s⁵ + s⁶`.

The square root with constant coefficient `+1` is obtained from the formal
binomial series.  The resulting embedding of the function field supplies the
integer orientation used in `SexticMumford`.
-/

open Polynomial
open scoped LaurentSeries PowerSeries

namespace MazurProof.N13Infinity

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

/-! ## The formal positive square root -/

def reverseF : K⟦X⟧ :=
  1 + 4 * PowerSeries.X + 6 * PowerSeries.X ^ 2 +
    2 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 +
    2 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6

def reverseTail : K⟦X⟧ := reverseF K - 1

omit [CharZero K] in
@[simp] theorem reverseTail_constantCoeff :
    PowerSeries.constantCoeff (reverseTail K) = 0 := by
  simp [reverseTail, reverseF]

omit [CharZero K] in
theorem reverseTail_hasSubst : PowerSeries.HasSubst (reverseTail K) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (reverseTail_constantCoeff K)

def sqrtReverseF : K⟦X⟧ :=
  PowerSeries.substAlgHom (reverseTail_hasSubst K)
    (PowerSeries.binomialSeries K (1 / 2 : K))

theorem sqrtReverseF_sq : sqrtReverseF K ^ 2 = reverseF K := by
  let h := reverseTail_hasSubst K
  change (PowerSeries.substAlgHom h
      (PowerSeries.binomialSeries K (1 / 2 : K))) ^ 2 = reverseF K
  rw [pow_two, ← map_mul, ← PowerSeries.binomialSeries_add]
  have hhalf : (1 / 2 : K) + 1 / 2 = 1 := by norm_num
  rw [hhalf]
  have hone : PowerSeries.binomialSeries K (1 : K) =
      (1 + PowerSeries.X : K⟦X⟧) := by
    simpa using (PowerSeries.binomialSeries_nat (R := K) (A := K) 1)
  rw [hone]
  simp only [map_add, map_one,
    PowerSeries.substAlgHom_X]
  simp [reverseTail]

@[simp] theorem sqrtReverseF_constantCoeff :
    PowerSeries.constantCoeff (sqrtReverseF K) = 1 := by
  rw [sqrtReverseF]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  rw [PowerSeries.coe_substAlgHom (reverseTail_hasSubst K)]
  rw [PowerSeries.coeff_subst' (reverseTail_hasSubst K)]
  simp only [PowerSeries.binomialSeries_coeff]
  rw [finsum_eq_single _ 0]
  · simp
  · intro b hb
    simp [PowerSeries.coeff_zero_eq_constantCoeff,
      reverseTail_constantCoeff, hb]

/-! ## An algebraic model of the function field -/

def curvePolyRat : (RatFunc K)[X] :=
  (SexticMumford.curvePoly (N13Mumford.model K)).map
    (algebraMap K[X] (RatFunc K))

theorem curvePolyRat_monic : (curvePolyRat K).Monic := by
  exact (SexticMumford.curvePoly_monic (N13Mumford.model K)).map _

theorem curvePolyRat_irreducible : Irreducible (curvePolyRat K) := by
  rw [curvePolyRat]
  exact
    (SexticMumford.curvePoly_monic
      (N13Mumford.model K)).irreducible_iff_irreducible_map_fraction_map
        (R := K[X]) (K := RatFunc K) |>.mp
        (SexticMumford.curvePoly_irreducible (N13Mumford.model K))

instance curvePolyRatIrreducibleFact :
    Fact (Irreducible (curvePolyRat K)) :=
  ⟨curvePolyRat_irreducible K⟩

abbrev AlgebraicFunctionField : Type u := AdjoinRoot (curvePolyRat K)

def coordinateToAlgebraic :
    N13Mumford.CoordinateRing K →+* AlgebraicFunctionField K :=
  AdjoinRoot.map (algebraMap K[X] (RatFunc K))
    (SexticMumford.curvePoly (N13Mumford.model K)) (curvePolyRat K) (by
      rw [curvePolyRat])

@[simp] theorem coordinateToAlgebraic_mk (g : K[X][X]) :
    coordinateToAlgebraic K (AdjoinRoot.mk (SexticMumford.curvePoly (N13Mumford.model K)) g) =
      AdjoinRoot.mk (curvePolyRat K)
        (g.map (algebraMap K[X] (RatFunc K))) := by
  simp only [coordinateToAlgebraic, AdjoinRoot.map, AdjoinRoot.lift_mk]
  rw [← Polynomial.eval₂_map]
  simpa only [← AdjoinRoot.algebraMap_eq, ← Polynomial.aeval_def] using
    (AdjoinRoot.aeval_eq
      (f := curvePolyRat K)
      (p := g.map (algebraMap K[X] (RatFunc K))))

theorem coordinateToAlgebraic_injective :
    Function.Injective (coordinateToAlgebraic K) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective z
    let r : K[X][X] := g %ₘ SexticMumford.curvePoly (N13Mumford.model K)
    have hrz : AdjoinRoot.mk (SexticMumford.curvePoly (N13Mumford.model K)) r =
        AdjoinRoot.mk (SexticMumford.curvePoly (N13Mumford.model K)) g := by
      simpa only [r, AdjoinRoot.modByMonicHom_mk] using
        (AdjoinRoot.mk_leftInverse (SexticMumford.curvePoly_monic (N13Mumford.model K))
          (AdjoinRoot.mk (SexticMumford.curvePoly (N13Mumford.model K)) g))
    have hmap : AdjoinRoot.mk (curvePolyRat K)
        (r.map (algebraMap K[X] (RatFunc K))) = 0 := by
      rw [← coordinateToAlgebraic_mk, hrz, hz]
    have hrdeg : r.degree < (SexticMumford.curvePoly (N13Mumford.model K)).degree := by
      exact Polynomial.degree_modByMonic_lt g
        (SexticMumford.curvePoly_monic (N13Mumford.model K))
    have hbase : Function.Injective
        (algebraMap K[X] (RatFunc K)) :=
      IsFractionRing.injective K[X] (RatFunc K)
    have hmapdeg :
        (r.map (algebraMap K[X] (RatFunc K))).degree <
          (curvePolyRat K).degree := by
      rw [curvePolyRat, Polynomial.degree_map_eq_of_injective hbase,
        Polynomial.degree_map_eq_of_injective hbase]
      exact hrdeg
    have hrmapzero : r.map (algebraMap K[X] (RatFunc K)) = 0 := by
      by_contra hr0
      exact (curvePolyRat_monic K).not_dvd_of_degree_lt hr0 hmapdeg
        (AdjoinRoot.mk_eq_zero.mp hmap)
    have hrzero : r = 0 :=
      (Polynomial.map_eq_zero_iff hbase).mp hrmapzero
    rw [← hrz, hrzero, map_zero]
    exact Submodule.zero_mem _
  · exact bot_le

/-! ## The branch `x = s⁻¹`, `s³y = +sqrt(reverseF)` -/

omit [CharZero K] in
theorem ratXInv_transcendental :
    Transcendental K ((RatFunc.X : RatFunc K)⁻¹) := by
  rw [Transcendental, ← IsAlgebraic.inv_iff]
  simpa [Transcendental] using (RatFunc.transcendental_X (K := K))

def invPolyAlgHom : K[X] →ₐ[K] RatFunc K :=
  Polynomial.aeval ((RatFunc.X : RatFunc K)⁻¹)

omit [CharZero K] in
theorem invPolyAlgHom_injective :
    Function.Injective (invPolyAlgHom K) := by
  exact transcendental_iff_injective.mp (ratXInv_transcendental K)

def ratInvAlgHom : RatFunc K →ₐ[K] RatFunc K :=
  RatFunc.liftAlgHom (invPolyAlgHom K)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (invPolyAlgHom_injective K))

omit [CharZero K] in
omit [CharZero K] in
@[simp] theorem ratInvAlgHom_X :
    ratInvAlgHom K (RatFunc.X : RatFunc K) =
      (RatFunc.X : RatFunc K)⁻¹ := by
  calc
    ratInvAlgHom K (RatFunc.X : RatFunc K) =
        ratInvAlgHom K
          (algebraMap K[X] (RatFunc K) Polynomial.X) := by
            rw [RatFunc.algebraMap_X]
    _ = invPolyAlgHom K Polynomial.X := by
      change RatFunc.liftRingHom (invPolyAlgHom K).toRingHom _
          (algebraMap K[X] (RatFunc K) Polynomial.X) = _
      exact RatFunc.liftRingHom_algebraMap _ _ _
    _ = (RatFunc.X : RatFunc K)⁻¹ := by simp [invPolyAlgHom]

def standardRatToLaurent : RatFunc K →+* LaurentSeries K :=
  IsFractionRing.lift
    (g := algebraMap K[X] (LaurentSeries K))
    (Polynomial.algebraMap_hahnSeries_injective (R := K) ℤ)

omit [CharZero K] in
@[simp] theorem standardRatToLaurent_X :
    standardRatToLaurent K (RatFunc.X : RatFunc K) =
      HahnSeries.single 1 1 := by
  calc
    standardRatToLaurent K (RatFunc.X : RatFunc K) =
        standardRatToLaurent K
          (algebraMap K[X] (RatFunc K) Polynomial.X) := by
            rw [RatFunc.algebraMap_X]
    _ = algebraMap K[X] (LaurentSeries K) Polynomial.X := by
      exact IsFractionRing.lift_algebraMap
        (Polynomial.algebraMap_hahnSeries_injective (R := K) ℤ) _
    _ = HahnSeries.single 1 1 := by simp

omit [CharZero K] in
@[simp] theorem standardRatToLaurent_algebraMap (p : K[X]) :
    standardRatToLaurent K (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (LaurentSeries K) p := by
  exact IsFractionRing.lift_algebraMap
    (Polynomial.algebraMap_hahnSeries_injective (R := K) ℤ) p

omit [CharZero K] in
omit [CharZero K] in
@[simp] theorem ratInvAlgHom_algebraMap (p : K[X]) :
    ratInvAlgHom K (algebraMap K[X] (RatFunc K) p) =
      invPolyAlgHom K p := by
  change RatFunc.liftRingHom (invPolyAlgHom K).toRingHom _
      (algebraMap K[X] (RatFunc K) p) = _
  exact RatFunc.liftRingHom_algebraMap _ _ _

def ratToLaurent : RatFunc K →+* LaurentSeries K :=
  (standardRatToLaurent K).comp
    (ratInvAlgHom K).toRingHom

def parameter : LaurentSeries K := HahnSeries.single 1 1

@[simp] theorem parameter_ne_zero : parameter K ≠ 0 := by
  simp [parameter]

omit [CharZero K] in
@[simp] theorem ratToLaurent_X :
    ratToLaurent K (RatFunc.X : RatFunc K) = (parameter K)⁻¹ := by
  simp [ratToLaurent, parameter]

omit [CharZero K] in
@[simp] theorem ratToLaurent_C (a : K) :
    ratToLaurent K (RatFunc.C a) =
      algebraMap K (LaurentSeries K) a := by
  rw [← RatFunc.algebraMap_C]
  change standardRatToLaurent K
      (ratInvAlgHom K (algebraMap K[X] (RatFunc K) (C a))) = _
  rw [ratInvAlgHom_algebraMap]
  simp only [invPolyAlgHom, Polynomial.aeval_C]
  change standardRatToLaurent K (RatFunc.C a) = _
  rw [← RatFunc.algebraMap_C]
  rw [standardRatToLaurent_algebraMap]
  rw [Polynomial.algebraMap_hahnSeries_apply, Polynomial.coe_C,
    HahnSeries.ofPowerSeries_C]
  rw [HahnSeries.algebraMap_apply' (Γ := ℤ)]
  simp

omit [CharZero K] in
theorem ratToLaurent_comp_algebraMap :
    (ratToLaurent K).comp (algebraMap K[X] (RatFunc K)) =
      Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K))
        ((parameter K)⁻¹) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp
  · simp

def wSeries : LaurentSeries K := (sqrtReverseF K : LaurentSeries K)

def ySeries : LaurentSeries K :=
  ((parameter K)⁻¹) ^ 3 * wSeries K

omit [CharZero K] in
theorem reverseF_coe :
    ((reverseF K : K⟦X⟧) : LaurentSeries K) =
      1 + 4 * parameter K + 6 * parameter K ^ 2 +
        2 * parameter K ^ 3 + parameter K ^ 4 +
        2 * parameter K ^ 5 + parameter K ^ 6 := by
  simp [reverseF, parameter, PowerSeries.coe_add, PowerSeries.coe_mul,
    PowerSeries.coe_pow, map_ofNat]

theorem wSeries_sq :
    wSeries K ^ 2 =
      1 + 4 * parameter K + 6 * parameter K ^ 2 +
        2 * parameter K ^ 3 + parameter K ^ 4 +
        2 * parameter K ^ 5 + parameter K ^ 6 := by
  rw [wSeries, ← PowerSeries.coe_pow, sqrtReverseF_sq, reverseF_coe]

theorem ySeries_sq :
    ySeries K ^ 2 =
      (N13Mumford.f K).eval₂ (algebraMap K (LaurentSeries K))
        ((parameter K)⁻¹) := by
  rw [ySeries]
  simp only [N13Mumford.f, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_mul, eval₂_ofNat, eval₂_one]
  field_simp [parameter_ne_zero K]
  rw [wSeries_sq]
  ring

theorem curvePolyRat_eval_ySeries :
    (curvePolyRat K).eval₂ (ratToLaurent K) (ySeries K) = 0 := by
  rw [curvePolyRat, Polynomial.eval₂_map,
    ratToLaurent_comp_algebraMap]
  change (X ^ 2 - C (N13Mumford.f K)).eval₂
      (Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K))
        ((parameter K)⁻¹)) (ySeries K) = 0
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  rw [ySeries_sq]
  exact sub_self _

def algebraicToLaurent :
    AlgebraicFunctionField K →+* LaurentSeries K :=
  AdjoinRoot.lift (ratToLaurent K) (ySeries K)
    (curvePolyRat_eval_ySeries K)

theorem algebraicToLaurent_injective :
    Function.Injective (algebraicToLaurent K) :=
  (algebraicToLaurent K).injective

def coordinateToLaurent :
    N13Mumford.CoordinateRing K →+* LaurentSeries K :=
  (algebraicToLaurent K).comp (coordinateToAlgebraic K)

theorem coordinateToLaurent_injective :
    Function.Injective (coordinateToLaurent K) :=
  (algebraicToLaurent_injective K).comp
    (coordinateToAlgebraic_injective K)

def functionFieldToLaurent :
    N13Mumford.FunctionField K →+* LaurentSeries K :=
  IsFractionRing.lift (coordinateToLaurent_injective K)

theorem functionFieldToLaurent_injective :
    Function.Injective (functionFieldToLaurent K) :=
  (functionFieldToLaurent K).injective

def laurentOrder : (LaurentSeries K)ˣ →* Multiplicative ℤ where
  toFun z := Multiplicative.ofAdd (z.1.order)
  map_one' := by
    change (1 : LaurentSeries K).order = 0
    simp
  map_mul' x y := by
    change ((x.1 * y.1 : LaurentSeries K).order) =
      x.1.order + y.1.order
    exact HahnSeries.order_mul x.ne_zero y.ne_zero

def infinityOrderHom :
    (N13Mumford.FunctionField K)ˣ →* Multiplicative ℤ :=
  (laurentOrder K).comp (Units.map (functionFieldToLaurent K))

def positiveInfinityOrder : SexticMumford.InfinityOrder (N13Mumford.model K) where
  ordPlus := infinityOrderHom K

end

end MazurProof.N13Infinity

end
end

-- module FLT.Assumptions.MazurProof.SexticMumfordBasis
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordBasis =====
section

/-!
# The rank-two basis of a smooth sextic affine ring

For a model `Y² = f(X)`, every element of the affine coordinate ring is
written uniquely as `p(X) + q(X)Y`.  This is the coefficient API used by
the Mumford ideal and normal-form layers.
-/

open Polynomial

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

variable (M : Model K)

def xClassHom : K[X] →+* CoordinateRing M :=
  AdjoinRoot.of (curvePoly M)

@[simp] theorem xClassHom_apply (p : K[X]) :
    xClassHom M p = xClass M p := rfl

@[simp] theorem xClass_zero : xClass M 0 = 0 := by
  exact map_zero (xClassHom M)

@[simp] theorem xClass_one : xClass M 1 = 1 := by
  exact map_one (xClassHom M)

@[simp] theorem xClass_add (p q : K[X]) :
    xClass M (p + q) = xClass M p + xClass M q := by
  exact map_add (xClassHom M) p q

@[simp] theorem xClass_sub (p q : K[X]) :
    xClass M (p - q) = xClass M p - xClass M q := by
  exact map_sub (xClassHom M) p q

@[simp] theorem xClass_neg (p : K[X]) :
    xClass M (-p) = -xClass M p := by
  exact map_neg (xClassHom M) p

@[simp] theorem xClass_mul (p q : K[X]) :
    xClass M (p * q) = xClass M p * xClass M q := by
  exact map_mul (xClassHom M) p q

@[simp] theorem xClass_pow (p : K[X]) (n : ℕ) :
    xClass M (p ^ n) = xClass M p ^ n := by
  exact map_pow (xClassHom M) p n

def normalPoly : CoordinateRing M →ₗ[K[X]] K[X][X] :=
  AdjoinRoot.modByMonicHom (curvePoly_monic M)

def coeff0 : CoordinateRing M →ₗ[K[X]] K[X] :=
  (Polynomial.lcoeff K[X] 0).comp (normalPoly M)

def coeffY : CoordinateRing M →ₗ[K[X]] K[X] :=
  (Polynomial.lcoeff K[X] 1).comp (normalPoly M)

@[simp] theorem normalPoly_mk (g : K[X][X]) :
    normalPoly M (mk M g) = g %ₘ curvePoly M := by
  rfl

@[simp] theorem coeff0_mk (g : K[X][X]) :
    coeff0 M (mk M g) = (g %ₘ curvePoly M).coeff 0 := by
  rfl

@[simp] theorem coeffY_mk (g : K[X][X]) :
    coeffY M (mk M g) = (g %ₘ curvePoly M).coeff 1 := by
  rfl

theorem degree_curvePoly : (curvePoly M).degree = 2 := by
  rw [degree_eq_natDegree (curvePoly_monic M).ne_zero,
    curvePoly_natDegree]
  norm_num

theorem normalPoly_eq_C_add_C_mul_X (z : CoordinateRing M) :
    normalPoly M z = C (coeff0 M z) + C (coeffY M z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ curvePoly M =
        C ((g %ₘ curvePoly M).coeff 0) +
          C ((g %ₘ curvePoly M).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := curvePoly M) (curvePoly_monic M)
        (n := 2) (by rw [degree_curvePoly]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm

theorem recompose (z : CoordinateRing M) :
    xClass M (coeff0 M z) + xClass M (coeffY M z) * yClass M = z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        xClass M (coeff0 M (AdjoinRoot.mk (curvePoly M) g)) +
              xClass M (coeffY M (AdjoinRoot.mk (curvePoly M) g)) * yClass M =
            AdjoinRoot.mk (curvePoly M)
              (C (coeff0 M (AdjoinRoot.mk (curvePoly M) g)) +
                C (coeffY M (AdjoinRoot.mk (curvePoly M) g)) * X) := by
                  simp only [xClass, yClass, mk, map_add, map_mul,
                    AdjoinRoot.mk_C, AdjoinRoot.mk_X]
        _ = AdjoinRoot.mk (curvePoly M)
              (normalPoly M (AdjoinRoot.mk (curvePoly M) g)) := by
                rw [normalPoly_eq_C_add_C_mul_X]
        _ = AdjoinRoot.mk (curvePoly M) g :=
          AdjoinRoot.mk_leftInverse (curvePoly_monic M)
            (AdjoinRoot.mk (curvePoly M) g)

@[simp] theorem coeff0_xClass (p : K[X]) :
    coeff0 M (xClass M p) = p := by
  change (C p %ₘ curvePoly M).coeff 0 = p
  rw [(modByMonic_eq_self_iff (curvePoly_monic M)).mpr]
  · simp
  · exact degree_C_le.trans_lt (by rw [degree_curvePoly]; norm_num)

@[simp] theorem coeffY_xClass (p : K[X]) :
    coeffY M (xClass M p) = 0 := by
  change (C p %ₘ curvePoly M).coeff 1 = 0
  rw [(modByMonic_eq_self_iff (curvePoly_monic M)).mpr]
  · simp
  · exact degree_C_le.trans_lt (by rw [degree_curvePoly]; norm_num)

@[simp] theorem coeff0_yClass : coeff0 M (yClass M) = 0 := by
  change (X %ₘ curvePoly M).coeff 0 = 0
  rw [(modByMonic_eq_self_iff (curvePoly_monic M)).mpr]
  · simp
  · rw [degree_X, degree_curvePoly]
    norm_num

@[simp] theorem coeffY_yClass : coeffY M (yClass M) = 1 := by
  change (X %ₘ curvePoly M).coeff 1 = 1
  rw [(modByMonic_eq_self_iff (curvePoly_monic M)).mpr]
  · simp
  · rw [degree_X, degree_curvePoly]
    norm_num

theorem eq_iff_coeff (z w : CoordinateRing M) :
    z = w ↔ coeff0 M z = coeff0 M w ∧ coeffY M z = coeffY M w := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, hY⟩
    rw [← recompose M z, ← recompose M w, h0, hY]

/-! ## Hyperelliptic conjugation and the quadratic norm -/

theorem neg_y_relation :
    (curvePoly M).eval₂ (AdjoinRoot.of (curvePoly M)) (-(yClass M)) = 0 := by
  change (X ^ 2 - C M.f).eval₂
      (AdjoinRoot.of (curvePoly M)) (-(yClass M)) = 0
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change (-(yClass M)) ^ 2 - xClass M M.f = 0
  rw [neg_sq, yClass_sq]
  exact sub_self _

def conjugate : CoordinateRing M →+* CoordinateRing M :=
  AdjoinRoot.lift (AdjoinRoot.of (curvePoly M)) (-(yClass M))
    (neg_y_relation M)

@[simp] theorem conjugate_xClass (p : K[X]) :
    conjugate M (xClass M p) = xClass M p := by
  change conjugate M (AdjoinRoot.of (curvePoly M) p) =
    AdjoinRoot.of (curvePoly M) p
  exact AdjoinRoot.lift_of (neg_y_relation M)

@[simp] theorem conjugate_yClass :
    conjugate M (yClass M) = -(yClass M) := by
  exact AdjoinRoot.lift_root (neg_y_relation M)

theorem conjugate_involutive : Function.Involutive (conjugate M) := by
  have hcomp : (conjugate M).comp (conjugate M) =
      RingHom.id (CoordinateRing M) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro k
        change conjugate M (conjugate M (xClass M (C k))) = xClass M (C k)
        rw [conjugate_xClass, conjugate_xClass]
      · change conjugate M (conjugate M (xClass M X)) = xClass M X
        rw [conjugate_xClass, conjugate_xClass]
    · change conjugate M (conjugate M (yClass M)) = yClass M
      rw [conjugate_yClass, map_neg, conjugate_yClass, neg_neg]
  intro z
  exact DFunLike.congr_fun hcomp z

def norm (z : CoordinateRing M) : CoordinateRing M :=
  z * conjugate M z

theorem norm_recompose (p q : K[X]) :
    norm M (xClass M p + xClass M q * yClass M) =
      xClass M (p ^ 2 - q ^ 2 * M.f) := by
  simp only [norm, map_add, map_mul, conjugate_xClass, conjugate_yClass]
  calc
    (xClass M p + xClass M q * yClass M) *
          (xClass M p + xClass M q * -yClass M) =
        xClass M p ^ 2 - xClass M q ^ 2 * yClass M ^ 2 := by ring
    _ = xClass M p ^ 2 - xClass M q ^ 2 * xClass M M.f := by
      rw [yClass_sq]
    _ = xClass M (p ^ 2 - q ^ 2 * M.f) := by
      change
        AdjoinRoot.of (curvePoly M) p ^ 2 -
            AdjoinRoot.of (curvePoly M) q ^ 2 *
              AdjoinRoot.of (curvePoly M) M.f =
          AdjoinRoot.of (curvePoly M) (p ^ 2 - q ^ 2 * M.f)
      simp only [map_sub, map_mul, map_pow]

end

end MazurProof.SexticMumford

end
end

-- module FLT.Assumptions.MazurProof.SexticMumfordNormalForm
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordNormalForm =====
section

/-!
# First normalization step for sextic Mumford ideals

Before choosing a two-generator `K[X]`-basis, a fractional ideal may be
cleared of denominators by a single nonzero element of the coordinate ring.
This is the first, representation-independent step in the normal-form
argument.
-/

open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- Every invertible fractional ideal of the sextic coordinate ring becomes
an integral ideal after multiplication by one nonzero principal factor. -/
theorem invFrac_exists_integral_scaling (M : Model K) (I : InvFrac M) :
    ∃ (a : CoordinateRing M) (J : Ideal (CoordinateRing M)), a ≠ 0 ∧
      (I : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
        FractionalIdeal.spanSingleton (CoordinateRing M)⁰
          (algebraMap (CoordinateRing M) (FunctionField M) a)⁻¹ * J := by
  exact FractionalIdeal.exists_eq_spanSingleton_mul
    (I : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))

end

end MazurProof.SexticMumford

end
end

-- module FLT.Assumptions.MazurProof.SexticMumfordIdeal
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordIdeal =====
section

/-!
# Mumford evaluation ideals for a smooth sextic affine ring

For a model `Y² = f(X)`, quotient evaluation `X ↦ X mod u`, `Y ↦ v mod u`
has kernel exactly `(u, Y - v)`.  This recovers canonical Mumford
polynomials from their ideal and is the algebraic core of normal-form
uniqueness.
-/

open Polynomial

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

variable (M : Model K)

abbrev MumfordResidue (D : SemiMumford M) : Type u :=
  K[X] ⧸ Ideal.span ({D.u} : Set K[X])

theorem mumford_root_relation (D : SemiMumford M) :
    (curvePoly M).eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v) = 0 := by
  change (X ^ 2 - C M.f).eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v) = 0
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X]))
    (D.v ^ 2 - M.f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  obtain ⟨w, hw⟩ := D.curve_dvd
  refine ⟨-w, ?_⟩
  calc
    D.v ^ 2 - M.f = -(M.f - D.v ^ 2) := by ring
    _ = -(D.u * w) := by rw [hw]
    _ = D.u * (-w) := by ring

def mumfordEval (D : SemiMumford M) :
    CoordinateRing M →+* MumfordResidue M D :=
  AdjoinRoot.lift
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v)
    (mumford_root_relation M D)

@[simp] theorem mumfordEval_xClass (D : SemiMumford M) (p : K[X]) :
    mumfordEval M D (xClass M p) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) p := by
  change mumfordEval M D (AdjoinRoot.of (curvePoly M) p) = _
  exact AdjoinRoot.lift_of (mumford_root_relation M D)

@[simp] theorem mumfordEval_yClass (D : SemiMumford M) :
    mumfordEval M D (yClass M) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v := by
  exact AdjoinRoot.lift_root (mumford_root_relation M D)

@[simp] theorem mumfordEval_ySubClass (D : SemiMumford M) :
    mumfordEval M D (ySubClass M D.v) = 0 := by
  simp [ySubClass]

theorem mumfordIdeal_le_ker (D : SemiMumford M) :
    mumfordIdeal M D.u D.v ≤ RingHom.ker (mumfordEval M D) := by
  apply Ideal.span_le.2
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · change mumfordEval M D (xClass M D.u) = 0
    rw [mumfordEval_xClass,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  · change mumfordEval M D (ySubClass M D.v) = 0
    rw [mumfordEval_ySubClass]

theorem ker_mumfordEval (D : SemiMumford M) :
    RingHom.ker (mumfordEval M D) = mumfordIdeal M D.u D.v := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    let p : K[X] := coeff0 M z
    let q : K[X] := coeffY M z
    have hz' : mumfordEval M D
        (xClass M p + xClass M q * yClass M) = 0 := by
      rw [recompose M z]
      exact hz
    have hquot : Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X]))
        (p + q * D.v) = 0 := by
      simpa only [map_add, map_mul, mumfordEval_xClass,
        mumfordEval_yClass, map_add, map_mul] using hz'
    have hdvd : D.u ∣ p + q * D.v := by
      exact Ideal.mem_span_singleton.mp
        (Ideal.Quotient.eq_zero_iff_mem.mp hquot)
    obtain ⟨s, hs⟩ := hdvd
    have hu : xClass M D.u ∈ mumfordIdeal M D.u D.v :=
      xClass_mem_mumfordIdeal M D.u D.v
    have hyv : ySubClass M D.v ∈ mumfordIdeal M D.u D.v :=
      Ideal.subset_span (by simp)
    have hbase : xClass M (p + q * D.v) ∈
        mumfordIdeal M D.u D.v := by
      rw [hs, xClass_mul, mul_comm]
      exact Ideal.mul_mem_left (mumfordIdeal M D.u D.v) (xClass M s) hu
    have hgraph : xClass M q * ySubClass M D.v ∈
        mumfordIdeal M D.u D.v :=
      Ideal.mul_mem_left (mumfordIdeal M D.u D.v) (xClass M q) hyv
    rw [← recompose M z]
    have hdecomp :
        xClass M p + xClass M q * yClass M =
          xClass M (p + q * D.v) + xClass M q * ySubClass M D.v := by
      simp only [xClass_add, xClass_mul, ySubClass]
      ring
    rw [hdecomp]
    exact Ideal.add_mem _ hbase hgraph
  · exact mumfordIdeal_le_ker M D

theorem mumfordEval_surjective (D : SemiMumford M) :
    Function.Surjective (mumfordEval M D) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨xClass M p, mumfordEval_xClass M D p⟩

/-- The graph quotient is canonically the monic polynomial quotient. -/
noncomputable def mumfordQuotientEquiv (D : SemiMumford M) :
    CoordinateRing M ⧸ mumfordIdeal M D.u D.v ≃+*
      MumfordResidue M D :=
  (Ideal.quotEquivOfEq (ker_mumfordEval M D).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (mumfordEval_surjective M D))

@[simp] theorem mumfordQuotientEquiv_apply_mk
    (D : SemiMumford M) (z : CoordinateRing M) :
    mumfordQuotientEquiv M D
        (Ideal.Quotient.mk (mumfordIdeal M D.u D.v) z) =
      mumfordEval M D z := by
  simp [mumfordQuotientEquiv]

/-- The graph quotient equivalence respects the coefficient field. -/
noncomputable def mumfordQuotientAlgEquiv (D : SemiMumford M) :
    (CoordinateRing M ⧸ mumfordIdeal M D.u D.v) ≃ₐ[K]
      MumfordResidue M D :=
  AlgEquiv.ofRingEquiv
    (f := mumfordQuotientEquiv M D)
    (by
      intro r
      change
        mumfordQuotientEquiv M D
            (Ideal.Quotient.mk
              (mumfordIdeal M D.u D.v) (xClass M (C r))) =
          Ideal.Quotient.mk
            (Ideal.span ({D.u} : Set K[X])) (C r)
      rw [mumfordQuotientEquiv_apply_mk,
        mumfordEval_xClass])

theorem mumfordIdeal_comap_base (D : SemiMumford M) :
    (mumfordIdeal M D.u D.v).comap (xClassHom M) =
      Ideal.span ({D.u} : Set K[X]) := by
  rw [← ker_mumfordEval]
  ext p
  simp only [Ideal.mem_comap, RingHom.mem_ker, xClassHom_apply,
    mumfordEval_xClass,
    Ideal.Quotient.eq_zero_iff_mem]

end

end MazurProof.SexticMumford

end
end

-- module FLT.Assumptions.MazurProof.SexticMumfordUnit
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordUnit =====
section

/-!
# Explicit invertibility of Mumford ideals on a smooth sextic

For a semi-Mumford pair `(u,v)`, squarefreeness of the sextic gives
`(u, 2v, (f-v²)/u) = 1`.  Consequently `(u,Y-v) (u,Y+v) = (u)`,
which packages the Mumford ideal as a unit fractional ideal.
-/

open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

variable (M : Model K)

theorem mumford_bezout (D : SemiMumford M) :
    ∃ w a b c : K[X],
      M.f - D.v ^ 2 = D.u * w ∧
      a * D.u + b * (2 * D.v) + c * w = 1 := by
  classical
  obtain ⟨w, hw⟩ := D.curve_dvd
  have hcop : IsCoprime D.u (EuclideanDomain.gcd (2 * D.v) w) := by
    apply isCoprime_of_irreducible_dvd
    · intro hzero
      exact D.u_monic.ne_zero hzero.1
    · intro z hz hzu hzg
      have hz2v : z ∣ 2 * D.v :=
        hzg.trans (EuclideanDomain.gcd_dvd_left (2 * D.v) w)
      have hzw : z ∣ w :=
        hzg.trans (EuclideanDomain.gcd_dvd_right (2 * D.v) w)
      have htwo : IsUnit (2 : K[X]) := by
        have heq : C (2 : K) = (2 : K[X]) := by
          exact map_natCast (C : K →+* K[X]) 2
        rw [← heq]
        exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr M.two_ne_zero)
      have hzv : z ∣ D.v := by
        rcases hz.prime.dvd_mul.mp hz2v with hz2 | hzv
        · exact (hz.not_isUnit (isUnit_of_dvd_unit hz2 htwo)).elim
        · exact hzv
      have hzzSub : z * z ∣ M.f - D.v ^ 2 := by
        rw [hw]
        exact mul_dvd_mul hzu hzw
      have hzzSq : z * z ∣ D.v ^ 2 := by
        simpa only [pow_two] using mul_dvd_mul hzv hzv
      have hzzF : z * z ∣ M.f := by
        simpa only [sub_add_cancel] using dvd_add hzzSub hzzSq
      exact ((squarefree_iff_irreducible_sq_not_dvd_of_ne_zero
        M.ne_zero).mp M.squarefree z hz) hzzF
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨w, a,
    b * EuclideanDomain.gcdA (2 * D.v) w,
    b * EuclideanDomain.gcdB (2 * D.v) w, hw, ?_⟩
  rw [← hab, EuclideanDomain.gcd_eq_gcd_ab]
  ring

theorem ySubClass_mem_mumfordIdeal (u v : K[X]) :
    ySubClass M v ∈ mumfordIdeal M u v := by
  exact Ideal.subset_span (by simp)

theorem mumfordIdeal_mul_conj_integral (D : SemiMumford M) :
    mumfordIdeal M D.u D.v * mumfordIdeal M D.u (-D.v) =
      Ideal.span ({xClass M D.u} : Set (CoordinateRing M)) := by
  let I := mumfordIdeal M D.u D.v
  let J := mumfordIdeal M D.u (-D.v)
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro p hp q hq
    rw [Ideal.mem_span_singleton]
    obtain ⟨p₀, pY, hpEq⟩ := Ideal.mem_span_pair.mp hp
    obtain ⟨q₀, qY, hqEq⟩ := Ideal.mem_span_pair.mp hq
    obtain ⟨w, hw⟩ := D.curve_dvd
    refine ⟨p₀ * q₀ * xClass M D.u +
        p₀ * qY * ySubClass M (-D.v) +
        pY * q₀ * ySubClass M D.v +
        pY * qY * xClass M w, ?_⟩
    rw [← hpEq, ← hqEq]
    simp only [ySubClass, xClass_neg, sub_neg_eq_add] at hpEq hqEq ⊢
    have hgraph :
        (yClass M - xClass M D.v) * (yClass M + xClass M D.v) =
          xClass M D.u * xClass M w := by
      calc
        (yClass M - xClass M D.v) * (yClass M + xClass M D.v) =
            yClass M ^ 2 - xClass M D.v ^ 2 := by ring
        _ = xClass M M.f - xClass M (D.v ^ 2) := by
          rw [yClass_sq, xClass_pow]
        _ = xClass M (M.f - D.v ^ 2) := by rw [xClass_sub]
        _ = xClass M (D.u * w) := by rw [hw]
        _ = xClass M D.u * xClass M w := by rw [xClass_mul]
    linear_combination pY * qY * hgraph
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨w, a, b, c, hw, hbez⟩ := mumford_bezout M D
    have huI : xClass M D.u ∈ I :=
      xClass_mem_mumfordIdeal M D.u D.v
    have huJ : xClass M D.u ∈ J :=
      xClass_mem_mumfordIdeal M D.u (-D.v)
    have hvI : ySubClass M D.v ∈ I :=
      ySubClass_mem_mumfordIdeal M D.u D.v
    have hvJ : ySubClass M (-D.v) ∈ J :=
      ySubClass_mem_mumfordIdeal M D.u (-D.v)
    have hu2 : xClass M D.u * xClass M D.u ∈ I * J :=
      Ideal.mul_mem_mul huI huJ
    have huv : xClass M D.u * xClass M (2 * D.v) ∈ I * J := by
      have hp : xClass M D.u * ySubClass M (-D.v) ∈ I * J :=
        Ideal.mul_mem_mul huI hvJ
      have hm : ySubClass M D.v * xClass M D.u ∈ I * J :=
        Ideal.mul_mem_mul hvI huJ
      have hd := Ideal.sub_mem (I * J) hp hm
      convert hd using 1
      simp only [ySubClass, xClass_neg, sub_neg_eq_add, xClass_mul]
      change xClass M D.u * (2 * xClass M D.v) =
        xClass M D.u * (yClass M + xClass M D.v) -
          (yClass M - xClass M D.v) * xClass M D.u
      ring
    have huw : xClass M D.u * xClass M w ∈ I * J := by
      have hg : ySubClass M D.v * ySubClass M (-D.v) ∈ I * J :=
        Ideal.mul_mem_mul hvI hvJ
      convert hg using 1
      simp only [ySubClass, xClass_neg, sub_neg_eq_add]
      calc
        xClass M D.u * xClass M w = xClass M (D.u * w) := by
          rw [xClass_mul]
        _ = xClass M (M.f - D.v ^ 2) := by rw [hw]
        _ = xClass M M.f - xClass M (D.v ^ 2) := by rw [xClass_sub]
        _ = yClass M ^ 2 - xClass M D.v ^ 2 := by
          rw [yClass_sq, xClass_pow]
        _ = (yClass M - xClass M D.v) *
            (yClass M + xClass M D.v) := by ring
    have ha : xClass M a * (xClass M D.u * xClass M D.u) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass M a) hu2
    have hb : xClass M b *
        (xClass M D.u * xClass M (2 * D.v)) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass M b) huv
    have hc : xClass M c * (xClass M D.u * xClass M w) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass M c) huw
    have hsum := Ideal.add_mem (I * J) (Ideal.add_mem (I * J) ha hb) hc
    have heq :
        xClass M a * (xClass M D.u * xClass M D.u) +
            xClass M b * (xClass M D.u * xClass M (2 * D.v)) +
            xClass M c * (xClass M D.u * xClass M w) =
          xClass M D.u := by
      calc
        _ = xClass M D.u *
            xClass M (a * D.u + b * (2 * D.v) + c * w) := by
              simp only [xClass_add, xClass_mul]
              ring
        _ = xClass M D.u * 1 := by rw [hbez, xClass_one]
        _ = xClass M D.u := mul_one _
    rw [heq] at hsum
    exact hsum

theorem mumfordIdeal_mul_conj_fractional (D : SemiMumford M) :
    (mumfordIdeal M D.u D.v :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) *
      (mumfordIdeal M D.u (-D.v) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      (Ideal.span ({xClass M D.u} : Set (CoordinateRing M)) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
  rw [← coeIdeal_mul, mumfordIdeal_mul_conj_integral]

def mumfordIdealUnit (D : SemiMumford M) : InvFrac M :=
  Units.mkOfMulEqOne
    (mumfordIdeal M D.u D.v :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))
    ((mumfordIdeal M D.u (-D.v) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) *
      (Ideal.span ({xClass M D.u} : Set (CoordinateRing M)) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))⁻¹)
    (by
      rw [← mul_assoc, mumfordIdeal_mul_conj_fractional]
      exact FractionalIdeal.coe_ideal_span_singleton_mul_inv
        (FunctionField M) (xClass_ne_zero M D.u_monic.ne_zero))

@[simp] theorem coe_mumfordIdealUnit (D : SemiMumford M) :
    (mumfordIdealUnit M D :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      mumfordIdeal M D.u D.v := rfl

end

end MazurProof.SexticMumford

end
end

-- module FLT.Assumptions.MazurProof.SexticOrientedPic
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticOrientedPic =====
section

/-!
# The concrete oriented Picard group of a smooth sextic

The affine coordinate ring omits the two points at infinity.  An
`InfinityOrder` supplies the order at the chosen point before quotienting by
principal fractional ideals.  This file packages balanced Mumford data into
that oriented quotient for an arbitrary smooth monic sextic model.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : Model K) (O : InfinityOrder M)

/-- The oriented Picard group attached to the affine sextic and the chosen
order at infinity. -/
abbrev ConcretePic : Type u :=
  OrientedPic M O

/-- The oriented invertible fractional ideal represented by balanced Mumford
data. -/
def mumfordRaw (D : Mumford M) : OrientedFrac M :=
  (mumfordIdealUnit M D.toSemi,
    Multiplicative.ofAdd ((D.nInf : ℤ) - 1))

/-- The oriented Picard class of a balanced Mumford representative. -/
def classOf (D : Mumford M) : ConcretePic M O :=
  Additive.ofMul <|
    QuotientGroup.mk'
      (principalOriented M O).range
      (mumfordRaw M D)

theorem classOf_eq_iff (D₁ D₂ : Mumford M) :
    classOf M O D₁ = classOf M O D₂ ↔
      ∃ α : (FunctionField M)ˣ,
        mumfordIdealUnit M D₁.toSemi *
              toPrincipalIdeal (CoordinateRing M) (FunctionField M) α =
            mumfordIdealUnit M D₂.toSemi ∧
        Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) * O.ordPlus α =
            Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1) := by
  change QuotientGroup.mk'
      (principalOriented M O).range
        (mumfordRaw M D₁) =
      QuotientGroup.mk'
      (principalOriented M O).range
        (mumfordRaw M D₂) ↔ _
  rw [QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, hz, hmul⟩
    obtain ⟨α, rfl⟩ := MonoidHom.mem_range.mp hz
    refine ⟨α, ?_, ?_⟩
    · exact congrArg Prod.fst hmul
    · exact congrArg Prod.snd hmul
  · rintro ⟨α, hIdeal, hInf⟩
    refine ⟨principalOriented M O α,
      MonoidHom.mem_range.mpr ⟨α, rfl⟩, ?_⟩
    exact Prod.ext hIdeal hInf

theorem zero_mumfordIdeal :
    mumfordIdeal M (zero M).u (zero M).v = ⊤ := by
  rw [zero_u, zero_v, mumfordIdeal]
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span (by simp [xClass_one])

theorem mumfordIdealUnit_zero :
    mumfordIdealUnit M (zero M).toSemi = 1 := by
  apply Units.ext
  change (mumfordIdeal M 1 0 :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) = 1
  rw [show mumfordIdeal M 1 0 = ⊤ from zero_mumfordIdeal M]
  rfl

@[simp] theorem classOf_zero : classOf M O (zero M) = 0 := by
  change Additive.ofMul
      (QuotientGroup.mk'
        (principalOriented M O).range
        (mumfordRaw M (zero M))) = 0
  have hraw : mumfordRaw M (zero M) = 1 := by
    apply Prod.ext
    · exact mumfordIdealUnit_zero M
    · simp [mumfordRaw]
  rw [hraw, map_one]
  rfl

end

end MazurProof.SexticMumford

end
end

-- module FLT.Assumptions.MazurProof.SexticMumfordNorm
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordNorm =====
section

/-!
# Structural identities for the quadratic norm

The hyperelliptic norm is multiplicative, fixes the polynomial subring, and
can be read off from the two canonical coefficients.  These facts are kept
separate from any curve-specific degree calculation.
-/

open Polynomial

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

theorem xClass_injective (M : Model K) :
    Function.Injective (xClass M) := by
  intro p q hpq
  by_contra hne
  have hsub : p - q ≠ 0 := sub_ne_zero.mpr hne
  exact xClass_ne_zero M hsub (by
    rw [xClass_sub, hpq, sub_self])

@[simp] theorem norm_xClass (M : Model K) (p : K[X]) :
    norm M (xClass M p) = xClass M (p ^ 2) := by
  calc
    norm M (xClass M p) = xClass M p * xClass M p := by
      simp only [norm, conjugate_xClass]
    _ = xClass M (p * p) := (xClass_mul M p p).symm
    _ = xClass M (p ^ 2) := by rw [pow_two]

theorem norm_eq_xClass_coeff (M : Model K) (z : CoordinateRing M) :
    norm M z =
      xClass M
        ((coeff0 M z) ^ 2 - (coeffY M z) ^ 2 * M.f) := by
  conv_lhs =>
    rw [← recompose M z]
  exact norm_recompose M (coeff0 M z) (coeffY M z)

@[simp] theorem coeffY_xClass_mul (M : Model K)
    (a : K[X]) (z : CoordinateRing M) :
    coeffY M (xClass M a * z) = a * coeffY M z := by
  rw [show xClass M a =
    algebraMap K[X] (CoordinateRing M) a from rfl]
  rw [← Algebra.smul_def, map_smul]
  rfl

@[simp] theorem coeffY_ySubClass (M : Model K) (v : K[X]) :
    coeffY M (ySubClass M v) = 1 := by
  simp [ySubClass]

theorem dvd_of_xClass_mul_ySubClass_mem_span
    (M : Model K) (u a v : K[X])
    (h : xClass M a * ySubClass M v ∈
      Ideal.span ({xClass M u} : Set (CoordinateRing M))) :
    u ∣ a := by
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨t, ht⟩ := h
  refine ⟨coeffY M t, ?_⟩
  have hc := congrArg (coeffY M) ht
  rw [coeffY_xClass_mul, coeffY_ySubClass, mul_one,
    coeffY_xClass_mul] at hc
  exact hc

theorem u_dvd_of_scaled_mumfordIdeal_eq
    (M : Model K) (u₁ v₁ u₂ v₂ : K[X])
    (h :
      mumfordIdeal M u₁ v₁ *
          Ideal.span ({xClass M u₂} : Set (CoordinateRing M)) =
        mumfordIdeal M u₂ v₂ *
          Ideal.span ({xClass M u₁} : Set (CoordinateRing M))) :
    u₁ ∣ u₂ := by
  have hyv :
      ySubClass M v₁ ∈ mumfordIdeal M u₁ v₁ :=
    Ideal.subset_span (by simp)
  have hu :
      xClass M u₂ ∈
        Ideal.span ({xClass M u₂} : Set (CoordinateRing M)) :=
    Ideal.subset_span (by simp)
  have hmem :
      ySubClass M v₁ * xClass M u₂ ∈
        mumfordIdeal M u₁ v₁ *
          Ideal.span ({xClass M u₂} : Set (CoordinateRing M)) :=
    Ideal.mul_mem_mul hyv hu
  rw [h] at hmem
  have hspan :
      xClass M u₂ * ySubClass M v₁ ∈
        Ideal.span ({xClass M u₁} : Set (CoordinateRing M)) := by
    rw [mul_comm]
    exact Ideal.mul_le_right hmem
  exact dvd_of_xClass_mul_ySubClass_mem_span M u₁ u₂ v₁ hspan

end

end MazurProof.SexticMumford

end
end

-- module FLT.Assumptions.MazurProof.SexticMumfordRepresentative
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordRepresentative =====
section

/-!
# Integral representatives of oriented sextic Picard classes

The balanced Mumford theorem has two logically separate steps.

1. Clear the denominator of an arbitrary invertible fractional ideal.
2. Reduce the resulting integral ideal to a Mumford ideal of degree at most
   the genus.

This file proves the first step for every oriented Picard class and proves
the quadratic Hermite normal form for every primitive integral ideal.  It
uses only structural fractional-ideal and PID theorems, and therefore does
not enumerate ideal classes.  The final theorem isolates balanced reduction
as the exact remaining surjectivity criterion for `classOf`.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : Model K) (O : InfinityOrder M)

set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
set_option maxHeartbeats 2000000 in
/-- An oriented representative whose finite component is an integral ideal.
The unit remembers that this ideal is invertible as a fractional ideal. -/
structure IntegralOrientedRep where
  ideal : Ideal (CoordinateRing M)
  unit : InvFrac M
  coe_unit :
    (unit :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) = ideal
  atInfinity : ℤ

namespace IntegralOrientedRep

/-- The raw oriented fractional ideal underlying an integral representative. -/
def raw (R : IntegralOrientedRep M) : OrientedFrac M :=
  (R.unit, Multiplicative.ofAdd R.atInfinity)

/-- The oriented Picard class of an integral representative. -/
def picClass (R : IntegralOrientedRep M) : ConcretePic M O :=
  Additive.ofMul <|
    QuotientGroup.mk' (principalOriented M O).range (R.raw M)

theorem ideal_ne_bot (R : IntegralOrientedRep M) : R.ideal ≠ ⊥ := by
  intro h
  have hzero :
      (R.unit :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) = 0 := by
    rw [R.coe_unit, h]
    rfl
  exact R.unit.ne_zero hzero

theorem ideal_isUnit (R : IntegralOrientedRep M) :
    IsUnit
      (R.ideal :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
  exact ⟨R.unit, R.coe_unit⟩

end IntegralOrientedRep

/-- Contract an integral ideal from the quadratic coordinate ring to its
polynomial subring. -/
def idealContraction (J : Ideal (CoordinateRing M)) : Ideal K[X] :=
  J.comap (xClassHom M)

/-- A nonzero ideal has nonzero contraction to `K[X]`.  The structural
reason is that the quadratic norm of any nonzero ideal element is a nonzero
polynomial lying in the contraction. -/
theorem idealContraction_ne_bot (J : Ideal (CoordinateRing M))
    (hJ : J ≠ ⊥) : idealContraction M J ≠ ⊥ := by
  obtain ⟨z, hzJ, hz⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hJ
  let p : K[X] :=
    (coeff0 M z) ^ 2 - (coeffY M z) ^ 2 * M.f
  have hconj : conjugate M z ≠ 0 := by
    intro hc
    apply hz
    calc
      z = conjugate M (conjugate M z) :=
        (conjugate_involutive M z).symm
      _ = 0 := by rw [hc, map_zero]
  have hnorm : norm M z ≠ 0 :=
    mul_ne_zero hz hconj
  have hp : p ≠ 0 := by
    intro hp
    apply hnorm
    rw [norm_eq_xClass_coeff]
    change xClass M p = 0
    rw [hp, xClass_zero]
  intro hbot
  have hpmem : p ∈ idealContraction M J := by
    change xClass M p ∈ J
    rw [← norm_eq_xClass_coeff]
    exact J.mul_mem_right (conjugate M z) hzJ
  rw [hbot, Ideal.mem_bot] at hpmem
  exact hp hpmem

/-- The canonical monic generator of the contraction of an integral ideal
to `K[X]`. -/
def contractionGenerator (J : Ideal (CoordinateRing M)) : K[X] := by
  classical
  exact normalize
    (Submodule.IsPrincipal.generator (idealContraction M J))

theorem contractionGenerator_monic (J : Ideal (CoordinateRing M))
    (hJ : J ≠ ⊥) : (contractionGenerator M J).Monic := by
  classical
  unfold contractionGenerator
  apply Polynomial.monic_normalize
  intro hgen
  exact idealContraction_ne_bot M J hJ
    ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero
      (idealContraction M J)).mpr hgen)

theorem span_contractionGenerator (J : Ideal (CoordinateRing M)) :
    Ideal.span ({contractionGenerator M J} : Set K[X]) =
      idealContraction M J := by
  classical
  unfold contractionGenerator
  calc
    Ideal.span
        ({normalize
          (Submodule.IsPrincipal.generator
            (idealContraction M J))} : Set K[X]) =
        Ideal.span
          ({Submodule.IsPrincipal.generator
            (idealContraction M J)} : Set K[X]) := by
      apply Ideal.span_singleton_eq_span_singleton.mpr
      exact (associated_normalize
        (Submodule.IsPrincipal.generator
          (idealContraction M J))).symm
    _ = idealContraction M J :=
      Ideal.span_singleton_generator (idealContraction M J)

theorem xClass_contractionGenerator_mem
    (J : Ideal (CoordinateRing M)) :
    xClass M (contractionGenerator M J) ∈ J := by
  change contractionGenerator M J ∈ idealContraction M J
  rw [← span_contractionGenerator M J]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- If an integral ideal has contraction `(u)` and contains one graph
generator `Y-v`, then it is exactly the corresponding Mumford ideal.  This
is the quadratic Hermite-normal-form step, proved from the rank-two
coefficient decomposition. -/
theorem mumfordIdeal_eq_of_contraction_eq_span_of_ySub_mem
    (J : Ideal (CoordinateRing M)) (u v : K[X])
    (hcontraction :
      idealContraction M J = Ideal.span ({u} : Set K[X]))
    (hgraph : ySubClass M v ∈ J) :
    mumfordIdeal M u v = J := by
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change u ∈ idealContraction M J
      rw [hcontraction]
      exact Ideal.subset_span (Set.mem_singleton _)
    · exact hgraph
  · intro w hw
    let q : K[X] := coeffY M w
    let r : CoordinateRing M :=
      w - xClass M q * ySubClass M v
    have hrJ : r ∈ J :=
      J.sub_mem hw (J.mul_mem_left (xClass M q) hgraph)
    have hrY : coeffY M r = 0 := by
      simp [r, q]
    have hrRecompose : xClass M (coeff0 M r) = r := by
      simpa [hrY] using recompose M r
    have hrContract :
        coeff0 M r ∈ idealContraction M J := by
      change xClass M (coeff0 M r) ∈ J
      rw [hrRecompose]
      exact hrJ
    rw [hcontraction, Ideal.mem_span_singleton] at hrContract
    obtain ⟨t, ht⟩ := hrContract
    have hrMumford : r ∈ mumfordIdeal M u v := by
      rw [← hrRecompose, ht, xClass_mul, mul_comm]
      exact Ideal.mul_mem_left _ (xClass M t)
        (xClass_mem_mumfordIdeal M u v)
    have hgraphMumford :
        xClass M q * ySubClass M v ∈ mumfordIdeal M u v :=
      Ideal.mul_mem_left _ (xClass M q)
        (Ideal.subset_span (by simp))
    have hwdecomp :
        w = r + xClass M q * ySubClass M v := by
      simp [r]
    rw [hwdecomp]
    exact Ideal.add_mem _ hrMumford hgraphMumford

/-- An integral ideal is primitive when some element has `Y`-coefficient
one.  This is the exact algebraic hypothesis needed to put it in Mumford
graph form. -/
def IdealIsPrimitive (J : Ideal (CoordinateRing M)) : Prop :=
  ∃ z ∈ J, coeffY M z = 1

/-- A primitive nonzero integral ideal has a semireduced Mumford
presentation.  The `u`-polynomial is the canonical contraction generator,
and `v` is reduced modulo `u`.  No degree bound or class enumeration enters
the proof. -/
theorem exists_semiMumford_of_primitive
    (J : Ideal (CoordinateRing M)) (hJ : J ≠ ⊥)
    (hprimitive : IdealIsPrimitive M J) (n : ℤ) :
    ∃ D : SemiMumford M,
      mumfordIdeal M D.u D.v = J ∧
      D.u = contractionGenerator M J ∧
      D.nInf = n := by
  obtain ⟨z, hzJ, hzY⟩ := hprimitive
  let u : K[X] := contractionGenerator M J
  let v0 : K[X] := -(coeff0 M z)
  let v : K[X] := v0 % u
  have huMonic : u.Monic :=
    contractionGenerator_monic M J hJ
  have hu : u ≠ 0 := huMonic.ne_zero
  have hcontraction :
      idealContraction M J = Ideal.span ({u} : Set K[X]) :=
    (span_contractionGenerator M J).symm
  have hgraph0 : ySubClass M v0 = z := by
    calc
      ySubClass M v0 =
          xClass M (coeff0 M z) +
            xClass M (coeffY M z) * yClass M := by
              simp [ySubClass, v0, hzY]
              ring
      _ = z := recompose M z
  have hvdecomp : v + u * (v0 / u) = v0 :=
    EuclideanDomain.mod_add_div v0 u
  have hgraph : ySubClass M v ∈ J := by
    have hpoly : v0 - v = u * (v0 / u) := by
      calc
        v0 - v = (v + u * (v0 / u)) - v :=
          congrArg (fun t : K[X] => t - v) hvdecomp.symm
        _ = u * (v0 / u) := by ring
    have hmultiple :
        xClass M (v0 - v) ∈ J := by
      rw [hpoly, xClass_mul, mul_comm]
      exact J.mul_mem_left (xClass M (v0 / u))
        (xClass_contractionGenerator_mem M J)
    have heq :
        ySubClass M v =
          ySubClass M v0 + xClass M (v0 - v) := by
      simp [ySubClass, xClass_sub]
    rw [heq]
    exact J.add_mem (hgraph0 ▸ hzJ) hmultiple
  have hcurve : u ∣ M.f - v ^ 2 := by
    have hprod :
        ySubClass M v * (yClass M + xClass M v) =
          xClass M (M.f - v ^ 2) := by
      simp only [ySubClass]
      calc
        (yClass M - xClass M v) *
            (yClass M + xClass M v) =
            yClass M ^ 2 - xClass M v ^ 2 := by ring
        _ = xClass M M.f - xClass M v ^ 2 := by
          rw [yClass_sq]
        _ = xClass M (M.f - v ^ 2) := by
          rw [xClass_sub, xClass_pow]
    have hmem :
        M.f - v ^ 2 ∈ idealContraction M J := by
      change xClass M (M.f - v ^ 2) ∈ J
      rw [← hprod]
      exact J.mul_mem_right (yClass M + xClass M v) hgraph
    rw [hcontraction, Ideal.mem_span_singleton] at hmem
    exact hmem
  let D : SemiMumford M :=
    { u := u
      v := v
      nInf := n
      u_monic := huMonic
      v_reduced := by
        rw [Polynomial.mod_eq_self_iff hu]
        exact EuclideanDomain.mod_lt _ hu
      curve_dvd := hcurve }
  refine ⟨D, ?_, rfl, rfl⟩
  exact mumfordIdeal_eq_of_contraction_eq_span_of_ySub_mem
    M J u v hcontraction hgraph

/-- Every raw oriented fractional ideal is equivalent, modulo a principal
oriented ideal, to one with an integral finite component. -/
theorem exists_integralRep_of_raw (I : InvFrac M)
    (n : Multiplicative ℤ) :
    ∃ R : IntegralOrientedRep M,
      QuotientGroup.mk' (principalOriented M O).range (I, n) =
        Additive.toMul (R.picClass M O) := by
  obtain ⟨a, J, ha, hI⟩ := invFrac_exists_integral_scaling M I
  have haMap :
      algebraMap (CoordinateRing M) (FunctionField M) a ≠ 0 := by
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (show a ∈ (CoordinateRing M)⁰ from
        mem_nonZeroDivisors_iff_ne_zero.mpr ha)
  let alpha : (FunctionField M)ˣ :=
    Units.mk0
      (algebraMap (CoordinateRing M) (FunctionField M) a) haMap
  let U : InvFrac M :=
    I * toPrincipalIdeal (CoordinateRing M) (FunctionField M) alpha
  have hU :
      (U :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) = J := by
    simp only [U, Units.val_mul, coe_toPrincipalIdeal, alpha,
      Units.val_mk0]
    rw [hI]
    calc
      (FractionalIdeal.spanSingleton (CoordinateRing M)⁰
            (algebraMap (CoordinateRing M) (FunctionField M) a)⁻¹ *
          (J :
            FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))) *
          FractionalIdeal.spanSingleton (CoordinateRing M)⁰
            (algebraMap (CoordinateRing M) (FunctionField M) a) =
        (FractionalIdeal.spanSingleton (CoordinateRing M)⁰
              (algebraMap (CoordinateRing M) (FunctionField M) a)⁻¹ *
            FractionalIdeal.spanSingleton (CoordinateRing M)⁰
              (algebraMap (CoordinateRing M) (FunctionField M) a)) *
          (J :
            FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
              ac_rfl
      _ = J := by
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
        simp [haMap]
  let R : IntegralOrientedRep M :=
    { ideal := J
      unit := U
      coe_unit := hU
      atInfinity :=
        Multiplicative.toAdd (n * O.ordPlus alpha) }
  refine ⟨R, ?_⟩
  change
    QuotientGroup.mk' (principalOriented M O).range (I, n) =
      QuotientGroup.mk' (principalOriented M O).range
        (U, Multiplicative.ofAdd R.atInfinity)
  have hprincipal :
      QuotientGroup.mk' (principalOriented M O).range
          (principalOriented M O alpha) = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff
      (principalOriented M O alpha)).2
      (MonoidHom.mem_range.mpr ⟨alpha, rfl⟩)
  calc
    QuotientGroup.mk' (principalOriented M O).range (I, n) =
        QuotientGroup.mk' (principalOriented M O).range
          ((I, n) * principalOriented M O alpha) := by
            rw [map_mul, hprincipal]; exact (mul_one (QuotientGroup.mk' (principalOriented M O).range (I, n))).symm
    _ = QuotientGroup.mk' (principalOriented M O).range
          (U, Multiplicative.ofAdd R.atInfinity) := by
            rfl

/-- Every oriented Picard class has an integral invertible-ideal
representative.  No Dedekind-domain or class-number hypothesis is used. -/
theorem exists_integralRepresentative (c : ConcretePic M O) :
    ∃ R : IntegralOrientedRep M, R.picClass M O = c := by
  change
    ∃ R : IntegralOrientedRep M,
      Additive.toMul (R.picClass M O) = Additive.toMul c
  obtain ⟨x, hx⟩ :=
    QuotientGroup.mk'_surjective (principalOriented M O).range
      (Additive.toMul c)
  obtain ⟨R, hR⟩ :=
    exists_integralRep_of_raw M O x.1 x.2
  exact ⟨R, hR.symm.trans hx⟩

end

end MazurProof.SexticMumford

end
end

-- module FLT.Assumptions.MazurProof.N13IntegralModelContraction
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralModelContraction =====
section

/-!
# Vertical localization and ideal contraction for the N13 integral model

The affine coordinate ring of the N13 generic fibre is obtained from the
integral good-model coordinate ring by inverting only the nonzero scalars of
`ℤ₂`.  The proof uses the rank-two normal form `p(x) + q(x)y`: a common
scalar denominator clears the two coefficient polynomials simultaneously.

Consequently every ideal on the generic affine fibre has a canonical
contraction to the integral model, and extending this contraction recovers
the original ideal exactly.  The contraction is vertically saturated.  This
is the algebraic integral-model layer needed before taking a reflexive hull
or lifting a section; it does not assert that the contracted ideal is already
invertible on the two-dimensional integral surface.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13IntegralModelContraction

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13TwoAdicCoordinateBaseChange.R₂

abbrev Q₂ : Type :=
  N13TwoAdicCoordinateBaseChange.Q₂

abbrev IntegralRing : Type :=
  N13TwoAdicCoordinateBaseChange.IntegralRing

abbrev GoodRing : Type :=
  N13TwoAdicCoordinateBaseChange.GoodRing

abbrev RationalRing : Type :=
  N13GoodSexticCoordinateEquiv.SexticRing (K := Q₂)

abbrev Pic : Type :=
  SexticMumford.ConcretePic
    (N13Mumford.model Q₂)
    (N13Infinity.positiveInfinityOrder Q₂)

abbrev IntegralOrientedRep : Type :=
  SexticMumford.IntegralOrientedRep
    (N13Mumford.model Q₂)

/-- The integral good model maps to its generalized generic fibre. -/
def integralToGood : IntegralRing →+* GoodRing :=
  N13TwoAdicCoordinateBaseChange.extendCoordinate

local instance integralGoodAlgebra :
    Algebra IntegralRing GoodRing :=
  integralToGood.toAlgebra

/-- The vertical multiplicative set consists exactly of nonzero `ℤ₂`
scalars inside the integral coordinate ring. -/
def verticalScalars : Submonoid IntegralRing :=
  (nonZeroDivisors R₂).map
    (algebraMap R₂ IntegralRing)

local instance polynomialAlgebra :
    Algebra R₂[X] Q₂[X] :=
  Polynomial.algebra R₂ Q₂

local instance polynomialLocalization :
    IsLocalization
      ((nonZeroDivisors R₂).map
        (Polynomial.C : R₂ →+* R₂[X]).toMonoidHom)
      Q₂[X] :=
  Polynomial.isLocalization (nonZeroDivisors R₂) Q₂

@[simp] theorem integralToGood_algebraMap
    (a : R₂) :
    integralToGood (algebraMap R₂ IntegralRing a) =
      algebraMap Q₂ GoodRing
        (N13TwoAdicCoordinateBaseChange.coeffMap a) := by
  change
    N13TwoAdicCoordinateBaseChange.extendCoordinate
        (N13GeneralizedMumfordIntegral.xClass (C a)) =
      N13GeneralizedMumfordIntegral.xClass
        (C (N13TwoAdicCoordinateBaseChange.coeffMap a))
  rw [N13TwoAdicCoordinateBaseChange.extend_xClass]
  simp [N13TwoAdicCoordinateBaseChange.mapPoly,
    N13TwoAdicCoordinateBaseChange.coeffMap]

/-- Inverting the vertical nonzero scalars produces the generalized generic
fibre coordinate ring. -/
theorem goodRing_isLocalization :
    IsLocalization verticalScalars GoodRing := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro s
    have hs := s.property
    change
      ∃ r : R₂, r ∈ nonZeroDivisors R₂ ∧
        algebraMap R₂ IntegralRing r =
          (s : IntegralRing) at hs
    obtain ⟨r, hr, hs⟩ := hs
    change IsUnit (integralToGood (s : IntegralRing))
    rw [← hs, integralToGood_algebraMap]
    have hr0 :
        N13TwoAdicCoordinateBaseChange.coeffMap r ≠ 0 := by
      change algebraMap R₂ Q₂ r ≠ 0
      simpa using
        (IsFractionRing.injective R₂ Q₂).ne
          (mem_nonZeroDivisors_iff_ne_zero.mp hr)
    exact IsUnit.map (algebraMap Q₂ GoodRing)
      (isUnit_iff_ne_zero.mpr hr0)
  · intro z
    obtain ⟨p, q, d, hp, hq⟩ :=
      IsLocalization.surj₂
        ((nonZeroDivisors R₂).map
          (Polynomial.C : R₂ →+* R₂[X]).toMonoidHom)
        Q₂[X]
        (N13GeneralizedMumfordIntegral.coeff0 z)
        (N13GeneralizedMumfordIntegral.coeffY z)
    obtain ⟨r, hr, hd⟩ := d.property
    change C r = (d : R₂[X]) at hd
    rw [← hd] at hp hq
    rw [Polynomial.algebraMap_def] at hp hq
    have hp0 :
        N13GeneralizedMumfordIntegral.coeff0 z *
            C (N13TwoAdicCoordinateBaseChange.coeffMap r) =
          N13TwoAdicCoordinateBaseChange.mapPoly p := by
      simpa [N13TwoAdicCoordinateBaseChange.mapPoly,
        N13TwoAdicCoordinateBaseChange.coeffMap,
        N13TwoAdicMumfordTransport.mapPoly,
        N13TwoAdicMumfordTransport.coeffMap] using hp
    have hq0 :
        N13GeneralizedMumfordIntegral.coeffY z *
            C (N13TwoAdicCoordinateBaseChange.coeffMap r) =
          N13TwoAdicCoordinateBaseChange.mapPoly q := by
      simpa [N13TwoAdicCoordinateBaseChange.mapPoly,
        N13TwoAdicCoordinateBaseChange.coeffMap,
        N13TwoAdicMumfordTransport.mapPoly,
        N13TwoAdicMumfordTransport.coeffMap] using hq
    let numerator : IntegralRing :=
      N13GeneralizedMumfordIntegral.xClass p +
        N13GeneralizedMumfordIntegral.xClass q *
          N13GeneralizedMumfordIntegral.yClass
    let denominator : verticalScalars :=
      ⟨algebraMap R₂ IntegralRing r,
        ⟨r, hr, rfl⟩⟩
    refine ⟨⟨numerator, denominator⟩, ?_⟩
    change
      z * integralToGood (denominator : IntegralRing) =
        integralToGood numerator
    dsimp only [denominator, numerator]
    rw [← N13GeneralizedMumfordIntegral.recompose z]
    rw [integralToGood_algebraMap]
    unfold integralToGood
    simp only [map_add, map_mul,
      N13TwoAdicCoordinateBaseChange.extend_xClass,
      N13TwoAdicCoordinateBaseChange.extend_yClass]
    have hscalar :
        algebraMap Q₂ GoodRing
            (N13TwoAdicCoordinateBaseChange.coeffMap r) =
          N13GeneralizedMumfordIntegral.xClass
            (C (N13TwoAdicCoordinateBaseChange.coeffMap r)) :=
      rfl
    rw [hscalar]
    have hp' := congrArg
      (N13GeneralizedMumfordIntegral.xClass (R := Q₂)) hp0
    have hq' := congrArg
      (N13GeneralizedMumfordIntegral.xClass (R := Q₂)) hq0
    simp only [
      N13GeneralizedMumfordIntegral.xClass_mul] at hp' hq'
    calc
      (N13GeneralizedMumfordIntegral.xClass
              (N13GeneralizedMumfordIntegral.coeff0 z) +
            N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeffY z) *
              N13GeneralizedMumfordIntegral.yClass) *
            N13GeneralizedMumfordIntegral.xClass
              (C (N13TwoAdicCoordinateBaseChange.coeffMap r)) =
          N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeff0 z) *
              N13GeneralizedMumfordIntegral.xClass
                (C (N13TwoAdicCoordinateBaseChange.coeffMap r)) +
            (N13GeneralizedMumfordIntegral.xClass
                  (N13GeneralizedMumfordIntegral.coeffY z) *
                N13GeneralizedMumfordIntegral.xClass
                  (C (N13TwoAdicCoordinateBaseChange.coeffMap r))) *
              N13GeneralizedMumfordIntegral.yClass := by ring
      _ =
          N13GeneralizedMumfordIntegral.xClass
              (N13TwoAdicCoordinateBaseChange.mapPoly p) +
            N13GeneralizedMumfordIntegral.xClass
                (N13TwoAdicCoordinateBaseChange.mapPoly q) *
              N13GeneralizedMumfordIntegral.yClass := by
            rw [hp', hq']
  · intro x y hxy
    exact
      ⟨1, by
        simpa using
          N13TwoAdicCoordinateBaseChange.extendCoordinate_injective hxy⟩

local instance goodRingLocalization :
    IsLocalization verticalScalars GoodRing :=
  goodRing_isLocalization

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra

/-- Completion of the square is an equivalence over the integral model. -/
def goodToSextic :
    GoodRing ≃ₐ[IntegralRing] RationalRing where
  __ :=
    N13GoodSexticCoordinateEquiv.coordinateRingEquiv
      (K := Q₂)
  commutes' _ := rfl

/-- The standard sextic generic-fibre coordinate ring is the same vertical
localization. -/
theorem rationalRing_isLocalization :
    IsLocalization verticalScalars RationalRing :=
  IsLocalization.isLocalization_of_algEquiv
    verticalScalars goodToSextic

local instance rationalRingLocalization :
    IsLocalization verticalScalars RationalRing :=
  rationalRing_isLocalization

/-- Canonical contraction of a generic-fibre ideal to the integral model. -/
def contractIdeal
    (J : Ideal RationalRing) :
    Ideal IntegralRing :=
  J.under IntegralRing

/-- Extending the canonical contraction recovers the generic-fibre ideal
exactly. -/
theorem map_contractIdeal
    (J : Ideal RationalRing) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (contractIdeal J) =
      J := by
  exact IsLocalization.map_under
    verticalScalars RationalRing J

/-- The contracted ideal is saturated with respect to every nonzero
vertical scalar. -/
theorem contractIdeal_vertical_saturated
    (J : Ideal RationalRing)
    {a : IntegralRing}
    (r : R₂) (hr : r ≠ 0)
    (ha :
      algebraMap R₂ IntegralRing r * a ∈
        contractIdeal J) :
    a ∈ contractIdeal J := by
  change
    N13TwoAdicCoordinateBaseChange.integralToSextic a ∈ J
  change
    N13TwoAdicCoordinateBaseChange.integralToSextic
        (algebraMap R₂ IntegralRing r * a) ∈ J at ha
  rw [map_mul] at ha
  let s : verticalScalars :=
    ⟨algebraMap R₂ IntegralRing r,
      ⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr, rfl⟩⟩
  have hs :
      IsUnit
        (algebraMap IntegralRing RationalRing s) :=
    IsLocalization.map_units RationalRing s
  exact (Ideal.unit_mul_mem_iff_mem J hs).mp ha

end

end MazurProof.N13IntegralModelContraction

end
end

-- module FLT.Assumptions.MazurProof.N13IntegralFractionalHull
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralFractionalHull =====
section

/-!
# Divisorial hulls on the N13 integral model

The N13 generic affine ring is the vertical localization of its integral
good-model ring.  This file proves that the common function field is also the
fraction field of the integral model and that vertical extension commutes with
inverse fractional ideals.

The reverse inclusion is the substantive point: a fractional ideal over the
Noetherian integral model has finitely many generators, so one vertical scalar
clears all denominators of their products with a generic inverse section.
Consequently the divisorial double inverse of a contracted invertible generic
ideal has exactly the original generic fibre.  No affine generator or
principality assumption is used.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13IntegralFractionalHull

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev IntegralRing : Type :=
  N13IntegralModelContraction.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing

abbrev FunctionField : Type :=
  N13Mumford.FunctionField
    N13IntegralModelContraction.Q₂

def integralToRational : IntegralRing →+* RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  integralToRational.toAlgebra

theorem integralToRational_injective :
    Function.Injective integralToRational := by
  exact
    (N13GoodSexticCoordinateEquiv.coordinateRingEquiv
      (K := N13IntegralModelContraction.Q₂)).injective.comp
      N13TwoAdicCoordinateBaseChange.extendCoordinate_injective

local instance integralRingDomain : IsDomain IntegralRing :=
  integralToRational_injective.isDomain integralToRational

local instance rationalRingLocalization :
    IsLocalization
      N13IntegralModelContraction.verticalScalars
      RationalRing :=
  N13IntegralModelContraction.rationalRing_isLocalization

/-- The function field of the generic fibre is also the fraction field of
the integral model. -/
theorem functionField_isFractionRing :
    IsFractionRing IntegralRing FunctionField := by
  let M := N13IntegralModelContraction.verticalScalars
  let N := nonZeroDivisors RationalRing
  have hloc :
      IsLocalization
          (N.comap (algebraMap IntegralRing RationalRing))
          FunctionField :=
    IsLocalization.localization_localization_isLocalization_of_has_all_units
      M N FunctionField (fun x hx => by
        change x ∈ nonZeroDivisors RationalRing
        rw [mem_nonZeroDivisors_iff_ne_zero]
        exact hx.ne_zero)
  have hsub :
      N.comap (algebraMap IntegralRing RationalRing) =
        nonZeroDivisors IntegralRing := by
    ext a
    change
      integralToRational a ∈ nonZeroDivisors RationalRing ↔
        a ∈ nonZeroDivisors IntegralRing
    simp only [mem_nonZeroDivisors_iff_ne_zero]
    simpa only [map_zero] using
      (integralToRational_injective.ne_iff
        (x := a) (y := 0))
  rw [hsub] at hloc
  exact hloc

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  functionField_isFractionRing

abbrev IntegralFractionalIdeal : Type :=
  FractionalIdeal IntegralRing⁰ FunctionField

abbrev RationalFractionalIdeal : Type :=
  FractionalIdeal RationalRing⁰ FunctionField

def nonZeroDivisors_le_comap :
    IntegralRing⁰ ≤
      RationalRing⁰.comap integralToRational :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
    integralToRational integralToRational_injective

/-- Extension of fractional ideals from the integral model to its generic
affine coordinate ring. -/
def extendFractional :
    IntegralFractionalIdeal →+* RationalFractionalIdeal :=
  FractionalIdeal.extendedHom'
    FunctionField nonZeroDivisors_le_comap

end

end MazurProof.N13IntegralFractionalHull

end
end

-- module FLT.Assumptions.MazurProof.N13IntegralGraphContraction
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralGraphContraction =====
section

/-!
# Exact contraction of integral N13 graph ideals

Coefficient extension and contraction already fix a smooth integral
generalized Mumford graph ideal.  Completion of the square is a coordinate
ring equivalence, so it cancels formally from a further extension and
contraction.  Hence the standard sextic graph contracts to the original
integral graph exactly.

This is a representative-level equality.  It does not construct an
integral graph from a generic Picard class.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13IntegralGraphContraction

noncomputable section

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev IntegralRing : Type :=
  N13IntegralModelContraction.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing

abbrev FunctionField : Type :=
  N13IntegralFractionalHull.FunctionField

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra

local instance integralRingDomain : IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

abbrev SmoothMumford₂ : Type :=
  N13GeneralizedMumfordReduction.SmoothMumford₂

abbrev SemiMumford₂ : Type :=
  N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂

/-- The integral graph ideal attached to generalized Mumford data. -/
def graphIdeal (D : SmoothMumford₂) : Ideal IntegralRing :=
  N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v

/-- The standard sextic graph ideal of smooth integral data. -/
def sexticIdeal
    (D : SmoothMumford₂) (nInf : ℤ) :
    Ideal RationalRing :=
  SexticMumford.mumfordIdeal
    (N13GoodSexticCoordinateEquiv.M
      (K := N13IntegralModelContraction.Q₂))
    (N13TwoAdicMumfordTransport.sexticSemi D nInf).u
    (N13TwoAdicMumfordTransport.sexticSemi D nInf).v

/-- The standard sextic generic graph attached to arbitrary integral
generalized Mumford data. -/
def sexticSemiIdeal
    (D : SemiMumford₂) (nInf : ℤ) :
    Ideal RationalRing :=
  SexticMumford.mumfordIdeal
    (N13GoodSexticCoordinateEquiv.M
      (K := N13IntegralModelContraction.Q₂))
    (N13TwoAdicMumfordTransport.sexticSemiOfSemi D nInf).u
    (N13TwoAdicMumfordTransport.sexticSemiOfSemi D nInf).v

end

end MazurProof.N13IntegralGraphContraction

end
end

-- module FLT.Assumptions.MazurProof.N13SpecialDualFrame
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialDualFrame =====
section

/-!
# The explicit special-fibre dual frame

For the selected nonspecial graph ideal `(X²+X,Y)`, three explicit primal
and multiplier-dual elements have evaluation sum one.  The only
denominator is `(Y+h)/(X²+X)`; its inverse-ideal membership follows
directly from the curve equation.

This is a symbolic certificate in the special affine coordinate ring.  It
does not use invertibility of the graph ideal and is therefore suitable as
the input relation for the two-chart lifting argument.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13SpecialDualFrame

noncomputable section

abbrev k : Type := N13GoodCoordinateRingTwo.K
abbrev A : Type := N13GoodCoordinateRingTwo.CoordinateRing
abbrev F : Type := N13GoodCoordinateRingTwo.FunctionField
abbrev Frac : Type := FractionalIdeal A⁰ F

def u : k[X] := X ^ 2 + X
def c : k[X] := X ^ 2 + X + 1

def I : Ideal A :=
  N13GoodCoordinateRingTwo.mumfordIdeal u 0

def uF : F :=
  algebraMap A F (N13GoodCoordinateRingTwo.xClass u)

def cF : F :=
  algebraMap A F (N13GoodCoordinateRingTwo.xClass c)

def x3F : F :=
  algebraMap A F (N13GoodCoordinateRingTwo.xClass (X ^ 3))

def yF : F :=
  algebraMap A F N13GoodCoordinateRingTwo.yClass

def hF : F :=
  algebraMap A F
    (N13GoodCoordinateRingTwo.xClass
      N13GoodCoordinateRingTwo.hPoly)

def quotientDual : F :=
  (yF + hF) / uF

/-- The three evaluations already lie in the special affine coordinate
ring, despite the denominator in the middle dual factor. -/
def product : Fin 3 → A :=
  ![
    N13GoodCoordinateRingTwo.xClass u *
      N13GoodCoordinateRingTwo.xClass (X ^ 3),
    N13GoodCoordinateRingTwo.xClass c *
      (N13GoodCoordinateRingTwo.yClass +
        N13GoodCoordinateRingTwo.xClass
          N13GoodCoordinateRingTwo.hPoly),
    N13GoodCoordinateRingTwo.yClass *
      N13GoodCoordinateRingTwo.xClass c
  ]

/-- The corresponding multiplier-dual factors. -/
def dual : Fin 3 → F :=
  ![x3F, quotientDual, cF]

end

end MazurProof.N13SpecialDualFrame

end
end

-- module FLT.Assumptions.MazurProof.N13SpecialQuotientBasis
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialQuotientBasis =====
section

/-!
# The literal basis of the fixed N13 special quotient

The selected special divisor has graph ideal `(X²+X,Y)`.  Evaluation on
that graph identifies its affine quotient with
`𝔽₂[X]/(X²+X)`.  The canonical monic power basis on the latter transports
back to the literal quotient basis `{1,x}`.

This file is only the fixed special-fibre endpoint.  It does not assert
that the contraction of an arbitrary generic Picard representative reduces
to this ideal.
-/

open Module
open Polynomial

namespace MazurProof.N13SpecialQuotientBasis

noncomputable section

abbrev k : Type :=
  N13GoodCoordinateRingTwo.K

abbrev A : Type :=
  N13GoodCoordinateRingTwo.CoordinateRing

/-- The fixed reduced smooth Mumford datum. -/
def specialData :
    N13GoodCoordinateRingTwo.SemiMumford :=
  N13GeneralizedMumfordReduction.reduceSmoothMumford
    N13AbelChartBase.baseSmoothMumford

@[simp] theorem specialData_u :
    specialData.u = (X ^ 2 + X : k[X]) :=
  N13AbelChartBase.reduce_baseSmoothMumford_u

@[simp] theorem specialData_v :
    specialData.v = 0 :=
  N13AbelChartBase.reduce_baseSmoothMumford_v

@[simp] theorem specialData_u_natDegree :
    specialData.u.natDegree = 2 := by
  rw [specialData_u]
  (compute_degree; norm_num)

/-- The fixed special graph ideal. -/
abbrev specialIdeal : Ideal A :=
  N13GoodCoordinateRingTwo.mumfordIdeal
    specialData.u specialData.v

/-- The monic quotient `k[X]/(u)` has its canonical power basis. -/
def residueBasis :
    Basis (Fin 2) k (AdjoinRoot specialData.u) :=
  (AdjoinRoot.powerBasis' specialData.u_monic).basis.reindex
    (finCongr (by
      change specialData.u.natDegree = 2
      exact specialData_u_natDegree))

theorem residueBasis_apply (i : Fin 2) :
    residueBasis i =
      AdjoinRoot.root specialData.u ^ (i : ℕ) := by
  change
    ((AdjoinRoot.powerBasis' specialData.u_monic).basis.reindex
        (finCongr specialData_u_natDegree)) i =
      AdjoinRoot.root specialData.u ^ (i : ℕ)
  rw [Basis.reindex_apply,
    PowerBasis.basis_eq_pow, finCongr_symm_apply, Fin.val_cast]
  rw [AdjoinRoot.powerBasis'_gen]

@[simp] theorem residueBasis_zero :
    residueBasis (0 : Fin 2) = 1 := by
  simp [residueBasis_apply]

@[simp] theorem residueBasis_one :
    residueBasis (1 : Fin 2) =
      AdjoinRoot.root specialData.u := by
  simp [residueBasis_apply]

/-- The graph-quotient equivalence respects the coefficient field. -/
def quotientAlgEquiv :
    (A ⧸ specialIdeal) ≃ₐ[k]
      N13GoodCoordinateRingTwo.MumfordResidue specialData :=
  by
    simpa only [A, k, specialIdeal] using
      N13GoodCoordinateRingTwo.mumfordQuotientAlgEquiv specialData

/-- Transport the polynomial quotient basis to the affine graph quotient. -/
def quotientBasis :
    Basis (Fin 2) k (A ⧸ specialIdeal) :=
  residueBasis.map
    quotientAlgEquiv.symm.toLinearEquiv

@[simp] theorem quotientBasis_zero :
    quotientBasis (0 : Fin 2) = 1 := by
  change quotientAlgEquiv.symm (residueBasis 0) = 1
  rw [residueBasis_zero]
  exact map_one quotientAlgEquiv.symm

@[simp] theorem quotientBasis_one :
    quotientBasis (1 : Fin 2) =
      Ideal.Quotient.mk specialIdeal
        (N13GoodCoordinateRingTwo.xClass X) := by
  change
    quotientAlgEquiv.symm (residueBasis 1) =
      Ideal.Quotient.mk specialIdeal
        (N13GoodCoordinateRingTwo.xClass X)
  rw [residueBasis_one]
  apply quotientAlgEquiv.injective
  rw [quotientAlgEquiv.apply_symm_apply]
  simp only [quotientAlgEquiv]
  change
    AdjoinRoot.root specialData.u =
      N13GoodCoordinateRingTwo.mumfordEval specialData
        (N13GoodCoordinateRingTwo.xClass X)
  rw [N13GoodCoordinateRingTwo.mumfordEval_xClass]
  rfl

end

end MazurProof.N13SpecialQuotientBasis

end
end

-- module FLT.Assumptions.MazurProof.N13SpecialGraphDivisor
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialGraphDivisor =====
section

/-!
# Degree-two Mumford graphs as effective divisors on the N13 special fibre

A monic quadratic generalized Mumford graph on the good characteristic-two
model splits over `F₂`.  Indeed, an irreducible quadratic would produce an
affine point over its quadratic root field, while the structural Frobenius
classification forces that root back into `F₂`.

The two roots, with their graph values, therefore define an effective
degree-two divisor.  If that divisor is the selected nonspecial base divisor,
its two distinct points force `u = X² + X` and `u ∣ v`; hence its graph ideal
is literally the fixed special ideal.  No finite table or representative
enumeration is used.
-/

open Polynomial
open scoped Sym2

namespace MazurProof.N13SpecialGraphDivisor

noncomputable section

open MazurProof.N13GoodCoordinateRingTwo

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem degreeTwo_splits
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    D.u.Splits := by
  by_contra hnot
  have hnoRoot (a : K) : D.u.eval a ≠ 0 := by
    intro ha
    exact hnot (Polynomial.Splits.of_natDegree_eq_two hdeg ha)
  have hroots : D.u.roots = 0 := by
    apply Multiset.eq_zero_of_forall_notMem
    intro a ha
    exact hnoRoot a ((Polynomial.mem_roots D.u_monic.ne_zero).mp ha)
  have hirr : Irreducible D.u := by
    apply (D.u_monic.irreducible_iff_roots_eq_zero_of_degree_le_three
      (by omega) (by omega)).mpr
    exact hroots
  letI : Fact (Irreducible D.u) := ⟨hirr⟩
  letI : Module.Finite K (AdjoinRoot D.u) :=
    (AdjoinRoot.powerBasis hirr.ne_zero).finite
  letI : Finite (AdjoinRoot D.u) :=
    Module.finite_of_finite K
  letI : Fintype (AdjoinRoot D.u) :=
    Fintype.ofFinite (AdjoinRoot D.u)
  letI : CharP (AdjoinRoot D.u) 2 :=
    charP_of_injective_algebraMap
      (algebraMap K (AdjoinRoot D.u)).injective 2
  have hcard : Fintype.card (AdjoinRoot D.u) = 4 := by
    rw [Module.card_eq_pow_finrank (K := K) (V := AdjoinRoot D.u),
      (AdjoinRoot.powerBasis hirr.ne_zero).finrank,
      ZMod.card, AdjoinRoot.powerBasis_dim, hdeg]
    norm_num
  let alpha : AdjoinRoot D.u := AdjoinRoot.root D.u
  let beta : AdjoinRoot D.u := Polynomial.aeval alpha D.v
  have hfour (z : AdjoinRoot D.u) : z ^ 4 = z := by
    rw [← hcard]
    exact FiniteField.pow_card z
  have hroot : Polynomial.aeval alpha D.u = 0 := by
    simp [alpha, Polynomial.aeval_def, AdjoinRoot.eval₂_root]
  have hcurve :
      N13GoodModelTwo.AffineEquation alpha beta := by
    have hc := congrArg (Polynomial.aeval alpha) D.curve_eq
    simp only [map_sub, map_add, map_pow, map_mul] at hc
    rw [hroot, zero_mul] at hc
    change
      beta ^ 2 + N13GoodModelTwo.h alpha * beta =
        N13GoodModelTwo.rhs alpha
    simpa [beta, N13GoodModelTwo.h, N13GoodModelTwo.rhs,
      hPoly, rhsPoly, Polynomial.aeval_def] using sub_eq_zero.mp hc
  have halpha : alpha ^ 2 = alpha :=
    ((N13GoodModelTwo.affineEquation_iff_fixed hfour alpha beta).mp hcurve).1
  rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one alpha halpha with ha | ha
  · have hz : D.u.eval 0 = 0 := by
      apply (algebraMap K (AdjoinRoot D.u)).injective
      have hzmap :
          algebraMap K (AdjoinRoot D.u) (D.u.eval 0) = 0 := by
        calc
          algebraMap K (AdjoinRoot D.u) (D.u.eval 0) =
              eval₂ (algebraMap K (AdjoinRoot D.u))
                (algebraMap K (AdjoinRoot D.u) 0) D.u := by
                  rw [Polynomial.eval₂_at_apply]
          _ = eval₂ (algebraMap K (AdjoinRoot D.u)) alpha D.u := by
                rw [ha]
                simp
          _ = 0 := AdjoinRoot.eval₂_root D.u
      simpa using hzmap
    exact hnoRoot 0 hz
  · have ho : D.u.eval 1 = 0 := by
      apply (algebraMap K (AdjoinRoot D.u)).injective
      have homap :
          algebraMap K (AdjoinRoot D.u) (D.u.eval 1) = 0 := by
        calc
          algebraMap K (AdjoinRoot D.u) (D.u.eval 1) =
              eval₂ (algebraMap K (AdjoinRoot D.u))
                (algebraMap K (AdjoinRoot D.u) 1) D.u := by
                  rw [Polynomial.eval₂_at_apply]
          _ = eval₂ (algebraMap K (AdjoinRoot D.u)) alpha D.u := by
                rw [ha]
                simp
          _ = 0 := AdjoinRoot.eval₂_root D.u
      simpa using homap
    exact hnoRoot 1 ho

theorem exists_rootPair
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    ∃ z : Sym2 K, z.toMultiset = D.u.roots := by
  have hcard : D.u.roots.card = 2 := by
    rw [← (degreeTwo_splits D hdeg).natDegree_eq_card_roots]
    exact hdeg
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard
  refine ⟨s(a, b), ?_⟩
  change ({a, b} : Multiset K) = D.u.roots
  exact hab.symm

noncomputable def rootPair
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    Sym2 K :=
  Classical.choose (exists_rootPair D hdeg)

theorem rootPair_toMultiset
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    (rootPair D hdeg).toMultiset = D.u.roots := by
  exact Classical.choose_spec (exists_rootPair D hdeg)

theorem mem_rootPair_iff_isRoot
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) (a : K) :
    a ∈ rootPair D hdeg ↔ D.u.IsRoot a := by
  rw [← Sym2.mem_toMultiset, rootPair_toMultiset,
    Polynomial.mem_roots D.u_monic.ne_zero]

theorem curveEquationAtRoot
    (D : SemiMumford) {a : K} (ha : D.u.IsRoot a) :
    N13GoodModelTwo.AffineEquation a (D.v.eval a) := by
  have hc := congrArg (Polynomial.eval a) D.curve_eq
  simp only [eval_sub, eval_add, eval_pow, eval_mul] at hc
  rw [ha, zero_mul] at hc
  change
    D.v.eval a ^ 2 +
        N13GoodModelTwo.h a * D.v.eval a =
      N13GoodModelTwo.rhs a
  simpa [N13GoodModelTwo.h, N13GoodModelTwo.rhs,
    hPoly, rhsPoly] using sub_eq_zero.mp hc

noncomputable def rootPoint
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (a : K) (ha : a ∈ rootPair D hdeg) :
    N13AbelFiberTwoModel.CurvePoint :=
  Sum.inl
    ⟨(a, D.v.eval a),
      curveEquationAtRoot D ((mem_rootPair_iff_isRoot D hdeg a).mp ha)⟩

noncomputable def graphDivisor
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    N13SymmetricSquareTwo.EffectiveDivisorTwo :=
  Sym2.pmap (rootPoint D hdeg) (rootPair D hdeg)
    (fun _ ha => ha)

/-- Abel equality with the selected nonspecial divisor already forces
literal equality of effective divisors.  The only other degree-two Abel
fibre is the canonical pencil, and the selected base divisor is not in it. -/
theorem graphDivisor_eq_special_of_abel_eq
    {J : Type*}
    (G : N13AbelFiberTwoModel.GeometricAbelCriterion J)
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (habel :
      G.abel (graphDivisor D hdeg) =
        G.abel N13AbelChartBase.specialBaseDivisor) :
    graphDivisor D hdeg =
      N13AbelChartBase.specialBaseDivisor := by
  rcases
      (G.eq_iff
        (graphDivisor D hdeg)
        N13AbelChartBase.specialBaseDivisor).mp habel with
    h | ⟨_, hbase⟩
  · exact h
  · exact
      (N13AbelChartBase.specialBaseDivisor_not_canonical hbase).elim

/-- The same rigidity statement in the canonical nineteen-element
set-valued Abel quotient. -/
theorem graphDivisor_eq_special_of_setAbel_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (habel :
      N13AbelFiberTwoModel.abel (graphDivisor D hdeg) =
        N13AbelFiberTwoModel.abel
          N13AbelChartBase.specialBaseDivisor) :
    graphDivisor D hdeg =
      N13AbelChartBase.specialBaseDivisor :=
  graphDivisor_eq_special_of_abel_eq
    N13AbelFiberTwoModel.picTwoSetModelCriterion D hdeg habel

theorem zero_one_roots_and_values_of_graphDivisor_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (hgraph :
      graphDivisor D hdeg =
        N13AbelChartBase.specialBaseDivisor) :
    D.u.IsRoot 0 ∧ D.u.IsRoot 1 ∧
      D.v.eval 0 = 0 ∧ D.v.eval 1 = 0 := by
  have hp00 :
      N13AbelChartBase.p00 ∈ graphDivisor D hdeg := by
    rw [hgraph]
    exact Sym2.mem_mk_left _ _
  have hp10 :
      N13AbelChartBase.p10 ∈ graphDivisor D hdeg := by
    rw [hgraph]
    exact Sym2.mem_mk_right _ _
  rw [graphDivisor, Sym2.mem_pmap_iff] at hp00 hp10
  obtain ⟨a, ha, hpa⟩ := hp00
  obtain ⟨b, hb, hpb⟩ := hp10
  have hca := congrArg N13AbelFiberTwoModel.curvePointEquiv hpa
  have hcb := congrArg N13AbelFiberTwoModel.curvePointEquiv hpb
  have ha0 : a = 0 := by
    symm
    simpa [N13AbelChartBase.p00, rootPoint,
      N13AbelFiberTwoModel.curvePointEquiv] using congrArg Prod.fst hca
  have hva0 : D.v.eval a = 0 := by
    symm
    simpa [N13AbelChartBase.p00, rootPoint,
      N13AbelFiberTwoModel.curvePointEquiv] using congrArg Prod.snd hca
  have hb1 : b = 1 := by
    symm
    simpa [N13AbelChartBase.p10, rootPoint,
      N13AbelFiberTwoModel.curvePointEquiv] using congrArg Prod.fst hcb
  have hvb0 : D.v.eval b = 0 := by
    symm
    simpa [N13AbelChartBase.p10, rootPoint,
      N13AbelFiberTwoModel.curvePointEquiv] using congrArg Prod.snd hcb
  subst a
  subst b
  exact
    ⟨(mem_rootPair_iff_isRoot D hdeg 0).mp ha,
      (mem_rootPair_iff_isRoot D hdeg 1).mp hb,
      hva0, hvb0⟩

theorem u_eq_base_and_dvd_v_of_graphDivisor_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (hgraph :
      graphDivisor D hdeg =
        N13AbelChartBase.specialBaseDivisor) :
    D.u = (X ^ 2 + X : K[X]) ∧ D.u ∣ D.v := by
  obtain ⟨hu0, hu1, hv0, hv1⟩ :=
    zero_one_roots_and_values_of_graphDivisor_eq D hdeg hgraph
  have htwo : (2 : K) = 0 :=
    CharP.cast_eq_zero K 2
  have hunit : IsUnit ((0 : K) - 1) := by
    have hnegOne : (-1 : K) = 1 := by
      change (-1 : ZMod 2) = 1
      decide
    rw [zero_sub, hnegOne]
    exact isUnit_one
  have hcop :
      IsCoprime (X - C (0 : K)) (X - C (1 : K)) :=
    isCoprime_X_sub_C_of_isUnit_sub hunit
  have hfactor :
      (X - C (0 : K)) * (X - C (1 : K)) =
        (X ^ 2 + X : K[X]) := by
    simp only [map_zero, sub_zero, map_one]
    have htwoPoly : (2 : K[X]) = 0 :=
      CharP.cast_eq_zero (K[X]) 2
    have hsum : (X : K[X]) + X = 0 := by
      calc
        (X : K[X]) + X = 2 * X := by ring
        _ = 0 := by rw [htwoPoly, zero_mul]
    have hnegX : -(X : K[X]) = X := by
      calc
        -(X : K[X]) = -X + (X + X) := by rw [hsum, add_zero]
        _ = X := by ring
    calc
      (X : K[X]) * (X - 1) = X ^ 2 - X := by ring
      _ = X ^ 2 + X := by simp [sub_eq_add_neg, hnegX]
  have hprod_u :
      (X - C (0 : K)) * (X - C (1 : K)) ∣ D.u :=
    hcop.mul_dvd
      (Polynomial.dvd_iff_isRoot.mpr hu0)
      (Polynomial.dvd_iff_isRoot.mpr hu1)
  have hu :
      (X - C (0 : K)) * (X - C (1 : K)) = D.u := by
    have hpdeg :
        ((X - C (0 : K)) * (X - C (1 : K))).natDegree = 2 := by
      rw [natDegree_mul
        (monic_X_sub_C (0 : K)).ne_zero
        (monic_X_sub_C (1 : K)).ne_zero]
      rw [natDegree_X_sub_C, natDegree_X_sub_C]
    apply Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff hprod_u
    · rw [hdeg, hpdeg]
    · rw [((monic_X_sub_C (0 : K)).mul
          (monic_X_sub_C (1 : K))).leadingCoeff,
        D.u_monic.leadingCoeff]
  have hprod_v :
      (X - C (0 : K)) * (X - C (1 : K)) ∣ D.v :=
    hcop.mul_dvd
      (Polynomial.dvd_iff_isRoot.mpr hv0)
      (Polynomial.dvd_iff_isRoot.mpr hv1)
  constructor
  · rw [← hu]
    exact hfactor
  · rw [← hu]
    exact hprod_v

/-- Literal equality with the selected special graph ideal already recovers
the monic quadratic and the graph value modulo it.  This is the converse
representative statement to `mumfordIdeal_eq_special_of_graphDivisor_eq`. -/
theorem u_eq_base_and_dvd_v_of_mumfordIdeal_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (hideal :
      mumfordIdeal D.u D.v =
        N13SpecialQuotientBasis.specialIdeal) :
    D.u = (X ^ 2 + X : K[X]) ∧ D.u ∣ D.v := by
  have hxmem :
      xClass N13SpecialQuotientBasis.specialData.u ∈
        mumfordIdeal D.u D.v := by
    rw [hideal]
    exact
      xClass_mem_mumfordIdeal
        N13SpecialQuotientBasis.specialData.u
        N13SpecialQuotientBasis.specialData.v
  have hxker :
      xClass N13SpecialQuotientBasis.specialData.u ∈
        RingHom.ker (mumfordEval D) := by
    rw [ker_mumfordEval D]
    exact hxmem
  have hxzero :=
    RingHom.mem_ker.mp hxker
  rw [mumfordEval_xClass,
    Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hxzero
  have hueq :
      D.u = (X ^ 2 + X : K[X]) := by
    have hspecial :
        N13SpecialQuotientBasis.specialData.u = D.u :=
      Polynomial.eq_of_monic_of_dvd_of_natDegree_le
        D.u_monic
        N13SpecialQuotientBasis.specialData.u_monic
        hxzero
        (by
          rw [hdeg,
            N13SpecialQuotientBasis.specialData_u_natDegree])
    simpa only [N13SpecialQuotientBasis.specialData_u] using hspecial.symm
  have hymem :
      yClass ∈ mumfordIdeal D.u D.v := by
    rw [hideal]
    change
      yClass ∈
        mumfordIdeal
          N13SpecialQuotientBasis.specialData.u
          N13SpecialQuotientBasis.specialData.v
    simpa only [N13SpecialQuotientBasis.specialData_v,
      ySubClass, xClass_zero, sub_zero] using
      ySubClass_mem_mumfordIdeal
        N13SpecialQuotientBasis.specialData.u
        N13SpecialQuotientBasis.specialData.v
  have hyker :
      yClass ∈ RingHom.ker (mumfordEval D) := by
    rw [ker_mumfordEval D]
    exact hymem
  have hyzero :=
    RingHom.mem_ker.mp hyker
  rw [mumfordEval_yClass,
    Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hyzero
  exact ⟨hueq, hyzero⟩

/-- The literal special graph ideal determines the selected effective
divisor.  The proof recovers the two roots and evaluates the graph there;
it does not enumerate the special curve. -/
theorem graphDivisor_eq_special_of_mumfordIdeal_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (hideal :
      mumfordIdeal D.u D.v =
        N13SpecialQuotientBasis.specialIdeal) :
    graphDivisor D hdeg =
      N13AbelChartBase.specialBaseDivisor := by
  obtain ⟨hu, hv⟩ :=
    u_eq_base_and_dvd_v_of_mumfordIdeal_eq D hdeg hideal
  have hr0 : D.u.IsRoot 0 := by
    simp [hu]
  have hr1 : D.u.IsRoot 1 := by
    change D.u.eval 1 = 0
    rw [hu]
    norm_num
    exact CharP.cast_eq_zero K 2
  have hmem0 :
      (0 : K) ∈ rootPair D hdeg :=
    (mem_rootPair_iff_isRoot D hdeg 0).2 hr0
  have hmem1 :
      (1 : K) ∈ rootPair D hdeg :=
    (mem_rootPair_iff_isRoot D hdeg 1).2 hr1
  obtain ⟨q, hq⟩ := hv
  have hv0 : D.v.eval 0 = 0 := by
    rw [hq, eval_mul, hr0, zero_mul]
  have hv1 : D.v.eval 1 = 0 := by
    rw [hq, eval_mul, hr1, zero_mul]
  have hp00 :
      N13AbelChartBase.p00 ∈ graphDivisor D hdeg := by
    rw [graphDivisor, Sym2.mem_pmap_iff]
    refine ⟨0, hmem0, ?_⟩
    simp [rootPoint, N13AbelChartBase.p00,
      N13AbelFiberTwoModel.curvePointEquiv, hv0]
  have hp10 :
      N13AbelChartBase.p10 ∈ graphDivisor D hdeg := by
    rw [graphDivisor, Sym2.mem_pmap_iff]
    refine ⟨1, hmem1, ?_⟩
    simp [rootPoint, N13AbelChartBase.p10,
      N13AbelFiberTwoModel.curvePointEquiv, hv1]
  have hpne :
      N13AbelChartBase.p00 ≠ N13AbelChartBase.p10 := by
    intro h
    have h' :=
      congrArg N13AbelFiberTwoModel.curvePointEquiv h
    simp [N13AbelChartBase.p00,
      N13AbelChartBase.p10] at h'
  simpa [N13AbelChartBase.specialBaseDivisor] using
    (Sym2.mem_and_mem_iff hpne).mp ⟨hp00, hp10⟩

theorem mumfordIdeal_eq_zero_of_dvd
    (u v : K[X]) (h : u ∣ v) :
    mumfordIdeal u v = mumfordIdeal u 0 := by
  obtain ⟨q, hq⟩ := h
  have hmultiple :
      xClass v ∈ mumfordIdeal u 0 := by
    rw [hq, xClass_mul, mul_comm]
    exact Ideal.mul_mem_left _ (xClass q)
      (xClass_mem_mumfordIdeal u 0)
  have hmultiple' :
      xClass v ∈ mumfordIdeal u v := by
    have hx : xClass v = xClass u * xClass q := by
      rw [hq, xClass_mul]
    rw [hx]
    simpa only [mul_comm] using
      Ideal.mul_mem_left _ (xClass q)
        (xClass_mem_mumfordIdeal u v)
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_mumfordIdeal u 0
    · have heq : ySubClass v = ySubClass 0 - xClass v := by
        simp [ySubClass]
      rw [heq]
      exact Ideal.sub_mem _
        (ySubClass_mem_mumfordIdeal u 0) hmultiple
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_mumfordIdeal u v
    · have heq : ySubClass 0 = ySubClass v + xClass v := by
        simp [ySubClass]
      rw [heq]
      exact Ideal.add_mem _
        (ySubClass_mem_mumfordIdeal u v) hmultiple'

theorem mumfordIdeal_eq_special_of_graphDivisor_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (hgraph :
      graphDivisor D hdeg =
        N13AbelChartBase.specialBaseDivisor) :
    mumfordIdeal D.u D.v =
      N13SpecialQuotientBasis.specialIdeal := by
  obtain ⟨hu, hv⟩ :=
    u_eq_base_and_dvd_v_of_graphDivisor_eq D hdeg hgraph
  calc
    mumfordIdeal D.u D.v = mumfordIdeal D.u 0 :=
      mumfordIdeal_eq_zero_of_dvd D.u D.v hv
    _ = N13SpecialQuotientBasis.specialIdeal := by
      simp [N13SpecialQuotientBasis.specialIdeal,
        N13SpecialQuotientBasis.specialData_u,
        N13SpecialQuotientBasis.specialData_v, hu]

/-- The complete special-fibre bridge: an Abel-compatible quadratic
Mumford graph has the fixed literal graph ideal. -/
theorem mumfordIdeal_eq_special_of_abel_eq
    {J : Type*}
    (G : N13AbelFiberTwoModel.GeometricAbelCriterion J)
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (habel :
      G.abel (graphDivisor D hdeg) =
        G.abel N13AbelChartBase.specialBaseDivisor) :
    mumfordIdeal D.u D.v =
      N13SpecialQuotientBasis.specialIdeal :=
  mumfordIdeal_eq_special_of_graphDivisor_eq D hdeg
    (graphDivisor_eq_special_of_abel_eq G D hdeg habel)

/-- Set-valued Abel compatibility is already enough to identify the fixed
special graph ideal. -/
theorem mumfordIdeal_eq_special_of_setAbel_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (habel :
      N13AbelFiberTwoModel.abel (graphDivisor D hdeg) =
        N13AbelFiberTwoModel.abel
          N13AbelChartBase.specialBaseDivisor) :
    mumfordIdeal D.u D.v =
      N13SpecialQuotientBasis.specialIdeal :=
  mumfordIdeal_eq_special_of_abel_eq
    N13AbelFiberTwoModel.picTwoSetModelCriterion D hdeg habel

/-- For quadratic special graphs, the intrinsic Abel class and the literal
graph ideal carry exactly the same information at the selected regular
class. -/
theorem setAbel_eq_iff_mumfordIdeal_eq_special
    (D : SemiMumford) (hdeg : D.u.natDegree = 2) :
    N13AbelFiberTwoModel.abel (graphDivisor D hdeg) =
        N13AbelFiberTwoModel.abel
          N13AbelChartBase.specialBaseDivisor ↔
      mumfordIdeal D.u D.v =
        N13SpecialQuotientBasis.specialIdeal := by
  constructor
  · exact mumfordIdeal_eq_special_of_setAbel_eq D hdeg
  · intro hideal
    exact congrArg N13AbelFiberTwoModel.abel
      (graphDivisor_eq_special_of_mumfordIdeal_eq
        D hdeg hideal)

end

end MazurProof.N13SpecialGraphDivisor

end
end


