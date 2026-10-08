-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianLocalization_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianLocalization_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:24:24.431981+00:00
-- url     : https://prove2.me/theorems/179a0e90-53d0-4505-942f-5d9e54b04c68
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianLocalization source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianLocalization

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianLocalization
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianCubic_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianOrderTwo_p0
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing

set_option autoImplicit false




/-!
# The global N13 sextic algebra inside the local Gaussian order

The fixed Gaussian cubic order is an integral presentation over `ℤ₂`.
After inverting `2`, its two generators satisfy the global sextic
presentation over `ℚ`.  This gives a structural specialization map from the
global sextic algebra to the localized order.

The construction deliberately stops before reduction modulo `2`: reduction
does not extend across an inverted `2`.  Instead, later lemmas identify the
global descent generators with integral elements of the order, which may then
be reduced by `N13GaussianOrderTwo.reduction`.
-/

open Polynomial

namespace MazurProof.N13GaussianLocalization

noncomputable section

open N13GaussianOrderTwo

abbrev Z2 : Type := ℤ_[2]

abbrev Q2 : Type := ℚ_[2]

abbrev Order : Type :=
  N13GaussianOrderTwo.Order

/-- The explicit Gaussian cubic order with only `2` inverted. -/
abbrev LocalOrder : Type :=
  Localization.Away (2 : Order)

/-- The coefficient map from `ℤ₂` into the localized Gaussian order. -/
def z2ToLocalOrder : Z2 →+* LocalOrder :=
  (algebraMap Order LocalOrder).comp (algebraMap Z2 Order)

theorem z2ToLocalOrder_two_isUnit :
    IsUnit (z2ToLocalOrder (2 : Z2)) := by
  change IsUnit (algebraMap Order LocalOrder (2 : Order))
  exact IsLocalization.Away.algebraMap_isUnit (2 : Order)

/-- Every nonzero `2`-adic integer becomes a unit after `2` is inverted.
This is the DVR factorization `z = u 2^v`, not a denominator calculation. -/
theorem z2ToLocalOrder_isUnit
    {z : Z2} (hz : z ≠ 0) :
    IsUnit (z2ToLocalOrder z) := by
  rw [PadicInt.unitCoeff_spec hz, map_mul, map_pow]
  exact
    (IsUnit.map z2ToLocalOrder
      (Units.isUnit (PadicInt.unitCoeff hz))).mul
      (z2ToLocalOrder_two_isUnit.pow _)

/-- The fraction-field map `ℚ₂ → O[1/2]`. -/
def q2ToLocalOrder : Q2 →+* LocalOrder :=
  IsLocalization.lift fun z : nonZeroDivisors Z2 =>
    z2ToLocalOrder_isUnit
      (by
        exact mem_nonZeroDivisors_iff_ne_zero.mp z.property)

@[simp] theorem q2ToLocalOrder_z2 (z : Z2) :
    q2ToLocalOrder (algebraMap Z2 Q2 z) =
      z2ToLocalOrder z :=
  IsLocalization.lift_eq _ z

/-- Restriction of the preceding map to rational coefficients. -/
def qToLocalOrder : ℚ →+* LocalOrder :=
  q2ToLocalOrder.comp (algebraMap ℚ Q2)

@[simp] theorem qToLocalOrder_intCast (n : ℤ) :
    qToLocalOrder n = n := by
  exact map_intCast qToLocalOrder n

@[simp] theorem qToLocalOrder_natCast (n : ℕ) :
    qToLocalOrder n = n := by
  exact map_natCast qToLocalOrder n

/-- The two integral Gaussian generators viewed after inverting `2`. -/
def localI : LocalOrder :=
  algebraMap Order LocalOrder N13GaussianOrderTwo.i

def localTheta : LocalOrder :=
  algebraMap Order LocalOrder N13GaussianOrderTwo.theta

theorem localI_sq :
    localI ^ 2 = (-1 : LocalOrder) := by
  rw [localI, ← map_pow, N13GaussianOrderTwo.i_sq, map_neg, map_one]

theorem localTheta_gaussian_cubic :
    localTheta ^ 3 + 2 * localTheta ^ 2 - localTheta - 1 -
        localI * (2 * localTheta * (localTheta + 1)) = 0 := by
  simpa [localI, localTheta, map_add, map_sub, map_mul, map_pow,
    map_ofNat] using
    congrArg (algebraMap Order LocalOrder)
      N13GaussianOrderTwo.theta_gaussian_cubic

/-- The cubic relation and `i² = -1` imply the N13 sextic relation. -/
theorem localTheta_sextic :
    eval₂ qToLocalOrder localTheta (N13Mumford.f ℚ) = 0 := by
  let Aθ : LocalOrder :=
    localTheta ^ 3 + 2 * localTheta ^ 2 - localTheta - 1
  let Bθ : LocalOrder :=
    2 * localTheta * (localTheta + 1)
  have hA : Aθ = localI * Bθ := by
    exact sub_eq_zero.mp localTheta_gaussian_cubic
  calc
    eval₂ qToLocalOrder localTheta (N13Mumford.f ℚ) =
        Aθ ^ 2 + Bθ ^ 2 := by
      simp only [N13Mumford.f, eval₂_add, eval₂_mul, eval₂_pow,
        eval₂_X, eval₂_one, eval₂_ofNat]
      dsimp [Aθ, Bθ]
      ring
    _ = (localI * Bθ) ^ 2 + Bθ ^ 2 := by rw [hA]
    _ = 0 := by rw [mul_pow, localI_sq]; ring

/-- Structural specialization of the global sextic algebra to the explicit
Gaussian order with `2` inverted. -/
def sexticToLocalOrder :
    N13SexticSquareclass.SexticAlgebra →+* LocalOrder :=
  AdjoinRoot.lift qToLocalOrder localTheta localTheta_sextic

@[simp] theorem sexticToLocalOrder_theta :
    sexticToLocalOrder N13GaussianCubic.theta = localTheta :=
  AdjoinRoot.lift_root localTheta_sextic

@[simp] theorem sexticToLocalOrder_scalar (q : ℚ) :
    sexticToLocalOrder
        (algebraMap ℚ N13SexticSquareclass.SexticAlgebra q) =
      qToLocalOrder q :=
  AdjoinRoot.lift_of localTheta_sextic

@[simp] theorem sexticToLocalOrder_ofPoly (p : ℚ[X]) :
    sexticToLocalOrder (N13SexticSquareclass.ofPoly p) =
      eval₂ qToLocalOrder localTheta p := by
  change
    (AdjoinRoot.lift qToLocalOrder localTheta localTheta_sextic)
        (AdjoinRoot.mk (N13Mumford.f ℚ) p) =
      eval₂ qToLocalOrder localTheta p
  exact AdjoinRoot.lift_mk localTheta_sextic p

/-! ## Integral images of the global descent generators -/

theorem localTheta_mul_inverse :
    localTheta *
        (localTheta ^ 2 + (2 - 2 * localI) * localTheta +
          (-1 - 2 * localI)) = 1 := by
  linear_combination localTheta_gaussian_cubic

theorem localTheta_isUnit :
    IsUnit localTheta :=
  isUnit_iff_exists_inv.mpr
    ⟨localTheta ^ 2 + (2 - 2 * localI) * localTheta +
      (-1 - 2 * localI), localTheta_mul_inverse⟩

theorem localTheta_add_one_mul_inverse :
    (localTheta + 1) *
        (-(localTheta ^ 2 + (1 - 2 * localI) * localTheta - 2)) =
      1 := by
  linear_combination -localTheta_gaussian_cubic

theorem localTheta_add_one_isUnit :
    IsUnit (localTheta + 1) :=
  isUnit_iff_exists_inv.mpr
    ⟨-(localTheta ^ 2 + (1 - 2 * localI) * localTheta - 2),
      localTheta_add_one_mul_inverse⟩

theorem localTwo_isUnit :
    IsUnit (2 : LocalOrder) := by
  simpa only [map_ofNat] using
    (IsLocalization.Away.algebraMap_isUnit (2 : Order) :
      IsUnit (algebraMap Order LocalOrder (2 : Order)))

/-- The imaginary part `2θ(θ+1)` of the Gaussian cubic factor is a
unit after inverting `2`.  This makes the Gaussian root determined by the
cubic relation. -/
theorem localB_isUnit :
    IsUnit (2 * localTheta * (localTheta + 1)) :=
  (localTwo_isUnit.mul localTheta_isUnit).mul
    localTheta_add_one_isUnit

/-- The intrinsic order-four element of the sextic algebra specializes to
the integral Gaussian generator.  No long polynomial reduction is needed:
the two elements satisfy the same cubic relation, and its coefficient
`2θ(θ+1)` is a unit. -/
@[simp] theorem sexticToLocalOrder_zeta :
    sexticToLocalOrder N13SexticSquareclass.zeta = localI := by
  let zI : LocalOrder :=
    sexticToLocalOrder N13SexticSquareclass.zeta
  let Bθ : LocalOrder :=
    2 * localTheta * (localTheta + 1)
  have hz :
      localTheta ^ 3 + 2 * localTheta ^ 2 - localTheta - 1 -
          zI * Bθ = 0 := by
    simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat,
      map_one, map_zero, sexticToLocalOrder_theta] using
      congrArg sexticToLocalOrder N13GaussianCubic.gaussian_cubic
  have hi :
      localTheta ^ 3 + 2 * localTheta ^ 2 - localTheta - 1 -
          localI * Bθ = 0 := by
    simpa only [Bθ] using localTheta_gaussian_cubic
  apply localB_isUnit.mul_right_cancel
  calc
    zI * Bθ =
        localTheta ^ 3 + 2 * localTheta ^ 2 - localTheta - 1 :=
      (sub_eq_zero.mp hz).symm
    _ = localI * Bθ :=
      sub_eq_zero.mp hi

@[simp] theorem sexticToLocalOrder_e1 :
    sexticToLocalOrder N13SexticSquareclass.e1 =
      algebraMap Order LocalOrder N13GaussianOrderTwo.e1Order := by
  have h :=
    congrArg sexticToLocalOrder N13GaussianCubic.e1_short
  simpa [N13GaussianOrderTwo.e1Order, localI, localTheta,
    map_add, map_sub, map_mul, map_pow, map_one] using h

@[simp] theorem sexticToLocalOrder_e2 :
    sexticToLocalOrder N13SexticSquareclass.e2 =
      algebraMap Order LocalOrder N13GaussianOrderTwo.e2Order := by
  have h :=
    congrArg sexticToLocalOrder N13GaussianCubic.e2_short
  simpa [N13GaussianOrderTwo.e2Order, localI, localTheta,
    map_add, map_sub, map_mul, map_pow, map_ofNat, map_one] using h

@[simp] theorem sexticToLocalOrder_primeA :
    sexticToLocalOrder N13SexticSquareclass.primeA =
      algebraMap Order LocalOrder N13GaussianOrderTwo.primeAOrder := by
  have h :=
    congrArg sexticToLocalOrder N13GaussianCubic.primeA_short
  simpa [N13GaussianOrderTwo.primeAOrder, localI, localTheta,
    map_add, map_sub, map_mul, map_pow, map_one] using h

@[simp] theorem sexticToLocalOrder_primeQ :
    sexticToLocalOrder N13SexticSquareclass.primeQ =
      algebraMap Order LocalOrder N13GaussianOrderTwo.primeQOrder := by
  have h :=
    congrArg sexticToLocalOrder N13GaussianCubic.primeQ_short
  simpa [N13GaussianOrderTwo.primeQOrder, localI,
    map_sub, map_mul, map_ofNat] using h

end

end MazurProof.N13GaussianLocalization


