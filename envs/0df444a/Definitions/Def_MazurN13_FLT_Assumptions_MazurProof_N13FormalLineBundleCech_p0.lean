-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FormalLineBundleCech_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13FormalLineBundleCech_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:37:47.627314+00:00
-- url     : https://prove2.me/theorems/376f486a-891b-4996-9e97-ff94fb411bee
-- title:
--   FLT.Assumptions.MazurProof.N13FormalLineBundleCech source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13FormalLineBundleCech

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13FormalLineBundleCech
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralFormalCech_p0

set_option autoImplicit false




/-!
# Near-trivial formal line bundles in the N13 Čech chart

A line bundle in the kernel of specialization admits, after choosing local
trivializations, a formal overlap transition which reduces to `1`.  Twisting
the two actual principal parts by such a transition perturbs the integral
connecting matrix, but does not change its special fibre.

This file encodes the actual quadratic formal curve algebra at infinity,
proves coefficientwise reduction respects its multiplication, and applies
the previously proved Čech--Nakayama theorem to every invertible transition
reducing to `1`.

The remaining geometric task is now sharply isolated: construct these two
local trivializations from a rational Picard class in the specialization
kernel.  No cohomology or matrix-surjectivity hypothesis remains.
-/

namespace MazurProof.N13FormalLineBundleCech

noncomputable section

open HahnSeries
open scoped LaurentSeries

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralCechObstruction.R₂

abbrev K : Type :=
  N13IntegralCechObstruction.K

abbrev Laurent₂ : Type :=
  N13CechLaurentSeriesCore.Laurent (R := R₂)

abbrev LaurentBar : Type :=
  N13CechLaurentSeriesCore.Laurent (R := K)

abbrev Overlap₂ : Type :=
  N13CechLaurentSeriesCore.Overlap (R := R₂)

abbrev OverlapBar : Type :=
  N13CechLaurentSeriesCore.Overlap (R := K)

abbrev PrincipalParts : Type :=
  N13IntegralCechObstruction.PrincipalParts

abbrev Obstruction : Type :=
  N13IntegralCechObstruction.Obstruction

/-- A Laurent monomial over an arbitrary coefficient ring. -/
def tPow
    {R : Type*} [CommRing R] (n : ℤ) :
    N13CechLaurentSeriesCore.Laurent (R := R) :=
  HahnSeries.single n 1

/-- The coefficient of `v` in the integral infinity-chart equation. -/
def hInfinity
    {R : Type*} [CommRing R] :
    N13CechLaurentSeriesCore.Laurent (R := R) :=
  tPow 0 + tPow 2 + tPow 3

/-- The right-hand side of the integral infinity-chart equation. -/
def rhsInfinity
    {R : Type*} [CommRing R] :
    N13CechLaurentSeriesCore.Laurent (R := R) :=
  tPow 1 + tPow 2

/-- Multiplication in the formal curve algebra

`v² + (1+t²+t³)v = t+t²`

written in the basis `1,v`. -/
def mulOverlap
    {R : Type*} [CommRing R]
    (z w : N13CechLaurentSeriesCore.Overlap (R := R)) :
    N13CechLaurentSeriesCore.Overlap (R := R) :=
  (z.1 * w.1 + z.2 * w.2 * rhsInfinity,
    z.1 * w.2 + z.2 * w.1 -
      z.2 * w.2 * hInfinity)

/-- The identity formal function. -/
def oneOverlap
    {R : Type*} [CommRing R] :
    N13CechLaurentSeriesCore.Overlap (R := R) :=
  (1, 0)

theorem mulOverlap_comm
    {R : Type*} [CommRing R]
    (z w : N13CechLaurentSeriesCore.Overlap (R := R)) :
    mulOverlap z w = mulOverlap w z := by
  apply Prod.ext <;>
    simp [mulOverlap]
  <;> ring

theorem mulOverlap_assoc
    {R : Type*} [CommRing R]
    (x y z : N13CechLaurentSeriesCore.Overlap (R := R)) :
    mulOverlap (mulOverlap x y) z =
      mulOverlap x (mulOverlap y z) := by
  apply Prod.ext <;>
    simp [mulOverlap]
  <;> ring

@[simp] theorem oneOverlap_mul
    {R : Type*} [CommRing R]
    (z : N13CechLaurentSeriesCore.Overlap (R := R)) :
    mulOverlap oneOverlap z = z := by
  apply Prod.ext <;>
    simp [mulOverlap, oneOverlap]

@[simp] theorem mul_oneOverlap
    {R : Type*} [CommRing R]
    (z : N13CechLaurentSeriesCore.Overlap (R := R)) :
    mulOverlap z oneOverlap = z := by
  apply Prod.ext <;>
    simp [mulOverlap, oneOverlap]

/-- Left multiplication by a fixed formal function is linear. -/
def leftMul
    {R : Type*} [CommRing R]
    (g : N13CechLaurentSeriesCore.Overlap (R := R)) :
    N13CechLaurentSeriesCore.Overlap (R := R) →ₗ[R]
      N13CechLaurentSeriesCore.Overlap (R := R) where
  toFun z := mulOverlap g z
  map_add' z w := by
    apply Prod.ext <;>
      simp [mulOverlap]
    <;> ring_nf
  map_smul' c z := by
    apply Prod.ext
    · change
        g.1 * (c • z.1) +
            g.2 * (c • z.2) * rhsInfinity =
          c • (g.1 * z.1 + g.2 * z.2 * rhsInfinity)
      simp only [← HahnSeries.single_zero_mul_eq_smul]
      ring
    · change
        g.1 * (c • z.2) + g.2 * (c • z.1) -
            g.2 * (c • z.2) * hInfinity =
          c •
            (g.1 * z.2 + g.2 * z.1 -
              g.2 * z.2 * hInfinity)
      simp only [← HahnSeries.single_zero_mul_eq_smul]
      ring

theorem mulOverlap_add_right
    {R : Type*} [CommRing R]
    (x y z : N13CechLaurentSeriesCore.Overlap (R := R)) :
    mulOverlap x (y + z) =
      mulOverlap x y + mulOverlap x z :=
  (leftMul x).map_add y z

theorem mulOverlap_add_left
    {R : Type*} [CommRing R]
    (x y z : N13CechLaurentSeriesCore.Overlap (R := R)) :
    mulOverlap (x + y) z =
      mulOverlap x z + mulOverlap y z := by
  rw [mulOverlap_comm (x + y) z,
    mulOverlap_add_right,
    mulOverlap_comm z x,
    mulOverlap_comm z y]

/-- Coefficientwise reduction of a two-adic Laurent series. -/
def reduceBase : R₂ →+* K :=
  PadicInt.toZMod

def reduceLaurent (f : Laurent₂) : LaurentBar :=
  f.map reduceBase

@[simp] theorem reduceLaurent_coeff
    (f : Laurent₂) (n : ℤ) :
    (reduceLaurent f).coeff n =
      reduceBase (f.coeff n) := rfl

@[simp] theorem reduceLaurent_zero :
    reduceLaurent 0 = 0 :=
  HahnSeries.map_zero
    reduceBase.toZeroHom

@[simp] theorem reduceLaurent_one :
    reduceLaurent 1 = 1 := by
  exact
    HahnSeries.map_one
      reduceBase.toMonoidWithZeroHom

@[simp] theorem reduceLaurent_add
    (f g : Laurent₂) :
    reduceLaurent (f + g) =
      reduceLaurent f + reduceLaurent g := by
  exact
    HahnSeries.map_add
      reduceBase.toAddMonoidHom

@[simp] theorem reduceLaurent_neg
    (f : Laurent₂) :
    reduceLaurent (-f) = -reduceLaurent f := by
  exact HahnSeries.map_neg reduceBase.toAddMonoidHom

@[simp] theorem reduceLaurent_sub
    (f g : Laurent₂) :
    reduceLaurent (f - g) =
      reduceLaurent f - reduceLaurent g := by
  rw [sub_eq_add_neg, reduceLaurent_add,
    reduceLaurent_neg, sub_eq_add_neg]

@[simp] theorem reduceLaurent_mul
    (f g : Laurent₂) :
    reduceLaurent (f * g) =
      reduceLaurent f * reduceLaurent g := by
  exact
    HahnSeries.map_mul
      reduceBase.toNonUnitalRingHom

@[simp] theorem reduceLaurent_tPow
    (n : ℤ) :
    reduceLaurent (tPow (R := R₂) n) =
      tPow (R := K) n := by
  ext m
  by_cases hmn : m = n
  · subst m
    simp [reduceLaurent, tPow, reduceBase]
  · simp [reduceLaurent, tPow, reduceBase, hmn]

/-- Coefficientwise reduction in the basis `1,v`. -/
def reduceOverlap (z : Overlap₂) : OverlapBar :=
  (reduceLaurent z.1, reduceLaurent z.2)

@[simp] theorem reduceOverlap_one :
    reduceOverlap (oneOverlap (R := R₂)) =
      oneOverlap (R := K) := by
  simp [reduceOverlap, oneOverlap]

/-- Reduction respects the actual quadratic formal-curve
multiplication. -/
theorem reduceOverlap_mul
    (z w : Overlap₂) :
    reduceOverlap (mulOverlap z w) =
      mulOverlap (reduceOverlap z) (reduceOverlap w) := by
  apply Prod.ext <;>
    simp [reduceOverlap, mulOverlap, hInfinity,
      rhsInfinity]

/-- An invertible formal transition function whose special fibre is the
identity transition. -/
structure NearIdentityTransition where
  transition : Overlap₂
  inverse : Overlap₂
  mul_inverse :
    mulOverlap transition inverse =
      oneOverlap
  inverse_mul :
    mulOverlap inverse transition =
      oneOverlap
  reduce_transition :
    reduceOverlap transition =
      oneOverlap

namespace NearIdentityTransition

variable (g : NearIdentityTransition)

/-- The untwisted formal line bundle. -/
def identity : NearIdentityTransition where
  transition := oneOverlap
  inverse := oneOverlap
  mul_inverse := oneOverlap_mul _
  inverse_mul := oneOverlap_mul _
  reduce_transition := reduceOverlap_one

/-- Tensor square of a near-trivial formal line bundle, written on its
overlap transition. -/
def square : NearIdentityTransition where
  transition := mulOverlap g.transition g.transition
  inverse := mulOverlap g.inverse g.inverse
  mul_inverse := by
    calc
      mulOverlap
          (mulOverlap g.transition g.transition)
          (mulOverlap g.inverse g.inverse) =
        mulOverlap g.transition
          (mulOverlap g.transition
            (mulOverlap g.inverse g.inverse)) :=
        mulOverlap_assoc _ _ _
      _ =
        mulOverlap g.transition
          (mulOverlap
            (mulOverlap g.transition g.inverse)
            g.inverse) := by
          rw [mulOverlap_assoc]
      _ =
        mulOverlap g.transition
          (mulOverlap oneOverlap g.inverse) := by
          rw [g.mul_inverse]
      _ = mulOverlap g.transition g.inverse := by
          rw [oneOverlap_mul]
      _ = oneOverlap := g.mul_inverse
  inverse_mul := by
    calc
      mulOverlap
          (mulOverlap g.inverse g.inverse)
          (mulOverlap g.transition g.transition) =
        mulOverlap g.inverse
          (mulOverlap g.inverse
            (mulOverlap g.transition g.transition)) :=
        mulOverlap_assoc _ _ _
      _ =
        mulOverlap g.inverse
          (mulOverlap
            (mulOverlap g.inverse g.transition)
            g.transition) := by
          rw [mulOverlap_assoc]
      _ =
        mulOverlap g.inverse
          (mulOverlap oneOverlap g.transition) := by
          rw [g.inverse_mul]
      _ = mulOverlap g.inverse g.transition := by
          rw [oneOverlap_mul]
      _ = oneOverlap := g.inverse_mul
  reduce_transition := by
    rw [reduceOverlap_mul, g.reduce_transition, oneOverlap_mul]

@[simp] theorem square_transition :
    g.square.transition =
      mulOverlap g.transition g.transition :=
  rfl

/-- The transition displacement from the identity. -/
def deviation : Overlap₂ :=
  g.transition - oneOverlap

/-- Squaring a transition is linear to first order.  The exact error is the
product of the transition displacement with itself. -/
theorem square_deviation :
    g.square.transition - oneOverlap -
          (g.deviation + g.deviation) =
      mulOverlap g.deviation g.deviation := by
  have htransition :
      g.transition = g.deviation + oneOverlap := by
    rw [deviation, sub_add_cancel]
  rw [square_transition, htransition]
  simp only [mulOverlap_add_left, mulOverlap_add_right,
    oneOverlap_mul, mul_oneOverlap]
  abel

/-- Twisting the actual principal parts by the line-bundle transition and
then passing to the two formal Čech obstruction coefficients. -/
def twistedConnectingMap :
    PrincipalParts →ₗ[R₂] Obstruction :=
  N13CechLaurentSeriesCore.obstruction.comp
    ((leftMul g.transition).comp
      N13IntegralFormalCech.principalOverlap)

/-- Reduction of formal Čech obstruction coefficients commutes with
coefficientwise reduction of the overlap. -/
theorem reduce_obstruction
    (z : Overlap₂) :
    N13IntegralCechObstruction.reduceCoefficients
        (N13CechLaurentSeriesCore.obstruction z) =
      N13CechLaurentSeriesCore.obstruction
        (reduceOverlap z) := by
  funext i
  fin_cases i <;>
    simp [N13IntegralCechObstruction.reduceCoefficients,
      N13CechLaurentSeriesCore.obstruction,
      reduceOverlap, reduceLaurent, reduceBase]

/-- The twisted connecting map has exactly the computed N13 special
fibre. -/
theorem reduce_twistedConnectingMap
    (a : PrincipalParts) :
    N13IntegralCechObstruction.reduceCoefficients
        (g.twistedConnectingMap a) =
      N13SpecialCechObstruction.connectingMap
        (N13IntegralCechObstruction.reduceCoefficients a) := by
  calc
    N13IntegralCechObstruction.reduceCoefficients
        (g.twistedConnectingMap a) =
        N13CechLaurentSeriesCore.obstruction
          (reduceOverlap
            (mulOverlap g.transition
              (N13IntegralFormalCech.principalOverlap a))) := by
          exact reduce_obstruction _
    _ =
        N13CechLaurentSeriesCore.obstruction
          (mulOverlap
            (reduceOverlap g.transition)
            (reduceOverlap
              (N13IntegralFormalCech.principalOverlap a))) := by
          rw [reduceOverlap_mul]
    _ =
        N13CechLaurentSeriesCore.obstruction
          (reduceOverlap
            (N13IntegralFormalCech.principalOverlap a)) := by
          rw [g.reduce_transition, oneOverlap_mul]
    _ =
        N13IntegralCechObstruction.reduceCoefficients
          (N13CechLaurentSeriesCore.obstruction
            (N13IntegralFormalCech.principalOverlap a)) := by
          exact (reduce_obstruction _).symm
    _ =
        N13IntegralCechObstruction.reduceCoefficients
          (N13IntegralCechObstruction.connectingMap a) := by
          rw [
            N13IntegralFormalCech.obstruction_principalOverlap]
    _ =
        N13SpecialCechObstruction.connectingMap
          (N13IntegralCechObstruction.reduceCoefficients a) :=
          N13IntegralCechObstruction.reduce_connectingMap a

theorem twistedConnectingMap_residueCompatible :
    N13IntegralCechObstruction.ResidueCompatible
      g.twistedConnectingMap :=
  g.reduce_twistedConnectingMap

/-- The identity transition recovers the integral connecting map exactly. -/
theorem identity_twistedConnectingMap :
    identity.twistedConnectingMap =
      N13IntegralCechObstruction.connectingMap := by
  apply LinearMap.ext
  intro a
  change
    N13CechLaurentSeriesCore.obstruction
        (mulOverlap oneOverlap
          (N13IntegralFormalCech.principalOverlap a)) =
      N13IntegralCechObstruction.connectingMap a
  rw [oneOverlap_mul]
  exact
    N13IntegralFormalCech.obstruction_principalOverlap a

/-- Every near-trivial formal line-bundle transition gives a surjective
bounded-pole connecting map. -/
theorem twistedConnectingMap_surjective :
    Function.Surjective g.twistedConnectingMap :=
  N13IntegralCechObstruction.surjective_of_residueCompatible
    g.twistedConnectingMap
    g.twistedConnectingMap_residueCompatible

/-- A bounded-pole cochain closed modulo two for the twisted line bundle
has an actual kernel lift with the same special fibre. -/
theorem exists_twisted_kernel_lift
    (x : PrincipalParts)
    (hx :
      g.twistedConnectingMap x ∈
        IsLocalRing.maximalIdeal R₂ •
          (⊤ : Submodule R₂ Obstruction)) :
    ∃ z : PrincipalParts,
      g.twistedConnectingMap z = 0 ∧
        x - z ∈
          IsLocalRing.maximalIdeal R₂ •
            (⊤ : Submodule R₂ PrincipalParts) :=
  N13IntegralCechObstruction.exists_kernel_lift_of_residueCompatible
    g.twistedConnectingMap
    g.twistedConnectingMap_residueCompatible
    x hx

end NearIdentityTransition

end

end MazurProof.N13FormalLineBundleCech


