-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicAbelChartLaw_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicAbelChartLaw_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:35:57.839994+00:00
-- url     : https://prove2.me/theorems/fa67429f-f791-455b-af7b-39280ae7f429
-- title:
--   FLT.Assumptions.MazurProof.N13TwoAdicAbelChartLaw source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13TwoAdicAbelChartLaw

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TwoAdicAbelChartLaw
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CrossQuadraticPolynomial_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicAbelChartData_p0

set_option autoImplicit false




/-!
# From a regular Abel law to the N13 two-adic kernel chart

The universal addition law is a polynomial in two disjoint coordinate
blocks.  If its restrictions to both axes are the identity, its nonlinear
error lies in the product of the two axis ideals.  Evaluation sends those
axis ideals into the coordinate ideals of the two input points, giving
exactly the error estimate required by `N13TwoAdicKernelChart.Chart`.

The final structure in this file records the remaining geometric seam:
kernel classes must be represented faithfully by the two Hensel disks and
their transported group law must be regular on this chart.
-/

namespace MazurProof.N13TwoAdicAbelChartLaw

noncomputable section

open MvPolynomial

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  ℤ_[2]

abbrev BiPoly : Type :=
  N13CrossQuadraticPolynomial.BiPoly R₂

universe u

variable {K : Type u}

/-- Evaluate the left variables at `z` and the right variables at `w`. -/
def evalPair
    (coord : K → Fin 2 → R₂) (z w : K) :
    BiPoly →+* R₂ :=
  eval₂Hom (RingHom.id R₂)
    (Sum.elim (coord z) (coord w))

@[simp] theorem evalPair_C
    (coord : K → Fin 2 → R₂) (z w : K) (a : R₂) :
    evalPair coord z w (C a) = a := by
  simp [evalPair]

@[simp] theorem evalPair_leftVar
    (coord : K → Fin 2 → R₂) (z w : K) (i : Fin 2) :
    evalPair coord z w
        (N13CrossQuadraticPolynomial.leftVar R₂ i) =
      coord z i := by
  simp [evalPair, N13CrossQuadraticPolynomial.leftVar]

@[simp] theorem evalPair_rightVar
    (coord : K → Fin 2 → R₂) (z w : K) (i : Fin 2) :
    evalPair coord z w
        (N13CrossQuadraticPolynomial.rightVar R₂ i) =
      coord w i := by
  simp [evalPair, N13CrossQuadraticPolynomial.rightVar]

theorem map_leftIdeal_le_coordIdeal
    (coord : K → Fin 2 → R₂) (z w : K) :
    Ideal.map (evalPair coord z w)
        (N13CrossQuadraticPolynomial.leftIdeal R₂) ≤
      N13TwoAdicKernelChart.coordIdeal coord z := by
  rw [Ideal.map_le_iff_le_comap,
    N13CrossQuadraticPolynomial.leftIdeal, Ideal.span_le]
  rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
  change
    evalPair coord z w
        (N13CrossQuadraticPolynomial.leftVar R₂ i) ∈
      N13TwoAdicKernelChart.coordIdeal coord z
  rw [evalPair_leftVar]
  apply Ideal.subset_span
  exact Set.mem_range_self i

theorem map_rightIdeal_le_coordIdeal
    (coord : K → Fin 2 → R₂) (z w : K) :
    Ideal.map (evalPair coord z w)
        (N13CrossQuadraticPolynomial.rightIdeal R₂) ≤
      N13TwoAdicKernelChart.coordIdeal coord w := by
  rw [Ideal.map_le_iff_le_comap,
    N13CrossQuadraticPolynomial.rightIdeal, Ideal.span_le]
  rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
  change
    evalPair coord z w
        (N13CrossQuadraticPolynomial.rightVar R₂ i) ∈
      N13TwoAdicKernelChart.coordIdeal coord w
  rw [evalPair_rightVar]
  apply Ideal.subset_span
  exact Set.mem_range_self i

/-- Evaluation carries every universal mixed term into the product of the
two actual coordinate ideals. -/
theorem eval_mem_coordIdeal_mul
    (coord : K → Fin 2 → R₂) (z w : K)
    (p : BiPoly)
    (hp :
      p ∈ N13CrossQuadraticPolynomial.leftIdeal R₂ *
        N13CrossQuadraticPolynomial.rightIdeal R₂) :
    evalPair coord z w p ∈
      N13TwoAdicKernelChart.coordIdeal coord z *
        N13TwoAdicKernelChart.coordIdeal coord w := by
  have hmap :
      evalPair coord z w p ∈
        Ideal.map (evalPair coord z w)
          (N13CrossQuadraticPolynomial.leftIdeal R₂ *
            N13CrossQuadraticPolynomial.rightIdeal R₂) :=
    Ideal.mem_map_of_mem (evalPair coord z w) hp
  rw [Ideal.map_mul] at hmap
  exact
    (Ideal.mul_mono
      (map_leftIdeal_le_coordIdeal coord z w)
      (map_rightIdeal_le_coordIdeal coord z w)) hmap

variable [AddCommGroup K]

/-- A regular two-coordinate group law written by four-variable
polynomials, with the identity laws on the two coordinate axes. -/
structure PolynomialLaw
    (coord : K → Fin 2 → R₂) where
  polynomial : Fin 2 → BiPoly
  realize :
    ∀ z w i,
      evalPair coord z w (polynomial i) =
        coord (z + w) i
  leftAxis :
    ∀ i,
      N13CrossQuadraticPolynomial.killLeft R₂
          (polynomial i) =
        N13CrossQuadraticPolynomial.rightVar R₂ i
  rightAxis :
    ∀ i,
      N13CrossQuadraticPolynomial.killRight R₂
          (polynomial i) =
        N13CrossQuadraticPolynomial.leftVar R₂ i

/-- The diagonal part of a regular group law.  This is the exact unary
input used by the separatedness argument. -/
structure DoublingLaw
    (coord : K → Fin 2 → R₂) where
  double_error_mem :
    ∀ z i,
      coord (2 • z) i - (coord z i + coord z i) ∈
        N13TwoAdicKernelChart.coordIdeal coord z *
          N13TwoAdicKernelChart.coordIdeal coord z

namespace DoublingLaw

variable {coord : K → Fin 2 → R₂}

/-- A unary doubling law upgrades suitable coordinates to the minimal
two-adic kernel chart. -/
def toChart
    (L : DoublingLaw coord)
    (coord_zero : coord 0 = 0)
    (coord_injective : Function.Injective coord)
    (coord_mem_two :
      ∀ z i,
        coord z i ∈ N13TwoAdicKernelChart.powTwoIdeal 1) :
    N13TwoAdicKernelChart.DoublingChart K where
  coord := coord
  coord_zero := coord_zero
  coord_injective := coord_injective
  coord_mem_two := coord_mem_two
  double_error_mem := L.double_error_mem

end DoublingLaw

namespace PolynomialLaw

variable {coord : K → Fin 2 → R₂}

theorem add_error_mem
    (L : PolynomialLaw coord)
    (z w : K) (i : Fin 2) :
    coord (z + w) i - (coord z i + coord w i) ∈
      N13TwoAdicKernelChart.coordIdeal coord z *
        N13TwoAdicKernelChart.coordIdeal coord w := by
  have huniversal :=
    N13CrossQuadraticPolynomial.error_mem_cross R₂
      L.polynomial L.leftAxis L.rightAxis i
  have heval :=
    eval_mem_coordIdeal_mul coord z w
      (N13CrossQuadraticPolynomial.error
        R₂ L.polynomial i)
      huniversal
  have hrealize :
      evalPair coord z w
          (N13CrossQuadraticPolynomial.error
            R₂ L.polynomial i) =
        coord (z + w) i - (coord z i + coord w i) := by
    simp only [N13CrossQuadraticPolynomial.error, map_sub,
      L.realize z w i, evalPair_leftVar, evalPair_rightVar]
    ring
  rw [hrealize] at heval
  exact heval

/-- Restrict a binary polynomial group law to the diagonal. -/
def toDoublingLaw
    (L : PolynomialLaw coord) :
    DoublingLaw coord where
  double_error_mem z i := by
    simpa only [two_nsmul] using L.add_error_mem z z i

/-- A regular polynomial law upgrades suitable coordinates to the abstract
two-adic kernel chart. -/
def toChart
    (L : PolynomialLaw coord)
    (coord_zero : coord 0 = 0)
    (coord_injective : Function.Injective coord)
    (coord_mem_two :
      ∀ z i,
        coord z i ∈ N13TwoAdicKernelChart.powTwoIdeal 1) :
    N13TwoAdicKernelChart.Chart K where
  coord := coord
  coord_zero := coord_zero
  coord_injective := coord_injective
  coord_mem_two := coord_mem_two
  add_error_mem := L.add_error_mem

end PolynomialLaw

/-- The minimal geometric input required for the separatedness argument:
faithful disk representatives and their unary doubling estimate. -/
structure DoublingGeometricData
    (K : Type u) [AddCommGroup K] where
  pair : K → N13TwoAdicAbelChartData.DiskPair
  pair_zero :
    pair 0 = N13TwoAdicAbelChartData.basePair
  pair_injective : Function.Injective pair
  law :
    DoublingLaw
      (fun z =>
        N13TwoAdicAbelChartData.DiskPair.coord (pair z))

namespace DoublingGeometricData

variable (D : DoublingGeometricData K)

def coord : K → Fin 2 → R₂ :=
  fun z => N13TwoAdicAbelChartData.DiskPair.coord (D.pair z)

@[simp] theorem coord_zero :
    D.coord 0 = 0 := by
  rw [coord, D.pair_zero]
  exact N13TwoAdicAbelChartData.DiskPair.coord_basePair

theorem coord_injective :
    Function.Injective D.coord :=
  N13TwoAdicAbelChartData.DiskPair.coord_injective.comp
    D.pair_injective

theorem coord_mem_two
    (z : K) (i : Fin 2) :
    D.coord z i ∈
      N13TwoAdicKernelChart.powTwoIdeal 1 :=
  N13TwoAdicAbelChartData.DiskPair.coord_mem_two
    (D.pair z) i

/-- The minimal unary chart attached to disk representatives. -/
def chart :
    N13TwoAdicKernelChart.DoublingChart K :=
  D.law.toChart D.coord_zero D.coord_injective
    D.coord_mem_two

include D

theorem separated :
    N18RouteC.Separated.NSeparated K 2 :=
  N13TwoAdicKernelChart.DoublingChart.separated (chart D)

end DoublingGeometricData

/-- The precise geometric input still required to identify a reduction
kernel with the two-disk Abel chart. -/
structure GeometricData (K : Type u) [AddCommGroup K] where
  pair : K → N13TwoAdicAbelChartData.DiskPair
  pair_zero :
    pair 0 = N13TwoAdicAbelChartData.basePair
  pair_injective : Function.Injective pair
  law :
    PolynomialLaw
      (fun z =>
        N13TwoAdicAbelChartData.DiskPair.coord (pair z))

namespace GeometricData

variable (D : GeometricData K)

def coord : K → Fin 2 → R₂ :=
  fun z => N13TwoAdicAbelChartData.DiskPair.coord (D.pair z)

@[simp] theorem coord_zero :
    D.coord 0 = 0 := by
  rw [coord, D.pair_zero]
  exact N13TwoAdicAbelChartData.DiskPair.coord_basePair

theorem coord_injective :
    Function.Injective D.coord :=
  N13TwoAdicAbelChartData.DiskPair.coord_injective.comp
    D.pair_injective

theorem coord_mem_two
    (z : K) (i : Fin 2) :
    D.coord z i ∈
      N13TwoAdicKernelChart.powTwoIdeal 1 :=
  N13TwoAdicAbelChartData.DiskPair.coord_mem_two
    (D.pair z) i

/-- The actual kernel chart obtained once the geometric representative and
regularity statements are supplied. -/
def chart :
    N13TwoAdicKernelChart.Chart K :=
  D.law.toChart D.coord_zero D.coord_injective
    D.coord_mem_two

/-- Forget the unused off-diagonal part of the polynomial law. -/
def toDoublingGeometricData :
    DoublingGeometricData K where
  pair := D.pair
  pair_zero := D.pair_zero
  pair_injective := D.pair_injective
  law := D.law.toDoublingLaw

include D

theorem separated :
    N18RouteC.Separated.NSeparated K 2 :=
  N13TwoAdicKernelChart.Chart.separated (chart D)

end GeometricData

end

end MazurProof.N13TwoAdicAbelChartLaw


