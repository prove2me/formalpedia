-- Prove2me | Definitions.Def_MazurN13_p03
-- name    : MazurN13_p03
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-08T00:05:57.218993+00:00
-- url     : https://prove2.me/theorems/ba37c7e5-f783-47ee-afe6-0f77ba29679d
-- title:
--   Mazur order 13 (Huang FLT port), part 3/33
-- statement:
--   Part 3 of 33 of a machine-checked Lean proof that no elliptic curve over $\mathbb{Q}$ has a rational point of exact order $13$ (the case $N=13$ of Mazur's torsion theorem). The chain as a whole proves that the only rational affine points of the genus-two curve $Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$ (a model of $X_1(13)$) have $X\in\{0,-1\}$ (cusps); the final result is `MazurProof.N13ConstructedRationalPointTheorem.affine_x_is_cuspidal` in part {N}.
--
--   This part is not a single definition: it is a verbatim, sorry-free slice of Xiang Huang's Lean development, ported to this Mathlib and split into compile-sized pieces, each importing the previous part. It contains the modules:
--
--   - `FLT.Assumptions.MazurProof.N13SpecialGraphReduction`
--   - `FLT.Assumptions.MazurProof.N13TwoAdicDisks`
--   - `FLT.Assumptions.MazurProof.N18RouteC_Separated`
--   - `FLT.Assumptions.MazurProof.N13TwoAdicKernelChart`
--   - `FLT.Assumptions.MazurProof.N13TwoAdicAbelChartData`
--   - `FLT.Assumptions.MazurProof.N13InfinityAPI`
--   - `FLT.Assumptions.MazurProof.N13InfinityMinus`
--   - `FLT.Assumptions.MazurProof.N13InfinityMinusAPI`
--   - `FLT.Assumptions.MazurProof.N13LaurentPolynomialOrder`
--   - `FLT.Assumptions.MazurProof.N13BranchNorm`
--   - `FLT.Assumptions.MazurProof.N13BranchLeading`
--   - `FLT.Assumptions.MazurProof.N13FactorRigidity`
--   - `FLT.Assumptions.MazurProof.SexticFunctionConjugation`
--   - `FLT.Assumptions.MazurProof.SexticMumfordIdealConjugation`
--   - `FLT.Assumptions.MazurProof.SexticMumfordPrincipalNumerator`
--
--   Port notes: API drift fixes only (transparency options, renamed lemmas, explicit instances); local notations expanded, `private` removed.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT commit 51bbb4f, directory FLT/Assumptions/MazurProof (N13* and SexticMumford* modules and their dependencies)

import Mathlib
import Definitions.Def_MazurN13_p02
set_option maxHeartbeats 1000000

-- module FLT.Assumptions.MazurProof.N13SpecialGraphReduction
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialGraphReduction =====
section

/-!
# Abel-compatible reduction of integral N13 Mumford graphs

Coefficientwise reduction of a smooth integral generalized Mumford graph is
again a special-fibre Mumford graph.  If its effective degree-two divisor
has the selected set-valued Abel class, special Abel rigidity identifies the
literal reduced graph ideal with `(X²+X,Y)`.

Combining this with exact contraction of integral sextic graphs gives the
representative-level special-ideal equality required by the two-fibre graph
recovery theorem.  The remaining geometric input is now only the existence
of an integral representative and its Abel compatibility.
-/

open Polynomial

namespace MazurProof.N13SpecialGraphReduction

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev SmoothMumford₂ : Type :=
  N13GeneralizedMumfordReduction.SmoothMumford₂

/-- Monic degree is preserved by coefficientwise reduction. -/
theorem reduceSmoothMumford_u_natDegree
    (D : SmoothMumford₂)
    (hdeg : D.u.natDegree = 2) :
    (N13GeneralizedMumfordReduction.reduceSmoothMumford D).u.natDegree =
      2 := by
  change
    (D.u.map
      N13GeneralizedMumfordReduction.reduceBase).natDegree = 2
  calc
    (D.u.map
        N13GeneralizedMumfordReduction.reduceBase).natDegree =
        D.u.natDegree :=
      D.u_monic.natDegree_map
        N13GeneralizedMumfordReduction.reduceBase
    _ = 2 := hdeg

/-- For an integral quadratic graph, mapped-ideal equality is equivalent to
the intrinsic special-fibre Abel equality. -/
theorem setAbel_eq_iff_map_mumfordIdeal_eq_special
    (D : SmoothMumford₂)
    (hdeg : D.u.natDegree = 2) :
    N13AbelFiberTwoModel.abel
          (N13SpecialGraphDivisor.graphDivisor
            (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
            (reduceSmoothMumford_u_natDegree D hdeg)) =
        N13AbelFiberTwoModel.abel
          N13AbelChartBase.specialBaseDivisor ↔
      Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := N13GeneralizedMumfordReduction.R₂) D.u D.v) =
        N13SpecialQuotientBasis.specialIdeal := by
  rw [N13GeneralizedMumfordReduction.map_smoothMumfordIdeal]
  exact
    N13SpecialGraphDivisor.setAbel_eq_iff_mumfordIdeal_eq_special
      (N13GeneralizedMumfordReduction.reduceSmoothMumford D)
      (reduceSmoothMumford_u_natDegree D hdeg)

end

end MazurProof.N13SpecialGraphReduction

end
end

-- module FLT.Assumptions.MazurProof.N13TwoAdicDisks
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicDisks =====
section

/-!
# The two integral residue disks used by the N13 Abel chart

For the good equation

`y² + (x³ + x + 1)y = x⁵ + x⁴`

over the two-adic integers, the fibres above the residue disks of `0` and
`-1` have a unique point whose `y`-coordinate lies in the maximal ideal.
Existence is one-variable Hensel lifting in the `y` coordinate.  Uniqueness
is the elementary factorization of the difference of two roots.

This is the local-curve part of the nonspecial Abel chart; it uses neither a
Picard scheme nor finite congruence tables.
-/

open Polynomial

namespace MazurProof.N13TwoAdicDisks

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  ℤ_[2]

/-- The maximal ideal `(2)` of the two-adic integers. -/
abbrev maximal : Ideal R₂ :=
  IsLocalRing.maximalIdeal R₂

/-- A useful local-ring form of the fact that being congruent to a unit
modulo the maximal ideal implies being a unit. -/
theorem isUnit_of_sub_mem_maximal
    {a u : R₂} (hu : IsUnit u)
    (hau : a - u ∈ maximal) :
    IsUnit a := by
  by_contra ha
  have ha_mem : a ∈ maximal := by
    simpa only [maximal, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] using ha
  have hu_mem : u ∈ maximal := by
    have hsub := maximal.sub_mem ha_mem hau
    convert hsub using 1
    ring
  have hnot : ¬IsUnit u := by
    simpa only [maximal, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] using hu_mem
  exact hnot hu

/-- The good equation, viewed as a monic polynomial in `Y`. -/
abbrev yFiber (x : R₂) : R₂[X] :=
  N13GoodModelTwo.affineFiber x

theorem yFiber_monic (x : R₂) :
    (yFiber x).Monic := by
  unfold yFiber N13GoodModelTwo.affineFiber
  monicity <;> norm_num

@[simp] theorem yFiber_eval (x y : R₂) :
    (yFiber x).eval y =
      N13GoodModelTwo.affineResidual x y :=
  N13GoodModelTwo.affineFiber_eval x y

@[simp] theorem yFiber_derivative_eval_zero (x : R₂) :
    (yFiber x).derivative.eval 0 =
      N13GoodModelTwo.h x := by
  rw [N13GoodModelTwo.affineFiber_derivative_eval]
  simp [N13GoodModelTwo.affineDerivativeY]

/-- Hensel lifting in the `Y` coordinate under the exact two hypotheses
needed at a residue disk. -/
theorem exists_y_mem_maximal
    (x : R₂)
    (hh : IsUnit (N13GoodModelTwo.h x))
    (hrhs : N13GoodModelTwo.rhs x ∈ maximal) :
    ∃ y : R₂,
      N13GoodModelTwo.AffineEquation x y ∧
        y ∈ maximal := by
  have heval :
      (yFiber x).eval 0 ∈ maximal := by
    have hneg := maximal.neg_mem hrhs
    simpa [yFiber_eval, N13GoodModelTwo.affineResidual] using hneg
  have hderiv :
      IsUnit
        (Ideal.Quotient.mk maximal
          ((yFiber x).derivative.eval 0)) := by
    rw [yFiber_derivative_eval_zero]
    exact hh.map (Ideal.Quotient.mk maximal)
  obtain ⟨y, hy, hymem⟩ :=
    HenselianRing.is_henselian
      (R := R₂) (I := maximal)
      (yFiber x) (yFiber_monic x) 0 heval hderiv
  refine ⟨y, ?_, by simpa using hymem⟩
  rw [N13GoodModelTwo.affineEquation_iff_residual,
    ← yFiber_eval]
  exact hy

/-- Two roots in the same selected `Y` residue disk coincide. -/
theorem y_eq_of_mem_maximal
    (x y z : R₂)
    (hh : IsUnit (N13GoodModelTwo.h x))
    (hy : N13GoodModelTwo.AffineEquation x y)
    (hz : N13GoodModelTwo.AffineEquation x z)
    (hymem : y ∈ maximal)
    (hzmem : z ∈ maximal) :
    y = z := by
  have hyzero :
      y ^ 2 + N13GoodModelTwo.h x * y -
          N13GoodModelTwo.rhs x = 0 :=
    sub_eq_zero.mpr hy
  have hzzero :
      z ^ 2 + N13GoodModelTwo.h x * z -
          N13GoodModelTwo.rhs x = 0 :=
    sub_eq_zero.mpr hz
  have hsum_mem : y + z ∈ maximal :=
    maximal.add_mem hymem hzmem
  have hunit :
      IsUnit (y + z + N13GoodModelTwo.h x) := by
    apply isUnit_of_sub_mem_maximal hh
    convert hsum_mem using 1
    ring
  have hprod :
      (y - z) *
        (y + z + N13GoodModelTwo.h x) = 0 := by
    calc
      (y - z) *
          (y + z + N13GoodModelTwo.h x) =
        (y ^ 2 + N13GoodModelTwo.h x * y -
            N13GoodModelTwo.rhs x) -
          (z ^ 2 + N13GoodModelTwo.h x * z -
            N13GoodModelTwo.rhs x) := by ring
      _ = 0 := by rw [hyzero, hzzero, sub_self]
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hprod).resolve_right hunit.ne_zero)

/-- The selected `Y` lift is unique whenever the fibre has unit derivative
and its constant term lies in the maximal ideal. -/
theorem existsUnique_y_mem_maximal
    (x : R₂)
    (hh : IsUnit (N13GoodModelTwo.h x))
    (hrhs : N13GoodModelTwo.rhs x ∈ maximal) :
    ∃! y : R₂,
      N13GoodModelTwo.AffineEquation x y ∧
        y ∈ maximal := by
  obtain ⟨y, hy, hymem⟩ :=
    exists_y_mem_maximal x hh hrhs
  refine ⟨y, ⟨hy, hymem⟩, ?_⟩
  intro z hz
  exact y_eq_of_mem_maximal x z y hh hz.1 hy hz.2 hymem

/-! ## The disk above `(0,0)` -/

theorem h_isUnit_of_mem_zeroDisk
    {x : R₂} (hx : x ∈ maximal) :
    IsUnit (N13GoodModelTwo.h x) := by
  apply isUnit_of_sub_mem_maximal isUnit_one
  have hm :=
    maximal.mul_mem_left (x ^ 2 + 1) hx
  convert hm using 1
  simp only [N13GoodModelTwo.h]
  ring

theorem rhs_mem_of_mem_zeroDisk
    {x : R₂} (hx : x ∈ maximal) :
    N13GoodModelTwo.rhs x ∈ maximal := by
  have hm :=
    maximal.mul_mem_left (x ^ 3 * (x + 1)) hx
  convert hm using 1
  simp only [N13GoodModelTwo.rhs]
  ring

theorem existsUnique_zeroDisk_y
    (x : R₂) (hx : x ∈ maximal) :
    ∃! y : R₂,
      N13GoodModelTwo.AffineEquation x y ∧
        y ∈ maximal :=
  existsUnique_y_mem_maximal x
    (h_isUnit_of_mem_zeroDisk hx)
    (rhs_mem_of_mem_zeroDisk hx)

/-- The unique `Y` coordinate above an `X` in the residue disk of zero. -/
def zeroDiskY (x : R₂) (hx : x ∈ maximal) : R₂ :=
  Classical.choose (existsUnique_zeroDisk_y x hx).exists

theorem zeroDiskY_spec
    (x : R₂) (hx : x ∈ maximal) :
    N13GoodModelTwo.AffineEquation x (zeroDiskY x hx) ∧
      zeroDiskY x hx ∈ maximal :=
  Classical.choose_spec (existsUnique_zeroDisk_y x hx).exists

theorem y_eq_zeroDiskY
    (x : R₂) (hx : x ∈ maximal)
    {y : R₂}
    (hy : N13GoodModelTwo.AffineEquation x y)
    (hymem : y ∈ maximal) :
    y = zeroDiskY x hx :=
  y_eq_of_mem_maximal x y (zeroDiskY x hx)
    (h_isUnit_of_mem_zeroDisk hx)
    hy (zeroDiskY_spec x hx).1 hymem
    (zeroDiskY_spec x hx).2

@[simp] theorem zeroDiskY_zero :
    zeroDiskY 0 maximal.zero_mem = 0 := by
  symm
  apply y_eq_zeroDiskY 0 maximal.zero_mem
  · simp [N13GoodModelTwo.AffineEquation,
      N13GoodModelTwo.h, N13GoodModelTwo.rhs]
  · exact maximal.zero_mem

/-! ## The disk above `(-1,0)` -/

theorem h_isUnit_of_mem_negOneDisk
    {x : R₂} (hx : x + 1 ∈ maximal) :
    IsUnit (N13GoodModelTwo.h x) := by
  apply isUnit_of_sub_mem_maximal isUnit_neg_one
  have hm :=
    maximal.mul_mem_left (x ^ 2 - x + 2) hx
  convert hm using 1
  simp only [N13GoodModelTwo.h]
  ring

theorem rhs_mem_of_mem_negOneDisk
    {x : R₂} (hx : x + 1 ∈ maximal) :
    N13GoodModelTwo.rhs x ∈ maximal := by
  have hm :=
    maximal.mul_mem_left (x ^ 4) hx
  convert hm using 1
  simp only [N13GoodModelTwo.rhs]
  ring

theorem existsUnique_negOneDisk_y
    (x : R₂) (hx : x + 1 ∈ maximal) :
    ∃! y : R₂,
      N13GoodModelTwo.AffineEquation x y ∧
        y ∈ maximal :=
  existsUnique_y_mem_maximal x
    (h_isUnit_of_mem_negOneDisk hx)
    (rhs_mem_of_mem_negOneDisk hx)

/-- The unique `Y` coordinate above an `X` in the residue disk of `-1`. -/
def negOneDiskY (x : R₂) (hx : x + 1 ∈ maximal) : R₂ :=
  Classical.choose (existsUnique_negOneDisk_y x hx).exists

theorem negOneDiskY_spec
    (x : R₂) (hx : x + 1 ∈ maximal) :
    N13GoodModelTwo.AffineEquation x (negOneDiskY x hx) ∧
      negOneDiskY x hx ∈ maximal :=
  Classical.choose_spec (existsUnique_negOneDisk_y x hx).exists

theorem y_eq_negOneDiskY
    (x : R₂) (hx : x + 1 ∈ maximal)
    {y : R₂}
    (hy : N13GoodModelTwo.AffineEquation x y)
    (hymem : y ∈ maximal) :
    y = negOneDiskY x hx :=
  y_eq_of_mem_maximal x y (negOneDiskY x hx)
    (h_isUnit_of_mem_negOneDisk hx)
    hy (negOneDiskY_spec x hx).1 hymem
    (negOneDiskY_spec x hx).2

@[simp] theorem negOneDiskY_negOne :
    negOneDiskY (-1) (by simp) = 0 := by
  symm
  apply y_eq_negOneDiskY (-1) (by simp)
  · simp [N13GoodModelTwo.AffineEquation,
      N13GoodModelTwo.h, N13GoodModelTwo.rhs]
    ring
  · exact maximal.zero_mem

end

end MazurProof.N13TwoAdicDisks

end
end

-- module FLT.Assumptions.MazurProof.N18RouteC_Separated
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N18RouteC_Separated =====
section

/-!
# Weak descent and formal-kernel separatedness for N18 Route C

This file is independent of any Mordell--Weil finite-generation theorem.  It
turns a weak `3`-descent, a seven-torsion reduction group, and strict growth in
the formal kernel into the uniform annihilator `[21]`.
-/

namespace MazurProof.N18RouteC.Separated

noncomputable section

def InfinitelyNSmulDivisible
    {G : Type*} [AddCommGroup G] (n : ℕ) (x : G) : Prop :=
  ∀ k : ℕ, ∃ y : G, (n ^ k) • y = x

def NSeparated (G : Type*) [AddCommGroup G] (n : ℕ) : Prop :=
  ∀ x : G, InfinitelyNSmulDivisible n x → x = 0

theorem nsmul_nsmul_comm
    {G : Type*} [AddCommGroup G]
    (m n : ℕ) (x : G) :
    m • (n • x) = n • (m • x) := by
  calc
    m • (n • x) = (n * m) • x := (mul_nsmul x n m).symm
    _ = (m * n) • x := by rw [Nat.mul_comm]
    _ = n • (m • x) := mul_nsmul x m n

end

end MazurProof.N18RouteC.Separated

end
end

-- module FLT.Assumptions.MazurProof.N13TwoAdicKernelChart
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicKernelChart =====
section

/-!
# A structural two-adic kernel chart

This file isolates the elementary formal-group argument needed for N13.
Suppose an additive group has two coordinates in `ℤ₂`, every coordinate is
divisible by two, and addition differs from coordinatewise addition by an
element of the product of the two coordinate ideals.  Then doubling raises
coordinate depth by at least one.  Infinite two-divisibility is therefore
incompatible with the separated two-adic filtration.

No formal power series, point table, or explicit genus-two addition formula
is used below.  The eventual curve-specific input is only the
cross-quadratic error statement.
-/

namespace MazurProof.N13TwoAdicKernelChart

noncomputable section

open N18RouteC.Separated

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  ℤ_[2]

/-- The principal ideal `(2^n)` in the two-adic integers. -/
def powTwoIdeal (n : ℕ) : Ideal R₂ :=
  Ideal.span ({(2 : R₂) ^ n} : Set R₂)

theorem powTwoIdeal_mul (r s : ℕ) :
    powTwoIdeal r * powTwoIdeal s =
      powTwoIdeal (r + s) := by
  simp only [powTwoIdeal,
    Ideal.span_singleton_mul_span_singleton, ← pow_add]

theorem powTwoIdeal_antitone
    {r s : ℕ} (hrs : r ≤ s) :
    powTwoIdeal s ≤ powTwoIdeal r := by
  rw [powTwoIdeal, powTwoIdeal,
    Ideal.span_singleton_le_iff_mem,
    Ideal.mem_span_singleton]
  exact pow_dvd_pow (2 : R₂) hrs

universe u

variable {K : Type u} [AddCommGroup K]

/-- The ideal generated by the two coordinates of `z`. -/
def coordIdeal
    (coord : K → Fin 2 → R₂) (z : K) :
    Ideal R₂ :=
  Ideal.span (Set.range (coord z))

set_option maxHeartbeats 4000000 in
/-- A two-coordinate chart whose transported addition law has only mixed
quadratic and higher error terms. -/
structure Chart (K : Type u) [AddCommGroup K] where
  coord : K → Fin 2 → R₂
  coord_zero : coord 0 = 0
  coord_injective : Function.Injective coord
  coord_mem_two :
    ∀ z i, coord z i ∈ powTwoIdeal 1
  add_error_mem :
    ∀ z w i,
      coord (z + w) i - (coord z i + coord w i) ∈
        coordIdeal coord z * coordIdeal coord w

namespace Chart

variable (C : Chart K)

/-- All chart coordinates have depth at least `n`. -/
def CoordDepth (n : ℕ) (z : K) : Prop :=
  ∀ i, C.coord z i ∈ powTwoIdeal n

theorem coordIdeal_le_powTwoIdeal
    {n : ℕ} {z : K}
    (hz : C.CoordDepth n z) :
    coordIdeal C.coord z ≤ powTwoIdeal n := by
  rw [coordIdeal, Ideal.span_le]
  intro a ha
  obtain ⟨i, rfl⟩ := ha
  exact hz i

theorem add_error_mem_powTwoIdeal
    {r s : ℕ} {z w : K}
    (hz : C.CoordDepth r z)
    (hw : C.CoordDepth s w)
    (i : Fin 2) :
    C.coord (z + w) i -
        (C.coord z i + C.coord w i) ∈
      powTwoIdeal (r + s) := by
  rw [← powTwoIdeal_mul]
  exact
    (Ideal.mul_mono
      (C.coordIdeal_le_powTwoIdeal hz)
      (C.coordIdeal_le_powTwoIdeal hw))
      (C.add_error_mem z w i)

theorem two_mul_mem_next
    {n : ℕ} {a : R₂}
    (ha : a ∈ powTwoIdeal n) :
    a + a ∈ powTwoIdeal (n + 1) := by
  rw [powTwoIdeal, Ideal.mem_span_singleton] at ha ⊢
  obtain ⟨b, hb⟩ := ha
  refine ⟨b, ?_⟩
  rw [hb, pow_succ]
  ring

/-- Doubling raises the two-adic coordinate depth by at least one. -/
theorem two_nsmul_depth
    {n : ℕ} (hn : 1 ≤ n) {z : K}
    (hz : C.CoordDepth n z) :
    C.CoordDepth (n + 1) (2 • z) := by
  intro i
  have herr :
      C.coord (z + z) i -
          (C.coord z i + C.coord z i) ∈
        powTwoIdeal (n + n) :=
    C.add_error_mem_powTwoIdeal hz hz i
  have herr' :
      C.coord (z + z) i -
          (C.coord z i + C.coord z i) ∈
        powTwoIdeal (n + 1) :=
    powTwoIdeal_antitone (by omega) herr
  have hlinear :
      C.coord z i + C.coord z i ∈
        powTwoIdeal (n + 1) :=
    two_mul_mem_next (hz i)
  have hsum :=
    Ideal.add_mem (powTwoIdeal (n + 1)) herr' hlinear
  simpa [two_nsmul] using hsum

/-- Iterated doubling starts at depth one and gains one level per step. -/
theorem twoPow_depth
    (z : K) :
    ∀ k : ℕ,
      C.CoordDepth (k + 1) ((2 ^ k) • z) := by
  intro k
  induction k with
  | zero =>
      intro i
      simpa only [pow_zero, one_nsmul, zero_add] using
        C.coord_mem_two z i
  | succ k ih =>
      have hstep :
          C.CoordDepth (k + 1 + 1)
            (2 • ((2 ^ k) • z)) :=
        C.two_nsmul_depth (n := k + 1) (by omega) ih
      simpa [pow_succ, mul_nsmul] using hstep

theorem coord_eq_zero_of_all_depth
    {z : K}
    (hz : ∀ n : ℕ, C.CoordDepth n z) :
    C.coord z = 0 := by
  funext i
  by_contra hi
  have hmem :
      C.coord z i ∈
        Ideal.span
          ({(2 : R₂) ^
            (C.coord z i).valuation.succ} : Set R₂) := by
    simpa only [powTwoIdeal] using
      hz (C.coord z i).valuation.succ i
  have hle :
      (C.coord z i).valuation.succ ≤
        (C.coord z i).valuation :=
    (PadicInt.mem_span_pow_iff_le_valuation
      (C.coord z i) hi
      (C.coord z i).valuation.succ).mp hmem
  omega

include C

/-- The cross-quadratic two-adic chart is separated: no nonzero element is
divisible by every power of two. -/
theorem separated :
    NSeparated K 2 := by
  intro z hdiv
  have hall : ∀ n : ℕ, C.CoordDepth n z := by
    intro n
    cases n with
    | zero =>
        intro i
        simp [powTwoIdeal]
    | succ k =>
        obtain ⟨y, hy⟩ := hdiv k
        have hdepth := C.twoPow_depth y k
        rw [hy] at hdepth
        simpa [Nat.succ_eq_add_one] using hdepth
  apply C.coord_injective
  rw [C.coord_zero]
  exact C.coord_eq_zero_of_all_depth hall

end Chart

/-! ## The unary doubling interface

Separatedness only iterates multiplication by two.  The binary addition
estimate above is therefore stronger than necessary: it is enough to know
the same quadratic error estimate on the diagonal. -/

set_option maxHeartbeats 4000000 in
/-- A two-coordinate chart with only the diagonal doubling estimate needed
for two-adic separatedness. -/
structure DoublingChart (K : Type u) [AddCommGroup K] where
  coord : K → Fin 2 → R₂
  coord_zero : coord 0 = 0
  coord_injective : Function.Injective coord
  coord_mem_two :
    ∀ z i, coord z i ∈ powTwoIdeal 1
  double_error_mem :
    ∀ z i,
      coord (2 • z) i - (coord z i + coord z i) ∈
        coordIdeal coord z * coordIdeal coord z

namespace DoublingChart

variable (C : DoublingChart K)

/-- All unary-chart coordinates have depth at least `n`. -/
def CoordDepth (n : ℕ) (z : K) : Prop :=
  ∀ i, C.coord z i ∈ powTwoIdeal n

theorem coordIdeal_le_powTwoIdeal
    {n : ℕ} {z : K}
    (hz : C.CoordDepth n z) :
    coordIdeal C.coord z ≤ powTwoIdeal n := by
  rw [coordIdeal, Ideal.span_le]
  intro a ha
  obtain ⟨i, rfl⟩ := ha
  exact hz i

theorem two_mul_mem_next
    {n : ℕ} {a : R₂}
    (ha : a ∈ powTwoIdeal n) :
    a + a ∈ powTwoIdeal (n + 1) := by
  rw [powTwoIdeal, Ideal.mem_span_singleton] at ha ⊢
  obtain ⟨b, hb⟩ := ha
  refine ⟨b, ?_⟩
  rw [hb, pow_succ]
  ring

/-- The diagonal quadratic estimate raises coordinate depth under
doubling. -/
theorem two_nsmul_depth
    {n : ℕ} (hn : 1 ≤ n) {z : K}
    (hz : C.CoordDepth n z) :
    C.CoordDepth (n + 1) (2 • z) := by
  intro i
  have herr :
      C.coord (2 • z) i -
          (C.coord z i + C.coord z i) ∈
        powTwoIdeal (n + n) := by
    rw [← powTwoIdeal_mul]
    exact
      (Ideal.mul_mono
        (C.coordIdeal_le_powTwoIdeal hz)
        (C.coordIdeal_le_powTwoIdeal hz))
        (C.double_error_mem z i)
  have herr' :
      C.coord (2 • z) i -
          (C.coord z i + C.coord z i) ∈
        powTwoIdeal (n + 1) :=
    powTwoIdeal_antitone (by omega) herr
  have hlinear :
      C.coord z i + C.coord z i ∈
        powTwoIdeal (n + 1) :=
    two_mul_mem_next (hz i)
  have hsum :=
    Ideal.add_mem (powTwoIdeal (n + 1)) herr' hlinear
  simpa using hsum

/-- Iterated doubling gains one level of depth at every step. -/
theorem twoPow_depth
    (z : K) :
    ∀ k : ℕ,
      C.CoordDepth (k + 1) ((2 ^ k) • z) := by
  intro k
  induction k with
  | zero =>
      intro i
      simpa only [pow_zero, one_nsmul, zero_add] using
        C.coord_mem_two z i
  | succ k ih =>
      have hstep :
          C.CoordDepth (k + 1 + 1)
            (2 • ((2 ^ k) • z)) :=
        C.two_nsmul_depth (n := k + 1) (by omega) ih
      simpa [pow_succ, mul_nsmul] using hstep

theorem coord_eq_zero_of_all_depth
    {z : K}
    (hz : ∀ n : ℕ, C.CoordDepth n z) :
    C.coord z = 0 := by
  funext i
  by_contra hi
  have hmem :
      C.coord z i ∈
        Ideal.span
          ({(2 : R₂) ^
            (C.coord z i).valuation.succ} : Set R₂) := by
    simpa only [powTwoIdeal] using
      hz (C.coord z i).valuation.succ i
  have hle :
      (C.coord z i).valuation.succ ≤
        (C.coord z i).valuation :=
    (PadicInt.mem_span_pow_iff_le_valuation
      (C.coord z i) hi
      (C.coord z i).valuation.succ).mp hmem
  omega

include C

/-- The unary doubling chart is already sufficient for two-adic
separatedness. -/
theorem separated :
    NSeparated K 2 := by
  intro z hdiv
  have hall : ∀ n : ℕ, C.CoordDepth n z := by
    intro n
    cases n with
    | zero =>
        intro i
        simp [powTwoIdeal]
    | succ k =>
        obtain ⟨y, hy⟩ := hdiv k
        have hdepth := C.twoPow_depth y k
        rw [hy] at hdepth
        simpa [Nat.succ_eq_add_one] using hdepth
  apply C.coord_injective
  rw [C.coord_zero]
  exact C.coord_eq_zero_of_all_depth hall

end DoublingChart

end

end MazurProof.N13TwoAdicKernelChart

end
end

-- module FLT.Assumptions.MazurProof.N13TwoAdicAbelChartData
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartData =====
section

/-!
# Integral Mumford data on the nonspecial N13 two-adic Abel chart

A point in the residue disk of `(0,0)` and a point in the residue disk of
`(-1,0)` have distinct `x`-coordinates by a unit.  Lagrange interpolation
therefore gives an integral graph polynomial through the two points.

The product of the two linear factors divides the curve residual.  The same
interpolation argument, applied to the inverses of the two vertical
derivatives, gives the smoothness Bezout identity.  Thus every such pair
defines smooth generalized Mumford data over `ℤ₂`, without a search through
congruence classes.
-/

open Polynomial

namespace MazurProof.N13TwoAdicAbelChartData

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  ℤ_[2]

abbrev maximal : Ideal R₂ :=
  N13TwoAdicDisks.maximal

set_option maxHeartbeats 4000000 in
/-- A pair of points in the two residue disks used by the nonspecial chart.
The `y`-coordinates are the canonical Hensel lifts and are therefore not
stored separately. -/
structure DiskPair where
  x₀ : R₂
  x₁ : R₂
  x₀_mem : x₀ ∈ maximal
  x₁_add_one_mem : x₁ + 1 ∈ maximal

/-- The distinguished pair `(0,0)+(-1,0)`. -/
def basePair : DiskPair where
  x₀ := 0
  x₁ := -1
  x₀_mem := maximal.zero_mem
  x₁_add_one_mem := by simp

namespace DiskPair

variable (P : DiskPair)

theorem reduceBase_eq_zero_of_mem
    {a : R₂} (ha : a ∈ maximal) :
    N13GeneralizedMumfordReduction.reduceBase a = 0 := by
  apply RingHom.mem_ker.mp
  rw [N13GeneralizedMumfordReduction.reduceBase,
    PadicInt.ker_toZMod]
  exact ha

@[simp] theorem reduceBase_x₀ :
    N13GeneralizedMumfordReduction.reduceBase P.x₀ = 0 :=
  reduceBase_eq_zero_of_mem P.x₀_mem

@[simp] theorem reduceBase_x₁ :
    N13GeneralizedMumfordReduction.reduceBase P.x₁ = 1 := by
  have hsum :
    N13GeneralizedMumfordReduction.reduceBase P.x₁ + 1 = 0 := by
    simpa only [map_add, map_one] using
      reduceBase_eq_zero_of_mem P.x₁_add_one_mem
  simpa only [CharTwo.neg_eq] using
    eq_neg_of_add_eq_zero_left hsum

def y₀ : R₂ :=
  N13TwoAdicDisks.zeroDiskY P.x₀ P.x₀_mem

def y₁ : R₂ :=
  N13TwoAdicDisks.negOneDiskY P.x₁ P.x₁_add_one_mem

@[simp] theorem basePair_y₀ :
    basePair.y₀ = 0 :=
  N13TwoAdicDisks.zeroDiskY_zero

@[simp] theorem basePair_y₁ :
    basePair.y₁ = 0 :=
  N13TwoAdicDisks.negOneDiskY_negOne

theorem y₀_spec :
    N13GoodModelTwo.AffineEquation P.x₀ P.y₀ ∧
      P.y₀ ∈ maximal :=
  N13TwoAdicDisks.zeroDiskY_spec P.x₀ P.x₀_mem

theorem y₁_spec :
    N13GoodModelTwo.AffineEquation P.x₁ P.y₁ ∧
      P.y₁ ∈ maximal :=
  N13TwoAdicDisks.negOneDiskY_spec P.x₁ P.x₁_add_one_mem

@[simp] theorem reduceBase_y₀ :
    N13GeneralizedMumfordReduction.reduceBase P.y₀ = 0 :=
  reduceBase_eq_zero_of_mem P.y₀_spec.2

@[simp] theorem reduceBase_y₁ :
    N13GeneralizedMumfordReduction.reduceBase P.y₁ = 0 :=
  reduceBase_eq_zero_of_mem P.y₁_spec.2

theorem x₁_sub_x₀_isUnit :
    IsUnit (P.x₁ - P.x₀) := by
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_neg_one
  have h :=
    maximal.sub_mem P.x₁_add_one_mem P.x₀_mem
  convert h using 1
  ring

theorem cross_x₁_sub_x₀_isUnit (Q : DiskPair) :
    IsUnit (P.x₁ - Q.x₀) := by
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_neg_one
  have h :=
    maximal.sub_mem P.x₁_add_one_mem Q.x₀_mem
  convert h using 1
  ring

/-- The inverse of the unit separating the two `x`-coordinates. -/
def deltaInv : R₂ :=
  ↑((P.x₁_sub_x₀_isUnit).unit⁻¹)

theorem deltaInv_mul_delta :
    P.deltaInv * (P.x₁ - P.x₀) = 1 := by
  rw [← (P.x₁_sub_x₀_isUnit).unit_spec]
  exact Units.inv_mul _

/-- The integral linear interpolant taking values `a₀,a₁` at the two
selected `x`-coordinates. -/
def interpolate (a₀ a₁ : R₂) : R₂[X] :=
  C a₀ +
    C (P.deltaInv * (a₁ - a₀)) * (X - C P.x₀)

@[simp] theorem interpolate_eval_x₀ (a₀ a₁ : R₂) :
    (P.interpolate a₀ a₁).eval P.x₀ = a₀ := by
  simp [interpolate]

@[simp] theorem interpolate_eval_x₁ (a₀ a₁ : R₂) :
    (P.interpolate a₀ a₁).eval P.x₁ = a₁ := by
  simp only [interpolate, eval_add, eval_C, eval_mul, eval_sub,
    eval_X]
  calc
    a₀ + P.deltaInv * (a₁ - a₀) * (P.x₁ - P.x₀) =
        a₀ + (a₁ - a₀) *
          (P.deltaInv * (P.x₁ - P.x₀)) := by ring
    _ = a₁ := by rw [P.deltaInv_mul_delta]; ring

/-- The monic polynomial cutting out the two selected affine points. -/
def u : R₂[X] :=
  (X - C P.x₀) * (X - C P.x₁)

/-- The graph polynomial through the two selected affine points. -/
def v : R₂[X] :=
  P.interpolate P.y₀ P.y₁

@[simp] theorem basePair_u :
    basePair.u =
      N13FormalAbelLinearization.uBase := by
  simp [u, basePair, N13FormalAbelLinearization.uBase]
  ring

@[simp] theorem basePair_v :
    basePair.v = 0 := by
  change basePair.interpolate basePair.y₀ basePair.y₁ = 0
  rw [basePair_y₀, basePair_y₁]
  simp [interpolate]

theorem u_monic : P.u.Monic := by
  exact (monic_X_sub_C P.x₀).mul (monic_X_sub_C P.x₁)

@[simp] theorem u_eval_x₀ :
    P.u.eval P.x₀ = 0 := by
  simp [u]

@[simp] theorem u_eval_x₁ :
    P.u.eval P.x₁ = 0 := by
  simp [u]

@[simp] theorem v_eval_x₀ :
    P.v.eval P.x₀ = P.y₀ :=
  P.interpolate_eval_x₀ P.y₀ P.y₁

@[simp] theorem v_eval_x₁ :
    P.v.eval P.x₁ = P.y₁ :=
  P.interpolate_eval_x₁ P.y₀ P.y₁

/-- The generalized-hyperelliptic residual after restriction to the graph
`Y=v(X)`. -/
def curveError : R₂[X] :=
  P.v ^ 2 +
      N13GeneralizedMumfordIntegral.hPoly * P.v -
    N13GeneralizedMumfordIntegral.rhsPoly

@[simp] theorem curveError_eval_x₀ :
    P.curveError.eval P.x₀ = 0 := by
  have hcurve := P.y₀_spec.1
  rw [N13GoodModelTwo.affineEquation_iff_residual] at hcurve
  simpa [curveError, N13GoodModelTwo.affineResidual,
    N13GoodModelTwo.h, N13GoodModelTwo.rhs,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly] using hcurve

@[simp] theorem curveError_eval_x₁ :
    P.curveError.eval P.x₁ = 0 := by
  have hcurve := P.y₁_spec.1
  rw [N13GoodModelTwo.affineEquation_iff_residual] at hcurve
  simpa [curveError, N13GoodModelTwo.affineResidual,
    N13GoodModelTwo.h, N13GoodModelTwo.rhs,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly] using hcurve

theorem u_dvd_curveError :
    P.u ∣ P.curveError := by
  have h₀ : X - C P.x₀ ∣ P.curveError := by
    rw [dvd_iff_isRoot, IsRoot]
    exact P.curveError_eval_x₀
  have h₁ : X - C P.x₁ ∣ P.curveError := by
    rw [dvd_iff_isRoot, IsRoot]
    exact P.curveError_eval_x₁
  have hprod :=
    (isCoprime_X_sub_C_of_isUnit_sub
      P.x₁_sub_x₀_isUnit).mul_dvd h₁ h₀
  simpa [u, mul_comm] using hprod

def w : R₂[X] :=
  Classical.choose P.u_dvd_curveError

theorem curve_eq :
    P.v ^ 2 +
        N13GeneralizedMumfordIntegral.hPoly * P.v -
      N13GeneralizedMumfordIntegral.rhsPoly =
        P.u * P.w :=
  Classical.choose_spec P.u_dvd_curveError

/-- The vertical derivative `2v+h` restricted to the graph. -/
def verticalDerivative : R₂[X] :=
  2 * P.v + N13GeneralizedMumfordIntegral.hPoly

@[simp] theorem verticalDerivative_eval_x₀ :
    P.verticalDerivative.eval P.x₀ =
      2 * P.y₀ + N13GoodModelTwo.h P.x₀ := by
  simp [verticalDerivative, N13GeneralizedMumfordIntegral.hPoly,
    N13GoodModelTwo.h]

@[simp] theorem verticalDerivative_eval_x₁ :
    P.verticalDerivative.eval P.x₁ =
      2 * P.y₁ + N13GoodModelTwo.h P.x₁ := by
  simp [verticalDerivative, N13GeneralizedMumfordIntegral.hPoly,
    N13GoodModelTwo.h]

theorem verticalDerivative_eval_x₀_isUnit :
    IsUnit (P.verticalDerivative.eval P.x₀) := by
  rw [P.verticalDerivative_eval_x₀]
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal
    (N13TwoAdicDisks.h_isUnit_of_mem_zeroDisk P.x₀_mem)
  have h := maximal.mul_mem_left (2 : R₂) P.y₀_spec.2
  convert h using 1
  ring

theorem verticalDerivative_eval_x₁_isUnit :
    IsUnit (P.verticalDerivative.eval P.x₁) := by
  rw [P.verticalDerivative_eval_x₁]
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal
    (N13TwoAdicDisks.h_isUnit_of_mem_negOneDisk
      P.x₁_add_one_mem)
  have h := maximal.mul_mem_left (2 : R₂) P.y₁_spec.2
  convert h using 1
  ring

def derivativeInv₀ : R₂ :=
  ↑((P.verticalDerivative_eval_x₀_isUnit).unit⁻¹)

def derivativeInv₁ : R₂ :=
  ↑((P.verticalDerivative_eval_x₁_isUnit).unit⁻¹)

@[simp] theorem derivativeInv₀_mul :
    P.derivativeInv₀ * P.verticalDerivative.eval P.x₀ = 1 := by
  rw [← (P.verticalDerivative_eval_x₀_isUnit).unit_spec]
  exact Units.inv_mul _

@[simp] theorem derivativeInv₁_mul :
    P.derivativeInv₁ * P.verticalDerivative.eval P.x₁ = 1 := by
  rw [← (P.verticalDerivative_eval_x₁_isUnit).unit_spec]
  exact Units.inv_mul _

/-- Interpolate the inverses of the two vertical derivatives. -/
def derivativeInverse : R₂[X] :=
  P.interpolate P.derivativeInv₀ P.derivativeInv₁

@[simp] theorem derivativeInverse_mul_eval_x₀ :
    (P.derivativeInverse * P.verticalDerivative).eval P.x₀ = 1 := by
  rw [eval_mul, derivativeInverse, P.interpolate_eval_x₀,
    P.derivativeInv₀_mul]

@[simp] theorem derivativeInverse_mul_eval_x₁ :
    (P.derivativeInverse * P.verticalDerivative).eval P.x₁ = 1 := by
  rw [eval_mul, derivativeInverse, P.interpolate_eval_x₁,
    P.derivativeInv₁_mul]

theorem u_dvd_derivativeInverse_mul_sub_one :
    P.u ∣ P.derivativeInverse * P.verticalDerivative - 1 := by
  have h₀ :
      X - C P.x₀ ∣
        P.derivativeInverse * P.verticalDerivative - 1 := by
    rw [dvd_iff_isRoot, IsRoot]
    rw [eval_sub, P.derivativeInverse_mul_eval_x₀, eval_one,
      sub_self]
  have h₁ :
      X - C P.x₁ ∣
        P.derivativeInverse * P.verticalDerivative - 1 := by
    rw [dvd_iff_isRoot, IsRoot]
    rw [eval_sub, P.derivativeInverse_mul_eval_x₁, eval_one,
      sub_self]
  have hprod :=
    (isCoprime_X_sub_C_of_isUnit_sub
      P.x₁_sub_x₀_isUnit).mul_dvd h₁ h₀
  simpa [u, mul_comm] using hprod

def bezoutQuotient : R₂[X] :=
  Classical.choose P.u_dvd_derivativeInverse_mul_sub_one

theorem bezoutQuotient_spec :
    P.derivativeInverse * P.verticalDerivative - 1 =
      P.u * P.bezoutQuotient :=
  Classical.choose_spec P.u_dvd_derivativeInverse_mul_sub_one

/-- The two-disk divisor supplies smooth integral generalized Mumford data. -/
def smoothMumford :
    N13GeneralizedMumfordReduction.SmoothMumford₂ where
  u := P.u
  v := P.v
  w := P.w
  u_monic := P.u_monic
  curve_eq := P.curve_eq
  bezout := by
    refine
      ⟨-P.bezoutQuotient, P.derivativeInverse, 0, ?_⟩
    rw [show
      2 * P.v +
          N13GeneralizedMumfordIntegral.hPoly =
        P.verticalDerivative by rfl]
    have h := P.bezoutQuotient_spec
    have hb :
        P.derivativeInverse * P.verticalDerivative =
          P.u * P.bezoutQuotient + 1 :=
      sub_eq_iff_eq_add.mp h
    rw [hb]
    ring

@[simp] theorem smoothMumford_u :
    P.smoothMumford.u = P.u := rfl

@[simp] theorem smoothMumford_v :
    P.smoothMumford.v = P.v := rfl

@[simp] theorem reducePoly_u :
    N13GeneralizedMumfordReduction.reducePoly P.u =
      (X ^ 2 + X :
        N13GoodCoordinateRingTwo.K[X]) := by
  rw [N13GeneralizedMumfordReduction.reducePoly_apply]
  simp only [u, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C,
    P.reduceBase_x₀, P.reduceBase_x₁, C_0, C_1, sub_zero]
  rw [CharTwo.sub_eq_add]
  ring

@[simp] theorem reducePoly_v :
    N13GeneralizedMumfordReduction.reducePoly P.v = 0 := by
  rw [N13GeneralizedMumfordReduction.reducePoly_apply]
  simp [v, interpolate]

/-- The monic divisor polynomial remembers the ordered pair because the two
roots lie in disjoint residue disks. -/
theorem u_injective :
    Function.Injective DiskPair.u := by
  intro P Q hPQ
  have hQ₀ : Q.u.eval P.x₀ = 0 := by
    rw [← hPQ]
    exact P.u_eval_x₀
  have hprod₀ :
      (P.x₀ - Q.x₀) * (P.x₀ - Q.x₁) = 0 := by
    simpa [u] using hQ₀
  have hright : P.x₀ - Q.x₁ ≠ 0 := by
    intro hzero
    apply (Q.cross_x₁_sub_x₀_isUnit P).ne_zero
    calc
      Q.x₁ - P.x₀ = -(P.x₀ - Q.x₁) := by ring
      _ = 0 := by rw [hzero]; simp
  have hx₀ : P.x₀ = Q.x₀ :=
    sub_eq_zero.mp
      ((mul_eq_zero.mp hprod₀).resolve_right hright)
  have hQ₁ : Q.u.eval P.x₁ = 0 := by
    rw [← hPQ]
    exact P.u_eval_x₁
  have hprod₁ :
      (P.x₁ - Q.x₀) * (P.x₁ - Q.x₁) = 0 := by
    simpa [u] using hQ₁
  have hleft : P.x₁ - Q.x₀ ≠ 0 :=
    (P.cross_x₁_sub_x₀_isUnit Q).ne_zero
  have hx₁ : P.x₁ = Q.x₁ :=
    sub_eq_zero.mp
      ((mul_eq_zero.mp hprod₁).resolve_left hleft)
  cases P
  cases Q
  simp_all

/-- Coordinates centered at the distinguished pair. -/
def coord : DiskPair → Fin 2 → R₂ :=
  fun Q => ![Q.x₀, Q.x₁ + 1]

@[simp] theorem coord_zero (Q : DiskPair) :
    coord Q 0 = Q.x₀ := rfl

@[simp] theorem coord_one (Q : DiskPair) :
    coord Q 1 = Q.x₁ + 1 := rfl

@[simp] theorem coord_basePair :
    coord basePair = 0 := by
  funext i
  fin_cases i <;> simp [coord, basePair]

theorem coord_mem_maximal
    (Q : DiskPair) (i : Fin 2) :
    coord Q i ∈ maximal := by
  fin_cases i
  · exact Q.x₀_mem
  · exact Q.x₁_add_one_mem

theorem maximal_eq_powTwoIdeal_one :
    maximal =
      N13TwoAdicKernelChart.powTwoIdeal 1 := by
  change IsLocalRing.maximalIdeal R₂ = _
  rw [PadicInt.maximalIdeal_eq_span_p,
    N13TwoAdicKernelChart.powTwoIdeal, pow_one]
  norm_num

theorem coord_mem_two
    (Q : DiskPair) (i : Fin 2) :
    coord Q i ∈
      N13TwoAdicKernelChart.powTwoIdeal 1 := by
  rw [← maximal_eq_powTwoIdeal_one]
  exact coord_mem_maximal Q i

theorem coord_injective :
    Function.Injective coord := by
  intro P Q hPQ
  have hx₀ := congrFun hPQ (0 : Fin 2)
  have hx₁ := congrFun hPQ (1 : Fin 2)
  cases P
  cases Q
  simp_all [coord]

end DiskPair

end

end MazurProof.N13TwoAdicAbelChartData

end
end

-- module FLT.Assumptions.MazurProof.N13InfinityAPI
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InfinityAPI =====
section

/-!
# Evaluation API for the positive infinity embedding of the N13 sextic
-/

open Polynomial
open scoped LaurentSeries nonZeroDivisors

namespace MazurProof.N13Infinity

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

@[simp] theorem functionFieldToLaurent_algebraMap
    (z : N13Mumford.CoordinateRing K) :
    functionFieldToLaurent K
        (algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) z) =
      coordinateToLaurent K z := by
  exact IsFractionRing.lift_algebraMap
    (coordinateToLaurent_injective K) z

theorem coordinateToAlgebraic_xClass (p : K[X]) :
    coordinateToAlgebraic K
      (SexticMumford.xClass (N13Mumford.model K) p) =
      AdjoinRoot.of (curvePolyRat K)
        (algebraMap K[X] (RatFunc K) p) := by
  simpa only [SexticMumford.xClass, SexticMumford.mk, Polynomial.map_C,
    AdjoinRoot.mk_C] using coordinateToAlgebraic_mk K (C p)

@[simp] theorem coordinateToLaurent_xClass (p : K[X]) :
    coordinateToLaurent K
      (SexticMumford.xClass (N13Mumford.model K) p) =
      p.eval₂ (algebraMap K (LaurentSeries K)) ((parameter K)⁻¹) := by
  change algebraicToLaurent K
      (coordinateToAlgebraic K
        (SexticMumford.xClass (N13Mumford.model K) p)) = _
  rw [coordinateToAlgebraic_xClass]
  unfold algebraicToLaurent
  rw [AdjoinRoot.lift_of (curvePolyRat_eval_ySeries K)]
  exact DFunLike.congr_fun (ratToLaurent_comp_algebraMap K) p

@[simp] theorem coordinateToLaurent_scalar (c : K) :
    coordinateToLaurent K (algebraMap K (N13Mumford.CoordinateRing K) c) =
      algebraMap K (LaurentSeries K) c := by
  change coordinateToLaurent K
    (SexticMumford.xClass (N13Mumford.model K) (C c)) = _
  rw [coordinateToLaurent_xClass]
  simp

def coordinateConstUnit (c : Kˣ) : (N13Mumford.CoordinateRing K)ˣ :=
  Units.map (algebraMap K (N13Mumford.CoordinateRing K)) c

def functionConstUnit (c : Kˣ) : (N13Mumford.FunctionField K)ˣ :=
  Units.map
    (algebraMap (N13Mumford.CoordinateRing K)
      (N13Mumford.FunctionField K))
    (coordinateConstUnit K c)

@[simp] theorem functionFieldToLaurent_functionConstUnit (c : Kˣ) :
    functionFieldToLaurent K (functionConstUnit K c :
      N13Mumford.FunctionField K) =
      algebraMap K (LaurentSeries K) (c : K) := by
  change functionFieldToLaurent K
      (algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (algebraMap K (N13Mumford.CoordinateRing K) (c : K))) = _
  rw [functionFieldToLaurent_algebraMap, coordinateToLaurent_scalar]

@[simp] theorem ordPlus_functionConstUnit (c : Kˣ) :
    (positiveInfinityOrder K).ordPlus (functionConstUnit K c) = 1 := by
  change Multiplicative.ofAdd
      ((functionFieldToLaurent K
        (functionConstUnit K c : N13Mumford.FunctionField K)).order) = 1
  rw [functionFieldToLaurent_functionConstUnit]
  simp [HahnSeries.algebraMap_apply', HahnSeries.order_single c.ne_zero]

@[simp] theorem principalIdeal_functionConstUnit (c : Kˣ) :
    toPrincipalIdeal (N13Mumford.CoordinateRing K)
      (N13Mumford.FunctionField K) (functionConstUnit K c) = 1 := by
  apply Units.ext
  rw [coe_toPrincipalIdeal]
  change FractionalIdeal.spanSingleton
      (N13Mumford.CoordinateRing K)⁰
      (algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (coordinateConstUnit K c : N13Mumford.CoordinateRing K)) = 1
  rw [← FractionalIdeal.spanSingleton_one]
  apply FractionalIdeal.spanSingleton_eq_spanSingleton.mpr
  refine ⟨(coordinateConstUnit K c)⁻¹, ?_⟩
  rw [Units.smul_def, Algebra.smul_def, ← map_mul]
  change algebraMap (N13Mumford.CoordinateRing K)
      (N13Mumford.FunctionField K)
      (((coordinateConstUnit K c)⁻¹ :
          (N13Mumford.CoordinateRing K)ˣ) * coordinateConstUnit K c :
        (N13Mumford.CoordinateRing K)ˣ) = 1
  simp

end

end MazurProof.N13Infinity

end
end

-- module FLT.Assumptions.MazurProof.N13InfinityMinus
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InfinityMinus =====
section

/-!
# The negative infinity of the N13 genus-two curve

The second branch at infinity is obtained by sending `Y` to the negative of
the positive Laurent expansion.  It gives the opposite orientation datum for
the two-infinity sextic model.
-/

open Polynomial
open scoped LaurentSeries PowerSeries

namespace MazurProof.N13InfinityMinus

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

def ySeriesMinus : LaurentSeries K := -(N13Infinity.ySeries K)

@[simp] theorem ySeriesMinus_eq_neg :
    ySeriesMinus K = -(N13Infinity.ySeries K) := rfl

theorem ySeriesMinus_sq :
    ySeriesMinus K ^ 2 =
      (N13Mumford.f K).eval₂ (algebraMap K (LaurentSeries K))
        ((N13Infinity.parameter K)⁻¹) := by
  rw [ySeriesMinus, neg_sq, N13Infinity.ySeries_sq]

theorem curvePolyRat_eval_ySeriesMinus :
    (N13Infinity.curvePolyRat K).eval₂ (N13Infinity.ratToLaurent K)
      (ySeriesMinus K) = 0 := by
  rw [N13Infinity.curvePolyRat, Polynomial.eval₂_map,
    N13Infinity.ratToLaurent_comp_algebraMap]
  change (X ^ 2 - C (N13Mumford.f K)).eval₂
      (Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K))
        ((N13Infinity.parameter K)⁻¹)) (ySeriesMinus K) = 0
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  rw [ySeriesMinus_sq]
  exact sub_self _

def algebraicToLaurentMinus :
    N13Infinity.AlgebraicFunctionField K →+* LaurentSeries K :=
  AdjoinRoot.lift (N13Infinity.ratToLaurent K) (ySeriesMinus K)
    (curvePolyRat_eval_ySeriesMinus K)

@[simp] theorem algebraicToLaurentMinus_root :
    algebraicToLaurentMinus K
      (AdjoinRoot.root (N13Infinity.curvePolyRat K)) = ySeriesMinus K := by
  exact AdjoinRoot.lift_root (curvePolyRat_eval_ySeriesMinus K)

theorem algebraicToLaurentMinus_injective :
    Function.Injective (algebraicToLaurentMinus K) :=
  (algebraicToLaurentMinus K).injective

def coordinateToLaurentMinus :
    N13Mumford.CoordinateRing K →+* LaurentSeries K :=
  (algebraicToLaurentMinus K).comp (N13Infinity.coordinateToAlgebraic K)

theorem coordinateToLaurentMinus_injective :
    Function.Injective (coordinateToLaurentMinus K) :=
  (algebraicToLaurentMinus_injective K).comp
    (N13Infinity.coordinateToAlgebraic_injective K)

@[simp] theorem coordinateToLaurentMinus_yClass :
    coordinateToLaurentMinus K
      (SexticMumford.yClass (N13Mumford.model K)) = ySeriesMinus K := by
  change algebraicToLaurentMinus K
    (N13Infinity.coordinateToAlgebraic K
      (AdjoinRoot.mk (SexticMumford.curvePoly (N13Mumford.model K)) X)) = _
  rw [N13Infinity.coordinateToAlgebraic_mk]
  simp only [Polynomial.map_X]
  exact algebraicToLaurentMinus_root K

def functionFieldToLaurentMinus :
    N13Mumford.FunctionField K →+* LaurentSeries K :=
  IsFractionRing.lift (coordinateToLaurentMinus_injective K)

theorem functionFieldToLaurentMinus_injective :
    Function.Injective (functionFieldToLaurentMinus K) :=
  (functionFieldToLaurentMinus K).injective

def infinityOrderHomMinus :
    (N13Mumford.FunctionField K)ˣ →* Multiplicative ℤ :=
  (N13Infinity.laurentOrder K).comp
    (Units.map (functionFieldToLaurentMinus K))

def negativeInfinityOrder :
    SexticMumford.InfinityOrder (N13Mumford.model K) where
  ordPlus := infinityOrderHomMinus K

end

end MazurProof.N13InfinityMinus

end
end

-- module FLT.Assumptions.MazurProof.N13InfinityMinusAPI
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InfinityMinusAPI =====
section

/-!
# Evaluation API for the negative infinity embedding of the N13 sextic
-/

open Polynomial
open scoped LaurentSeries nonZeroDivisors

namespace MazurProof.N13InfinityMinus

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

@[simp] theorem functionFieldToLaurentMinus_algebraMap
    (z : N13Mumford.CoordinateRing K) :
    functionFieldToLaurentMinus K
        (algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) z) =
      coordinateToLaurentMinus K z := by
  exact IsFractionRing.lift_algebraMap
    (coordinateToLaurentMinus_injective K) z

@[simp] theorem coordinateToLaurentMinus_xClass (p : K[X]) :
    coordinateToLaurentMinus K
      (SexticMumford.xClass (N13Mumford.model K) p) =
      p.eval₂ (algebraMap K (LaurentSeries K)) ((N13Infinity.parameter K)⁻¹) := by
  change algebraicToLaurentMinus K
      (N13Infinity.coordinateToAlgebraic K
        (SexticMumford.xClass (N13Mumford.model K) p)) = _
  rw [N13Infinity.coordinateToAlgebraic_xClass]
  unfold algebraicToLaurentMinus
  rw [AdjoinRoot.lift_of (curvePolyRat_eval_ySeriesMinus K)]
  exact DFunLike.congr_fun (N13Infinity.ratToLaurent_comp_algebraMap K) p

@[simp] theorem coordinateToLaurentMinus_scalar (c : K) :
    coordinateToLaurentMinus K
      (algebraMap K (N13Mumford.CoordinateRing K) c) =
      algebraMap K (LaurentSeries K) c := by
  change coordinateToLaurentMinus K
    (SexticMumford.xClass (N13Mumford.model K) (C c)) = _
  rw [coordinateToLaurentMinus_xClass]
  simp

end

end MazurProof.N13InfinityMinus

namespace MazurProof.N13Infinity

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

theorem wSeries_coeff_zero :
    (wSeries K).coeff (0 : ℤ) = 1 := by
  change (HahnSeries.ofPowerSeries ℤ K (sqrtReverseF K)).coeff (0 : ℕ) = 1
  rw [HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, sqrtReverseF_constantCoeff]

theorem wSeries_ne_zero : wSeries K ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun z : LaurentSeries K => z.coeff (0 : ℤ)) h
  simp [wSeries_coeff_zero] at hcoeff

/-- The square-root factor in the Laurent expansion is a unit at infinity. -/
theorem wSeries_order : (wSeries K).order = 0 := by
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero (by simp [wSeries_coeff_zero])
  · rw [HahnSeries.le_order_iff_forall (wSeries_ne_zero K)]
    intro j hj
    change (HahnSeries.ofPowerSeries ℤ K (sqrtReverseF K)).coeff j = 0
    rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image]
    rintro n ⟨_, hn⟩
    have hnon : (0 : ℤ) ≤ (Nat.castOrderEmbedding n : ℤ) := by
      change (0 : ℤ) ≤ (n : ℤ)
      omega
    rw [hn] at hnon
    omega

/-- Both branches have a pole of order three at their respective infinities. -/
theorem ySeries_order : (ySeries K).order = -3 := by
  rw [ySeries]
  have hp : (parameter K)⁻¹ ^ 3 = HahnSeries.single (-3 : ℤ) 1 := by
    simp [parameter, HahnSeries.inv_single, HahnSeries.single_pow]
  rw [hp, HahnSeries.order_mul (HahnSeries.single_ne_zero one_ne_zero)
    (wSeries_ne_zero K), HahnSeries.order_single one_ne_zero, wSeries_order]
  norm_num

end

end MazurProof.N13Infinity

namespace MazurProof.N13InfinityMinus

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

end

end MazurProof.N13InfinityMinus

end
end

-- module FLT.Assumptions.MazurProof.N13LaurentPolynomialOrder
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13LaurentPolynomialOrder =====
section

/-!
# The order at infinity of a polynomial

The substitution `X = s⁻¹` reverses a polynomial.  Its leading
coefficient becomes the constant coefficient of the reversed polynomial,
so the latter has order zero; the factor `s⁻ⁿ` accounts for the whole
order.  This is the formal local calculation used at the cusps of `X₁(13)`.
-/

open Polynomial
open scoped LaurentSeries PowerSeries

namespace MazurProof
namespace N13LaurentPolynomialOrder

noncomputable section

universe u

variable (K : Type u) [Field K]

/-- The Laurent parameter at infinity. -/
def parameter : LaurentSeries K := HahnSeries.single 1 1

/-- Evaluation of a polynomial after the substitution `X = s⁻¹`. -/
def evalAtInfinity (p : K[X]) : LaurentSeries K :=
  p.eval₂ (algebraMap K (LaurentSeries K)) (parameter K)⁻¹

@[simp] lemma parameter_ne_zero : parameter K ≠ 0 := by
  simp [parameter]

@[simp] lemma parameter_inv : (parameter K)⁻¹ = HahnSeries.single (-1 : ℤ) 1 := by
  simp [parameter, HahnSeries.inv_single]

@[simp] lemma order_parameter : (parameter K).order = 1 := by
  simp [parameter, HahnSeries.order_single]

@[simp] lemma order_parameter_inv_pow (n : ℕ) :
    ((parameter K)⁻¹ ^ n).order = -(n : ℤ) := by
  rw [parameter_inv, HahnSeries.order_pow]
  simp [HahnSeries.order_single]

lemma eval_parameter_eq_ofPowerSeries (p : K[X]) :
    p.eval₂ (algebraMap K (LaurentSeries K)) (parameter K) =
      HahnSeries.ofPowerSeries ℤ K p := by
  have h : Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K)) (parameter K) =
      algebraMap K[X] (LaurentSeries K) := by
    apply Polynomial.ringHom_ext
    · intro a
      change Polynomial.eval₂ (algebraMap K (LaurentSeries K)) (parameter K) (C a) = _
      rw [Polynomial.eval₂_C, Polynomial.algebraMap_hahnSeries_apply]
      simp [HahnSeries.algebraMap_apply']
    · change Polynomial.eval₂ (algebraMap K (LaurentSeries K)) (parameter K) X = _
      rw [Polynomial.eval₂_X, Polynomial.algebraMap_hahnSeries_apply]
      simp [parameter, HahnSeries.ofPowerSeries_X]
  change (Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K)) (parameter K)) p = _
  rw [h, Polynomial.algebraMap_hahnSeries_apply]

lemma order_ofPowerSeries_of_coeff_zero_ne (p : K[X]) (hp : p.coeff 0 ≠ 0) :
    (HahnSeries.ofPowerSeries ℤ K p).order = 0 := by
  have hcoeff : (HahnSeries.ofPowerSeries ℤ K p).coeff 0 ≠ 0 := by
    have hcoeff_eq : (HahnSeries.ofPowerSeries ℤ K p).coeff 0 = p.coeff 0 := by
      calc
        (HahnSeries.ofPowerSeries ℤ K p).coeff 0 = PowerSeries.coeff 0 (p : K⟦X⟧) :=
          HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (p : K⟦X⟧) 0
        _ = p.coeff 0 := Polynomial.coeff_coe p 0
    rwa [hcoeff_eq]
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero hcoeff
  · rw [← HahnSeries.zero_le_orderTop_iff]
    apply HahnSeries.le_orderTop_iff_forall.mpr
    intro j hj
    rw [HahnSeries.ofPowerSeries_apply]
    apply HahnSeries.embDomain_notin_image_support
    rintro ⟨n, -, rfl⟩
    have hnonneg : (0 : ℤ) ≤ (Nat.castOrderEmbedding (α := ℤ) n : ℤ) := by
      simp
    exact (not_lt_of_ge (WithTop.coe_le_coe.mpr hnonneg)) hj

lemma order_eval_parameter_reverse (p : K[X]) (hp : p ≠ 0) :
    (p.reverse.eval₂ (algebraMap K (LaurentSeries K)) (parameter K)).order = 0 := by
  rw [eval_parameter_eq_ofPowerSeries]
  apply order_ofPowerSeries_of_coeff_zero_ne
  simpa using p.leadingCoeff_ne_zero.mpr hp

lemma evalAtInfinity_eq_reverse_mul (p : K[X]) :
    evalAtInfinity K p =
      p.reverse.eval₂ (algebraMap K (LaurentSeries K)) (parameter K) *
        (parameter K)⁻¹ ^ p.natDegree := by
  letI : Invertible ((parameter K)⁻¹) :=
    invertibleOfNonzero (inv_ne_zero (parameter_ne_zero K))
  symm
  unfold evalAtInfinity parameter
  simpa [Polynomial.reverse, HahnSeries.inv_single, invOf_eq_inv] using
    (Polynomial.eval₂_reflect_mul_pow (algebraMap K (LaurentSeries K))
      ((parameter K)⁻¹) p.natDegree p le_rfl)

theorem order_evalAtInfinity (p : K[X]) (hp : p ≠ 0) :
    (evalAtInfinity K p).order = -(p.natDegree : ℤ) := by
  rw [evalAtInfinity_eq_reverse_mul, HahnSeries.order_mul]
  · rw [order_eval_parameter_reverse K p hp, order_parameter_inv_pow]
    simp
  · rw [eval_parameter_eq_ofPowerSeries]
    intro hzero
    apply hp
    apply Polynomial.reverse_eq_zero.mp
    apply Polynomial.coe_injective K
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa using hzero
  · exact pow_ne_zero _ (inv_ne_zero (parameter_ne_zero K))

end
end N13LaurentPolynomialOrder
end MazurProof

end
end

-- module FLT.Assumptions.MazurProof.N13BranchNorm
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13BranchNorm =====
section

/-!
# The two infinity branches and the quadratic norm on `X₁(13)`

For an affine function `p(X) + q(X)Y`, the two Laurent embeddings differ
only in the sign of `Y`.  Their product is therefore the polynomial norm
`p² - q²f`.  This packages the structural reason that the two infinity
orders must be used together: cancellation at one branch is detected by
the other branch.
-/

open Polynomial
open scoped LaurentSeries

namespace MazurProof.N13BranchNorm

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

def evalPoly : K[X] →+* LaurentSeries K :=
  Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K))
    ((N13Infinity.parameter K)⁻¹)

omit [CharZero K] in
@[simp] theorem evalPoly_apply (p : K[X]) :
    evalPoly K p =
      p.eval₂ (algebraMap K (LaurentSeries K))
        ((N13Infinity.parameter K)⁻¹) := rfl

omit [CharZero K] in
theorem evalPoly_eq_evalAtInfinity (p : K[X]) :
    evalPoly K p =
      N13LaurentPolynomialOrder.evalAtInfinity K p := by
  rfl

omit [CharZero K] in
theorem evalPoly_ne_zero {p : K[X]} (hp : p ≠ 0) :
    evalPoly K p ≠ 0 := by
  rw [evalPoly_eq_evalAtInfinity,
    N13LaurentPolynomialOrder.evalAtInfinity_eq_reverse_mul]
  apply mul_ne_zero
  · rw [N13LaurentPolynomialOrder.eval_parameter_eq_ofPowerSeries]
    intro hzero
    apply hp
    apply Polynomial.reverse_eq_zero.mp
    apply Polynomial.coe_injective K
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa using hzero
  · exact pow_ne_zero _
      (inv_ne_zero (N13LaurentPolynomialOrder.parameter_ne_zero K))

omit [CharZero K] in
theorem evalPoly_order (p : K[X]) (hp : p ≠ 0) :
    (evalPoly K p).order = -(p.natDegree : ℤ) := by
  rw [evalPoly_eq_evalAtInfinity]
  exact N13LaurentPolynomialOrder.order_evalAtInfinity K p hp

@[simp] theorem coordinateToLaurent_yClass :
    N13Infinity.coordinateToLaurent K
      (SexticMumford.yClass (N13Mumford.model K)) =
      N13Infinity.ySeries K := by
  change N13Infinity.algebraicToLaurent K
    (N13Infinity.coordinateToAlgebraic K
      (AdjoinRoot.mk
        (SexticMumford.curvePoly (N13Mumford.model K)) X)) = _
  rw [N13Infinity.coordinateToAlgebraic_mk]
  simp only [Polynomial.map_X]
  exact AdjoinRoot.lift_root
    (N13Infinity.curvePolyRat_eval_ySeries K)

def linearFunction (p q : K[X]) : N13Mumford.CoordinateRing K :=
  SexticMumford.xClass (N13Mumford.model K) p +
    SexticMumford.xClass (N13Mumford.model K) q *
      SexticMumford.yClass (N13Mumford.model K)

@[simp] theorem coordinateToLaurent_linearFunction (p q : K[X]) :
    N13Infinity.coordinateToLaurent K (linearFunction K p q) =
      evalPoly K p + evalPoly K q * N13Infinity.ySeries K := by
  simp [linearFunction, coordinateToLaurent_yClass]

@[simp] theorem coordinateToLaurentMinus_linearFunction (p q : K[X]) :
    N13InfinityMinus.coordinateToLaurentMinus K (linearFunction K p q) =
      evalPoly K p - evalPoly K q * N13Infinity.ySeries K := by
  simp [linearFunction, N13InfinityMinus.ySeriesMinus_eq_neg]
  ring

def normNumerator (p q : K[X]) : K[X] :=
  p ^ 2 - q ^ 2 * N13Mumford.f K

theorem branch_product (p q : K[X]) :
    N13Infinity.coordinateToLaurent K (linearFunction K p q) *
        N13InfinityMinus.coordinateToLaurentMinus K
          (linearFunction K p q) =
      evalPoly K (normNumerator K p q) := by
  rw [coordinateToLaurent_linearFunction,
    coordinateToLaurentMinus_linearFunction]
  calc
    (evalPoly K p + evalPoly K q * N13Infinity.ySeries K) *
          (evalPoly K p - evalPoly K q * N13Infinity.ySeries K) =
        evalPoly K p ^ 2 -
          evalPoly K q ^ 2 * N13Infinity.ySeries K ^ 2 := by ring
    _ = evalPoly K p ^ 2 -
          evalPoly K q ^ 2 * evalPoly K (N13Mumford.f K) := by
            have hy :
                N13Infinity.ySeries K ^ 2 =
                  evalPoly K (N13Mumford.f K) := by
              simpa only [evalPoly_apply] using
                N13Infinity.ySeries_sq K
            rw [hy]
    _ = evalPoly K (normNumerator K p q) := by
      simp only [normNumerator, map_sub, map_mul, map_pow]

theorem branch_orders_add (p q : K[X])
    (hnorm : normNumerator K p q ≠ 0) :
    (N13Infinity.coordinateToLaurent K (linearFunction K p q)).order +
        (N13InfinityMinus.coordinateToLaurentMinus K
          (linearFunction K p q)).order =
      -((normNumerator K p q).natDegree : ℤ) := by
  have hproduct :
      N13Infinity.coordinateToLaurent K (linearFunction K p q) *
          N13InfinityMinus.coordinateToLaurentMinus K
            (linearFunction K p q) ≠ 0 := by
    rw [branch_product]
    exact evalPoly_ne_zero K hnorm
  have hplus :
      N13Infinity.coordinateToLaurent K (linearFunction K p q) ≠ 0 :=
    left_ne_zero_of_mul hproduct
  have hminus :
      N13InfinityMinus.coordinateToLaurentMinus K
          (linearFunction K p q) ≠ 0 :=
    right_ne_zero_of_mul hproduct
  calc
    (N13Infinity.coordinateToLaurent K (linearFunction K p q)).order +
          (N13InfinityMinus.coordinateToLaurentMinus K
            (linearFunction K p q)).order =
        (N13Infinity.coordinateToLaurent K (linearFunction K p q) *
          N13InfinityMinus.coordinateToLaurentMinus K
            (linearFunction K p q)).order :=
      (HahnSeries.order_mul hplus hminus).symm
    _ = (evalPoly K (normNumerator K p q)).order := by
      rw [branch_product]
    _ = -((normNumerator K p q).natDegree : ℤ) :=
      evalPoly_order K _ hnorm

end

end MazurProof.N13BranchNorm

end
end

-- module FLT.Assumptions.MazurProof.N13BranchLeading
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13BranchLeading =====
section

/-!
# Leading pole degree across the two infinity branches

For `p(X) + q(X)Y`, cancellation can raise the order at one infinity, but
it cannot raise the order at both.  The minimum of the two branch orders is
the negative of

`max (deg p) (deg q + 3)`.

The proof is valuation-theoretic.  For arbitrary Laurent series `a,b`, the
pair `a+b, a-b` remembers the smaller of the orders of `a,b`, because `2` is
invertible.  This avoids any coefficient enumeration.
-/

open Polynomial
open scoped LaurentSeries

namespace MazurProof.N13BranchLeading

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

theorem min_orderTop_add_sub (a b : LaurentSeries K) :
    min (a + b).orderTop (a - b).orderTop =
      min a.orderTop b.orderTop := by
  apply le_antisymm
  · apply le_min
    · calc
        min (a + b).orderTop (a - b).orderTop ≤
            ((a + b) + (a - b)).orderTop :=
          HahnSeries.min_orderTop_le_orderTop_add
        _ = (2 * a).orderTop := by ring_nf
        _ = a.orderTop := by
          have htwo : (2 : LaurentSeries K) =
              algebraMap K (LaurentSeries K) (2 : K) :=
            (map_ofNat (algebraMap K (LaurentSeries K)) 2).symm
          rw [htwo, HahnSeries.orderTop_mul]
          simp [HahnSeries.algebraMap_apply',
            HahnSeries.orderTop_single (show (2 : K) ≠ 0 by norm_num)]
    · calc
        min (a + b).orderTop (a - b).orderTop ≤
            ((a + b) - (a - b)).orderTop :=
          HahnSeries.min_orderTop_le_orderTop_sub
        _ = (2 * b).orderTop := by ring_nf
        _ = b.orderTop := by
          have htwo : (2 : LaurentSeries K) =
              algebraMap K (LaurentSeries K) (2 : K) :=
            (map_ofNat (algebraMap K (LaurentSeries K)) 2).symm
          rw [htwo, HahnSeries.orderTop_mul]
          simp [HahnSeries.algebraMap_apply',
            HahnSeries.orderTop_single (show (2 : K) ≠ 0 by norm_num)]
  · apply le_min
    · exact HahnSeries.min_orderTop_le_orderTop_add
    · exact HahnSeries.min_orderTop_le_orderTop_sub

theorem min_order_add_sub_of_ne
    (a b : LaurentSeries K)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hplus : a + b ≠ 0) (hminus : a - b ≠ 0) :
    min (a + b).order (a - b).order = min a.order b.order := by
  have htop := min_orderTop_add_sub K a b
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero ha,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hb,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hplus,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hminus] at htop
  exact WithTop.coe_injective (by
    simpa only [WithTop.coe_min] using htop)

def poleDegree (p q : K[X]) : ℕ :=
  by
    classical
    exact max p.natDegree (if q = 0 then 0 else q.natDegree + 3)

theorem ySeries_ne_zero : N13Infinity.ySeries K ≠ 0 := by
  intro hzero
  have horder := N13Infinity.ySeries_order K
  rw [hzero, HahnSeries.order_zero] at horder
  norm_num at horder

theorem evalPoly_mul_ySeries_order (q : K[X]) (hq : q ≠ 0) :
    (N13BranchNorm.evalPoly K q * N13Infinity.ySeries K).order =
      -((q.natDegree + 3 : ℕ) : ℤ) := by
  rw [HahnSeries.order_mul
    (N13BranchNorm.evalPoly_ne_zero K hq)
    (ySeries_ne_zero K),
    N13BranchNorm.evalPoly_order K q hq,
    N13Infinity.ySeries_order]
  omega

theorem branch_min_order (p q : K[X])
    (hz : N13BranchNorm.linearFunction K p q ≠ 0) :
    min
        (N13Infinity.coordinateToLaurent K
          (N13BranchNorm.linearFunction K p q)).order
        (N13InfinityMinus.coordinateToLaurentMinus K
          (N13BranchNorm.linearFunction K p q)).order =
      -(poleDegree K p q : ℤ) := by
  have hplus :
      N13Infinity.coordinateToLaurent K
          (N13BranchNorm.linearFunction K p q) ≠ 0 := by
    intro hzero
    apply hz
    apply N13Infinity.coordinateToLaurent_injective K
    simpa using hzero
  have hminus :
      N13InfinityMinus.coordinateToLaurentMinus K
          (N13BranchNorm.linearFunction K p q) ≠ 0 := by
    intro hzero
    apply hz
    apply N13InfinityMinus.coordinateToLaurentMinus_injective K
    simpa using hzero
  have hplus' :
      N13BranchNorm.evalPoly K p +
          N13BranchNorm.evalPoly K q * N13Infinity.ySeries K ≠ 0 := by
    simpa only [N13BranchNorm.coordinateToLaurent_linearFunction] using
      hplus
  have hminus' :
      N13BranchNorm.evalPoly K p -
          N13BranchNorm.evalPoly K q * N13Infinity.ySeries K ≠ 0 := by
    simpa only [N13BranchNorm.coordinateToLaurentMinus_linearFunction] using
      hminus
  rw [N13BranchNorm.coordinateToLaurent_linearFunction,
    N13BranchNorm.coordinateToLaurentMinus_linearFunction]
  by_cases hp : p = 0
  · have hq : q ≠ 0 := by
      intro hq
      apply hz
      simp [N13BranchNorm.linearFunction, hp, hq]
    simp only [hp, map_zero, zero_add, zero_sub, HahnSeries.order_neg,
      min_self]
    rw [evalPoly_mul_ySeries_order K q hq]
    simp [poleDegree, hq]
  · by_cases hq : q = 0
    · simp only [hq, map_zero, zero_mul, add_zero, sub_zero, min_self]
      rw [N13BranchNorm.evalPoly_order K p hp]
      simp [poleDegree]
    · have ha := N13BranchNorm.evalPoly_ne_zero K hp
      have hb : N13BranchNorm.evalPoly K q *
          N13Infinity.ySeries K ≠ 0 :=
        mul_ne_zero (N13BranchNorm.evalPoly_ne_zero K hq)
          (ySeries_ne_zero K)
      rw [min_order_add_sub_of_ne K _ _ ha hb hplus' hminus',
        N13BranchNorm.evalPoly_order K p hp,
        evalPoly_mul_ySeries_order K q hq]
      simp only [poleDegree, hq, if_false]
      omega

end

end MazurProof.N13BranchLeading

end
end

-- module FLT.Assumptions.MazurProof.N13FactorRigidity
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FactorRigidity =====
section

/-!
# Small-factor rigidity on the `X₁(13)` sextic

Suppose two affine functions multiply to a polynomial of degree at most two
and neither has more than a simple pole at the positive infinity.  Then both
functions lie in the polynomial subring and have degree at most one.

The proof does not compare coefficients.  It uses the quadratic norm and both
infinity branches.  A nonzero `Y`-part forces pole degree at least three; the
two norm-degree inequalities then contradict the degree of the product.
-/

open Polynomial
open scoped LaurentSeries

namespace MazurProof.N13FactorRigidity

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

theorem minus_order_le_neg_three_of_coeffY_ne_zero
    (p q : K[X])
    (hz : N13BranchNorm.linearFunction K p q ≠ 0)
    (hq : q ≠ 0)
    (hplus : (-2 : ℤ) ≤
      (N13Infinity.coordinateToLaurent K
        (N13BranchNorm.linearFunction K p q)).order) :
    (N13InfinityMinus.coordinateToLaurentMinus K
      (N13BranchNorm.linearFunction K p q)).order ≤ -3 := by
  have hmin :=
    N13BranchLeading.branch_min_order K p q hz
  have hpole :
      3 ≤ N13BranchLeading.poleDegree K p q := by
    simp only [N13BranchLeading.poleDegree, hq, if_false]
    omega
  omega

/-- If two affine functions with at most double poles at the positive
infinity multiply to a polynomial of degree at most four, neither function
has a `Y`-part.  If both had a `Y`-part, both negative-branch pole orders
would be at most `-3`, whereas their product has pole order at least `-4`.
Once one `Y`-part vanishes, the rank-two coefficient decomposition forces
the other to vanish as well. -/
theorem factor_pair_coeffY_eq_zero
    (z w : N13Mumford.CoordinateRing K) (P : K[X])
    (hP : P ≠ 0) (hdeg : P.natDegree ≤ 4)
    (hprod :
      z * w = SexticMumford.xClass (N13Mumford.model K) P)
    (hzplus : (-2 : ℤ) ≤
      (N13Infinity.coordinateToLaurent K z).order)
    (hwplus : (-2 : ℤ) ≤
      (N13Infinity.coordinateToLaurent K w).order) :
    SexticMumford.coeffY (N13Mumford.model K) z = 0 ∧
      SexticMumford.coeffY (N13Mumford.model K) w = 0 := by
  let M := N13Mumford.model K
  let pz := SexticMumford.coeff0 M z
  let qz := SexticMumford.coeffY M z
  let pw := SexticMumford.coeff0 M w
  let qw := SexticMumford.coeffY M w
  have hzlin : N13BranchNorm.linearFunction K pz qz = z :=
    SexticMumford.recompose M z
  have hwlin : N13BranchNorm.linearFunction K pw qw = w :=
    SexticMumford.recompose M w
  have hxP :
      SexticMumford.xClass M P ≠ 0 :=
    SexticMumford.xClass_ne_zero M hP
  have hzw : z * w ≠ 0 := by
    rw [hprod]
    exact hxP
  have hz : z ≠ 0 := left_ne_zero_of_mul hzw
  have hw : w ≠ 0 := right_ne_zero_of_mul hzw
  have hzMinus :
      N13InfinityMinus.coordinateToLaurentMinus K z ≠ 0 :=
    by simpa using
      (N13InfinityMinus.coordinateToLaurentMinus_injective K).ne hz
  have hwMinus :
      N13InfinityMinus.coordinateToLaurentMinus K w ≠ 0 :=
    by simpa using
      (N13InfinityMinus.coordinateToLaurentMinus_injective K).ne hw
  have hminusSum :
      (N13InfinityMinus.coordinateToLaurentMinus K z).order +
          (N13InfinityMinus.coordinateToLaurentMinus K w).order =
        -(P.natDegree : ℤ) := by
    have hmapped :=
      congrArg
        (N13InfinityMinus.coordinateToLaurentMinus K) hprod
    rw [map_mul,
      N13InfinityMinus.coordinateToLaurentMinus_xClass] at hmapped
    calc
      (N13InfinityMinus.coordinateToLaurentMinus K z).order +
            (N13InfinityMinus.coordinateToLaurentMinus K w).order =
          (N13InfinityMinus.coordinateToLaurentMinus K z *
            N13InfinityMinus.coordinateToLaurentMinus K w).order :=
        (HahnSeries.order_mul hzMinus hwMinus).symm
      _ = (N13BranchNorm.evalPoly K P).order := by
        rw [hmapped]
        rfl
      _ = -(P.natDegree : ℤ) :=
        N13BranchNorm.evalPoly_order K P hP
  have hone : qz = 0 ∨ qw = 0 := by
    by_contra hboth
    push Not at hboth
    have hzBound :=
      minus_order_le_neg_three_of_coeffY_ne_zero
        K pz qz (hzlin.trans_ne hz) hboth.1
          (by simpa only [hzlin] using hzplus)
    have hwBound :=
      minus_order_le_neg_three_of_coeffY_ne_zero
        K pw qw (hwlin.trans_ne hw) hboth.2
          (by simpa only [hwlin] using hwplus)
    rw [hzlin] at hzBound
    rw [hwlin] at hwBound
    have hdegZ : (P.natDegree : ℤ) ≤ 4 := by
      exact_mod_cast hdeg
    omega
  rcases hone with hqz | hqw
  · have hzpoly : z = SexticMumford.xClass M pz := by
      simpa [M, N13BranchNorm.linearFunction, hqz] using hzlin.symm
    have hpz : pz ≠ 0 := by
      intro hpz
      apply hz
      rw [hzpoly, hpz, SexticMumford.xClass_zero]
    have hcoeff : pz * qw = 0 := by
      have hcoeff' := congrArg (SexticMumford.coeffY M) hprod
      rw [hzpoly, SexticMumford.coeffY_xClass_mul] at hcoeff'
      simpa [M, qw] using hcoeff'
    exact ⟨hqz, (mul_eq_zero.mp hcoeff).resolve_left hpz⟩
  · have hwpoly : w = SexticMumford.xClass M pw := by
      simpa [M, N13BranchNorm.linearFunction, hqw] using hwlin.symm
    have hpw : pw ≠ 0 := by
      intro hpw
      apply hw
      rw [hwpoly, hpw, SexticMumford.xClass_zero]
    have hprod' :
        w * z = SexticMumford.xClass (N13Mumford.model K) P := by
      simpa [mul_comm] using hprod
    have hcoeff : pw * qz = 0 := by
      have hcoeff' := congrArg (SexticMumford.coeffY M) hprod'
      rw [hwpoly, SexticMumford.coeffY_xClass_mul] at hcoeff'
      simpa [M, qz] using hcoeff'
    exact ⟨(mul_eq_zero.mp hcoeff).resolve_left hpw, hqw⟩

end

end MazurProof.N13FactorRigidity

end
end

-- module FLT.Assumptions.MazurProof.SexticFunctionConjugation
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticFunctionConjugation =====
section

/-!
# Hyperelliptic conjugation on the sextic function field

The affine involution `Y ↦ -Y` extends functorially from the coordinate ring
to the fraction field.  Packaging it as a ring equivalence makes conjugation
of units and fractional ideals available without choosing numerators and
denominators.
-/

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

def conjugateEquiv (M : Model K) :
    CoordinateRing M ≃+* CoordinateRing M where
  toFun := conjugate M
  invFun := conjugate M
  left_inv := conjugate_involutive M
  right_inv := conjugate_involutive M
  map_mul' := map_mul (conjugate M)
  map_add' := map_add (conjugate M)

@[simp] theorem conjugateEquiv_apply (M : Model K)
    (z : CoordinateRing M) :
    conjugateEquiv M z = conjugate M z := rfl

@[simp] theorem conjugateEquiv_symm (M : Model K) :
    (conjugateEquiv M).symm = conjugateEquiv M := by
  rfl

def functionConjugateEquiv (M : Model K) :
    FunctionField M ≃+* FunctionField M :=
  IsFractionRing.ringEquivOfRingEquiv (K := FunctionField M)
    (L := FunctionField M) (conjugateEquiv M)

@[simp] theorem functionConjugateEquiv_algebraMap
    (M : Model K) (z : CoordinateRing M) :
    functionConjugateEquiv M
        (algebraMap (CoordinateRing M) (FunctionField M) z) =
      algebraMap (CoordinateRing M) (FunctionField M) (conjugate M z) := by
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (conjugateEquiv M) z

@[simp] theorem functionConjugateEquiv_symm (M : Model K) :
    (functionConjugateEquiv M).symm = functionConjugateEquiv M := by
  rw [functionConjugateEquiv,
    IsFractionRing.ringEquivOfRingEquiv_symm, conjugateEquiv_symm]

theorem functionConjugate_involutive (M : Model K) :
    Function.Involutive (functionConjugateEquiv M) := by
  intro z
  simpa only [functionConjugateEquiv_symm] using
    (functionConjugateEquiv M).symm_apply_apply z

def conjugateFunctionUnit (M : Model K) :
    (FunctionField M)ˣ →* (FunctionField M)ˣ :=
  Units.map (functionConjugateEquiv M).toRingHom

@[simp] theorem conjugateFunctionUnit_val (M : Model K)
    (z : (FunctionField M)ˣ) :
    (conjugateFunctionUnit M z : FunctionField M) =
      functionConjugateEquiv M (z : FunctionField M) := rfl

end

end MazurProof.SexticMumford

end
end

-- module FLT.Assumptions.MazurProof.SexticMumfordIdealConjugation
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordIdealConjugation =====
section

/-!
# Conjugation of Mumford ideals

Hyperelliptic conjugation sends `(u, Y-v)` to `(u, Y+v)`.  The following lifts
that elementary generator identity to integral and fractional ideals.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

theorem map_conjugate_mumfordIdeal (M : Model K) (u v : K[X]) :
    Ideal.map (conjugate M) (mumfordIdeal M u v) =
      mumfordIdeal M u (-v) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change conjugate M (xClass M u) ∈ mumfordIdeal M u (-v)
      rw [conjugate_xClass]
      exact xClass_mem_mumfordIdeal M u (-v)
    · change conjugate M (ySubClass M v) ∈ mumfordIdeal M u (-v)
      have htarget : ySubClass M (-v) ∈ mumfordIdeal M u (-v) :=
        ySubClass_mem_mumfordIdeal M u (-v)
      have heq :
          conjugate M (ySubClass M v) = -ySubClass M (-v) := by
        simp [ySubClass]
        ring
      rw [heq]
      exact (mumfordIdeal M u (-v)).neg_mem htarget
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · simpa using Ideal.mem_map_of_mem (conjugate M)
        (xClass_mem_mumfordIdeal M u v)
    · have hsource :
          -ySubClass M v ∈ mumfordIdeal M u v :=
        (mumfordIdeal M u v).neg_mem
          (ySubClass_mem_mumfordIdeal M u v)
      have hmap := Ideal.mem_map_of_mem (conjugate M) hsource
      have heq :
          conjugate M (-ySubClass M v) = ySubClass M (-v) := by
        simp [ySubClass]
        ring
      rw [← heq]
      exact hmap

def conjugateFractionalIdealEquiv (M : Model K) :
    FractionalIdeal (CoordinateRing M)⁰ (FunctionField M) ≃+*
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M) :=
  FractionalIdeal.ringEquivOfRingEquiv
    (FunctionField M) (FunctionField M) (conjugateEquiv M)

theorem conjugateFractionalIdealEquiv_coeIdeal
    (M : Model K) (I : Ideal (CoordinateRing M)) :
    conjugateFractionalIdealEquiv M
        (I : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      (Ideal.map (conjugate M) I :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
  ext x
  simp only [conjugateFractionalIdealEquiv,
    FractionalIdeal.ringEquivOfRingEquiv_apply,
    FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨conjugate M a, Ideal.mem_map_of_mem (conjugate M) ha, ?_⟩
    change algebraMap (CoordinateRing M) (FunctionField M)
        (conjugate M a) =
      functionConjugateEquiv M
        (algebraMap (CoordinateRing M) (FunctionField M) a)
    exact (functionConjugateEquiv_algebraMap M a).symm
  · rintro ⟨b, hb, rfl⟩
    rw [Ideal.mem_map_iff_of_surjective (conjugate M)
      (conjugate_involutive M).surjective] at hb
    obtain ⟨a, ha, hab⟩ := hb
    refine ⟨algebraMap (CoordinateRing M) (FunctionField M) a,
      FractionalIdeal.mem_coeIdeal_of_mem _ ha, ?_⟩
    change functionConjugateEquiv M
        (algebraMap (CoordinateRing M) (FunctionField M) a) =
      algebraMap (CoordinateRing M) (FunctionField M) b
    rw [functionConjugateEquiv_algebraMap, hab]

@[simp] theorem conjugateFractionalIdealEquiv_mumfordIdeal
    (M : Model K) (u v : K[X]) :
    conjugateFractionalIdealEquiv M
        (mumfordIdeal M u v :
          FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      (mumfordIdeal M u (-v) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
  rw [conjugateFractionalIdealEquiv_coeIdeal,
    map_conjugate_mumfordIdeal]

@[simp] theorem conjugateFractionalIdealEquiv_spanSingleton
    (M : Model K) (z : FunctionField M) :
    conjugateFractionalIdealEquiv M
        (FractionalIdeal.spanSingleton (CoordinateRing M)⁰ z) =
      FractionalIdeal.spanSingleton (CoordinateRing M)⁰
        (functionConjugateEquiv M z) := by
  exact FractionalIdeal.ringEquivOfRingEquiv_spanSingleton
    (FunctionField M) (FunctionField M) (conjugateEquiv M) z

def conjugateInvFrac (M : Model K) : InvFrac M →* InvFrac M :=
  Units.map (conjugateFractionalIdealEquiv M).toRingHom

@[simp] theorem conjugateInvFrac_principal
    (M : Model K) (z : (FunctionField M)ˣ) :
    conjugateInvFrac M
        (toPrincipalIdeal (CoordinateRing M) (FunctionField M) z) =
      toPrincipalIdeal (CoordinateRing M) (FunctionField M)
        (conjugateFunctionUnit M z) := by
  apply Units.ext
  change conjugateFractionalIdealEquiv M
      ((toPrincipalIdeal (CoordinateRing M) (FunctionField M) z :
        InvFrac M) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
    ((toPrincipalIdeal (CoordinateRing M) (FunctionField M)
      (conjugateFunctionUnit M z) : InvFrac M) :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))
  rw [coe_toPrincipalIdeal, coe_toPrincipalIdeal,
    conjugateFractionalIdealEquiv_spanSingleton,
    conjugateFunctionUnit_val]

def conjugateSemiMumford (M : Model K) (D : SemiMumford M) :
    SemiMumford M where
  u := D.u
  v := -D.v
  nInf := D.nInf
  u_monic := D.u_monic
  v_reduced := by
    rw [← Polynomial.modByMonic_eq_mod (-D.v) D.u_monic,
      Polynomial.neg_modByMonic,
      Polynomial.modByMonic_eq_mod D.v D.u_monic,
      D.v_reduced]
  curve_dvd := by
    simpa only [neg_sq] using D.curve_dvd

@[simp] theorem conjugateSemiMumford_u (M : Model K)
    (D : SemiMumford M) : (conjugateSemiMumford M D).u = D.u := rfl

@[simp] theorem conjugateSemiMumford_v (M : Model K)
    (D : SemiMumford M) : (conjugateSemiMumford M D).v = -D.v := rfl

@[simp] theorem conjugateInvFrac_mumfordIdealUnit
    (M : Model K) (D : SemiMumford M) :
    conjugateInvFrac M (mumfordIdealUnit M D) =
      mumfordIdealUnit M (conjugateSemiMumford M D) := by
  apply Units.ext
  change conjugateFractionalIdealEquiv M
      (mumfordIdeal M D.u D.v :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
    (mumfordIdeal M D.u (-D.v) :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))
  rw [conjugateFractionalIdealEquiv_mumfordIdeal]

theorem conjugate_principal_relation
    (M : Model K) (D₁ D₂ : SemiMumford M)
    (z : (FunctionField M)ˣ)
    (h :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) z =
        mumfordIdealUnit M D₂) :
    mumfordIdealUnit M (conjugateSemiMumford M D₁) *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M)
            (conjugateFunctionUnit M z) =
        mumfordIdealUnit M (conjugateSemiMumford M D₂) := by
  have hmap := congrArg (conjugateInvFrac M) h
  simpa only [map_mul, conjugateInvFrac_mumfordIdealUnit,
    conjugateInvFrac_principal] using hmap

end

end MazurProof.SexticMumford

end
end

-- module FLT.Assumptions.MazurProof.SexticMumfordPrincipalNumerator
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordPrincipalNumerator =====
section

/-!
# Integral numerators from principal relations

For a principal relation between two Mumford ideals, multiplying the
principal generator by the first `u`-polynomial clears all affine
denominator.  The proof is ideal-theoretic: the first Mumford ideal times its
hyperelliptic conjugate is the principal ideal `(u)`.
-/

open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

theorem exists_numerator_mem_of_principal_relation
    (M : Model K) (D₁ D₂ : SemiMumford M)
    (α : (FunctionField M)ˣ)
    (h :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) α =
        mumfordIdealUnit M D₂) :
    ∃ z : CoordinateRing M,
      z ∈ mumfordIdeal M D₂.u D₂.v ∧
        algebraMap (CoordinateRing M) (FunctionField M) z =
        (α : FunctionField M) *
          algebraMap (CoordinateRing M) (FunctionField M)
            (xClass M D₁.u) := by
  have hx :
      algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₁.u) ∈
        (mumfordIdealUnit M D₁ :
          FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
    rw [coe_mumfordIdealUnit]
    exact FractionalIdeal.mem_coeIdeal_of_mem (CoordinateRing M)⁰
      (xClass_mem_mumfordIdeal M D₁.u D₁.v)
  have hα :
      (α : FunctionField M) ∈
        (toPrincipalIdeal (CoordinateRing M) (FunctionField M) α :
          FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
    rw [coe_toPrincipalIdeal]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  have hprod := FractionalIdeal.mul_mem_mul hx hα
  have hfrac := congrArg
    (fun U : InvFrac M =>
      (U : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))) h
  rw [Units.val_mul, coe_toPrincipalIdeal, coe_mumfordIdealUnit,
    coe_mumfordIdealUnit] at hfrac
  rw [coe_mumfordIdealUnit, coe_toPrincipalIdeal] at hprod
  rw [hfrac] at hprod
  obtain ⟨z, hzmem, hzeq⟩ :=
    (FractionalIdeal.mem_coeIdeal (CoordinateRing M)⁰).mp hprod
  exact ⟨z, hzmem, by simpa [mul_comm] using hzeq⟩

theorem reverse_principal_relation
    (M : Model K) (D₁ D₂ : SemiMumford M)
    (α : (FunctionField M)ˣ)
    (h :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) α =
        mumfordIdealUnit M D₂) :
    mumfordIdealUnit M D₂ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) α⁻¹ =
        mumfordIdealUnit M D₁ := by
  rw [← h]
  simp only [mul_assoc, map_inv, mul_inv_cancel, mul_one]

theorem exists_integral_factor_pair_of_principal_relation
    (M : Model K) (D₁ D₂ : SemiMumford M)
    (α : (FunctionField M)ˣ)
    (h :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) α =
        mumfordIdealUnit M D₂) :
    ∃ z w : CoordinateRing M,
      z ∈ mumfordIdeal M D₂.u D₂.v ∧
      w ∈ mumfordIdeal M D₁.u D₁.v ∧
      z * w = xClass M (D₁.u * D₂.u) ∧
      algebraMap (CoordinateRing M) (FunctionField M) z =
        (α : FunctionField M) *
          algebraMap (CoordinateRing M) (FunctionField M)
            (xClass M D₁.u) ∧
      algebraMap (CoordinateRing M) (FunctionField M) w =
        (↑α⁻¹ : FunctionField M) *
          algebraMap (CoordinateRing M) (FunctionField M)
            (xClass M D₂.u) := by
  obtain ⟨z, hzmem, hzeq⟩ :=
    exists_numerator_mem_of_principal_relation M D₁ D₂ α h
  obtain ⟨w, hwmem, hweq⟩ :=
    exists_numerator_mem_of_principal_relation M D₂ D₁ α⁻¹
      (reverse_principal_relation M D₁ D₂ α h)
  refine ⟨z, w, hzmem, hwmem, ?_, hzeq, hweq⟩
  apply IsFractionRing.injective (CoordinateRing M) (FunctionField M)
  rw [map_mul, hzeq, hweq, xClass_mul, map_mul]
  change
    ((α : FunctionField M) *
        algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₁.u)) *
      ((↑α⁻¹ : FunctionField M) *
        algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₂.u)) =
      algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₁.u) *
        algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₂.u)
  rw [Units.val_inv_eq_inv_val]
  field_simp

end

end MazurProof.SexticMumford

end
end


