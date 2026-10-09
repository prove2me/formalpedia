-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialAffineVerticalGraph_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialAffineVerticalGraph_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:37:19.717902+00:00
-- url     : https://prove2.me/theorems/724602a1-7c40-4d48-9ade-40230a5aa63f
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialAffineVerticalGraph source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialAffineVerticalGraph

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialAffineVerticalGraph
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialConstantInfinityVerticalGraph_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialQuadraticGraphRegularity_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialVerticalDivisorCharts_p0

set_option autoImplicit false




/-!
# Vertical graphs on the special affine chart

A rank-two affine quotient with basis `{1,y}` is cut out by a monic
quadratic `m(y)` and a linear relation `x=a+cy`.  Over `F₂` the reduced
slope is either zero or one.

For slope zero, the curve equation forces `m=y²+y`, and the graph ideal is
the principal fibre ideal `(x-a)`.  For slope one, the involution
`y=x+a` turns the vertical graph into the horizontal graph
`m(x+a)=0, y=x+a`.  This file proves both ideal identities and packages the
nonconstant branch as regular special Mumford data.
-/

open Polynomial

namespace MazurProof.N13SpecialAffineVerticalGraph

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The special residue field. -/
abbrev K :=
  N13GoodCoordinateRingTwo.K

/-- The special affine coordinate ring. -/
abbrev Ring :=
  N13GoodCoordinateRingTwo.CoordinateRing

/-- Substitute a polynomial for `x` in the affine curve equation while
retaining `y` as the polynomial variable. -/
def verticalCurve (s : K[X]) : K[X] :=
  X ^ 2 +
    N13GoodCoordinateRingTwo.hPoly.comp s * X -
    N13GoodCoordinateRingTwo.rhsPoly.comp s

/-- The special vertical graph ideal
`(m(y),x-(a+cy))`. -/
def verticalIdeal (m : K[X]) (a c : K) : Ideal Ring :=
  Ideal.span
    ({aeval N13GoodCoordinateRingTwo.yClass m,
      N13GoodCoordinateRingTwo.xClass X -
        aeval N13GoodCoordinateRingTwo.yClass
          (C a + C c * X)} : Set Ring)

/-- At a constant special horizontal coordinate, the sheet polynomial is
`y²+y`. -/
theorem verticalCurve_C (a : K) :
    verticalCurve (C a) = X ^ 2 + X := by
  unfold verticalCurve
  have hh := N13SpecialVerticalDivisorCharts.hPoly_eval a
  have hr := N13SpecialVerticalDivisorCharts.rhsPoly_eval a
  simp [comp_C, hh, hr]

/-- In the slope-zero branch, the vertical graph ideal is the principal
fibre ideal `(x-a)`. -/
theorem verticalIdeal_eq_span_of_slope_zero
    (m w : K[X])
    (a : K)
    (hm : m.Monic)
    (hdeg : m.natDegree = 2)
    (hcurve : verticalCurve (C a) = m * w) :
    verticalIdeal m a 0 =
      Ideal.span
        ({N13GoodCoordinateRingTwo.xClass (X - C a)} :
          Set Ring) := by
  have hmShape : m = X ^ 2 + X := by
    apply
      N13SpecialConstantInfinityVerticalGraph.monicQuadratic_eq_X_sq_add_X
        m w hm hdeg
    rw [← hcurve, verticalCurve_C]
  let p : K[X] := X - C a
  let J : Ideal Ring :=
    Ideal.span
      ({N13GoodCoordinateRingTwo.xClass p} : Set Ring)
  have hpJ :
      N13GoodCoordinateRingTwo.xClass p ∈ J :=
    Ideal.subset_span (by simp)
  have hhdiv :
      p ∣ N13GoodCoordinateRingTwo.hPoly - C 1 := by
    simpa [p, N13SpecialVerticalDivisorCharts.hPoly_eval a] using
      (X_sub_C_dvd_sub_C_eval
        (p := N13GoodCoordinateRingTwo.hPoly) (a := a))
  have hrhsdiv :
      p ∣ N13GoodCoordinateRingTwo.rhsPoly := by
    simpa [p, N13SpecialVerticalDivisorCharts.rhsPoly_eval a] using
      (X_sub_C_dvd_sub_C_eval
        (p := N13GoodCoordinateRingTwo.rhsPoly) (a := a))
  have hhJ :
      N13GoodCoordinateRingTwo.xClass
          (N13GoodCoordinateRingTwo.hPoly - C 1) ∈ J := by
    obtain ⟨q, hq⟩ := hhdiv
    rw [hq, N13GoodCoordinateRingTwo.xClass_mul]
    exact
      Ideal.mul_mem_right
        (N13GoodCoordinateRingTwo.xClass q) J hpJ
  have hrhsJ :
      N13GoodCoordinateRingTwo.xClass
          N13GoodCoordinateRingTwo.rhsPoly ∈ J := by
    obtain ⟨q, hq⟩ := hrhsdiv
    rw [hq, N13GoodCoordinateRingTwo.xClass_mul]
    exact
      Ideal.mul_mem_right
        (N13GoodCoordinateRingTwo.xClass q) J hpJ
  have hyyJ :
      N13GoodCoordinateRingTwo.yClass ^ 2 +
          N13GoodCoordinateRingTwo.yClass ∈ J := by
    have hdelta :=
      Ideal.mul_mem_right
        N13GoodCoordinateRingTwo.yClass J hhJ
    have hmem := Ideal.sub_mem J hrhsJ hdelta
    have hrel := N13GoodCoordinateRingTwo.yClass_relation
    convert hmem using 1
    simp only [N13GoodCoordinateRingTwo.xClass_sub]
    have hOne :
        N13GoodCoordinateRingTwo.xClass (C (1 : K)) = 1 := rfl
    rw [hOne]
    linear_combination hrel
  have hpClass :
      N13GoodCoordinateRingTwo.xClass p =
        N13GoodCoordinateRingTwo.xClass X -
          algebraMap K Ring a := by
    rw [show
      N13GoodCoordinateRingTwo.xClass p =
        N13GoodCoordinateRingTwo.xClass X -
          N13GoodCoordinateRingTwo.xClass (C a) by
      simp [p]]
    congr 1
  rw [verticalIdeal]
  simp only [Polynomial.aeval_C, map_zero, zero_mul, add_zero]
  rw [← hpClass]
  change
    Ideal.span
        ({aeval N13GoodCoordinateRingTwo.yClass m,
          N13GoodCoordinateRingTwo.xClass p} : Set Ring) =
      J
  rw [hmShape]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · simpa using hyyJ
    · exact hpJ
  · apply Ideal.span_mono
    simp

/-- Translation by an `F₂` coordinate is involutive. -/
theorem translateLinear_comp_translateLinear (a : K) :
    (C a + X).comp (X + C a) = X := by
  have haa : a + a = 0 := by
    fin_cases a <;> decide
  simp only [add_comp, C_comp, X_comp]
  calc
    C a + (X + C a) = X + (C a + C a) := by ring
    _ = X := by rw [← C_add, haa]; simp

/-- Translation by `a` on special affine polynomials. -/
def translate (a : K) (p : K[X]) : K[X] :=
  p.comp (X + C a)

/-- Translating a slope-one vertical factorization gives the horizontal
special semigraph equation. -/
theorem translated_curve_eq
    (m w : K[X])
    (a : K)
    (hcurve :
      verticalCurve (C a + X) = m * w) :
    (X + C a) ^ 2 +
          N13GoodCoordinateRingTwo.hPoly * (X + C a) -
          N13GoodCoordinateRingTwo.rhsPoly =
      translate a m * translate a w := by
  have h :=
    congrArg (fun p : K[X] => p.comp (X + C a)) hcurve
  simp only [verticalCurve, pow_comp, add_comp, mul_comp,
    sub_comp, X_comp] at h
  rw [comp_assoc, translateLinear_comp_translateLinear, comp_X,
    comp_assoc, translateLinear_comp_translateLinear, comp_X] at h
  simpa [translate] using h

/-- The translated slope-one vertical graph is regular horizontal special
Mumford data. -/
def horizontalGraph
    (m w : K[X])
    (a : K)
    (hm : m.Monic)
    (hdeg : m.natDegree = 2)
    (hcurve :
      verticalCurve (C a + X) = m * w) :
    N13GoodCoordinateRingTwo.SemiMumford where
  u := translate a m
  v := X + C a
  w := translate a w
  u_monic := hm.comp_X_add_C a
  curve_eq := translated_curve_eq m w a hcurve
  bezout :=
    N13SpecialQuadraticGraphRegularity.quadratic_graph_bezout
      (translate a m) (X + C a) (translate a w)
      (hm.comp_X_add_C a)
      (by
        change (m.comp (X + C a)).natDegree = 2
        rw [Polynomial.natDegree_comp, natDegree_X_add_C, hdeg])

/-- The translated horizontal polynomial retains degree two. -/
theorem horizontalGraph_u_natDegree
    (m w : K[X])
    (a : K)
    (hm : m.Monic)
    (hdeg : m.natDegree = 2)
    (hcurve :
      verticalCurve (C a + X) = m * w) :
    (horizontalGraph m w a hm hdeg hcurve).u.natDegree = 2 := by
  change (m.comp (X + C a)).natDegree = 2
  rw [Polynomial.natDegree_comp, natDegree_X_add_C, hdeg]

/-- Evaluating at the special class `x` is the canonical base-polynomial
map into the affine coordinate ring. -/
theorem xClass_eq_aeval_xClass (p : K[X]) :
    N13GoodCoordinateRingTwo.xClass p =
      aeval (N13GoodCoordinateRingTwo.xClass X) p := by
  let ψ : K[X] →ₐ[K] Ring :=
    IsScalarTower.toAlgHom K K[X] Ring
  have h :
      aeval (N13GoodCoordinateRingTwo.xClass X) = ψ := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    rfl
  exact (DFunLike.congr_fun h p).symm

/-- The equations `x=a+y` and `y=x+a` define the same element of the
special affine coordinate ring. -/
theorem verticalLinear_eq_horizontalLinear (a : K) :
    N13GoodCoordinateRingTwo.xClass X -
        aeval N13GoodCoordinateRingTwo.yClass (C a + X) =
      N13GoodCoordinateRingTwo.yClass -
        N13GoodCoordinateRingTwo.xClass (X + C a) := by
  simp only [map_add, Polynomial.aeval_C, aeval_X,
    N13GoodCoordinateRingTwo.xClass_add]
  have hCa :
      N13GoodCoordinateRingTwo.xClass (C a) =
        algebraMap K Ring a :=
    (IsScalarTower.algebraMap_apply K K[X] Ring a).symm
  rw [hCa]
  have htwoK : (2 : K) = 0 :=
    CharP.cast_eq_zero K 2
  have htwo : (2 : Ring) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (algebraMap K Ring) htwoK
  linear_combination
    (N13GoodCoordinateRingTwo.xClass X -
      N13GoodCoordinateRingTwo.yClass) * htwo

/-- Modulo the common slope-one linear equation, evaluating `m` at `y` or
at `x+a` gives the same class. -/
theorem verticalPolynomial_sub_horizontalPolynomial_mem
    (m : K[X])
    (a : K) :
    aeval N13GoodCoordinateRingTwo.yClass m -
        N13GoodCoordinateRingTwo.xClass (translate a m) ∈
      Ideal.span
        ({N13GoodCoordinateRingTwo.yClass -
            N13GoodCoordinateRingTwo.xClass
              (X + C a)} : Set Ring) := by
  let s : Ring :=
    N13GoodCoordinateRingTwo.xClass (X + C a)
  obtain ⟨q, hq⟩ :=
    sub_dvd_eval_sub N13GoodCoordinateRingTwo.yClass s
      (m.map (algebraMap K Ring))
  have hdiff :
      aeval N13GoodCoordinateRingTwo.yClass m -
          aeval s m =
        (N13GoodCoordinateRingTwo.yClass - s) * q := by
    simpa [Polynomial.aeval_def] using hq
  have hs :
      N13GoodCoordinateRingTwo.xClass (translate a m) =
        aeval s m := by
    rw [xClass_eq_aeval_xClass, translate, aeval_comp]
    apply congrArg (fun z : Ring => aeval z m)
    simpa only [s] using
      (xClass_eq_aeval_xClass (X + C a)).symm
  change
    aeval N13GoodCoordinateRingTwo.yClass m -
        N13GoodCoordinateRingTwo.xClass (translate a m) ∈
      Ideal.span
        ({N13GoodCoordinateRingTwo.yClass - s} : Set Ring)
  rw [hs, hdiff]
  exact
    Ideal.mul_mem_right q _
      (Ideal.subset_span (by simp))

/-- A slope-one vertical graph ideal is literally the translated horizontal
Mumford ideal. -/
theorem verticalIdeal_eq_mumfordIdeal_of_slope_one
    (m : K[X])
    (a : K) :
    verticalIdeal m a 1 =
      N13GoodCoordinateRingTwo.mumfordIdeal
        (translate a m) (X + C a) := by
  let g : Ring :=
    N13GoodCoordinateRingTwo.yClass -
      N13GoodCoordinateRingTwo.xClass (X + C a)
  let mY : Ring :=
    aeval N13GoodCoordinateRingTwo.yClass m
  let mX : Ring :=
    N13GoodCoordinateRingTwo.xClass (translate a m)
  have hlinear := verticalLinear_eq_horizontalLinear a
  have hdiff :
      mY - mX ∈ Ideal.span ({g} : Set Ring) := by
    exact verticalPolynomial_sub_horizontalPolynomial_mem m a
  rw [verticalIdeal,
    N13GoodCoordinateRingTwo.mumfordIdeal,
    N13GoodCoordinateRingTwo.ySubClass]
  simp only [map_one, one_mul]
  change Ideal.span ({mY, _} : Set Ring) =
    Ideal.span ({mX, g} : Set Ring)
  rw [hlinear]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have hmX :
          mX ∈ Ideal.span ({mX, g} : Set Ring) :=
        Ideal.subset_span (by simp)
      have hdiff' :
          mY - mX ∈ Ideal.span ({mX, g} : Set Ring) :=
        (Ideal.span_mono (by
          intro z hz
          simp only [Set.mem_singleton_iff] at hz
          subst z
          simp [g])) hdiff
      have hadd :=
        Ideal.add_mem (Ideal.span ({mX, g} : Set Ring)) hdiff' hmX
      simpa [g] using hadd
    · exact Ideal.subset_span (by simp [g])
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have hmY :
          mY ∈ Ideal.span ({mY, g} : Set Ring) :=
        Ideal.subset_span (by simp)
      have hdiff' :
          mY - mX ∈ Ideal.span ({mY, g} : Set Ring) :=
        (Ideal.span_mono (by
          intro z hz
          simp only [Set.mem_singleton_iff] at hz
          subst z
          simp [g])) hdiff
      have hsub :=
        Ideal.sub_mem (Ideal.span ({mY, g} : Set Ring)) hmY hdiff'
      simpa [g] using hsub
    · exact Ideal.subset_span (by simp [g])

end

end MazurProof.N13SpecialAffineVerticalGraph


