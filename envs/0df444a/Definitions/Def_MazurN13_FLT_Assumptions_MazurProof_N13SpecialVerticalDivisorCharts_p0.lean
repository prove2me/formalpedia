-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialVerticalDivisorCharts_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialVerticalDivisorCharts_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:23:52.278265+00:00
-- url     : https://prove2.me/theorems/69fb2529-e0cd-4c81-8655-dfe7cb0e64c3
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialVerticalDivisorCharts source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialVerticalDivisorCharts

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialVerticalDivisorCharts
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialGraphDivisorCharts_p0

set_option autoImplicit false




/-!
# Chart ideals of vertical special N13 divisors

The finite canonical fibre above `x = a` consists of the two points
`(a,0)` and `(a,1)`.  Their affine point ideals multiply to the principal
horizontal ideal `(X-a)`: the two graph factors are hyperelliptic conjugates.

This file also computes the infinity-chart ideal.  The fibre above `a = 0`
is absent from the overlap and has unit infinity ideal.  The fibre above
`a = 1` meets the infinity chart at `t = 1`, where the two ordinate ideals
again multiply to the principal ideal `(t-1)`.
-/

open Polynomial
open scoped Sym2

namespace MazurProof.N13SpecialVerticalDivisorCharts

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

open N13GoodCoordinateRingTwo

abbrev K := N13GoodCoordinateRingTwo.K

/-- The two affine sheets above a special horizontal coordinate. -/
def verticalPoint (a y : K) :
    N13SpecialDivisorCharts.CurvePoint :=
  N13AbelFiberTwoModel.curvePointEquiv.symm
    (Sum.inl a, y)

/-- The affine chart ideal of one sheet is its literal point graph ideal. -/
theorem verticalPoint_affineIdeal (a y : K) :
    (N13SpecialDivisorCharts.point
        (verticalPoint a y)).affineIdeal =
      mumfordIdeal (X - C a) (C y) := by
  change
    (N13SpecialDivisorCharts.point
        (Sum.inl
          (⟨(a, y), _⟩ :
            N13SpecialDivisorCharts.AffinePoint))).affineIdeal =
      _
  rw [N13SpecialGraphDivisorCharts.point_affineIdeal]
  rfl

/-- The affine vertical derivative is one at every special affine point. -/
theorem hPoly_eval (a : K) :
    hPoly.eval a = 1 := by
  simp only [hPoly, eval_add, eval_pow, eval_X, eval_one]
  fin_cases a <;> decide

/-- Both finite base coordinates are roots of the affine right-hand side. -/
theorem rhsPoly_eval (a : K) :
    rhsPoly.eval a = 0 := by
  simp only [rhsPoly, eval_add, eval_pow, eval_X]
  fin_cases a <;> decide

/-- The two affine sheet ideals multiply to the principal fibre ideal. -/
theorem verticalPointIdeal_mul :
    ∀ a : K,
      mumfordIdeal (X - C a) 0 *
          mumfordIdeal (X - C a) 1 =
        Ideal.span ({xClass (X - C a)} :
          Set CoordinateRing) := by
  intro a
  let p : K[X] := X - C a
  have hrhs : p ∣ -rhsPoly := by
    have hdiv :
        p ∣ -rhsPoly - C ((-rhsPoly).eval a) :=
      X_sub_C_dvd_sub_C_eval
    simpa [p, rhsPoly_eval a] using hdiv
  let w : K[X] := Classical.choose hrhs
  have hw : -rhsPoly = p * w :=
    Classical.choose_spec hrhs
  let D :
      GeneralizedGraphIdealCore.SemiGraph hPoly rhsPoly :=
    { u := p
      v := 0
      w := w
      curve_eq := by
        simpa using hw }
  have hhdiv : p ∣ hPoly - C 1 := by
    simpa [p, hPoly_eval a] using
      (X_sub_C_dvd_sub_C_eval (p := hPoly) (a := a))
  obtain ⟨s, hs⟩ := hhdiv
  have hbez :
      ∃ A B C : K[X],
        A * D.u + B * (2 * D.v + hPoly) + C * D.w = 1 := by
    refine ⟨-s, 1, 0, ?_⟩
    dsimp [D]
    have htwo : (2 : K[X]) = 0 :=
      CharP.cast_eq_zero (K[X]) 2
    rw [htwo, zero_mul, zero_add, one_mul, zero_mul, add_zero]
    rw [C_1] at hs
    linear_combination hs
  have hconj :
      mumfordIdeal p (conjugateV 0) =
        mumfordIdeal p 1 := by
    have heval :
        (conjugateV 0).eval a = 1 := by
      simp [conjugateV, hPoly_eval a]
    have hdiv :
        p ∣ conjugateV 0 - C 1 := by
      simpa [p, heval] using
        (X_sub_C_dvd_sub_C_eval
          (p := conjugateV 0) (a := a))
    simpa [mumfordIdeal,
      GeneralizedGraphIdealCore.graphIdeal,
      ySubClass,
      GeneralizedGraphIdealCore.ySubClass] using
      (GeneralizedGraphIdealCore.graphIdeal_eq_of_dvd_sub
        xClassHom yClass p 1 (conjugateV 0) hdiv)
  rw [← hconj]
  change
    GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass p 0 *
        GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass p
            (GeneralizedGraphIdealCore.conjugateV hPoly 0) =
      Ideal.span ({xClassHom p} : Set CoordinateRing)
  exact
    (GeneralizedGraphIdealCore.graphIdeal_mul_conj
      xClassHom yClass hPoly rhsPoly D
      yClass_relation hbez)

/-- The affine ideal of a finite canonical divisor is `(X-a)`. -/
theorem canonicalDivisor_affineIdeal (a : K) :
    (N13SpecialDivisorCharts.ofDivisor
        (N13AbelFiberTwoModel.canonicalDivisor
          (Sum.inl a))).affineIdeal =
      Ideal.span ({xClass (X - C a)} :
        Set CoordinateRing) := by
  rw [N13AbelFiberTwoModel.canonicalDivisor,
    N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13SpecialDivisorCharts.point
        (verticalPoint a 0)).affineIdeal *
      (N13SpecialDivisorCharts.point
        (verticalPoint a 1)).affineIdeal =
      _
  rw [verticalPoint_affineIdeal, verticalPoint_affineIdeal]
  simpa using verticalPointIdeal_mul a

/-- The ordinate on the special infinity chart satisfies its generalized
quadratic equation. -/
theorem infinity_yClass_relation :
    N13SpecialInfinityChart.vClass ^ 2 +
        (algebraMap K[X]
          N13SpecialDivisorCharts.SpecialInfinity)
            N13SpecialInfinityChart.hPoly *
          N13SpecialInfinityChart.vClass =
      (algebraMap K[X]
        N13SpecialDivisorCharts.SpecialInfinity)
          N13SpecialInfinityChart.rhsPoly := by
  change
    N13SpecialInfinityChart.vClass ^ 2 +
        (AdjoinRoot.of N13SpecialInfinityChart.curvePoly)
            N13SpecialInfinityChart.hPoly *
          N13SpecialInfinityChart.vClass =
      (AdjoinRoot.of N13SpecialInfinityChart.curvePoly)
        N13SpecialInfinityChart.rhsPoly
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [N13SpecialInfinityChart.curvePoly]
  ring

/-- At any `F₂`-rational base coordinate `t = a`, the two infinity-chart
sheet ideals multiply to the principal fibre ideal `(t-a)`. -/
theorem infinityPointIdeal_mul (a : K) :
    N13SpecialDivisorCharts.infinityPointIdeal a 0 *
        N13SpecialDivisorCharts.infinityPointIdeal a 1 =
      Ideal.span
        ({N13SpecialInfinityChart.tClass -
            algebraMap K[X] N13SpecialDivisorCharts.SpecialInfinity
              (C a)} :
          Set N13SpecialDivisorCharts.SpecialInfinity) := by
  let xClassHom :
      K[X] →+* N13SpecialDivisorCharts.SpecialInfinity :=
    AdjoinRoot.of N13SpecialInfinityChart.curvePoly
  let yClass : N13SpecialDivisorCharts.SpecialInfinity :=
    N13SpecialInfinityChart.vClass
  let p : K[X] := X - C a
  have hrhs : p ∣ -N13SpecialInfinityChart.rhsPoly := by
    have heval :
        (-N13SpecialInfinityChart.rhsPoly).eval a = 0 := by
      simp only [N13SpecialInfinityChart.rhsPoly, eval_neg,
        eval_add, eval_X, eval_pow]
      fin_cases a <;> decide
    have hdiv :
        p ∣ -N13SpecialInfinityChart.rhsPoly -
          C ((-N13SpecialInfinityChart.rhsPoly).eval a) :=
      X_sub_C_dvd_sub_C_eval
    simpa [p, heval] using hdiv
  let w : K[X] := Classical.choose hrhs
  have hw :
      -N13SpecialInfinityChart.rhsPoly = p * w :=
    Classical.choose_spec hrhs
  let D : GeneralizedGraphIdealCore.SemiGraph
      N13SpecialInfinityChart.hPoly
      N13SpecialInfinityChart.rhsPoly :=
    { u := p
      v := 0
      w := w
      curve_eq := by simpa using hw }
  have hhEval :
      N13SpecialInfinityChart.hPoly.eval a = 1 := by
    simp only [N13SpecialInfinityChart.hPoly, eval_add,
      eval_one, eval_pow, eval_X]
    fin_cases a <;> decide
  have hhdiv :
      p ∣ N13SpecialInfinityChart.hPoly - C 1 := by
    simpa [p, hhEval] using
      (X_sub_C_dvd_sub_C_eval
        (p := N13SpecialInfinityChart.hPoly) (a := a))
  obtain ⟨s, hs⟩ := hhdiv
  have hbez :
      ∃ A B C : K[X],
        A * D.u +
            B * (2 * D.v + N13SpecialInfinityChart.hPoly) +
            C * D.w = 1 := by
    refine ⟨-s, 1, 0, ?_⟩
    dsimp [D]
    have htwo : (2 : K[X]) = 0 :=
      CharP.cast_eq_zero (K[X]) 2
    rw [htwo, zero_mul, zero_add, one_mul, zero_mul, add_zero]
    rw [C_1] at hs
    linear_combination hs
  have hconj :
      GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass p
            (GeneralizedGraphIdealCore.conjugateV
              N13SpecialInfinityChart.hPoly 0) =
        GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass p 1 := by
    have heval :
        (GeneralizedGraphIdealCore.conjugateV
          N13SpecialInfinityChart.hPoly 0).eval a = 1 := by
      simp [GeneralizedGraphIdealCore.conjugateV, hhEval]
    have hdiv :
        p ∣
          GeneralizedGraphIdealCore.conjugateV
              N13SpecialInfinityChart.hPoly 0 -
            C 1 := by
      simpa [p, heval] using
        (X_sub_C_dvd_sub_C_eval
          (p := GeneralizedGraphIdealCore.conjugateV
            N13SpecialInfinityChart.hPoly 0)
          (a := a))
    exact
      GeneralizedGraphIdealCore.graphIdeal_eq_of_dvd_sub
        xClassHom yClass p 1
        (GeneralizedGraphIdealCore.conjugateV
          N13SpecialInfinityChart.hPoly 0) hdiv
  have hproduct :=
    GeneralizedGraphIdealCore.graphIdeal_mul_conj
      xClassHom yClass
        N13SpecialInfinityChart.hPoly
        N13SpecialInfinityChart.rhsPoly
        D infinity_yClass_relation hbez
  rw [hconj] at hproduct
  change
    GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass p 0 *
        GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass p 1 =
      Ideal.span ({xClassHom p} :
        Set N13SpecialDivisorCharts.SpecialInfinity) at hproduct
  have hX :
      xClassHom X = N13SpecialInfinityChart.tClass := rfl
  simpa [N13SpecialDivisorCharts.infinityPointIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    GeneralizedGraphIdealCore.ySubClass,
    xClassHom, yClass, p, hX] using hproduct

/-- At `t = 1`, the two infinity-chart sheet ideals multiply to `(t-1)`. -/
theorem infinityPointIdeal_one_mul :
    N13SpecialDivisorCharts.infinityPointIdeal 1 0 *
        N13SpecialDivisorCharts.infinityPointIdeal 1 1 =
      Ideal.span
        ({N13SpecialInfinityChart.tClass -
            algebraMap K[X]
              N13SpecialDivisorCharts.SpecialInfinity (C 1)} :
          Set N13SpecialDivisorCharts.SpecialInfinity) :=
  infinityPointIdeal_mul 1

/-- One of the two special curve points above the base point at infinity. -/
def infinityVerticalPoint (v : K) :
    N13SpecialDivisorCharts.CurvePoint :=
  N13AbelFiberTwoModel.curvePointEquiv.symm
    (Sum.inr (), v)

/-- A point above the base point at infinity is absent from the ordinary
affine chart. -/
theorem infinityVerticalPoint_affineIdeal (v : K) :
    (N13SpecialDivisorCharts.point
        (infinityVerticalPoint v)).affineIdeal = ⊤ := by
  rw [N13SpecialDivisorCharts.point.eq_def]
  rfl

/-- A point above the base point at infinity has its literal ideal at
`t = 0`. -/
theorem infinityVerticalPoint_infinityIdeal (v : K) :
    (N13SpecialDivisorCharts.point
        (infinityVerticalPoint v)).infinityIdeal =
      N13SpecialDivisorCharts.infinityPointIdeal 0 v := by
  rw [N13SpecialDivisorCharts.point.eq_def]
  rfl

/-- The canonical divisor above the base point at infinity is absent from
the ordinary affine chart. -/
theorem canonicalInfinityDivisor_affineIdeal :
    (N13SpecialDivisorCharts.ofDivisor
        (N13AbelFiberTwoModel.canonicalDivisor
          (Sum.inr ()))).affineIdeal = ⊤ := by
  rw [N13AbelFiberTwoModel.canonicalDivisor,
    N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13SpecialDivisorCharts.point
        (infinityVerticalPoint 0)).affineIdeal *
      (N13SpecialDivisorCharts.point
        (infinityVerticalPoint 1)).affineIdeal =
      ⊤
  rw [infinityVerticalPoint_affineIdeal,
    infinityVerticalPoint_affineIdeal]
  simp

/-- The infinity ideal of the canonical divisor above infinity is the
principal fibre ideal `(t)`. -/
theorem canonicalInfinityDivisor_infinityIdeal :
    (N13SpecialDivisorCharts.ofDivisor
        (N13AbelFiberTwoModel.canonicalDivisor
          (Sum.inr ()))).infinityIdeal =
      Ideal.span
        ({N13SpecialInfinityChart.tClass} :
          Set N13SpecialDivisorCharts.SpecialInfinity) := by
  rw [N13AbelFiberTwoModel.canonicalDivisor,
    N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13SpecialDivisorCharts.point
        (infinityVerticalPoint 0)).infinityIdeal *
      (N13SpecialDivisorCharts.point
        (infinityVerticalPoint 1)).infinityIdeal =
      _
  rw [infinityVerticalPoint_infinityIdeal,
    infinityVerticalPoint_infinityIdeal,
    infinityPointIdeal_mul]
  congr 2
  simp

/-- A finite point above `x = 0` is absent from the infinity chart. -/
theorem verticalPoint_zero_infinityIdeal (y : K) :
    (N13SpecialDivisorCharts.point
      (verticalPoint 0 y)).infinityIdeal = ⊤ := by
  rw [N13SpecialDivisorCharts.point.eq_def]
  dsimp [verticalPoint, N13AbelFiberTwoModel.curvePointEquiv]
  simp [N13SpecialDivisorCharts.affineZeroPoint]

/-- A finite point above `x = 1` has its literal ideal at `t = 1`. -/
theorem verticalPoint_one_infinityIdeal (y : K) :
    (N13SpecialDivisorCharts.point
        (verticalPoint 1 y)).infinityIdeal =
      N13SpecialDivisorCharts.infinityPointIdeal 1 y := by
  rw [N13SpecialDivisorCharts.point.eq_def]
  dsimp [verticalPoint, N13AbelFiberTwoModel.curvePointEquiv]
  simp [N13SpecialDivisorCharts.affineOnePoint]

/-- The infinity ideal of a finite canonical fibre is unit above `x = 0`
and the principal ideal `(t-1)` above `x = 1`. -/
theorem canonicalDivisor_infinityIdeal (a : K) :
    (N13SpecialDivisorCharts.ofDivisor
        (N13AbelFiberTwoModel.canonicalDivisor
          (Sum.inl a))).infinityIdeal =
      if a = 0 then ⊤ else
        Ideal.span
          ({N13SpecialInfinityChart.tClass -
              algebraMap K[X]
                N13SpecialDivisorCharts.SpecialInfinity (C 1)} :
            Set N13SpecialDivisorCharts.SpecialInfinity) := by
  rw [N13AbelFiberTwoModel.canonicalDivisor,
    N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13SpecialDivisorCharts.point
        (verticalPoint a 0)).infinityIdeal *
      (N13SpecialDivisorCharts.point
        (verticalPoint a 1)).infinityIdeal =
      _
  rcases
      N13GoodModelTwo.fixedTwo_eq_zero_or_one
        a (ZMod.pow_card a) with rfl | rfl
  · rw [verticalPoint_zero_infinityIdeal,
      verticalPoint_zero_infinityIdeal]
    simp
  · rw [verticalPoint_one_infinityIdeal,
      verticalPoint_one_infinityIdeal]
    simp only [if_false, one_ne_zero]
    change
      N13SpecialDivisorCharts.infinityPointIdeal 1 0 *
          N13SpecialDivisorCharts.infinityPointIdeal 1 1 =
        _
    exact infinityPointIdeal_one_mul

/-- The canonical divisor above a constant infinity coordinate `t = a`.
At `a = 0` this is the base fibre at infinity; at `a = 1` it is the finite
fibre above `x = 1`. -/
def constantInfinityFibreDivisor
    (a : K) :
    N13SpecialDivisorCharts.EffectiveDivisorTwo :=
  if a = 0 then
    N13AbelFiberTwoModel.canonicalDivisor (Sum.inr ())
  else
    N13AbelFiberTwoModel.canonicalDivisor (Sum.inl 1)

/-- The affine ideal of the constant-`t` canonical fibre is unit at `t=0`
and `(x-1)` at `t=1`. -/
theorem constantInfinityFibreDivisor_affineIdeal (a : K) :
    (N13SpecialDivisorCharts.ofDivisor
        (constantInfinityFibreDivisor a)).affineIdeal =
      if a = 0 then ⊤ else
        Ideal.span
          ({xClass (X - C 1)} : Set CoordinateRing) := by
  rcases
      N13GoodModelTwo.fixedTwo_eq_zero_or_one
        a (ZMod.pow_card a) with rfl | rfl
  · simp [constantInfinityFibreDivisor,
      canonicalInfinityDivisor_affineIdeal]
  · simp [constantInfinityFibreDivisor,
      canonicalDivisor_affineIdeal]

/-- The infinity ideal of the constant-`t` canonical fibre is the principal
fibre ideal `(t-a)`. -/
theorem constantInfinityFibreDivisor_infinityIdeal (a : K) :
    (N13SpecialDivisorCharts.ofDivisor
        (constantInfinityFibreDivisor a)).infinityIdeal =
      Ideal.span
        ({N13SpecialInfinityChart.tClass -
            algebraMap K[X]
              N13SpecialDivisorCharts.SpecialInfinity (C a)} :
          Set N13SpecialDivisorCharts.SpecialInfinity) := by
  rcases
      N13GoodModelTwo.fixedTwo_eq_zero_or_one
        a (ZMod.pow_card a) with rfl | rfl
  · rw [constantInfinityFibreDivisor,
      if_pos rfl, canonicalInfinityDivisor_infinityIdeal]
    congr 2
    simp
  · rw [constantInfinityFibreDivisor,
      if_neg one_ne_zero,
      canonicalDivisor_infinityIdeal]
    simp

end

end MazurProof.N13SpecialVerticalDivisorCharts


