-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialConstantInfinityVerticalGraph_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialConstantInfinityVerticalGraph_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:26:15.092765+00:00
-- url     : https://prove2.me/theorems/4285a5c1-68e4-4b89-86a4-b809d6ac9755
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialConstantInfinityVerticalGraph source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialConstantInfinityVerticalGraph

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialConstantInfinityVerticalGraph
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialVerticalDivisorCharts_p0

set_option autoImplicit false




/-!
# Constant vertical graphs on the special infinity chart

When a vertical relation specializes to the constant equation `t = a`, its
monic quadratic ordinate equation is forced by the special curve equation
to be `v²+v`.  Thus the vertical graph ideal is just the principal fibre
ideal `(t-a)`, and its divisor is the canonical pair of the two sheets over
that base point.  This calculation treats both `t=0` and `t=1` uniformly.
-/

open Polynomial

namespace MazurProof.N13SpecialConstantInfinityVerticalGraph

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The special residue field. -/
abbrev K := N13SpecialInfinityChart.K

/-- The special infinity coordinate ring. -/
abbrev Ring := N13SpecialDivisorCharts.SpecialInfinity

/-- Substitute an infinity-coordinate polynomial into the special curve
while retaining `v` as the polynomial variable. -/
def verticalCurve (s : K[X]) : K[X] :=
  X ^ 2 +
    N13SpecialInfinityChart.hPoly.comp s * X -
    N13SpecialInfinityChart.rhsPoly.comp s

/-- The vertical graph ideal `(m(v),t-a)` on the special infinity chart. -/
def verticalIdeal (m : K[X]) (a : K) : Ideal Ring :=
  Ideal.span
    ({aeval N13SpecialInfinityChart.vClass m,
      N13SpecialInfinityChart.tClass -
        algebraMap K[X] Ring (C a)} : Set Ring)

/-- Substitution of either constant `F₂` coordinate into the special
infinity equation leaves the sheet polynomial `v²+v`. -/
theorem verticalCurve_C (a : K) :
    verticalCurve (C a) = X ^ 2 + X := by
  rcases
      N13GoodModelTwo.fixedTwo_eq_zero_or_one
        a (ZMod.pow_card a) with rfl | rfl
  · unfold verticalCurve
    simp [N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly]
  · unfold verticalCurve
    simp [N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly]
    have htwo : (2 : K[X]) = 0 :=
      CharP.cast_eq_zero (K[X]) 2
    linear_combination X * htwo - htwo

/-- A monic quadratic factor of `v²+v` is the full polynomial `v²+v`. -/
theorem monicQuadratic_eq_X_sq_add_X
    (m w : K[X])
    (hm : m.Monic)
    (hdeg : m.natDegree = 2)
    (hcurve : X ^ 2 + X = m * w) :
    m = X ^ 2 + X := by
  have htargetMonic : (X ^ 2 + X : K[X]).Monic := by
    apply monic_X_pow_add
    rw [degree_X]
    norm_num
  have htargetDegree : (X ^ 2 + X : K[X]).natDegree = 2 := by
    compute_degree
    norm_num
  have hmDegree : m.IsMonicOfDegree 2 :=
    ⟨hdeg, hm⟩
  have hprodDegree : (m * w).IsMonicOfDegree (2 + 0) := by
    rw [← hcurve]
    exact ⟨by simpa using htargetDegree, htargetMonic⟩
  have hwDegree : w.IsMonicOfDegree 0 :=
    hmDegree.of_mul_left hprodDegree
  have hw : w = 1 :=
    eq_one_of_monic_natDegree_zero
      hwDegree.monic hwDegree.natDegree_eq
  rw [hw, mul_one] at hcurve
  exact hcurve.symm

/-- A constant vertical quadratic graph cuts out exactly the principal
base-fibre ideal `(t-a)`. -/
theorem verticalIdeal_eq_span
    (m w : K[X])
    (a : K)
    (hm : m.Monic)
    (hdeg : m.natDegree = 2)
    (hcurve : verticalCurve (C a) = m * w) :
    verticalIdeal m a =
      Ideal.span
        ({N13SpecialInfinityChart.tClass -
            algebraMap K[X] Ring (C a)} : Set Ring) := by
  have hmShape : m = X ^ 2 + X := by
    apply monicQuadratic_eq_X_sq_add_X m w hm hdeg
    rw [← hcurve, verticalCurve_C]
  let xClassHom : K[X] →+* Ring :=
    AdjoinRoot.of N13SpecialInfinityChart.curvePoly
  let p : K[X] := X - C a
  let J : Ideal Ring :=
    Ideal.span ({xClassHom p} : Set Ring)
  have hpJ : xClassHom p ∈ J :=
    Ideal.subset_span (by simp)
  have hhEval :
      N13SpecialInfinityChart.hPoly.eval a = 1 := by
    simp only [N13SpecialInfinityChart.hPoly, eval_add,
      eval_one, eval_pow, eval_X]
    fin_cases a <;> decide
  have hrhsEval :
      N13SpecialInfinityChart.rhsPoly.eval a = 0 := by
    simp only [N13SpecialInfinityChart.rhsPoly,
      eval_add, eval_X, eval_pow]
    fin_cases a <;> decide
  have hhdiv :
      p ∣ N13SpecialInfinityChart.hPoly - C 1 := by
    simpa [p, hhEval] using
      (X_sub_C_dvd_sub_C_eval
        (p := N13SpecialInfinityChart.hPoly) (a := a))
  have hrhsdiv :
      p ∣ N13SpecialInfinityChart.rhsPoly := by
    simpa [p, hrhsEval] using
      (X_sub_C_dvd_sub_C_eval
        (p := N13SpecialInfinityChart.rhsPoly) (a := a))
  have hhJ :
      xClassHom (N13SpecialInfinityChart.hPoly - C 1) ∈ J := by
    obtain ⟨q, hq⟩ := hhdiv
    rw [hq, map_mul]
    exact Ideal.mul_mem_right (xClassHom q) J hpJ
  have hrhsJ :
      xClassHom N13SpecialInfinityChart.rhsPoly ∈ J := by
    obtain ⟨q, hq⟩ := hrhsdiv
    rw [hq, map_mul]
    exact Ideal.mul_mem_right (xClassHom q) J hpJ
  have hvvJ :
      N13SpecialInfinityChart.vClass ^ 2 +
          N13SpecialInfinityChart.vClass ∈ J := by
    have hdelta :=
      Ideal.mul_mem_right N13SpecialInfinityChart.vClass J hhJ
    have hmem := Ideal.sub_mem J hrhsJ hdelta
    have hrel :=
      N13SpecialVerticalDivisorCharts.infinity_yClass_relation
    change
      N13SpecialInfinityChart.vClass ^ 2 +
          xClassHom N13SpecialInfinityChart.hPoly *
            N13SpecialInfinityChart.vClass =
        xClassHom N13SpecialInfinityChart.rhsPoly at hrel
    convert hmem using 1
    change
      N13SpecialInfinityChart.vClass ^ 2 +
          N13SpecialInfinityChart.vClass =
        xClassHom N13SpecialInfinityChart.rhsPoly -
          xClassHom
              (N13SpecialInfinityChart.hPoly - C 1) *
            N13SpecialInfinityChart.vClass
    simp only [map_sub]
    have hOne : xClassHom (C (1 : K)) = 1 := rfl
    rw [hOne]
    linear_combination hrel
  have hpClass :
      xClassHom p =
        N13SpecialInfinityChart.tClass -
          algebraMap K[X] Ring (C a) := by
    simp [xClassHom, p, N13SpecialInfinityChart.tClass]
  rw [verticalIdeal]
  rw [← hpClass]
  change
    Ideal.span
        ({aeval N13SpecialInfinityChart.vClass m,
          xClassHom p} : Set Ring) =
      J
  rw [hmShape]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · simpa using hvvJ
    · exact hpJ
  · apply Ideal.span_mono
    simp

end

end MazurProof.N13SpecialConstantInfinityVerticalGraph


