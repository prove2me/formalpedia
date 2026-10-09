-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialNonconstantInfinityVerticalGraph_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialNonconstantInfinityVerticalGraph_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:44:17.088796+00:00
-- url     : https://prove2.me/theorems/4184ee65-31d3-475f-b823-950ec60d0150
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialNonconstantInfinityVerticalGraph source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialNonconstantInfinityVerticalGraph

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialNonconstantInfinityVerticalGraph
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialInfinityGraphDivisorCharts_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialConstantInfinityVerticalGraph_p0

set_option autoImplicit false




/-!
# Nonconstant vertical graphs on the special infinity chart

In the nonconstant residue branch a vertical relation has the form
`t=a+v`.  Characteristic two makes this affine change of variable
involutive: `v=t+a`.  Consequently the vertical graph

`m(v)=0,  t=a+v`

is the same closed subscheme as the horizontal graph

`m(t+a)=0,  v=t+a`.

This file carries out that change of variables inside the special coordinate
ring and packages the translated equations as the monic horizontal graph data
already handled by the completed-root divisor construction.
-/

open Polynomial

namespace MazurProof.N13SpecialNonconstantInfinityVerticalGraph

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The special residue field. -/
abbrev K :=
  N13SpecialInfinityChart.K

/-- The special infinity coordinate ring. -/
abbrev Ring :=
  N13SpecialDivisorCharts.SpecialInfinity

/-- Translation by the residue coordinate `a`; over `F₂` this translation
is its own inverse. -/
def translate (a : K) (p : K[X]) : K[X] :=
  p.comp (X + C a)

/-- The nonconstant vertical graph ideal `(m(v),t-(a+v))`. -/
def verticalIdeal (m : K[X]) (a : K) : Ideal Ring :=
  Ideal.span
    ({aeval N13SpecialInfinityChart.vClass m,
      N13SpecialInfinityChart.tClass -
        aeval N13SpecialInfinityChart.vClass (C a + X)} :
      Set Ring)

/-- Translation by an `F₂` coordinate is involutive. -/
theorem translateLinear_comp_translateLinear (a : K) :
    (C a + X).comp (X + C a) = X := by
  have haa : a + a = 0 := by
    fin_cases a <;> decide
  simp only [add_comp, C_comp, X_comp]
  calc
    C a + (X + C a) = X + (C a + C a) := by ring
    _ = X := by rw [← C_add, haa]; simp

/-- Translating a vertical factorization through the involution `v=t+a`
gives the horizontal semigraph equation on the infinity chart. -/
theorem translated_curve_eq
    (m w : K[X])
    (a : K)
    (hcurve :
      N13SpecialConstantInfinityVerticalGraph.verticalCurve
          (C a + X) =
        m * w) :
    (X + C a) ^ 2 +
          N13SpecialInfinityChart.hPoly * (X + C a) -
          N13SpecialInfinityChart.rhsPoly =
      translate a m * translate a w := by
  have h :=
    congrArg (fun p : K[X] => p.comp (X + C a)) hcurve
  simp only [N13SpecialConstantInfinityVerticalGraph.verticalCurve,
    pow_comp, add_comp, mul_comp, sub_comp, X_comp] at h
  rw [comp_assoc, translateLinear_comp_translateLinear, comp_X,
    comp_assoc, translateLinear_comp_translateLinear, comp_X] at h
  simpa [translate] using h

/-- The translated vertical equations form monic horizontal graph data.
This is the bridge to the completed-root divisor machinery. -/
def horizontalGraph
    (m w : K[X])
    (a : K)
    (hm : m.Monic)
    (hcurve :
      N13SpecialConstantInfinityVerticalGraph.verticalCurve
          (C a + X) =
        m * w) :
    N13SpecialInfinityGraphDivisor.SemiMumford where
  u := translate a m
  v := X + C a
  w := translate a w
  u_monic := hm.comp_X_add_C a
  curve_eq := translated_curve_eq m w a hcurve

/-- Translation preserves the degree of a monic quadratic. -/
theorem horizontalGraph_u_natDegree
    (m w : K[X])
    (a : K)
    (hm : m.Monic)
    (hdeg : m.natDegree = 2)
    (hcurve :
      N13SpecialConstantInfinityVerticalGraph.verticalCurve
          (C a + X) =
        m * w) :
    (horizontalGraph m w a hm hcurve).u.natDegree = 2 := by
  change (m.comp (X + C a)).natDegree = 2
  rw [Polynomial.natDegree_comp, natDegree_X_add_C, hdeg]

/-- Evaluating a base polynomial at the special class `t` is the canonical
map from the base polynomial ring into the infinity coordinate ring. -/
theorem xClassHom_eq_aeval_tClass (p : K[X]) :
    N13SpecialInfinityGraphDivisorCharts.xClassHom p =
      aeval N13SpecialInfinityChart.tClass p := by
  let ψ : K[X] →ₐ[K] Ring :=
    IsScalarTower.toAlgHom K K[X] Ring
  have h :
      aeval N13SpecialInfinityChart.tClass = ψ := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    rfl
  exact (DFunLike.congr_fun h p).symm

/-- The two linear equations `t=a+v` and `v=t+a` define the same element
of the special coordinate ring. -/
theorem verticalLinear_eq_horizontalLinear (a : K) :
    N13SpecialInfinityChart.tClass -
        aeval N13SpecialInfinityChart.vClass (C a + X) =
      N13SpecialInfinityChart.vClass -
        N13SpecialInfinityGraphDivisorCharts.xClassHom (X + C a) := by
  simp only [map_add, Polynomial.aeval_C, aeval_X]
  rw [xClassHom_eq_aeval_tClass, xClassHom_eq_aeval_tClass]
  simp only [Polynomial.aeval_X, Polynomial.aeval_C]
  have htwoK : (2 : K) = 0 :=
    CharP.cast_eq_zero K 2
  have htwo : (2 : Ring) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (algebraMap K Ring) htwoK
  linear_combination
    (N13SpecialInfinityChart.tClass -
      N13SpecialInfinityChart.vClass) * htwo

/-- After imposing the common linear equation, evaluating `m` at `v`
or at `t+a` gives the same class. -/
theorem verticalPolynomial_sub_horizontalPolynomial_mem
    (m : K[X])
    (a : K) :
    aeval N13SpecialInfinityChart.vClass m -
        N13SpecialInfinityGraphDivisorCharts.xClassHom
          (translate a m) ∈
      Ideal.span
        ({N13SpecialInfinityChart.vClass -
            N13SpecialInfinityGraphDivisorCharts.xClassHom
              (X + C a)} : Set Ring) := by
  let s : Ring :=
    N13SpecialInfinityGraphDivisorCharts.xClassHom (X + C a)
  obtain ⟨q, hq⟩ :=
    sub_dvd_eval_sub N13SpecialInfinityChart.vClass s
      (m.map (algebraMap K Ring))
  have hdiff :
      aeval N13SpecialInfinityChart.vClass m -
          aeval s m =
        (N13SpecialInfinityChart.vClass - s) * q := by
    simpa [Polynomial.aeval_def] using hq
  have hs :
      N13SpecialInfinityGraphDivisorCharts.xClassHom
          (translate a m) =
        aeval s m := by
    rw [xClassHom_eq_aeval_tClass, translate, aeval_comp]
    apply congrArg (fun z : Ring => aeval z m)
    simpa only [s] using
      (xClassHom_eq_aeval_tClass (X + C a)).symm
  change
    aeval N13SpecialInfinityChart.vClass m -
        N13SpecialInfinityGraphDivisorCharts.xClassHom
          (translate a m) ∈
      Ideal.span
        ({N13SpecialInfinityChart.vClass - s} : Set Ring)
  rw [hs, hdiff]
  exact
    Ideal.mul_mem_right q _
      (Ideal.subset_span (by simp))

/-- The nonconstant vertical ideal is literally the horizontal graph ideal
obtained by the involutive translation `v=t+a`. -/
theorem verticalIdeal_eq_graphIdeal
    (m : K[X])
    (a : K) :
    verticalIdeal m a =
      N13SpecialInfinityGraphDivisorCharts.graphIdeal
        (translate a m) (X + C a) := by
  let g : Ring :=
    N13SpecialInfinityChart.vClass -
      N13SpecialInfinityGraphDivisorCharts.xClassHom (X + C a)
  let mV : Ring :=
    aeval N13SpecialInfinityChart.vClass m
  let mT : Ring :=
    N13SpecialInfinityGraphDivisorCharts.xClassHom (translate a m)
  have hlinear := verticalLinear_eq_horizontalLinear a
  have hdiff :
      mV - mT ∈ Ideal.span ({g} : Set Ring) := by
    exact verticalPolynomial_sub_horizontalPolynomial_mem m a
  rw [verticalIdeal,
    N13SpecialInfinityGraphDivisorCharts.graphIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    GeneralizedGraphIdealCore.ySubClass]
  change Ideal.span ({mV, _} : Set Ring) =
    Ideal.span ({mT, g} : Set Ring)
  rw [hlinear]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have hmT :
          mT ∈ Ideal.span ({mT, g} : Set Ring) :=
        Ideal.subset_span (by simp)
      have hdiff' :
          mV - mT ∈ Ideal.span ({mT, g} : Set Ring) :=
        (Ideal.span_mono (by
          intro z hz
          simp only [Set.mem_singleton_iff] at hz
          subst z
          simp [g])) hdiff
      have hadd :=
        Ideal.add_mem (Ideal.span ({mT, g} : Set Ring)) hdiff' hmT
      simpa [g] using hadd
    · exact Ideal.subset_span (by simp [g])
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have hmV :
          mV ∈ Ideal.span ({mV, g} : Set Ring) :=
        Ideal.subset_span (by simp)
      have hdiff' :
          mV - mT ∈ Ideal.span ({mV, g} : Set Ring) :=
        (Ideal.span_mono (by
          intro z hz
          simp only [Set.mem_singleton_iff] at hz
          subst z
          simp [g])) hdiff
      have hsub :=
        Ideal.sub_mem (Ideal.span ({mV, g} : Set Ring)) hmV hdiff'
      simpa [g] using hsub
    · exact Ideal.subset_span (by simp [g])

end

end MazurProof.N13SpecialNonconstantInfinityVerticalGraph


