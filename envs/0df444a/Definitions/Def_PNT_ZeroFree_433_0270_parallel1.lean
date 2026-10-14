-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0270_parallel1
-- name    : PNT_ZeroFree_433_0270_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:27:19.319021+00:00
-- url     : https://prove2.me/theorems/82fd7906-50ae-4621-8cd7-b0a2a8dac687
-- title:
--   Zero-free region foundations: Eisenstein.FullFrequencyExpansion [0270_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.FullFrequencyExpansion
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/FullFrequencyExpansion.lean#L205-L592

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0147_parallel1
import Definitions.Def_PNT_ZeroFree_433_0151_parallel2
import Definitions.Def_PNT_ZeroFree_433_0155_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel2
import Definitions.Def_PNT_ZeroFree_433_0241

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/FullFrequencyExpansion.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical


section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups


section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma coefficient_weighted_summable_of_polynomial (F:Eis→ℂ) (C:ℝ) (hC:0≤C)
    (hF:∀h:Eis,h≠0→‖F h‖≤C*‖eisEmbedding h‖^(1/3:ℝ)) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else ‖F h‖*‖cuspFrequency h‖^(-4:ℝ)) := by
  let D:ℝ:=‖(3:ℂ)*eisLam‖
  have hD:0<D:=norm_pos_iff.mpr (mul_ne_zero (by norm_num) eisLam_ne_zero)
  have hDp:0<D^(-4:ℝ):=Real.rpow_pos_of_pos hD _
  have hs:Summable (fun h:Eis=>(C/D^(-4:ℝ))*‖eisEmbedding h‖^(-(11/3):ℝ)):=
    (summable_embedding_rpow (-(11/3):ℝ) (by norm_num)).mul_left _
  apply Summable.of_nonneg_of_le (fun h=>by split_ifs <;> positivity) _ hs
  intro h
  split_ifs with hh
  · exact mul_nonneg (div_nonneg hC hDp.le) (Real.rpow_nonneg (norm_nonneg _) _)
  · have hx:0<‖eisEmbedding h‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hh)
    have he:‖eisEmbedding h‖^(1/3:ℝ)*‖eisEmbedding h‖^(-4:ℝ)=
        ‖eisEmbedding h‖^(-(11/3):ℝ):=by
      rw [←Real.rpow_add hx]
      congr 1
      norm_num
    calc
      _≤(C*‖eisEmbedding h‖^(1/3:ℝ))*‖cuspFrequency h‖^(-4:ℝ):=
        mul_le_mul_of_nonneg_right (hF h hh) (Real.rpow_nonneg (norm_nonneg _) _)
      _=(C/D^(-4:ℝ))*(‖eisEmbedding h‖^(1/3:ℝ)*‖eisEmbedding h‖^(-4:ℝ)):=by
        rw [cuspFrequency,norm_div,Real.div_rpow (norm_nonneg _) (norm_nonneg _)]
        change (C*‖eisEmbedding h‖^(1/3:ℝ))*(‖eisEmbedding h‖^(-4:ℝ)/D^(-4:ℝ))=_
        ring
      _=_:=by rw [he]


lemma derivative_coefficient_weighted_summable (F:Eis→ℂ) (A:ℂ)
    (hF:Summable (fun h:Eis=>if h=0 then (0:ℝ) else ‖F h‖*‖cuspFrequency h‖^(-4:ℝ))) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (F h)‖*‖cuspFrequency h‖^(-5:ℝ)) := by
  apply (hF.mul_left ‖A‖).congr
  intro h
  split_ifs with hh
  · simp
  · have hx:0<‖cuspFrequency h‖:=norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
    have hp:‖cuspFrequency h‖*‖cuspFrequency h‖^(-5:ℝ)=‖cuspFrequency h‖^(-4:ℝ):=by
      conv_lhs => lhs; rw [←Real.rpow_one ‖cuspFrequency h‖]
      rw [←Real.rpow_add hx]
      norm_num
    rw [norm_mul,norm_mul,norm_star]
    calc
      _=‖A‖*‖F h‖*(‖cuspFrequency h‖*‖cuspFrequency h‖^(-5:ℝ)):=by rw [hp];ring
      _=_:=by ring


end

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma radial_inverse_weight (x:ℝ) (hx:0<x) :
    (x^2)^(-(3/2):ℝ)/x^2=x^(-5:ℝ) := by
  calc
    _=(x^2)^(-(3/2):ℝ)*(x^2)^(-1:ℝ):=by rw [Real.rpow_neg_one];rfl
    _=(x^2)^(-(5/2):ℝ):=by
      rw [←Real.rpow_add (sq_pos_of_pos hx)]
      congr 1
      norm_num
    _=x^(-5:ℝ):=by
      rw [←Real.rpow_natCast_mul hx.le]
      congr 1
      norm_num

lemma radialCoefficient_weighted_summable_of_fourth (F:Eis→ℂ) (A:ℂ)
    (hF:Summable (fun h:Eis=>if h=0 then (0:ℝ) else ‖F h‖*‖cuspFrequency h‖^(-4:ℝ))) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (F h)/((‖eisEmbedding h‖^2:ℝ):ℂ)‖*
        (‖eisEmbedding h‖^2)^(-(3/2):ℝ)) := by
  let D:ℝ:=‖(3:ℂ)*eisLam‖
  have hD:0<D:=norm_pos_iff.mpr (mul_ne_zero (by norm_num) eisLam_ne_zero)
  have hDp:D^(-5:ℝ)≠0:=(Real.rpow_pos_of_pos hD _).ne'
  apply ((derivative_coefficient_weighted_summable F A hF).mul_left (D^(-5:ℝ))).congr
  intro h
  split_ifs with hh
  · simp
  · have hx:0<‖eisEmbedding h‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hh)
    have hf:‖cuspFrequency h‖=‖eisEmbedding h‖/D:=by rw [cuspFrequency,norm_div]
    have hw:D^(-5:ℝ)*(‖eisEmbedding h‖/D)^(-5:ℝ)=‖eisEmbedding h‖^(-5:ℝ):=by
      rw [Real.div_rpow hx.le hD.le]
      field_simp [hDp]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    calc
      _=‖A*cuspFrequency h*star (F h)‖*(D^(-5:ℝ)*(‖eisEmbedding h‖/D)^(-5:ℝ)):=by rw [hf];ring
      _=‖A*cuspFrequency h*star (F h)‖*‖eisEmbedding h‖^(-5:ℝ):=by rw [hw]
      _=_:=by rw [←radial_inverse_weight _ hx];ring


end

open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O


end


open scoped Classical MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def fixedCuspReduction : SL(2,Eis) →* SL(2,Eis⧸Ideal.span {(3:Eis)}) :=
  Matrix.SpecialLinearGroup.map (n:=Fin 2) (Ideal.Quotient.mk (Ideal.span {(3:Eis)}))

abbrev FixedCuspSector := fixedCuspReduction.range

instance p2mAnonymous_PNT_ZeroFree_433_0270_parallel1_1 : Finite FixedCuspSector := by
  let : Finite (Eis⧸Ideal.span {(3:Eis)}) := finite_quotient_span (by norm_num : (3:Eis)≠0)
  infer_instance

def fixedCuspSector (M : SL(2,Eis)) : FixedCuspSector :=
  ⟨fixedCuspReduction M,⟨M,rfl⟩⟩

def fixedCuspRepresentative (s : FixedCuspSector) : SL(2,Eis) := s.property.choose

lemma fixedCuspRepresentative_reduction (s : FixedCuspSector) :
    fixedCuspReduction (fixedCuspRepresentative s)=s.val := s.property.choose_spec

lemma fixedCusp_difference_levelThree (M : SL(2,Eis)) :
    M*(fixedCuspRepresentative (fixedCuspSector M))⁻¹∈levelThree := by
  change fixedCuspReduction (M*(fixedCuspRepresentative (fixedCuspSector M))⁻¹)=1
  rw [map_mul,map_inv,fixedCuspRepresentative_reduction]
  change fixedCuspReduction M*(fixedCuspReduction M)⁻¹=1
  exact mul_inv_cancel _

theorem exists_fixed_cusp_decomposition :
    ∃(j:FixedCuspSector→Fin 3) (T:FixedCuspSector→SL(2,Eis))
      (G:SL(2,Eis)→levelTwo),
      (∀s,T s 1 0=0 ∧ IsUnit (T s 0 0) ∧ IsUnit (T s 1 1)) ∧
      ∀M:SL(2,Eis),M=(G M:SL(2,Eis))*cuspRepresentative (j (fixedCuspSector M))*
        T (fixedCuspSector M) := by
  have h (s:FixedCuspSector) := three_cusp_decomposition (fixedCuspRepresentative s)
  choose G0 j T hT hT0 hT1 he using h
  let D : SL(2,Eis)→levelTwo := fun M=>
    ⟨M*(fixedCuspRepresentative (fixedCuspSector M))⁻¹,
      levelThree_le_levelTwo (fixedCusp_difference_levelThree M)⟩
  refine ⟨j,T,fun M=>D M*G0 (fixedCuspSector M),fun s=>⟨hT s,hT0 s,hT1 s⟩,?_⟩
  intro M
  change M=(M*(fixedCuspRepresentative (fixedCuspSector M))⁻¹)*
    (G0 (fixedCuspSector M):SL(2,Eis))*cuspRepresentative (j (fixedCuspSector M))*T (fixedCuspSector M)
  rw [he (fixedCuspSector M)]
  group

end CubicEisenstein

end

end OAI

end


