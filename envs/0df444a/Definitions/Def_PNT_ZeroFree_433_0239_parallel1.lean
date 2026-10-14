-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0239_parallel1
-- name    : PNT_ZeroFree_433_0239_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:10:15.225661+00:00
-- url     : https://prove2.me/theorems/b5789846-8a1a-49ed-b24e-ba9173f942a2
-- title:
--   Zero-free region foundations: Eisenstein.ConjugateCuspProfiles [0239_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.ConjugateCuspProfiles
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ConjugateCuspProfiles.lean#L6-L613

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0068_1
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0076
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0104
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0154_parallel1
import Definitions.Def_PNT_ZeroFree_433_0183_parallel1
import Definitions.Def_PNT_ZeroFree_433_0197_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0219_parallel1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel1
import Definitions.Def_PNT_ZeroFree_433_0234_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0237_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ConjugateCuspProfiles.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace RSLocal

@[simp] theorem int_toNat_two : Int.toNat (2 : ℤ) = 2 := by decide

end RSLocal

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
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cubicBesselIntegralDeriv_continuousAt (x : ℝ) (hx : 0<x) :
    ContinuousAt (fun y : ℝ=>∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv y t) x := by
  let delta := x/2
  have hdelta : 0<delta := half_pos hx
  apply continuousAt_of_dominated («μ» := volume.restrict (Set.Ioi (0:ℝ)))
    (bound:=fun t : ℝ=>(4/delta)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)))
  · exact Eventually.of_forall (fun y=>by unfold cubicBesselDensityDeriv cubicBesselDensity;fun_prop)
  · filter_upwards [Ioi_mem_nhds (show delta<x by dsimp [delta];linarith)] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hyp : 0<y := hdelta.trans hy
    have htp : 0<t := ht
    calc
      _ ≤ (4/delta)*Real.exp (-y/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) :=
        cubicBesselDensityDeriv_bound delta y t hdelta hy.le ht
      _ ≤ _ := by
        have he : Real.exp (-y/2)≤1 := Real.exp_le_one_iff.mpr (by linarith)
        calc
          _ ≤ (4/delta)*1*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by gcongr
          _ = _ := by ring
  · exact cubicBesselDerivativeMajorant_integrable.const_mul (4/delta)
  · exact Eventually.of_forall (fun t=>by unfold cubicBesselDensityDeriv cubicBesselDensity;fun_prop)

lemma schlafliBesselK_cubic_derivative_continuousAt (x : ℝ) (hx : 0<x) :
    ContinuousAt schlafliBesselK_cubic_derivative x := by
  have hp4 : ContinuousAt (fun y : ℝ=>(y/2)^(-(4:ℝ)/3)) x :=
    (continuousAt_id.div_const 2).rpow_const (Or.inl (by positivity))
  have hp1 : ContinuousAt (fun y : ℝ=>(y/2)^(-(1:ℝ)/3)) x :=
    (continuousAt_id.div_const 2).rpow_const (Or.inl (by positivity))
  have hI := (cubicBesselIntegral_hasDerivAt x hx).continuousAt
  have hD := cubicBesselIntegralDeriv_continuousAt x hx
  apply Complex.continuous_ofReal.continuousAt.comp
  exact ((continuousAt_const.mul hp4).mul hI).add ((continuousAt_const.mul hp1).mul hD)


end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

def cuspSpatialInput (q : ℝ × ℂ) : SpatialCoordinates := ![q.2.re,q.2.im,q.1]
def cuspSpatialOutput (p : SpatialCoordinates) : ℝ × ℂ := (p 2,spatialHorizontal p)

lemma cuspSpatialInput_contDiff : ContDiff ℝ 1 cuspSpatialInput := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · change ContDiff ℝ 1 (fun q : ℝ × ℂ=>q.2.re)
    exact Complex.reCLM.contDiff.comp contDiff_snd
  · change ContDiff ℝ 1 (fun q : ℝ × ℂ=>q.2.im)
    exact Complex.imCLM.contDiff.comp contDiff_snd
  · change ContDiff ℝ 1 (fun q : ℝ × ℂ=>q.1)
    fun_prop

lemma cuspSpatialOutput_contDiff : ContDiff ℝ 1 cuspSpatialOutput :=
  (contDiff_apply ℝ ℝ 2).prodMk (spatialHorizontal_contDiff.of_le (by simp))

lemma cuspSpatialInput_horizontal (q : ℝ × ℂ) : spatialHorizontal (cuspSpatialInput q)=q.2 :=
  Complex.re_add_im q.2


end

section
open Filter MeasureTheory
open scoped BigOperators Classical

open ActualEisensteinCubic ConcreteTraceCRT CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ninth_trace_character_period (c x : Eis) :
    ShortDraftTrace.breveE ((eisEmbedding c/(9*eisLam))*(9*eisEmbedding x))=1 := by
  have he : (eisEmbedding c/(9*eisLam))*(9*eisEmbedding x)=eisEmbedding (c*x)/eisLam := by
    rw [map_mul]
    ring
  rw [he,breveE_embedding_div_traceLambda]


lemma periodic_integral_zero_of_eigen_translation (f : ℂ→ℂ)
    (hf : ∀x:Eis,∀z,f (z+3*eisEmbedding x)=f z) (b c : ℂ)
    (hc : c≠1) (he : ∀z,f (b+z)=c*f z) :
    (∫z in periodDomain,f z)=0 := by
  have hi := period_integral_translation f hf b
  simp_rw [he] at hi
  rw [integral_const_mul] at hi
  have hzero : (c-1)*(∫z in periodDomain,f z)=0 := by linear_combination hi
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hc)


end

open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

abbrev UnitLowerData := Σa:PrimaryLower,{d:PrimaryLower//IsCoprime a.val d.val}

def unitLowerToPrimitive (u : Eisˣ) (p : UnitLowerData) : PrimitiveRow := by
  refine ⟨![(u:Eis)*(p.1.val-p.2.val.val),p.2.val.val],?_,?_,p.2.val.2⟩
  · change IsCoprime ((u:Eis)*(p.1.val-p.2.val.val)) p.2.val.val
    apply (isCoprime_mul_unit_left_left u.isUnit _ _).mpr
    apply IsCoprime.symm
    apply (isCoprime_right_congr_of_dvd p.2.val.val (p.1.val-p.2.val.val) p.1.val
      ⟨-1,by ring⟩).mpr
    exact p.2.2.symm
  · have hd : (3:Eis)∣p.1.val-p.2.val.val := by
      simpa only [sub_sub_sub_cancel_right] using dvd_sub p.1.2 p.2.val.2
    exact hd.mul_left (u:Eis)

lemma unitLowerToPrimitive_bijective (u : Eisˣ) :
    Function.Bijective (unitLowerToPrimitive u) := by
  constructor
  · rintro ⟨a,d,hd⟩ ⟨b,e,he⟩ h
    have hrow := congrArg Subtype.val h
    have hde : d=e := Subtype.ext (congrFun hrow 1)
    subst e
    have hab : a=b := by
      apply Subtype.ext
      have hh := congrFun hrow 0
      change (u:Eis)*(a.val-d.val)=(u:Eis)*(b.val-d.val) at hh
      have hcancel := u.isUnit.mul_left_cancel hh
      linear_combination hcancel
    subst b
    rfl
  · intro r
    let d : PrimaryLower := ⟨r.val 1,r.2.2.2⟩
    let a : PrimaryLower := ⟨(↑u⁻¹:Eis)*r.val 0+r.val 1,by
      have hc := r.2.2.1.mul_left (↑u⁻¹:Eis)
      have hh := dvd_add hc r.2.2.2
      convert! hh using 1 ;ring⟩
    have hcop : IsCoprime a.val d.val := by
      apply IsCoprime.symm
      apply (isCoprime_right_congr_of_dvd d.val a.val ((↑u⁻¹:Eis)*r.val 0)
        ⟨1,by dsimp [a,d];ring⟩).mpr
      exact (isCoprime_mul_unit_left_right u⁻¹.isUnit _ _).mpr r.2.1.symm
    refine ⟨⟨a,d,hcop⟩,Subtype.ext ?_⟩
    funext i
    fin_cases i
    · change (u:Eis)*((↑u⁻¹:Eis)*r.val 0+r.val 1-r.val 1)=r.val 0
      rw [add_sub_cancel_right,←mul_assoc]
      simp
    · rfl

def unitLowerEquiv (u : Eisˣ) : UnitLowerData≃PrimitiveRow :=
  Equiv.ofBijective _ (unitLowerToPrimitive_bijective u)

lemma rowOperator_lowerCusp (t : Eis) (v : Fin 2→ℂ) :
    rowOperator (integralComplexMatrix (lowerCuspMatrix t)) v=
      ![v 0+eisEmbedding t*v 1,v 1] := by
  rw [rowOperator_apply]
  funext i
  simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_two,integralComplexMatrix_apply]
  fin_cases i <;>
    simp [lowerCuspMatrix,mul_comm]

lemma unitLower_row_phase (u : Eisˣ) (p : UnitLowerData) :
    (cosetCharacter (primitiveRowEquiv.symm (unitLowerEquiv u p)))⁻¹=
      eisEmbedding (symbol (u:Eis) p.2.val.val)*
        eisEmbedding (symbol p.2.val.val p.1.val) := by
  rw [inverse_cosetCharacter_eq_row_symbol,primitiveRowEquiv_symm_row]
  change eisEmbedding (symbol ((u:Eis)*(p.1.val-p.2.val.val)) p.2.val.val)=_
  have hh : symbol ((u:Eis)*(p.1.val-p.2.val.val)) p.2.val.val=
      symbol ((u:Eis)*p.1.val) p.2.val.val := by
    exact symbol_congr ⟨-(u:Eis),by ring⟩
  rw [hh,symbol_mul_numerator _ _ _ (primaryLower_primary p.2.val),
    symbol_reciprocity p.1.val p.2.val.val (primaryLower_ne_zero p.1)
      (primaryLower_ne_zero p.2.val) (primaryLower_primary p.1)
        (primaryLower_primary p.2.val),map_mul]

def unitLowerTerm (u : Eisˣ) (z : ℂ) (v : ℝ) (s : ℂ) (a d : Eis) : ℂ :=
  (eisEmbedding (symbol (u:Eis) d)*eisEmbedding (symbol d a))*
    ((v/(‖eisEmbedding ((u:Eis)*a)*z+eisEmbedding d‖^2+
      ‖eisEmbedding ((u:Eis)*a)‖^2*v^2):ℝ):ℂ)^s

lemma unitLower_summand (u : Eisˣ) (z : ℂ) (v : ℝ) (hv : 0<v)
    (s : ℂ) (p : UnitLowerData) :
    summand (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s
      (primitiveRowEquiv.symm (unitLowerEquiv u p))=
      unitLowerTerm u z v s p.1.val p.2.val.val := by
  let r : Fin 2→ℂ := ![eisEmbedding ((u:Eis)*p.1.val),eisEmbedding p.2.val.val]
  have hr : rowOperator (integralComplexMatrix (lowerCuspMatrix (u:Eis)))
      (embeddedRow (primitiveRowEquiv.symm (unitLowerEquiv u p)))=r := by
    rw [embeddedRow, primitiveRowEquiv_symm_row, rowOperator_lowerCusp]
    funext i
    fin_cases i <;>
      simp [unitLowerEquiv, Equiv.ofBijective_apply, unitLowerToPrimitive, r, map_mul, map_sub, mul_sub]
  have hr0 : r≠0 := by
    intro hh
    have he := congrFun hh 1
    exact eisEmbedding_ne_zero (primaryLower_ne_zero p.2.val) he
  have hp := heightDenominator_pos z v hv r hr0
  rw [summand,←rowOperator_mul,hr,rowEnergy_upperSection,unitLower_row_phase]
  change _=(eisEmbedding (symbol (u:Eis) p.2.val.val)*eisEmbedding (symbol p.2.val.val p.1.val))*
    ((v/heightDenominator z v r:ℝ):ℂ)^s
  have hi : ((v/heightDenominator z v r:ℝ):ℂ)=
      (((heightDenominator z v r/v:ℝ):ℂ))⁻¹ := by
    simp only [Complex.ofReal_div,inv_div]
  rw [hi,Complex.inv_cpow_ofReal_nonneg (div_nonneg hp.le hv.le),Complex.cpow_neg]

theorem unitLowerEisenstein_eq_rows (u : Eisˣ) (z : ℂ) (v : ℝ) (hv : 0<v) (s : ℂ) :
    eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s=
      ∑'p:UnitLowerData,unitLowerTerm u z v s p.1.val p.2.val.val := by
  rw [eisenstein,←primitiveRowEquiv.symm.tsum_eq,←(unitLowerEquiv u).tsum_eq]
  exact tsum_congr (unitLower_summand u z v hv s)

end CubicEisenstein

end

end OAI

end


