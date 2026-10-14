-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0266_parallel1
-- name    : PNT_ZeroFree_433_0266_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:24:54.019477+00:00
-- url     : https://prove2.me/theorems/aa400906-4910-4712-9bdb-9d4160ca50da
-- title:
--   Zero-free region foundations: Eisenstein.RamifiedTransform [0266_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.RamifiedTransform
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/RamifiedTransform.lean#L86-L485

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0096
import Definitions.Def_PNT_ZeroFree_433_0147_parallel1
import Definitions.Def_PNT_ZeroFree_433_0151_parallel2
import Definitions.Def_PNT_ZeroFree_433_0155_parallel1
import Definitions.Def_PNT_ZeroFree_433_0220_parallel1
import Definitions.Def_PNT_ZeroFree_433_0237_parallel1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel2
import Definitions.Def_PNT_ZeroFree_433_0260_parallel2_1
import Definitions.Def_PNT_ZeroFree_433_0265_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/RamifiedTransform.lean
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
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance p2mAnonymous_PNT_ZeroFree_433_0266_parallel1_1 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def lowRamifiedTransform (F:Eis→ℂ) (h:Eis) :ℂ :=
  3*F (9*h)+∑u:Eisˣ,∑k:Fin 5,ramifiedRawWeight h u k.val*
    F (h*(9*(u.val*lambda^(k.val+2))))


lemma sourceRayPhase_of_three_dvd (h:Eis) (hh:(3:Eis)∣h) :
    ShortDraftTrace.breveE (cuspFrequency h)=1 := by
  obtain ⟨z,rfl⟩:=hh
  have he:cuspFrequency ((3:Eis)*z)=eisEmbedding z/eisLam:=by
    simp only [cuspFrequency,map_mul,map_ofNat]
    ring
  rw [he]
  exact breveE_embedding_div_traceLambda z


lemma lowRamifiedTransform_sub (F G:Eis→ℂ) (h:Eis) :
    lowRamifiedTransform (fun x=>F x-G x) h=
      lowRamifiedTransform F h-lowRamifiedTransform G h := by
  simp only [lowRamifiedTransform,mul_sub,Finset.sum_sub_distrib]
  ring


end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance p2mAnonymous_PNT_ZeroFree_433_0266_parallel1_2 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

lemma ramifiedFunction_reduce (F:Eis→ℂ) (hneg:∀x,F (-x)=F x)
    (hpow:∀x m,F (x*lambda^m)=F (x*lambda^(m%3))) (n:Eis) (u:Eisˣ) (m:ℕ) :
    ∃j k:Fin 3,F (n*((u:Eis)*lambda^m))=F (n*omega^j.val*lambda^k.val) := by
  obtain ⟨j,hj|hj⟩:=unit_eq_sign_omega u
  · refine ⟨j,⟨m%3,Nat.mod_lt _ (by decide)⟩,?_⟩
    rw [hj,←mul_assoc,hpow]
  · refine ⟨j,⟨m%3,Nat.mod_lt _ (by decide)⟩,?_⟩
    rw [hj,neg_mul,mul_neg,hneg,←mul_assoc,hpow]

lemma ramifiedFunction_family_bound (F:Eis→ℂ) (hneg:∀x,F (-x)=F x)
    (hpow:∀x m,F (x*lambda^m)=F (x*lambda^(m%3))) (n:Eis) (M:ℝ)
    (hM:∀j k:Fin 3,‖F (n*omega^j.val*lambda^k.val)‖≤M) (u:Eisˣ) (m:ℕ) :
    ‖F (n*((u:Eis)*lambda^m))‖≤M := by
  obtain ⟨j,k,hjk⟩:=ramifiedFunction_reduce F hneg hpow n u m
  rw [hjk]
  exact hM j k

lemma ramifiedNine_eq : (9:Eis)=omega*lambda^4 := by
  have hw:omega^2=-omega-1:=by linear_combination ramified_omega_relation
  have hl:lambda^2=-3*omega:=by
    change (omega-1)^2=-3*omega
    linear_combination hw
  calc
    (9:Eis)=9*omega^3:=by rw [omega_primitive.pow_eq_one]; ring
    _=omega*((-3*omega)^2):=by ring
    _=omega*((lambda^2)^2):=by rw [hl]
    _=omega*lambda^4:=by ring


lemma lowRamifiedLeading (F:Eis→ℂ)
    (hpow:∀x m,F (x*lambda^m)=F (x*lambda^(m%3))) (n:Eis) (j k:Fin 3) :
    F (9*(lowRamifiedFrequency ⟨(j.val+2)%3,Nat.mod_lt _ (by decide)⟩ k*n))=
      F (n*omega^j.val*lambda^k.val) := by
  have ho:omega^((j.val+2)%3+1)=omega^j.val:=by
    fin_cases j <;> norm_num [omega_primitive.pow_eq_one]
  have he:9*(lowRamifiedFrequency ⟨(j.val+2)%3,Nat.mod_lt _ (by decide)⟩ k*n)=
      (n*omega^j.val)*lambda^(k.val+6):=by
    simp only [lowRamifiedFrequency,ramifiedNine_eq]
    rw [show k.val+6=4+(k.val+2) by omega,pow_add,←ho,pow_succ]
    ring
  rw [he,hpow,show (k.val+6)%3=k.val by omega]


end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma exists_primary_unit_lambda_factor (h:Eis) (hh:h≠0) :
    ∃n:Eis,∃u:Eisˣ,∃m:ℕ,lambda^2∣n-1 ∧ h=n*((u:Eis)*lambda^m) := by
  obtain ⟨⟨m,J⟩,hm⟩:=lambdaFactorMap_bijective.2
    ⟨Ideal.span {h},Ideal.span_singleton_eq_bot.not.mpr hh⟩
  have hi:ramifiedIdeal^m*J.val=Ideal.span {h}:=congrArg Subtype.val hm
  have hs:Ideal.span {lambda^m*primaryGenerator J.val}=Ideal.span {h}:=by
    rw [lambdaFactor_generator_span,hi]
  obtain ⟨u,hu⟩:=Ideal.span_singleton_eq_span_singleton.mp hs
  refine ⟨primaryGenerator J.val,u,m,(primaryGenerator_spec J.val J.property).2,?_⟩
  linear_combination -hu


end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O


end

section
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def thetaFrequencyScale : ℂ := 1/((3:ℂ)*eisLam)
def thetaBesselScale : ℝ := ‖thetaFrequencyScale‖


lemma thetaFrequencyScale_ne_zero : thetaFrequencyScale≠0 := by
  exact one_div_ne_zero (mul_ne_zero (by norm_num) eisLam_ne_zero)

lemma thetaBesselScale_pos : 0<thetaBesselScale := norm_pos_iff.mpr thetaFrequencyScale_ne_zero

lemma thetaBesselScale_eq : thetaBesselScale=1/Real.sqrt 27 := by
  have hl : ‖eisLam‖^2=(3:ℝ) := by
    have h := congrArg norm TraceLambdaPhase.eisLam_sq
    norm_num only [norm_pow,norm_neg,Complex.norm_ofNat] at h
    exact h
  have hd : ‖(3:ℂ)*eisLam‖=Real.sqrt 27 := by
    rw [norm_mul,Complex.norm_ofNat]
    nlinarith [Real.sq_sqrt (show (0:ℝ)≤27 by norm_num),
      Real.sqrt_nonneg (27:ℝ),norm_nonneg eisLam]
  rw [thetaBesselScale,thetaFrequencyScale,norm_div,norm_one,hd]


lemma cuspFrequency_eq_thetaFrequencyScale (h : Eis) :
    cuspFrequency h=thetaFrequencyScale*eisEmbedding h := by
  unfold cuspFrequency thetaFrequencyScale
  ring

lemma completedCoefficient_mul_length (Ψ : Eis→*ℂ) (I J : NonzeroIdeal)
    (hI : primaryGenerator I.val≠0) (hJ : primaryGenerator J.val≠0)
    (hsq : Squarefree I.val) :
    completedMellinCoefficient Ψ (I,J)*(completedMellinLength (I,J):ℂ)=
      star (eisEmbedding (primaryGenerator I.val*(primaryGenerator J.val)^3))*
        (‖eisEmbedding (primaryGenerator J.val)‖:ℂ)*gaussTwo I.val hI*
        Ψ (primaryGenerator I.val)*(Ψ (primaryGenerator J.val))^3 := by
  have hni : (Ideal.absNorm I.val:ℂ)=(‖eisEmbedding (primaryGenerator I.val)‖:ℂ)^2 := by
    exact_mod_cast (primaryGenerator_norm_sq I.val hI).symm
  have hnj : (Ideal.absNorm J.val:ℂ)=(‖eisEmbedding (primaryGenerator J.val)‖:ℂ)^2 := by
    exact_mod_cast (primaryGenerator_norm_sq J.val hJ).symm
  have hi0 : (‖eisEmbedding (primaryGenerator I.val)‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hI))
  have hj0 : (‖eisEmbedding (primaryGenerator J.val)‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hJ))
  rw [completedMellinCoefficient,columnWeight_eq Ψ I.val hsq hI]
  rw [show cubeWeight Ψ J.val=star (FiniteGaussPhase.angularFactor (primaryGenerator J.val))^3*
    Ψ (primaryGenerator J.val)^3/(Ideal.absNorm J.val:ℂ) from rfl]
  simp only [FiniteGaussPhase.angularFactor,completedMellinLength,
    Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,
    ←primaryGenerator_norm I.val hI,hni,hnj,map_mul,map_pow,star_mul,star_pow,
    Complex.star_def,map_div₀,Complex.conj_ofReal]
  field_simp [hi0,hj0]

lemma thetaPair_frequency_norm (I J : NonzeroIdeal)
    (hI : primaryGenerator I.val≠0) (hJ : primaryGenerator J.val≠0) :
    ‖cuspFrequency (primaryGenerator I.val*(primaryGenerator J.val)^3)‖=
      thetaBesselScale*Real.sqrt (completedMellinLength (I,J)) := by
  rw [cuspFrequency_eq_thetaFrequencyScale,norm_mul,map_mul,map_pow,norm_mul,norm_pow]
  have he : completedMellinLength (I,J)=
      (‖eisEmbedding (primaryGenerator I.val)‖*‖eisEmbedding (primaryGenerator J.val)‖^3)^2 := by
    rw [completedMellinLength,←primaryGenerator_norm_sq I.val hI,←primaryGenerator_norm_sq J.val hJ]
    ring
  rw [he,Real.sqrt_sq (by positivity)]
  rfl


end


end


end CubicEisenstein

end

end OAI

end


