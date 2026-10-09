-- Prove2me | Definitions.Def_OAIHecke78B021
-- name    : OAIHecke78B021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T01:57:42.601896+00:00
-- url     : https://prove2.me/theorems/335fec17-c35f-43ab-90a6-827a1da8a921
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 22 of 29
-- statement:
--   Definitions bundle 22 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B020` of this split, and through them their definitions. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `Eisenstein.RamifiedTransform`, `Eisenstein.EntireMellinProfile`, `Eisenstein.RamifiedValuation`, `Eisenstein.SourceCuspKernels`, `Eisenstein.FullFrequencyExpansion`, `Eisenstein.FixedCuspArrays`, `Cusp.WeylRepresentatives`, `ChineseRemainder.PrimaryCompletions`, `Cusp.ResiduePhases`, `ChineseRemainder.FrequencyLifts`, `RowCompletion.PeriodicRows`, `GaussSum.ReflectionPool`, `Eisenstein.FixedConductor`, `Eisenstein.FixedThetaTwists`, `Descent.MarkedReflection`, `Descent.MarkedStratum`, `Moments.SupportedCorrelation`, `Detector.GramCommonActual`, `Detector.Row`, `Detector.RowInterchange`, `Detector.Physical`, `Detector.LowRow`, `Moments.Support`, `Moments.RowNorm`, `Detector.GramNumerator`, `Detector.GramPrimaryLattice`, `Detector.SpectralSeparation`, `Hecke.RowClosure`, `Moments.SecondDiagonal`, `Moments.FirstFrequency`, `Moments.Partition`, `Moments.SecondTail`, `Moments.SecondLocalization`, `PrimeRows.Ramified`, `PrimeRows.MarkedCoordinates`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B020

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B021

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  Eisenstein.RamifiedTransform
  Eisenstein.EntireMellinProfile
  Eisenstein.RamifiedValuation
  Eisenstein.SourceCuspKernels
  Eisenstein.FullFrequencyExpansion
  Eisenstein.FixedCuspArrays
  Cusp.WeylRepresentatives
  ChineseRemainder.PrimaryCompletions
  Cusp.ResiduePhases
  ChineseRemainder.FrequencyLifts
  RowCompletion.PeriodicRows
  GaussSum.ReflectionPool
  Eisenstein.FixedConductor
  Eisenstein.FixedThetaTwists
  Descent.MarkedReflection
  Descent.MarkedStratum
  Moments.SupportedCorrelation
  Detector.GramCommonActual
  Detector.Row
  Detector.RowInterchange
  Detector.Physical
  Detector.LowRow
  Moments.Support
  Moments.RowNorm
  Detector.GramNumerator
  Detector.GramPrimaryLattice
  Detector.SpectralSeparation
  Hecke.RowClosure
  Moments.SecondDiagonal
  Moments.FirstFrequency
  Moments.Partition
  Moments.SecondTail
  Moments.SecondLocalization
  PrimeRows.Ramified
  PrimeRows.MarkedCoordinates
-/

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
local instance instFintypeUnitsO_7 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def lowRamifiedTransform (F:Eis→ℂ) (h:Eis) :ℂ :=
  3*F (9*h)+∑u:Eisˣ,∑k:Fin 5,ramifiedRawWeight h u k.val*
    F (h*(9*(u.val*lambda^(k.val+2))))

lemma principalArithmeticResidue_low (a r:Fin 3) (n:Eis) (hn:lambda^2∣n-1) :
    principalArithmeticResidue (lowRamifiedFrequency a r*n)=
      (∑u:Eisˣ,∑k:Fin 5,ramifiedRawWeight (lowRamifiedFrequency a r*n) u k.val*
        unramifiedGaussResidue ((lowRamifiedFrequency a r*n)*(9*(u.val*lambda^(k.val+2)))))/
          ((9*Real.sqrt 3/2:ℝ):ℂ) := by
  let h:=lowRamifiedFrequency a r*n
  have hh:h≠0:=mul_ne_zero (lowRamifiedFrequency_ne_zero a r) (primary_ne_zero n hn)
  let N:=max (ramifiedFrequencyBound h+1) 5
  rw [principalArithmeticResidue_eq_sum h hh N (le_max_left _ _)]
  apply congrArg (fun z:ℂ=>z/((9*Real.sqrt 3/2:ℝ):ℂ))
  apply Finset.sum_congr rfl
  intro u hu
  change (∑k∈Finset.range N,principalResidueTerm h u k)=
    ∑k:Fin 5,principalResidueTerm h u k.val
  rw [Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
  intro k hk hk5
  have hz:=lowRamifiedFrequency_primary_vanish a r n hn u k
    (by simpa only [Finset.mem_range,not_lt] using hk5)
  simp only [principalResidueTerm,h,hz,mul_zero,zero_mul]

lemma sourceRayPhase_of_three_dvd (h:Eis) (hh:(3:Eis)∣h) :
    ShortDraftTrace.breveE (cuspFrequency h)=1 := by
  obtain ⟨z,rfl⟩:=hh
  have he:cuspFrequency ((3:Eis)*z)=eisEmbedding z/eisLam:=by
    simp only [cuspFrequency,map_mul,map_ofNat]
    ring
  rw [he]
  exact breveE_embedding_div_traceLambda z

lemma lowRamifiedFrequency_three_dvd (a r:Fin 3) : (3:Eis)∣lowRamifiedFrequency a r := by
  simpa only [lowRamifiedFrequency,←ramifiedOmegaUnit_val,←Units.val_pow_eq_pow_val] using
    ramifiedElement_level (ramifiedOmegaUnit^a.val) (r.val+2) (by omega)

theorem lowRamifiedTransform_actual (a r:Fin 3) (n:Eis) (hn:lambda^2∣n-1) :
    lowRamifiedTransform unramifiedGaussResidue (lowRamifiedFrequency a r*n)=
      (4*((9*Real.sqrt 3/2:ℝ):ℂ))*sourceArithmeticResidue (lowRamifiedFrequency a r*n) := by
  rw [sourceArithmeticResidue,if_pos (sourceRayPhase_of_three_dvd _
    (dvd_mul_of_dvd_left (lowRamifiedFrequency_three_dvd a r) n)),
    principalArithmeticResidue_low a r n hn]
  unfold lowRamifiedTransform
  field_simp [show ((9*Real.sqrt 3/2:ℝ):ℂ)≠0 by exact_mod_cast (show (9*Real.sqrt 3/2:ℝ)≠0 by positivity)]
  ; ring

lemma lowRamifiedTransform_sub (F G:Eis→ℂ) (h:Eis) :
    lowRamifiedTransform (fun x=>F x-G x) h=
      lowRamifiedTransform F h-lowRamifiedTransform G h := by
  simp only [lowRamifiedTransform,mul_sub,Finset.sum_sub_distrib]
  ring

lemma ramifiedRawWeight_frequency_cube (h p:Eis) (hp:lambda^2∣p-1) (u:Eisˣ) (k:ℕ) :
    ramifiedRawWeight (h*p^3) u k=ramifiedRawWeight h u k := by
  rw [ramifiedRawWeight,ramifiedRawWeight,arithmeticResidueSum_frequency_cube h _ p
    (ramifiedElement_ne_zero u (k+2)) (ramifiedElement_level u (k+2) (by omega)) hp
    (ramified_primary_coprime u (k+2) p hp).of_mul_left_right]

lemma lowRamifiedTransform_cube_comp (F:Eis→ℂ) (h p:Eis) (hp:lambda^2∣p-1) :
    lowRamifiedTransform (fun x=>F (x*p^3)) h=lowRamifiedTransform F (h*p^3) := by
  simp only [lowRamifiedTransform,ramifiedRawWeight_frequency_cube h p hp]
  have he:9*h*p^3=9*(h*p^3):=by ring
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  ring_nf

theorem lowRamifiedTransform_cube_difference (p:Eis) (hp:Prime p) (hpp:lambda^2∣p-1)
    (a r:Fin 3) (n:Eis) (hn:lambda^2∣n-1) :
    lowRamifiedTransform (fun x=>unramifiedGaussResidue (x*p^3)-unramifiedGaussResidue x)
      (lowRamifiedFrequency a r*n)=0 := by
  rw [lowRamifiedTransform_sub,lowRamifiedTransform_cube_comp _ _ p hpp]
  have hnp:lambda^2∣n*p^3-1:=primary_mul n (p^3) hn (primary_pow_congruence p hpp 3)
  rw [mul_assoc,lowRamifiedTransform_actual a r (n*p^3) hnp,
    lowRamifiedTransform_actual a r n hn]
  rw [←mul_assoc,sourceArithmeticResidue_prime_cube p hp hpp _
    (mul_ne_zero (lowRamifiedFrequency_ne_zero a r) (primary_ne_zero n hn)),sub_self]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance instFintypeUnitsO_8 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

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

lemma lowRamified_inner_family (a r:Fin 3) (n:Eis) (u:Eisˣ) (k:ℕ) :
    (lowRamifiedFrequency a r*n)*(9*(u.val*lambda^(k+2)))=
      n*((↑(ramifiedOmegaUnit^(a.val+1)*u):Eis)*lambda^(r.val+k+8)) := by
  simp only [lowRamifiedFrequency,ramifiedNine_eq,Units.val_mul,Units.val_pow_eq_pow_val,
    ramifiedOmegaUnit_val]
  rw [show r.val+k+8=(r.val+2)+(4+(k+2)) by omega]
  simp only [pow_add,pow_one]
  ring

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

lemma lowRamified_remainder_bound (F:Eis→ℂ) (hneg:∀x,F (-x)=F x)
    (hpow:∀x m,F (x*lambda^m)=F (x*lambda^(m%3))) (n:Eis) (hn:lambda^2∣n-1)
    (M:ℝ) (hM0:0≤M) (hM:∀j k:Fin 3,‖F (n*omega^j.val*lambda^k.val)‖≤M)
    (a r:Fin 3) :
    ‖∑u:Eisˣ,∑k:Fin 5,ramifiedRawWeight (lowRamifiedFrequency a r*n) u k.val*
      F ((lowRamifiedFrequency a r*n)*(9*(u.val*lambda^(k.val+2))))‖≤(5/3)*M := by
  calc
    _≤∑u:Eisˣ,∑k:Fin 5,‖ramifiedRawWeight (lowRamifiedFrequency a r*n) u k.val*
        F ((lowRamifiedFrequency a r*n)*(9*(u.val*lambda^(k.val+2))))‖:=by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun u hu=>norm_sum_le _ _))
    _≤∑u:Eisˣ,∑k:Fin 5,‖ramifiedRawWeight (lowRamifiedFrequency a r*n) u k.val‖*M:=by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul,lowRamified_inner_family]
      exact mul_le_mul_of_nonneg_left (ramifiedFunction_family_bound F hneg hpow n M hM _ _) (norm_nonneg _)
    _=(∑u:Eisˣ,∑k:Fin 5,‖ramifiedRawWeight (lowRamifiedFrequency a r*n) u k.val‖)*M:=by
      simp only [Finset.sum_mul]
    _≤(5/3)*M:=mul_le_mul_of_nonneg_right (lowRamifiedRawWeight_sum a r n hn) hM0

theorem lowRamifiedTransform_injective (F:Eis→ℂ) (hneg:∀x,F (-x)=F x)
    (hpow:∀x m,F (x*lambda^m)=F (x*lambda^(m%3))) (n:Eis) (hn:lambda^2∣n-1)
    (hz:∀a r:Fin 3,lowRamifiedTransform F (lowRamifiedFrequency a r*n)=0) :
    ∀j k:Fin 3,F (n*omega^j.val*lambda^k.val)=0 := by
  obtain ⟨i,hi,himax⟩:=Finset.exists_max_image (Finset.univ:Finset (Fin 3×Fin 3))
    (fun i=>‖F (n*omega^i.1.val*lambda^i.2.val)‖) Finset.univ_nonempty
  let M:=‖F (n*omega^i.1.val*lambda^i.2.val)‖
  have hM:∀j k:Fin 3,‖F (n*omega^j.val*lambda^k.val)‖≤M:=by
    intro j k
    exact himax (j,k) (Finset.mem_univ _)
  let a:Fin 3:=⟨(i.1.val+2)%3,Nat.mod_lt _ (by decide)⟩
  have hb:=lowRamified_remainder_bound F hneg hpow n hn M (norm_nonneg _) hM a i.2
  have he:=hz a i.2
  unfold lowRamifiedTransform at he
  have hlead:F (9*(lowRamifiedFrequency a i.2*n))=F (n*omega^i.1.val*lambda^i.2.val):=
    lowRamifiedLeading F hpow n i.1 i.2
  rw [hlead] at he
  have hnorm:3*M≤(5/3)*M:=by
    have heq:3*F (n*omega^i.1.val*lambda^i.2.val)=
        -(∑u:Eisˣ,∑k:Fin 5,ramifiedRawWeight (lowRamifiedFrequency a i.2*n) u k.val*
          F ((lowRamifiedFrequency a i.2*n)*(9*(u.val*lambda^(k.val+2))))):=by
      linear_combination he
    have hh:=congrArg norm heq
    rw [norm_mul,Complex.norm_ofNat,norm_neg] at hh
    exact hh.le.trans hb
  have hmzero:M=0:=by have hm0:0≤M:=norm_nonneg _; nlinarith
  intro j k
  exact norm_eq_zero.mp (le_antisymm (hmzero ▸ hM j k) (norm_nonneg _))

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

theorem unramifiedGaussResidue_prime_cube (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) :
    unramifiedGaussResidue (h*p^3)=unramifiedGaussResidue h := by
  by_cases hh:h=0
  · simp only [hh,zero_mul]
  obtain ⟨n,u,m,hn,hfactor⟩:=exists_primary_unit_lambda_factor h hh
  let F:Eis→ℂ:=fun x=>unramifiedGaussResidue (x*p^3)-unramifiedGaussResidue x
  have hneg:∀x,F (-x)=F x:=by
    intro x
    dsimp only [F]
    rw [neg_mul,unramifiedGaussResidue_neg,unramifiedGaussResidue_neg]
  have hpow:∀x k,F (x*lambda^k)=F (x*lambda^(k%3)):=by
    intro x k
    dsimp only [F]
    have h1:unramifiedGaussResidue ((x*lambda^k)*p^3)=
        unramifiedGaussResidue ((x*lambda^(k%3))*p^3):=by
      rw [show (x*lambda^k)*p^3=(x*p^3)*lambda^k by ring,
        show (x*lambda^(k%3))*p^3=(x*p^3)*lambda^(k%3) by ring]
      exact unramifiedGaussResidue_lambda_pow (x*p^3) k
    exact congrArg₂ (fun a b:ℂ=>a-b) h1 (unramifiedGaussResidue_lambda_pow x k)
  have hz:∀j k:Fin 3,F (n*omega^j.val*lambda^k.val)=0:=
    lowRamifiedTransform_injective F hneg hpow n hn
      (fun a r=>lowRamifiedTransform_cube_difference p hp hpp a r n hn)
  obtain ⟨j,k,hjk⟩:=ramifiedFunction_reduce F hneg hpow n u m
  have hF:F h=0:=by rw [hfactor,hjk,hz]
  exact sub_eq_zero.mp hF

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem unramifiedGaussResidue_prime_factor (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    unramifiedGaussResidue (h*p)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))*
        primeCubicGauss p hp hprimary 2 h*unramifiedGaussResidue h := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  have hrec:=unramifiedGaussResidue_prime_recurrence p hp hprimary h hph
  rw [unramifiedGaussResidue_prime_cube p hp hprimary h] at hrec
  have hrel:(Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*
      primeCubicGauss p hp hprimary 1 h*unramifiedGaussResidue (h*p)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*unramifiedGaussResidue h:=by
    linear_combination hrec
  have hG:=primeCubicGauss_one_mul_two p hp hprimary h hph
  let q:ℂ:=(Ideal.absNorm (Ideal.span {p}):ℂ)
  have hq:q≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hpower:q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q^2=1:=by
    rw [←Complex.cpow_add _ _ hq,←Complex.cpow_natCast q 2,
      ←Complex.cpow_add _ _ hq]
    norm_num
  calc
    unramifiedGaussResidue (h*p)=
        (q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q^2)*unramifiedGaussResidue (h*p):=by rw [hpower,one_mul]
    _=q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 h*
        (q^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 h*unramifiedGaussResidue (h*p)):=by
      calc
        _=q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q*
          (primeCubicGauss p hp hprimary 1 h*primeCubicGauss p hp hprimary 2 h)*
          unramifiedGaussResidue (h*p):=by rw [hG];ring
        _=_:=by ring
    _=q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 h*(q⁻¹*unramifiedGaussResidue h):=by rw [hrel]
    _=_:=by
      change q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 h*(q⁻¹*unramifiedGaussResidue h)=
        q^(-(2/3:ℂ))*primeCubicGauss p hp hprimary 2 h*unramifiedGaussResidue h
      field_simp [hq]

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
def thetaDerivativeScalar : ℂ :=
  (-2*Real.pi*Complex.I)*star thetaFrequencyScale*infinityCoefficientScalar

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def thetaTwistedSource (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (v : ℝ) (hv : 0<v) (z : ℂ) : ℂ :=
  traceTwistedConjugateSource c hc (fixedThetaQuotient Ψ c) v hv z

end

open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def thetaTwistedCuspProfile (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (v : ℝ) : ℂ :=
  ∑h:Eis⧸Ideal.span {c},finiteAdditiveFourierCoeff (quotientTrace c hc)
    (fixedThetaQuotient Ψ c) h*cuspBarProfile cubicSourceConjugateFunction (thetaFourierTranslation c h) v

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def unramifiedResidualCoefficient (h:Eis) :ℂ:=cubicBesselNormalizer h*unramifiedGaussResidue h

lemma primeCubicGauss_two_norm (p:Eis) (hp:Prime p) (hpp:lambda^2∣p-1)
    (h:Eis) (hph:¬p∣h) : ‖primeCubicGauss p hp hpp 2 h‖=‖eisEmbedding p‖ := by
  have he:=congrArg norm (primeCubicGauss_one_mul_two p hp hpp h hph)
  rw [norm_mul,primeCubicGauss_two_eq_star,norm_star,Complex.norm_natCast] at he
  have hn:=eisEmbedding_norm_sq_eq_absNorm_span p
  have hg:0≤‖primeCubicGauss p hp hpp 1 h‖:=norm_nonneg _
  have hr:0≤‖eisEmbedding p‖:=norm_nonneg _
  rw [primeCubicGauss_two_eq_star,norm_star]
  nlinarith

lemma unramifiedResidualCoefficient_prime_factor (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    unramifiedResidualCoefficient (h*p)=
      (primeCubicGauss p hp hpp 2 h/(‖eisEmbedding p‖:ℂ))*unramifiedResidualCoefficient h := by
  rw [unramifiedResidualCoefficient,cubicBesselNormalizer_mul,
    unramifiedGaussResidue_prime_factor p hp hpp h hph,unramifiedResidualCoefficient]
  calc
    _=((‖eisEmbedding p‖:ℂ)^(1/3:ℂ)*(Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ)))*
      primeCubicGauss p hp hpp 2 h*(cubicBesselNormalizer h*unramifiedGaussResidue h):=by ring
    _=_:=by rw [prime_normalizer_powers p hp.ne_zero]; ring

lemma unramifiedResidualCoefficient_prime_norm (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    ‖unramifiedResidualCoefficient (h*p)‖=‖unramifiedResidualCoefficient h‖ := by
  rw [unramifiedResidualCoefficient_prime_factor p hp hpp h hph,norm_mul,norm_div,
    primeCubicGauss_two_norm p hp hpp h hph,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp.ne_zero)),one_mul]

theorem unramifiedGaussResidue_primary_cube (b:Eis) (hb:b≠0)
    (hbp:lambda^2∣b-1) (h:Eis) :
    unramifiedGaussResidue (h*b^3)=unramifiedGaussResidue h := by
  obtain ⟨s,hs,hpr⟩:=exists_primary_prime_factorization b hb hbp
  rw [←hs]
  clear hs hb hbp b
  induction s using Multiset.induction_on generalizing h with
  | empty=>simp
  | @cons p s ih=>
    have hp:=hpr p (Multiset.mem_cons_self _ _)
    have hs:∀q∈s,Prime q∧lambda^2∣q-1:=fun q hq=>hpr q (Multiset.mem_cons_of_mem hq)
    rw [Multiset.prod_cons,show h*(p*s.prod)^3=(h*s.prod^3)*p^3 by ring,
      unramifiedGaussResidue_prime_cube p hp.1 hp.2]
    exact ih h hs

lemma unramifiedResidualCoefficient_primary_cube (b:Eis) (hb:b≠0)
    (hbp:lambda^2∣b-1) (h:Eis) :
    unramifiedResidualCoefficient (h*b^3)=
      (‖eisEmbedding b‖:ℂ)*unramifiedResidualCoefficient h := by
  rw [unramifiedResidualCoefficient,cubicBesselNormalizer_mul_cube h b hb,
    unramifiedGaussResidue_primary_cube b hb hbp h,unramifiedResidualCoefficient]
  ring

theorem unramifiedResidualCoefficient_prime_product_norm {ι:Type*}
    (s:Finset ι) (p:ι→Eis) (hp:∀i∈s,Prime (p i))
    (hprimary:∀i∈s,lambda^2∣p i-1)
    (hpair:∀i∈s,∀j∈s,i≠j→IsCoprime (p i) (p j))
    (h:Eis) (hph:∀i∈s,¬p i∣h) :
    ‖unramifiedResidualCoefficient (h*(∏i∈s,p i))‖=‖unramifiedResidualCoefficient h‖ := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s hi ih=>
    have hpi:=hp i (Finset.mem_insert_self _ _)
    have hpri:=hprimary i (Finset.mem_insert_self _ _)
    have hps:∀j∈s,Prime (p j):=fun j hj=>hp j (Finset.mem_insert_of_mem hj)
    have hprs:∀j∈s,lambda^2∣p j-1:=fun j hj=>hprimary j (Finset.mem_insert_of_mem hj)
    have hcpi:IsCoprime (p i) (∏j∈s,p j):=IsCoprime.prod_right (fun j hj=>
      hpair i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (by intro he;subst j;exact hi hj))
    have hpb:¬p i∣h*(∏j∈s,p j):=by
      intro hd
      rcases hpi.dvd_mul.mp hd with hd|hd
      · exact hph i (Finset.mem_insert_self _ _) hd
      · exact hpi.not_isUnit (hcpi.isUnit_of_dvd hd)
    rw [Finset.prod_insert hi,show h*(p i*(∏j∈s,p j))=(h*(∏j∈s,p j))*p i by ring,
      unramifiedResidualCoefficient_prime_norm (p i) hpi hpri _ hpb]
    exact ih hps hprs (fun j hj k hk hjk=>hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
      (fun j hj=>hph j (Finset.mem_insert_of_mem hj))

theorem unramifiedResidualCoefficient_squarefree_cube_norm (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) (hsq:Squarefree I)
    (u:Eisˣ) (m:ℕ) :
    ‖unramifiedResidualCoefficient ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖=
      ‖eisEmbedding (primaryGenerator J)‖*‖unramifiedResidualCoefficient (u.val*lambda^m)‖ := by
  rw [unramifiedResidualCoefficient_primary_cube _ hJ (primaryGenerator_spec J hJ).2,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  congr 1
  rw [primaryGenerator_squarefree_support I hI hsq]
  apply unramifiedResidualCoefficient_prime_product_norm
  · exact fun P hP=>primaryPrime_isPrime_of_mem I P hI hP
  · exact fun P hP=>(primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
  · exact primaryPrime_support_coprime I hI
  · intro P hP hd
    have hp:=primaryPrime_isPrime_of_mem I P hI hP
    have hpp:lambda^2∣primaryPrime P-1:=
      (primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
    have hc:IsCoprime (u.val*lambda^m) (primaryPrime P):=
      (ramified_primary_coprime u m _ hpp).of_mul_left_right
    exact hp.not_isUnit (hc.symm.isUnit_of_dvd hd)

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def threeRamifiedUnit :Eisˣ:=-(ramifiedOmegaUnit^2)
def traceRamifiedUnit :Eisˣ:=-ramifiedOmegaUnit

lemma three_eq_ramifiedUnit : (3:Eis)=(threeRamifiedUnit:Eis)*lambda^2 := by
  have hw:omega^2=-omega-1:=by linear_combination ramified_omega_relation
  have hl:lambda^2=-3*omega:=by
    change (omega-1)^2=-3*omega
    linear_combination hw
  simp only [threeRamifiedUnit,Units.val_neg,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,hl]
  calc
    (3:Eis)=3*omega^3:=by rw [omega_primitive.pow_eq_one]; ring
    _=_:=by ring

lemma trace_eq_ramifiedUnit : ramifiedTraceLambda=(traceRamifiedUnit:Eis)*lambda := by
  have hw:=ramified_omega_relation
  simp only [traceRamifiedUnit,Units.val_neg,ramifiedOmegaUnit_val]
  change 1+2*omega=-omega*(omega-1)
  linear_combination hw

def ramifiedSixUnit (side:Bool) :RamifiedSixBranch→Eisˣ
  | .inl _=>threeRamifiedUnit*ramifiedCuspRoot side
  | .inr (.inl _)=>threeRamifiedUnit*(-ramifiedCuspRoot side)⁻¹^4*(-ramifiedCuspRoot side)
  | .inr (.inr (.inl _))=>threeRamifiedUnit*(-ramifiedCuspRoot side)⁻¹^4
  | .inr (.inr (.inr j))=>threeRamifiedUnit*(-ramifiedCuspRoot side)⁻¹^4*
      ramifiedCuspScaleUnit side*traceRamifiedUnit*ramifiedOmegaUnit^j.val

def ramifiedSixPower :RamifiedSixBranch→ℕ
  | .inl _=>2
  | .inr (.inl _)=>2
  | .inr (.inr (.inl _))=>2
  | .inr (.inr (.inr _))=>3

lemma ramifiedSixPower_bounds (i:RamifiedSixBranch) : 2≤ ramifiedSixPower i ∧ ramifiedSixPower i≤3 := by
  rcases i with i|i
  · norm_num [ramifiedSixPower]
  rcases i with i|i
  · norm_num [ramifiedSixPower]
  rcases i with i|i <;> norm_num [ramifiedSixPower]

lemma unitCuspUnramifiedIndex_multiplier (u t:Eisˣ) (h:Eis) :
    unitCuspUnramifiedIndex u t h=(3*(↑u⁻¹:Eis)^4*(t:Eis))*h := by
  unfold unitCuspUnramifiedIndex
  have ht:(t:Eis)*(↑t⁻¹:Eis)=1:=by simp
  calc
    _=(3*(↑u⁻¹:Eis)^4*(t:Eis)*h)*((t:Eis)*(↑t⁻¹:Eis)):=by ring
    _=_:=by rw [ht,mul_one]

theorem ramifiedSixIndex_multiplier (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) (i:RamifiedSixBranch) :
    ramifiedSixIndex side h hf i=
      ((ramifiedSixUnit side i:Eis)*lambda^(ramifiedSixPower i))*h := by
  rcases i with i|i
  · simp only [ramifiedSixIndex,unitCuspUnramifiedIndex_multiplier,
      ramifiedSixUnit,ramifiedSixPower,Units.val_mul,Units.val_one,inv_one,one_pow]
    rw [three_eq_ramifiedUnit]
    ring
  rcases i with i|i
  · simp only [ramifiedSixIndex,unitCuspUnramifiedIndex_multiplier,
      ramifiedSixUnit,ramifiedSixPower,Units.val_mul,Units.val_pow_eq_pow_val]
    rw [three_eq_ramifiedUnit]
    ring
  rcases i with i|j
  · simp only [ramifiedSixIndex,unitCuspUnramifiedIndex_multiplier,
      ramifiedSixUnit,ramifiedSixPower,Units.val_mul,Units.val_pow_eq_pow_val,Units.val_one,mul_one]
    rw [three_eq_ramifiedUnit]
    ring
  · have hh:=onceCuspFrequencyQuotient_spec (ramifiedCuspScaleUnit side) h hf j
    change 3*((↑(-ramifiedCuspRoot side)⁻¹:Eis)^2*
      (onceCuspScale (ramifiedCuspScaleUnit side)*omega^j.val))^2*
      onceCuspFrequencyQuotient (ramifiedCuspScaleUnit side) h hf j=_
    calc
      _=3*(↑(-ramifiedCuspRoot side)⁻¹:Eis)^4*
          (onceCuspScale (ramifiedCuspScaleUnit side)*omega^j.val)*h:=by
        conv_rhs => rw [hh]
        ring
      _=_:=by
        simp only [ramifiedSixUnit,ramifiedSixPower,Units.val_mul,Units.val_pow_eq_pow_val,
          ramifiedOmegaUnit_val,onceCuspScale]
        rw [three_eq_ramifiedUnit,trace_eq_ramifiedUnit]
        ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_norm_third (u:Eisˣ) (m:ℕ) :
    ‖eisEmbedding (u.val*lambda^m)‖^(1/3:ℝ)=(3:ℝ)^((m:ℝ)/6) := by
  have hs:‖eisEmbedding (u.val*lambda^m)‖^2=(3:ℝ)^m:=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,ramifiedElement_absNorm,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _=(‖eisEmbedding (u.val*lambda^m)‖^2)^(1/6:ℝ):=by
      rw [←Real.rpow_natCast_mul (norm_nonneg _)]
      congr 1
      norm_num
    _=((3:ℝ)^m)^(1/6:ℝ):=by rw [hs]
    _=(3:ℝ)^((m:ℝ)/6):=by
      rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤3)]
      congr 1
      ring

lemma cubicBesselNormalizer_ramified_mul_norm (h:Eis) (u:Eisˣ) (m:ℕ) :
    ‖cubicBesselNormalizer (h*(u.val*lambda^m))‖=
      ‖cubicBesselNormalizer h‖*(3:ℝ)^((m:ℝ)/6) := by
  have hp:0<‖eisEmbedding (u.val*lambda^m)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (ramifiedElement_ne_zero u m))
  rw [cubicBesselNormalizer_mul,norm_mul]
  have he:=Complex.norm_cpow_eq_rpow_re_of_pos hp (1/3:ℂ)
  have hre:(1/3:ℂ).re=(1/3:ℝ):=by norm_num
  rw [hre,ramified_norm_third] at he
  rw [he]
  ring

def unramifiedCoefficientBaseBound :ℝ:=
  ‖cubicBesselNormalizer 1‖*ramifiedResidueFamilyMass 1

lemma unramifiedCoefficientBaseBound_nonneg :0≤unramifiedCoefficientBaseBound:=
  mul_nonneg (norm_nonneg _) (ramifiedResidueFamilyMass_nonneg _)

lemma unramifiedResidualCoefficient_ramified_bound (u:Eisˣ) (m:ℕ) :
    ‖unramifiedResidualCoefficient (u.val*lambda^m)‖≤
      unramifiedCoefficientBaseBound*(3:ℝ)^((m:ℝ)/6) := by
  have hc:‖cubicBesselNormalizer (u.val*lambda^m)‖=
      ‖cubicBesselNormalizer 1‖*(3:ℝ)^((m:ℝ)/6):=by
    simpa only [one_mul] using cubicBesselNormalizer_ramified_mul_norm 1 u m
  rw [unramifiedResidualCoefficient,norm_mul,hc,unramifiedCoefficientBaseBound]
  have he:=mul_le_mul_of_nonneg_left (unramifiedGaussResidue_unit_lambda_norm_le u m)
    (mul_nonneg (norm_nonneg (cubicBesselNormalizer 1)) (Real.rpow_nonneg (show (0:ℝ)≤3 by norm_num) ((m:ℝ)/6)))
  exact he.trans_eq (by ring)

theorem unramifiedResidualCoefficient_squarefree_cube_bound (I J:Ideal Eis)
    (hI:CompletedGauss.primaryGenerator I≠0) (hJ:CompletedGauss.primaryGenerator J≠0) (hsq:Squarefree I)
    (u:Eisˣ) (m:ℕ) :
    ‖unramifiedResidualCoefficient ((u.val*lambda^m)*CompletedGauss.primaryGenerator I*
      (CompletedGauss.primaryGenerator J)^3)‖≤
      unramifiedCoefficientBaseBound*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (CompletedGauss.primaryGenerator J)‖ := by
  rw [unramifiedResidualCoefficient_squarefree_cube_norm I J hI hJ hsq u m]
  exact (mul_le_mul_of_nonneg_left (unramifiedResidualCoefficient_ramified_bound u m)
    (norm_nonneg _)).trans_eq (by ring)

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedSixWeight_norm_le_one (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) (i:RamifiedSixBranch) :
    ‖ramifiedSixWeight side h hf i (4/3)‖≤1 := by
  rcases i with i|i
  · norm_num [ramifiedSixWeight,norm_mul,breveE_norm]
  rcases i with i|i
  · norm_num [ramifiedSixWeight,norm_mul,breveE_norm]
  rcases i with i|i
  · norm_num [ramifiedSixWeight,norm_mul,breveE_norm]
  · unfold ramifiedSixWeight
    dsimp only
    split_ifs
    · simp only [norm_mul,breveE_norm,mul_one]
      norm_num only [norm_inv,norm_div,norm_one,Complex.norm_ofNat]
      have hw:=ramifiedWeight_norm_scalar 1
      norm_num only [pow_one,Nat.cast_ofNat] at hw
      have hb:=ramifiedDecayRatio_lt_one.le
      nlinarith [norm_nonneg ((3:ℂ)^(-(4/3:ℂ)))]
    · simp

lemma ramifiedSixIndex_squarefree_cube (side:Bool) (u:Eisˣ) (m:ℕ) (n b:Eis)
    (hf:(3:Eis)∣((u.val*lambda^m)*n*b^3)-onceCuspScale (ramifiedCuspScaleUnit side))
    (i:RamifiedSixBranch) :
    ramifiedSixIndex side ((u.val*lambda^m)*n*b^3) hf i=
      (((ramifiedSixUnit side i*u:Eisˣ):Eis)*lambda^(ramifiedSixPower i+m))*n*b^3 := by
  rw [ramifiedSixIndex_multiplier,Units.val_mul,pow_add]
  ring

lemma ramifiedSix_normalized_term_bound (side:Bool) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) (hsq:Squarefree I)
    (u:Eisˣ) (m:ℕ)
    (hf:(3:Eis)∣((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)-
      onceCuspScale (ramifiedCuspScaleUnit side)) (i:RamifiedSixBranch) :
    ‖cubicBesselNormalizer ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)*
      unramifiedGaussResidue (ramifiedSixIndex side
        ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3) hf i)‖≤
      (unramifiedCoefficientBaseBound*(3:ℝ)^(1/2:ℝ))*(3:ℝ)^((m:ℝ)/6)*
        ‖eisEmbedding (primaryGenerator J)‖ := by
  let h:=(u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3
  let idx:=ramifiedSixIndex side h hf i
  have hc:‖cubicBesselNormalizer idx‖=
      ‖cubicBesselNormalizer h‖*(3:ℝ)^((ramifiedSixPower i:ℝ)/6):=by
    dsimp only [idx]
    rw [ramifiedSixIndex_multiplier,mul_comm]
    exact cubicBesselNormalizer_ramified_mul_norm h (ramifiedSixUnit side i) (ramifiedSixPower i)
  have hp:1≤(3:ℝ)^((ramifiedSixPower i:ℝ)/6):=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hcle:‖cubicBesselNormalizer h‖≤‖cubicBesselNormalizer idx‖:=by
    rw [hc]
    exact le_mul_of_one_le_right (norm_nonneg _) hp
  have hnorm:‖unramifiedResidualCoefficient idx‖≤
      unramifiedCoefficientBaseBound*(3:ℝ)^(((ramifiedSixPower i+m:ℕ):ℝ)/6)*
        ‖eisEmbedding (primaryGenerator J)‖:=by
    dsimp only [idx,h]
    rw [ramifiedSixIndex_squarefree_cube]
    exact unramifiedResidualCoefficient_squarefree_cube_bound I J hI hJ hsq
      (ramifiedSixUnit side i*u) (ramifiedSixPower i+m)
  have hexp:((ramifiedSixPower i+m:ℕ):ℝ)/6≤(m:ℝ)/6+1/2:=by
    have hr:(ramifiedSixPower i:ℝ)≤3:=by exact_mod_cast (ramifiedSixPower_bounds i).2
    push_cast
    linarith
  have hpow:(3:ℝ)^(((ramifiedSixPower i+m:ℕ):ℝ)/6)≤
      (3:ℝ)^((m:ℝ)/6)*(3:ℝ)^(1/2:ℝ):=by
    rw [←Real.rpow_add (by norm_num : (0:ℝ)<3)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  calc
    _≤‖unramifiedResidualCoefficient idx‖:=by
      rw [unramifiedResidualCoefficient,norm_mul,norm_mul]
      exact mul_le_mul_of_nonneg_right hcle (norm_nonneg _)
    _≤unramifiedCoefficientBaseBound*(3:ℝ)^(((ramifiedSixPower i+m:ℕ):ℝ)/6)*
        ‖eisEmbedding (primaryGenerator J)‖:=hnorm
    _≤unramifiedCoefficientBaseBound*((3:ℝ)^((m:ℝ)/6)*(3:ℝ)^(1/2:ℝ))*
        ‖eisEmbedding (primaryGenerator J)‖:=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow unramifiedCoefficientBaseBound_nonneg)
        (norm_nonneg _)
    _=_:=by ring

theorem ramifiedBesselValue_squarefree_cube_bound :
    ∃C:ℝ,0<C ∧ ∀(side:Bool) (I J:Ideal Eis),
      primaryGenerator I≠0→primaryGenerator J≠0→Squarefree I→∀(u:Eisˣ) (m:ℕ),
      ‖ramifiedBesselValue side ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖≤
        C*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖ := by
  let V:ℂ:=((9*Real.sqrt 3/2:ℝ):ℂ)
  let A:ℝ:=‖(3:ℂ)^(2/3:ℂ)‖*‖V⁻¹‖
  let B:ℝ:=unramifiedCoefficientBaseBound*(3:ℝ)^(1/2:ℝ)
  have hA:0≤A:=mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hB:0≤B:=mul_nonneg unramifiedCoefficientBaseBound_nonneg (Real.rpow_nonneg (by norm_num) _)
  refine ⟨1+6*A*B,by positivity,?_⟩
  intro side I J hI hJ hsq u m
  let h:=(u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3
  let D:ℝ:=B*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖
  have hD:0≤D:=by dsimp only [D]; positivity
  unfold ramifiedBesselValue
  split_ifs with hf
  · have hs:‖cubicBesselNormalizer h*ramifiedArithmeticResidue side h hf‖≤6*D:=by
      have he:cubicBesselNormalizer h*ramifiedArithmeticResidue side h hf=
          ∑i:RamifiedSixBranch,ramifiedSixWeight side h hf i (4/3)*
            (cubicBesselNormalizer h*unramifiedGaussResidue (ramifiedSixIndex side h hf i)):=by
        rw [ramifiedArithmeticResidue,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [he]
      calc
        _≤∑i:RamifiedSixBranch,‖ramifiedSixWeight side h hf i (4/3)*
            (cubicBesselNormalizer h*unramifiedGaussResidue (ramifiedSixIndex side h hf i))‖:=norm_sum_le _ _
        _≤∑i:RamifiedSixBranch,D:=by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_right (ramifiedSixWeight_norm_le_one side h hf i) (norm_nonneg _)).trans
            (by simpa only [one_mul,D,B,h] using ramifiedSix_normalized_term_bound side I J hI hJ hsq u m hf i)
        _=6*D:=by simp [RamifiedSixBranch]
    have he:‖(3:ℂ)^(2/3:ℂ)*cubicBesselNormalizer h*ramifiedArithmeticResidue side h hf/V‖≤A*(6*D):=by
      rw [div_eq_mul_inv,mul_assoc ((3:ℂ)^(2/3:ℂ)),norm_mul,norm_mul]
      dsimp only [A]
      nlinarith [mul_le_mul_of_nonneg_left hs (norm_nonneg ((3:ℂ)^(2/3:ℂ))),norm_nonneg (V⁻¹)]
    refine he.trans ?_
    dsimp only [A,B,D]
    have hnonneg:0≤(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖:=by positivity
    nlinarith
  · rw [norm_zero]
    positivity

end CubicEisenstein

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceResidualFourierCoefficient_prime_norm (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    ‖sourceResidualFourierCoefficient (h*p)‖=‖sourceResidualFourierCoefficient h‖ := by
  have hp9:¬p∣9*h:=by
    have ht:=ramified_prime_frequency_not_dvd h p hp hpp hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using ht
  rw [sourceResidualFourierCoefficient_prime_factor p hp hpp h hph,norm_mul,norm_div,
    primeCubicGauss_two_norm p hp hpp (9*h) hp9,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp.ne_zero)),one_mul]

theorem sourceResidualFourierCoefficient_prime_product_norm {ι:Type*}
    (s:Finset ι) (p:ι→Eis) (hp:∀i∈s,Prime (p i))
    (hprimary:∀i∈s,lambda^2∣p i-1)
    (hpair:∀i∈s,∀j∈s,i≠j→IsCoprime (p i) (p j))
    (h:Eis) (hph:∀i∈s,¬p i∣h) :
    ‖sourceResidualFourierCoefficient (h*(∏i∈s,p i))‖=‖sourceResidualFourierCoefficient h‖ := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s hi ih=>
    have hpi:=hp i (Finset.mem_insert_self _ _)
    have hpri:=hprimary i (Finset.mem_insert_self _ _)
    have hps:∀j∈s,Prime (p j):=fun j hj=>hp j (Finset.mem_insert_of_mem hj)
    have hprs:∀j∈s,lambda^2∣p j-1:=fun j hj=>hprimary j (Finset.mem_insert_of_mem hj)
    have hcpi:IsCoprime (p i) (∏j∈s,p j):=IsCoprime.prod_right (fun j hj=>
      hpair i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (by intro he;subst j;exact hi hj))
    have hpb:¬p i∣h*(∏j∈s,p j):=by
      intro hd
      rcases hpi.dvd_mul.mp hd with hd|hd
      · exact hph i (Finset.mem_insert_self _ _) hd
      · exact hpi.not_isUnit (hcpi.isUnit_of_dvd hd)
    rw [Finset.prod_insert hi,show h*(p i*(∏j∈s,p j))=(h*(∏j∈s,p j))*p i by ring,
      sourceResidualFourierCoefficient_prime_norm (p i) hpi hpri _ hpb]
    exact ih hps hprs (fun j hj k hk hjk=>hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
      (fun j hj=>hph j (Finset.mem_insert_of_mem hj))

lemma sourceResidualFourierCoefficient_ramified_bound (u:Eisˣ) (m:ℕ) :
    ‖sourceResidualFourierCoefficient (u.val*lambda^m)‖≤
      (‖cubicBesselNormalizer 1‖*(9*ramifiedSourceFamilyConstant*ramifiedResidueFamilyMass 1))*
        (3:ℝ)^((m:ℝ)/6) := by
  have hc:‖cubicBesselNormalizer (u.val*lambda^m)‖=
      ‖cubicBesselNormalizer 1‖*(3:ℝ)^((m:ℝ)/6):=by
    simpa only [one_mul] using cubicBesselNormalizer_ramified_mul_norm 1 u m
  rw [sourceResidualFourierCoefficient,norm_mul,hc]
  exact (mul_le_mul_of_nonneg_left (sourceArithmeticResidue_unit_lambda_bound u m)
    (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (show (0:ℝ)≤3 by norm_num) ((m:ℝ)/6)))).trans_eq (by ring)

lemma sourceResidualFourierCoefficient_squarefree_cube_norm (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) (hsq:Squarefree I)
    (u:Eisˣ) (m:ℕ) :
    ‖sourceResidualFourierCoefficient ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖=
      ‖eisEmbedding (primaryGenerator J)‖*‖sourceResidualFourierCoefficient (u.val*lambda^m)‖ := by
  rw [sourceResidualFourierCoefficient_primary_cube _ hJ (primaryGenerator_spec J hJ).2 _
    (mul_ne_zero (ramifiedElement_ne_zero u m) hI),norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  congr 1
  rw [primaryGenerator_squarefree_support I hI hsq]
  apply sourceResidualFourierCoefficient_prime_product_norm
  · exact fun P hP=>primaryPrime_isPrime_of_mem I P hI hP
  · exact fun P hP=>(primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
  · exact primaryPrime_support_coprime I hI
  · intro P hP hd
    have hp:=primaryPrime_isPrime_of_mem I P hI hP
    have hpp:lambda^2∣primaryPrime P-1:=
      (primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
    have hc:IsCoprime (u.val*lambda^m) (primaryPrime P):=
      (ramified_primary_coprime u m _ hpp).of_mul_left_right
    exact hp.not_isUnit (hc.symm.isUnit_of_dvd hd)

theorem sourceResidualFourierCoefficient_squarefree_cube_bound :
    ∃C:ℝ,0<C ∧ ∀(I J:Ideal Eis),primaryGenerator I≠0→primaryGenerator J≠0→
      Squarefree I→∀(u:Eisˣ) (m:ℕ),
      ‖sourceResidualFourierCoefficient ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖≤
        C*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖ := by
  let C:ℝ:=‖cubicBesselNormalizer 1‖*(9*ramifiedSourceFamilyConstant*ramifiedResidueFamilyMass 1)
  have hC:0≤C:=by dsimp only [C]; exact mul_nonneg (norm_nonneg _) (mul_nonneg
    (mul_nonneg (by norm_num) ramifiedSourceFamilyConstant_nonneg) (ramifiedResidueFamilyMass_nonneg _))
  refine ⟨1+C,by positivity,?_⟩
  intro I J hI hJ hsq u m
  rw [sourceResidualFourierCoefficient_squarefree_cube_norm I J hI hJ hsq u m]
  have he:=mul_le_mul_of_nonneg_left (sourceResidualFourierCoefficient_ramified_bound u m)
    (norm_nonneg (eisEmbedding (primaryGenerator J)))
  have hz:0≤(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖:=by positivity
  dsimp only [C] at *
  nlinarith

theorem three_cusp_coefficients_squarefree_cube_bound :
    ∃C:ℝ,0<C ∧ ∀(I J:Ideal Eis),primaryGenerator I≠0→primaryGenerator J≠0→
      Squarefree I→∀(u:Eisˣ) (m:ℕ),
      ‖sourceResidualFourierCoefficient ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖≤
        C*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖ ∧
      ∀side:Bool,‖ramifiedBesselValue side ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖≤
        C*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖ := by
  obtain ⟨Cs,hCs,hs⟩:=sourceResidualFourierCoefficient_squarefree_cube_bound
  obtain ⟨Cr,hCr,hr⟩:=ramifiedBesselValue_squarefree_cube_bound
  refine ⟨Cs+Cr,by positivity,?_⟩
  intro I J hI hJ hsq u m
  have hz:0≤(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖:=by positivity
  constructor
  · exact (hs I J hI hJ hsq u m).trans (by nlinarith)
  · intro side
    exact (hr side I J hI hJ hsq u m).trans (by nlinarith)

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

end

section
open scoped Classical BigOperators

open ActualEisensteinCubic CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

abbrev ThetaPrimaryCubePair :=
  {I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
  {J:Ideal Eis // primaryGenerator J≠0}

def thetaPrimaryProduct (p : ThetaPrimaryCubePair) : GoodIdeal :=
  ⟨p.1.val*p.2.val^3,by
    rw [primaryGenerator_mul,primaryGenerator_pow]
    exact mul_ne_zero p.1.property.2 (pow_ne_zero 3 p.2.property)⟩

abbrev ThetaFullIndex := Eisˣ × ℕ × ThetaPrimaryCubePair

def thetaFullFrequency (p : ThetaFullIndex) : Eis :=
  (p.1.val*lambda^p.2.1)*primaryGenerator p.2.2.1.val*
    (primaryGenerator p.2.2.2.val)^3

end

section
open scoped BigOperators Classical MatrixGroups
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

structure SourceCuspDatum where
  gamma : levelTwo
  index : Fin 3
  lower_ne_zero :
    (integralComplexMatrix (gamma:SL(2,Eis))*integralComplexMatrix (cuspRepresentative index)) 1 0≠0

namespace SourceCuspDatum

def matrix (d : SourceCuspDatum) : SL(2,ℂ) :=
  integralComplexMatrix (d.gamma:SL(2,Eis))*integralComplexMatrix (cuspRepresentative d.index)
def point (d : SourceCuspDatum) : ℂ := d.matrix 0 0/d.matrix 1 0
def dualPoint (d : SourceCuspDatum) : ℂ := -d.matrix 1 1/d.matrix 1 0
def heightScale (d : SourceCuspDatum) : ℝ := ‖d.matrix 1 0‖^2
def multiplier (d : SourceCuspDatum) : ℂ := -star (levelTwoComplexCharacter d.gamma)/(d.matrix 1 0)^2

end SourceCuspDatum

lemma exists_sourceCuspDatum (a c : Eis) (hc : c≠0) :
    ∃d:SourceCuspDatum,d.point=eisEmbedding a/eisEmbedding c := by
  obtain ⟨M,hMc,hratio⟩:=exists_integral_matrix_cusp_ratio a c hc
  obtain ⟨G,j,T,hT,_,_,hM⟩:=three_cusp_decomposition M
  let g:SL(2,ℂ):=integralComplexMatrix (G:SL(2,Eis))*integralComplexMatrix (cuspRepresentative j)
  have he:integralComplexMatrix M=g*integralComplexMatrix T:=by
    rw [hM,map_mul,map_mul]
  have ht:integralComplexMatrix T 1 0=0:=by rw [integralComplexMatrix_apply,hT,map_zero]
  have hmc:(g*integralComplexMatrix T) 1 0≠0:=by
    rw [←he,integralComplexMatrix_apply]
    exact eisEmbedding_ne_zero hMc
  obtain ⟨hg,hr⟩:=upper_triangular_right_cusp_ratio g (integralComplexMatrix T) ht hmc
  refine ⟨⟨G,j,hg⟩,?_⟩
  change g 0 0/g 1 0=_
  rw [←hr,←he]
  exact hratio

def rationalSourceCusp (a c : Eis) (hc : c≠0) : SourceCuspDatum :=
  (exists_sourceCuspDatum a c hc).choose

def sourceCuspZFamily (j : Fin 3) (z : ℂ) : ℝ→ℂ :=
  cuspZProfile (fun w=>cubicSourceConjugateFunction (integralComplexMatrix (cuspRepresentative j) • w)) z

def finiteTwistCusp (c : Eis) (hc : c≠0) (h : Eis⧸Ideal.span {c}) : SourceCuspDatum :=
  rationalSourceCusp (-3*Quotient.out h) c hc

end

open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

local notation "Eis" => ActualEisensteinCubic.O

namespace SubexponentialBesselCoefficients

def scaledConjugateZTerm (coeff : SubexponentialBesselCoefficients)
    (r v : ℝ) (z : ℂ) (h : Eis) : ℂ :=
  (-2*Real.pi*Complex.I*cuspFrequency h/(r:ℂ))*star (coeff.term h (v/r,z/(r:ℂ)))

end SubexponentialBesselCoefficients

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace CubicEisenstein

section
open scoped BigOperators Classical MatrixGroups
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def sourceCuspCoefficients (j : Fin 3) : SubexponentialBesselCoefficients :=
  ![sourceBesselCoefficients,ramifiedBesselCoefficients false,ramifiedBesselCoefficients true] j

def sourceCuspScale (j : Fin 3) : ℝ := ![1,3,3] j
def sourceCuspBesselConstant (j : Fin 3) : ℂ := ![(3*Real.pi)*constantArithmeticResidue,0,0] j

lemma sourceCuspScale_pos (j : Fin 3) : 0<sourceCuspScale j := by
  fin_cases j <;> norm_num [sourceCuspScale]

def sourceCuspZTerm (j : Fin 3) (z : ℂ) (v : ℝ) (h : Eis) : ℂ :=
  (sourceCuspCoefficients j).scaledConjugateZTerm (sourceCuspScale j) v z h

end

open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def sourceCuspRadialLength (h : Eis) : ℝ := if h=0 then 1 else ‖eisEmbedding h‖^2
def sourceCuspRadialScale (j : Fin 3) : ℝ := thetaBesselScale/sourceCuspScale j

def sourceCuspRadialBaseCoefficient (j : Fin 3) (h : Eis) : ℂ :=
  (-2*Real.pi*Complex.I*cuspFrequency h)*star ((sourceCuspCoefficients j).value h)/
    ((sourceCuspScale j:ℂ)^2*(sourceCuspRadialLength h:ℂ))

def sourceCuspRadialCoefficient (j : Fin 3) (z : ℂ) (h : Eis) : ℂ :=
  sourceCuspRadialBaseCoefficient j h*
    ShortDraftTrace.breveE (-cuspFrequency h*(z/(sourceCuspScale j:ℂ)))

end CubicEisenstein

open Filter MeasureTheory
open scoped Classical BigOperators Topology

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open scoped BigOperators Classical Topology ContDiff MatrixGroups

section
open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def SourceCuspDatum.smoothedKernel (d:SourceCuspDatum) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  (d.multiplier*(d.heightScale:ℂ)*
      ((thetaBesselScale/sourceCuspRadialScale d.index:ℝ):ℂ)^2)*
    ∑'n:Eis,sourceCuspRadialCoefficient d.index d.dualPoint n*
      CubicReflectionKernel.paperKernel (Vstar W)
        (27*thetaBesselScale^2*(sourceCuspRadialScale d.index)^2*X*
          sourceCuspRadialLength n/d.heightScale^2)

end

open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

end

open scoped Classical MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def fixedCuspCoefficientBound : ℝ :=
  Classical.choose three_cusp_coefficients_squarefree_cube_bound

def fixedCuspArrayIndex (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : Eis :=
  (u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3

def fixedCuspArrayEligible (I J:Ideal Eis) : Prop :=
  Squarefree I ∧ primaryGenerator I≠0 ∧ primaryGenerator J≠0

def fixedCuspArrayWeight (m:ℕ) (J:Ideal Eis) : ℝ :=
  (3:ℝ)^((m:ℝ)/6)*Real.sqrt (Ideal.absNorm J:ℝ)

def fixedCuspArray (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  if fixedCuspArrayEligible I J then
    (sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J) /
      ((fixedCuspCoefficientBound*fixedCuspArrayWeight m J:ℝ):ℂ)
  else 0

def fixedConjugateCuspArray (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  star (fixedCuspArray j u m I J)

end CubicEisenstein

section
open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

namespace LocalReflectionBrackets

section
open CubicEisenstein
variable {F : Type*} [Field F] [Fintype F]

def frequencyMultiplier (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x h : F) : ℂ :=
  if h=0 then 1 else (((χ⁻¹)^2) ((σ:F)*h))*ψ (((ε:F)*x)*h⁻¹)

def frequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : ℕ) (σ ε : Fˣ) (x h : F) : ℂ :=
  finiteAdditiveFourierCoeff ψ (fun t=>(χ^j) t) h*frequencyMultiplier χ ψ σ ε x h

open ActualEisensteinCubic CompletedGauss
noncomputable local instance quotientFieldFrequency (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] :
    Field (ActualEisensteinCubic.O⧸P) := Ideal.Quotient.field P
noncomputable local instance quotientFintypeFrequency (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] :
    Fintype (ActualEisensteinCubic.O⧸P) := Fintype.ofFinite _

end

open ActualEisensteinCubic CubicEisenstein IdealGaussCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

end LocalReflectionBrackets
end

namespace CubicEisenstein
open scoped Classical MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma upper_right_removed_bottom (M T:SL(2,Eis)) (hT:T 1 0=0) :
    (M*T⁻¹) 1 0=M 1 0*T 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,hT]

structure FixedCuspShape (H:SL(2,Eis)) where
  gamma : levelTwo
  index : Fin 3
  upper : SL(2,Eis)
  lower_zero : upper 1 0=0
  upper_unit : IsUnit (upper 0 0)
  lower_unit : IsUnit (upper 1 1)
  factorization : H=(gamma:SL(2,Eis))*cuspRepresentative index*upper

lemma exists_fixedCuspShape (H:SL(2,Eis)) : Nonempty (FixedCuspShape H) := by
  obtain ⟨G,j,T,hT,hT0,hT1,he⟩:=three_cusp_decomposition H
  exact ⟨⟨G,j,T,hT,hT0,hT1,he⟩⟩

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H) (g:levelTwo)

lemma removed_eq : (g:SL(2,Eis))*H*s.upper⁻¹=
    ((g*s.gamma:levelTwo):SL(2,Eis))*cuspRepresentative s.index := by
  calc
    _ = (g:SL(2,Eis))*((s.gamma:SL(2,Eis))*cuspRepresentative s.index*s.upper)*s.upper⁻¹ :=
      congrArg (fun K:SL(2,Eis)=>(g:SL(2,Eis))*K*s.upper⁻¹) s.factorization
    _ = _ := by simp only [Subgroup.coe_mul]; group

def datum (h:((g:SL(2,Eis))*H) 1 0≠0) : SourceCuspDatum where
  gamma := g*s.gamma
  index := s.index
  lower_ne_zero := by
    rw [←map_mul,←s.removed_eq g,integralComplexMatrix_apply,
      upper_right_removed_bottom _ _ s.lower_zero,map_mul]
    exact mul_ne_zero (eisEmbedding_ne_zero h) (eisEmbedding_ne_zero s.lower_unit.ne_zero)

end FixedCuspShape
end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups ContDiff

end

end OAI
end

section

namespace OAI

noncomputable section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace ShortDraftCusp
open scoped BigOperators Classical MatrixGroups Matrix

section
open ActualEisensteinCubic CubicKubota CubicEisenstein ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def A3WeylCusp (u : Eis) : SL(2,Eis) :=
  ⟨!![u,-1;1,0],by simp [Matrix.det_fin_two]⟩

lemma A3_ramified_relative_matrix (M : SL(2,Eis)) (u : Eis) :
    ((M*(lowerCuspMatrix u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) =
      !![M 0 0-u*M 0 1,M 0 1;M 1 0-u*M 1 1,M 1 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerCuspMatrix,Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

lemma A3_unramified_relative_matrix (M : SL(2,Eis)) (u : Eis) :
    ((M*(A3WeylCusp u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) =
      !![-M 0 1,M 0 0+u*M 0 1;-M 1 1,M 1 0+u*M 1 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A3WeylCusp,Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

lemma A3_ramified_mem_levelThree (M : SL(2,Eis)) (u : Eis)
    (ha : (3:Eis)∣M 0 0-1) (hb : (3:Eis)∣M 0 1)
    (hc : (3:Eis)∣M 1 0-u) (hd : (3:Eis)∣M 1 1-1) :
    M*(lowerCuspMatrix u)⁻¹∈levelThree := by
  apply (mem_levelThree_iff_entries _).mpr
  intro i j
  rw [A3_ramified_relative_matrix]
  fin_cases i <;> fin_cases j
  · convert (preTransparency := .instances) dvd_sub ha (dvd_mul_of_dvd_right hb u) using 1 ; simp ; ring
  · simpa using hb
  · convert (preTransparency := .instances) dvd_sub hc (dvd_mul_of_dvd_right hd u) using 1 ; simp ; ring
  · simpa using hd

lemma A3_unramified_mem_levelThree (M : SL(2,Eis)) (u : Eis)
    (ha : (3:Eis)∣M 0 0-u) (hb : (3:Eis)∣M 0 1+1)
    (hc : (3:Eis)∣M 1 0-1) (hd : (3:Eis)∣M 1 1) :
    M*(A3WeylCusp u)⁻¹∈levelThree := by
  apply (mem_levelThree_iff_entries _).mpr
  intro i j
  rw [A3_unramified_relative_matrix]
  fin_cases i <;> fin_cases j
  · convert (preTransparency := .instances) dvd_neg.mpr hb using 1 ; simp ; ring
  · convert (preTransparency := .instances) dvd_add ha (dvd_mul_of_dvd_right hb u) using 1 ; simp ; ring
  · simpa using dvd_neg.mpr hd
  · convert (preTransparency := .instances) dvd_add hc (dvd_mul_of_dvd_right hd u) using 1 ; simp ; ring

end

open ActualEisensteinCubic CubicKubota CubicEisenstein ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

end ShortDraftCusp

namespace CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

section
open CompletedGauss CompletedDyadic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def sourceFrequencyAngle (h:Eis) : ℂ := eisEmbedding h/(‖eisEmbedding h‖:ℂ)

def fixedRadialCoefficientScalar : ℂ :=
  (-2*Real.pi*Complex.I)*thetaFrequencyScale*(fixedCuspCoefficientBound:ℂ)

end

open CompletedGauss CompletedDyadic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

open scoped Classical BigOperators

namespace CanonicalRowCompletion
open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticAllOddCRT
open UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

theorem idealRowHom_congr_mod (I:Ideal Eis) (x y:Eis) (hxy:x-y∈I) :
    idealRowHom x I=idealRowHom y I := by
  by_cases hI:I=0
  · subst I
    simp only [map_zero]
  change (if I=0 then 0 else _)=(if I=0 then 0 else _)
  rw [if_neg hI,if_neg hI]
  congr 1
  apply Multiset.map_congr rfl
  intro P hP
  have hle:I≤P:=((Ideal.mem_normalizedFactors_iff hI).mp hP).2
  unfold localRowValue
  split_ifs with hp
  · let:P.IsMaximal:=hp.1
    congr 1
    exact Ideal.Quotient.eq.mpr (hle hxy)
  · rfl

lemma sexticReciprocityPhase_congr_right (a x y:Eis) (hxy:(4:Eis)∣x-y) :
    sexticReciprocityPhase a x=sexticReciprocityPhase a y := by
  unfold sexticReciprocityPhase
  rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub x y hxy]

lemma sexticReciprocityPhase_norm (a x:Eis) : ‖sexticReciprocityPhase a x‖≤1 := by
  unfold sexticReciprocityPhase quadraticRaySign
  split_ifs <;> norm_num

def reciprocalRow (a:Eis) (ha:Supported (Ideal.span {a})) : Eis→*ℂ where
  toFun n:=sexticReciprocityPhase a n*idealRowHom n (Ideal.span {a})
  map_one' := by rw [sexticReciprocityPhase_one_right a ha,idealRowHom_one_supported _ ha,one_mul]
  map_mul' x y := by
    rw [sexticReciprocityPhase_mul_right,idealRowHom_argument_mul]
    ring

lemma reciprocalRow_eq_idealRowHom (a n:Eis)
    (ha:Supported (Ideal.span {a})) (hn:Supported (Ideal.span {n}))
    (hpa:lambda^2∣a-1) (hpn:lambda^2∣n-1) :
    reciprocalRow a ha n=idealRowHom a (Ideal.span {n}) := by
  have h:=idealRowHom_primary_reciprocity n a hpn hpa hn ha
  have hs:sexticReciprocityPhase n a=sexticReciprocityPhase a n := by
    exact congrArg (fun z:ℤ=>(z:ℂ)) (quadraticRaySign_symm _ _)
  change sexticReciprocityPhase a n*idealRowHom n (Ideal.span {a})=_
  rw [hs] at h
  exact h.symm

end CanonicalRowCompletion

namespace CubicEisenstein
open scoped Classical BigOperators MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

def amplitude (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  fixedConjugateCuspArray s.index u m I J*
    sourceFrequencyAngle (fixedCuspArrayIndex u m I J)*
    ShortDraftTrace.breveE (-cuspFrequency (fixedCuspArrayIndex u m I J)*
      eisEmbedding (s.upper 0 0*s.upper 0 1)/(sourceCuspScale s.index:ℂ))

end FixedCuspShape
end CubicEisenstein

open scoped BigOperators Classical Matrix MatrixGroups

namespace ShortDraftCRT
variable {R:Type*} [CommRing R]

lemma exists_controlled_inverse (B c a:R) (ha:IsCoprime a (B*c)) :
    ∃d0:R,B*c∣a*d0-1 := by
  obtain ⟨x,y,hxy⟩:=ha
  refine ⟨x,-y,?_⟩
  linear_combination hxy

lemma exists_controlled_zero_inverse (B c a:R)
    (hBc:IsCoprime B c) (hac:IsCoprime a c) :
    ∃d0:R,B∣d0 ∧ c∣a*d0-1 := by
  obtain ⟨x,y,hxy⟩:=hac.mul_left hBc
  refine ⟨B*x,⟨x,rfl⟩,-y,?_⟩
  linear_combination hxy

variable [IsDomain R]

lemma fixed_completion_upper_right_dvd (B M c r a d0 b d:R)
    (hc:c≠0) (hBM:B∣M) (hr:IsCoprime r (M*c))
    (hinv:B*c∣a*d0-1) (hdet:a*d-b*(c*r)=1) (hd:M*c∣d-d0) : B∣b := by
  have hBcM:B*c∣M*c:=mul_dvd_mul_right hBM c
  have hadd:B*c∣a*(d-d0):=dvd_mul_of_dvd_right (hBcM.trans hd) a
  have hfull:B*c∣a*d-1:=by
    convert (preTransparency := .instances) dvd_add hadd hinv using 1 ; ring
  have hmul:B*c∣c*(b*r):=by
    convert (preTransparency := .instances) hfull using 1
    linear_combination -hdet
  rw [mul_comm B c] at hmul
  have hbr:B∣b*r:=(mul_dvd_mul_iff_left hc).mp hmul
  have hBr:IsCoprime B r:=hr.of_mul_right_left.symm.of_isCoprime_of_dvd_left hBM
  exact hBr.dvd_of_dvd_mul_right hbr

theorem exists_fixed_completion_upper_right (B M c r a d0:R)
    (hc:c≠0) (hBM:B∣M) (hr:IsCoprime r (M*c)) (har:IsCoprime a r)
    (hinv:B*c∣a*d0-1) :
    ∃b d:R,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ B∣b := by
  obtain ⟨b,d,hdet,hd⟩:=exists_fixed_completion M c r a d0
    ((dvd_mul_left c B).trans hinv) hr har
  exact ⟨b,d,hdet,hd,fixed_completion_upper_right_dvd B M c r a d0 b d hc hBM hr hinv hdet hd⟩

omit [IsDomain R] in
theorem exists_fixed_completion_lower_right (B M c r a d0:R)
    (hBM:B∣M) (hr:IsCoprime r (M*c)) (har:IsCoprime a r)
    (hzero:B∣d0) (hinv:c∣a*d0-1) :
    ∃b d:R,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ B∣d ∧ B∣a*d ∧ B∣b*(c*r)+1 := by
  obtain ⟨b,d,hdet,hd⟩:=exists_fixed_completion M c r a d0 hinv hr har
  have hdd:B∣d-d0:=(hBM.trans (dvd_mul_right M c)).trans hd
  have hBd:B∣d:=by
    convert (preTransparency := .instances) dvd_add hdd hzero using 1 ; ring
  have hBad:B∣a*d:=dvd_mul_of_dvd_right hBd a
  refine ⟨b,d,hdet,hd,hBd,hBad,?_⟩
  convert (preTransparency := .instances) hBad using 1
  linear_combination -hdet

end ShortDraftCRT

end

end OAI
end

section

namespace OAI

noncomputable section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace ShortDraftCRT
open scoped BigOperators Classical Matrix MatrixGroups

section
open ActualEisensteinCubic CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma primary_coprime_nine (a:Eis) (ha:lambda^2∣a-1) : IsCoprime a (9:Eis) := by
  have h3:=primary_coprime_three a ha
  simpa only [show (3:Eis)*3=9 by norm_num] using h3.mul_right h3

lemma nine_coprime_of_not_lambda_dvd (c:Eis) (hc:¬lambda∣c) : IsCoprime (9:Eis) c := by
  have hL:IsCoprime lambda c:=
    PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr hc
  have h3:IsCoprime (3:Eis) c:=(hL.mul_left hL).of_isCoprime_of_dvd_left
    (by simpa only [pow_two] using three_dvd_lambda_sq)
  simpa only [show (3:Eis)*3=9 by norm_num] using h3.mul_left h3

lemma primary_numerator_controlled_inverse (c a:Eis)
    (ha:lambda^2∣a-1) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)*c∣a*d0-1 :=
  exists_controlled_inverse 9 c a ((primary_coprime_nine a ha).mul_right hac)

lemma completion_primary_lower_right (a b c d:Eis)
    (hdet:a*d-b*c=1) (ha:(3:Eis)∣a-1) (hb:(3:Eis)∣b) : (3:Eis)∣d-1 := by
  have had:(3:Eis)∣a*d-1:=by
    convert (preTransparency := .instances) dvd_mul_of_dvd_left hb c using 1
    linear_combination hdet
  convert (preTransparency := .instances) dvd_sub had (dvd_mul_of_dvd_left ha d) using 1 ; ring

lemma completion_negative_upper_right (a b c d:Eis)
    (hdet:a*d-b*c=1) (hc:(3:Eis)∣c-1) (hd:(3:Eis)∣d) : (3:Eis)∣b+1 := by
  have hbc:(3:Eis)∣b*c+1:=by
    convert (preTransparency := .instances) dvd_mul_of_dvd_right hd a using 1
    linear_combination -hdet
  convert (preTransparency := .instances) dvd_sub hbc (dvd_mul_of_dvd_right hc b) using 1 ; ring

theorem exists_primary_numerator_completion (M c a:Eis)
    (hc:c≠0) (h9M:(9:Eis)∣M) (ha:lambda^2∣a-1) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)*c∣a*d0-1 ∧
      ∀r:Eis,IsCoprime r (M*c)→IsCoprime a r→lambda^2∣r-1→
      ∃b d:Eis,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ (9:Eis)∣b ∧
        (3:Eis)∣d-1 ∧ (3:Eis)∣c*r-c := by
  obtain ⟨d0,hd0⟩:=primary_numerator_controlled_inverse c a ha hac
  refine ⟨d0,hd0,?_⟩
  intro r hr har hprimary
  obtain ⟨b,d,hdet,hd,hb⟩:=exists_fixed_completion_upper_right 9 M c r a d0 hc h9M hr har hd0
  refine ⟨b,d,hdet,hd,hb,completion_primary_lower_right a b (c*r) d hdet
    (three_dvd_primary_sub_one a ha) ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hb),?_⟩
  convert (preTransparency := .instances) dvd_mul_of_dvd_right (three_dvd_primary_sub_one r hprimary) c using 1 ; ring

theorem exists_unramified_denominator_completion (M c a:Eis)
    (h9M:(9:Eis)∣M) (hc:¬lambda∣c) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)∣d0 ∧ c∣a*d0-1 ∧
      ∀r:Eis,IsCoprime r (M*c)→IsCoprime a r→
      ∃b d:Eis,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ (9:Eis)∣d ∧
        (9:Eis)∣a*d ∧ (9:Eis)∣b*(c*r)+1 := by
  obtain ⟨d0,hzero,hinv⟩:=exists_controlled_zero_inverse 9 c a
    (nine_coprime_of_not_lambda_dvd c hc) hac
  exact ⟨d0,hzero,hinv,fun r hr har=>exists_fixed_completion_lower_right 9 M c r a d0
    h9M hr har hzero hinv⟩

theorem exists_primary_denominator_completion (M c a:Eis)
    (h9M:(9:Eis)∣M) (hc:lambda^2∣c-1) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)∣d0 ∧ c∣a*d0-1 ∧
      ∀r:Eis,IsCoprime r (M*c)→IsCoprime a r→lambda^2∣r-1→
      ∃b d:Eis,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ (9:Eis)∣d ∧
        (9:Eis)∣a*d ∧ (9:Eis)∣b*(c*r)+1 ∧ (3:Eis)∣b+1 ∧ (3:Eis)∣c*r-1 := by
  have hcl:¬lambda∣c:=by
    intro hd
    have hcL:IsCoprime lambda c:=
      (primary_coprime_three c hc).symm.of_isCoprime_of_dvd_left
        ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three)
    exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (hcL.isUnit_of_dvd hd)
  obtain ⟨d0,hzero,hinv,hcomp⟩:=exists_unramified_denominator_completion M c a h9M hcl hac
  refine ⟨d0,hzero,hinv,?_⟩
  intro r hr har hpr
  obtain ⟨b,d,hdet,hd,hBd,had,hbc⟩:=hcomp r hr har
  have hc3:(3:Eis)∣c*r-1:=three_dvd_primary_sub_one _ (primary_mul c r hc hpr)
  exact ⟨b,d,hdet,hd,hBd,had,hbc,completion_negative_upper_right a b (c*r) d hdet hc3
    ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hBd),hc3⟩

end

section
variable {R:Type*} [CommRing R] [IsDomain R]

theorem exists_fixed_matrix_completion_controlled
    (B N M c a0 r0 b0 d0 bResidue dResidue:R)
    (hc:c≠0) (hBM:B∣M) (hNM:N∣M)
    (hdet0:a0*d0-b0*(c*r0)=1)
    (hb0:B∣b0-bResidue) (hd0:N∣d0-dResidue) :
    ∀a r:R,M*c∣a-a0→M∣r-r0→IsCoprime r (M*c)→IsCoprime a r→
      ∃b d:R,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ B∣b-bResidue ∧ N∣d-dResidue ∧
        (!![a,b;c*r,d]:Matrix (Fin 2) (Fin 2) R).map
          (Ideal.Quotient.mk (Ideal.span {M}))=
        (!![a0,b0;c*r0,d0]:Matrix (Fin 2) (Fin 2) R).map
          (Ideal.Quotient.mk (Ideal.span {M})) := by
  intro a r ha hrr hr har
  obtain ⟨b,d,hdet,hd,hmat⟩:=exists_fixed_matrix_completion M c a0 r0 d0 b0 hc hdet0
    a r ha hrr hr har
  have hbd:B∣b-b0:=hBM.trans (fixed_completion_congr M c r r0 a a0 b b0 d d0 hc
    hr.of_mul_right_left.symm hdet hdet0 ha hd hrr)
  have hdd:N∣d-d0:=(hNM.trans (dvd_mul_right M c)).trans hd
  refine ⟨b,d,hdet,hd,?_,?_,hmat⟩
  · convert (preTransparency := .instances) dvd_add hbd hb0 using 1 ; ring
  · convert (preTransparency := .instances) dvd_add hdd hd0 using 1 ; ring

end

section
open ActualEisensteinCubic CubicEisenstein CubicJacobiGlobal CubicKubota ShortDraftCusp
local notation "Eis" => ActualEisensteinCubic.O

def controlledCompletionMatrix (a b c d:Eis) (hdet:a*d-b*c=1) : SL(2,Eis) :=
  ⟨!![a,b;c,d],by simpa [Matrix.det_fin_two] using hdet⟩

end

open ActualEisensteinCubic CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem exists_primary_numerator_sector_completions {ι Q:Type*}
    (M c:Eis) (hc:c≠0) (h9M:(9:Eis)∣M)
    (sector:ι→Q) (a r:ι→Eis)
    (haPrimary:∀i,lambda^2∣a i-1) (hrPrimary:∀i,lambda^2∣r i-1)
    (hcop:∀i,IsCoprime (a i) (c*r i)) (hr:∀i,IsCoprime (r i) (M*c))
    (ha:∀i j,sector i=sector j→M*c∣a i-a j)
    (hrr:∀i j,sector i=sector j→M∣r i-r j) :
    ∃(b d:ι→Eis) (C:Q→Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {M})),
      (∀i,a i*d i-b i*(c*r i)=1) ∧ (∀i,(9:Eis)∣b i) ∧ (∀i,(3:Eis)∣d i-1) ∧
      ∀i,(!![a i,b i;c*r i,d i]:Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {M}))=C (sector i) := by
  have h3M:(3:Eis)∣M:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9M
  have hlocal (q:Q) :
      ∃C:Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {M}),
      ∀i,sector i=q→∃b d:Eis,a i*d-b*(c*r i)=1 ∧ (9:Eis)∣b ∧ (3:Eis)∣d-1 ∧
        (!![a i,b;c*r i,d]:Matrix (Fin 2) (Fin 2) Eis).map
          (Ideal.Quotient.mk (Ideal.span {M}))=C := by
    by_cases hq:∃j,sector j=q
    · obtain ⟨j,hj⟩:=hq
      obtain ⟨inverse,_,hcompletion⟩:=exists_primary_numerator_completion M c (a j) hc h9M
        (haPrimary j) (hcop j).of_mul_right_left
      obtain ⟨b0,d0,hdet0,_,hb0,hd0,_⟩:=hcompletion (r j) (hr j)
        (hcop j).of_mul_right_right (hrPrimary j)
      refine ⟨(!![a j,b0;c*r j,d0]:Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {M})),?_⟩
      intro i hi
      have hs:sector i=sector j:=hi.trans hj.symm
      obtain ⟨b,d,hdet,_,hb,hd,hmat⟩:=exists_fixed_matrix_completion_controlled
        9 3 M c (a j) (r j) b0 d0 0 1 hc h9M h3M hdet0 (by simpa using hb0) hd0
        (a i) (r i) (ha i j hs) (hrr i j hs) (hr i) (hcop i).of_mul_right_right
      exact ⟨b,d,hdet,by simpa using hb,hd,hmat⟩
    · refine ⟨0,?_⟩
      intro i hi
      exact False.elim (hq ⟨i,hi⟩)
  choose C hC using hlocal
  have hi (i:ι):=hC (sector i) i rfl
  choose b d hdet hb hd hmat using hi
  exact ⟨b,d,C,hdet,hb,hd,hmat⟩

theorem exists_primary_denominator_sector_completions {ι Q:Type*}
    (M c:Eis) (h9M:(9:Eis)∣M) (hcPrimary:lambda^2∣c-1)
    (sector:ι→Q) (a r:ι→Eis) (hrPrimary:∀i,lambda^2∣r i-1)
    (hcop:∀i,IsCoprime (a i) (c*r i)) (hr:∀i,IsCoprime (r i) (M*c))
    (ha:∀i j,sector i=sector j→M*c∣a i-a j)
    (hrr:∀i j,sector i=sector j→M∣r i-r j) :
    ∃(b d:ι→Eis) (C:Q→Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {M})),
      (∀i,a i*d i-b i*(c*r i)=1) ∧ (∀i,(3:Eis)∣b i+1) ∧ (∀i,(9:Eis)∣d i) ∧
      ∀i,(!![a i,b i;c*r i,d i]:Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {M}))=C (sector i) := by
  have hc:c≠0:=primary_ne_zero c hcPrimary
  have h3M:(3:Eis)∣M:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9M
  have hlocal (q:Q) :
      ∃C:Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {M}),
      ∀i,sector i=q→∃b d:Eis,a i*d-b*(c*r i)=1 ∧ (3:Eis)∣b+1 ∧ (9:Eis)∣d ∧
        (!![a i,b;c*r i,d]:Matrix (Fin 2) (Fin 2) Eis).map
          (Ideal.Quotient.mk (Ideal.span {M}))=C := by
    by_cases hq:∃j,sector j=q
    · obtain ⟨j,hj⟩:=hq
      obtain ⟨inverse,_,_,hcompletion⟩:=exists_primary_denominator_completion M c (a j)
        h9M hcPrimary (hcop j).of_mul_right_left
      obtain ⟨b0,d0,hdet0,_,hd0,_,_,hb0,_⟩:=hcompletion (r j) (hr j)
        (hcop j).of_mul_right_right (hrPrimary j)
      refine ⟨(!![a j,b0;c*r j,d0]:Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {M})),?_⟩
      intro i hi
      have hs:sector i=sector j:=hi.trans hj.symm
      obtain ⟨b,d,hdet,_,hb,hd,hmat⟩:=exists_fixed_matrix_completion_controlled
        3 9 M c (a j) (r j) b0 d0 (-1) 0 hc h3M h9M hdet0
        (by simpa using hb0) (by simpa using hd0)
        (a i) (r i) (ha i j hs) (hrr i j hs) (hr i) (hcop i).of_mul_right_right
      exact ⟨b,d,hdet,by simpa using hb,by simpa using hd,hmat⟩
    · refine ⟨0,?_⟩
      intro i hi
      exact False.elim (hq ⟨i,hi⟩)
  choose C hC using hlocal
  have hi (i:ι):=hC (sector i) i rfl
  choose b d hdet hb hd hmat using hi
  exact ⟨b,d,C,hdet,hb,hd,hmat⟩

end ShortDraftCRT

open scoped Classical BigOperators

namespace CanonicalRowCompletion
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def coprimalityMask (m:Eis) : Eis→*ℂ where
  toFun n:=if IsCoprime m n then 1 else 0
  map_one' := by simp only [isCoprime_one_right,ite_true]
  map_mul' x y := by
    simp only [IsCoprime.mul_right_iff]
    by_cases hx:IsCoprime m x <;> by_cases hy:IsCoprime m y <;> simp [hx,hy]

lemma coprimalityMask_norm (m n:Eis) : ‖coprimalityMask m n‖≤1 := by
  change ‖if IsCoprime m n then (1:ℂ) else 0‖≤1
  split_ifs <;> norm_num

lemma isCoprime_congr_mod (m x y:Eis) (hxy:m∣x-y) : IsCoprime m x↔IsCoprime m y := by
  obtain ⟨z,hz⟩:=hxy
  constructor
  · rintro ⟨r,s,hrs⟩
    refine ⟨r+s*z,s,?_⟩
    linear_combination hrs-s*hz
  · rintro ⟨r,s,hrs⟩
    refine ⟨r-s*z,s,?_⟩
    linear_combination hrs+s*hz

lemma coprimalityMask_periodic (m:Eis) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {m}) (coprimalityMask m) := by
  intro x y hxy
  change (if IsCoprime m x then (1:ℂ) else 0)=(if IsCoprime m y then 1 else 0)
  rw [isCoprime_congr_mod m x y (Ideal.mem_span_singleton.mp hxy)]

lemma idealRowHom_prime_sixth_mask (m:Eis) (P:Ideal Eis) [P.IsMaximal] (hg:lambda∉P) :
    idealRowHom (m^6) P=if IsCoprime P (Ideal.span {m}) then 1 else 0 := by
  rw [idealRowHom_prime _ P hg]
  have hm:=canonicalSextic_sixth_power_mask P hg m
  rw [hm]
  rw [SixthPowerAverage.prime_coprime_span_iff]
  by_cases hm:m∈P <;> simp [hm]

theorem idealRowHom_sixth_mask (m:Eis) (I:Ideal Eis) (hI:Supported I) :
    idealRowHom (m^6) I=if IsCoprime I (Ideal.span {m}) then 1 else 0 := by
  have hprod (s:Multiset (Ideal Eis))
      (hs:∀P∈s,P.IsMaximal ∧ lambda∉P) :
      idealRowHom (m^6) s.prod=if IsCoprime s.prod (Ideal.span {m}) then 1 else 0 := by
    induction s using Multiset.induction_on with
    | empty =>
      change idealRowHom (m^6) 1=if IsCoprime (1:Ideal Eis) (Ideal.span {m}) then 1 else 0
      simp only [map_one,isCoprime_one_left,ite_true]
    | @cons P s ih =>
      have hp:=hs P (Multiset.mem_cons_self _ _)
      let:P.IsMaximal:=hp.1
      have ht:∀R∈s,R.IsMaximal ∧ lambda∉R:=fun R hR=>hs R (Multiset.mem_cons_of_mem hR)
      rw [Multiset.prod_cons,map_mul,idealRowHom_prime_sixth_mask m P hp.2,ih ht,
        IsCoprime.mul_left_iff]
      by_cases hP:IsCoprime P (Ideal.span {m}) <;>
        by_cases hS:IsCoprime s.prod (Ideal.span {m}) <;> simp [hP,hS]
  have h:=hprod (normalizedFactors I) (fun P hP=>
    ⟨(supported_factors_good I hI P hP).1,(supported_factors_good I hI P hP).2.1⟩)
  rwa [Ideal.prod_normalizedFactors_eq_self hI.1] at h

lemma idealRowHom_sixth_eq_mask (m n:Eis) (hn:Supported (Ideal.span {n})) :
    idealRowHom (m^6) (Ideal.span {n})=coprimalityMask m n := by
  rw [idealRowHom_sixth_mask m _ hn,Ideal.isCoprime_span_singleton_iff]
  change (if IsCoprime n m then (1:ℂ) else 0)=(if IsCoprime m n then 1 else 0)
  rw [isCoprime_comm]

lemma rowTwist_extract_sixth_mask (Ψ:Eis→*ℂ) (m f z n:Eis)
    (hn:Supported (Ideal.span {n})) :
    rowTwist Ψ m f z n=Ψ n*coprimalityMask m n*
      idealRowHom (f^4*z) (Ideal.span {n}) := by
  change Ψ n*idealRowHom (m^6*f^4*z) (Ideal.span {n})=_
  rw [show m^6*f^4*z=m^6*(f^4*z) by ring,idealRowHom_argument_mul,
    idealRowHom_sixth_eq_mask m n hn]
  ring

end CanonicalRowCompletion

open scoped BigOperators Classical MatrixGroups Matrix

namespace ShortDraftCusp

open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O

noncomputable local instance A4quotientField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P

end ShortDraftCusp

end

end OAI
end

section

namespace OAI

noncomputable section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace ShortDraftCusp
open scoped BigOperators Classical MatrixGroups Matrix

section
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase IdealGaussCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A4_bad_modulus_ne_zero (c0:Eis) (hc0:c0≠0) : ramifiedTraceLambda^3*c0≠0 := by
  apply mul_ne_zero _ hc0
  apply pow_ne_zero
  intro hz
  have he:=ramifiedEmbedding_traceLambda
  rw [hz,map_zero] at he
  exact eisLam_ne_zero he.symm

def A4BadPhase (c0:Eis) (hc0:c0≠0) (d U x:Eis) : ℂ :=
  quotientTrace (ramifiedTraceLambda^3*c0) (A4_bad_modulus_ne_zero c0 hc0)
    (Ideal.Quotient.mk _ (-d*U*x))

noncomputable local instance A4phaseField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P

end

open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
open CompletedGauss LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance A4frequencyField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P

end ShortDraftCusp

open scoped BigOperators Classical

namespace FiniteGaussPhase

section
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT IdealGaussCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem exists_product_trace_shifts {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i}))) :
    ∃k : ∀i,(Eis⧸Ideal.span {p i})ˣ,
      (∀i,Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)*(k i:Eis⧸Ideal.span {p i})=1) ∧
      ∀i,coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
        (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))) i=
          (quotientTrace (p i) (hp i)).mulShift (k i:Eis⧸Ideal.span {p i}) := by
  have hone (i : ι) : ∃k : (Eis⧸Ideal.span {p i})ˣ,
      Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)*(k:Eis⧸Ideal.span {p i})=1 ∧
      coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
        (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))) i=
          (quotientTrace (p i) (hp i)).mulShift (k:Eis⧸Ideal.span {p i}) := by
    obtain ⟨u,v,hbez⟩:=bezout_of_principal_coprime (cofactor_coprime p hcop i)
    have hv : Ideal.Quotient.mk (Ideal.span {p i}) v*
        Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)=1 := by
      simpa only [mul_comm] using bezout_inverse_left hbez
    refine ⟨Units.mkOfMulEqOne _ _ hv,?_,?_⟩
    · simpa only [Units.val_mkOfMulEqOne,mul_comm] using hv
    · exact coordinate_trace_character p hp hcop i u v hbez
  choose k hki hkψ using hone
  exact ⟨k,hki,hkψ⟩

noncomputable def productTraceShift {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i}))) :
    ∀i,(Eis⧸Ideal.span {p i})ˣ :=
  (exists_product_trace_shifts p hp hcop).choose

lemma productTraceShift_inverse {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i}))) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)*
      (productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})=1 :=
  (exists_product_trace_shifts p hp hcop).choose_spec.1 i

end

open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT IdealGaussCRT
local notation "Eis" => ActualEisensteinCubic.O

end FiniteGaussPhase

open scoped Classical BigOperators

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def A4PhaseFromResidue (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}) (x:Eis) : ℂ :=
  quotientTrace (ramifiedTraceLambda^3*c0) (A4_bad_modulus_ne_zero c0 hc0)
    (v*Ideal.Quotient.mk _ x)

end ShortDraftCusp

open scoped Classical BigOperators

namespace ShortDraftCRT
open ActualEisensteinCubic FiniteGaussPhase ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]

def finiteCrossNumerator (a c l:Eis) (p h:ι→Eis) : Eis :=
  a*(∏i,p i)+l^2*c*∑i,h i*cofactor p i

lemma prime_dvd_other_cofactor (p:ι→Eis) {i k:ι} (hik:i≠k) : p i∣cofactor p k := by
  exact Finset.dvd_prod_of_mem p (Finset.mem_erase.mpr ⟨hik,Finset.mem_univ i⟩)

lemma finiteCrossNumerator_local (a c l:Eis) (p h:ι→Eis) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) (finiteCrossNumerator a c l p h)=
      Ideal.Quotient.mk (Ideal.span {p i}) (l^2*c*cofactor p i)*
        Ideal.Quotient.mk (Ideal.span {p i}) (h i) := by
  let q:=Ideal.Quotient.mk (Ideal.span {p i})
  have hz:q (∏k,p k)=0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr ⟨cofactor p i, (prime_mul_cofactor p i).symm⟩
  have hs:(∑k,q (h k)*q (cofactor p k))=q (h i)*q (cofactor p i) := by
    apply Finset.sum_eq_single i
    · intro k hk hki
      have hk0:q (cofactor p k)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr (prime_dvd_other_cofactor p hki.symm))
      rw [hk0,mul_zero]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  change q (finiteCrossNumerator a c l p h)=q (l^2*c*cofactor p i)*q (h i)
  simp only [finiteCrossNumerator,map_add,map_mul,map_sum,map_pow,hz,mul_zero,zero_add,hs]
  ring

lemma finiteCrossNumerator_fixed (N a c l:Eis) (p h:ι→Eis)
    (hh:∀i,N∣h i) : N∣finiteCrossNumerator a c l p h-a*(∏i,p i) := by
  have hs:N∣∑i,h i*cofactor p i:=Finset.dvd_sum (fun i _=>dvd_mul_of_dvd_left (hh i) _)
  convert (preTransparency := .instances) dvd_mul_of_dvd_right hs (l^2*c) using 1 ; simp [finiteCrossNumerator]

lemma finiteCrossNumerator_fixed_sector {κ:Type*} [Fintype κ]
    (M a c l:Eis) (p h:ι→Eis) (p0 h0:κ→Eis)
    (hc:c∣M) (hh:∀i,M^2∣h i) (hh0:∀i,M^2∣h0 i)
    (hr:M^2∣(∏i,p i)-(∏i,p0 i)) :
    M*c∣finiteCrossNumerator a c l p h-finiteCrossNumerator a c l p0 h0 := by
  have hmc:M*c∣M^2:=by simpa only [pow_two] using mul_dvd_mul_left M hc
  apply hmc.trans
  have h1:=finiteCrossNumerator_fixed (M^2) a c l p h hh
  have h0:=finiteCrossNumerator_fixed (M^2) a c l p0 h0 hh0
  have h2:=dvd_mul_of_dvd_right hr a
  convert (preTransparency := .instances) dvd_sub (dvd_add h1 h2) h0 using 1 ; ring

lemma finiteCrossNumerator_coprime (a c l:Eis) (p h:ι→Eis)
    (hbase:IsCoprime a c) (hpair:Pairwise (Function.onFun IsCoprime p))
    (hc:∀i,IsCoprime c (p i)) (hl:∀i,IsCoprime l (p i))
    (hh:∀i,IsCoprime (h i) (p i)) :
    IsCoprime (finiteCrossNumerator a c l p h) (c*∏i,p i) := by
  have hmodc:c∣finiteCrossNumerator a c l p h-a*(∏i,p i):=by
    refine ⟨l^2*(∑i,h i*cofactor p i),?_⟩
    unfold finiteCrossNumerator
    ring
  have hcR:IsCoprime c (∏i,p i):=IsCoprime.prod_right (fun i _=>hc i)
  have hca:IsCoprime c (finiteCrossNumerator a c l p h):=
    (CanonicalRowCompletion.isCoprime_congr_mod c _ _ hmodc).mpr (hbase.symm.mul_right hcR)
  apply hca.symm.mul_right
  apply IsCoprime.prod_right
  intro i hi
  have hcof:IsCoprime (p i) (cofactor p i):=
    IsCoprime.prod_right (fun k hk=>hpair (Ne.symm (Finset.mem_erase.mp hk).1))
  have hterm:IsCoprime (p i) (l^2*c*cofactor p i*h i):=
    (((hl i).symm.pow_right : IsCoprime (p i) (l^2)).mul_right (hc i).symm).mul_right hcof |>.mul_right (hh i).symm
  have he:=finiteCrossNumerator_local a c l p h i
  rw [←map_mul] at he
  have hd:p i∣finiteCrossNumerator a c l p h-l^2*c*cofactor p i*h i:=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  exact ((CanonicalRowCompletion.isCoprime_congr_mod (p i) _ _ hd).mpr hterm).symm

end ShortDraftCRT

end

end OAI
end

section

namespace OAI

noncomputable section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped Classical BigOperators

namespace ShortDraftCRT
open ActualEisensteinCubic FiniteGaussPhase ConcreteTraceCRT CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]

omit [Fintype ι] in
theorem exists_strong_unit_frequency_lifts (M:Eis) (p:ι→Eis)
    (hM:∀i,IsCoprime M (p i)) (x:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    ∃h:ι→Eis,(∀i,M^2∣h i) ∧
      (∀i,Ideal.Quotient.mk (Ideal.span {p i}) (h i)=(x i:Eis⧸Ideal.span {p i})) ∧
      ∀i,IsCoprime (h i) (p i) := by
  have hx (i:ι) := exists_frequency_lift (M^2) (p i)
    (Quotient.out (x i:Eis⧸Ideal.span {p i})) (hM i).pow_left
  choose h hh hd using hx
  have he (i:ι):Ideal.Quotient.mk (Ideal.span {p i}) (h i)=(x i:Eis⧸Ideal.span {p i}) := by
    calc
      _=Ideal.Quotient.mk (Ideal.span {p i}) (Quotient.out (x i:Eis⧸Ideal.span {p i})) :=
        Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (hd i))
      _=x i:=Ideal.Quotient.mk_out _
  refine ⟨h,hh,he,?_⟩
  intro i
  apply IsCoprime.symm
  apply (isUnit_quotient_span_iff (p i) (h i)).mp
  rw [he]
  exact (x i).isUnit

end ShortDraftCRT

open scoped BigOperators Classical

namespace FixedRayActiveSet

def activeStratum {ι : Type*} [Fintype ι]
    (F : ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)] (A:Finset ι) :
    Finset (∀i,F i) := Finset.univ.filter (fun h=>∀i,h i≠0↔i∈A)

end FixedRayActiveSet

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def paperLambdaQuotient (h:Eis) : Eis :=
  if hh:ramifiedTraceLambda∣h then hh.choose else 0

def sourceCuspPhaseNumerator (j:Fin 3) (u h:Eis) : Eis :=
  if j=0 then ramifiedTraceLambda*u^2*h else -u^2*paperLambdaQuotient h

end CubicEisenstein

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve QuadraticAllOddCRT
open ConcreteTraceCRT UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def cubicTwoSupplement : Eis→*ℂ where
  toFun n:=(actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal n)
  map_one' := by simp
  map_mul' x y := by simp only [map_mul]

def quadraticTwoSupplement : Eis→*ℂ :=
  InitialMeanSquare.normCharacter (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ))

def twoSupplement : Eis→*ℂ := cubicTwoSupplement^2*quadraticTwoSupplement

lemma cubicTwoSupplement_norm (n:Eis) : ‖cubicTwoSupplement n‖≤1 := by
  change ‖(actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2)
    (Ideal.Quotient.mk cubicTwoIdeal n)‖≤1
  exact FiniteRayExpansion.norm_char_le_one _ _

lemma twoSupplement_norm (n:Eis) : ‖twoSupplement n‖≤1 := by
  change ‖cubicTwoSupplement n^2*quadraticTwoSupplement n‖≤1
  rw [norm_mul,norm_pow]
  apply (mul_le_of_le_one_left (norm_nonneg _)
    _).trans (InitialMeanSquare.normCharacter_norm_le_one _ n)
  exact pow_le_one₀ (norm_nonneg _) (cubicTwoSupplement_norm n)

lemma cubicTwoSupplement_periodic (x y:Eis) (hxy:x-y∈Ideal.span {(8:Eis)}) :
    cubicTwoSupplement x=cubicTwoSupplement y := by
  have h2:x-y∈cubicTwoIdeal:=by
    obtain ⟨k,hk⟩:=Ideal.mem_span_singleton.mp hxy
    apply Ideal.mem_span_singleton.mpr
    refine ⟨-4*k,?_⟩
    change x-y=(-2:Eis)*(-4*k)
    rw [hk]
    ring
  change (actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal x)=
    (actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal y)
  rw [Ideal.Quotient.eq.mpr h2]

lemma twoSupplement_periodic :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(8:Eis)}) twoSupplement := by
  intro x y hxy
  change cubicTwoSupplement x^2*quadraticTwoSupplement x=
    cubicTwoSupplement y^2*quadraticTwoSupplement y
  rw [cubicTwoSupplement_periodic x y hxy]
  congr 1
  exact CanonicalCoefficientClass.normCharacter_factorsModulo _ x y hxy

lemma idealRowHom_two_prime (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hs:Supported (Ideal.span {p})) :
    idealRowHom (2:Eis) (Ideal.span {p})=twoSupplement p := by
  let:(Ideal.span {p}).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  obtain ⟨hg,hc⟩:=supported_prime_data p hp hs
  have h2:idealRowHom (2:Eis) (Ideal.span {p})^2=cubicTwoSupplement p:=by
    rw [idealRowHom_prime _ _ hg]
    have he:=canonicalSextic_four_eq_fixed_two (Ideal.span {p}) hg p rfl hprimary
    have hfour:Ideal.Quotient.mk (Ideal.span {p}) (4:Eis)=
      (Ideal.Quotient.mk (Ideal.span {p}) (2:Eis))^2:=by norm_num [map_ofNat]
    rw [hfour,map_pow] at he
    change (actualSextic (Ideal.span {p}) hg) (Ideal.Quotient.mk _ 2)^2=
      (actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal p)
    rw [canonicalSextic_pow_two]
    exact he
  have h3:idealRowHom (2:Eis) (Ideal.span {p})^3=quadraticTwoSupplement p:=by
    rw [idealRowHom_prime _ _ hg,←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),actualSextic_cube_quadratic]
    change ((quadraticChar (Eis⧸Ideal.span {p}) (Ideal.Quotient.mk _ (2:Eis)):ℤ):ℂ)=_
    simp only [map_ofNat]
    rw [quadraticChar_two hc]
    have hn:Ideal.absNorm (Ideal.span {p})=Fintype.card (Eis⧸Ideal.span {p}):=by
      rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
    change ((ZMod.χ₈ (Fintype.card (Eis⧸Ideal.span {p})):ℤ):ℂ)=
      ((ZMod.χ₈ (Ideal.absNorm (Ideal.span {p})):ℤ):ℂ)
    rw [hn]
  have hn2:(2:Eis)∉Ideal.span {p}:=by
    intro hz
    have he: (2:Eis⧸Ideal.span {p})=0:=by
      simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr hz
    exact Ring.two_ne_zero hc he
  have h6:idealRowHom (2:Eis) (Ideal.span {p})^6=1:=by
    rw [idealRowHom_prime _ _ hg]
    have he:=canonicalSextic_sixth_power_mask (Ideal.span {p}) hg (2:Eis)
    change actualSextic _ hg (Ideal.Quotient.mk _ ((2:Eis)^6))=_ at he
    simpa only [map_pow,if_neg hn2] using he
  calc
    _=idealRowHom (2:Eis) (Ideal.span {p})*idealRowHom (2:Eis) (Ideal.span {p})^6:=by rw [h6,mul_one]
    _=idealRowHom (2:Eis) (Ideal.span {p})^3*(idealRowHom (2:Eis) (Ideal.span {p})^2)^2:=by ring
    _=twoSupplement p:=by
      rw [h2,h3]
      change quadraticTwoSupplement p*cubicTwoSupplement p^2=cubicTwoSupplement p^2*quadraticTwoSupplement p
      ring

theorem idealRowHom_two_formula (n:Eis) (hn:lambda^2∣n-1)
    (hs:Supported (Ideal.span {n})) :
    idealRowHom (2:Eis) (Ideal.span {n})=twoSupplement n := by
  have hn0:n≠0:=by intro hz;apply hs.1;simp [hz]
  obtain ⟨s,hprod,hfactors⟩:=exists_primary_prime_factorization n hn0 hn
  rw [←hprod] at hs ⊢
  clear hprod hn hn0 n
  induction s using Multiset.induction_on with
  | empty=>simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one]
  | @cons p s ih=>
    have hp:=hfactors p (Multiset.mem_cons_self _ _)
    have htail:∀q∈s,Prime q ∧ lambda^2∣q-1:=fun q hq=>hfactors q (Multiset.mem_cons_of_mem hq)
    have hsplit:Supported (Ideal.span {p}) ∧ Supported (Ideal.span {s.prod}):=by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,supported_mul_iff] using hs
    rw [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,map_mul,
      idealRowHom_two_prime p hp.1 hp.2 hsplit.1,ih hsplit.2 htail,map_mul]

end

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def supportedIdealRow (a:Eis) : Eis→*ℂ where
  toFun n:=if Supported (Ideal.span {n}) then idealRowHom a (Ideal.span {n}) else 0
  map_one' := by
    have hs:Supported (1:Ideal Eis):=⟨one_ne_zero,by
      intro P hP
      rw [normalizedFactors_one] at hP
      exact False.elim (Multiset.notMem_zero P hP)⟩
    rw [show Ideal.span {(1:Eis)}=(1:Ideal Eis) by simp only [Ideal.span_singleton_one,Ideal.one_eq_top],
      if_pos hs,map_one]
  map_mul' x y := by
    rw [←Ideal.span_singleton_mul_span_singleton,supported_mul_iff,map_mul]
    by_cases hx:Supported (Ideal.span {x}) <;> by_cases hy:Supported (Ideal.span {y}) <;> simp [hx,hy]

lemma supportedIdealRow_norm (a n:Eis) : ‖supportedIdealRow a n‖≤1 := by
  change ‖if _ then _ else _‖≤_
  split_ifs
  · exact idealRowHom_norm _ _
  · simp

lemma exists_supported_primary_unit (x:Eis) (hx:Supported (Ideal.span {x})) :
    ∃u:Eisˣ,lambda^2∣u.val*x-1 := by
  have hg:=supported_primaryGenerator_ne_zero (Ideal.span {x}) hx
  have hp:=primaryGenerator_spec (Ideal.span {x}) hg
  have ha:Associated x (primaryGenerator (Ideal.span {x})):=
    Ideal.span_singleton_eq_span_singleton.mp hp.1.symm
  obtain ⟨u,hu⟩:=ha
  refine ⟨u,?_⟩
  have he:u.val*x=primaryGenerator (Ideal.span {x}):=by simpa only [mul_comm] using hu
  rw [he]
  exact hp.2

theorem supportedIdealRow_lambda_periodic :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(36:Eis)}) (supportedIdealRow lambda) := by
  intro x y hxy
  have hs:=CanonicalUnitEuler.supported_span_congruent_mod_thirty_six x y hxy
  change (if Supported (Ideal.span {x}) then _ else 0)=
    (if Supported (Ideal.span {y}) then _ else 0)
  by_cases hx:Supported (Ideal.span {x})
  · have hy:=hs.mp hx
    rw [if_pos hx,if_pos hy]
    obtain ⟨u,hux⟩:=exists_supported_primary_unit x hx
    have h36:(36:Eis)∣u.val*x-u.val*y:=by
      convert (preTransparency := .instances) dvd_mul_of_dvd_right (Ideal.mem_span_singleton.mp hxy) u.val using 1 ; ring
    have hl:lambda^2∣u.val*x-u.val*y:=
      lambda_sq_dvd_three.trans ((show (3:Eis)∣36 from ⟨12,by norm_num⟩).trans h36)
    have huy:lambda^2∣u.val*y-1:=by
      convert (preTransparency := .instances) dvd_sub hux hl using 1 ; ring
    have hsp (z:Eis) : Ideal.span {u.val*z}=Ideal.span {z}:=
      Ideal.span_singleton_mul_left_unit u.isUnit z
    have he:=idealRowHom_lambda_mod_thirty_six (u.val*x) (u.val*y) hux huy
      (by rwa [hsp]) (by rwa [hsp]) h36
    simpa only [hsp] using he
  · rw [if_neg hx,if_neg (fun hy=>hx (hs.mpr hy))]

lemma supportedIdealRow_lambda_primary (n:Eis) (hs:Supported (Ideal.span {n})) :
    supportedIdealRow lambda n=idealRowHom lambda (Ideal.span {n}) := by
  change (if Supported (Ideal.span {n}) then _ else _)=_
  rw [if_pos hs]

end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

lemma negative_two_prime : Prime (-2:Eis) :=
  (Ideal.span_singleton_prime (by norm_num : (-2:Eis)≠0)).mp
    (show (Ideal.span {(-2:Eis)}).IsPrime from cubicTwoIdeal_isMaximal.isPrime)

theorem exists_supported_numerator_factorization (x:Eis) (hx:x≠0) :
    ∃u:Eisˣ,∃a b:ℕ,∃r:Eis,Supported (Ideal.span {r}) ∧ lambda^2∣r-1 ∧
      x=u.val*lambda^a*(2:Eis)^b*r := by
  obtain ⟨n,u,a,hn,hxform⟩:=CubicEisenstein.exists_primary_unit_lambda_factor x hx
  have hn0:n≠0:=by
    intro hz
    exact hx (by rw [hxform,hz,zero_mul])
  obtain ⟨r,hr,hrnot⟩:=(FiniteMultiplicity.of_prime_left negative_two_prime hn0).exists_eq_pow_mul_and_not_dvd
  let b:ℕ:=multiplicity (-2:Eis) n
  change n=(-2:Eis)^b*r at hr
  have hp:lambda^2∣(-2:Eis)^b-1:=neg_two_primary.trans (sub_one_dvd_pow_sub_one (-2:Eis) b)
  have hprimary:lambda^2∣r-1:=by
    have hh:=dvd_sub hn (dvd_mul_of_dvd_left hp r)
    have he:n-1-(((-2:Eis)^b-1)*r)=r-1:=by rw [hr];ring
    rwa [he] at hh
  have hnot2:¬(2:Eis)∣r:=by
    intro h2
    exact hrnot (by simpa only [neg_dvd] using h2)
  have hnotlambda:¬lambda∣r:=by
    intro hLam
    have hsub:lambda∣r-1:=(dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans hprimary
    have hone:lambda∣(1:Eis):=by
      convert (preTransparency := .instances) dvd_sub hLam hsub using 1 ; ring
    exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (isUnit_of_dvd_one hone)
  let v:Eisˣ:=u*(-1:Eisˣ)^b
  refine ⟨v,a,b,r,(supported_span_iff r).mpr ⟨hnotlambda,hnot2⟩,hprimary,?_⟩
  have hp2:(-2:Eis)^b=(-1:Eis)^b*(2:Eis)^b:=by
    rw [show (-2:Eis)=(-1)*2 by ring,mul_pow]
  rw [hxform,hr,hp2]
  dsimp only [v]
  simp only [Units.val_mul,Units.val_pow_eq_pow_val,Units.coe_neg_one]
  ring

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalUnitEuler
local notation "Eis" => ActualEisensteinCubic.O

lemma idealRowHom_argument_pow (a:Eis) (k:ℕ) (I:Ideal Eis) (hI:Supported I) :
    idealRowHom (a^k) I=(idealRowHom a I)^k := by
  induction k with
  | zero => simpa only [pow_zero] using idealRowHom_one_supported I hI
  | succ k ih => rw [pow_succ,idealRowHom_argument_mul,ih,pow_succ]

def reciprocityPhaseMonoid (r:Eis) (hr:Supported (Ideal.span {r})) : Eis→*ℂ where
  toFun n:=sexticReciprocityPhase r n
  map_one' := sexticReciprocityPhase_one_right r hr
  map_mul' := sexticReciprocityPhase_mul_right r

def numeratorBadTwist (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) : Eis→*ℂ :=
  unitSupplement u * supportedIdealRow lambda^a * twoSupplement^b * reciprocityPhaseMonoid r hr

lemma numeratorBadTwist_norm (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) (n:Eis) : ‖numeratorBadTwist u a b r hr n‖≤1 := by
  change ‖((unitSupplement u n * (supportedIdealRow lambda n)^a) * (twoSupplement n)^b) *
    sexticReciprocityPhase r n‖≤1
  simp only [norm_mul,norm_pow]
  have hu:=unitSupplement_norm u n
  have ha:‖supportedIdealRow lambda n‖^a≤1:=
    pow_le_one₀ (norm_nonneg _) (supportedIdealRow_norm lambda n)
  have hb:‖twoSupplement n‖^b≤1:=
    pow_le_one₀ (norm_nonneg _) (twoSupplement_norm n)
  have hrn:=sexticReciprocityPhase_norm r n
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _)
    ((mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) hu).trans ha)).trans hb)).trans hrn

lemma numeratorBadTwist_periodic (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(72:Eis)}) (numeratorBadTwist u a b r hr) := by
  intro x y hxy
  have h72:(72:Eis)∣x-y:=Ideal.mem_span_singleton.mp hxy
  have h36:x-y∈(Ideal.span {(36:Eis)}:Ideal Eis):=
    Ideal.mem_span_singleton.mpr ((show (36:Eis)∣72 from ⟨2,by norm_num⟩).trans h72)
  have h8:x-y∈(Ideal.span {(8:Eis)}:Ideal Eis):=
    Ideal.mem_span_singleton.mpr ((show (8:Eis)∣72 from ⟨9,by norm_num⟩).trans h72)
  have h4:(4:Eis)∣x-y:=(show (4:Eis)∣72 from ⟨18,by norm_num⟩).trans h72
  change ((unitSupplement u x * (supportedIdealRow lambda x)^a) * (twoSupplement x)^b) *
      sexticReciprocityPhase r x =
    ((unitSupplement u y * (supportedIdealRow lambda y)^a) * (twoSupplement y)^b) *
      sexticReciprocityPhase r y
  rw [unitSupplement_periodic u x y h36,supportedIdealRow_lambda_periodic x y h36,
    twoSupplement_periodic x y h8,sexticReciprocityPhase_congr_right r x y h4]

def movingNumeratorRow (r:Eis) (hr:Supported (Ideal.span {r})) : Eis→*ℂ where
  toFun n:=idealRowHom n (Ideal.span {r})
  map_one' := idealRowHom_one_supported _ hr
  map_mul' a b := idealRowHom_argument_mul a b _

lemma movingNumeratorRow_norm (r:Eis) (hr:Supported (Ideal.span {r})) (n:Eis) :
    ‖movingNumeratorRow r hr n‖≤1 := idealRowHom_norm n _

lemma movingNumeratorRow_periodic (r:Eis) (hr:Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {r}) (movingNumeratorRow r hr) :=
  idealRowHom_congr_mod _

theorem idealRowHom_factor_numerator (u:Eisˣ) (a b:ℕ) (r n:Eis)
    (hr:Supported (Ideal.span {r})) (hpr:lambda^2∣r-1)
    (hn:Supported (Ideal.span {n})) (hpn:lambda^2∣n-1) :
    idealRowHom (u.val*lambda^a*(2:Eis)^b*r) (Ideal.span {n})=
      numeratorBadTwist u a b r hr n * movingNumeratorRow r hr n := by
  have hu:unitSupplement u n=idealRowHom u.val (Ideal.span {n}):=by
    change (if Supported (Ideal.span {n}) then _ else 0)=_
    rw [if_pos hn]
  have hrec:=reciprocalRow_eq_idealRowHom r n hr hn hpr hpn
  change sexticReciprocityPhase r n*idealRowHom n (Ideal.span {r})=
    idealRowHom r (Ideal.span {n}) at hrec
  change _=(((unitSupplement u n * (supportedIdealRow lambda n)^a) * (twoSupplement n)^b) *
    sexticReciprocityPhase r n)*idealRowHom n (Ideal.span {r})
  rw [idealRowHom_argument_mul,idealRowHom_argument_mul,idealRowHom_argument_mul,
    idealRowHom_argument_pow _ _ _ hn,idealRowHom_argument_pow _ _ _ hn,
    hu,supportedIdealRow_lambda_primary n hn,←idealRowHom_two_formula n hpn hn,←hrec]
  ring

end CanonicalRowCompletion

end

end OAI
end

section

namespace OAI

noncomputable section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalUnitEuler
local notation "Eis" => ActualEisensteinCubic.O

lemma numeratorBadTwist_zero_of_not_supported (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) (n:Eis) (hn:¬Supported (Ideal.span {n})) :
    numeratorBadTwist u a b r hr n=0 := by
  have hu:unitSupplement u n=0:=by
    change (if Supported (Ideal.span {n}) then _ else 0)=0
    rw [if_neg hn]
  change ((unitSupplement u n * (supportedIdealRow lambda n)^a) * (twoSupplement n)^b) *
    sexticReciprocityPhase r n=0
  rw [hu,zero_mul,zero_mul,zero_mul]

lemma rowTwist_zero_of_not_supported (Ψ:Eis→*ℂ) (m f z n:Eis)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m) (hn:¬Supported (Ideal.span {n})) :
    rowTwist Ψ m f z n=0 := by
  have hu:unitSupplement (1:Eisˣ) n=0:=by
    change (if Supported (Ideal.span {n}) then _ else 0)=0
    rw [if_neg hn]
  have h:=congrArg (fun T:Eis→*ℂ=>T n) (rowTwist_unitSupplement Ψ m f z (1:Eisˣ) hmLam hm2)
  change rowTwist Ψ m f ((1:Eisˣ).val*z) n=unitSupplement (1:Eisˣ) n*rowTwist Ψ m f z n at h
  simpa only [Units.val_one,one_mul,hu,zero_mul] using h

def actualPeriodicRow (Ψ:Eis→*ℂ) (m:Eis) (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) : Eis→*ℂ :=
  Ψ * coprimalityMask m * numeratorBadTwist u a b r hr * movingNumeratorRow r hr

lemma actualPeriodicRow_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (m:Eis) (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) (n:Eis) :
    ‖actualPeriodicRow Ψ m u a b r hr n‖≤1 := by
  change ‖((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*movingNumeratorRow r hr n‖≤1
  simp only [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _)
    (hΨ n)).trans (coprimalityMask_norm m n))).trans (numeratorBadTwist_norm u a b r hr n))).trans
    (movingNumeratorRow_norm r hr n)

lemma actualPeriodicRow_periodic (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (m:Eis) (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo
      (Q*Ideal.span {m}*Ideal.span {(72:Eis)}*Ideal.span {r})
      (actualPeriodicRow Ψ m u a b r hr) := by
  intro x y hxy
  have hQ:x-y∈Q:=Ideal.mul_le_left (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have hm:x-y∈Ideal.span {m}:=Ideal.mul_le_right (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have h72:x-y∈Ideal.span {(72:Eis)}:=Ideal.mul_le_right (Ideal.mul_le_left hxy)
  have hrxy:x-y∈Ideal.span {r}:=Ideal.mul_le_right hxy
  change ((Ψ x*coprimalityMask m x)*numeratorBadTwist u a b r hr x)*movingNumeratorRow r hr x=
    ((Ψ y*coprimalityMask m y)*numeratorBadTwist u a b r hr y)*movingNumeratorRow r hr y
  rw [hΨ x y hQ,coprimalityMask_periodic m x y hm,numeratorBadTwist_periodic u a b r hr x y h72,
    movingNumeratorRow_periodic r hr x y hrxy]

theorem rowTwist_eq_actualPeriodicRow_primary (Ψ:Eis→*ℂ) (m f z:Eis)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m) (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) (hpr:lambda^2∣r-1)
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (n:Eis) (hpn:lambda^2∣n-1) :
    rowTwist Ψ m f z n=actualPeriodicRow Ψ m u a b r hr n := by
  by_cases hn:Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask Ψ m f z n hn,hx,
      idealRowHom_factor_numerator u a b r n hr hpr hn hpn]
    change _=((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*movingNumeratorRow r hr n
    ring
  · rw [rowTwist_zero_of_not_supported Ψ m f z n hmLam hm2 hn]
    change 0=((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*movingNumeratorRow r hr n
    rw [numeratorBadTwist_zero_of_not_supported u a b r hr n hn,mul_zero,zero_mul]

theorem exists_actual_periodic_row (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hQ:Q≠0) (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(u:Eisˣ)(a b:ℕ)(r:Eis)(hr:Supported (Ideal.span {r})),
      lambda^2∣r-1 ∧ f^4*z=u.val*lambda^a*(2:Eis)^b*r ∧
      (Q*Ideal.span {m}*Ideal.span {(72:Eis)}*Ideal.span {r})≠0 ∧
      CanonicalCoefficientClass.FactorsModulo
        (Q*Ideal.span {m}*Ideal.span {(72:Eis)}*Ideal.span {r})
        (actualPeriodicRow Ψ m u a b r hr) ∧
      (∀n,‖actualPeriodicRow Ψ m u a b r hr n‖≤1) ∧
      (∀n,lambda^2∣n-1 → rowTwist Ψ m f z n=actualPeriodicRow Ψ m u a b r hr n) := by
  obtain ⟨u,a,b,r,hr,hpr,hx⟩:=exists_supported_numerator_factorization (f^4*z)
    (mul_ne_zero (pow_ne_zero _ hf) hz)
  refine ⟨u,a,b,r,hr,hpr,hx,?_,actualPeriodicRow_periodic Ψ Q hΨ m u a b r hr,
    actualPeriodicRow_norm Ψ hΨnorm m u a b r hr,?_⟩
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero hQ (by
      simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hm))
      (by simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot];norm_num)) hr.1
  · exact fun n hpn=>rowTwist_eq_actualPeriodicRow_primary Ψ m f z hmLam hm2 u a b r hr hpr hx n hpn

end CanonicalRowCompletion

namespace CompletedGauss

section
open ActualEisensteinCubic IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def completedReflectionPool (I Q:Ideal Eis) : Finset (Ideal Eis) :=
  (primeSupport (I*Q)).filter (fun P=>lambda∉P ∧ ringChar (Eis⧸P)≠2 ∧ ¬P∣rowResidualPart I Q)

lemma mem_completedReflectionPool (I Q P:Ideal Eis) (hI:I≠0) (hQ:Q≠0) :
    P∈completedReflectionPool I Q ↔
      Prime P ∧ P∣I*Q ∧ lambda∉P ∧ ringChar (Eis⧸P)≠2 ∧ ¬P∣rowResidualPart I Q := by
  simp only [completedReflectionPool,Finset.mem_filter,primeSupport,Multiset.mem_toFinset,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff (mul_ne_zero hI hQ)]
  aesop

lemma completedReflectionPool_maximal (I Q:Ideal Eis) (P:completedReflectionPool I Q) :
    P.val.IsMaximal := by
  have hm: P.val∈normalizedFactors (I*Q):=
    Multiset.mem_toFinset.mp (Finset.mem_filter.mp P.property).1
  have hp:=prime_of_normalized_factor P.val hm
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

lemma completedReflectionPool_good (I Q:Ideal Eis) (P:completedReflectionPool I Q) :
    lambda∉P.val := (Finset.mem_filter.mp P.property).2.1

lemma completedReflectionPool_nonresidual (I Q:Ideal Eis) (P:completedReflectionPool I Q) :
    ¬P.val∣rowResidualPart I Q := (Finset.mem_filter.mp P.property).2.2.2

theorem completedReflectionPool_eq_on_fiber (I J Q:Ideal Eis)
    (hI:I≠0) (hJ:J≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I Q=rowMaskPart J Q) :
    completedReflectionPool I Q=completedReflectionPool J Q := by
  ext P
  rw [mem_completedReflectionPool I Q P hI hQ,mem_completedReflectionPool J Q P hJ hQ]
  constructor
  · rintro ⟨hP,hdiv,hgood,hodd,hres⟩
    obtain ⟨hdivJ,hresJ,_⟩:=nonresidual_prime_transport I J 1 Q P hI hJ hP hA hT hdiv hres
    exact ⟨hP,hdivJ,hgood,hodd,hresJ⟩
  · rintro ⟨hP,hdiv,hgood,hodd,hres⟩
    obtain ⟨hdivI,hresI,_⟩:=nonresidual_prime_transport J I 1 Q P hJ hI hP hA.symm hT.symm hdiv hres
    exact ⟨hP,hdivI,hgood,hodd,hresI⟩

end

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss

end

end OAI
end

section

namespace OAI

noncomputable section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma actualSextic_sixth_one (P:Ideal Eis) [P.IsMaximal] (hg:lambda∉P) :
    actualSextic P hg^6=1 := by
  apply MulChar.ext
  intro t
  obtain ⟨n,hn⟩:=Ideal.Quotient.mk_surjective (t:Eis⧸P)
  have hnot:n∉P:=by
    intro hm
    have ht:(t:Eis⧸P)=0:=by rw [←hn];exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
    exact t.ne_zero ht
  have h:=canonicalSextic_sixth_power_mask P hg n
  change actualSextic P hg (Ideal.Quotient.mk P (n^6))=_ at h
  rw [map_pow,map_pow,if_neg hnot] at h
  rw [MulChar.pow_apply_coe,MulChar.one_apply_coe,←hn]
  exact h

lemma primeIndex_pairwise_coprime (I:Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (fun P:PrimeIndex I=>P.val)) := by
  intro P Q hPQ
  exact Ideal.isCoprime_of_isMaximal (fun he=>hPQ (Subtype.ext he))

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalUnitEuler
local notation "Eis" => ActualEisensteinCubic.O

end CanonicalRowCompletion

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance A4unitsField (P:Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P

theorem exists_A4_local_units {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (c0 U w:Eis) (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1) :
    ∃σ ε:∀i,(Eis⧸Ideal.span {p i})ˣ,
      (∀i,(σ i:Eis⧸Ideal.span {p i})=
        Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^2*c0*cofactor p i)) ∧
      ∀i,Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i)*
        (σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1 := by
  have hone (i:ι) : ∃σ ε:(Eis⧸Ideal.span {p i})ˣ,
      (σ:Eis⧸Ideal.span {p i})=Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^2*c0*cofactor p i) ∧
      Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i)*
        (σ:Eis⧸Ideal.span {p i})*(ε:Eis⧸Ideal.span {p i})=-1 := by
    let q:=Ideal.Quotient.mk (Ideal.span {p i})
    have hz:q (∏k,p k)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem p (Finset.mem_univ i)))
    have hb:q (ramifiedTraceLambda^3*c0)*q w=1 := by
      have he:=congrArg q hbez
      simp only [map_add,map_mul,map_pow,map_one,hz,mul_zero,zero_add] at he
      simpa only [map_mul,map_pow,mul_assoc,mul_comm,mul_left_comm] using he
    have hb0:q (ramifiedTraceLambda^3*c0)≠0 := by
      intro he
      rw [he,zero_mul] at hb
      exact zero_ne_one hb
    have hc0:q (cofactor p i)≠0 := by
      intro he
      have hi:=productTraceShift_inverse p hp hcop i
      change q (cofactor p i)*_=1 at hi
      rw [he,zero_mul] at hi
      exact zero_ne_one hi
    have hB:q (ramifiedTraceLambda^3*c0*cofactor p i)≠0 := by
      rw [map_mul]
      exact mul_ne_zero hb0 hc0
    have hS:q (ramifiedTraceLambda^2*c0*cofactor p i)≠0 := by
      intro he
      apply hB
      calc
        _=q ramifiedTraceLambda*q (ramifiedTraceLambda^2*c0*cofactor p i) := by
          simp only [map_mul,map_pow]
          ring
        _=0:=by rw [he,mul_zero]
    let σ:(Eis⧸Ideal.span {p i})ˣ:=Units.mk0 _ hS
    let B:(Eis⧸Ideal.span {p i})ˣ:=Units.mk0 _ hB
    refine ⟨σ,-(B*σ)⁻¹,rfl,?_⟩
    have hcancel:=congrArg (fun u:(Eis⧸Ideal.span {p i})ˣ=>(u:Eis⧸Ideal.span {p i}))
      (mul_inv_cancel (B*σ))
    simpa only [B,Units.val_mk0,Units.val_mul,Units.val_one,Units.val_neg,mul_neg] using congrArg Neg.neg hcancel
  choose σ ε hσ hε using hone
  exact ⟨σ,ε,hσ,hε⟩

end ShortDraftCusp

open scoped Classical BigOperators MatrixGroups

namespace ShortDraftCRT
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT PrimaryIdealUnitReindex
local notation "Eis" => ActualEisensteinCubic.O

lemma exists_primary_unit_multiple (x:Eis) (hx:¬lambda∣x) :
    ∃u:Eisˣ,lambda^2∣u.val*x-1 := by
  have hg:primaryGenerator (Ideal.span {x})≠0:=primaryGenerator_span_ne_zero_iff x |>.mpr hx
  have hspec:=primaryGenerator_spec (Ideal.span {x}) hg
  have ha:Associated x (primaryGenerator (Ideal.span {x})):=
    Ideal.span_singleton_eq_span_singleton.mp hspec.1.symm
  obtain ⟨u,hu⟩:=ha
  refine ⟨u,?_⟩
  rw [mul_comm,hu]
  exact hspec.2

lemma normalize_coprime_pair (a c:Eis) (hcop:IsCoprime a c) :
    ∃u:Eisˣ,IsCoprime (u.val*a) (u.val*c) ∧
      (lambda∣u.val*c→lambda^2∣u.val*a-1) ∧
      (¬lambda∣u.val*c→lambda^2∣u.val*c-1) := by
  have hunit (u:Eisˣ):IsCoprime (u.val*a) (u.val*c) := by
    obtain ⟨r,s,hrs⟩:=hcop
    refine ⟨r*(↑u⁻¹:Eis),s*(↑u⁻¹:Eis),?_⟩
    calc
      _=((↑u⁻¹:Eis)*u.val)*(r*a+s*c):=by ring
      _=1:=by rw [Units.inv_mul,hrs,mul_one]
  have hd (u:Eisˣ):lambda∣u.val*c↔lambda∣c := by
    constructor
    · intro h
      have hh:=dvd_mul_of_dvd_right h (↑u⁻¹:Eis)
      simpa only [←mul_assoc,Units.inv_mul,one_mul] using hh
    · intro h
      exact dvd_mul_of_dvd_right h u.val
  by_cases hc:lambda∣c
  · have ha:¬lambda∣a:=fun h=>lambda_prime_actual.not_isUnit (hcop.isUnit_of_dvd' h hc)
    obtain ⟨u,hu⟩:=exists_primary_unit_multiple a ha
    exact ⟨u,hunit u,fun _=>hu,fun hn=>False.elim (hn ((hd u).mpr hc))⟩
  · obtain ⟨u,hu⟩:=exists_primary_unit_multiple c hc
    exact ⟨u,hunit u,fun h=>False.elim (hc ((hd u).mp h)),fun _=>hu⟩

theorem exists_normalized_rational_cusp (a c:Eis) (hc:c≠0) :
    ∃a0 c0:Eis,c0≠0 ∧ c0∣c ∧ IsCoprime a0 c0 ∧
      eisEmbedding a0/eisEmbedding c0=eisEmbedding a/eisEmbedding c ∧
      (lambda∣c0→lambda^2∣a0-1) ∧ (¬lambda∣c0→lambda^2∣c0-1) := by
  let d:Eis:=IsBezout.gcd a c
  obtain ⟨a',ha⟩:=IsBezout.gcd_dvd_left a c
  obtain ⟨c',hc'⟩:=IsBezout.gcd_dvd_right a c
  change a=d*a' at ha
  change c=d*c' at hc'
  have hd:d≠0:=by intro hz; exact hc (by rw [hc',hz,zero_mul])
  have hcp:c'≠0:=by intro hz; exact hc (by rw [hc',hz,mul_zero])
  obtain ⟨r,s,hrs⟩:=IsBezout.gcd_eq_sum a c
  have hred:IsCoprime a' c':=by
    refine ⟨r,s,?_⟩
    apply mul_left_cancel₀ hd
    change d*(r*a'+s*c')=d*1
    calc
      _=r*a+s*c:=by rw [ha,hc'];ring
      _=d:=hrs
      _=_:=by ring
  obtain ⟨u,hu,hua,huc⟩:=normalize_coprime_pair a' c' hred
  refine ⟨u.val*a',u.val*c',mul_ne_zero u.ne_zero hcp,?_,hu,?_,hua,huc⟩
  · refine ⟨d*(↑u⁻¹:Eis),?_⟩
    rw [hc']
    calc
      d*c'=((u.val*(↑u⁻¹:Eis))*d)*c':=by rw [Units.mul_inv,one_mul]
      _=_:=by ring
  · rw [ha,hc',map_mul,map_mul,map_mul,map_mul]
    have he:=eisEmbedding_ne_zero hd
    have hf:=eisEmbedding_ne_zero hcp
    have hu0:=eisEmbedding_ne_zero u.ne_zero
    field_simp

end ShortDraftCRT

end

end OAI
end

section

namespace OAI

noncomputable section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped Classical

namespace CubicEisenstein

section
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O

lemma A4_traceLambda_pow_four : ramifiedTraceLambda^4=(9:Eis) := by
  apply eisEmbedding_injective
  rw [map_pow,map_ofNat,ramifiedEmbedding_traceLambda]
  calc
    _=(eisLam^2)^2:=by ring
    _=9:=by rw [TraceLambdaPhase.eisLam_sq];norm_num

structure PrincipalStratumArithmetic {ι:Type*} [Fintype ι]
    (p:ι→Eis) (N a0 c0:Eis) where
  lift : (∀i,(Eis⧸Ideal.span {p i})ˣ)→ι→Eis
  lift_period : ∀v i,N^2∣lift v i
  lift_residue : ∀v i,Ideal.Quotient.mk (Ideal.span {p i}) (lift v i)=(v i:Eis⧸Ideal.span {p i})
  U : Eis
  w : Eis
  bezout : U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1
  sigma : ∀i,(Eis⧸Ideal.span {p i})ˣ
  epsilon : ∀i,(Eis⧸Ideal.span {p i})ˣ
  sigma_value : ∀i,(sigma i:Eis⧸Ideal.span {p i})=
    Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^2*c0*cofactor p i)
  epsilon_value : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i)*
    (sigma i:Eis⧸Ideal.span {p i})*(epsilon i:Eis⧸Ideal.span {p i})=-1
  gamma : (∀i,(Eis⧸Ideal.span {p i})ˣ)→levelThree
  numerator : ∀v,(gamma v:SL(2,Eis)) 0 0=finiteCrossNumerator a0 c0 ramifiedTraceLambda p (lift v)
  denominator : ∀v,(gamma v:SL(2,Eis)) 1 0=c0*∏i,p i
  numerator_fixed : ∀v,(9:Eis)*c0∣(gamma v:SL(2,Eis)) 0 0-(gamma (fun _=>1):SL(2,Eis)) 0 0
  inverse_fixed : ∀v,ramifiedTraceLambda^3*c0∣(gamma v:SL(2,Eis)) 1 1-(gamma (fun _=>1):SL(2,Eis)) 1 1

end

open scoped BigOperators Classical ContDiff MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CompletedDyadic
open CubicKubota CubicJacobiGlobal ShortDraftCusp LocalReflectionBrackets FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

open scoped BigOperators Classical

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

abbrev BasePrimeIndex (I Q:Ideal Eis) := {P:PrimeIndex I // Q≤P.val}
abbrev FreePrimeIndex (I Q:Ideal Eis) := {P:PrimeIndex I // ¬Q≤P.val}

def basePrimeRow (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) : Eis→*ℂ where
  toFun n:=∏P:BasePrimeIndex I Q,
    (actualSextic P.val.val ((supported_factors_good I hI P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.1)^((normalizedFactors I).count P.val.val%6))
        (Ideal.Quotient.mk P.val.val n)
  map_one' := by simp only [map_one,Finset.prod_const_one]
  map_mul' x y := by simp only [map_mul,Finset.prod_mul_distrib]

def freePrimeRow (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) : Eis→*ℂ where
  toFun n:=∏P:FreePrimeIndex I Q,
    (actualSextic P.val.val ((supported_factors_good I hI P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.1)^((normalizedFactors I).count P.val.val%6))
        (Ideal.Quotient.mk P.val.val n)
  map_one' := by simp only [map_one,Finset.prod_const_one]
  map_mul' x y := by simp only [map_mul,Finset.prod_mul_distrib]

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
open ConcretePrimeRowBridge
local notation "Eis" => ActualEisensteinCubic.O

def goodMaskMovingIdeal (g r:Eis) : Ideal Eis := (Ideal.span {g})^6*Ideal.span {r}

lemma goodMaskMovingIdeal_supported (g r:Eis)
    (hg:Supported (Ideal.span {g})) (hr:Supported (Ideal.span {r})) :
    Supported (goodMaskMovingIdeal g r) := by
  exact (supported_mul_iff _ _).mpr ⟨supported_pow hg 6,hr⟩

lemma good_odd_prime_two_not_mem (P:Ideal Eis) [P.IsMaximal]
    (hodd:ringChar (Eis⧸P)≠2) : (2:Eis)∉P := by
  intro ht
  have he:=maximal_ideal_eq_span_of_mem P inferInstance (2:Eis) twoIdeal_maximal ht
  exact hodd (he ▸ twoIdeal_characteristic)

lemma count_span_eq_zero_of_not_mem (P:Ideal Eis) (x:Eis) (hx:x∉P) :
    (normalizedFactors (Ideal.span {x})).count P=0 := by
  apply Multiset.count_eq_zero.mpr
  intro hm
  have h0:(Ideal.span {x}:Ideal Eis)≠0:=by
    apply Ideal.span_singleton_eq_bot.not.mpr
    intro he
    exact hx (he ▸ P.zero_mem)
  exact hx (Ideal.dvd_span_singleton.mp
    ((UniqueFactorizationMonoid.mem_normalizedFactors_iff h0).mp hm).2)

lemma good_factor_count (P:Ideal Eis) [P.IsMaximal]
    (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) :
    (normalizedFactors (Ideal.span {u.val*lambda^a*(2:Eis)^b*r})).count P=
      (normalizedFactors (Ideal.span {r})).count P := by
  have hl:(Ideal.span {lambda}:Ideal Eis)≠0:=
    Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero
  have ht:(Ideal.span {(2:Eis)}:Ideal Eis)≠0:=Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  have hcl:=count_span_eq_zero_of_not_mem P lambda hgood
  have hct:=count_span_eq_zero_of_not_mem P 2 (good_odd_prime_two_not_mem P hodd)
  rw [show u.val*lambda^a*(2:Eis)^b*r=u.val*(lambda^a*(2:Eis)^b*r) by ring,
    Ideal.span_singleton_mul_left_unit u.isUnit,
    ←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_mul_span_singleton,
    ←Ideal.span_singleton_pow,←Ideal.span_singleton_pow,
    normalizedFactors_mul (mul_ne_zero (pow_ne_zero _ hl) (pow_ne_zero _ ht)) hr.1,
    normalizedFactors_mul (pow_ne_zero _ hl) (pow_ne_zero _ ht)]
  simp only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul,hcl,hct,mul_zero,zero_add]

theorem goodMaskMovingIdeal_count (I F:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (P:Ideal Eis) [P.IsMaximal] (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P=
      6*(normalizedFactors (Ideal.span {m})).count P+
        4*(normalizedFactors F).count P+(normalizedFactors I).count P := by
  have hmc:(normalizedFactors (Ideal.span {m})).count P=(normalizedFactors (Ideal.span {g})).count P:=by
    rw [hm]
    exact good_factor_count P hgood hodd um am bm g hg
  have hrc:(normalizedFactors (Ideal.span {r})).count P=
      4*(normalizedFactors F).count P+(normalizedFactors I).count P:=by
    have hh:=good_factor_count P hgood hodd u a b r hr
    rw [←hx,←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_pow,hf,hz,
      normalizedFactors_mul (pow_ne_zero 4 hF) hI] at hh
    simpa only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul] using hh.symm
  rw [goodMaskMovingIdeal,normalizedFactors_mul (pow_ne_zero 6 hg.1) hr.1]
  simp only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul,←hmc,hrc]
  omega

end CanonicalRowCompletion

end

end OAI
end

section

namespace OAI

noncomputable section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
local notation "Eis" => ActualEisensteinCubic.O

def fixedThetaRowCoeff (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (h:Eis⧸Ideal.span {c}) : ℂ :=
  finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient φ c) h

end CubicEisenstein

namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

lemma admissiblePrimeGood (K:Ideal Eis) (hK:Admissible K) (P:PrimeIndex K) : lambda∉P.val :=
  (hK.2.2 P.val (Multiset.mem_toFinset.mp P.property)).1

end

open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss

open scoped Classical BigOperators ContDiff

namespace CompletedGauss.FreeReflection

section
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

def pool (I Q Q0:Ideal Eis) : Finset (Ideal Eis) :=
  (completedReflectionPool I Q).filter (fun P=>¬Q0≤P)

lemma pool_subset (I Q Q0:Ideal Eis) : pool I Q Q0⊆completedReflectionPool I Q :=
  Finset.filter_subset _ _
lemma pool_maximal (I Q Q0:Ideal Eis) (P:pool I Q Q0) : P.val.IsMaximal :=
  completedReflectionPool_maximal I Q ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_good (I Q Q0:Ideal Eis) (P:pool I Q Q0) : lambda∉P.val :=
  completedReflectionPool_good I Q ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_nonresidual (I Q Q0:Ideal Eis) (P:pool I Q Q0) : ¬P.val∣rowResidualPart I Q :=
  completedReflectionPool_nonresidual I Q ⟨P.val,pool_subset I Q Q0 P.property⟩

lemma pool_eq_on_fiber (I J Q Q0:Ideal Eis) (hI:I≠0) (hJ:J≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart I=rowPowerfulPart J) (hT:rowMaskPart I Q=rowMaskPart J Q) :
    pool I Q Q0=pool J Q Q0 := by
  unfold pool
  rw [completedReflectionPool_eq_on_fiber I J Q hI hJ hQ hA hT]

end

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss.FreeReflection

end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open CompletedGauss CanonicalRowCompletion CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι : Type*}

def markTwist (p : ι → Eis) (T : Finset ι) : Eis →* ℂ :=
  ∏ i ∈ T, coprimalityMask (p i)

def markedThetaQuotient (p : ι → Eis) (S : Finset ι) (Ψ : Eis →* ℂ) (c : Eis)
    (x : Eis ⧸ Ideal.span {c}) : ℂ :=
  fixedThetaQuotient Ψ c x * ∏ i ∈ S, if p i ∣ Quotient.out x then 1 else 0

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CubicEisenstein LocalReflectionBrackets CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

section Local
variable {F : Type*} [Field F] [Fintype F]

def markedFrequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x h : F) : ℂ :=
  finiteAdditiveFourierCoeff ψ zeroMark h * frequencyMultiplier χ ψ σ ε x h

def mixedFrequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (marked : Bool) (j : ℕ) (σ ε : Fˣ) (x h : F) : ℂ :=
  if marked then markedFrequencyRow χ ψ σ ε x h else frequencyRow χ ψ j σ ε x h

end Local

noncomputable local instance markedStratumField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) :=
  Ideal.Quotient.field P
noncomputable local instance markedStratumFintype (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) :=
  Fintype.ofFinite _

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentSupportedCorrelation
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCorrelation CenteredMomentCommonSupport

def supportedModulusCharacter (d : O) (hd : Supported (Ideal.span {d})) :
    MulChar (Residue d) ℂ where
  toFun x := Quotient.liftOn' x (fun z => idealRowHom z (Ideal.span {d})) (by
    intro x y hxy
    exact idealRowHom_congr_mod _ x y ((Ideal.span {d}).quotientRel_def.mp hxy))
  map_one' := idealRowHom_one_supported _ hd
  map_mul' := by
    intro x y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact idealRowHom_argument_mul x y _
  map_nonunit' := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change idealRowHom x (Ideal.span {d}) = 0
    by_contra hn
    have hm := idealRowHom_sixth_mask x (Ideal.span {d}) hd
    rw [idealRowHom_argument_pow x 6 _ hd, Ideal.isCoprime_span_singleton_iff] at hm
    have hcop : IsCoprime d x := by
      by_contra h
      rw [if_neg h] at hm
      exact (pow_ne_zero 6 hn) hm
    exact hx (isUnit_residue_of_coprime d x hcop)

@[simp] theorem supportedModulusCharacter_mk (d : O)
    (hd : Supported (Ideal.span {d})) (x : O) :
    supportedModulusCharacter d hd (Ideal.Quotient.mk _ x) = idealRowHom x (Ideal.span {d}) := rfl

lemma supported_mul_elements (d a : O)
    (hd : Supported (Ideal.span {d})) (ha : Supported (Ideal.span {a})) :
    Supported (Ideal.span {d * a}) := by
  rw [← Ideal.span_singleton_mul_span_singleton]
  exact (supported_mul_iff _ _).mpr ⟨hd, ha⟩

@[simp] lemma star_sexticReciprocityPhase (a b : O) :
    star (sexticReciprocityPhase a b) = sexticReciprocityPhase a b := by
  simp only [sexticReciprocityPhase, star_intCast]

def supportedCorrelation (u v : O)
    (hu : Supported (Ideal.span {u})) (hv : Supported (Ideal.span {v}))
    [Fintype (Residue u)] [Fintype (Residue v)] (j : O) : ℂ :=
  fullModulusCorrelation u v (supportedModulusCharacter u hu) (supportedModulusCharacter v hv) j

lemma supported_element_ne_zero (d : O) (hd : Supported (Ideal.span {d})) : d ≠ 0 := by
  intro h
  exact hd.1 (by simp [h])

def actualCorrelation (u v : O)
    (hu : Supported (Ideal.span {u})) (hv : Supported (Ideal.span {v})) (j : O) : ℂ := by
  letI := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero u hu)
  letI := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero v hv)
  letI : Fintype (Residue u) := Fintype.ofFinite _
  letI : Fintype (Residue v) := Fintype.ofFinite _
  exact supportedCorrelation u v hu hv j

def completeSupportExtension (D E : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (j a b : O) : ℂ :=
  actualCorrelation D E hD hE j * sexticReciprocityPhase a E *
    star (sexticReciprocityPhase b D) * sexticReciprocityPhase a b *
    idealRowHom j (Ideal.span {a}) * star (idealRowHom (-j) (Ideal.span {b}))

end SevenEighths.CenteredMomentSupportedCorrelation
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def actualCommon (C : O) (hC : Supported (Ideal.span {C})) (n₁ n₂ k : O) : ℂ := by
  letI := finite_quotient_span (supported_element_ne_zero C hC)
  letI : Fintype (ResidueQ C) := Fintype.ofFinite _
  exact fullCorrelation (fun x : ResidueQ C=>Ideal.Quotient.mk _ n₂*x)
    (fun y : ResidueQ C=>Ideal.Quotient.mk _ n₁*y)
    (supportedModulusCharacter C hC) (supportedModulusCharacter C hC) (Ideal.Quotient.mk _ k)

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve InitialMeanSquare ProbeCompleted

local notation "O" => ActualEisensteinCubic.O

def targetMonoid (η : HeckeFamily.Character) : O →* ℂ where
  toFun := HeckeFamily.elementCoeff η
  map_one' := HeckeFamily.elementCoeff_one η
  map_mul' := HeckeFamily.elementCoeff_mul η

def rowCoefficient (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m : O) : O →* ℂ :=
  targetMonoid η * conjugateMonoid Xi * reciprocityPhaseMonoid s hs *
    (idealRowHom m).toMonoidHom.comp principalIdealHom.toMonoidHom

def spectralSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (t : ℂ) (I J : Ideal O) : ℂ :=
  (completedMask S D I J * completedCorrection I J *
    (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I) : ℂ)) * cubeWeight Ψ J) *
      (CubicEisenstein.fullIdealWeight t I * CubicEisenstein.fullIdealWeight (3 * t) J)

def spectralRow (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ) (t : ℂ) : ℂ :=
  ∑' p : Ideal O × Ideal O, spectralSummand S D Ψ t p.1 p.2

end SevenEighths.ProbeRow
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def mellinSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (σ Z : ℝ) (p : Ideal O × Ideal O) (y : ℝ) : ℂ :=
  (Z : ℂ) ^ ((σ : ℂ) + y * Complex.I) * Complex.exp (((σ : ℂ) + y * Complex.I) ^ 2) *
    spectralSummand S D Ψ ((σ : ℂ) + y * Complex.I) p.1 p.2

end SevenEighths.ProbeRow
end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein ProbeCompleted ProbeRow

local notation "O" => ActualEisensteinCubic.O

structure CalibrationData where
  excluded : Finset (Ideal O)
  generator : O
  generator_ne_zero : generator ≠ 0
  residue : MulChar (O ⧸ Ideal.span {generator}) ℂ

def elementNorm (a : O) : ℝ := Ideal.absNorm (Ideal.span {a})

def CalibrationData.residueMonoid (C : CalibrationData) : O →* ℂ :=
  C.residue.toMonoidHom.comp (Ideal.Quotient.mk (Ideal.span {C.generator})).toMonoidHom

def CalibrationData.Xi (C : CalibrationData) : O →* ℂ :=
  C.residueMonoid * (idealRowHom C.generator).toMonoidHom.comp principalIdealHom.toMonoidHom

def CalibrationData.tau (C : CalibrationData) : ℂ :=
  (∑' d : O ⧸ Ideal.span {C.generator}, C.residue d *
    quotientTrace C.generator C.generator_ne_zero d) /
      (Real.sqrt (elementNorm C.generator) : ℂ)

def sexticGauss (s : O) (hs : s ≠ 0) (h : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {s},
    idealRowHom (GaussianShiftedPartition.representative s d) (Ideal.span {s}) *
      quotientTrace s hs (Ideal.Quotient.mk _ h * d)

def verticalIntegral (σ : ℝ) (F : ℂ → ℂ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, F ((σ : ℂ) + y * Complex.I)

def markedPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W₀ W₁ : ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  (Y : ℂ)⁻¹ * ∑' s : {I : Ideal O // Supported I},
    if ∀ p ∈ C.excluded, ¬p ∣ s.val then
      let a := primaryGenerator s.val
      let ha := supported_primaryGenerator_ne_zero s.val s.property
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let q_s : ℝ := Ideal.absNorm s.val
      W₁ (q_s / Y) * idealRowHom C.generator s.val /
        (C.tau * C.residueMonoid a * (Real.sqrt (elementNorm C.generator * q_s * X) : ℂ)) *
      ∑' m : O,
        C.residueMonoid m * (Real.sqrt q_s : ℂ)⁻¹ * sexticGauss a ha (-m) *
          W₀ (elementNorm m / (elementNorm C.generator * q_s * X)) *
          verticalIntegral 4 (fun t => (Z : ℂ) ^ t * Complex.exp (t ^ 2) *
            spectralRow C.excluded D (rowCoefficient η C.Xi a has m) t)
    else 0

def slotProduct {K : ℕ} (p : Fin K → O) (J : Finset (Fin K)) : O := ∏ i ∈ J, p i

def compensatedTuple {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (p : Fin K → O) (X Y Z : ℝ) : ℂ :=
  ProbeCompensation.tupleOperation p elementNorm (HeckeFamily.elementCoeff η)
    (fun a => markedPhysicalProbe η C (Ideal.span {a}) W₀ W₁) X Y Z

@[simp] theorem elementNorm_one : elementNorm (1 : O) = 1 := by
  simp [elementNorm]

attribute [local irreducible] markedPhysicalProbe

def compensatedPhysicalProbe {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (slotPrimes : Fin K → Finset O)
    (slotWindow : Fin K → ℝ → ℂ) (slotScale : Fin K → ℝ) (X Y Z : ℝ) : ℂ :=
  ∑ p : ((i : Fin K) → {a : O // a ∈ slotPrimes i}),
    (∏ i : Fin K, slotWindow i (elementNorm (p i).val / slotScale i)) *
      compensatedTuple η C W₀ W₁ (fun i => (p i).val) X Y Z

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def physicalRowBase (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) : O→*ℂ :=
  targetMonoid η*conjugateMonoid Xi*reciprocityPhaseMonoid s hs

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentSupport
open UniqueFactorizationMonoid IdealMobiusDivisorSum CanonicalQuadraticSieve

def supportExtract (I : Ideal O) (S : Finset (Ideal O)) : Ideal O :=
  ((normalizedFactors I).filter (fun P => P ∈ S)).prod

def supportResidual (I : Ideal O) (S : Finset (Ideal O)) : Ideal O :=
  ((normalizedFactors I).filter (fun P => P ∉ S)).prod

theorem supportExtract_factors (I : Ideal O) (S : Finset (Ideal O)) :
    normalizedFactors (supportExtract I S) = (normalizedFactors I).filter (fun P => P ∈ S) :=
  normalizedFactors_prod_eq_self_of_subset (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportResidual_factors (I : Ideal O) (S : Finset (Ideal O)) :
    normalizedFactors (supportResidual I S) = (normalizedFactors I).filter (fun P => P ∉ S) :=
  normalizedFactors_prod_eq_self_of_subset (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportExtract_ne_zero (I : Ideal O) (S : Finset (Ideal O)) : supportExtract I S ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportResidual_ne_zero (I : Ideal O) (S : Finset (Ideal O)) : supportResidual I S ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportExtract_support (I : Ideal O) (S : Finset (Ideal O)) :
    primeSupport (supportExtract I S) = primeSupport I ∩ S := by
  ext P
  simp [primeSupport, supportExtract_factors]

theorem supportExtract_count (I P : Ideal O) (S : Finset (Ideal O)) :
    (normalizedFactors (supportExtract I S)).count P =
      if P ∈ S then (normalizedFactors I).count P else 0 := by
  rw [supportExtract_factors, Multiset.count_filter]

theorem supportExtract_supported (I : Ideal O) (hI : Supported I) (S : Finset (Ideal O)) :
    Supported (supportExtract I S) := by
  refine ⟨supportExtract_ne_zero I S, ?_⟩
  intro P hP
  rw [supportExtract_factors] at hP
  exact hI.2 P (Multiset.mem_filter.mp hP).1

theorem supportResidual_supported (I : Ideal O) (hI : Supported I) (S : Finset (Ideal O)) :
    Supported (supportResidual I S) := by
  refine ⟨supportResidual_ne_zero I S, ?_⟩
  intro P hP
  rw [supportResidual_factors] at hP
  exact hI.2 P (Multiset.mem_filter.mp hP).1

open CompletedGauss hiding primeSupport
open CanonicalRowCompletion CenteredMomentSupportedCorrelation

def idealCorrelation (I J : Ideal O) (hI : Supported I) (hJ : Supported J) (j : O) : ℂ :=
  actualCorrelation (primaryGenerator I) (primaryGenerator J)
    ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ) j

end SevenEighths.CenteredMomentSupport
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentRowNorm
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCorrelation CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport
local notation "O" => ActualEisensteinCubic.O

def pairResidue (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (x : Residue (a * b)) : ℂ :=
  supportedModulusCharacter a ha (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
    star (supportedModulusCharacter b hb
      (frequencyReduction b (a * b) (dvd_mul_left b a) x))

@[simp] theorem pairResidue_mk (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (z : O) :
    pairResidue a b ha hb (Ideal.Quotient.mk _ z) =
      idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b})) := by
  simp only [pairResidue, frequencyReduction_mk, supportedModulusCharacter_mk]

def pairFourier (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (h : O) : ℂ :=
  ∑' x : Residue (a * b), pairResidue a b ha hb x *
    quotientTrace (a * b) (mul_ne_zero (supported_element_ne_zero a ha)
      (supported_element_ne_zero b hb)) (Ideal.Quotient.mk _ h * x)

def rowPolynomial {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ) (z : O) : ℂ :=
  ∑ i ∈ S, c i * idealRowHom z (Ideal.span {a i})

def rowEnergy {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) : ℂ :=
  ∑' z : O, ((‖rowPolynomial S a c z‖ ^ 2 : ℝ) : ℂ) *
    W (‖eisEmbedding z‖ ^ 2 / K)

end SevenEighths.CenteredMomentRowNorm

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def numeratorExtension (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) : O→*ℂ :=
  numeratorBadTwist u a b r hr*movingNumeratorRow r hr

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

abbrev PrimaryElement := {n : O // Supported (Ideal.span {n}) ∧ λ₀^2∣n-1}

def primaryIdealEquiv : SupportedIdeal≃PrimaryElement where
  toFun I := ⟨primaryGenerator I.val,(supported_span_primaryGenerator_iff _).mpr I.property,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).2⟩
  invFun n := ⟨Ideal.span {n.val},n.property.1⟩
  left_inv I := Subtype.ext (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).1
  right_inv n := Subtype.ext (primaryGenerator_span n.val (supported_element_ne_zero _ n.property.1) n.property.2)

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted
local notation "O" => ActualEisensteinCubic.O

def baseRowCoefficient (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) : O →* ℂ :=
  targetMonoid η * InitialMeanSquare.conjugateMonoid Xi * reciprocityPhaseMonoid s hs

end SevenEighths.ProbeRow
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeRowClosure
open HeckeFamily
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem periodic_of_primary (M : Ideal O)
    (hM : M ≤ Ideal.span {λ₀ ^ 2}) (G F : O →* ℂ)
    (hF : CanonicalCoefficientClass.FactorsModulo M F)
    (hu : ∀ (u : Oˣ) x, G ((u : O) * x) = G x)
    (hz : ∀ x, λ₀ ∣ x → G x = 0)
    (hagree : ∀ x, λ₀ ^ 2 ∣ x - 1 → G x = F x) :
    CanonicalCoefficientClass.FactorsModulo M G := by
  intro x y hxy
  have hdiff : λ₀ ^ 2 ∣ x - y := Ideal.mem_span_singleton.mp (hM hxy)
  have hdiff' : λ₀ ∣ x - y := (dvd_pow_self λ₀ (by decide : 2 ≠ 0)).trans hdiff
  by_cases hx : λ₀ ∣ x
  · have hy : λ₀ ∣ y := by
      convert (preTransparency := .instances) dvd_sub hx hdiff' using 1 ; ring
    rw [hz x hx, hz y hy]
  · have hg := PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff x |>.mpr hx
    have hspec := CompletedGauss.primaryGenerator_spec (Ideal.span {x}) hg
    obtain ⟨u, hu'⟩ := Ideal.span_singleton_eq_span_singleton.mp hspec.1.symm
    have hp : λ₀ ^ 2 ∣ (u : O) * x - 1 := by
      have hp' : λ₀ ^ 2 ∣ CompletedGauss.primaryGenerator (Ideal.span {x}) - 1 := hspec.2
      rwa [mul_comm, hu']
    have hq : λ₀ ^ 2 ∣ (u : O) * y - 1 := by
      have hd := hdiff.trans (dvd_mul_left (x-y) (u : O))
      convert (preTransparency := .instances) dvd_sub hp hd using 1 ; ring
    rw [← hu u x, ← hu u y, hagree _ hp, hagree _ hq]
    apply hF
    simpa only [mul_sub] using M.mul_mem_left (u : O) hxy

def quotientRow (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) : (O ⧸ M) →* ℂ where
  toFun x := Quotient.liftOn' x G (fun a b hab => hG a b (M.quotientRel_def.mp hab))
  map_one' := G.map_one
  map_mul' x y := by
    refine Quotient.inductionOn₂' x y ?_
    exact G.map_mul

@[simp] theorem quotientRow_mk (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) (z : O) :
    quotientRow M G hG (Ideal.Quotient.mk M z) = G z := rfl

def residueRow (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) : MulChar (O ⧸ M) ℂ :=
  MulChar.ofUnitHom (Units.map (quotientRow M G hG))

theorem residueRow_mk (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) (z : O) :
    residueRow M G hG (Ideal.Quotient.mk M z) =
      if IsUnit (Ideal.Quotient.mk M z) then G z else 0 := by
  by_cases hz : IsUnit (Ideal.Quotient.mk M z)
  · obtain ⟨u, hu⟩ := hz
    rw [if_pos (hu ▸ u.isUnit), ← hu]
    change MulChar.ofUnitHom (Units.map (quotientRow M G hG)) (u : O ⧸ M) = G z
    rw [MulChar.ofUnitHom_coe]
    change quotientRow M G hG (u : O ⧸ M) = G z
    rw [hu, quotientRow_mk]
  · rw [if_neg hz]
    exact MulChar.map_nonunit _ hz

def rowCharacter (M : Ideal O) (hM : M ≠ ⊥) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G)
    (hu : ∀ u : Oˣ, G (u : O) = 1) : Character :=
  Character.ofResidue M hM (residueRow M G hG) (by
    intro u
    rw [residueRow_mk, if_pos (u.isUnit.map (Ideal.Quotient.mk M)), hu])

theorem elementCoeff_rowCharacter (M : Ideal O) (hM : M ≠ ⊥) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G)
    (hu : ∀ u : Oˣ, G (u : O) = 1) (z : O) :
    elementCoeff (rowCharacter M hM G hG hu) z =
      if IsUnit (Ideal.Quotient.mk M z) then G z else 0 := residueRow_mk M G hG z

def elementHom (η : Character) : O →* ℂ where
  toFun := elementCoeff η
  map_one' := elementCoeff_one η
  map_mul' := elementCoeff_mul η

theorem elementHom_periodic (η : Character) :
    CanonicalCoefficientClass.FactorsModulo η.modulus (elementHom η) := by
  intro x y hxy
  apply congrArg η.residue
  exact Ideal.Quotient.eq.mpr hxy

theorem elementHom_norm (η : Character) (x : O) : ‖elementHom η x‖ ≤ 1 := by
  let : Finite (O ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (O ⧸ η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue _

theorem rowTwist_unit_mul (η : Character) (m f z : O) (u : Oˣ) (n : O) :
    CanonicalRowCompletion.rowTwist (elementHom η) m f z ((u : O)*n) =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n := by
  change elementCoeff η ((u : O)*n) * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) (Ideal.span {(u : O)*n}) = elementCoeff η n * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) (Ideal.span {n})
  rw [elementCoeff_unit_mul, Ideal.span_singleton_mul_left_unit u.isUnit]

theorem rowTwist_unit (η : Character) (m f z : O) (u : Oˣ) :
    CanonicalRowCompletion.rowTwist (elementHom η) m f z (u : O) = 1 := by
  simpa using rowTwist_unit_mul η m f z u 1

theorem rowTwist_periodic (η : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r-1) (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r) :
    CanonicalCoefficientClass.FactorsModulo
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r})
      (CanonicalRowCompletion.rowTwist (elementHom η) m f z) := by
  refine periodic_of_primary _ ?_ _
    (CanonicalRowCompletion.actualPeriodicRow (elementHom η) m u a b r hr)
    (CanonicalRowCompletion.actualPeriodicRow_periodic _ _ (elementHom_periodic η) _ _ _ _ _ hr)
    (rowTwist_unit_mul η m f z) ?_ ?_
  · have hd3 : λ₀ ^ 2 ∣ (3 : O) := ActualEisensteinCubic.lambda_sq_dvd_three
    have hd72 : λ₀ ^ 2 ∣ (72 : O) := hd3.trans ⟨24, by norm_num⟩
    exact (Ideal.mul_le_left.trans Ideal.mul_le_right).trans
      ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr hd72))
  · intro n hn
    apply CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2
    intro hs
    exact ((CanonicalQuadraticSieve.supported_span_iff n).mp hs).1 hn
  · exact CanonicalRowCompletion.rowTwist_eq_actualPeriodicRow_primary
      _ _ _ _ hmLam hm2 u a b r hr hpr hx

theorem rowTwist_nonzero_coprime (η : Character) (m f z n : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hn : CanonicalRowCompletion.rowTwist (elementHom η) m f z n ≠ 0) :
    CanonicalQuadraticSieve.Supported (Ideal.span {n}) ∧ IsCoprime n (m^6*f^4*z) := by
  have hs : CanonicalQuadraticSieve.Supported (Ideal.span {n}) := by
    by_contra h
    exact hn (CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 h)
  refine ⟨hs, ?_⟩
  have hrow : CanonicalRowCompletion.idealRowHom (m^6*f^4*z) (Ideal.span {n}) ≠ 0 :=
    right_ne_zero_of_mul hn
  have hp := pow_ne_zero 6 hrow
  rw [← CanonicalRowCompletion.idealRowHom_argument_pow _ _ _ hs,
    CanonicalRowCompletion.idealRowHom_sixth_mask _ _ hs] at hp
  by_cases hc : IsCoprime (Ideal.span {n}) (Ideal.span {m^6*f^4*z})
  · exact (Ideal.isCoprime_span_singleton_iff _ _).mp hc
  · simp [hc] at hp

theorem rowTwist_nonzero_unit (η : Character) (m f z n : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r)
    (hn : CanonicalRowCompletion.rowTwist (elementHom η) m f z n ≠ 0) :
    IsUnit (Ideal.Quotient.mk
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}) n) := by
  obtain ⟨hs, hc⟩ := rowTwist_nonzero_coprime η m f z n hmLam hm2 hn
  have hm : IsCoprime n m := hc.of_isCoprime_of_dvd_right ⟨m^5*f^4*z, by ring⟩
  have hr : IsCoprime n r := hc.of_isCoprime_of_dvd_right
    ⟨m^6*((u : O)*λ₀^a*(2 : O)^b), by
      rw [show m^6*f^4*z = m^6*(f^4*z) by ring, hx]; ring⟩
  have h2 := hm.of_isCoprime_of_dvd_right hm2
  have h9 := (ShortDraftCRT.nine_coprime_of_not_lambda_dvd n
    ((CanonicalQuadraticSieve.supported_span_iff n).mp hs).1).symm
  have h72 : IsCoprime n (72 : O) := by
    convert (preTransparency := .instances) (h2.pow_right : IsCoprime n ((2 : O)^3)).mul_right h9 using 1 ; norm_num
  have he : elementCoeff η n ≠ 0 := left_ne_zero_of_mul hn
  have hη : IsCoprime (Ideal.span {n}) η.modulus := by
    apply (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp
    exact MulChar.apply_ne_zero_iff.mp he
  rw [IdealCharacter.isUnit_mk_iff_isCoprime, IsCoprime.mul_right_iff,
    IsCoprime.mul_right_iff, IsCoprime.mul_right_iff]
  exact ⟨⟨⟨hη, (Ideal.isCoprime_span_singleton_iff _ _).mpr hm⟩,
    (Ideal.isCoprime_span_singleton_iff _ _).mpr h72⟩,
    (Ideal.isCoprime_span_singleton_iff _ _).mpr hr⟩

theorem exists_row_character (η : Character) (m f z : O)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ : Character, ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n := by
  obtain ⟨u, a, b, r, hr, hpr, hx, hM, _, _, _⟩ :=
    CanonicalRowCompletion.exists_actual_periodic_row (elementHom η) η.modulus
      η.modulus_ne_bot (elementHom_periodic η) (elementHom_norm η) m f z hm hf hz hmLam hm2
  let M := η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}
  let G := CanonicalRowCompletion.rowTwist (elementHom η) m f z
  have hG := rowTwist_periodic η m f z hmLam hm2 u a b r hr hpr hx
  refine ⟨rowCharacter M hM G hG (rowTwist_unit η m f z), ?_⟩
  intro n
  rw [elementCoeff_rowCharacter]
  split_ifs with hn
  · rfl
  · exact Eq.symm (not_not.mp (fun h => hn (rowTwist_nonzero_unit η m f z n hmLam hm2 u a b r hx h)))

def rowConductorBound (η : Character) (m f z : O) : ℕ :=
  η.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : O)}).absNorm *
    ((Ideal.span {f}).absNorm ^ 4 * (Ideal.span {z}).absNorm)

theorem row_modulus_norm_le (η : Character) (m f z : O)
    (hf : f ≠ 0) (hz : z ≠ 0) (u : Oˣ) (a b : ℕ) (r : O)
    (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r) :
    (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}).absNorm ≤
      rowConductorBound η m f z := by
  have hprod : (Ideal.span {f^4*z} : Ideal O) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (pow_ne_zero _ hf) hz)
  let : Finite (O ⧸ Ideal.span {f^4*z}) := Ring.HasFiniteQuotients.finiteQuotient hprod
  have hle : (Ideal.span {f^4*z} : Ideal O) ≤ Ideal.span {r} := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    apply Ideal.mem_span_singleton.mpr
    exact ⟨(u : O)*λ₀^a*(2 : O)^b, by rw [hx]; ring⟩
  have hn := FiniteConductor.absNorm_le_of_le hle
  have heq : (Ideal.span {f^4*z} : Ideal O) = (Ideal.span {f})^4 * Ideal.span {z} := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
  rw [heq, map_mul, map_pow] at hn
  simpa only [rowConductorBound, map_mul] using
    Nat.mul_le_mul_left
      (η.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : O)}).absNorm) hn

theorem exists_row_character_with_conductor (η : Character) (m f z : O)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ : Character, χ.modulus.absNorm ≤ rowConductorBound η m f z ∧
      ∀ n : O, elementCoeff χ n =
        CanonicalRowCompletion.rowTwist (elementHom η) m f z n := by
  obtain ⟨u, a, b, r, hr, hpr, hx, hM, _, _, _⟩ :=
    CanonicalRowCompletion.exists_actual_periodic_row (elementHom η) η.modulus
      η.modulus_ne_bot (elementHom_periodic η) (elementHom_norm η) m f z hm hf hz hmLam hm2
  let M := η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}
  let G := CanonicalRowCompletion.rowTwist (elementHom η) m f z
  have hG := rowTwist_periodic η m f z hmLam hm2 u a b r hr hpr hx
  refine ⟨rowCharacter M hM G hG (rowTwist_unit η m f z),
    row_modulus_norm_le η m f z hf hz u a b r hx, ?_⟩
  intro n
  rw [elementCoeff_rowCharacter]
  split_ifs with hn
  · rfl
  · exact Eq.symm (not_not.mp (fun h => hn (rowTwist_nonzero_unit η m f z n hmLam hm2 u a b r hx h)))

theorem idealCoeff_eq_row (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n) (I : Ideal O) :
    idealCoeff χ I = idealCoeff η I * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) I := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero, zero_mul]
  let n := ConcretePrimeRowBridge.idealGenerator I
  have hn : n ≠ 0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hI
  have hs : Ideal.span {n} = I := ConcretePrimeRowBridge.span_idealGenerator I
  rw [← hs, idealCoeff_span χ hn, heq]
  change elementCoeff η n * _ = idealCoeff η (Ideal.span {n}) * _
  rw [idealCoeff_span η hn]
  rfl

end SevenEighths.HeckeRowClosure

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondDiagonal
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O

def secondZeroEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) : ℂ :=
  ∑ i ∈ S, ∑ j ∈ S, (c i*star (c j)) *
    (actualCorrelation (a i) (a j) (ha i) (ha j) 0 /
      ((Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ)*
       (Real.sqrt (Ideal.absNorm (Ideal.span {a j}) : ℝ) : ℂ)))

end SevenEighths.CenteredMomentSecondDiagonal

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstFrequency
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentFirstReduced CenteredMomentFirstAssembly
open CenteredMomentFirstColumns CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CenteredMomentPrimitive CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def dilatedFrequency {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i) (j : ι → ℕ)
    (e a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (k : ℝ) (h : O) : ℂ :=
  let r := finitePrimeModulus P
  let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
  tripleRow a b r (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G e*
    ((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*
    tripleFourier a b r (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
      (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G h

end SevenEighths.CenteredMomentFirstFrequency

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentPartition
open CenteredMomentCorrelation CenteredMomentCommonSupport

open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve
open CenteredMomentSupportedCorrelation CenteredMomentUnequal
open CenteredMomentProductCRT
open ConcretePrimeRowBridge hiding O
local notation "O" => ActualEisensteinCubic.O

section Product
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem supported_product (a : ι → O) (ha : ∀ i, Supported (Ideal.span {a i})) :
    Supported (Ideal.span {∏ i, a i}) := by
  have hs (S : Finset ι) : Supported (Ideal.span {∏ i ∈ S, a i}) := by
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Ideal.span_singleton_one]
      rw [← Ideal.one_eq_top]
      change Supported (1 : Ideal O)
      refine ⟨one_ne_zero, ?_⟩
      intro P hP
      simp only [UniqueFactorizationMonoid.normalizedFactors_one,
        Multiset.notMem_zero] at hP
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi]
      exact supported_mul_elements _ _ (ha i) ih
  exact hs Finset.univ

def partitionNormalizer (p : ι → O) (c d : ι → ℕ) (U : Finset ι) : ℝ :=
  ∏ i, (Ideal.absNorm (Ideal.span {p i}) : ℝ) ^ (min (c i) (d i) - if i ∈ U then 1 else 0)

def dividedFrequency (p : ι → O) (c d : ι → ℕ) (w : O) (i : ι) : O :=
  cofactor (fun j => p j ^ min (c j) (d j)) i * w

end Product

end SevenEighths.CenteredMomentPartition

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondTail
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson CompletedGauss
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSupportedCorrelation CenteredMomentSecondWholeKernel
local notation "O" => ActualEisensteinCubic.O

def secondDiscardedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
    ∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
      actualCorrelation (primaryGenerator I) (primaryGenerator J)
        ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ) (-h)*
      paperRadialFourier W (K*‖eisEmbedding h‖^2/
        ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2)

end SevenEighths.CenteredMomentSecondTail

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondLocalization
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentSecondWholeKernel CenteredMomentSecondTail
open CenteredMomentSectorLocalization CenteredMomentSupportedCorrelation
open CenteredMomentSecondDiagonal
local notation "O" => ActualEisensteinCubic.O

def secondRetainedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
    ∑' h : O,(retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
      actualCorrelation (primaryGenerator I) (primaryGenerator J)
        ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ) (-h)*
      paperRadialFourier W (K*‖eisEmbedding h‖^2/
        ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2)

def secondRetainedEnergy (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*heightCoeff η t I)*star (c J*heightCoeff η t J))*
      secondRetainedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

end SevenEighths.CenteredMomentSecondLocalization

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def ramifiedCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z : ℂ) : ℂ :=
  let p := primaryGenerator P.val
  let hp := supported_primeGenerator_prime P hs
  letI : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let hsp : Supported (Ideal.span {p}) := (span_primaryGenerator_of_supported P.val hs).symm ▸ hs
  let hg := (supported_prime_data p hp hsp).1
  ramifiedClosed p hp hg (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
    x w z (multiplicity p u.val)

def ramifiedPrimes (S : Finset (Ideal O)) (u : FreeRow) : Finset PrimeIdeal :=
  (SmoothMobiusCorrection.primeSet (Ideal.span {u.val})).filter (fun P => P.val∉S)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def continuedMarkedLocal (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z : ℂ) : ℂ :=
  let p := primaryGenerator P.val
  let hp := supported_primeGenerator_prime P hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let hsp : Supported (Ideal.span {p}) := (span_primaryGenerator_of_supported P.val hs).symm ▸ hs
  let hg := (supported_prime_data p hp hsp).1
  rowClosedMarked p hp hg (targetMonoid η p) (actualACube η p)
    ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
    (multiplicity p u.val)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end


