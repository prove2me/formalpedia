-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0280_parallel1
-- name    : PNT_ZeroFree_433_0280_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:23:25.184318+00:00
-- url     : https://prove2.me/theorems/74f91acc-1c66-4241-9637-680a0a99a716
-- title:
--   Zero-free region foundations: Cusp.StaticReflectionPhases [0280_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Cusp.StaticReflectionPhases
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Cusp/StaticReflectionPhases.lean#L83-L631

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0046_1_1
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0089
import Definitions.Def_PNT_ZeroFree_433_0092
import Definitions.Def_PNT_ZeroFree_433_0124
import Definitions.Def_PNT_ZeroFree_433_0126
import Definitions.Def_PNT_ZeroFree_433_0127
import Definitions.Def_PNT_ZeroFree_433_0129_parallel2
import Definitions.Def_PNT_ZeroFree_433_0183_parallel1
import Definitions.Def_PNT_ZeroFree_433_0190_parallel1
import Definitions.Def_PNT_ZeroFree_433_0211_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1
import Definitions.Def_PNT_ZeroFree_433_0271_parallel1
import Definitions.Def_PNT_ZeroFree_433_0273_parallel1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Cusp/StaticReflectionPhases.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

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
open scoped BigOperators Classical MatrixGroups

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A4PhaseFromResidue_norm (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}) (x:Eis) :
    ‖A4PhaseFromResidue c0 hc0 v x‖=1 := by
  let:Finite (Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}):=
    finite_quotient_span (A4_bad_modulus_ne_zero c0 hc0)
  unfold A4PhaseFromResidue
  exact AddChar.norm_apply _ _
end ShortDraftCusp


end

open scoped Classical BigOperators

namespace CanonicalRowCompletion
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalCoefficientClass
local notation "Eis" => ActualEisensteinCubic.O

def reflectionConductor (q:ℕ) : Eis := (2592*q:ℕ)

def reflectionExcludedPrimes (q:ℕ) : Finset (Ideal Eis) :=
  gcdMaskPrimes (Ideal.span {reflectionConductor q})

lemma reflectionConductor_ne_zero (q:ℕ) (hq:q≠0) : reflectionConductor q≠0 := by
  unfold reflectionConductor
  exact_mod_cast Nat.mul_ne_zero (by decide : 2592≠0) hq

lemma reflectionConductor_ideal (q:ℕ) :
    Ideal.span {reflectionConductor q}=
      Ideal.span {(9:Eis)}*(fixedBaseConductor q*Ideal.span {(72:Eis)}) := by
  rw [fixedBaseConductor_principal,Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_mul_span_singleton]
  congr 1
  unfold reflectionConductor
  push_cast
  ring_nf

lemma reflectionExcludedPrimes_bad (q:ℕ) :
    fixedBadPrimes⊆reflectionExcludedPrimes q := Finset.subset_union_left

lemma reflectionExcludedPrimes_prime (q:ℕ) (P:Ideal Eis)
    (hP:P∈reflectionExcludedPrimes q) : Prime P := by
  let:P.IsMaximal:=gcdMaskPrimes_maximal _ ⟨P,hP⟩
  exact Ideal.prime_of_isPrime (NeZero.ne P) inferInstance

lemma reflectionConductor_prime_mem (q:ℕ) (hq:q≠0) (P:Ideal Eis)
    (hP:Prime P) (hd:P∣Ideal.span {reflectionConductor q}) :
    P∈reflectionExcludedPrimes q := by
  apply Finset.mem_union_right
  apply Multiset.mem_toFinset.mpr
  apply (Ideal.mem_normalizedFactors_iff (Ideal.span_singleton_eq_bot.not.mpr
    (reflectionConductor_ne_zero q hq))).mpr
  exact ⟨Ideal.isPrime_of_prime hP,Ideal.dvd_iff_le.mp hd⟩

lemma reflectionExcludedGenerator_ne_zero (q:ℕ) :
    excludedGenerator (reflectionExcludedPrimes q)≠0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  exact Finset.prod_ne_zero_iff.mpr (fun P hP=>(reflectionExcludedPrimes_prime q P hP).ne_zero)

lemma reflectionExcludedGenerator_bad (q:ℕ) :
    lambda∣excludedGenerator (reflectionExcludedPrimes q) ∧
      (2:Eis)∣excludedGenerator (reflectionExcludedPrimes q) := by
  constructor
  · apply Ideal.mem_span_singleton.mp
    exact excludedGenerator_mem _ (reflectionExcludedPrimes_bad q (by simp [fixedBadPrimes]))
  · apply Ideal.mem_span_singleton.mp
    exact excludedGenerator_mem _ (reflectionExcludedPrimes_bad q (by simp [fixedBadPrimes]))

lemma reflectionConductor_coprime_of_not_excluded (q:ℕ) (hq:q≠0)
    (P:Ideal Eis) [P.IsMaximal] (hP:P∉reflectionExcludedPrimes q) :
    IsCoprime (Ideal.span {reflectionConductor q}) P := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra ht
  have he:P=Ideal.span {reflectionConductor q}⊔P:=
    (show P.IsMaximal from inferInstance).eq_of_le ht le_sup_right
  exact hP (reflectionConductor_prime_mem q hq P
    (Ideal.prime_of_isPrime (NeZero.ne P) inferInstance)
    (Ideal.dvd_iff_le.mpr (le_sup_left.trans he.symm.le)))

lemma reflectionConductor_coprime_primary (q:ℕ) (hq:q≠0)
    (p:Eis) [(Ideal.span {p}).IsMaximal]
    (hp:Ideal.span {p}∉reflectionExcludedPrimes q) :
    IsCoprime (reflectionConductor q) p :=
  (Ideal.isCoprime_span_singleton_iff _ _).mp
    (reflectionConductor_coprime_of_not_excluded q hq _ hp)


end CanonicalRowCompletion

open scoped BigOperators Classical


open scoped BigOperators Classical MatrixGroups Matrix

namespace ShortDraftCusp


section
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
open CompletedGauss CubicKubota CubicJacobiGlobal LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance stratumMultiplierField (P:Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance stratumMultiplierFintype (P:Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _


end

open ActualEisensteinCubic CubicEisenstein CubicKubota CubicJacobiGlobal ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O


end ShortDraftCusp

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O

structure ControlledStratumArithmetic {ι:Type*} [Fintype ι]
    (p:ι→Eis) (N a0 c0:Eis) (numeratorMode:Bool) where
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
  matrix : (∀i,(Eis⧸Ideal.span {p i})ˣ)→SL(2,Eis)
  numerator : ∀v,matrix v 0 0=finiteCrossNumerator a0 c0 ramifiedTraceLambda p (lift v)
  denominator : ∀v,matrix v 1 0=c0*∏i,p i
  matrix_fixed : ∀v i j,N∣matrix v i j-matrix (fun _=>1) i j
  conditions : ∀v,if numeratorMode then
    (9:Eis)∣matrix v 0 1 ∧ (3:Eis)∣matrix v 1 1-1
    else (3:Eis)∣matrix v 0 1+1 ∧ (9:Eis)∣matrix v 1 1


end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

lemma frequency_congruence (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) (D.matrix v 0 0)=
      (D.sigma i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}) := by
  rw [D.numerator,finiteCrossNumerator_local,D.sigma_value,D.lift_residue]

lemma numerator_congruence (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    N∣D.matrix v 0 0-a0*∏i,p i := by
  rw [D.numerator]
  exact finiteCrossNumerator_fixed N a0 c0 ramifiedTraceLambda p (D.lift v)
    (fun i=>(dvd_pow_self N (by decide : (2:ℕ)≠0)).trans (D.lift_period v i))

lemma numerator_mod_three (D:ControlledStratumArithmetic p N a0 c0 mode)
    (h3N:(3:Eis)∣N) (hr:lambda^2∣(∏i,p i)-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : (3:Eis)∣D.matrix v 0 0-a0 := by
  have hprod:=three_dvd_primary_sub_one (∏i,p i) hr
  convert! dvd_add (h3N.trans (D.numerator_congruence v))
    (dvd_mul_of_dvd_right hprod a0) using 1 ; ring

lemma numerator_primary (D:ControlledStratumArithmetic p N a0 c0 mode)
    (h3N:(3:Eis)∣N) (hr:lambda^2∣(∏i,p i)-1) (ha:lambda^2∣a0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : lambda^2∣D.matrix v 0 0-1 := by
  convert! dvd_add (lambda_sq_dvd_three.trans (D.numerator_mod_three h3N hr v)) ha using 1 ; ring

lemma denominator_primary (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hr:lambda^2∣(∏i,p i)-1) (hc:lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : lambda^2∣D.matrix v 1 0-1 := by
  rw [D.denominator]
  exact primary_mul c0 (∏i,p i) hc hr


lemma determinant (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v 0 0*D.matrix v 1 1-D.matrix v 0 1*(c0*∏i,p i)=1 := by
  simpa only [Matrix.det_fin_two,D.denominator] using (D.matrix v).property

def ramifiedFixedFactor (D:ControlledStratumArithmetic p N a0 c0 true) (u q:Eis) : ℂ :=
  eisEmbedding (symbol (-u) (D.matrix (fun _=>1) 0 0-u*D.matrix (fun _=>1) 0 1)*
    symbol q (D.matrix (fun _=>1) 0 0))

def unramifiedFixedFactor (D:ControlledStratumArithmetic p N a0 c0 false) : ℂ :=
  eisEmbedding (symbol (D.matrix (fun _=>1) 0 0) c0)


end ControlledStratumArithmetic
end CubicEisenstein

end

end OAI

end


