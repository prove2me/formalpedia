-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0183_parallel1
-- name    : PNT_ZeroFree_433_0183_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:05:05.410004+00:00
-- url     : https://prove2.me/theorems/f6eebe53-993d-4a24-a224-98c9261bdf1a
-- title:
--   Zero-free region foundations: RowCompletion.SupportBounds [0183_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.RowCompletion.SupportBounds
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/RowCompletion/SupportBounds.lean#L84-L441

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0051
import Definitions.Def_PNT_ZeroFree_433_0054
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0108
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0153_parallel1
import Definitions.Def_PNT_ZeroFree_433_0158_parallel1
import Definitions.Def_PNT_ZeroFree_433_0182_parallel1
import Definitions.Def_PNT_ZeroFree_433_0198_parallel1
import Definitions.Def_PNT_ZeroFree_433_0206_parallel1
import Definitions.Def_PNT_ZeroFree_433_0221
import Definitions.Def_PNT_ZeroFree_433_0224_parallel1
import Definitions.Def_PNT_ZeroFree_433_0276_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/RowCompletion/SupportBounds.lean
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

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight

theorem localRowValue_zero_of_mem (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) (hx : x∈P) :
    localRowValue x P = 0 := by
  unfold localRowValue
  split_ifs with h
  · let : P.IsMaximal := h.1
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact MulChar.map_nonunit _ (not_isUnit_zero)
  · rfl

theorem idealRowHom_zero_of_dvd (x : ActualEisensteinCubic.O) {P I : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPI : P∣I) (hx : x∈P) : idealRowHom x I = 0 := by
  obtain ⟨J,rfl⟩ := hPI
  rw [map_mul]
  have hz : idealRowHom x P = 0 := by
    rw [idealRowHom,primeValueHom_prime _ P hP,localRowValue_zero_of_mem x P hx]
  rw [hz,zero_mul]

theorem columnWeight_zero_of_mask (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) {P I : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPI : P∣I) (hm : m∈P) :
    columnWeight (rowTwist Ψ m f z) I = 0 := by
  unfold columnWeight
  have hx : m^6*f^4*z∈P := by
    have hm6 : m^6∈P := by
      rw [show m^6=m^5*m by ring]
      exact P.mul_mem_left (m^5) hm
    exact P.mul_mem_right z (P.mul_mem_right (f^4) hm6)
  by_cases hg : primaryGenerator I=0
  · rw [hg]
    change squarefreeGaussCoefficient I * (Ψ 0 * idealRowHom _ (Ideal.span {0})) = 0
    rw [Ideal.span_singleton_zero]
    change squarefreeGaussCoefficient I * (Ψ 0 * idealRowHom _ (0:Ideal ActualEisensteinCubic.O)) = 0
    rw [map_zero (idealRowHom _),mul_zero,mul_zero]
  · change squarefreeGaussCoefficient I *
      (Ψ (primaryGenerator I) * idealRowHom _ (Ideal.span {primaryGenerator I})) = 0
    rw [(primaryGenerator_spec I hg).1,idealRowHom_zero_of_dvd _ hP hPI hx,mul_zero,mul_zero]

theorem columnWeight_zero_of_not_squarefree (Ψ : ActualEisensteinCubic.O →* ℂ) {I : Ideal ActualEisensteinCubic.O}
    (hI : ¬Squarefree I) : columnWeight Ψ I = 0 := by
  simp [columnWeight,squarefreeGaussCoefficient,hI]


end

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open FirstPassCubeLabels hiding O

theorem localRowValue_mul (a b : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) :
    localRowValue (a*b) P = localRowValue a P * localRowValue b P := by
  unfold localRowValue
  split_ifs with h
  · let : P.IsMaximal := h.1
    simp only [map_mul]
  · simp

theorem idealRowHom_argument_mul (a b : ActualEisensteinCubic.O) (I : Ideal ActualEisensteinCubic.O) :
    idealRowHom (a*b) I = idealRowHom a I * idealRowHom b I := by
  by_cases hI : I=0
  · rw [hI,map_zero,map_zero,map_zero,zero_mul]
  change (if I=0 then 0 else _) = (if I=0 then 0 else _) * (if I=0 then 0 else _)
  simp only [if_neg hI]
  have hprod (s : Multiset (Ideal ActualEisensteinCubic.O)) :
      (s.map (localRowValue (a*b))).prod =
        (s.map (localRowValue a)).prod * (s.map (localRowValue b)).prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons P s ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons]
      rw [localRowValue_mul,ih]
      ring
  exact hprod _

theorem rowTwist_row_factor (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z n : ActualEisensteinCubic.O) :
    rowTwist Ψ m f z n =
      rowTwist Ψ m f 1 n * idealRowHom z (Ideal.span {n}) := by
  change Ψ n * idealRowHom (m^6*f^4*z) (Ideal.span {n}) =
    (Ψ n * idealRowHom (m^6*f^4*1) (Ideal.span {n})) * idealRowHom z (Ideal.span {n})
  rw [mul_one,idealRowHom_argument_mul]
  ring

theorem cubeWeight_row_factor (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (B : Ideal ActualEisensteinCubic.O) :
    cubeWeight (rowTwist Ψ m f z) B =
      cubeWeight (rowTwist Ψ m f 1) B * idealRowHom z B^3 := by
  by_cases hB : primaryGenerator B=0
  · have hzero (x:ActualEisensteinCubic.O) : rowTwist Ψ m f x (primaryGenerator B) = 0 := by
      rw [hB]
      change Ψ 0 * idealRowHom _ (Ideal.span {(0:ActualEisensteinCubic.O)}) = 0
      rw [Ideal.span_singleton_zero]
      change Ψ 0 * idealRowHom _ (0:Ideal ActualEisensteinCubic.O) = 0
      rw [map_zero (idealRowHom _),mul_zero]
    change _ * rowTwist Ψ m f z (primaryGenerator B)^3 / _ =
      (_ * rowTwist Ψ m f 1 (primaryGenerator B)^3 / _) * _
    rw [hzero z,hzero 1]
    simp
  · change _ * rowTwist Ψ m f z (primaryGenerator B)^3 / _ =
      (_ * rowTwist Ψ m f 1 (primaryGenerator B)^3 / _) * _
    rw [rowTwist_row_factor,(primaryGenerator_spec B hB).1,mul_pow]
    ring

theorem idealRowHom_prime_powers {ι : Type*} (P : ι → Ideal ActualEisensteinCubic.O)
    [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (pool : Finset ι)
    (v : ι → ℕ) (z : ActualEisensteinCubic.O) :
    idealRowHom z (∏i∈pool,(P i)^v i) = multiplicityRow P hg pool v z := by
  rw [map_prod]
  simp only [map_pow,multiplicityRow]
  apply Finset.prod_congr rfl
  intro i hi
  rw [idealRowHom_prime z (P i) (hg i)]

theorem cubeWeight_prime_powers {ι : Type*} (P : ι → Ideal ActualEisensteinCubic.O)
    [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (pool : Finset ι)
    (v : ι → ℕ) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) :
    cubeWeight (rowTwist Ψ m f z) (∏i∈pool,(P i)^v i) =
      cubeWeight (rowTwist Ψ m f 1) (∏i∈pool,(P i)^v i) *
        multiplicityRow P hg pool v z^3 := by
  rw [cubeWeight_row_factor,idealRowHom_prime_powers P hg pool v z]

end

section
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O

def excludedGenerator (S : Finset (Ideal ActualEisensteinCubic.O)) : ActualEisensteinCubic.O := idealGenerator (∏P∈S,P)

theorem excludedGenerator_mem (S : Finset (Ideal ActualEisensteinCubic.O)) {P : Ideal ActualEisensteinCubic.O} (hP : P∈S) :
    excludedGenerator S∈P := by
  have hdiv : P∣∏Q∈S,Q := Finset.dvd_prod_of_mem (fun Q:Ideal ActualEisensteinCubic.O=>Q) hP
  have hm : idealGenerator (∏Q∈S,Q)∈Ideal.span {idealGenerator (∏Q∈S,Q)} :=
    Ideal.subset_span (by simp)
  rw [span_idealGenerator] at hm
  exact (Ideal.dvd_iff_le.mp hdiv) hm


theorem canonicalSourceCoefficient_fixed_mask {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i}) (Ψ : ActualEisensteinCubic.O →* ℂ) (m c f : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (T : Finset ι)
    (hc : rowCoprimeMask (fun i=>Ideal.span {p i}) T c=1) :
    canonicalSourceCoefficient p hp hcop hg Ψ (m*c) f H T =
      canonicalSourceCoefficient p hp hcop hg Ψ m f H T := by
  simp only [canonicalSourceCoefficient,FirstPassCubeLabels.mask_mul _ hg,hc,mul_one]

end


open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open CompletedGauss hiding O

def cubeIndex (F : Finset (Ideal ActualEisensteinCubic.O)) (B : Ideal ActualEisensteinCubic.O) : primePool F →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i=>(UniqueFactorizationMonoid.normalizedFactors B).count i.val)

@[simp] theorem cubeIndex_apply (F : Finset (Ideal ActualEisensteinCubic.O)) (B : Ideal ActualEisensteinCubic.O) (i : primePool F) :
    cubeIndex F B i = (UniqueFactorizationMonoid.normalizedFactors B).count i.val := by
  simp [cubeIndex]

def cubeIdeal (F : Finset (Ideal ActualEisensteinCubic.O)) (v : primePool F →₀ ℕ) : Ideal ActualEisensteinCubic.O :=
  ∏i:primePool F,i.val^v i

theorem cubeIdeal_cubeIndex (F : Finset (Ideal ActualEisensteinCubic.O)) (B : Ideal ActualEisensteinCubic.O) (hB : B≠0)
    (hcover : ∀P∈UniqueFactorizationMonoid.normalizedFactors B,P∈primePool F) :
    cubeIdeal F (cubeIndex F B) = B := by
  have hsub : (UniqueFactorizationMonoid.normalizedFactors B).toFinset ⊆ primePool F := by
    intro P hP
    exact hcover P (Multiset.mem_toFinset.mp hP)
  calc
    _ = ∏P∈primePool F,P^(UniqueFactorizationMonoid.normalizedFactors B).count P := by
      simp only [cubeIdeal,cubeIndex_apply]
      exact Finset.prod_coe_sort (s := primePool F)
        (f := fun P:Ideal ActualEisensteinCubic.O=>P^(UniqueFactorizationMonoid.normalizedFactors B).count P)
    _ = (UniqueFactorizationMonoid.normalizedFactors B).prod :=
      (Finset.prod_multiset_count_of_subset _ _ hsub).symm
    _ = B := Ideal.prod_normalizedFactors_eq_self hB

theorem cubeIndex_inj (F : Finset (Ideal ActualEisensteinCubic.O)) (B C : Ideal ActualEisensteinCubic.O) (hB : B≠0) (hC : C≠0)
    (hb : ∀P∈UniqueFactorizationMonoid.normalizedFactors B,P∈primePool F)
    (hc : ∀P∈UniqueFactorizationMonoid.normalizedFactors C,P∈primePool F)
    (heq : cubeIndex F B = cubeIndex F C) : B=C := by
  have he := congrArg (cubeIdeal F) heq
  rwa [cubeIdeal_cubeIndex F B hB hb,cubeIdeal_cubeIndex F C hC hc] at he


theorem cubeIdeal_ne_zero (F : Finset (Ideal ActualEisensteinCubic.O)) (v : primePool F →₀ ℕ) :
    cubeIdeal F v ≠ 0 := by
  unfold cubeIdeal
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ (NeZero.ne i.val))

theorem cubeIdeal_primaryGenerator (F : Finset (Ideal ActualEisensteinCubic.O))
    (v : primePool F →₀ ℕ) :
    primaryGenerator (cubeIdeal F v) =
      FirstPassCubeLabels.primeProduct (poolPrimary F) Finset.univ v := by
  change primaryGeneratorHom (∏i:primePool F,i.val^v i) = _
  rw [map_prod]
  simp only [map_pow]
  unfold FirstPassCubeLabels.primeProduct
  apply Finset.prod_congr rfl
  intro i hi
  change primaryGenerator i.val^v i = poolPrimary F i^v i
  rw [←primaryPrime_eq_primaryGenerator i.val]
  rfl

end CanonicalRowCompletion


end

end OAI

end


