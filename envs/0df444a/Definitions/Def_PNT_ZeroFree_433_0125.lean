-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0125
-- name    : PNT_ZeroFree_433_0125
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:08:35.699325+00:00
-- url     : https://prove2.me/theorems/3453ab92-e79c-475b-afa3-5b8f70a1d359
-- title:
--   Zero-free region foundations: CubicSieve.PrincipalDensity [0125]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.PrincipalDensity
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/PrincipalDensity.lean#L79-L653

import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0043
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0060
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0072
import Definitions.Def_PNT_ZeroFree_433_0077
import Definitions.Def_PNT_ZeroFree_433_0082
import Definitions.Def_PNT_ZeroFree_433_0089
import Definitions.Def_PNT_ZeroFree_433_0092
import Definitions.Def_PNT_ZeroFree_433_0098
import Definitions.Def_PNT_ZeroFree_433_0099
import Definitions.Def_PNT_ZeroFree_433_0101
import Definitions.Def_PNT_ZeroFree_433_0102
import Definitions.Def_PNT_ZeroFree_433_0103
import Definitions.Def_PNT_ZeroFree_433_0105
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0114
import Definitions.Def_PNT_ZeroFree_433_0118_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0121
import Definitions.Def_PNT_ZeroFree_433_0121_parallel1
import Definitions.Def_PNT_ZeroFree_433_0122
import Definitions.Def_PNT_ZeroFree_433_0122_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0125_parallel1
import Definitions.Def_PNT_ZeroFree_433_0128
import Definitions.Def_PNT_ZeroFree_433_0152_parallel1
import Definitions.Def_PNT_ZeroFree_433_0153_parallel2
import Definitions.Def_PNT_ZeroFree_433_0210
import Definitions.Def_PNT_ZeroFree_433_0235_parallel1
import Definitions.Def_PNT_ZeroFree_433_0271_parallel1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/PrincipalDensity.lean
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


open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum


variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def maskedSourceDensity (G : Ideal O) (rows : m → Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (M : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    ((sourcePrincipalScale M (rows i):ℝ):ℂ)*primePoolDensity (G*(cols j*cols k))


omit [DecidableEq m] [DecidableEq n] in
theorem maskedSourcePrincipalTruncation_eq (G : Ideal O) (hG : Squarefree G)
    (W : 𝓢(ℝ,ℂ)) (hW : W 0=0) (rows : m → Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (M : ℝ) (Z : m → ℝ)
    (hcols : ∀ j, Admissible (cols j)) (hGc : ∀ j, IsCoprime G (cols j)) :
    maskedSourcePrincipalTruncation G W rows cols a M Z =
      paperRadialFourier W 0*maskedSourceDensity G rows cols a M -
      paperRadialFourier W 0*maskedPrincipalDivisorCorrection G rows cols cols a a M Z := by
  classical
  have ht (i : m) (j k : n) :
      originalTerm rows cols cols a a 1 1 i j k *
        principalTruncation (fun P : primePool {G*(cols j*cols k)} => P.val) Finset.univ W
          (sourcePrincipalScale M (rows i)) (Z i) =
      paperRadialFourier W 0*(originalTerm rows cols cols a a 1 1 i j k *
        ((sourcePrincipalScale M (rows i):ℝ):ℂ)*primePoolDensity (G*(cols j*cols k))) -
      paperRadialFourier W 0*(originalTerm rows cols cols a a 1 1 i j k *
        ∑ d ∈ idealDivisors (G*(cols j*cols k)), if Z i < (Ideal.absNorm d:ℝ) then
          (UniqueFactorizationMonoid.moebius d:ℂ)*
            ((sourcePrincipalScale M (rows i)/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) := by
    by_cases hc : IsCoprime (cols j) (cols k)
    · have hC : Squarefree (cols j*cols k) := squarefree_mul_iff.mpr
        ⟨hc.isRelPrime,(hcols j).2.1,(hcols k).2.1⟩
      have hprod : Squarefree (G*(cols j*cols k)) := squarefree_mul_iff.mpr
        ⟨((hGc j).mul_right (hGc k)).isRelPrime,hG,hC⟩
      have hp := principalTruncation_scaled (G*(cols j*cols k)) hprod W 1
        (sourcePrincipalScale M (rows i)) (Z i)
      simp only [Complex.ofReal_one,one_mul,hW,zero_mul,sub_zero] at hp
      rw [hp]
      ring
    · have hz : originalTerm rows cols cols a a 1 1 i j k=0 := by simp only [originalTerm,hc,ite_false]
      simp only [hz,zero_mul,mul_zero,sub_zero]
  unfold maskedSourcePrincipalTruncation
  simp_rw [ht]
  simp only [maskedSourceDensity,maskedPrincipalDivisorCorrection,sourcePrincipalScale,Finset.sum_sub_distrib,Finset.mul_sum]

omit [DecidableEq m] [DecidableEq n] in
theorem maskedPrincipalSourceSum_eq (G : Ideal O) (hG : Squarefree G)
    (W : 𝓢(ℝ,ℂ)) (hW : W 0=0) (rows : m → Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (M T : ℝ)
    (hcols : ∀ j, Admissible (cols j)) (hGc : ∀ j, IsCoprime G (cols j)) :
    maskedPrincipalSourceSum G W rows cols a M =
      paperRadialFourier W 0*maskedSourceDensity G rows cols a M -
      paperRadialFourier W 0*maskedPrincipalDivisorCorrection G rows cols cols a a M
        (fun i => T*sourcePrincipalScale M (rows i)) +
      originalMaskedTruncatedMiddle G W rows cols cols a a M
        (fun i => sourcePrincipalScale M (rows i)/T)
        (fun i => T*sourcePrincipalScale M (rows i)) (T^4) +
      maskedSourceErrorSum G W rows cols a M T := by
  rw [←maskedSourcePrincipalTruncation_eq G hG W hW rows cols a M _ hcols hGc]
  unfold maskedPrincipalSourceSum maskedSourcePrincipalTruncation originalMaskedTruncatedMiddle maskedSourceErrorSum
  simp only [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  unfold truncationError sourcePrincipalScale
  ring

end
section

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator


section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator IdealMobiusDivisorSum


theorem masked_source_principal_difference (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
        (G : Ideal O), Squarefree G →
      ∀ (B N M T : ℝ), 1≤B → 1≤N → 0<M → 4≤T →
      ∀ (rows : m → Ideal O) (cols : n → Ideal O),
        Function.Injective rows → Function.Injective cols →
        (∀ i, Admissible (rows i) ∧ B/2≤(Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ)≤B) →
        (∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀ j, IsCoprime G (cols j)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)), W 0=0 →
        ‖maskedPrincipalSourceSum G W rows cols a M -
          paperRadialFourier W 0*maskedSourceDensity G rows cols a M‖ ≤
        sourcePrincipalMajorant s C l hexp deltaLoss hδ ε hε G B N M T a W := by
  obtain ⟨s,C,hC,herr⟩ := maskedSource_error_uniform l
  refine ⟨s,C,hC,?_⟩
  intro m n _ _ _ _ α hexp deltaLoss hδ ε hε G hG B N M T hB hN hM hT rows cols hr hc hrows hcols hGc a W hW
  let Z := fun i => T*sourcePrincipalScale M (rows i)
  let Y := fun i => sourcePrincipalScale M (rows i)/T
  have hT0 : 0≤T := by linarith
  have hsplit := maskedPrincipalSourceSum_eq G hG W hW rows cols a M T (fun j => (hcols j).1) hGc
  change maskedPrincipalSourceSum G W rows cols a M =
    paperRadialFourier W 0*maskedSourceDensity G rows cols a M -
    paperRadialFourier W 0*maskedPrincipalDivisorCorrection G rows cols cols a a M Z +
    originalMaskedTruncatedMiddle G W rows cols cols a a M Y Z (T^4) +
    maskedSourceErrorSum G W rows cols a M T at hsplit
  have heq : maskedPrincipalSourceSum G W rows cols a M -
      paperRadialFourier W 0*maskedSourceDensity G rows cols a M =
      -(paperRadialFourier W 0*maskedPrincipalDivisorCorrection G rows cols cols a a M Z) +
      originalMaskedTruncatedMiddle G W rows cols cols a a M Y Z (T^4) +
      maskedSourceErrorSum G W rows cols a M T := by rw [hsplit]; ring
  have hl := hexp.masked_source_large_principal_sum deltaLoss hδ ε hε G hG.ne_zero B N M T hB hN hM (by linarith)
    rows cols cols hr hc hc hrows hcols hcols hGc hGc a a Z (fun _ => le_rfl)
  have hm := hexp.original_masked_truncated_middle deltaLoss hδ ε hε G hG B N M T hB hN hM hT0
    rows cols cols hr hc hc hrows a a W Y Z (T^4) hcols hcols hGc hGc (fun _ => le_rfl)
  have he := herr ε hε G hG.ne_zero B N M T hB hN hM hT rows cols hr hc
    (fun i => ⟨(hrows i).1.1,(hrows i).2.2⟩) (fun j => ⟨(hcols j).1.1,(hcols j).2⟩) a W
  have hn := norm_four_correction_terms
    (paperRadialFourier W 0*maskedPrincipalDivisorCorrection G rows cols cols a a M Z) 0
    (originalMaskedTruncatedMiddle G W rows cols cols a a M Y Z (T^4))
    (maskedSourceErrorSum G W rows cols a M T)
  simp only [sub_zero,norm_zero,add_zero] at hn
  rw [heq]
  apply hn.trans
  rw [norm_mul]
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hl (norm_nonneg _)) hm) he


end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

lemma maskedPrincipalSourceDifference_dyadic {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (W : 𝓢(ℝ,ℂ)) (S : Finset (Ideal O)) (K : ℝ)
    (cols : n → Ideal O) (a : n → ℂ) (M : ℝ) :
    maskedPrincipalSourceSum G W (fun I : S => I.val) cols a M -
      paperRadialFourier W 0*maskedSourceDensity G (fun I : S => I.val) cols a M =
    ∑ j : Fin (columnDyadicLength K+1),
      (maskedPrincipalSourceSum G W (fun I : divisorDyadicBin S K j => I.val) cols a M -
        paperRadialFourier W 0*maskedSourceDensity G (fun I : divisorDyadicBin S K j => I.val) cols a M) := by
  classical
  have h := sum_ideal_subtype_dyadic (A := ℂ) S K (fun I =>
    maskedPrincipalSourceSum G W (fun _ : Unit => I) cols a M -
      paperRadialFourier W 0*maskedSourceDensity G (fun _ : Unit => I) cols a M)
  simpa only [maskedPrincipalSourceSum,maskedSourceDensity,originalTerm,
    Finset.mul_sum,←Finset.sum_sub_distrib,Fintype.sum_unique] using h

theorem masked_source_principal_global (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] {α : ℝ} (hexp : HasSieveExponent α), 1/2≤α →
      ∀ (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) (G : Ideal O), Squarefree G →
      ∀ (K N M T : ℝ), 1≤K → 1≤N → 0<M → 4≤T →
      ∀ (S : Finset (Ideal O)), (∀ I∈S, Admissible I ∧ (Ideal.absNorm I:ℝ)≤K) →
      ∀ (cols : n → Ideal O), Function.Injective cols →
        (∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀ j, IsCoprime G (cols j)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)), W 0=0 →
        ‖maskedPrincipalSourceSum G W (fun I : S => I.val) cols a M -
          paperRadialFourier W 0*maskedSourceDensity G (fun I : S => I.val) cols a M‖ ≤
        (columnDyadicLength K+1:ℕ)*sourcePrincipalMajorant s C l hexp deltaLoss hδ ε hε G (2*K) N M T a W := by
  obtain ⟨s,C,hC,hbound⟩ := masked_source_principal_difference l
  refine ⟨s,C,hC,?_⟩
  intro n _ _ α hexp hα deltaLoss hδ ε hε G hG K N M T hK hN hM hT S hS cols hc hcols hGc a W hW
  classical
  let R := sourcePrincipalMajorant s C l hexp deltaLoss hδ ε hε G (2*K) N M T a W
  have hSnorm (I : Ideal O) (hI : I∈S) : 1≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K := by
    have hi := hS I hI
    refine ⟨?_,hi.2⟩
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hi.1.1 (Ideal.absNorm_eq_zero_iff.mp h))
  have hR : 0≤R := sourcePrincipalMajorant_nonneg s C hC.le l hexp deltaLoss hδ ε hε G (2*K) N M T a W
    (by linarith) (by linarith) hM.le (by linarith)
  have hb (j : Fin (columnDyadicLength K+1)) :
      ‖maskedPrincipalSourceSum G W (fun I : divisorDyadicBin S K j => I.val) cols a M -
        paperRadialFourier W 0*maskedSourceDensity G (fun I : divisorDyadicBin S K j => I.val) cols a M‖ ≤ R := by
    by_cases hj : (divisorDyadicBin S K j).Nonempty
    · let B := 2*divisorDyadicScale j.val
      have hB : 1≤B := by dsimp only [B]; linarith [divisorDyadicScale_ge_one j.val]
      have hBK : B≤2*K := by
        dsimp only [B]
        exact mul_le_mul_of_nonneg_left (divisorDyadicBin_scale_le S K hSnorm j hj) (by norm_num)
      have hrows (I : divisorDyadicBin S K j) : Admissible I.val ∧
          B/2≤(Ideal.absNorm I.val:ℝ) ∧ (Ideal.absNorm I.val:ℝ)≤B := by
        have hi := divisorDyadicBin_bounds S K hSnorm j I.val I.property
        refine ⟨(hS I.val (Finset.mem_filter.mp I.property).1).1,?_,hi.2⟩
        dsimp only [B]
        linarith
      have hh := hbound hexp deltaLoss hδ ε hε G hG B N M T hB hN hM hT
        (fun I : divisorDyadicBin S K j => I.val) cols Subtype.val_injective hc hrows hcols hGc a W hW
      apply hh.trans
      exact sourcePrincipalMajorant_mono s C hC.le l hexp hα deltaLoss hδ ε hε G B (2*K) N M T a W
        (by linarith) hBK (by linarith) hM.le (by linarith)
    · have he := Finset.not_nonempty_iff_eq_empty.mp hj
      have : IsEmpty (divisorDyadicBin S K j) := by
        refine ⟨fun I => ?_⟩
        have hi := I.property
        simp only [he,Finset.notMem_empty] at hi
      simpa only [maskedPrincipalSourceSum,maskedSourceDensity,Finset.univ_eq_empty,
        Finset.sum_empty,mul_zero,sub_zero,norm_zero] using hR
  rw [maskedPrincipalSourceDifference_dyadic G W S K cols a M]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : Fin (columnDyadicLength K+1), R := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,R]

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum

theorem primePoolDensity_eq_support (G : Ideal O) :
    primePoolDensity G = ∏ P ∈ primeSupport G, (1-(1:ℂ)/(Ideal.absNorm P:ℂ)) := by
  rw [primePoolDensity,Finset.prod_coe_sort (primePool {G})
    (fun P : Ideal O => (1-(1:ℂ)/(Ideal.absNorm P:ℂ)))]
  simp [primePool,primeSupport]

theorem primePoolDensity_eq_real (G : Ideal O) :
    primePoolDensity G = (idealPrimeDensity {G} G : ℂ) := by
  simp only [primePoolDensity,idealPrimeDensity,idealSupport_singleton_univ,
    Complex.ofReal_prod,Complex.ofReal_sub,Complex.ofReal_one,
    Complex.ofReal_div,Complex.ofReal_natCast]

theorem primePoolDensity_norm_le_one (G : Ideal O) (hG : G ≠ 0) :
    ‖primePoolDensity G‖ ≤ 1 := by
  rw [primePoolDensity_eq_real,Complex.norm_real,Real.norm_eq_abs]
  have hb := idealPrimeDensity_mem_Icc {G}
    (by intro I hI; simpa only [Finset.mem_singleton.mp hI,Ideal.zero_eq_bot] using hG) G
  rw [abs_of_nonneg hb.1]
  exact hb.2

theorem primePoolDensity_star (G : Ideal O) : star (primePoolDensity G) = primePoolDensity G := by
  rw [primePoolDensity_eq_real]
  simp

theorem primePoolDensity_mul (G H : Ideal O) (hG : G ≠ 0) (hH : H ≠ 0)
    (hcop : IsCoprime G H) : primePoolDensity (G*H) = primePoolDensity G*primePoolDensity H := by
  simp only [primePoolDensity_eq_support,primeSupport]
  rw [UniqueFactorizationMonoid.normalizedFactors_mul hG hH,Multiset.toFinset_add,
    Finset.prod_union]
  apply Finset.disjoint_left.mpr
  intro P hPG hPH
  exact (Multiset.disjoint_left.mp (UniqueFactorizationMonoid.disjoint_normalizedFactors hcop.isRelPrime))
    (Multiset.mem_toFinset.mp hPG) (Multiset.mem_toFinset.mp hPH)


theorem normalizedPairDensity_eq_primePoolDensity (I J G : Ideal O)
    (hI : IsCoprime I G) (hJ : IsCoprime J G) :
    normalizedPairDensity I J G = primePoolDensity G := by
  rw [normalizedPairDensity,primePoolDensity_eq_support]
  apply Finset.prod_congr rfl
  intro P hP
  have hPG : P ∣ G := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
    (Multiset.mem_toFinset.mp hP)
  rw [idealZeroMask_generator_eq_one I P (hI.of_isCoprime_of_dvd_right hPG),
    idealZeroMask_generator_eq_one J P (hJ.of_isCoprime_of_dvd_right hPG),one_mul]

end

open ActualEisensteinCubic

def densityColumn {n : Type*} (cols : n → Ideal O) (a : n → ℂ) : n → ℂ :=
  fun j => primePoolDensity (cols j) * a j

theorem densityColumn_norm_le {n : Type*} (cols : n → Ideal O) (a : n → ℂ)
    (hcols : ∀ j, cols j ≠ 0) (j : n) : ‖densityColumn cols a j‖ ≤ ‖a j‖ := by
  rw [densityColumn,norm_mul]
  exact (mul_le_mul_of_nonneg_right (primePoolDensity_norm_le_one _ (hcols j))
    (norm_nonneg _)).trans_eq (one_mul _)

theorem densityColumn_energy_le {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (hcols : ∀ j, cols j ≠ 0) :
    (∑ j, ‖densityColumn cols a j‖^2) ≤ ∑ j, ‖a j‖^2 := by
  apply Finset.sum_le_sum
  intro j _
  exact pow_le_pow_left₀ (norm_nonneg _) (densityColumn_norm_le cols a hcols j) 2

theorem actualPrincipalDifference_densityColumn {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (G : Ideal O) (K : ℝ)
    (hcols : ∀ j, cols j ≠ 0) (hcop : ∀ j, IsCoprime (cols j) G) :
    actualPrincipalDifference cols (densityColumn cols a) G K =
      (∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        star (a j)*a k*primePoolDensity (cols j*cols k)*
          (normalizedPairPartial (cols j) (cols k) K * normalizedPairDivisors (cols j) (cols k) G)
        else 0) -
      primePoolDensity G * (∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        star (a j)*a k*primePoolDensity (cols j*cols k)*
          normalizedPairCoprimePartial (cols j) (cols k) G K else 0) := by
  unfold actualPrincipalDifference
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hjk : IsCoprime (cols j) (cols k)
  · simp only [hjk,ite_true,densityColumn,star_mul,primePoolDensity_star,
      primePoolDensity_mul _ _ (hcols j) (hcols k) hjk,
      normalizedPairDensity_eq_primePoolDensity _ _ _ (hcop j) (hcop k)]
    ring
  · simp only [hjk,ite_false,mul_zero,sub_self]

theorem primePoolDensity_common_conductor (I J G : Ideal O)
    (hI : I ≠ 0) (hJ : J ≠ 0) (hG : G ≠ 0)
    (hIJ : IsCoprime I J) (hGI : IsCoprime G I) (hGJ : IsCoprime G J) :
    primePoolDensity (G*(I*J)) = primePoolDensity G*(primePoolDensity I*primePoolDensity J) := by
  rw [primePoolDensity_mul G (I*J) hG (mul_ne_zero hI hJ) (hGI.mul_right hGJ),
    primePoolDensity_mul I J hI hJ hIJ]

open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss IdealMobiusDivisorSum

def densityPairSum {n : Type} [Fintype n] (cols : n → Ideal O) (a : n → ℂ)
    (P : Ideal O → Ideal O → ℂ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j)*a k*primePoolDensity (cols j*cols k)*P (cols j) (cols k) else 0

theorem unrestrictedPrincipalDensity_eq {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) (R : ℝ) (hR : 0 ≤ R) :
    unrestrictedPrincipalDensity rows cols cols a a R =
      (Real.sqrt R : ℂ)*densityPairSum cols a
        (fun I J => ∑ i, normalizedIdealPair I J (rows i)) := by
  unfold unrestrictedPrincipalDensity
  rw [Finset.sum_comm]
  simp only [densityPairSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j) (cols k)
  · simp only [unrestrictedPairTerm,hc,ite_true,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.sqrt_div hR]
    simp only [Complex.ofReal_div,normalizedIdealPair]
    ring
  · simp only [unrestrictedPairTerm,hc,ite_false,zero_mul,mul_zero,Finset.sum_const_zero]

theorem unrestrictedPrincipalDensity_squarefree {n : Type} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (a : n → ℂ) (R K : ℝ) (hR : 0 ≤ R) :
    unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols a a R =
      (Real.sqrt R : ℂ)*densityPairSum cols a (fun I J => normalizedPairPartial I J K) := by
  simpa only [normalizedPairPartial] using
    unrestrictedPrincipalDensity_eq (fun I : squarefreeIdealRange K => I.val) cols a R hR

theorem originalTerm_one_eq_unrestricted {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (rows : m → Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (hrows : ∀ i, Supported (rows i)) (hcols : ∀ j, Admissible (cols j))
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k)) (i : m) (j k : n) :
    originalTerm rows cols cols a a 1 1 i j k = unrestrictedPairTerm rows cols cols a a i j k := by
  by_cases hc : IsCoprime (cols j) (cols k)
  · simp only [originalTerm,unrestrictedPairTerm,hc,ite_true,one_dvd,star_mul,
      canonical_quadraticRow_star _ (hcols j),
      unrestrictedPairCharacter_eq_primary _ _ (hcols j) (hcols k) (hray j k) _ (hrows i)]
    ring
  · simp only [originalTerm,unrestrictedPairTerm,hc,ite_false]

theorem maskedSourceDensity_eq {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (G : Ideal O) (hG : G ≠ 0)
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) (M : ℝ)
    (hrows : ∀ i, Supported (rows i)) (hcols : ∀ j, Admissible (cols j))
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (hGc : ∀ j, IsCoprime G (cols j)) :
    maskedSourceDensity G rows cols a M =
      primePoolDensity G*unrestrictedPrincipalDensity rows cols cols a a M := by
  simp only [maskedSourceDensity,unrestrictedPrincipalDensity,Finset.mul_sum,sourcePrincipalScale]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [originalTerm_one_eq_unrestricted rows cols a hrows hcols hray]
  by_cases hc : IsCoprime (cols j) (cols k)
  · rw [primePoolDensity_mul G (cols j*cols k) hG (mul_ne_zero (hcols j).1 (hcols k).1)
      ((hGc j).mul_right (hGc k))]
    ring
  · simp only [unrestrictedPairTerm,hc,ite_false,zero_mul,mul_zero]

theorem maskedSourceDensity_coprime_squarefree {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (hG : G ≠ 0) (K M : ℝ) (hM : 0 ≤ M) (cols : n → Ideal O) (a : n → ℂ)
    (hcols : ∀ j, Admissible (cols j)) (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (hGc : ∀ j, IsCoprime G (cols j)) (hbad : ∀ P ∈ fixedBadPrimes, P ∣ G) :
    maskedSourceDensity G (fun I : coprimeSquarefreeRange G K => I.val) cols a M =
      (Real.sqrt M : ℂ)*primePoolDensity G* densityPairSum cols a
        (fun I J => normalizedPairCoprimePartial I J G K) := by
  rw [maskedSourceDensity_eq G hG _ cols a M]
  · rw [unrestrictedPrincipalDensity_eq _ _ _ _ hM]
    unfold normalizedPairCoprimePartial
    ring
  · intro I
    exact admissible_supported ((mem_idealRange.mp
      (coprimeSquarefreeRange_subset_idealRange G hbad K I.property)).1)
  · exact hcols
  · exact hray
  · exact hGc

end CanonicalQuadraticSieve

end

end OAI

end


