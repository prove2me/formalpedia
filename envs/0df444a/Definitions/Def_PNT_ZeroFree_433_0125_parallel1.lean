-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0125_parallel1
-- name    : PNT_ZeroFree_433_0125_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:31:42.647512+00:00
-- url     : https://prove2.me/theorems/e0da153e-163c-436a-9458-f00930373628
-- title:
--   Zero-free region foundations: CubicSieve.PrincipalDensity [0125_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.PrincipalDensity
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/PrincipalDensity.lean#L79-L501

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0060
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0066
import Definitions.Def_PNT_ZeroFree_433_0072
import Definitions.Def_PNT_ZeroFree_433_0077
import Definitions.Def_PNT_ZeroFree_433_0080
import Definitions.Def_PNT_ZeroFree_433_0089
import Definitions.Def_PNT_ZeroFree_433_0098
import Definitions.Def_PNT_ZeroFree_433_0101
import Definitions.Def_PNT_ZeroFree_433_0102
import Definitions.Def_PNT_ZeroFree_433_0103
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0109_1
import Definitions.Def_PNT_ZeroFree_433_0113
import Definitions.Def_PNT_ZeroFree_433_0114
import Definitions.Def_PNT_ZeroFree_433_0148
import Definitions.Def_PNT_ZeroFree_433_0173_parallel1
import Definitions.Def_PNT_ZeroFree_433_0241
import Definitions.Def_PNT_ZeroFree_433_0242_parallel2
import Definitions.Def_PNT_ZeroFree_433_0260_parallel2
import Definitions.Def_PNT_ZeroFree_433_0265_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel1
import Definitions.Def_PNT_ZeroFree_433_0275_parallel1

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

namespace SecondPassIntegration

open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic SecondPassArithmetic

theorem childDensity_elementary_normalized {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ)
    (X F K A M : ℝ) (J : ℕ) (hX : 0 < X) (hF : 1 ≤ F) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hV₁ : ∀ s,‖V₁ s‖ ≤ M) (hV₂ : ∀ s,‖V₂ s‖ ≤ M)
    (hVs₁ : ∀ s,V₁ s ≠ 0 → |s| ≤ A) (hVs₂ : ∀ s,V₂ s ≠ 0 → |s| ≤ A)
    (hT : ∀ z∈T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J)/(X*F) ≤
      (6*128^4*K*(max 1 (X*Real.exp A))^2*M^2/X)*
        (∫ t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3 := by
  let B := (6*128^4*K*(max 1 (X*Real.exp A))^2*M^2/X)*(X*F)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hXF : 0 < X*F := mul_pos hX (lt_of_lt_of_le zero_lt_one hF)
  have h₁ (a : ℝ) : childEnergy p hp hcop hg pool Ψ₁ m T V₁ X true false a 0 ≤ B*(1+‖a‖)^(2*J) := by
    have h := childEnergy_elementary_normalized p hp hcop hg hc hinj pool Ψ₁ hΨ₁ m T V₁
      X F K A M a 0 hX hF hK hA hM hV₁ hVs₁ hT true false
    have hh : childEnergy p hp hcop hg pool Ψ₁ m T V₁ X true false a 0 ≤ B := (div_le_iff₀ hXF).mp h
    exact hh.trans (le_mul_of_one_le_right hB (one_le_pow₀ (by linarith [norm_nonneg a])))
  have h₂ (a : ℝ) : childEnergy p hp hcop hg pool Ψ₂ m T V₂ X false true a 0 ≤ B*(1+‖a‖)^(2*J) := by
    have h := childEnergy_elementary_normalized p hp hcop hg hc hinj pool Ψ₂ hΨ₂ m T V₂
      X F K A M a 0 hX hF hK hA hM hV₂ hVs₂ hT false true
    have hh : childEnergy p hp hcop hg pool Ψ₂ m T V₂ X false true a 0 ≤ B := (div_le_iff₀ hXF).mp h
    exact hh.trans (le_mul_of_one_le_right hB (one_le_pow₀ (by linarith [norm_nonneg a])))
  have hd := densityChildEnergy_polynomial_bound p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X J B B hB hB h₁ h₂
  rw [Real.mul_self_sqrt hB] at hd
  apply (div_le_iff₀ hXF).mpr
  convert! hd using 1 ; dsimp [B] ; ring

theorem childDensity_elementary_supported {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ)
    (X F K A M : ℝ) (J : ℕ) (hX : 0 < X) (hF : 1 ≤ F) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hscale : 1 ≤ X*Real.exp A)
    (hV₁ : ∀ s,‖V₁ s‖ ≤ M) (hV₂ : ∀ s,‖V₂ s‖ ≤ M)
    (hVs₁ : ∀ s,V₁ s ≠ 0 → |s| ≤ A) (hVs₂ : ∀ s,V₂ s ≠ 0 → |s| ≤ A)
    (hT : ∀ z∈T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J)/(X*F) ≤
      (6*128^4*(Real.exp A*M)^2*(∫ t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3)*K*X := by
  have h := childDensity_elementary_normalized p hp hcop hg hc hinj pool Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m T V₁ V₂ X F K A M J hX hF hK hA hM hV₁ hV₂ hVs₁ hVs₂ hT
  rw [max_eq_right hscale] at h
  convert! h using 1
  field_simp

end SecondPassIntegration

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

def sourcePrincipalScale (M : ℝ) (I : Ideal O) : ℝ := Real.sqrt (M/(Ideal.absNorm I:ℝ))

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]


def maskedPrincipalSourceSum (G : Ideal O) (W : 𝓢(ℝ,ℂ))
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) (M : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    ∑' z : O, rowCoprimeMask (fun P : primePool {G*(cols j*cols k)} => P.val) Finset.univ z *
      (if z=0 then 0 else W (‖eisEmbedding z‖^2/sourcePrincipalScale M (rows i)))

def maskedSourcePrincipalTruncation (G : Ideal O) (W : 𝓢(ℝ,ℂ))
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) (M : ℝ) (Z : m → ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    principalTruncation (fun P : primePool {G*(cols j*cols k)} => P.val) Finset.univ W
      (sourcePrincipalScale M (rows i)) (Z i)

def maskedSourceErrorSum (G : Ideal O) (W : 𝓢(ℝ,ℂ))
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) (M T : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    truncationError (fun P : primePool {G*(cols j*cols k)} => P.val) Finset.univ W
      (sourcePrincipalScale M (rows i))
      (sourcePrincipalScale M (rows i)/T)
      (T*sourcePrincipalScale M (rows i)) (T^4)


end
section

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

theorem maskedSource_error_uniform (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (ε : ℝ) (hε : 0<ε) (G : Ideal O), G≠0 →
      ∀ (B N M T : ℝ), 1≤B → 1≤N → 0<M → 4≤T →
      ∀ (rows : m → Ideal O) (cols : n → Ideal O),
        Function.Injective rows → Function.Injective cols →
        (∀ i, rows i≠0 ∧ (Ideal.absNorm (rows i):ℝ)≤B) →
        (∀ j, cols j≠0 ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)),
        ‖maskedSourceErrorSum G W rows cols a M T‖ ≤
          16384*B*N*((supportConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N))^ε)*
            (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l)*∑ j, ‖a j‖^2 := by
  obtain ⟨s,C,hC,hbound⟩ := primePool_symmetric_error_bound l
  refine ⟨s,C,hC,?_⟩
  intro m n _ _ _ _ ε hε G hG B N M T hB hN hM hT rows cols hr hc hrows hcols a W
  let E := (supportConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N))^ε)*
    (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l
  let error := fun i j k =>
    truncationError (fun P : primePool {G*(cols j*cols k)} => P.val) Finset.univ W
      (sourcePrincipalScale M (rows i)) (sourcePrincipalScale M (rows i)/T)
      (T*sourcePrincipalScale M (rows i)) (T^4)
  have hs := (supportConstant_pos ε hε).le
  have hE : 0≤E := by dsimp only [E]; positivity
  have herr (i : m) (j k : n) : ‖error i j k‖≤E := by
    have hi : 0<(Ideal.absNorm (rows i):ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => (hrows i).1 (Ideal.absNorm_eq_zero_iff.mp h))
    have hX : 0<sourcePrincipalScale M (rows i) := Real.sqrt_pos.mpr (div_pos hM hi)
    have h := hbound ε hε (G*(cols j*cols k))
      (mul_ne_zero hG (mul_ne_zero (hcols j).1 (hcols k).1)) W
      (sourcePrincipalScale M (rows i)) (sourcePrincipalScale M (rows i)) T hX
      (by linarith) (by linarith) hT
    simp only [map_mul,Nat.cast_mul] at h
    apply h.trans
    dsimp only [E]
    gcongr
    · exact (hcols j).2
    · exact (hcols k).2
  exact actual_pair_error_ideal_bound rows cols hr hc B N hB hN hrows hcols a E hE error herr

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator IdealMobiusDivisorSum

def sourcePrincipalMajorant {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (G : Ideal O) (B N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  ‖paperRadialFourier W 0‖*((idealDivisors G).card *
    (((columnDyadicLength N+1:ℕ):ℝ)^2 *
      (2*divisorEnergyFactor ε hε N a a*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (4*N/T+Real.sqrt M*B^(α-1/2))))) +
  (idealDivisors G).card * (((columnDyadicLength N+1:ℕ):ℝ)^2 *
    ((2*nonzeroLatticeEnvelopeConstant*originalMiddleDecayConstant W)*
      divisorEnergyFactor ε hε N a a*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (N+(2*T)*Real.sqrt M*B^(α-1/2)))) +
  16384*B*N*((supportConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N))^ε)*
    (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l)*∑ j, ‖a j‖^2


lemma sourcePrincipalMajorant_nonneg {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (G : Ideal O) (B N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB : 0≤B) (hN : 0≤N) (_hM : 0≤M) (hT : 0≤T) :
    0≤sourcePrincipalMajorant s C l hexp deltaLoss hδ ε hε G B N M T a W := by
  have he := divisorEnergyFactor_nonneg ε hε N a a
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have hs := (supportConstant_pos ε hε).le
  have hlat := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := originalMiddleDecayConstant_nonneg W
  unfold sourcePrincipalMajorant
  positivity

lemma sourcePrincipalMajorant_mono {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (G : Ideal O) (B' B N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB' : 0≤B') (hB : B'≤B) (hN : 0≤N) (_hM : 0≤M) (hT : 0≤T) :
    sourcePrincipalMajorant s C l hexp deltaLoss hδ ε hε G B' N M T a W ≤
      sourcePrincipalMajorant s C l hexp deltaLoss hδ ε hε G B N M T a W := by
  have hB0 := hB'.trans hB
  have hα0 : 0≤α-1/2 := by linarith
  have he := divisorEnergyFactor_nonneg ε hε N a a
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have hs := (supportConstant_pos ε hε).le
  have hlat := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := originalMiddleDecayConstant_nonneg W
  unfold sourcePrincipalMajorant
  gcongr

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator


end

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum


theorem idealZeroMask_generator_eq_one (I G : Ideal O) (hcop : IsCoprime I G) :
    idealZeroMask I (idealGenerator G) = 1 := by
  apply if_neg
  rintro ⟨P,hP,hgen⟩
  have hPG : P ∣ G := by
    apply Ideal.dvd_iff_le.mpr
    rw [← span_idealGenerator G]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgen)
  exact (UniqueFactorizationMonoid.prime_of_normalized_factor P hP).not_isUnit
    (hcop.isRelPrime (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP) hPG)


end


end CanonicalQuadraticSieve

end

end OAI

end


