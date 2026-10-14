-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0185_parallel2
-- name    : PNT_ZeroFree_433_0185_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:16:09.034785+00:00
-- url     : https://prove2.me/theorems/df0aea10-6b48-440e-8db5-1ace77ba1fae
-- title:
--   Zero-free region foundations: CubicSieve.LogSeparation [0185_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.LogSeparation
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/LogSeparation.lean#L125-L613

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0073
import Definitions.Def_PNT_ZeroFree_433_0078
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0087
import Definitions.Def_PNT_ZeroFree_433_0154_parallel1
import Definitions.Def_PNT_ZeroFree_433_0182_parallel1
import Definitions.Def_PNT_ZeroFree_433_0183_parallel1
import Definitions.Def_PNT_ZeroFree_433_0184_parallel1
import Definitions.Def_PNT_ZeroFree_433_0185_parallel1
import Definitions.Def_PNT_ZeroFree_433_0197_parallel1
import Definitions.Def_PNT_ZeroFree_433_0237_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/LogSeparation.lean
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

namespace CanonicalCubeSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open FourierBridge JointLogSeparation


theorem reopening_norm_separation (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X n q : ℝ) (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : B ≤ n) (hn' : n ≤ Real.exp 1*B) (hq : 0 < q) :
    (Real.sqrt X : ℂ)⁻¹ * (Real.sqrt n : ℂ) * W (q*n^3/X) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          cubeFrequencyFactor (Real.log (n/B)) ξ * frequencyTwist V ξ (Real.log (q/ell)) := by
  have hn0 : 0 < n := lt_of_lt_of_le hB hn
  have hsep := reopening_separation_with_window W a b ha hs hW V hV
    (Real.log (n/B)) (Real.log (q/ell)) (cube_log_bin B n hB hn hn')
  rw [cube_log_argument B ell n q hB hell hn0 hq] at hsep
  rw [hX, cube_half_normalization_complex B ell n hB hell hn0, mul_assoc, hsep]


theorem completed_cube_norm_separation (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X n q : ℝ) (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : B ≤ n) (hn' : n ≤ Real.exp 1*B) (hq : 0 < q) :
    (n : ℂ)⁻¹ * (Real.sqrt (X/n^3) : ℂ)⁻¹ * W (q/(X/n^3)) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          cubeFrequencyFactor (Real.log (n/B)) ξ * frequencyTwist V ξ (Real.log (q/ell)) := by
  have hXp : 0 < X := hX ▸ mul_pos (pow_pos hB _) hell
  rw [completed_cube_half_weight_complex X n hXp (lt_of_lt_of_le hB hn), div_div_eq_mul_div]
  exact reopening_norm_separation W a b ha hs hW V hV B ell X n q hB hell hX hn hn' hq

def separatedCubeCoefficient {κ : Type*} (β : κ → ℂ) (n : κ → ℝ)
    (B ξ : ℝ) (v : κ) : ℂ := β v * cubeFrequencyFactor (Real.log (n v/B)) ξ

lemma separatedCubeCoefficient_bound {κ : Type*} (β : κ → ℂ) (n : κ → ℝ)
    (B ξ Γ : ℝ) (hB : 0 < B) (hΓ : 0 ≤ Γ) (v : κ)
    (hn : B ≤ n v) (hn' : n v ≤ Real.exp 1*B) (hβ : ‖β v‖ ≤ Γ) :
    ‖separatedCubeCoefficient β n B ξ v‖ ≤ Γ*Real.exp (1/2) := by
  unfold separatedCubeCoefficient
  rw [norm_mul]
  exact mul_le_mul hβ (cubeFrequencyFactor_bound _ ξ (cube_log_bin B _ hB hn hn').2)
    (norm_nonneg _) hΓ

theorem reopening_finite_sum_integrable {κ τ : Type*}
    (Q : Finset κ) (S : Finset τ) (β : κ → ℂ) (A : κ → τ → ℂ)
    (n : κ → ℝ) (q : τ → ℝ) (B ell : ℝ) (b V : 𝓢(ℝ,ℂ)) :
    Integrable (fun ξ : ℝ => b ξ * ∑v∈Q,∑j∈S,
      separatedCubeCoefficient β n B ξ v * A v j * frequencyTwist V ξ (Real.log (q j/ell))) := by
  have hi : Integrable (fun ξ : ℝ => ∑v∈Q,∑j∈S,
      (β v*A v j)*(b ξ*cubeFrequencyFactor (Real.log (n v/B)) ξ*
        frequencyTwist V ξ (Real.log (q j/ell)))) := by
    apply integrable_finsetSum
    intro v hv
    apply integrable_finsetSum
    intro j hj
    exact (reopening_integrable b V _ _).const_mul _
  convert! hi using 1
  funext ξ
  simp only [Finset.mul_sum, separatedCubeCoefficient]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem reopening_finite_sum {κ τ : Type*}
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (Q : Finset κ) (S : Finset τ) (β : κ → ℂ) (A : κ → τ → ℂ)
    (n : κ → ℝ) (q : τ → ℝ) (B ell X : ℝ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : ∀v∈Q,B ≤ n v) (hn' : ∀v∈Q,n v ≤ Real.exp 1*B)
    (hq : ∀j∈S,0 < q j) :
    (∑v∈Q,∑j∈S, (β v*A v j)*
      ((n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹ * W (q j/(X/(n v)^3)))) =
    ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ * ∑v∈Q,∑j∈S,
        separatedCubeCoefficient β n B ξ v * A v j *
          frequencyTwist V ξ (Real.log (q j/ell)) := by
  let G : ℝ → κ → τ → ℂ := fun ξ v j => (β v*A v j)*
    (reopeningCoefficient W a b ha hs hW ξ * cubeFrequencyFactor (Real.log (n v/B)) ξ *
      frequencyTwist V ξ (Real.log (q j/ell)))
  have hi (v : κ) (j : τ) : Integrable (fun ξ => G ξ v j) :=
    (reopening_integrable _ V _ _).const_mul _
  have hterm (v : κ) (hv : v∈Q) (j : τ) (hj : j∈S) :
      (β v*A v j)*((n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹ * W (q j/(X/(n v)^3))) =
        ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,G ξ v j := by
    rw [completed_cube_norm_separation W a b ha hs hW V hV B ell X (n v) (q j)
      hB hell hX (hn v hv) (hn' v hv) (hq j hj)]
    rw [show (∫ ξ : ℝ,G ξ v j) = (β v*A v j)*∫ ξ : ℝ,
        reopeningCoefficient W a b ha hs hW ξ * cubeFrequencyFactor (Real.log (n v/B)) ξ *
          frequencyTwist V ξ (Real.log (q j/ell)) from integral_const_mul _ _]
    ring
  calc
    _ = ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∑v∈Q,∑j∈S,∫ ξ : ℝ,G ξ v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j hj => hterm v hv j hj)
    _ = ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,∑v∈Q,∑j∈S,G ξ v j := by
      congr 1
      rw [integral_finsetSum _ (fun v hv => integrable_finsetSum _ (fun j hj => hi v j))]
      apply Finset.sum_congr rfl
      intro v hv
      exact (integral_finsetSum _ (fun j hj => hi v j)).symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [Finset.mul_sum, separatedCubeCoefficient]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [G]
      ring

end CanonicalCubeSeparation

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight

theorem rowTwist_primary_zero_of_mask (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) {P B : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPB : P∣B) (hm : m∈P) :
    rowTwist Ψ m f z (primaryGenerator B) = 0 := by
  have hx : m^6*f^4*z∈P := by
    have hm6 : m^6∈P := by
      rw [show m^6=m^5*m by ring]
      exact P.mul_mem_left (m^5) hm
    exact P.mul_mem_right z (P.mul_mem_right (f^4) hm6)
  by_cases hg : primaryGenerator B=0
  · rw [hg]
    change Ψ 0 * idealRowHom _ (Ideal.span {(0:ActualEisensteinCubic.O)}) = 0
    rw [Ideal.span_singleton_zero]
    change Ψ 0 * idealRowHom _ (0:Ideal ActualEisensteinCubic.O) = 0
    rw [map_zero (idealRowHom _),mul_zero]
  · change Ψ (primaryGenerator B) * idealRowHom _ (Ideal.span {primaryGenerator B}) = 0
    rw [(primaryGenerator_spec B hg).1,idealRowHom_zero_of_dvd _ hP hPB hx,mul_zero]

theorem cubeWeight_zero_of_prime_mask (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) {P B : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPB : P∣B) (hm : m∈P) :
    cubeWeight (rowTwist Ψ m f z) B = 0 :=
  cubeWeight_zero_of_mask _ B (rowTwist_primary_zero_of_mask Ψ m f z hP hPB hm)

theorem summand_cube_support (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D)
    (I B : Ideal ActualEisensteinCubic.O) (hn : summand (rowTwist Ψ m f z) W X I B≠0) :
    B∈outsideIdealsUpTo S D := by
  have hI : I≠0 := fun h=>hn (by rw [h,summand_zero_left])
  have hB : B≠0 := fun h=>hn (by rw [h,summand_zero_right])
  have hw : W ((Ideal.absNorm I:ℝ)*(Ideal.absNorm B:ℝ)^3/X)≠0 :=
    fun h=>hn (summand_zero_window _ W X I B h)
  have hsize := (div_le_iff₀ hX).mp (hW _ hw)
  have hb := (triple_scale_bounds (Ideal.absNorm I:ℝ) (Ideal.absNorm B:ℝ) 1
    (norm_at_least_one I hI) (norm_at_least_one B hB) (by norm_num)).2.1
  simp only [one_pow,mul_one] at hb
  apply mem_outsideIdealsUpTo.mpr
  refine ⟨?_,?_,?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (fun h=>hB (Ideal.absNorm_eq_zero_iff.mp h))
  · exact_mod_cast (hb.trans hsize).trans hD
  · intro P hP hPB
    have hz := cubeWeight_zero_of_prime_mask Ψ m f z (hSp P hP) hPB (hm P hP)
    exact hn (by simp only [summand,hz,mul_zero,zero_mul])


open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O


end

open ActualEisensteinCubic
open CompletedGauss hiding O


end CanonicalRowCompletion

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels


section
variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})


def canonicalSmoothedEnergy (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (H : Finset ι → ℂ) (K : ℝ) : ℝ :=
  (∑I∈labels,nonzeroRowMajorantSum
    (fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I)) K).re

theorem canonicalSmoothedEnergy_nonneg (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (H : Finset ι → ℂ) (K : ℝ) (hK : 0<K) :
    0≤canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K := by
  unfold canonicalSmoothedEnergy
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro I hI
  have he := finite_nonzero_row_energy_le_majorant
    (fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I)) ∅ K hK
    (by simp) (by simp)
  simpa using he

theorem canonicalSmoothedEnergy_zero_correction (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (H : Finset ι → ℂ) (K : ℝ) (hK : 0<K) :
    canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K=
      (∑I∈labels,∑'z:ActualEisensteinCubic.O,rowMajorant (‖eisEmbedding z‖^2/K)*
        (‖fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I) z‖^2:ℝ)).re-
      ∑I∈labels,‖fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I) 0‖^2 := by
  unfold canonicalSmoothedEnergy
  simp only [nonzeroRowMajorantSum_eq_sub _ K hK,Finset.sum_sub_distrib,Complex.sub_re,
    Complex.re_sum,Complex.ofReal_re]


def canonicalLogEnergy (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ → ℂ) (X K : ℝ) : ℝ :=
  canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels (fun S=>V (columnLog p X S)) K

end


end SecondPassArithmetic

end

end OAI

end


