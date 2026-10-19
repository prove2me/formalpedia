-- Prove2me | Definitions.Def_OAIQWERD000
-- name    : OAIQWERD000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T18:33:07.413739+00:00
-- url     : https://prove2.me/theorems/31fbd187-a74e-4ef1-acd2-6ce938daf689
-- title:
--   OpenAI entropy-rate dimension split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof of the entropy-rate dimension formula for self-similar measures on the line (`OAI.EntropyRateDimension.entropy_rate_dimension`). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/MeasureTheory/SelfSimilar` (OpenAI, *The entropy-rate dimension formula for self-similar measures on the line*, OpenAI Math Release, September 24, 2026, result family 148, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them are the Bernoulli shift `Bernoulli.shift`, the coding map and address measure of a system (`Coding.law`, `Coding.addressMeasure`, `Coding.exponent`), the finite and measure-theoretic entropies (`FiniteEntropy`, `MeasureEntropy`), the block and compressed systems (`System.blocks`, `System.compressed`), and the auxiliary functions of the ergodic theorems (`ErgodicAux.maxSum`, `ErgodicAux.boundedSums`, `ErgodicAux.tailError`). It also contains the lemmas those definitions use in their bodies (for example `FiniteCondition.mass_pos` and `MeasureEntropy.pairLaw_probability`, needed to build distributions and probability measures), and OpenAI's `@[simp]` lemmas `maxSum_zero` and `maxSum_succ`.
--
--   The definitions of the published statement (`System`, `System.affine`, `System.wordAffine`, `System.completeMap`, `System.wordWeight`, `System.mapSupport`, `System.mapMass`, `System.walkEntropy`, `System.entropyRate`, `System.lyapunov`, `System.SelfSimilar`, `lowerHausdorffDimension`) are not repeated: the bundle imports them from the published bundle `Def_SelfSimilar`. It imports no other bundle.
--
--   Modules: `BallIntegrability.lean`, `BallLimits.lean`, `BallRatios.lean`, `Basic.lean`, `Bernoulli.lean`, `BlockWords.lean`, `Boundary.lean`, `Coding.lean`, `CodingIntegrals.lean`, `Conditioning.lean`, `DigitSumset.lean`, `EntropyBudget.lean`, `ErgodicAverages.lean`, `ExactDimension.lean`, `FairPairs.lean`, `FiniteDistribution.lean`, `FiniteEntropy.lean`, `FiniteRefinement.lean`, `FiniteVariance.lean`, `GridCoupling.lean`, `InvariantLaw.lean`, `MeasureEntropy.lean`, `PairBands.lean`, `PairGain.lean`, `ProductLaw.lean`, `RadialLimit.lean`, `RadiusGrowth.lean`, `RandomGrid.lean`, `RetainedLoss.lean`, `SuffixLaw.lean`, `SumsetBound.lean`, `TailConvolution.lean`, `TranslationGain.lean`, `TriangularAverages.lean`, `TypedLaw.lean`, `UpperBound.lean`, `WindowCount.lean`, `WindowGain.lean`, `WordAverage.lean`, `WordTypes.lean`.
--
--   The theorems of the development that the definitions do not need are proved in the four solutions of this split. Three of them prove the published classical statements `OAI.EntropyRateDimension.ErgodicAux.ae_tendsto_average` (Birkhoff's pointwise ergodic theorem, ergodic case), `OAI.EntropyRateDimension.ErgodicAux.ae_tendsto_triangle` (Maker's generalized ergodic theorem, ergodic case) and `OAI.EntropyRateDimension.Bernoulli.shift_ergodic` (Bernoulli shifts are ergodic), which are stated with Mathlib's definitions only, so that other developments can use them; the fourth proves `OAI.EntropyRateDimension.entropy_rate_dimension` from them.
-- source:
--   OpenAI, The entropy-rate dimension formula for self-similar measures on the line, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 148; Apache License 2.0); definitions carved from lean/OAI/MeasureTheory/SelfSimilar at commit adc7f12

import Mathlib
import Definitions.Def_SelfSimilar

section
-- module Solutions.OAIQW_EntropyRateDimension.Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace System
variable {ι : Type uι} [Fintype ι]

theorem wordWeight_pos (S : System ι) {n : ℕ} (w : Fin n → ι) :
    0 < S.wordWeight w :=
  Finset.prod_pos (fun i _ => S.weight_pos (w i))

theorem wordWeight_sum (S : System ι) (n : ℕ) :
    ∑ w : Fin n → ι, S.wordWeight w = 1 := by
  classical
  simpa [wordWeight, S.weight_sum] using
    (Fintype.prod_sum (fun (_ : Fin n) i => S.weight i)).symm

theorem mapMass_sum (S : System ι) (n : ℕ) :
    ∑ g ∈ S.mapSupport n, S.mapMass n g = 1 := by
  classical
  simp only [mapSupport, mapMass]
  rw [Finset.sum_fiberwise_of_maps_to]
  · exact S.wordWeight_sum n
  · exact fun w hw => Finset.mem_image_of_mem _ hw

theorem mapMass_pos (S : System ι) {n : ℕ} {g : ℝ × ℝ}
    (hg : g ∈ S.mapSupport n) : 0 < S.mapMass n g := by
  classical
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hg
  apply lt_of_lt_of_le (S.wordWeight_pos w)
  apply Finset.single_le_sum (fun v _ => (S.wordWeight_pos v).le)
  simp

end System

end EntropyRateDimension
end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.FiniteEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteEntropy

noncomputable def entropy {α : Type uα} (s : Finset α) (p : α → ℝ) : ℝ :=
  ∑ i ∈ s, Real.negMulLog (p i)

noncomputable def mass {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α) (p : α → ℝ)
    (f : α → β) (b : β) : ℝ := ∑ a ∈ s.filter (fun a => f a = b), p a

noncomputable def observableEntropy {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α)
    (p : α → ℝ) (f : α → β) : ℝ := entropy (s.image f) (mass s p f)

theorem mass_nonneg {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α) (p : α → ℝ)
    (f : α → β) (hp : ∀ a ∈ s, 0 ≤ p a) (b : β) : 0 ≤ mass s p f b := by
  classical
  exact Finset.sum_nonneg (fun a ha => hp a (Finset.mem_filter.mp ha).1)

theorem mass_sum {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α) (p : α → ℝ) (f : α → β) :
    ∑ b ∈ s.image f, mass s p f b = ∑ a ∈ s, p a := by
  classical
  simpa only [mass] using
    (Finset.sum_fiberwise_of_maps_to (s := s)
      (fun a ha => Finset.mem_image_of_mem f ha) p)

theorem mass_eq_zero_of_not_mem {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α)
    (p : α → ℝ) (f : α → β) {b : β} (hb : b ∉ s.image f) : mass s p f b = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a ha
  exact (hb (Finset.mem_image.mpr ⟨a, (Finset.mem_filter.mp ha).1,
    (Finset.mem_filter.mp ha).2⟩)).elim

noncomputable def conditionalEntropy {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) : ℝ :=
  observableEntropy s p (fun a => (f a, g a)) - observableEntropy s p g

noncomputable def js {α : Type uα} (s : Finset α) (p q : α → ℝ) : ℝ :=
  entropy s (fun a => (p a+q a)/2)-(entropy s p+entropy s q)/2

noncomputable def totalVariation {α : Type uα} (s : Finset α) (p q : α → ℝ) : ℝ :=
  (∑ a ∈ s, |p a-q a|)/2

end FiniteEntropy
end EntropyRateDimension
end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.FiniteDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension

structure FiniteDistribution (α : Type uα) where
  weight : α → ℝ
  support : Finset α
  nonneg : ∀ a, 0 ≤ weight a
  vanish : ∀ a ∉ support, weight a=0
  sum_one : ∑ a ∈ support, weight a=1

namespace FiniteDistribution

attribute [local instance] Classical.propDecidable

noncomputable def entropy {α : Type uα} (p : FiniteDistribution α) : ℝ :=
  ∑' a, Real.negMulLog (p.weight a)

noncomputable def tv {α : Type uα} (p q : FiniteDistribution α) : ℝ :=
  (∑' a, |p.weight a-q.weight a|)/2

theorem sum_on {α : Type uα} (p : FiniteDistribution α) (s : Finset α)
    (hs : p.support ⊆ s) : ∑ a ∈ s, p.weight a=1 := by
  rw [← p.sum_one]
  exact (Finset.sum_subset hs (fun a _ ha => p.vanish a ha)).symm

noncomputable def mix {α : Type uα} (p q : FiniteDistribution α) : FiniteDistribution α := by
  classical
  refine ⟨fun a => (p.weight a+q.weight a)/2,p.support ∪ q.support,
    fun a => div_nonneg (add_nonneg (p.nonneg a) (q.nonneg a)) (by norm_num), ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_union, not_or] at ha
    rw [p.vanish a ha.1, q.vanish a ha.2]
    norm_num
  · rw [← Finset.sum_div, Finset.sum_add_distrib,
      p.sum_on _ Finset.subset_union_left, q.sum_on _ Finset.subset_union_right]
    norm_num

noncomputable def js {α : Type uα} (p q : FiniteDistribution α) : ℝ :=
  (p.mix q).entropy-(p.entropy+q.entropy)/2

noncomputable def map {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f : α → β) : FiniteDistribution β := by
  classical
  refine ⟨FiniteEntropy.mass p.support p.weight f,p.support.image f,
    FiniteEntropy.mass_nonneg _ _ _ (fun a _ => p.nonneg a), ?_, ?_⟩
  · exact fun b hb => FiniteEntropy.mass_eq_zero_of_not_mem p.support p.weight f hb
  · exact (FiniteEntropy.mass_sum ..).trans p.sum_one

noncomputable def translate (p : FiniteDistribution ℤ) (j : ℤ) : FiniteDistribution ℤ :=
  p.map (fun a => a+j)

end FiniteDistribution

end EntropyRateDimension
end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.MeasureEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace MeasureEntropy

noncomputable def mass {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) (b : β) : ℝ := μ.real {x | f x = b}

noncomputable def entropy {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) : ℝ := ∑' b, Real.negMulLog (mass μ f b)

theorem mass_nonneg {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) (b : β) : 0 ≤ mass μ f b := ENNReal.toReal_nonneg

theorem mass_eq_zero_of_ae {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) {b : β} (hb : b ∉ s) :
    mass μ f b = 0 := by
  have hh : μ {x | f x = b} = 0 := measure_mono_null (by
    intro x hx
    change f x = b at hx
    change f x ∉ s
    simpa only [hx] using hb) (ae_iff.mp hs)
  simp only [mass, Measure.real_def, hh, ENNReal.toReal_zero]

theorem mass_sum {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) :
    ∑ b ∈ s, mass μ f b = 1 := by
  classical
  have hd : (↑s : Set β).PairwiseDisjoint (fun b => {x | f x = b}) := by
    intro b _ c _ hbc
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hbc (hx.symm.trans hy)
  have hm : ∀ b ∈ s, MeasurableSet {x | f x = b} :=
    fun b _ => (measurableSet_singleton b).preimage hf
  have he : (⋃ b ∈ s, {x | f x = b}) = {x | f x ∈ s} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨b,hb,hxb⟩
      simpa only [hxb] using hb
    · intro hx
      exact ⟨f x,hx,rfl⟩
  have hu : μ (⋃ b ∈ s, {x | f x = b}) = 1 := by
    rw [he]
    calc
      _ = μ Set.univ := measure_congr (by
        filter_upwards [hs] with x hx
        apply propext
        change (f x ∈ s) ↔ True
        exact iff_true_intro hx)
      _ = 1 := measure_univ
  rw [measure_biUnion_finset hd hm] at hu
  have he' := congrArg ENNReal.toReal hu
  simpa only [ENNReal.toReal_sum (fun b _ => measure_ne_top μ _), ENNReal.toReal_one, mass, Measure.real_def] using he'

def CompactlyCarried (μ : Measure ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ μ (Set.Icc (-B) B)ᶜ = 0

noncomputable def label (s u x : ℝ) : ℤ := ⌊x/s+u⌋

noncomputable def grid (μ : Measure ℝ) (s u : ℝ) : ℝ := entropy μ (label s u)

noncomputable def averaged (μ : Measure ℝ) (s : ℝ) : ℝ :=
  ∫ u in Set.Icc (0 : ℝ) 1, grid μ s u

theorem label_measurable (s u : ℝ) : Measurable (label s u) :=
  ((measurable_id.div_const s).add_const u).floor

theorem label_in_interval {B s u x : ℝ} (hs : 0 < s) (hx : x ∈ Set.Icc (-B) B) :
    label s u x ∈ Finset.Icc ⌊-B/s+u⌋ ⌊B/s+u⌋ := by
  exact Finset.mem_Icc.mpr ⟨Int.floor_le_floor (by linarith [(div_le_div_iff_of_pos_right hs).mpr hx.1]),
    Int.floor_le_floor (by linarith [(div_le_div_iff_of_pos_right hs).mpr hx.2])⟩

theorem label_ae_finite (μ : Measure ℝ) {B s u : ℝ} (hs : 0 < s)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) :
    ∀ᵐ x ∂μ, label s u x ∈ Finset.Icc ⌊-B/s+u⌋ ⌊B/s+u⌋ := by
  have hb : ∀ᵐ x ∂μ, x ∈ Set.Icc (-B) B := ae_iff.mpr hB
  exact hb.mono (fun _ hx => label_in_interval hs hx)

noncomputable def relativeLabel (s t u v x : ℝ) : ℤ :=
  label s u x - ⌊(t/s)*(label t v x : ℝ)+u-(t/s)*v⌋

noncomputable def fairShift (μ : Measure ℝ) (v : ℝ) : Measure ℝ :=
  ∑ i : Fin 2, ENNReal.ofReal (1/2 : ℝ) • μ.map (fun x => x+(i : ℝ)*v)

noncomputable def observationLaw {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) :
    FiniteDistribution β :=
  ⟨mass μ f,s,mass_nonneg μ f,fun _b hb => mass_eq_zero_of_ae μ f s hs hb,
    mass_sum μ f hf s hs⟩

noncomputable def gridLaw (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) : FiniteDistribution ℤ :=
  observationLaw μ (label s u) (label_measurable s u)
    (Finset.Icc ⌊-hμ.choose/s+u⌋ ⌊hμ.choose/s+u⌋)
    (label_ae_finite μ hs hμ.choose_spec.2)

noncomputable def gridDeficit (μ : Measure ℝ) (s u : ℝ) : ℝ :=
  grid (fairShift μ s) s u-grid μ s u

noncomputable def deficit (μ : Measure ℝ) (s : ℝ) : ℝ :=
  Real.log 2-(averaged μ s-averaged μ (2*s))

end MeasureEntropy
end EntropyRateDimension
end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.RandomGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace RandomGrid

local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  ⟨by simp⟩

noncomputable def hit (c : AddCircle (1 : ℝ)) (r : ℝ) (u : AddCircle (1 : ℝ)) : ℝ :=
  if dist u c ≤ r then 1 else 0

end RandomGrid

end EntropyRateDimension
end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.Boundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace Boundary
open Set

noncomputable def increment (a u : ℝ) : ℝ := (⌊u+a⌋ : ℝ)-(⌊u⌋ : ℝ)

end Boundary

end EntropyRateDimension
end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.TranslationGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace MeasureEntropy

attribute [local instance] Classical.propDecidable

noncomputable def information {α : Type uα} {β : Type uβ} [MeasurableSpace α]
    (μ ν : Measure α) (f : α → β) : ℝ :=
  entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) f-(entropy μ f+entropy ν f)/2

noncomputable def gridInformation (μ : Measure ℝ) (v s u : ℝ) : ℝ :=
  information μ (μ.map (fun x => x+v)) (label s u)

end MeasureEntropy

end EntropyRateDimension

end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.FairPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uα uβ

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace FairPairs

structure Law where
  support : Finset ℝ
  prob : ℝ → ℝ
  prob_pos : ∀ x ∈ support, 0 < prob x
  prob_sum : ∑ x ∈ support, prob x = 1

noncomputable def Law.edges (ν : Law) (ℓ : ℤ) : Finset (ℝ × ℝ) := by
  classical
  exact (ν.support ×ˢ ν.support).filter fun e =>
    e.1 < e.2 ∧ (2 : ℝ) ^ (-ℓ) ≤ e.2 - e.1 ∧ e.2 - e.1 < (2 : ℝ) ^ (1 - ℓ)

noncomputable def incident {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) (x : ℝ) : ℝ := by
  classical
  exact ∑ e, ((if e.val.1 = x then w e / 2 else 0) +
      (if e.val.2 = x then w e / 2 else 0))

def Feasible {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) : Prop :=
  (∀ e, 0 ≤ w e) ∧ ∀ x ∈ ν.support, incident w x ≤ ν.prob x

noncomputable def capacity (ν : Law) (ℓ : ℤ) : ℝ :=
  sSup {t : ℝ | ∃ w : ν.edges ℓ → ℝ, Feasible w ∧ ∑ e, w e = t}

noncomputable def bandIndex (u : ℝ) : ℤ := -⌊Real.logb 2 u⌋

noncomputable def conditionalCoupling {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) (x y : ℝ) : ℝ :=
  if g x = g y then ν.prob x * ν.prob y / FiniteEntropy.mass ν.support ν.prob g (g x) else 0

end FairPairs

end EntropyRateDimension

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.ProductLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace ProductLaw

variable {ι : Type uι} {α : Type uα} [Fintype ι] [DecidableEq ι] [Fintype α]

noncomputable def weight (p : ι → α → ℝ) (x : ι → α) : ℝ := ∏ i, p i (x i)

variable {β : Type uβ} [DecidableEq β]

noncomputable def cellMass (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β) (i : ι) : ℝ :=
  ∑ a, if g i a = c i then p i a else 0

noncomputable def conditional (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β) (i : ι) (a : α) : ℝ :=
  (if g i a = c i then p i a else 0) / cellMass p g c i

end ProductLaw

end EntropyRateDimension
end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.GridCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace RandomGrid

attribute [local instance] unitCircleProbability

noncomputable def shift (u : AddCircle (1 : ℝ)) : ℝ := (AddCircle.equivIco 1 0 u).val

noncomputable def cell (δ : ℝ) (u : AddCircle (1 : ℝ)) (x : ℝ) : ℤ :=
  ⌊x / δ + shift u⌋

end RandomGrid

end EntropyRateDimension
end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.FiniteRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteRefinement

open FiniteEntropy

variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

noncomputable def cellMean (p : α → ℝ) (v : α → ℝ) (g : α → β) (b : β) : ℝ :=
  ∑ a, ((if g a = b then p a else 0) / mass Finset.univ p g b) * v a

end FiniteRefinement

end EntropyRateDimension
end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.SumsetBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uβ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FairPairs

open FiniteEntropy

noncomputable def Law.bandSupport (ν : Law) : Finset ℤ := by
  classical
  exact (ν.support ×ˢ ν.support).image (fun e => bandIndex |e.2-e.1|)

noncomputable def Law.bandCost (ν : Law) (R : ℝ) : ℝ := by
  classical
  exact ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ R),
    (2 : ℝ)^(1-ℓ)*capacity ν ℓ

noncomputable def Law.partitionEntropy (ν : Law) (k : ℕ) (g : ℝ → List ℤ) : ℝ := by
  classical
  exact conditionalEntropy Finset.univ
    (ProductLaw.weight (fun _ : Fin k => fun a : ν.support => ν.prob a))
    (fun x i => g (x i)) (fun x => ∑ i, (x i : ℝ))

noncomputable def Law.refinementCost (ν : Law) (k : ℕ) (R : ℝ) : ℝ :=
  (352*k^4/R)*ν.bandCost R*Real.log 2

noncomputable def Law.sumset (ν : Law) (k : ℕ) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun x : Fin k → ν.support => ∑ i, (x i : ℝ))

noncomputable def Law.shannonEntropy (ν : Law) : ℝ := entropy ν.support ν.prob / Real.log 2

noncomputable def Law.gridEntropy (ν : Law) (ρ : ℝ) : ℝ := by
  classical
  exact observableEntropy ν.support ν.prob (fun x => ⌊x/ρ⌋) / Real.log 2

end FairPairs

end EntropyRateDimension
end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.WordTypes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace System
variable {ι : Type uι} [Fintype ι]

theorem wordAffine_slope (S : System ι) (w : List ι) :
    (S.wordAffine w).1 = (w.map S.ratio).prod := by
  induction w with
  | nil => rfl
  | cons i w ih => simpa only [wordAffine,List.map_cons,List.prod_cons] using congrArg (S.ratio i * ·) ih

theorem completeMap_slope (S : System ι) {n : ℕ} (w : Fin n → ι) :
    (S.completeMap w).1 = ∏ j, S.ratio (w j) := by
  rw [completeMap,wordAffine_slope,List.map_ofFn,List.prod_ofFn]
  rfl

theorem completeMap_slope_ne_zero (S : System ι) {n : ℕ} (w : Fin n → ι) :
    (S.completeMap w).1 ≠ 0 := by
  rw [completeMap_slope]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => abs_pos.mp (S.ratio_pos (w j)))

end System
end EntropyRateDimension

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.DigitSumset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uβ

section

open scoped BigOperators
namespace EntropyRateDimension
namespace DigitSumset

noncomputable def counts {α : Type uα} {β : Type uβ} [Fintype α] [Fintype β] {k : ℕ}
    (w : Fin k → β → α) : β → α → Fin (k+1) := by
  classical
  exact fun j a => ⟨(Finset.univ.filter (fun t => w t j=a)).card,
    Nat.lt_succ_of_le ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Fintype.card_fin k))⟩

noncomputable def sumset (S : Finset ℝ) (k : ℕ) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun w : Fin k → S => ∑ t, (w t : ℝ))

end DigitSumset
end EntropyRateDimension

end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.Bernoulli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology

namespace EntropyRateDimension
namespace Bernoulli

variable {α : Type uα} [MeasurableSpace α]

def shift (ω : ℕ → α) (n : ℕ) : α := ω (n+1)

end Bernoulli
end EntropyRateDimension
end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.Coding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
namespace EntropyRateDimension
namespace Coding
open Filter Set
open scoped Topology

variable {ι : Type uι} [Fintype ι] [Nonempty ι]

def shift (ω : ℕ → ι) (n : ℕ) : ι := ω (n+1)

def slope (S : System ι) (ω : ℕ → ι) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, S.ratio (ω j)

def term (S : System ι) (ω : ℕ → ι) (n : ℕ) : ℝ :=
  slope S ω n * S.offset (ω n)

noncomputable def point (S : System ι) (ω : ℕ → ι) : ℝ := ∑' n, term S ω n

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def symbolMeasure (S : System ι) : Measure ι :=
  ∑ i, ENNReal.ofReal (S.weight i) • Measure.dirac i

noncomputable def addressMeasure (S : System ι) : Measure (ℕ → ι) :=
  Measure.infinitePi fun _ : ℕ => symbolMeasure S

noncomputable def law (S : System ι) : Measure ℝ := (addressMeasure S).map (point S)

end Coding
end EntropyRateDimension

end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.InvariantLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
namespace EntropyRateDimension.System
open MeasureTheory Filter Set
open scoped Topology BigOperators
variable {ι : Type uι} [Fintype ι]

noncomputable def average (S : System ι) (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => f
  | n+1 => fun x => ∑ i, S.weight i * average S f n (S.affine i x)

end EntropyRateDimension.System

end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.BallRatios
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace EntropyRateDimension
namespace BallRatios

abbrev Radius := {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) ≤ 1}

noncomputable def maximal (μ ν : Measure ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ q : Radius, μ (closedBall x (q.val : ℝ)) / ν (closedBall x (q.val : ℝ))

noncomputable def logEnvelope (μ ν : Measure ℝ) (x : ℝ) : ℝ :=
  max 0 (Real.log (maximal μ ν x).toReal)

noncomputable def logRatio (μ ν : Measure ℝ) (x r : ℝ) : ℝ :=
  Real.log (μ (closedBall x r) / ν (closedBall x r)).toReal

end BallRatios
end EntropyRateDimension

end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.BallIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace EntropyRateDimension
open MeasureTheory Metric Set Filter
open scoped Topology BigOperators
namespace System
variable {ι : Type uι} [Fintype ι]

noncomputable def component (S : System ι) (μ : Measure ℝ) (i : ι) : Measure ℝ :=
  ENNReal.ofReal (S.weight i) • μ.map (S.affine i)

instance component_finite (S : System ι) (μ : Measure ℝ) [IsFiniteMeasure μ] (i : ι) :
    IsFiniteMeasure (S.component μ i) := by
  constructor
  simp only [component,Measure.smul_apply,smul_eq_mul]
  exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)

end System

namespace BallRatios
noncomputable def information (μ : Measure ℝ) (x r : ℝ) : ℝ :=
  -Real.log (μ.real (closedBall x r))

end BallRatios

end EntropyRateDimension

end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.CodingIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter EntropyRateDimension.Bernoulli
open scoped Topology BigOperators ENNReal
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local instance instMeasurableSpace_solutions : MeasurableSpace ι := ⊤

local instance instMeasurableSingletonClass_solutions_r0d8c31_1 : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
noncomputable def envelope (S : System ι) (ω : ℕ → ι) : ℝ :=
  BallRatios.logEnvelope (law S) (S.component (law S) (ω 0)) (point S ω)

noncomputable def corr (S : System ι) (n : ℕ) (ω : ℕ → ι) : ℝ :=
  BallRatios.logRatio (law S) (S.component (law S) (ω 0)) (point S ω) |slope S ω n|

noncomputable def corrLimit (S : System ι) (ω : ℕ → ι) : ℝ :=
  Real.log ((law S).rnDeriv (S.component (law S) (ω 0)) (point S ω)).toReal

end EntropyRateDimension.Coding

end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.ErgodicAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace EntropyRateDimension
namespace ErgodicAux

variable {α : Type uα}

def maxSum (T : α → α) (f : α → ℝ) : ℕ → α → ℝ
  | 0, _ => 0
  | n+1, x => max 0 (f x + maxSum T f n (T x))

@[simp] theorem maxSum_zero (T : α → α) (f : α → ℝ) (x : α) :
    maxSum T f 0 x = 0 := rfl

@[simp] theorem maxSum_succ (T : α → α) (f : α → ℝ) (n : ℕ) (x : α) :
    maxSum T f (n+1) x = max 0 (f x + maxSum T f n (T x)) := rfl

variable [MeasurableSpace α] {μ : Measure α}

def boundedSums (T : α → α) (f : α → ℝ) : Set α :=
  {x | BddAbove (Set.range (fun n : ℕ => birkhoffSum T f n x))}

end ErgodicAux
end EntropyRateDimension

end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.TriangularAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace EntropyRateDimension.ErgodicAux

variable {α : Type uα}

noncomputable def tailError (f : ℕ → α → ℝ) (g : α → ℝ) (N : ℕ) (x : α) : ℝ :=
  ⨆ k : ℕ, |f (N+k) x - g x|

end EntropyRateDimension.ErgodicAux

end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.BallLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter
open EntropyRateDimension.Bernoulli EntropyRateDimension.ErgodicAux
open scoped Topology BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local instance instMeasurableSpace_solutions_1 : MeasurableSpace ι := ⊤

local instance instMeasurableSingletonClass_solutions_1_r0d8c31_1 : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
noncomputable def clippedCorr (S : System ι) (n : ℕ) (ω : ℕ → ι) : ℝ :=
  max 0 (min (envelope S ω) (corr S n ω))
noncomputable def clippedLimit (S : System ι) (ω : ℕ → ι) : ℝ :=
  max 0 (min (envelope S ω) (corrLimit S ω))

noncomputable def weightObs (S : System ι) (ω : ℕ → ι) : ℝ := -Real.log (S.weight (ω 0))
noncomputable def contractionObs (S : System ι) (ω : ℕ → ι) : ℝ := -Real.log |S.ratio (ω 0)|

noncomputable def prefixInfo (S : System ι) (n : ℕ) (ω : ℕ → ι) : ℝ :=
  BallRatios.information (law S) (point S ω) |slope S ω n|

noncomputable def infoRate (S : System ι) : ℝ :=
  (∫ ω, weightObs S ω ∂addressMeasure S) - (∫ ω, clippedLimit S ω ∂addressMeasure S)

end EntropyRateDimension.Coding

end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.RadiusGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter
open EntropyRateDimension.ErgodicAux
open scoped Topology BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local instance instMeasurableSpace_solutions_2 : MeasurableSpace ι := ⊤

local instance instMeasurableSingletonClass_solutions_2_r0d8c31_1 : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
noncomputable def exponent (S : System ι) : ℝ := infoRate S / (S.lyapunov * Real.log 2)

end EntropyRateDimension.Coding

end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.RadialLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
open Set Filter
open scoped Topology
namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter
open scoped Topology BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local instance instMeasurableSpace_solutions_3 : MeasurableSpace ι := ⊤

end EntropyRateDimension.Coding

end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.ExactDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
open Set Filter
open scoped Topology

namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter
open scoped Topology
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local instance instMeasurableSpace_solutions_4 : MeasurableSpace ι := ⊤

end EntropyRateDimension.Coding

namespace EntropyRateDimension.System
open MeasureEntropy
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local instance instMeasurableSpace : MeasurableSpace ι := ⊤

end EntropyRateDimension.System

end

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.UpperBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uM

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

def wordMap (S : System ι) {n : ℕ} (w : Fin n → ι) (x : ℝ) : ℝ :=
  (S.completeMap w).1*x+(S.completeMap w).2

theorem completeMap_abs_lt_one (S : System ι) {n : ℕ} (hn : 0 < n) (w : Fin n → ι) :
    |(S.completeMap w).1| < 1 := by
  rw [completeMap_slope,Finset.abs_prod]
  calc
    _ < ∏ j : Fin n, (1 : ℝ) := Finset.prod_lt_prod_of_nonempty
      (fun j _ => S.ratio_pos (w j)) (fun j _ => S.ratio_lt_one (w j))
      ⟨⟨0,hn⟩,Finset.mem_univ _⟩
    _ = 1 := by simp

noncomputable def compressed (S : System ι) {n : ℕ} (hn : 0 < n) : System (S.mapSupport n) where
  ratio g := g.val.1
  offset g := g.val.2
  weight g := S.mapMass n g.val
  ratio_pos g := by
    obtain ⟨w,_,hw⟩ := Finset.mem_image.mp g.property
    rw [← hw]
    exact abs_pos.mpr (S.completeMap_slope_ne_zero w)
  ratio_lt_one g := by
    obtain ⟨w,_,hw⟩ := Finset.mem_image.mp g.property
    rw [← hw]
    exact S.completeMap_abs_lt_one hn w
  weight_pos g := S.mapMass_pos g.property
  weight_sum := by
    classical
    rw [← Finset.sum_subtype (S.mapSupport n) (fun _ => Iff.rfl)]
    exact S.mapMass_sum n

end EntropyRateDimension.System

namespace EntropyRateDimension.Coding
open MeasureTheory
open scoped BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local instance instMeasurableSpace_solutions_5 : MeasurableSpace ι := ⊤

end EntropyRateDimension.Coding

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.Conditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uβ

namespace EntropyRateDimension.FairPairs
open MeasureTheory FiniteEntropy
open scoped BigOperators ENNReal

noncomputable def Law.ofObservable {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 < p a) (hp1 : ∑ a ∈ s, p a=1) (f : α → ℝ) : Law := by
  classical
  exact ⟨s.image f, mass s p f, by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.sum_pos' (fun a ha => (hp a (Finset.mem_filter.mp ha).1).le)
      ⟨a,Finset.mem_filter.mpr ⟨ha,rfl⟩,hp a ha⟩,
    (mass_sum s p f).trans hp1⟩

@[simp] theorem Law.ofObservable_support {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 < p a) (hp1 : ∑ a ∈ s, p a=1) (f : α → ℝ) :
    (Law.ofObservable s p hp hp1 f).support=s.image f := rfl

@[simp] theorem Law.ofObservable_prob {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 < p a) (hp1 : ∑ a ∈ s, p a=1) (f : α → ℝ) :
    (Law.ofObservable s p hp hp1 f).prob=mass s p f := rfl

@[simp] theorem Law.ofObservable_entropy {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 < p a) (hp1 : ∑ a ∈ s, p a=1) (f : α → ℝ) :
    (Law.ofObservable s p hp hp1 f).shannonEntropy=observableEntropy s p f/Real.log 2 := rfl

end EntropyRateDimension.FairPairs

namespace EntropyRateDimension.FiniteCondition
open FiniteEntropy FairPairs MeasureTheory
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

noncomputable def fiber (tag : α → β) (a : α) : Finset α :=
  Finset.univ.filter (fun v => tag v=tag a)

noncomputable def mass (p : α → ℝ) (tag : α → β) (a : α) : ℝ :=
  ∑ v ∈ fiber tag a, p v

theorem mass_pos (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (a : α) :
    0 < mass p tag a := by
  classical
  exact Finset.sum_pos' (fun v _ => (hp v).le) ⟨a,by simp [fiber],hp a⟩

noncomputable def posterior (p : α → ℝ) (tag : α → β) (a v : α) : ℝ :=
  if tag v=tag a then p v/mass p tag a else 0

theorem fiber_normalized_sum (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (a : α) :
    ∑ v ∈ fiber tag a, p v/mass p tag a=1 := by
  rw [← Finset.sum_div]
  exact div_self (mass_pos p hp tag a).ne'

noncomputable def law (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (a : α) (f : α → ℝ) : Law :=
  Law.ofObservable (fiber tag a) (fun v => p v/mass p tag a)
    (fun v _ => div_pos (hp v) (mass_pos p hp tag a)) (fiber_normalized_sum p hp tag a) f

end EntropyRateDimension.FiniteCondition

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.PairGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uβ

namespace EntropyRateDimension.MeasureEntropy
open MeasureTheory
open scoped BigOperators ENNReal

noncomputable def shiftLaw (μ : Measure ℝ) (b : ℝ) : Measure ℝ := μ.map (fun x => x+b)

instance shiftLaw_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] (b : ℝ) :
    IsProbabilityMeasure (shiftLaw μ b) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const b).aemeasurable).2 inferInstance

noncomputable def window (μ : Measure ℝ) (s t : ℝ) : ℝ := averaged μ s-averaged μ t

noncomputable def pairLaw (μ : Measure ℝ) (x y : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1/2 : ℝ) • shiftLaw μ x+ENNReal.ofReal (1/2 : ℝ) • shiftLaw μ y

instance pairLaw_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] (x y : ℝ) :
    IsProbabilityMeasure (pairLaw μ x y) := by
  constructor
  simpa [pairLaw,Measure.add_apply,Measure.smul_apply,measure_univ] using ENNReal.inv_two_add_inv_two

noncomputable def finiteConv (ν : FairPairs.Law) (a : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  ∑ x : ν.support, ENNReal.ofReal (ν.prob x) • shiftLaw μ (a*x)

end EntropyRateDimension.MeasureEntropy

namespace EntropyRateDimension.FairPairs
open MeasureTheory MeasureEntropy
open scoped BigOperators ENNReal

noncomputable def residual {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) (x : ν.support) : ℝ :=
  ν.prob x-incident w x

noncomputable def decompositionWeight {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) :
    ν.edges ℓ ⊕ ν.support → ℝ := Sum.elim w (residual w)

noncomputable def decompositionLaw {ν : Law} {ℓ : ℤ} (μ : Measure ℝ) (a : ℝ) :
    ν.edges ℓ ⊕ ν.support → Measure ℝ := Sum.elim
      (fun e => pairLaw μ (a*e.val.1) (a*e.val.2))
      (fun x => shiftLaw μ (a*x))

instance decompositionLaw_probability {ν : Law} {ℓ : ℤ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : ℝ) (z : ν.edges ℓ ⊕ ν.support) : IsProbabilityMeasure (decompositionLaw μ a z) := by
  cases z <;> dsimp [decompositionLaw] <;> infer_instance

end EntropyRateDimension.FairPairs

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.TypedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uα uβ uγ uM

namespace EntropyRateDimension.Typed
open MeasureTheory FairPairs FiniteCondition
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

abbrev tagWord (tag : α → β) {n : ℕ} (w : Fin n → α) : Fin n → β := fun j => tag (w j)

noncomputable def prob (S : System α) (tag : α → β) {n : ℕ} (w v : Fin n → α) : ℝ :=
  ∏ j, posterior S.weight tag (w j) (v j)

noncomputable def law (S : System α) (tag : α → β) {n : ℕ} (w : Fin n → α) : Law :=
  FiniteCondition.law S.wordWeight (fun v => S.wordWeight_pos v) (tagWord tag) w
    (fun v => (S.completeMap v).2)

noncomputable def tail (S : System α) (tag : α → β) (μ : Measure ℝ)
    {n : ℕ} (w : Fin n → α) : Measure ℝ :=
  ∑ v, ENNReal.ofReal (prob S tag w v) • μ.map (S.wordMap v)

end EntropyRateDimension.Typed

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.TailConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs FiniteCondition
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

noncomputable def scaledTail (S : System α) (tag : α → β) (μ : Measure ℝ)
    (a : ℝ) {n : ℕ} (w : Fin n → α) : Measure ℝ :=
  (tail S tag μ w).map (fun x => a*x)

end EntropyRateDimension.Typed

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.FiniteVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

namespace EntropyRateDimension.System
open scoped BigOperators
variable {α : Type uα} [Fintype α]

noncomputable def wordDepth (S : System α) {n : ℕ} (w : Fin n → α) : ℝ :=
  -Real.log |(S.completeMap w).1|/Real.log 2

noncomputable def letterDepth (S : System α) (a : α) : ℝ :=
  -Real.log |S.ratio a|/Real.log 2

noncomputable def depthVariance (S : System α) : ℝ :=
  ∑ a, S.weight a*(S.letterDepth a-S.lyapunov)^2

end EntropyRateDimension.System

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.SuffixLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uβ uγ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

noncomputable def listLaw (S : System α) (tag : α → β) (W : List α) : Law :=
  law S tag W.get
noncomputable def listTail (S : System α) (tag : α → β) (μ : Measure ℝ) (W : List α) : Measure ℝ :=
  tail S tag μ W.get

noncomputable def listScaledTail (S : System α) (tag : α → β) (μ : Measure ℝ)
    (a : ℝ) (W : List α) : Measure ℝ := (listTail S tag μ W).map (fun x => a*x)

noncomputable def suffixLaw (S : System α) (tag : α → β) (μ : Measure ℝ) (W : List α) (j : ℕ) : Measure ℝ :=
  listScaledTail S tag μ (S.wordAffine (W.take j)).1 (W.drop j)

noncomputable def suffixWindow (S : System α) (tag : α → β) (μ : Measure ℝ)
    (s : ℝ) (N : ℕ) (W : List α) (j : ℕ) : ℝ :=
  window (suffixLaw S tag μ W j) s (N*s)

end EntropyRateDimension.Typed

namespace EntropyRateDimension.System
open scoped BigOperators
variable {α : Type uα} [Fintype α]

noncomputable def listDepth (S : System α) (W : List α) : ℝ := (W.map S.letterDepth).sum

end EntropyRateDimension.System

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.WordAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uα

namespace EntropyRateDimension.System
open scoped BigOperators
variable {α : Type uα} [Fintype α]

noncomputable def wordAverage (S : System α) (n : ℕ) (f : List α → ℝ) : ℝ :=
  ∑ w : Fin n → α, S.wordWeight w*f (List.ofFn w)

end EntropyRateDimension.System

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.BlockWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uα uβ uγ

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

noncomputable def blocks (S : System ι) {b : ℕ} (hb : 0 < b) : System (Fin b → ι) where
  ratio w := (S.completeMap w).1
  offset w := (S.completeMap w).2
  weight w := S.wordWeight w
  ratio_pos w := abs_pos.mpr (S.completeMap_slope_ne_zero w)
  ratio_lt_one w := S.completeMap_abs_lt_one hb w
  weight_pos w := S.wordWeight_pos w
  weight_sum := S.wordWeight_sum b

def flattenWordEquiv (n b : ℕ) : (Fin n → Fin b → ι) ≃ (Fin (n*b) → ι) :=
  (Equiv.curry (Fin n) (Fin b) ι).symm.trans (Equiv.piCongrLeft (fun _ => ι) finProdFinEquiv)

omit [Fintype ι] in
@[simp] theorem flattenWordEquiv_apply (n b : ℕ) (w : Fin n → Fin b → ι)
    (i : Fin n) (j : Fin b) : flattenWordEquiv n b w (finProdFinEquiv (i,j))=w i j := by
  simp [flattenWordEquiv]

noncomputable def wordType {b : ℕ} (w : Fin b → ι) : ι → Fin (b+1) := by
  classical
  exact fun i => ⟨(Finset.univ.filter (fun j => w j=i)).card,
    Nat.lt_succ_of_le ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Fintype.card_fin b))⟩

end EntropyRateDimension.System

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.EntropyBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open FiniteEntropy FairPairs FiniteCondition MeasureEntropy MeasureTheory
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [Fintype β] [DecidableEq β]

noncomputable def entropyLoss (S : System α) (tag : α → β) {n : ℕ}
    (w : Fin n → α) (ρ : ℝ) : ℝ :=
  ((law S tag w).shannonEntropy-(law S tag w).gridEntropy ρ)*Real.log 2

end EntropyRateDimension.Typed

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.RetainedLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open FairPairs MeasureTheory MeasureEntropy
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]

noncomputable def fineScale (A : ℝ) (n : ℕ) : ℝ := (2 : ℝ)^(-⌈A*n⌉)
noncomputable def bandStart (A : ℝ) (n : ℕ) : ℤ := ⌈A*n⌉-1

noncomputable def retainedLoss (S : System α) (tag : α → β) (A A' : ℝ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → α, if S.wordDepth w ≤ A'*n then
    S.wordWeight w*entropyLoss S tag w (fineScale A n) else 0

end EntropyRateDimension.Typed

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.PairBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uβ

namespace EntropyRateDimension
open scoped BigOperators Topology
open Filter

namespace Typed
open FairPairs
variable {α : Type uα} {β : Type uβ} [Fintype α] [Nonempty α] [DecidableEq β]

noncomputable def pairBudget (S : System α) (tag : α → β) (A' : ℝ)
    (a B : ℤ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → α, if S.wordDepth w ≤ A'*n then S.wordWeight w*
    ∑ ℓ ∈ Finset.Icc a B, capacity (law S tag w) ℓ else 0

end Typed
end EntropyRateDimension

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.WindowCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EntropyRateDimension.Windows
open scoped BigOperators

abbrev Retained (σ : ℕ → ℝ) (A' : ℝ) (n : ℕ) (a B L : ℤ) (j : ℕ) : Prop :=
  σ (j+n)-σ j ≤ A'*n ∧ a ≤ L-⌈σ j⌉ ∧ L-⌈σ j⌉ ≤ B

end EntropyRateDimension.Windows

end OAI
end

section
-- module Solutions.OAIQW_EntropyRateDimension.WindowGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs Windows
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

noncomputable def retainedCapacity (S : System α) (tag : α → β)
    (A' : ℝ) (n : ℕ) (a B L : ℤ) (W : List α) (j : ℕ) : ℝ :=
  if Retained (fun j => S.listDepth (W.take j)) A' n a B L j then
    capacity (listLaw S tag ((W.drop j).take n)) (L-⌈S.listDepth (W.take j)⌉) else 0

noncomputable def retainedDrop (S : System α) (tag : α → β) (μ : Measure ℝ)
    (M : ℕ) (A' : ℝ) (n : ℕ) (a B L : ℤ) (W : List α) (j : ℕ) : ℝ :=
  if Retained (fun j => S.listDepth (W.take j)) A' n a B L j then
    suffixWindow S tag μ ((2 : ℝ)^(-L)/M) (M*M) W j-
      suffixWindow S tag μ ((2 : ℝ)^(-L)/M) (M*M) W (j+n) else 0

end EntropyRateDimension.Typed

end OAI
end


