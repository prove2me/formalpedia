-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy__SelfSimilarCorollaries
-- name    : OAI_MeasureTheory_SelfSimilar_MeasureEntropy__SelfSimilarCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:22:12.018654+00:00
-- url     : https://prove2.me/theorems/c56980f9-7aec-45ca-833f-d99375a055a4
-- title:
--   Grid entropies and their averages for measures on the line
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   1. **Observation entropy.** For a measure $\mu$ and an observable $f$, the masses $\mu\{f=b\}$ and their entropy $\sum_b-m(b)\log m(b)$. For an almost surely finite-valued observable this gives a finite distribution.
--   2. **Compact carriers.** $\mu$ is compactly carried if it vanishes outside some $[-B,B]$.
--   3. **Grids.** The label $\ell_{s,u}(x)=\lfloor x/s+u\rfloor$ of the grid of mesh $s$ shifted by $u$, the grid entropy $H_{s,u}(\mu)$, and its average over shifts
--   $$
--   \bar H_s(\mu)=\int_0^1H_{s,u}(\mu)\,du .
--   $$
--   4. **Relative labels.** The position of the $s$-cell inside the coarser $t$-cell.
--   5. **Fair shift and deficits.** $\frac12(\mu+\mu(\cdot-v))$; the grid deficit $H_{s,u}(\text{fair shift by }s)-H_{s,u}(\mu)$; and the scale deficit $\log2-(\bar H_s-\bar H_{2s})$, which measures how far the entropy is from growing by one bit when the scale halves.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SelfSimilarCorollaries mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Model
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution__SelfSimilarCorollaries

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

theorem mixture_probability {ι : Type uι} {α : Type uα} [Fintype ι] [MeasurableSpace α]
    (ν : ι → Measure α) [∀ i, IsProbabilityMeasure (ν i)] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) :
    IsProbabilityMeasure (∑ i, ENNReal.ofReal (w i) • ν i) := by
  constructor
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hw1, ENNReal.ofReal_one]

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


