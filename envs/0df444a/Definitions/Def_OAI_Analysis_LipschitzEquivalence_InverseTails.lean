-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
-- name    : OAI_Analysis_LipschitzEquivalence_InverseTails
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:22:06.035919+00:00
-- url     : https://prove2.me/theorems/6b6ac734-30bd-42d1-aa58-54fed87b2648
-- title:
--   Tail control, compactness and global inverses for slot maps
-- statement:
--   Tools for Hilbert sums $\mathcal H=\bigl(\bigoplus_nE_n\bigr)_{\ell^2}$ and for proving surjectivity of limits of maps.
--
--   1. **Heads and tails.** $\mathrm{head}_s(x)$ keeps the first $s$ slots; it converges to $x$, and $\|x-\mathrm{head}_sx\|^2=\|x\|^2-\sum_{i<s}\|x_i\|^2$. A sequence converging slotwise with uniformly small tails is Cauchy. If the $E_i$ are proper, a bounded sequence whose tails are dominated by those of a fixed $y\in\mathcal H$,
--   $$
--   \|F_k-\mathrm{head}_sF_k\|\le\|y-\mathrm{head}_sy\|\quad\text{for all }k,s,
--   $$
--   has a convergent subsequence.
--   2. **Inverse tails.** For the frozen isometry with unit vectors $\xi$, both components of the inverse image of $y$ have tails bounded by the tail of $y$. Hence for any sequence of unit-vector choices, the inverse images of a fixed $y$ have a convergent subsequence.
--   3. **Global inverse.** A covering map onto a preconnected space with one point having a unique preimage is bijective, and a proper local homeomorphism into a Hausdorff setting is a covering map.
--   4. **Limits of moving maps.** If the maps $x\mapsto\mathrm{frozen}_{w_k(x)}(x)$ are surjective, uniformly $K$-Lipschitz and converge pointwise to $f$, then $f$ is surjective.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/InverseTails.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/InverseTails.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LipschitzEquivalence mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition

namespace OAI

universe uE uG uX uY uF

noncomputable section
namespace LipschitzCounterexample

namespace HilbertSlots
open scoped ENNReal
open Filter Topology
variable {E : ℕ → Type uE} [∀ i, NormedAddCommGroup (E i)]

def cutHead (s : ℕ) (x : HilbertSum E) : HilbertSum E :=
  ∑ i ∈ Finset.range s, lp.single 2 i (x i)

theorem prefix_tendsto (x : HilbertSum E) : Tendsto (fun s => cutHead s x) atTop (𝓝 x) :=
  (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x).tendsto_sum_nat

theorem norm_sub_prefix_sq (x : HilbertSum E) (s : ℕ) :
    ‖x - cutHead s x‖^2 = ‖x‖^2 - ∑ i ∈ Finset.range s, ‖x i‖^2 := by
  simpa [cutHead] using lp.norm_compl_sum_single (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    x (Finset.range s)

theorem cauchy_of_small_tails (F : ℕ → HilbertSum E) (z : ∀ i, E i)
    (hz : ∀ i, Tendsto (fun k => F k i) atTop (𝓝 (z i)))
    (ht : ∀ ε > 0, ∃ s, ∀ k, ‖F k - cutHead s (F k)‖ < ε) : CauchySeq F := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨s, hs⟩ := ht (ε/3) (by positivity)
  have hp : Tendsto (fun k => cutHead s (F k)) atTop
      (𝓝 (∑ i ∈ Finset.range s, lp.single 2 i (z i))) := by
    apply tendsto_finsetSum
    intro i hi
    exact (lp.isometry_single (p := (2 : ℝ≥0∞)) i).continuous.continuousAt.tendsto.comp (hz i)
  have hc := hp.cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hc (ε/3) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hb := dist_triangle4 (F m) (cutHead s (F m)) (cutHead s (F n)) (F n)
  rw [dist_comm (cutHead s (F n)) (F n)] at hb
  simp only [dist_eq_norm] at hb hN
  have ha := hs m
  have hd := hs n
  have he := hN m hm n hn
  rw [dist_eq_norm]
  linarith

theorem subsequence_of_tail_domination [∀ i, ProperSpace (E i)]
    (F : ℕ → HilbertSum E) {G : ℕ → Type uG} [∀ i, NormedAddCommGroup (G i)]
    (y : HilbertSum G) (C : ℝ) (hb : ∀ k, ‖F k‖ ≤ C)
    (ht : ∀ k s, ‖F k - cutHead s (F k)‖ ≤ ‖y - cutHead s y‖) :
    ∃ x : HilbertSum E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (F ∘ φ) atTop (𝓝 x) := by
  have hK : IsCompact {z : ∀ i, E i | ∀ i, z i ∈ Metric.closedBall 0 C} :=
    isCompact_pi_infinite (fun i => isCompact_closedBall (0 : E i) C)
  obtain ⟨z, hzK, φ, hφ, hz⟩ := hK.tendsto_subseq (x := fun k i => F k i) (by
    intro k i
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (F k) i).trans (hb k))
  have hc : CauchySeq (F ∘ φ) := by
    apply cauchy_of_small_tails (F ∘ φ) z
    · intro i
      exact (tendsto_pi_nhds.1 hz) i
    · intro ε hε
      have hy : Tendsto (fun s => y - cutHead s y) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := y)).sub (prefix_tendsto y)
      obtain ⟨s, hs⟩ := Filter.Eventually.exists
        ((NormedAddGroup.tendsto_nhds_zero.1 hy) ε hε)
      exact ⟨s, fun k => (ht (φ k) s).trans_lt hs⟩
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨x, φ, hφ, hx⟩

end HilbertSlots

namespace HilbertSlots
open scoped ENNReal InnerProductSpace
open Filter Topology
variable {E : ℕ → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  (ξ : ∀ i, E i) (hξ : ∀ i, ‖ξ i‖ = 1)

theorem inverse_tail_norm_sq (y : HilbertSum E) (s : ℕ) :
    ‖(frozenInv ξ hξ y).fst - cutHead s (frozenInv ξ hξ y).fst‖^2 +
      ‖(frozenInv ξ hξ y).snd - cutHead s (frozenInv ξ hξ y).snd‖^2 ≤
        ‖y - cutHead s y‖^2 := by
  simp only [norm_sub_prefix_sq]
  have hp := inverse_prefix_energy ξ hξ y s
  rw [Finset.sum_add_distrib] at hp
  have hn := WithLp.prod_norm_sq_eq_of_L2 (frozenInv ξ hξ y)
  rw [norm_frozenInv] at hn
  linarith

theorem inverse_fst_tail (y : HilbertSum E) (s : ℕ) :
    ‖(frozenInv ξ hξ y).fst - cutHead s (frozenInv ξ hξ y).fst‖ ≤
      ‖y - cutHead s y‖ := by
  have h := inverse_tail_norm_sq ξ hξ y s
  nlinarith [sq_nonneg ‖(frozenInv ξ hξ y).snd - cutHead s (frozenInv ξ hξ y).snd‖,
    norm_nonneg (y - cutHead s y),
    norm_nonneg ((frozenInv ξ hξ y).fst - cutHead s (frozenInv ξ hξ y).fst)]

theorem inverse_snd_tail (y : HilbertSum E) (s : ℕ) :
    ‖(frozenInv ξ hξ y).snd - cutHead s (frozenInv ξ hξ y).snd‖ ≤
      ‖y - cutHead s y‖ := by
  have h := inverse_tail_norm_sq ξ hξ y s
  nlinarith [sq_nonneg ‖(frozenInv ξ hξ y).fst - cutHead s (frozenInv ξ hξ y).fst‖,
    norm_nonneg (y - cutHead s y),
    norm_nonneg ((frozenInv ξ hξ y).snd - cutHead s (frozenInv ξ hξ y).snd)]

omit ξ hξ in

theorem inverse_subsequence [∀ i, ProperSpace (E i)]
    (w : ℕ → ∀ i, E i) (hw : ∀ k i, ‖w k i‖ = 1) (y : HilbertSum E) :
    ∃ x : WithLp 2 (HilbertSum E × RealL2), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => frozenInv (w (φ k)) (hw (φ k)) y) atTop (𝓝 x) := by
  obtain ⟨u, φ, hφ, hu⟩ := subsequence_of_tail_domination
    (fun k => (frozenInv (w k) (hw k) y).fst) y ‖y‖ (fun k => by
      have h := WithLp.norm_fst_le (p := (2 : ℝ≥0∞)) (HilbertSum E) (frozenInv (w k) (hw k) y)
      simpa only [norm_frozenInv] using h)
    (fun k s => inverse_fst_tail (w k) (hw k) y s)
  obtain ⟨v, ψ, hψ, hv⟩ := subsequence_of_tail_domination
    (fun k => (frozenInv (w (φ k)) (hw (φ k)) y).snd) y ‖y‖ (fun k => by
      have h := WithLp.norm_snd_le (p := (2 : ℝ≥0∞)) (HilbertSum E)
        (frozenInv (w (φ k)) (hw (φ k)) y)
      simpa only [norm_frozenInv] using h)
    (fun k s => inverse_snd_tail (w (φ k)) (hw (φ k)) y s)
  refine ⟨WithLp.toLp 2 (u, v), φ ∘ ψ, hφ.comp hψ, ?_⟩
  have ht := (hu.comp hψ.tendsto_atTop).prodMk_nhds hv
  exact ((WithLp.prodContinuousLinearEquiv 2 ℝ (HilbertSum E) RealL2).symm.continuous.tendsto
    (u,v)).comp ht

end HilbertSlots

namespace GlobalInverse
variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]

def uniqueFiber (f : X → Y) (y : Y) : Prop :=
  Nonempty (f ⁻¹' {y}) ∧ Subsingleton (f ⁻¹' {y})

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem uniqueFiber_iff (f : X → Y) (y : Y) : uniqueFiber f y ↔ ∃! x, f x = y := by
  constructor
  · rintro ⟨⟨x⟩, hs⟩
    refine ⟨x, x.2, fun a ha => ?_⟩
    exact congrArg Subtype.val (hs.elim ⟨a, ha⟩ x)
  · rintro ⟨x, hx, hu⟩
    exact ⟨⟨⟨x, hx⟩⟩, ⟨fun a b => Subtype.ext ((hu a a.2).trans (hu b b.2).symm)⟩⟩

theorem covering_bijective [PreconnectedSpace Y] (f : X → Y) (hf : IsCoveringMap f)
    (y₀ : Y) (h₀ : ∃! x, f x = y₀) : Function.Bijective f := by
  have hl : ∀ y, ∃ U, y ∈ U ∧ IsOpen U ∧ ∀ z ∈ U,
      uniqueFiber f y ↔ uniqueFiber f z := by
    intro y
    obtain ⟨hd, U, hy, hU, hpre, H, hH⟩ := hf y
    refine ⟨U, hy, hU, fun z hz => ?_⟩
    have he : IsEvenlyCovered f z (f ⁻¹' {y}) := ⟨hd, U, hz, hU, hpre, H, hH⟩
    exact and_congr he.fiberHomeomorph.toEquiv.nonempty_congr
      he.fiberHomeomorph.toEquiv.subsingleton_congr
  have ho : IsOpen {y | uniqueFiber f y} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨U, hyU, hU, he⟩ := hl y
    exact Filter.mem_of_superset (hU.mem_nhds hyU) (fun z hz => (he z hz).1 hy)
  have hcomp : IsOpen {y | ¬ uniqueFiber f y} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨U, hyU, hU, he⟩ := hl y
    exact Filter.mem_of_superset (hU.mem_nhds hyU) (fun z hz h => hy ((he z hz).2 h))
  have hc : IsClosed {y | uniqueFiber f y} := by simpa only [Set.compl_ofPred, not_not] using hcomp.isClosed_compl
  have hu : {y | uniqueFiber f y} = Set.univ :=
    (show IsClopen {y | uniqueFiber f y} from ⟨hc, ho⟩).eq_univ
      ⟨y₀, (uniqueFiber_iff f y₀).2 h₀⟩
  have he : ∀ y, ∃! x, f x = y := by
    intro y
    apply (uniqueFiber_iff f y).1
    change y ∈ {y | uniqueFiber f y}
    rw [hu]
    trivial
  constructor
  · intro x x' h
    obtain ⟨z, hz, huniq⟩ := he (f x)
    exact (huniq x rfl).trans (huniq x' h.symm).symm
  · intro y; obtain ⟨x, hx, _⟩ := he y; exact ⟨x, hx⟩

theorem proper_covering [T2Space X] (f : X → Y) (hp : IsProperMap f)
    (hl : IsLocalHomeomorph f) : IsCoveringMap f := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  apply hp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
  · intro y hy
    apply (hp.isCompact_preimage isCompact_singleton).finite
    apply IsDiscrete.of_openPartialHomeomorph f (Set.Subset.refl _)
    intro x hx
    obtain ⟨e, hx, he⟩ := hl x
    exact ⟨e, hx, he.symm⟩
  · exact hl.isLocalHomeomorphOn

end GlobalInverse

namespace GlobalInverse
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedAddCommGroup F]

end GlobalInverse

namespace HilbertSlots
open scoped ENNReal NNReal
open Filter Topology
variable {E : ℕ → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]

theorem moving_limit_surjective [∀ i, ProperSpace (E i)]
    (w : ℕ → WithLp 2 (HilbertSum E × RealL2) → ∀ i, E i)
    (hw : ∀ k x i, ‖w k x i‖ = 1)
    (f : WithLp 2 (HilbertSum E × RealL2) → HilbertSum E) (K : ℝ≥0)
    (hs : ∀ k, Function.Surjective (moving (w k) (hw k)))
    (hL : ∀ k, LipschitzWith K (moving (w k) (hw k)))
    (hf : ∀ x, Tendsto (fun k => moving (w k) (hw k) x) atTop (𝓝 (f x))) :
    Function.Surjective f := by
  intro y
  choose a ha using fun k => hs k y
  have he : ∀ k, a k = frozenInv (w k (a k)) (hw k (a k)) y := by
    intro k
    apply (frozen (w k (a k)) (hw k (a k))).injective
    exact (ha k).trans (frozen_right_inv (w k (a k)) (hw k (a k)) y).symm
  obtain ⟨x, φ, hφ, hx⟩ := inverse_subsequence (fun k => w k (a k))
    (fun k => hw k (a k)) y
  have hx' : Tendsto (a ∘ φ) atTop (𝓝 x) := by
    apply hx.congr
    intro k
    exact (he (φ k)).symm
  have hd : Tendsto (fun k => dist (moving (w (φ k)) (hw (φ k)) x) y)
      atTop (𝓝 0) := by
    have hbound : ∀ k, dist (moving (w (φ k)) (hw (φ k)) x) y ≤
        (K : ℝ) * dist x (a (φ k)) := by
      intro k
      rw [← ha (φ k)]
      exact (hL (φ k)).dist_le_mul x (a (φ k))
    apply squeeze_zero (fun k => dist_nonneg) hbound
    have ht := (tendsto_const_nhds (x := x)).dist hx'
    simpa using ht.const_mul (K : ℝ)
  have ht := ((hf x).comp hφ.tendsto_atTop).congr_dist hd
  exact ⟨x, tendsto_nhds_unique ht tendsto_const_nhds⟩

end HilbertSlots

end LipschitzCounterexample
end

end OAI


