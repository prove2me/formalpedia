-- Prove2me | Definitions.Def_Q220Uk007
-- name    : Q220Uk007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T14:48:28.178854+00:00
-- url     : https://prove2.me/theorems/9af8c0b6-ca72-464f-b2f3-b3a2a022b3a6
-- title:
--   Definitions bundle Q220Uk007 of the split of OpenAI, Uniform computation of the squared-logarithmic k-server bound
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniformKServer.uniform_squared_logarithmic_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform computation of the squared-logarithmic k-server bound*, OpenAI Math Release, September 24, 2026, result family 110, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 317 declarations of OpenAI's Lean: 83 definitions, 1 inductive type or structure and 233 theorems. The definitions and types are `OAI.UniformKServer.EpochShadow.shadowTrace`, `OAI.UniformKServer.EpochSide.param`, `OAI.UniformKServer.EpochTape.fullTrace`, `OAI.UniformKServer.HiddenHistory.data`, `OAI.UniformKServer.HiddenHistory.location`, `OAI.UniformKServer.HiddenHistory.next`, `OAI.UniformKServer.HiddenHistory.trace`, `OAI.UniformKServer.KeySizePosterior.input`, `OAI.UniformKServer.KeySizeTracker.pot`, `OAI.UniformKServer.OfflineLaw.configEqFL`, `OAI.UniformKServer.OfflineLaw.configEqHP`, `OAI.UniformKServer.OfflineLaw.data`, `OAI.UniformKServer.OfflineLaw.history`, `OAI.UniformKServer.PartitionLevel.Input.cutoff`, `OAI.UniformKServer.PartitionTree.Label`, `OAI.UniformKServer.PartitionTree.LevelTape`, `OAI.UniformKServer.PartitionTree.Tape`, `OAI.UniformKServer.PartitionTree.actualAllocation`, `OAI.UniformKServer.PartitionTree.allocationEndpoint`, `OAI.UniformKServer.PartitionTree.anchor`, `OAI.UniformKServer.PartitionTree.anchorEndpoint`, `OAI.UniformKServer.PartitionTree.componentFlow`, `OAI.UniformKServer.PartitionTree.flowEndpoint`, `OAI.UniformKServer.PartitionTree.lastLabel`, `OAI.UniformKServer.PartitionTree.levelLaw`, `OAI.UniformKServer.PartitionTree.map`, `OAI.UniformKServer.PartitionTree.publicInput`, `OAI.UniformKServer.PartitionTree.region`, `OAI.UniformKServer.PartitionTree.roundingChain`, `OAI.UniformKServer.PartitionTree.shape`, `OAI.UniformKServer.PartitionTree.size`, `OAI.UniformKServer.PartitionTree.sizeEndpoint`, `OAI.UniformKServer.PartitionTree.staticLevel`, `OAI.UniformKServer.PartitionTree.tapeLaw`, `OAI.UniformKServer.PartitionTree.weight`, `OAI.UniformKServer.PartitionTree.word`, `OAI.UniformKServer.SideFiniteInput.Data`, `OAI.UniformKServer.SideFiniteInput.input`, `OAI.UniformKServer.SideFiniteInput.post`, `OAI.UniformKServer.SideFiniteInput.prepared` and 44 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `UniformKServer_ActualAnchorTravel`, `UniformKServer_ActualEditFinance`, `UniformKServer_ActualPartitions`, `UniformKServer_ActualPilot`, `UniformKServer_ActualPublicFlow`, `UniformKServer_ActualRoundingChain`, `UniformKServer_ActualSizeBudget`, `UniformKServer_AnchorFinance`, `UniformKServer_CommonAnchorTravel`, `UniformKServer_CooldownLabels`, `UniformKServer_DyadicTiers`, `UniformKServer_EpochOutputParameters`, `UniformKServer_EpochShadow`, `UniformKServer_EpochSide`, `UniformKServer_EpochSideBudget`, `UniformKServer_EpochSideCharge`, `UniformKServer_EpochTape`, `UniformKServer_FineVariation`, `UniformKServer_FiniteLawFinance`, `UniformKServer_FiniteLawTheorem`, `UniformKServer_FlowAuxiliary`, `UniformKServer_HeavyAnchorGeometry`, `UniformKServer_HeavyRadius`, `UniformKServer_HeavySeparation`, `UniformKServer_HeavyTape`, `UniformKServer_HiddenFlow`, `UniformKServer_HiddenHistory`, `UniformKServer_HorizonPolicy`, `UniformKServer_KeySizePosterior`, `UniformKServer_KeySizeTracker`, `UniformKServer_LevelAnchorContinuity`, `UniformKServer_LevelAnchorRelease`, `UniformKServer_LevelMap`, `UniformKServer_LevelSeparation`, `UniformKServer_LiteralBound`, `UniformKServer_LiteralVector`, `UniformKServer_OfflineLaw`, `UniformKServer_PartitionAnchors`, `UniformKServer_PartitionGeometry`, `UniformKServer_PartitionLaw`, `UniformKServer_PartitionLevel`, `UniformKServer_PartitionMovement`, `UniformKServer_PartitionScales`, `UniformKServer_PartitionSeparation`, `UniformKServer_PartitionTransport`, `UniformKServer_PartitionTree`, `UniformKServer_PilotCapacity`, `UniformKServer_PilotCredits`, `UniformKServer_PilotDrift`, `UniformKServer_PilotEdits`, `UniformKServer_PilotExtension`, `UniformKServer_PilotFamily`, `UniformKServer_PilotPersistence`, `UniformKServer_PilotRelocation`, `UniformKServer_PilotSlope`, `UniformKServer_PilotStability`, `UniformKServer_PublicFlow`, `UniformKServer_PublicRounding`, `UniformKServer_RankFunctions`, `UniformKServer_RoundedMetricStep`, `UniformKServer_RoundingChain`, `UniformKServer_RoundingKernel`, `UniformKServer_SideFiniteInput`, `UniformKServer_SideParameterChanges`, `UniformKServer_SideRecurrence`, `UniformKServer_StarAllocator`, `UniformKServer_StarCaps`, `UniformKServer_StarFeasibilityParameters`, `UniformKServer_StarLower`, `UniformKServer_StarOutputData`, `UniformKServer_StarOutputFeasibility`, `UniformKServer_StarParameters`, `UniformKServer_StarRanks`, `UniformKServer_StarSchedules`, `UniformKServer_StarTrackers`, `UniformKServer_SwitchFinite`, `UniformKServer_TierLabeledKeys`, `UniformKServer_TierLabels`, `UniformKServer_TierSchedule`, `UniformKServer_TreeAllocator`, `UniformKServer_TreeCoverage`, `UniformKServer_TreeDistribution`, `UniformKServer_TreePosteriorRegions`, `UniformKServer_TreeRounding`.
--
--   **Imports.** It imports the published bundle `Def_UniformKServer`; the bundles `Q220Uk004`, `Q220Uk005` and `Q220Uk006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q220Uk009` and `Q220Uk010`.
-- source:
--   OpenAI, Uniform computation of the squared-logarithmic k-server bound, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 110; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_UniformKServer
import Definitions.Def_Q220Uk004
import Definitions.Def_Q220Uk005
import Definitions.Def_Q220Uk006

section
-- module Solutions.Q220_UK.UniformKServer_TreeRounding
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace UniformKServer.TreeRounding
open UniformKServer.BalancedStar
noncomputable section

/-- Make the kernel valid even at probability-zero states. -/
theorem star_kernel {Ω ι : Type} [Fintype Ω] [Fintype ι]
    (I : BalancedStar.Input Ω ι) :
    ∃ (g : Ω × Finset ι → ℝ) (y : Ω × Finset ι → ι → ℤ),
      (∀ z, 0 ≤ g z) ∧ (∀ ω, ∑ A, g (ω,A) = I.μ ω) ∧
      (∀ z i, Balanced (I.b i) (y z i)) ∧
      (∀ z, ∑ i, y z i = I.N z.1) ∧
      (∀ i, ∑ z, g z * (y z i : ℝ) = I.b i) ∧
      (∑ z, g z * ∑ i, |(y z i : ℝ) - (I.X z.1 i : ℝ)|) ≤
        32*BalancedStar.T I + 11*BalancedStar.imbalance I := by
  classical
  obtain ⟨hv,g,hg,hrow,hvalid,hmean,hcost⟩ := BalancedStar.rounding_star I
  choose fallback hfb using hv
  let y := fun z : Ω × Finset ι => if 0 < g z then realized I.b z.2 else
    realized I.b (fallback z.1)
  have he (z : Ω × Finset ι) (i : ι) :
      g z * (y z i : ℝ) = g z * (realized I.b z.2 i : ℝ) := by
    dsimp only [y]
    split_ifs with hp
    · rfl
    · have hz : g z = 0 := le_antisymm (le_of_not_gt hp) (hg z)
      simp [hz]
  refine ⟨g,y,hg,hrow,?_,?_,?_,?_⟩
  · intro z i
    dsimp only [y]
    split_ifs with hp
    · exact (hvalid z hp).1 i
    · exact (hfb z.1).1 i
  · intro z
    dsimp only [y]
    split_ifs with hp
    · exact (hvalid z hp).2
    · exact (hfb z.1).2
  · intro i
    simpa only [he] using hmean i
  · calc
      _ = BalancedStar.jointCost I g := by
        apply Finset.sum_congr rfl
        intro z _
        dsimp only [y]
        split_ifs with hp
        · rfl
        · have hz : g z = 0 := le_antisymm (le_of_not_gt hp) (hg z)
          simp [hz]
      _ ≤ _ := hcost

/-- An extension of an already generated joint state preserves every old
observable and permits completely correlated prescribed parent totals. -/
theorem extended_star (L : Law) {ι : Type} [Fintype ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (X : L.State → ι → ℤ) (N : L.State → ℤ)
    (hX : ∀ s i, Balanced (a i) (X s i))
    (hN : ∀ s, Balanced (∑ i, b i) (N s))
    (hXm : ∀ i, mean L (fun s => (X s i : ℝ)) = a i)
    (hNm : mean L (fun s => (N s : ℝ)) = ∑ i, b i) :
    ∃ (L' : Law) (π : L'.State → L.State) (Y : L'.State → ι → ℤ),
      (∀ f : L.State → ℝ, mean L' (f ∘ π) = mean L f) ∧
      (∀ s i, Balanced (b i) (Y s i)) ∧
      (∀ s, ∑ i, Y s i = N (π s)) ∧
      (∀ i, mean L' (fun s => (Y s i : ℝ)) = b i) ∧
      mean L' (fun s => ∑ i, |(Y s i : ℝ) - (X (π s) i : ℝ)|) ≤
        32*(∑ i, |a i-b i|) + 11*mean L (fun s => |(N s : ℝ)-∑ i,(X s i : ℝ)|) := by
  classical
  let I : BalancedStar.Input L.State ι :=
    ⟨L.mass,L.nonneg,L.total,a,b,ha,hb,X,N,hX,hN,hXm,hNm⟩
  obtain ⟨g,y,hg,hrow,hy,hsum,hm,hcost⟩ := star_kernel I
  let L' : Law := ⟨L.State × Finset ι, inferInstance, g, hg, by
    rw [Fintype.sum_prod_type]
    simp only [hrow]
    exact L.total⟩
  refine ⟨L',Prod.fst,y,?_,hy,hsum,hm,hcost⟩
  intro f
  dsimp only [mean,L',Function.comp_def]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.sum_mul,hrow]
  rfl


theorem good_step {n k : ℕ} (S : Shape n) (a b : Allocation S k)
    (L : Law) (X : L.State → Vertex n → ℤ)
    (hX : ∀ s, Rounded a (X s))
    (hm : ∀ v, mean L (fun s => (X s v : ℝ)) = a.amount v)
    (v : Vertex n) (E : Extension L n) (hE : Good a b L X v.val E) :
    ∃ E' : Extension L n, Good a b L X (v.val+1) E' := by
  classical
  have hpos (q : Allocation S k) (i : Local S v) : 0 ≤ localReal S q.amount v i := by
    cases i with
    | inl i => exact q.nonneg i.val
    | inr _ => exact q.park_nonneg v
  have hxb (s : E.law.State) (i : Local S v) :
      Balanced (localReal S a.amount v i) (localInt S (X (E.original s)) v i) := by
    cases i with
    | inl i => exact (hX (E.original s)).2.1 i.val
    | inr _ => exact (hX (E.original s)).2.2 v
  obtain ⟨L',π,Y,hpres,hy,hsum,hym,hcost⟩ := extended_star E.law
    (localReal S a.amount v) (localReal S b.amount v) (hpos a) (hpos b)
    (fun s => localInt S (X (E.original s)) v) (fun s => E.value s v)
    hxb (by simpa only [sum_localReal] using hE.balanced v (assigned_current S v))
    (old_local_mean S a L X hm E v)
    (by simpa only [sum_localReal] using hE.mean v (assigned_current S v))
  let E' : Extension L n := {
    law := L'
    original := E.original ∘ π
    preserves := by
      intro f
      change mean L' ((f ∘ E.original) ∘ π) = mean L f
      rw [hpres,E.preserves]
    value := fun z => assignChildren S v (E.value (π z)) (Y z) }
  have hnew (z : L'.State) (i : Local S v) : localInt S (E'.value z) v i = Y z i :=
    assign_local S v (E.value (π z)) (Y z) (hsum z) i
  have hval (u : Vertex n) (hu : assigned S v.val u) (z : L'.State) :
      E'.value z u = E.value (π z) u := by
    apply assign_unchanged
    rcases hu with hu | hu
    · exact Or.inl hu
    · right
      intro he
      rw [he] at hu
      exact lt_irrefl _ hu
  have hprev (j : Vertex n) (hj : j.val < v.val) (z : L'.State) (i : Local S j) :
      localInt S (E'.value z) j i = localInt S (E.value (π z)) j i :=
    assign_old_local S v _ _ j hj i
  have hnode (j : Vertex n) (hj : assigned S v.val j) :
      nodeMovement L X E' j = nodeMovement L X E j := by
    dsimp only [nodeMovement]
    simp only [hval j hj]
    exact hpres (fun z => |(E.value z j : ℝ) - (X (E.original z) j : ℝ)|)
  have hloc (j : Vertex n) (hj : j.val < v.val) :
      localMovement S L X E' j = localMovement S L X E j := by
    dsimp only [localMovement]
    simp only [hprev j hj]
    exact hpres (fun z => ∑ i : Local S j,
      |(localInt S (E.value z) j i : ℝ) - (localInt S (X (E.original z)) j i : ℝ)|)
  have hcase (u : Vertex n) (hu : assigned S (v.val+1) u) :
      assigned S v.val u ∨ u ≠ 0 ∧ S.parent u = v := by
    by_cases hp : assigned S v.val u
    · exact Or.inl hp
    right
    have hz : u ≠ 0 := fun he => hp (Or.inl he)
    refine ⟨hz,Fin.ext ?_⟩
    have ht : (S.parent u).val < v.val+1 := hu.resolve_left hz
    have hn : ¬ (S.parent u).val < v.val := fun he => hp (Or.inr he)
    omega
  refine ⟨E',?_⟩
  constructor
  · intro z
    rw [hval 0 (Or.inl rfl)]
    exact hE.root (π z)
  · intro u hu z
    rcases hcase u hu with hp | hp
    · rw [hval u hp]
      exact hE.balanced u hp (π z)
    · change Balanced (b.amount u) (assignChildren S v _ _ u)
      rw [show assignChildren S v (E.value (π z)) (Y z) u = Y z (.inl ⟨u,hp⟩) from
        assign_child S v _ _ ⟨u,hp⟩]
      exact hy z (.inl ⟨u,hp⟩)
  · intro u hu
    rcases hcase u hu with hp | hp
    · simp only [hval u hp]
      rw [show (fun z => (E.value (π z) u : ℝ)) =
        (fun z => (E.value z u : ℝ)) ∘ π from rfl,hpres]
      exact hE.mean u hp
    · have hc (z : L'.State) : E'.value z u = Y z (.inl ⟨u,hp⟩) :=
        assign_child S v _ _ ⟨u,hp⟩
      simp only [hc]
      exact hym (.inl ⟨u,hp⟩)
  · intro j hj z
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · change Balanced _ (localInt S (E'.value z) j (.inr ()))
      rw [hprev j hj]
      exact hE.parks j hj (π z)
    · have he : j=v := Fin.ext hj
      subst j
      change Balanced _ (localInt S (E'.value z) v (.inr ()))
      rw [hnew]
      exact hy z (.inr ())
  · intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · rw [hloc j hj,hnode j (by
        by_cases hz : j=0
        · exact Or.inl hz
        · exact Or.inr (lt_trans (S.earlier j hz) hj))]
      exact hE.bound j hj
    · have he : j=v := Fin.ext hj
      subst j
      rw [hnode v (assigned_current S v)]
      have hi : mean E.law (fun s => |(E.value s v : ℝ) -
          ∑ i : Local S v, (localInt S (X (E.original s)) v i : ℝ)|) =
          nodeMovement L X E v := by
        apply mean_congr
        intro s
        rw [← Int.cast_sum,sum_localInt]
      rw [hi] at hcost
      change mean L' _ ≤ _
      simpa only [hnew,localVariation,E',Function.comp_def] using hcost

theorem good_all {n k : ℕ} (S : Shape n) (a b : Allocation S k)
    (L : Law) (X : L.State → Vertex n → ℤ)
    (hX : ∀ s, Rounded a (X s))
    (hm : ∀ v, mean L (fun s => (X s v : ℝ)) = a.amount v) :
    ∃ E : Extension L n, Good a b L X (n+1) E := by
  have hi (s : ℕ) (hs : s ≤ n+1) : ∃ E : Extension L n, Good a b L X s E := by
    induction s with
    | zero => exact good_zero S a b L X
    | succ s ih =>
      obtain ⟨E,hE⟩ := ih (by omega)
      exact good_step S a b L X hX hm ⟨s,by omega⟩ E hE
  exact hi (n+1) le_rfl


/-- Exact companion proposition rounding-global for one conditional finite
update. Geometric separation tau ≥22 is stated as 22*w_child ≤ w_parent,
which includes the exact source weights r_j. No local kernels are assumed. -/
theorem tree_rounding {n k : ℕ} (S : Shape n) (w : Vertex n → ℝ)
    (hw : ∀ v, 0 ≤ w v)
    (hsep : ∀ v, v ≠ 0 → 22*w v ≤ w (S.parent v))
    (a b : Allocation S k) (L : Law) (X : L.State → Vertex n → ℤ)
    (hX : ∀ s, Rounded a (X s))
    (hmean : ∀ v, mean L (fun s => (X s v : ℝ)) = a.amount v) :
    ∃ E : Extension L n,
      (∀ s, Rounded b (E.value s)) ∧
      (∀ v, mean E.law (fun s => (E.value s v : ℝ)) = b.amount v) ∧
      movement S w L X E ≤ 132 * variation w a b := by
  classical
  obtain ⟨E,hE⟩ := good_all S a b L X hX hmean
  have hall (v : Vertex n) : assigned S (n+1) v := Or.inr (S.parent v).isLt
  refine ⟨E,?_,?_,?_⟩
  · intro s
    exact ⟨hE.root s,fun v => hE.balanced v (hall v) s,
      fun v => hE.parks v v.isLt s⟩
  · exact fun v => hE.mean v (hall v)
  let f : Vertex n → ℝ := nodeMovement L X E
  let g : Vertex n → ℝ := fun v => |b.amount v-a.amount v|
  have hf (v : Vertex n) : 0 ≤ f v := mean_nonneg E.law fun _ => abs_nonneg _
  have hg (v : Vertex n) : 0 ≤ g v := abs_nonneg _
  have hf0 : f 0 = 0 := by
    dsimp only [f,nodeMovement]
    calc
      _ = mean E.law (fun _ => 0) := by
        apply mean_congr
        intro s
        rw [hE.root s,(hX (E.original s)).1]
        simp
      _ = 0 := mean_const _ _
  have hg0 : g 0 = 0 := by simp [g,a.root,b.root]
  have hlocal (v : Vertex n) : (∑ i : Children S v, f i.val) ≤
      32*(2*(∑ i : Children S v,g i.val)+g v)+11*f v := by
    calc
      _ ≤ localMovement S L X E v := childMovement_le S L X E v
      _ ≤ 32*localVariation a b v+11*f v := hE.bound v v.isLt
      _ ≤ _ := by
        have ht := localVariation_le S a b v
        dsimp only [g]
        linarith
  have hrec := Finset.sum_le_sum (s := Finset.univ)
    (fun v _ => mul_le_mul_of_nonneg_left (hlocal v) (hw v))
  have hleft : (∑ v, w v * ∑ i : Children S v, f i.val) = movement S w L X E :=
    weighted_children S w f
  have hright : (∑ v, w v * (32*(2*(∑ i : Children S v,g i.val)+g v)+11*f v)) =
      64*variation w a b+32*(∑ v,w v*g v)+11*(∑ v,w v*f v) := by
    calc
      _ = ∑ v, (64*(w v*(∑ i : Children S v,g i.val))+
          32*(w v*g v)+11*(w v*f v)) := by
            apply Finset.sum_congr rfl
            intro v _
            ring
      _ = 64*(∑ v,w v*(∑ i : Children S v,g i.val))+
          32*(∑ v,w v*g v)+11*(∑ v,w v*f v) := by
            rw [Finset.sum_add_distrib,Finset.sum_add_distrib,
              ← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum]
      _ = _ := by rw [weighted_children]; rfl
  rw [hleft,hright] at hrec
  have hfs : 22*(∑ v,w v*f v) ≤ movement S w L X E :=
    weight_separation S w f hsep hf hf0
  have hgs : 22*(∑ v,w v*g v) ≤ variation w a b :=
    weight_separation S w g hsep hg hg0
  have hgV : 0 ≤ variation w a b := by
    apply Finset.sum_nonneg
    intro v _
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hw _) (abs_nonneg _)
  linarith


/-- The independent BalancedRepair.initial rounding: no movement is charged for selecting it. -/
theorem tree_initialization {n k : ℕ} (S : Shape n) (a : Allocation S k) :
    ∃ (L : Law) (X : L.State → Vertex n → ℤ),
      (∀ s, Rounded a (X s)) ∧
      (∀ v, mean L (fun s => (X s v : ℝ)) = a.amount v) := by
  classical
  let x : Vertex n → ℤ := fun v => if v=0 then k else 0
  have hc (v : Vertex n) (i : Children S v) : x i.val = 0 := by
    simp [x,i.property.1]
  have hsum (v : Vertex n) : ∑ i : Children S v, (x i.val : ℝ) = 0 := by
    simp only [hc,Int.cast_zero,Finset.sum_const_zero]
  have hnonneg (v : Vertex n) : 0 ≤ (x v : ℝ) := by
    dsimp [x]
    split_ifs <;> positivity
  let b : Allocation S k := {
    amount := fun v => (x v : ℝ)
    nonneg := hnonneg
    park_nonneg := by intro v; simpa only [park,hsum,sub_zero] using hnonneg v
    root := by simp [x] }
  let L : Law := {
    State := Unit
    finite := inferInstance
    mass := fun _ => 1
    nonneg := by intro; norm_num
    total := by simp }
  let X : L.State → Vertex n → ℤ := fun _ => x
  have hr : ∀ s, Rounded b (X s) := by
    intro s
    refine ⟨by simp [X,x],?_,?_⟩
    · intro v
      left
      exact (Int.floor_intCast (x v)).symm
    · intro v
      left
      simp only [b,park,sub_zero,intPark,X,hc,Finset.sum_const_zero]
      simp
  have hm : ∀ v, mean L (fun s => (X s v : ℝ)) = b.amount v := by
    intro v
    exact mean_const L _
  obtain ⟨E,hE,hmE,_⟩ := tree_rounding S (fun _ => 0) (by simp) (by simp)
    b a L X hr hm
  exact ⟨E.law,E.value,hE,hmE⟩

end
end UniformKServer.TreeRounding

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RoundedMetricStep
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                        
section

/-! A causal one-step extension with a literal labeled metric configuration.
No independence between old parent and child counts is imposed. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset TreeAncestry
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X : Type*} [PseudoMetricSpace X]

theorem metric_step (w : Vertex n→ℝ) (hw : ∀ v,0≤w v)
    (hsep : ∀ v,v≠0 → 22*w v≤w (S.parent v))
    (a b : Allocation S k) (f g : Vertex n→X) (G : ℝ) (hG : 0≤G)
    (hgeo : ∀ u v,0<park S a.amount u → 0<park S b.amount v → u≠v →
      dist (f u) (g v)≤G*pathCost (S:=S) w u v)
    (L : Law) (x : L.State→Vertex n→ℤ)
    (hx : ∀ s,Rounded a (x s))
    (hm : ∀ v,mean L (fun s=>(x s v:ℝ))=a.amount v)
    (R : ∀ s,Realization (k:=k) (S:=S) (x s)) :
    ∃ E : Extension L n,
      (∀ s,Rounded b (E.value s)) ∧
      (∀ v,mean E.law (fun s=>(E.value s v:ℝ))=b.amount v) ∧
      ∃ T : ∀ s,Realization (k:=k) (S:=S) (E.value s),
        mean E.law (fun s=>∑ i,dist (f ((R (E.original s)).tuple i)) (g ((T s).tuple i)))≤
        G*132*variation w a b+∑ v,park S b.amount v*commonDistance a b f g v := by
  obtain ⟨E,he,hmE,hmove⟩ := tree_rounding S w hw hsep a b L x hx hm
  let U (s : E.law.State) := realize b (E.value s) (he s)
  have hp (s : E.law.State) := parked_matching a b w hw f g G hG hgeo
    (hx (E.original s)) (he s) (R (E.original s)) (U s)
  choose π hπ using hp
  let T (s : E.law.State) := (U s).permute (π s)
  refine ⟨E,he,hmE,T,?_⟩
  have heach (s : E.law.State) :
      (∑ i,dist (f ((R (E.original s)).tuple i)) (g ((T s).tuple i)))≤
      G*(∑ v : Vertex n,if v=0 then 0 else w (S.parent v)*|(E.value s v:ℝ)-x (E.original s) v|)+
      ∑ v,(intPark S (E.value s) v:ℝ)*commonDistance a b f g v := hπ s
  have h := mean_mono E.law heach
  have hfirst : mean E.law (fun s=>G*(∑ v : Vertex n,if v=0 then 0 else
      w (S.parent v)*|(E.value s v:ℝ)-x (E.original s) v|))=G*movement S w L x E := by
    rw [mean_mul,mean_sum]
    congr 1
    unfold movement
    apply sum_congr rfl
    intro v _
    by_cases hv : v=0
    · simp [hv,mean_const]
    · simp only [hv,ite_false, if_false,mean_mul]
  have hsecond : mean E.law (fun s=>∑ v,(intPark S (E.value s) v:ℝ)*commonDistance a b f g v)=
      ∑ v,park S b.amount v*commonDistance a b f g v := by
    rw [mean_sum]
    apply sum_congr rfl
    intro v _
    simp only [mul_comm _ (commonDistance a b f g v),mean_mul,mean_intPark E.law E.value hmE]
  rw [mean_add,hfirst,hsecond] at h
  have hg := mul_le_mul_of_nonneg_left hmove hG
  nlinarith only [h,hg]

end UniformKServer.TreeRounding

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeDistribution
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! Initial and next rounded configurations live in one fixed finite alphabet;
conditional extension states are eliminated by exact finite push-forward. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset
open scoped Classical
variable {n k : ℕ} {S : Shape n}

theorem distribution_initial (a : Allocation S k) : Nonempty (Distribution a) := by
  obtain ⟨L,x,hx,hm⟩ := tree_initialization S a
  let R (s : L.State) := realize a (x s) (hx s)
  let f (s : L.State) := stateOf a (x s) (hx s) (R s)
  refine ⟨⟨L.finiteLaw.map f,?_,?_⟩⟩
  · intro y hy
    obtain ⟨s,rfl,_⟩ := map_positive L.finiteLaw f y hy
    simpa only [f,stateOf_value] using hx s
  · intro v
    rw [FiniteProbability.Law.expect_map]
    change mean L (fun s=>((f s).value v:ℝ))=a.amount v
    simpa only [f,stateOf_value] using hm v

variable {X : Type} [PseudoMetricSpace X]

theorem distribution_step (w : Vertex n→ℝ) (hw : ∀ v,0≤w v)
    (hsep : ∀ v,v≠0 → 22*w v≤w (S.parent v))
    (a b : Allocation S k) (f g : Vertex n→X) (G : ℝ) (hG : 0≤G)
    (hgeo : ∀ u v,0<park S a.amount u → 0<park S b.amount v → u≠v →
      dist (f u) (g v)≤G*TreeAncestry.pathCost (S:=S) w u v)
    (P : Distribution a) :
    ∃ C : Coupling a b P, C.joint.expect (fun st=>stateDistance f g st.1 st.2)≤
      G*132*variation w a b+∑ v,park S b.amount v*commonDistance a b f g v := by
  let L := P.supportLaw
  let x : L.State→Vertex n→ℤ := fun s=>s.val.value
  have hx (s : L.State) : Rounded a (x s) := P.rounded s.val s.property
  have hm (v : Vertex n) : mean L (fun s=>(x s v:ℝ))=a.amount v :=
    (P.support_mean _).trans (P.mean v)
  let R (s : L.State) := s.val.realization
  obtain ⟨E,he,hme,T,hcost⟩ := metric_step w hw hsep a b f g G hG hgeo L x hx hm R
  let new (s : E.law.State) := stateOf b (E.value s) (he s) (T s)
  let Q : Distribution b := {
    law := E.law.finiteLaw.map new
    rounded := by
      intro y hy
      obtain ⟨s,rfl,_⟩ := map_positive E.law.finiteLaw new y hy
      simpa only [new,stateOf_value] using he s
    mean := by
      intro v
      rw [FiniteProbability.Law.expect_map]
      change mean E.law (fun s=>((new s).value v:ℝ))=b.amount v
      simpa only [new,stateOf_value] using hme v }
  let pair (s : E.law.State) : State S k × State S k := ((E.original s).val,new s)
  let C : Coupling a b P := {
    joint := E.law.finiteLaw.map pair
    first := by
      intro F
      rw [FiniteProbability.Law.expect_map]
      change mean E.law ((fun s : L.State=>F s.val) ∘ E.original)=P.law.expect F
      rw [E.preserves,P.support_mean]
    next := Q
    second := by
      intro F
      change (E.law.finiteLaw.map pair).expect (F ∘ Prod.snd)=
        (E.law.finiteLaw.map new).expect F
      simp only [FiniteProbability.Law.expect_map]
      rfl }
  refine ⟨C,?_⟩
  change (E.law.finiteLaw.map pair).expect _≤_
  rw [FiniteProbability.Law.expect_map]
  change mean E.law (fun s=>∑ i,dist (f ((R (E.original s)).tuple i))
    (g (((new s).realization.tuple) i)))≤_
  simpa only [new,stateOf_tuple] using hcost

end UniformKServer.TreeRounding

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RoundingChain
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Chosen joint repairs form one adapted Markov chain on a fixed finite state
space. The choices use the old distribution and current geometric data only. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X Ω : Type} [PseudoMetricSpace X]

def chosenStep (w : Vertex n→ℝ) (hw : ∀ v,0≤w v)
    (hsep : ∀ v,v≠0 → 22*w v≤w (S.parent v))
    (a b : Allocation S k) (f g : Vertex n→X) (G : ℝ) (hG : 0≤G)
    (hgeo : ∀ u v,0<park S a.amount u → 0<park S b.amount v → u≠v →
      dist (f u) (g v)≤G*TreeAncestry.pathCost (S:=S) w u v)
    (P : Distribution a) : Coupling a b P :=
  Classical.choose (distribution_step w hw hsep a b f g G hG hgeo P)

namespace ChainInput
variable (D : ChainInput S k X Ω)

def step (t : ℕ) (ω : Ω) (P : Distribution (D.allocation t ω)) :=
  chosenStep D.weight D.weight_nonneg D.weight_separated (D.allocation t ω)
    (D.allocation (t+1) ω) (D.anchors t ω) (D.anchors (t+1) ω)
    D.factor D.factor_nonneg (D.geometry t ω) P

def distribution : (t : ℕ)→(ω : Ω)→Distribution (D.allocation t ω)
  | 0,ω => Classical.choice (distribution_initial (D.allocation 0 ω))
  | t+1,ω => (D.step t ω (distribution t ω)).next

def joint (t : ℕ) (ω : Ω) := (D.step t ω (D.distribution t ω)).joint

end ChainInput
end UniformKServer.TreeRounding

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RankFunctions
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

                                                                      
                                                          
noncomputable section
namespace UniformKServer.RankFunctions

theorem coeff_at {β p : ℝ} (hβ : allowed β) (hp : pstar ≤ p) :
    2 ≤ A β+B β*h p ∧ A β+B β*h p ≤ 3 := by
  have hc := coeff_bounds hβ
  have hm := mul_le_mul_of_nonneg_left (h_bound hp) hc.2.1
  have h0 := mul_nonneg hc.2.1 (h_nonneg p)
  constructor <;> linarith [hc.1, hc.2.2.2.1]

theorem sqrt_middle_ordered {β p q : ℝ} (hβ : allowed β)
    (hp : pstar ≤ p) (hpq : p ≤ q) :
    |Real.sqrt (rank β p)-Real.sqrt (rank β q)| ≤ 4*(q-p) := by
  have hq : pstar ≤ q := hp.trans hpq
  have hc := coeff_bounds hβ
  have hCp := coeff_at hβ hp
  have hCq := coeff_at hβ hq
  have hx := h_nonneg p
  have hy := h_nonneg q
  have hxy := h_antitone hpq
  have hCxy : A β+B β*h q ≤ A β+B β*h p := by nlinarith [hc.2.1]
  have hSxy := Real.sqrt_le_sqrt hCxy
  have hSp₀ : 1 ≤ Real.sqrt (A β+B β*h p) := by
    apply (Real.le_sqrt (by norm_num) (by linarith [hCp.1])).mpr
    norm_num <;> linarith [hCp.1]
  have hSq₀ : 1 ≤ Real.sqrt (A β+B β*h q) := by
    apply (Real.le_sqrt (by norm_num) (by linarith [hCq.1])).mpr
    norm_num <;> linarith [hCq.1]
  have hSp : Real.sqrt (A β+B β*h p) ≤ 2 := by
    apply (Real.sqrt_le_left (by norm_num)).mpr
    norm_num <;> linarith [hCp.2]
  have hroot : Real.sqrt (A β+B β*h p)-Real.sqrt (A β+B β*h q) ≤ B β*(h p-h q) := by
    have hh := sqrt_diff_aux (by linarith [hCp.1] : 0 ≤ A β+B β*h p)
      (by linarith [hCq.1] : 0 ≤ A β+B β*h q) (by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hSxy), abs_of_nonneg (sub_nonneg.mpr hCxy)] at hh
    nlinarith only [hh]
  have hcost : h p*Real.sqrt (A β+B β*h p)-h q*Real.sqrt (A β+B β*h q) ≤
      (2+(7/12)*B β)*(h p-h q) := by
    have h1 := mul_le_mul_of_nonneg_left hSp (sub_nonneg.mpr hxy)
    have h2 := mul_le_mul_of_nonneg_left hroot hy
    have h3 := mul_le_mul_of_nonneg_right (h_bound hq) (mul_nonneg hc.2.1 (sub_nonneg.mpr hxy))
    nlinarith only [h1,h2,h3]
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt (rank_antitone hβ hpq))),
    rank_middle hp, rank_middle hq, sqrt_middle_eq, sqrt_middle_eq]
  calc
    _ ≤ (2+(7/12)*B β)*(h p-h q) := hcost
    _ ≤ 4*(h p-h q) := mul_le_mul_of_nonneg_right (by linarith [hc.2.2.1]) (sub_nonneg.mpr hxy)
    _ ≤ 4*(q-p) := by linarith [h_diff hpq]

theorem sqrt_rank_lipschitz {β : ℝ} (hβ : allowed β) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) :
    |Real.sqrt (rank β p)-Real.sqrt (rank β q)| ≤ 4*|p-q| := by
  wlog hpq : p ≤ q generalizing p q
  · simpa only [abs_sub_comm] using this hq hp (le_of_not_ge hpq)
  rw [abs_sub_comm p q, abs_of_nonneg (sub_nonneg.mpr hpq)]
  by_cases hq' : q ≤ pstar
  · have hh := sqrt_left hβ hp hq (hpq.trans hq') hq'
    simpa only [abs_sub_comm p q, abs_of_nonneg (sub_nonneg.mpr hpq)] using hh
  · by_cases hp' : pstar ≤ p
    · exact sqrt_middle_ordered hβ hp' hpq
    · have hpp : p ≤ pstar := le_of_lt (lt_of_not_ge hp')
      have hqq : pstar ≤ q := le_of_lt (lt_of_not_ge hq')
      have h1 := sqrt_left hβ hp (by norm_num [pstar]) hpp (le_refl pstar)
      have h2 := sqrt_middle_ordered hβ (le_refl pstar) hqq
      have htri := abs_sub_le (Real.sqrt (rank β p)) (Real.sqrt (rank β pstar)) (Real.sqrt (rank β q))
      rw [abs_sub_comm p pstar, abs_of_nonneg (sub_nonneg.mpr hpp)] at h1
      linarith

end UniformKServer.RankFunctions

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotExtension
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem drift_bounded [DecidableEq X] (r σ R : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (μ ν g : X → ℝ)
    (hν : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1) (x : X)
    (hg : ∀ y, g y ∈ Set.Icc (0:ℝ) 1) :
    max (value r σ R (fun y => μ y-ν y+if y=x then 1 else 0) g-value r σ R μ g) 0 ≤ 514*r := by
  obtain ⟨z, hz, hmin, _⟩ := minimum_exists r σ R μ g
  calc
    _ ≤ r*∑ y, ν y*max (integrand r σ R g z x-integrand r σ R g z y) 0 :=
      drift_nonneg_bound r σ R hr μ ν g z hν hν1 x hz hmin
    _ ≤ r*∑ y, ν y*514 := by
      apply mul_le_mul_of_nonneg_left _ hr.le
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (hν y)
      apply max_le _ (by norm_num)
      linarith [(integrand_bounds r σ R hr hσ hσ1 hR g z hg hz x).2,
        (integrand_bounds r σ R hr hσ hσ1 hR g z hg hz y).1]
    _ = _ := by rw [←Finset.sum_mul,hν1]; ring


end
end UniformKServer.PilotCompact


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotCapacity
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem other_reduction_loss [DecidableEq X] (r σ R : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hR : 256 ≤ R)
    (g z : X → ℝ) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1) (hz : feasible r σ R z)
    (s x p : X) :
    (∑ t, if t=s ∨ t=x then 0 else
      (relocate r R z s x t-z t)*coefficient r σ R g t p) ≤ 2*((dist s x/r)/(10*R)) := by
  let f : X → ℝ := fun t => if t=s ∨ t=x then 0 else
    (z t-relocate r R z s x t)*bumpB σ (dist t p/r)
  have hRpos : 0 < R := by linarith
  have hq : 0 ≤ (dist s x/r)/(10*R) := by positivity
  have hf : ∀ t, f t ≤ (dist s x/r)/(10*R) := by
    intro t
    dsimp [f]
    split_ifs with ht
    · exact hq
    · have hh := relocate_reduction r R hr hRpos z hz.1 s x t
        (fun h => ht (Or.inl h)) (fun h => ht (Or.inr h))
      exact (mul_le_mul_of_nonneg_left (bumpB_bounds σ _).2 hh.1).trans (by simpa using hh.2)
  have huni : ∀ u v, 0 < f u → 0 < f v → u=v := by
    intro u v hu hv
    have hh : ∀ t, 0 < f t → 0 < z t*bumpB σ (dist t p/r) := by
      intro t ht
      dsimp [f] at ht
      split_ifs at ht with hcase
      · linarith
      · have hc : z t-relocate r R z s x t ≤ z t := by
          linarith [relocate_nonneg r R z hz.1 s x t]
        exact ht.trans_le (mul_le_mul_of_nonneg_right hc (bumpB_bounds σ _).1)
    exact positive_bump_unique r σ R hr hσ z hz p u v (hh u hu) (hh v hv)
  have hsum := sum_le_unique f _ hq hf huni
  have hterm : ∀ t, (if t=s ∨ t=x then 0 else
      (relocate r R z s x t-z t)*coefficient r σ R g t p) ≤ 2*f t := by
    intro t
    dsimp [f]
    split_ifs with ht
    · norm_num
    · have hh := relocate_reduction r R hr hRpos z hz.1 s x t
        (fun h => ht (Or.inl h)) (fun h => ht (Or.inr h))
      have hA := (bumpA_bounds σ R (dist t p/r) hRpos).1
      have hB := (bumpB_bounds σ (dist t p/r)).1
      have hgs := (hg t).1
      have hgp := (hg p).2
      have hac : 0 ≤ (1+g t)*bumpA σ R (dist t p/r) := mul_nonneg (by linarith) hA
      have hbc : 0 ≤ (1-g p)*bumpB σ (dist t p/r) := mul_nonneg (by linarith) hB
      have ha := mul_nonneg hh.1 hac
      have hb := mul_nonneg hh.1 hbc
      unfold coefficient
      nlinarith only [ha,hb]
  calc
    _ ≤ ∑ t, 2*f t := Finset.sum_le_sum fun t _ => hterm t
    _ = 2*∑ t, f t := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)


end
end UniformKServer.PilotCompact

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotRelocation
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]
omit [Fintype X] in
theorem coefficient_move (r σ R L : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hL : 0 ≤ L)
    (g : X → ℝ) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ p q, |g p-g q| ≤ L*(dist p q/r)) (s x p : X) :
    coefficient r σ R g x p-coefficient r σ R g s p ≤
      (1026/σ+256*L)*(dist s x/r) := by
  have hRpos : 0 < R := by linarith
  let w := dist s x/r
  have hw : 0 ≤ w := by dsimp [w] <;> positivity
  have hd := normalized_dist_difference r hr s x p
  have hB : |bumpB σ (dist s p/r)-bumpB σ (dist x p/r)| ≤ w/σ :=
    (bumpB_lipschitz σ _ _ hσ).trans (div_le_div_of_nonneg_right hd hσ.le)
  have hA : |bumpA σ R (dist s p/r)-bumpA σ R (dist x p/r)| ≤ (2/σ)*w :=
    (bumpA_lipschitz σ R _ _ hσ hσ1 hR (by positivity) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hd (by positivity))
  have hgdiff : |g x-g s| ≤ L*w := by
    simpa only [abs_sub_comm] using hgLip s x
  have haBounds := bumpA_bounds σ R (dist x p/r) hRpos
  have hsBounds := hg s
  have hpBounds := hg p
  have hprod : |(1+g x)*bumpA σ R (dist x p/r)-(1+g s)*bumpA σ R (dist s p/r)| ≤
      (4/σ+L)*w := by
    have he : (1+g x)*bumpA σ R (dist x p/r)-(1+g s)*bumpA σ R (dist s p/r) =
        (1+g s)*(bumpA σ R (dist x p/r)-bumpA σ R (dist s p/r))+
        (g x-g s)*bumpA σ R (dist x p/r) := by ring
    rw [he]
    calc
      _ ≤ |(1+g s)*(bumpA σ R (dist x p/r)-bumpA σ R (dist s p/r))|+
        |(g x-g s)*bumpA σ R (dist x p/r)| := abs_add_le _ _
      _ = (1+g s)*|bumpA σ R (dist s p/r)-bumpA σ R (dist x p/r)|+
        |g x-g s| *bumpA σ R (dist x p/r) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hsBounds.1] : 0≤1+g s),
            abs_of_nonneg haBounds.1, abs_sub_comm (bumpA σ R (dist x p/r))]
      _ ≤ 2*((2/σ)*w)+(L*w)*1 := add_le_add
        (mul_le_mul (by linarith [hsBounds.2]) hA (abs_nonneg _) (by norm_num))
        (mul_le_mul hgdiff haBounds.2 haBounds.1 (mul_nonneg hL hw))
      _ = _ := by ring
  have hBg : (1+g p)*(bumpB σ (dist s p/r)-bumpB σ (dist x p/r)) ≤ 2*(w/σ) := by
    calc
      _ ≤ (1+g p)*|bumpB σ (dist s p/r)-bumpB σ (dist x p/r)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith [hpBounds.1])
      _ ≤ 2*(w/σ) := mul_le_mul (by linarith [hpBounds.2]) hB (abs_nonneg _) (by norm_num)
  have hAp : (1+g x)*bumpA σ R (dist x p/r)-(1+g s)*bumpA σ R (dist s p/r) ≤
      (4/σ+L)*w := (le_abs_self _).trans hprod
  unfold coefficient
  calc
    _ = 256*((1+g x)*bumpA σ R (dist x p/r)-(1+g s)*bumpA σ R (dist s p/r))+
        (1+g p)*(bumpB σ (dist s p/r)-bumpB σ (dist x p/r)) := by ring
    _ ≤ 256*((4/σ+L)*w)+2*(w/σ) := add_le_add (by linarith) hBg
    _ = _ := by dsimp [w] <;> ring

theorem relocation_pointwise_loss [DecidableEq X] (r σ R L : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hL : 0 ≤ L)
    (g z : X → ℝ) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ p q, |g p-g q| ≤ L*(dist p q/r)) (hz : feasible r σ R z)
    (s x p : X) (hsx : s ≠ x) (hzx : z x=0) :
    integrand r σ R g (relocate r R z s x) p-integrand r σ R g z p ≤
      (z s*(1026/σ+256*L)+2/(10*R))*(dist s x/r) := by
  rw [integrand_relocate r σ R g z s x p hsx hzx]
  calc
    _ ≤ z s*((1026/σ+256*L)*(dist s x/r))+2*((dist s x/r)/(10*R)) := add_le_add
      (mul_le_mul_of_nonneg_left (coefficient_move r σ R L hr hσ hσ1 hR hL g hg hgLip s x p) (hz.1 s))
      (other_reduction_loss r σ R hr hσ hR g z hg hz s x p)
    _ = _ := by ring

theorem relocation_integral_loss [DecidableEq X] (r σ R γ L : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hL : 0 ≤ L) (hγσ : γ ≤ σ/64) (hLγ : L*γ ≤ 1)
    (μ g z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ p q, |g p-g q| ≤ L*(dist p q/r)) (hz : feasible r σ R z)
    (s x : X) (hsx : s ≠ x) (hzx : z x=0) (hnear : dist s x/r < σ/4)
    (hother : ∀ t, t ≠ s → 0 < z t → R/2 < dist t x/r) :
    (∑ p, μ p*(integrand r σ R g (relocate r R z s x) p-integrand r σ R g z p)) ≤
      -(256*z s/σ^2)*((dist s x/r)^2*ballMass r γ μ x -
        5*(dist s x/r)*innerMoment r γ μ x) +
      (z s*(1026/σ+256*L)+2/(10*R))*(dist s x/r)*
        (ballMass r (100*R) μ x-ballMass r γ μ x) := by
  let A := 256*z s/σ^2
  let B := (z s*(1026/σ+256*L)+2/(10*R))*(dist s x/r)
  let w := dist s x/r
  have hbound : ∀ p, integrand r σ R g (relocate r R z s x) p-integrand r σ R g z p ≤
      -A*(w^2-5*w*(dist x p/r))*(if dist x p ≤ γ*r then 1 else 0) +
      B*((if dist x p ≤ (100*R)*r then 1 else 0)-(if dist x p ≤ γ*r then 1 else 0)) := by
    intro p
    by_cases hi : dist x p ≤ γ*r
    · have ho : dist x p ≤ (100*R)*r := hi.trans
        (mul_le_mul_of_nonneg_right (by linarith : γ ≤ 100*R) hr.le)
      simp only [ite_eq_left hi,ite_eq_left ho,sub_self,mul_zero,add_zero,mul_one]
      exact relocated_inner_gain r σ R γ L hr hσ hσ1 hR hL hγσ hLγ g z hg hgLip hz s x p hsx hzx hnear hother hi
    · rw [ite_eq_right hi]
      simp only [mul_zero,sub_zero,zero_add]
      by_cases ho : dist x p ≤ (100*R)*r
      · rw [ite_eq_left ho,mul_one]
        exact relocation_pointwise_loss r σ R L hr hσ hσ1 hR hL g z hg hgLip hz s x p hsx hzx
      · rw [ite_eq_right ho,mul_zero,relocate_unchanged_outside r σ R hr hσ hσ1 hR g z s x p hsx hzx hnear (lt_of_not_ge ho)]
  have he : (∑ p, μ p*(-A*(w^2-5*w*(dist x p/r))*(if dist x p ≤ γ*r then 1 else 0) +
      B*((if dist x p ≤ (100*R)*r then 1 else 0)-(if dist x p ≤ γ*r then 1 else 0)))) =
      -A*(w^2*ballMass r γ μ x-5*w*innerMoment r γ μ x)+B*(ballMass r (100*R) μ x-ballMass r γ μ x) := by
    unfold ballMass innerMoment
    simp only [mul_sub,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    split_ifs <;> ring
  exact (Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (hbound p) (hμ p))).trans_eq he

theorem near_displacement [DecidableEq X] (r σ R γ δ L : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hL : 0 ≤ L) (hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hγL : γ ≤ 1/(1+L))
    (hδ : 0 < δ) (hδbound : δ ≤ 1/4112)
    (μ g z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ p q, |g p-g q| ≤ L*(dist p q/r))
    (x : X) (hM : 0 < ballMass r γ μ x)
    (hconc : ballMass r (100*R) μ x ≤ (1+δ)*ballMass r γ μ x)
    (hz : feasible r σ R z)
    (hmin : objective r σ R μ g z = value r σ R μ g)
    (s : X) (hs : 0 < z s) (hnear : dist s x/r < σ/4) :
    dist s x/r ≤ (5+L)*((ballMass r (100*R) μ x-ballMass r γ μ x)/ballMass r γ μ x +
      innerMoment r γ μ x/ballMass r γ μ x) := by
  let M := ballMass r γ μ x
  let S := ballMass r (100*R) μ x
  let T := innerMoment r γ μ x
  let w := dist s x/r
  let A := 256*z s/σ^2
  let B := z s*(1026/σ+256*L)+2/(10*R)
  have hT : 0 ≤ T := (innerMoment_bounds r γ hr μ hμ x).1
  have hSM : 0 ≤ S-M := sub_nonneg.mpr
    (ballMass_mono r γ (100*R) hr.le (by linarith) μ hμ x)
  have hC : 0 ≤ 5+L := by linarith
  by_cases hsx : s=x
  · subst s
    simp only [dist_self,zero_div]
    exact mul_nonneg hC (add_nonneg (div_nonneg hSM hM.le) (div_nonneg hT hM.le))
  have hw : 0 < w := div_pos (dist_pos.mpr hsx) hr
  have hA : 0 < A := by dsimp [A] <;> positivity
  have hlarge : (3:ℝ)/4 ≤ z s := by
    have hh := nearWeight_large r σ R γ δ hr hσ hσ1 hR hγ hγσ hδ hδbound μ g z hμ hg x hM hconc hz hmin
    rwa [nearWeight_eq_site r σ R hr hσ z hz x s hs hnear] at hh
  have hother : ∀ t, t ≠ s → 0 < z t → R/2 < dist t x/r := by
    intro t hts htp
    by_contra hfar
    have hfar' : dist t x/r ≤ R/2 := le_of_not_gt hfar
    have hnear' : σ/4 ≤ dist t x/r := by
      by_contra hh
      exact hts (near_positive_unique r σ R hr hσ z hz x s t hs htp hnear (lt_of_not_ge hh))
    have he := middle_site_zero r σ R γ δ hr hσ hσ1 hR hγ hγσ hδ hδbound μ g z hμ hg x hM hconc hz hmin t hnear' hfar'
    linarith
  have hzx := zero_at_relocation_target r σ R hr hR z hz s x hsx hother
  have hfeas := relocate_feasible r σ R hr hσ hσ1 hR z hz s x hsx hs hnear hother
  have hLγ : L*γ ≤ 1 := by
    have hh := (le_div_iff₀ (by linarith : 0<1+L)).mp hγL
    nlinarith
  have henergy := relocation_integral_loss r σ R γ L hr hσ hσ1 hR hL hγσ hLγ μ g z hμ hg hgLip hz s x hsx hzx hnear hother
  have hmin' := value_le r σ R μ g (relocate r R z s x) hfeas
  rw [←hmin] at hmin'
  have hnonneg : 0 ≤ ∑ p, μ p*(integrand r σ R g (relocate r R z s x) p-integrand r σ R g z p) := by
    unfold objective at hmin'
    have hh := (mul_le_mul_iff_right₀ hr).mp hmin'
    simp_rw [mul_sub,Finset.sum_sub_distrib]
    linarith
  have hb : B ≤ A*(5+L) := relocation_constant_bound σ R L (z s) hσ hσ1 hR hL (by linarith)
  have hpay : B*w*(S-M) ≤ A*(5+L)*w*(S-M) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hw.le) hSM
  have hcap : A*w*(M*w-5*T-(5+L)*(S-M)) ≤ 0 := by
    change (∑ p, μ p*(integrand r σ R g (relocate r R z s x) p-integrand r σ R g z p)) ≤
      -A*(w^2*M-5*w*T)+B*w*(S-M) at henergy
    nlinarith only [henergy,hnonneg,hpay]
  have hnum : M*w ≤ 5*T+(5+L)*(S-M) := by
    by_contra hh
    have hp := mul_pos (mul_pos hA hw) (show 0<M*w-5*T-(5+L)*(S-M) by linarith)
    linarith
  calc
    w ≤ (5*T+(5+L)*(S-M))/M := (le_div_iff₀ hM).mpr (by nlinarith only [hnum])
    _ ≤ ((5+L)*T+(5+L)*(S-M))/M := div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hL hT]) hM.le
    _ = _ := by dsimp [M,S,T] <;> ring



end
end UniformKServer.PilotCompact

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotSlope
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem local_slope [DecidableEq X] (r σ R γ δ L : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hL : 0 ≤ L) (hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hγL : γ ≤ 1/(1+L))
    (hδ : 0 < δ) (hδbound : δ ≤ 1/4112)
    (μ g z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ p q, |g p-g q| ≤ L*(dist p q/r))
    (x y : X) (hM : 0 < ballMass r γ μ x)
    (hconc : ballMass r (100*R) μ x ≤ (1+δ)*ballMass r γ μ x)
    (hz : feasible r σ R z) (hmin : objective r σ R μ g z = value r σ R μ g)
    (hxy : dist x y/r < σ/8) :
    max (integrand r σ R g z x-integrand r σ R g z y) 0 ≤
      localSlopeConstant σ L *
      ((ballMass r (100*R) μ x-ballMass r γ μ x)/ballMass r γ μ x +
        innerMoment r γ μ x/ballMass r γ μ x)*(dist x y/r) := by
  obtain ⟨s,hnear,hlarge,huniq,hdef⟩ := near_site_exists r σ R γ δ hr hσ hσ1 hR hγ hγσ hδ hδbound
    μ g z hμ hg x hM hconc hz hmin
  have hs : 0<z s := by linarith
  have hdisp := near_displacement r σ R γ δ L hr hσ hσ1 hR hL hγ hγσ hγL hδ hδbound
    μ g z hμ hg hgLip x hM hconc hz hmin s hs hnear
  have hother : ∀ t,t≠s → 0<z t → R/2<dist t x/r := by
    intro t hts htp
    by_contra hf
    have hn : σ/4≤dist t x/r := by
      by_contra hh
      exact hts (huniq t htp (lt_of_not_ge hh))
    have he := middle_site_zero r σ R γ δ hr hσ hσ1 hR hγ hγσ hδ hδbound
      μ g z hμ hg x hM hconc hz hmin t hn (le_of_not_gt hf)
    linarith
  let h := (ballMass r (100*R) μ x-ballMass r γ μ x)/ballMass r γ μ x
  let t := innerMoment r γ μ x/ballMass r γ μ x
  have hh : 0≤h := div_nonneg (sub_nonneg.mpr (ballMass_mono r γ (100*R) hr.le (by linarith) μ hμ x)) hM.le
  have ht : 0≤t := div_nonneg (innerMoment_bounds r γ hr μ hμ x).1 hM.le
  have hc : 512*γ/σ^2≤8/σ := by
    calc
      _ ≤ (8*σ)/σ^2 := div_le_div_of_nonneg_right (by linarith) (sq_nonneg σ)
      _ = _ := by field_simp
  have hdef' : 1-z s≤(514+8/σ)*(h+t) := by
    have hc' := mul_le_mul_of_nonneg_right hc ht
    have hp1 : 0≤(8/σ)*h := by positivity
    change 1-z s≤(512*γ/σ^2)*t+514*h at hdef
    nlinarith only [hdef,hc',hp1,ht]
  have hv : 0≤dist x y/r := by positivity
  have hcp : 0≤L+1024/σ := by positivity
  have hsp : 0≤1024/σ^2 := by positivity
  have hk : 0≤localSlopeConstant σ L := by unfold localSlopeConstant; positivity
  refine max_le ?_ (mul_nonneg (mul_nonneg hk (add_nonneg hh ht)) hv)
  have hraw := local_slope_raw r σ R L hr hσ hσ1 hR hL g z hg hgLip hz s x y hnear hother hxy
  have h1 := mul_le_mul_of_nonneg_left hdef' hcp
  have h2 := mul_le_mul_of_nonneg_left hdisp hsp
  have hco : (L+1024/σ)*(1-z s)+1024*(dist s x/r)/σ^2 ≤ localSlopeConstant σ L*(h+t) := by
    change (1024/σ^2)*(dist s x/r) ≤ (1024/σ^2)*((5+L)*(h+t)) at h2
    calc
      _ = (L+1024/σ)*(1-z s)+(1024/σ^2)*(dist s x/r) := by ring
      _ ≤ (L+1024/σ)*((514+8/σ)*(h+t))+(1024/σ^2)*((5+L)*(h+t)) := add_le_add h1 h2
      _ = _ := by unfold localSlopeConstant; ring
  exact hraw.trans (mul_le_mul_of_nonneg_right hco hv)

end
end UniformKServer.PilotCompact


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotStability
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem shell_scale_sum (r τ γ R : ℝ) (N p : ℕ) (k : ℝ)
    (hr : 0 < r) (hτ : 2 ≤ τ) (hγ : 0 < γ) (hγR : γ ≤ 100*R)
    (hp : 100*R ≤ γ*(2:ℝ)^p) (hk : 1/2 ≤ k)
    (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hμk : ∑ y, μ y = k) (x : X)
    (hM : 1/2 ≤ ballMass r γ μ x) :
    (∑ j ∈ Finset.range N, min 1 (shellRatio (r*τ^j) γ R μ x)) ≤
      (p:ℝ)/Real.log 2*Real.log (2*k) := by
  let A := fun j => ballMass (r*τ^(N-1-j)) γ μ x
  let B := fun j => ballMass (r*τ^(N-1-j)) (100*R) μ x
  have hrad : Monotone (fun j => r*τ^j) := PilotScales.radius_mono r τ hr.le (by linarith)
  have ha (j : ℕ) : 1/2 ≤ A j := by
    apply hM.trans
    apply ballMass_extent_mono _ _ _ _ _ μ hμ x
    exact mul_le_mul_of_nonneg_left (by simpa using hrad (Nat.zero_le (N-1-j))) hγ.le
  have hs : ∀ j < N, B j ≤ if j < p then k else A (j-p) := by
    intro j hj
    by_cases hjp : j < p
    · rw [ite_eq_left hjp]
      exact (ballMass_total _ _ μ hμ x).trans_eq hμk
    · rw [ite_eq_right hjp]
      apply ballMass_extent_mono _ _ _ _ _ μ hμ x
      have hid : N-1-(j-p) = (N-1-j)+p := by omega
      have hpow : (2:ℝ)^p ≤ τ^p := pow_le_pow_left₀ (by norm_num) hτ p
      have hshift : 100*R ≤ γ*τ^p := hp.trans (mul_le_mul_of_nonneg_left hpow hγ.le)
      change 100*R*(r*τ^(N-1-j)) ≤ γ*(r*τ^(N-1-(j-p)))
      rw [hid,pow_add]
      calc
        _ ≤ (γ*τ^p)*(r*τ^(N-1-j)) := mul_le_mul_of_nonneg_right hshift (by positivity)
        _ = _ := by ring
  have hb : ∀ j < N, A j ≤ B j := by
    intro j _
    exact ballMass_mono _ γ (100*R) (by positivity) hγR μ hμ x
  have hh := PilotScales.shell_sum A B N p (1/2) k (by norm_num) hk
    (fun j _ => ha j) hb hs
  have he : k/(1/2) = 2*k := by ring
  rw [he] at hh
  change (∑ j ∈ Finset.range N, (fun i => min 1 (shellRatio (r*τ^i) γ R μ x)) (N-1-j)) ≤ _ at hh
  rw [Finset.sum_range_reflect (fun i => min 1 (shellRatio (r*τ^i) γ R μ x)) N] at hh
  exact hh

theorem moment_scale_sum (r τ γ : ℝ) (N : ℕ) (k : ℝ)
    (hr : 0 < r) (hτ : 2 ≤ τ) (hγ : 0 < γ) (hk : 1/2 ≤ k)
    (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hμk : ∑ y, μ y = k) (x : X)
    (hM : 1/2 ≤ ballMass r γ μ x) :
    (∑ j ∈ Finset.range N, momentRatio (r*τ^j) γ μ x) ≤
      2*γ*(1+Real.log (2*k)) := by
  have hpos : 0 < ballMass r γ μ x := by linarith
  have hlog : 0 ≤ Real.log (2*k) := Real.log_nonneg (by linarith)
  by_cases hN : N = 0
  · subst N
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  · have h := PilotScales.pilot_moment_sum μ (dist x) hμ (fun _ => dist_nonneg)
      r τ γ hr hτ hγ N (Nat.pos_of_ne_zero hN) hpos
    have he : (∑ j ∈ Finset.range N, momentRatio (r*τ^j) γ μ x) =
        ∑ j ∈ Finset.range N, PilotScales.moment μ (dist x) (γ*PilotScales.radius r τ j) /
          (PilotScales.radius r τ j * PilotScales.mass μ (dist x) (γ*PilotScales.radius r τ j)) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [momentRatio,innerMoment_mass,div_div,ballMass,PilotScales.mass,PilotScales.radius]
      rfl
    rw [he]
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add_right
    apply Real.log_le_log
    · exact div_pos ((show ballMass r γ μ x ≤ ballMass (r*τ^(N-1)) γ μ x from
        ballMass_extent_mono _ _ _ _ (mul_le_mul_of_nonneg_left
          (by simpa [PilotScales.radius] using PilotScales.radius_mono r τ hr.le (by linarith) (Nat.zero_le (N-1))) hγ.le) μ hμ x).trans_lt' hpos) hpos
    · apply (div_le_iff₀ hpos).mpr
      change ballMass (r*τ^(N-1)) γ μ x ≤ 2*k*ballMass r γ μ x
      have ht := (ballMass_total (r*τ^(N-1)) γ μ hμ x).trans_eq hμk
      nlinarith [mul_le_mul_of_nonneg_left hM (show 0 ≤ k by linarith)]

end
end UniformKServer.PilotCompact


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotPersistence
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem good_drift [DecidableEq X] (r σ R γ δ L : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hL : 0 ≤ L) (hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hγL : γ ≤ 1/(1+L))
    (hδ : 0 < δ) (hδbound : δ ≤ 1/4112)
    (μ ν g : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hν : ∀ y, 0 ≤ ν y)
    (hν1 : ∑ y, ν y = 1) (hg : ∀ y, g y ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ y z, |g y-g z| ≤ L*(dist y z/r)) (x : X)
    (hM : 0 < ballMass r γ μ x) (hgood : shellRatio r γ R μ x ≤ δ) :
    positiveDrift r σ R μ ν g x ≤
      localSlopeConstant σ L*(shellRatio r γ R μ x+momentRatio r γ μ x)*
        (∑ y, ν y*dist x y)+exceptional r σ ν x := by
  have hconc : ballMass r (100*R) μ x ≤ (1+δ)*ballMass r γ μ x := by
    have hx := (div_le_iff₀ hM).mp hgood
    linarith
  have hh := shellRatio_nonneg r γ R hr.le (by linarith) μ hμ x
  have ht := momentRatio_nonneg r γ hr μ hμ x
  have hC : 0 ≤ localSlopeConstant σ L := by unfold localSlopeConstant; positivity
  obtain ⟨z,hz,hmin,_⟩ := minimum_exists r σ R μ g
  have hpoint (y : X) :
      max (integrand r σ R g z x-integrand r σ R g z y) 0 ≤
        localSlopeConstant σ L*(shellRatio r γ R μ x+momentRatio r γ μ x)*(dist x y/r)+
          if r ≤ 8*dist x y/σ then 514 else 0 := by
    by_cases he : r ≤ 8*dist x y/σ
    · rw [ite_eq_left he]
      have hd : 0 ≤ localSlopeConstant σ L*(shellRatio r γ R μ x+momentRatio r γ μ x)*(dist x y/r) := by positivity
      apply max_le _ (by linarith)
      linarith [(integrand_bounds r σ R hr hσ hσ1 hR g z hg hz x).2,
        (integrand_bounds r σ R hr hσ hσ1 hR g z hg hz y).1]
    · rw [ite_eq_right he,add_zero]
      apply local_slope r σ R γ δ L hr hσ hσ1 hR hL hγ hγσ hγL hδ hδbound
        μ g z hμ hg hgLip x y hM hconc hz hmin
      apply (div_lt_iff₀ hr).mpr
      have hx := (div_lt_iff₀ hσ).mp (lt_of_not_ge he)
      nlinarith
  calc
    _ ≤ r*∑ y, ν y*max (integrand r σ R g z x-integrand r σ R g z y) 0 :=
      drift_nonneg_bound r σ R hr μ ν g z hν hν1 x hz hmin
    _ ≤ r*∑ y, ν y*(localSlopeConstant σ L*(shellRatio r γ R μ x+momentRatio r γ μ x)*(dist x y/r)+
          if r ≤ 8*dist x y/σ then 514 else 0) := by
      apply mul_le_mul_of_nonneg_left _ hr.le
      exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hpoint y) (hν y)
    _ = _ := by
      unfold exceptional
      rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs
      · field_simp
      · field_simp
        ring

theorem mixed_drift [DecidableEq X] (r σ R γ δ L : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hL : 0 ≤ L) (hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hγL : γ ≤ 1/(1+L))
    (hδ : 0 < δ) (hδbound : δ ≤ 1/4112)
    (μ ν g : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hν : ∀ y, 0 ≤ ν y)
    (hν1 : ∑ y, ν y = 1) (hg : ∀ y, g y ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ y z, |g y-g z| ≤ L*(dist y z/r)) (x : X)
    (hM : 0 < ballMass r γ μ x) :
    positiveDrift r σ R μ ν g x ≤
      ((L+1026/σ)/δ*min 1 (shellRatio r γ R μ x)+
        localSlopeConstant σ L*(min 1 (shellRatio r γ R μ x)+momentRatio r γ μ x))*
        (∑ y, ν y*dist x y)+exceptional r σ ν x := by
  let h := shellRatio r γ R μ x
  let t := momentRatio r γ μ x
  have hh : 0 ≤ h := shellRatio_nonneg r γ R hr.le (by linarith) μ hμ x
  have ht : 0 ≤ t := momentRatio_nonneg r γ hr μ hμ x
  have he : 0 ≤ ∑ y, ν y*dist x y := Finset.sum_nonneg fun y _ => mul_nonneg (hν y) dist_nonneg
  have hC : 0 ≤ localSlopeConstant σ L := by unfold localSlopeConstant; positivity
  have hΛ : 0 ≤ L+1026/σ := by positivity
  have hm : 0 ≤ min 1 h := le_min (by norm_num) hh
  have hex := exceptional_nonneg r σ hr.le ν hν x
  change positiveDrift r σ R μ ν g x ≤
    ((L+1026/σ)/δ*min 1 h+localSlopeConstant σ L*(min 1 h+t))*(∑ y,ν y*dist x y)+exceptional r σ ν x
  by_cases hg' : h ≤ δ
  · have hmin : min 1 h = h := min_eq_right (by linarith)
    rw [hmin]
    have hbound := good_drift r σ R γ δ L hr hσ hσ1 hR hL hγ hγσ hγL hδ hδbound
      μ ν g hμ hν hν1 hg hgLip x hM hg'
    have hnonneg : 0 ≤ ((L+1026/σ)/δ*h)*(∑ y, ν y*dist x y) := by positivity
    dsimp [h,t] at hnonneg ⊢
    nlinarith only [hbound,hnonneg]
  · have hδmin : δ ≤ min 1 h := le_min (by linarith) (le_of_not_ge hg')
    have hΛbound : L+1026/σ ≤ (L+1026/σ)/δ*min 1 h := by
      calc
        _ = (L+1026/σ)/δ*δ := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hδmin (by positivity)
    have hbound := drift_lipschitz r σ R L hr hσ hσ1 hR hL μ ν g hν hν1 x hg hgLip
    have hmul := mul_le_mul_of_nonneg_right hΛbound he
    have hnonneg : 0 ≤ (localSlopeConstant σ L*(min 1 h+t))*(∑ y,ν y*dist x y) := by positivity
    change positiveDrift r σ R μ ν g x ≤ _ at hbound
    nlinarith only [hbound,hmul,hnonneg,hex]

end
end UniformKServer.PilotCompact


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotCredits
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem coarse_drift [DecidableEq X] (r τ σ R γ δ L : ℝ) (N p : ℕ) (k : ℝ)
    (hr : 0 < r) (hτ : 2 ≤ τ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hL : 0 ≤ L) (hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hγL : γ ≤ 1/(1+L))
    (hδ : 0 < δ) (hδbound : δ ≤ 1/4112) (hk : 1/2 ≤ k)
    (hp : 100*R ≤ γ*(2:ℝ)^p)
    (μ ν : X → ℝ) (g : ℕ → X → ℝ) (x : X)
    (hμ : ∀ y, 0 ≤ μ y) (hμk : ∑ y, μ y = k)
    (hν : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1)
    (hg : ∀ j y, g j y ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ j y z, |g j y-g j z| ≤ L*(dist y z/(r*τ^j)))
    (hM : 1/2 ≤ ballMass r γ μ x) :
    (∑ j ∈ Finset.range N, positiveDrift (r*τ^j) σ R μ ν (g j) x) ≤
      coarseConstant σ γ δ L p k*(∑ y, ν y*dist x y) := by
  have hτ0 : 0 < τ := by linarith
  have he : 0 ≤ ∑ y, ν y*dist x y := Finset.sum_nonneg fun y _ => mul_nonneg (hν y) dist_nonneg
  have hA : 0 ≤ (L+1026/σ)/δ := by positivity
  have hC : 0 ≤ localSlopeConstant σ L := by unfold localSlopeConstant; positivity
  have hH := shell_scale_sum r τ γ R N p k hr hτ hγ (by linarith) hp hk μ hμ hμk x hM
  have hT := moment_scale_sum r τ γ N k hr hτ hγ hk μ hμ hμk x hM
  have hE := exceptional_sum r τ σ N hr hτ hσ ν hν x
  have hpoint (j : ℕ) : positiveDrift (r*τ^j) σ R μ ν (g j) x ≤
      ((L+1026/σ)/δ*min 1 (shellRatio (r*τ^j) γ R μ x)+
        localSlopeConstant σ L*(min 1 (shellRatio (r*τ^j) γ R μ x)+momentRatio (r*τ^j) γ μ x))*
        (∑ y, ν y*dist x y)+exceptional (r*τ^j) σ ν x := by
    apply mixed_drift _ σ R γ δ L (by positivity) hσ hσ1 hR hL hγ hγσ hγL hδ hδbound
      μ ν (g j) hμ hν hν1 (hg j) (hgLip j) x
    have hm := ballMass_extent_mono r (r*τ^j) γ γ (mul_le_mul_of_nonneg_left
      (by simpa [PilotScales.radius] using PilotScales.radius_mono r τ hr.le (by linarith) (Nat.zero_le j)) hγ.le) μ hμ x
    linarith
  calc
    _ ≤ ∑ j ∈ Finset.range N,
      (((L+1026/σ)/δ*min 1 (shellRatio (r*τ^j) γ R μ x)+
        localSlopeConstant σ L*(min 1 (shellRatio (r*τ^j) γ R μ x)+momentRatio (r*τ^j) γ μ x))*
        (∑ y, ν y*dist x y)+exceptional (r*τ^j) σ ν x) :=
      Finset.sum_le_sum fun j _ => hpoint j
    _ = ((L+1026/σ)/δ*(∑ j ∈ Finset.range N, min 1 (shellRatio (r*τ^j) γ R μ x))+
        localSlopeConstant σ L*((∑ j ∈ Finset.range N, min 1 (shellRatio (r*τ^j) γ R μ x))+
          ∑ j ∈ Finset.range N, momentRatio (r*τ^j) γ μ x))*(∑ y,ν y*dist x y)+
        ∑ j ∈ Finset.range N, exceptional (r*τ^j) σ ν x := by
      rw [Finset.sum_add_distrib,←Finset.sum_mul,Finset.sum_add_distrib,
        ←Finset.mul_sum,←Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ ((L+1026/σ)/δ*((p:ℝ)/Real.log 2*Real.log (2*k)) +
        localSlopeConstant σ L*((p:ℝ)/Real.log 2*Real.log (2*k)+2*γ*(1+Real.log (2*k))))*
        (∑ y,ν y*dist x y)+(8224/σ)*(∑ y,ν y*dist x y) := by
      exact add_le_add (mul_le_mul_of_nonneg_right
        (add_le_add (mul_le_mul_of_nonneg_left hH hA)
          (mul_le_mul_of_nonneg_left (add_le_add hH hT) hC)) he) hE
    _ = _ := by unfold coarseConstant; ring

theorem driftConstant_log (σ γ δ L : ℝ) (p : ℕ) (k : ℝ)
    (hσ : 0 < σ) (hγ : 0 < γ) (hδ : 0 < δ) (hL : 0 ≤ L) (hk : 2 ≤ k) :
    2056/γ + coarseConstant σ γ δ L p k ≤ driftConstant σ γ δ L p*(1+Real.log (k+1)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk1 : 0 < k+1 := by linarith
  have hlk : 0 ≤ Real.log (k+1) := Real.log_nonneg (by linarith)
  have hl : Real.log (2*k) ≤ 2*Real.log (k+1) := by
    have hh := Real.log_le_log (by linarith : 0 < 2*k)
      (show 2*k ≤ (k+1)*(k+1) by nlinarith [sq_nonneg k])
    rw [Real.log_mul hk1.ne' hk1.ne'] at hh
    linarith
  have hl' : Real.log (2*k) ≤ 2*(1+Real.log (k+1)) := by linarith
  have h1l : 1+Real.log (2*k) ≤ 2*(1+Real.log (k+1)) := by linarith
  have hH := mul_le_mul_of_nonneg_left hl' (show 0 ≤ (p:ℝ)/Real.log 2 by positivity)
  have hT := mul_le_mul_of_nonneg_left h1l (show 0 ≤ 2*γ by positivity)
  have hbase := mul_le_mul_of_nonneg_left (show 1 ≤ 1+Real.log (k+1) by linarith)
    (show 0 ≤ 2056/γ+8224/σ by positivity)
  have hA : 0 ≤ (L+1026/σ)/δ := by positivity
  have hC : 0 ≤ localSlopeConstant σ L := by unfold localSlopeConstant; positivity
  calc
    _ = (2056/γ+8224/σ) + (L+1026/σ)/δ*((p:ℝ)/Real.log 2*Real.log (2*k)) +
        localSlopeConstant σ L*((p:ℝ)/Real.log 2*Real.log (2*k)+2*γ*(1+Real.log (2*k))) := by
      unfold coarseConstant; ring
    _ ≤ (2056/γ+8224/σ)*(1+Real.log (k+1)) +
        (L+1026/σ)/δ*((p:ℝ)/Real.log 2*(2*(1+Real.log (k+1)))) +
        localSlopeConstant σ L*((p:ℝ)/Real.log 2*(2*(1+Real.log (k+1)))+
          2*γ*(2*(1+Real.log (k+1)))) := by
      exact add_le_add (add_le_add (by simpa using hbase) (mul_le_mul_of_nonneg_left hH hA))
        (mul_le_mul_of_nonneg_left (add_le_add hH hT) hC)
    _ = _ := by unfold driftConstant; field_simp

theorem small_drift [DecidableEq X] (r τ σ R γ e : ℝ) (N : ℕ)
    (hr : 0 < r) (hτ : 2 ≤ τ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hγ : 0 < γ) (he : 0 ≤ e)
    (μ ν : X → ℝ) (g : ℕ → X → ℝ) (x : X)
    (hν : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1)
    (hg : ∀ j y, g j y ∈ Set.Icc (0:ℝ) 1)
    (hsmall : ∀ j < N, r*τ^j ≤ 2*e/γ) :
    (∑ j ∈ Finset.range N, positiveDrift (r*τ^j) σ R μ ν (g j) x) ≤ (2056/γ)*e := by
  have hτ0 : 0 < τ := by linarith
  calc
    _ ≤ ∑ j ∈ Finset.range N, 514*(r*τ^j) := by
      apply Finset.sum_le_sum
      intro j _
      exact drift_bounded _ σ R (by positivity) hσ hσ1 hR μ ν (g j) hν hν1 x (hg j)
    _ = 514*(∑ j ∈ Finset.range N, r*τ^j) := (Finset.mul_sum ..).symm
    _ ≤ 514*(2*(2*e/γ)) := mul_le_mul_of_nonneg_left
      (radius_subsum_le r τ _ hr.le hτ (by positivity) _
        (fun j hj => hsmall j (Finset.mem_range.mp hj))) (by norm_num)
    _ = _ := by ring

end
end UniformKServer.PilotCompact



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotDrift
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

attribute [local instance] Classical.propDecidable

/-- Companion §06, Lemma pilot-drift, in increasing scale order (the finite
source list is its reversal). The integer p is any fixed scale-shift with
2^p γ ≥ 100R; the source uses ceil(log₂(100R/γ)). No drift estimate is assumed. -/
theorem pilot_drift (r τ σ R γ δ L : ℝ) (N p k : ℕ)
    (hr : 0 < r) (hτ : 2 ≤ τ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hL : 0 ≤ L) (hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hγL : γ ≤ 1/(1+L))
    (hδ : 0 < δ) (hδbound : δ ≤ 1/4112) (hk : 2 ≤ k)
    (hp : 100*R ≤ γ*(2:ℝ)^p)
    (μ ν : X → ℝ) (g : ℕ → X → ℝ) (x : X)
    (hμ : ∀ y, 0 ≤ μ y) (hμk : ∑ y, μ y = k)
    (hν : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1) (hνμ : ∀ y, ν y ≤ μ y)
    (hg : ∀ j y, g j y ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ j y z, |g j y-g j z| ≤ L*(dist y z/(r*τ^j))) :
    (∑ j ∈ Finset.range N,
      max (value (r*τ^j) σ R (fun y => μ y-ν y+if y=x then 1 else 0) (g j) -
        value (r*τ^j) σ R μ (g j)) 0) ≤
      driftConstant σ γ δ L p * (1+Real.log (k+1)) * (∑ y, ν y*dist x y) := by
  classical
  let e := ∑ y, ν y*dist x y
  have he : 0 ≤ e := Finset.sum_nonneg fun y _ => mul_nonneg (hν y) dist_nonneg
  have hτ0 : 0 < τ := by linarith
  have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨m,hmN,hsmall,hcoarse⟩ := scale_cut r τ γ e N hγ
  have hsm := small_drift r τ σ R γ e m hr hτ hσ hσ1 hR hγ he μ ν g x hν hν1 hg hsmall
  have hco : (∑ j ∈ Finset.range (N-m), positiveDrift (r*τ^(m+j)) σ R μ ν (g (m+j)) x) ≤
      coarseConstant σ γ δ L p k*e := by
    rcases hcoarse with hm | hcoarse
    · subst m
      simp only [Nat.sub_self,Finset.range_zero,Finset.sum_empty]
      exact mul_nonneg (coarseConstant_nonneg σ γ δ L p k hσ hγ hδ hL (by linarith)) he
    · have hrm : 0 < r*τ^m := by positivity
      have hM := inner_mass_half (r*τ^m) γ hrm hγ μ ν hμ hν hν1 hνμ x hcoarse
      have hh := coarse_drift (r*τ^m) τ σ R γ δ L (N-m) p k hrm hτ hσ hσ1 hR
        hL hγ hγσ hγL hδ hδbound (by linarith) hp μ ν (fun j => g (m+j)) x hμ hμk
        hν hν1 (fun j => hg (m+j)) (fun j y z => by
          simpa only [pow_add,mul_assoc] using hgLip (m+j) y z) hM
      simpa only [pow_add,mul_assoc] using hh
  have hsum : (∑ j ∈ Finset.range N, positiveDrift (r*τ^j) σ R μ ν (g j) x) =
      (∑ j ∈ Finset.range m, positiveDrift (r*τ^j) σ R μ ν (g j) x)+
        ∑ j ∈ Finset.range (N-m), positiveDrift (r*τ^(m+j)) σ R μ ν (g (m+j)) x := by
    conv_lhs => rw [show N = m+(N-m) by omega,Finset.sum_range_add]
  change (∑ j ∈ Finset.range N, positiveDrift (r*τ^j) σ R μ ν (g j) x) ≤ _
  rw [hsum]
  calc
    _ ≤ (2056/γ)*e+coarseConstant σ γ δ L p k*e := add_le_add hsm hco
    _ = (2056/γ+coarseConstant σ γ δ L p k)*e := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (driftConstant_log σ γ δ L p k hσ hγ hδ hL hkR) he

end
end UniformKServer.PilotCompact

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotEdits
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.PilotEdits

section
open PilotCompact
attribute [local instance] Classical.propDecidable
variable {X Ω I : Type*} [Fintype X] [MetricSpace X] [Fintype Ω] [Fintype I]

lemma potential_filtering {k : ℕ} (F : Flow X Ω k)
    (T : I → Template) (a : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (r τ : ℝ) (N t : ℕ) (g : Ω → I → ℕ → X → ℝ)
    (hmeas : ∀ i j ω ω', (F.filtration t).r ω ω' → g ω i j = g ω' i j) :
    average F.weight (fun ω => potential T a r τ N (F.filtered t ω) (g ω)) ≤
      average F.weight (fun ω => potential T a r τ N (F.post t ω) (g ω)) := by
  have he : ∀ μ : Ω → X → ℝ,
      average F.weight (fun ω => potential T a r τ N (μ ω) (g ω)) =
        ∑ i, a i * ∑ j ∈ Finset.range N,
          ∑ ω, F.weight ω*value (r*τ^j) (T i).sigma (T i).R (μ ω) (g ω i j) := by
    intro μ
    simp only [average,potential,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro ω _
    ring
  rw [he,he]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (ha i)
  apply Finset.sum_le_sum
  intro j _
  exact filtering (r*τ^j) (T i).sigma (T i).R F.weight (F.filtration t)
    (F.post t) (F.filtered t) (fun ω => g ω i j) F.weight_nonneg
    (F.post_measurable t) (hmeas i j) (F.filtering t)

lemma potential_drift {k : ℕ} (hk : 2 ≤ k) (F : Flow X Ω k)
    (T : I → Template) (a : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (r τ : ℝ) (hr : 0 < r) (hτ : 2 ≤ τ) (N t : ℕ) (ω : Ω)
    (g : I → ℕ → X → ℝ)
    (hg : ∀ i j y, g i j y ∈ Set.Icc (0:ℝ) 1)
    (hLip : ∀ i j y z, |g i j y-g i j z| ≤ (T i).L*(dist y z/(r*τ^j))) :
    potential T a r τ N (F.post (t+1) ω) g - potential T a r τ N (F.filtered t ω) g ≤
      (∑ i, a i*rate (T i))*(1+Real.log (k+1))*moverCost F t ω := by
  have hu : F.post (t+1) ω = fun y => F.filtered t ω y-F.mover t ω y+
      if y=F.request t ω then 1 else 0 := funext (F.update t ω)
  have hi : ∀ i, (∑ j ∈ Finset.range N,
      (value (r*τ^j) (T i).sigma (T i).R (F.post (t+1) ω) (g i j)-
        value (r*τ^j) (T i).sigma (T i).R (F.filtered t ω) (g i j))) ≤
      rate (T i)*(1+Real.log (k+1))*moverCost F t ω := by
    intro i
    apply le_trans (Finset.sum_le_sum fun j _ => le_max_left _ 0)
    simpa only [hu,rate,moverCost] using pilot_drift r τ (T i).sigma (T i).R (T i).gamma
      (T i).delta (T i).L N (T i).shift k hr hτ (T i).sigma_pos (T i).sigma_le_one
      (T i).R_large (T i).L_nonneg (T i).gamma_pos (T i).gamma_sigma (T i).gamma_L
      (T i).delta_pos (T i).delta_small hk (T i).shift_large (F.filtered t ω)
      (F.mover t ω) (g i) (F.request t ω) (F.filtered_nonneg t ω) (F.filtered_total t ω)
      (F.mover_nonneg t ω) (F.mover_total t ω) (F.mover_le t ω) (hg i) (hLip i)
  calc
    _ = ∑ i, a i * ∑ j ∈ Finset.range N,
      (value (r*τ^j) (T i).sigma (T i).R (F.post (t+1) ω) (g i j)-
        value (r*τ^j) (T i).sigma (T i).R (F.filtered t ω) (g i j)) := by
      simp only [potential,Finset.sum_sub_distrib,mul_sub]
    _ ≤ ∑ i, a i*(rate (T i)*(1+Real.log (k+1))*moverCost F t ω) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hi i) (ha i)
    _ = _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

end
variable {X Ω I : Type*} [Fintype X] [MetricSpace X] [Fintype Ω] [Fintype I]

/-- The finite-family pilot edit budget, companion Corollary pilot-edits.
All constants on the right are fixed before choosing the law and horizon. -/
theorem pilot_edits {k : ℕ} (hk : 2 ≤ k) (F : Flow X Ω k)
    (T : I → Template) (a : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (r τ : ℝ) (hr : 0 < r) (hτ : 2 ≤ τ) (N H : ℕ)
    (g : ℕ → Ω → I → ℕ → X → ℝ)
    (hg : ∀ t ω i j y, g t ω i j y ∈ Set.Icc (0:ℝ) 1)
    (hLip : ∀ t ω i j y z, |g t ω i j y-g t ω i j z| ≤
      (T i).L*(dist y z/(r*τ^j)))
    (hmeas : ∀ t i j ω ω', (F.filtration t).r ω ω' → g t ω i j = g t ω' i j)
    (charge : ℕ → Ω → ℝ) (_hc : ∀ t ω, 0 ≤ charge t ω)
    (hedit : ∀ t ω, charge t ω ≤
      potential T a r τ N (F.post (t+1) ω) (g t ω) -
        potential T a r τ N (F.post (t+1) ω) (g (t+1) ω)) :
    (∑ t ∈ Finset.range H, average F.weight (charge t)) ≤
      (∑ i, a i*rate (T i)) * (1+Real.log (k+1)) *
        (∑ t ∈ Finset.range H, average F.weight (moverCost F t)) +
      2*k*(∑ i, a i)*(∑ j ∈ Finset.range N, r*τ^j)
 := by
  let D := (∑ i, a i*rate (T i))*(1+Real.log (k+1))
  let init := 2*(k:ℝ)*(∑ i, a i)*(∑ j ∈ Finset.range N, r*τ^j)
  let Φ := fun t => average F.weight (fun ω => potential T a r τ N (F.post t ω) (g t ω))
  have hstep : ∀ t, Φ (t+1)+average F.weight (charge t) ≤
      Φ t + D*average F.weight (moverCost F t) := by
    intro t
    have he := average_mono F.weight (charge t)
      (fun ω => potential T a r τ N (F.post (t+1) ω) (g t ω)-
        potential T a r τ N (F.post (t+1) ω) (g (t+1) ω)) F.weight_nonneg (hedit t)
    rw [average_sub] at he
    have hd := average_mono F.weight
      (fun ω => potential T a r τ N (F.post (t+1) ω) (g t ω)-
        potential T a r τ N (F.filtered t ω) (g t ω))
      (fun ω => D*moverCost F t ω) F.weight_nonneg
      (fun ω => potential_drift hk F T a ha r τ hr hτ N t ω (g t ω) (hg t ω) (hLip t ω))
    rw [average_sub,average_smul] at hd
    have hf := potential_filtering F T a ha r τ N t (g t) (hmeas t)
    dsimp only [Φ]
    linarith
  have htel : ∀ H, (∑ t ∈ Finset.range H, average F.weight (charge t))+Φ H ≤
      Φ 0 + D*(∑ t ∈ Finset.range H, average F.weight (moverCost F t)) := by
    intro H
    induction H with
    | zero => simp
    | succ H ih =>
      rw [Finset.sum_range_succ,Finset.sum_range_succ]
      have hs := hstep H
      nlinarith
  have hterminal : 0 ≤ Φ H := by
    apply Finset.sum_nonneg
    intro ω _
    exact mul_nonneg (F.weight_nonneg ω)
      (potential_bounds T a ha r τ hr hτ N k (F.post H ω) (F.post_nonneg H ω)
        (F.post_total H ω) (g H ω) (hg H ω)).1
  have hinit : Φ 0 ≤ init := by
    have hh := average_mono F.weight
      (fun ω => potential T a r τ N (F.post 0 ω) (g 0 ω))
      (fun _ => init) F.weight_nonneg (fun ω =>
        (potential_bounds T a ha r τ hr hτ N k (F.post 0 ω) (F.post_nonneg 0 ω)
        (F.post_total 0 ω) (g 0 ω) (hg 0 ω)).2)
    simpa only [Φ,average,←Finset.sum_mul,F.weight_total,one_mul] using hh
  have htotal := htel H
  change _ ≤ D*(∑ t ∈ Finset.range H, average F.weight (moverCost F t))+init
  linarith

end UniformKServer.PilotEdits

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HiddenFlow
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! The true-metric posterior flow is derived from literal labeled one-server
trajectories. Observing further partition randomness may refine the filtration;
no filtering identity on a later selected event is assumed. -/
noncomputable section
namespace UniformKServer.HiddenFlow
open Finset ConditionalLaw
open scoped Classical
variable {X Ω : Type*} [Fintype X] [Fintype Ω] {k : ℕ}

section Cost
variable [MetricSpace X]

theorem expected_mover_cost (D : Data X Ω k) (t : ℕ) :
    (∑ ω, D.weight ω*PilotEdits.moverCost (flow D) t ω)=
    ∑ ω, D.weight ω*dist (D.request t ω) (D.position t ω (D.chosen t ω)) := by
  unfold PilotEdits.moverCost
  change (∑ ω, D.weight ω*∑ y, mover D t ω y*dist (D.request t ω) y)=_
  simp only [mul_sum]
  rw [sum_comm]
  have he (y : X) : (∑ ω, D.weight ω*(mover D t ω y*dist (D.request t ω) y))=
      ∑ ω, D.weight ω*(moverAtom D t ω y*dist (D.request t ω) y) := by
    have h := test_identity (fun v => (D.positive v).le) (D.filtration (t+1))
      (fun v => dist (D.request t v) y) (fun v => moverAtom D t v y)
      (fun ω v hv => by change dist (D.request t ω) y=dist (D.request t v) y; rw [D.request_measurable t ω v hv])
    unfold mover
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (apply sum_congr rfl <;> intro ω _ <;> ring)
  simp_rw [he]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  rw [←mul_sum]
  simp only [moverAtom,atom,ite_mul,one_mul,zero_mul]
  simp

end Cost
end UniformKServer.HiddenFlow

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_KeySizeTracker
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! The unreset affine entropy tracker for each fixed heavy-key slot. Filtering
is charged at the old measurable coefficient on every step. -/
noncomputable section
namespace UniformKServer.KeySizeTracker
open Finset RankTracking EntropyCredit
open scoped Classical
variable {Ω : Type*} [Fintype Ω]

variable {K : ℝ}

def pot (I : Input Ω K) (t : ℕ) (ω : Ω) : ℝ := tangent (held I t ω) (I.size t ω)

theorem comparisons (I : Input Ω K) (t : ℕ) (ω : Ω) : keep (I.size t ω) (held I t ω) := by
  have hp := (I.range t ω).1
  cases t with
  | zero => simp only [held,keep]; constructor <;> nlinarith
  | succ t =>
    simp only [held]
    split_ifs with h
    · exact h
    · unfold keep; constructor <;> nlinarith

theorem held_measurable (I : Input Ω K) (t : ℕ) : measurableAt I.filtration t (held I t) := by
  induction t with
  | zero => exact I.measurable 0
  | succ t ih =>
    intro ω v hv
    have ho := ih ω v (I.refines t ω v hv)
    have hn := I.measurable (t+1) ω v hv
    simp only [held,ho,hn]

theorem potential_bound (I : Input Ω K) (hK : 1 ≤ K) (t : ℕ) (ω : Ω) :
    |pot I t ω| ≤ K*(1+ell K) := by
  have hu := held_range I t ω
  have hs := I.range t ω
  have he : |1+Real.log (held I t ω)| ≤ ell K := by simpa only [abs_neg] using slope_bound K _ hK hu
  have hp : 0 ≤ ell K := by unfold ell; linarith [Real.log_nonneg hK]
  unfold pot tangent
  calc
    _ ≤ |held I t ω|+|(1+Real.log (held I t ω))*I.size t ω| := abs_sub _ _
    _ = held I t ω+|1+Real.log (held I t ω)| *I.size t ω := by
      rw [abs_mul,abs_of_nonneg (show 0 ≤ held I t ω by linarith [hu.1]),
        abs_of_nonneg (show 0 ≤ I.size t ω by linarith [hs.1])]
    _ ≤ K+(ell K)*K := add_le_add hu.2 (mul_le_mul he hs.2 (by linarith [hs.1]) hp)
    _ = _ := by ring

theorem step_release (I : Input Ω K) (t : ℕ) (ω : Ω) :
    charge I t ω ≤ 144*(tangent (held I t ω) (I.size (t+1) ω)-pot I (t+1) ω) := by
  by_cases h : keep (I.size (t+1) ω) (held I t ω)
  · simp only [charge,pot,held,ite_eq_left h,sub_self,mul_zero,le_refl]
  · have hc := relative_credit (I.size (t+1) ω) (held I t ω)
      (by linarith [(I.range (t+1) ω).1]) (by linarith [(held_range I t ω).1]) h
    simpa only [charge,ite_eq_right h,pot,held,add_comm] using hc

theorem potential_step (I : Input Ω K) (t : ℕ) (ω : Ω) :
    charge I t ω+144*pot I (t+1) ω ≤ 144*pot I t ω+
      144*(-(1+Real.log (held I t ω)))*(I.filtered (t+1) ω-I.size t ω)+
      144*(-(1+Real.log (held I t ω)))*(I.size (t+1) ω-I.filtered (t+1) ω) := by
  have h := step_release I t ω
  simp only [pot,tangent] at *
  nlinarith only [h]

theorem expected_step (I : Input Ω K) (hK : 1 ≤ K) (t : ℕ) :
    average I.weight (charge I t)+144*average I.weight (pot I (t+1)) ≤
      144*average I.weight (pot I t)+144*ell K*
      average I.weight (fun ω => |I.size (t+1) ω-I.filtered (t+1) ω|) := by
  have hf := I.filtering t (fun ω => 144*(-(1+Real.log (held I t ω)))) (by
    intro ω v hv
    dsimp only
    rw [held_measurable I t ω v hv])
  have hs := average_mono I.nonneg (potential_step I t)
  have he (ω : Ω) : 144*(-(1+Real.log (held I t ω)))*(I.size (t+1) ω-I.filtered (t+1) ω) ≤
      (144*ell K)*|I.size (t+1) ω-I.filtered (t+1) ω| := by
    have hl : (-(1+Real.log (held I t ω)))*(I.size (t+1) ω-I.filtered (t+1) ω) ≤
        ell K*|I.size (t+1) ω-I.filtered (t+1) ω| := by
      calc
        _ ≤ |(-(1+Real.log (held I t ω)))*(I.size (t+1) ω-I.filtered (t+1) ω)| := le_abs_self _
        _ ≤ _ := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (slope_bound K _ hK (held_range I t ω)) (abs_nonneg _)
    nlinarith
  have hb := average_mono I.nonneg he
  simp only [average_add,average_mul] at hs hb
  rw [hf] at hs
  linarith

theorem budget (I : Input Ω K) (hK : 1 ≤ K) (H : ℕ) :
    (∑ t ∈ Finset.range H, average I.weight (charge I t)) ≤
      144*ell K*(∑ t ∈ Finset.range H,
        average I.weight (fun ω => |I.size (t+1) ω-I.filtered (t+1) ω|))+288*K*(1+ell K) := by
  have ht : ∀ H, (∑ t ∈ Finset.range H, average I.weight (charge I t))+
      144*average I.weight (pot I H) ≤
      144*ell K*(∑ t ∈ Finset.range H,
        average I.weight (fun ω => |I.size (t+1) ω-I.filtered (t+1) ω|))+
          144*average I.weight (pot I 0) := by
    intro H
    induction H with
    | zero => simp
    | succ H ih =>
      have hs := expected_step I hK H
      rw [sum_range_succ,sum_range_succ]
      linarith
  have hr (t : ℕ) : |average I.weight (pot I t)| ≤ K*(1+ell K) := by
    calc
      _ ≤ ∑ ω, |I.weight ω*pot I t ω| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ ω, I.weight ω*(K*(1+ell K)) := sum_le_sum fun ω _ => by
        rw [abs_mul,abs_of_nonneg (I.nonneg ω)]
        exact mul_le_mul_of_nonneg_left (potential_bound I hK t ω) (I.nonneg ω)
      _ = _ := by rw [←sum_mul,I.total,one_mul]
  have h0 := (abs_le.mp (hr 0)).2
  have hH := (abs_le.mp (hr H)).1
  nlinarith [ht H]

end UniformKServer.KeySizeTracker

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_KeySizePosterior
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! The entropy size tracker instantiated by true finite hidden-count data.
Its drift estimate is conditional L1 contraction, never event-conditional. -/
noncomputable section
namespace UniformKServer.KeySizePosterior
open Finset ConditionalLaw RankTracking KeySizeTracker
open scoped Classical
variable {X Ω : Type*} [Fintype Ω] {k : ℕ}

def input (D : HiddenFlow.Data X Ω k) (N : ℕ → Ω → ℝ)
    (hN : ∀ t ω, N t ω ∈ Set.Icc 0 (k:ℝ)) : KeySizeTracker.Input Ω (k+1) where
  weight := D.weight
  nonneg := fun ω => (D.positive ω).le
  total := D.total
  filtration := D.filtration
  refines := D.refines
  size := fun t ω => 1+posterior D.weight (D.filtration t) (N t) ω
  filtered := fun t ω => 1+posterior D.weight (D.filtration t) (N (t-1)) ω
  range := by
    intro t ω
    have hn := posterior_nonneg (fun v => (D.positive v).le) (fun v => (hN t v).1) (D.filtration t) ω
    have hu : posterior D.weight (D.filtration t) (N t) ω ≤ k := by
      unfold posterior
      calc
        _ ≤ ∑ v, kernel D.weight (D.filtration t) ω v*(k:ℝ) := sum_le_sum fun v _ =>
          mul_le_mul_of_nonneg_left (hN t v).2 (kernel_nonneg (fun x => (D.positive x).le) _ _ _)
        _ = _ := by rw [←sum_mul,HiddenFlow.normalization D,one_mul]
    constructor <;> linarith
  measurable := by
    intro t ω v hv
    dsimp only
    rw [posterior_measurable _ _ _ ω v hv]
  filtering := by
    intro t a ha
    have hf := ConditionalLaw.filtering (fun v => (D.positive v).le) (D.filtration t)
      (D.filtration (t+1)) (D.refines t) a (N t) ha
    simpa only [Nat.add_sub_cancel,add_sub_add_left_eq_sub,average,mul_assoc] using hf

theorem drift (D : HiddenFlow.Data X Ω k) (N : ℕ → Ω → ℝ)
    (hN : ∀ t ω, N t ω ∈ Set.Icc 0 (k:ℝ)) (t : ℕ) :
    average D.weight (fun ω => |(input D N hN).size (t+1) ω-(input D N hN).filtered (t+1) ω|) ≤
    average D.weight (fun ω => |N (t+1) ω-N t ω|) := by
  simpa only [input,Nat.add_sub_cancel,add_sub_add_left_eq_sub,average] using
    expected_contraction (fun v => (D.positive v).le) (D.filtration (t+1)) (N (t+1)) (N t)

theorem budget (D : HiddenFlow.Data X Ω k) (N : ℕ → Ω → ℝ)
    (hN : ∀ t ω, N t ω ∈ Set.Icc 0 (k:ℝ)) (H : ℕ) :
    (∑ t ∈ range H, average D.weight (KeySizeTracker.charge (input D N hN) t)) ≤
      144*ell (k+1)*(∑ t ∈ range H, average D.weight (fun ω => |N (t+1) ω-N t ω|))+
      288*(k+1)*(1+ell (k+1)) := by
  have hk : (1:ℝ) ≤ k+1 := by linarith [Nat.cast_nonneg (α:=ℝ) k]
  have he : 0 ≤ ell (k+1) := by unfold ell; linarith [Real.log_nonneg hk]
  have hb := KeySizeTracker.budget (input D N hN) hk H
  have hd := sum_le_sum (fun t (_ : t ∈ range H) => drift D N hN t)
  have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ 144*ell (k+1) by positivity)
  exact hb.trans (add_le_add hm (le_refl _))

end UniformKServer.KeySizePosterior

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyRadius
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

/-! A finite exact realization of the uniform heavy-ball radius.  The same
finite signature records membership for every possible center. Thus selecting
a center by the input-driven schedule does not alter the radius distribution. -/
noncomputable section
namespace UniformKServer.HeavyRadius
open FiniteProbability
open scoped Classical
variable {X : Type*} [Fintype X] [MetricSpace X]

attribute [local instance] OAI.UniformKServer.HeavyRadius.pairDecEq
theorem separation (r : ℝ) (hr : 0 < r) (c x y : X) :
    (law r).expect (fun ω => if ω.val (c,x) != ω.val (c,y) then (1:ℝ) else 0) ≤ dist x y/(4*r) := by
  rw [law,FiniteThreshold.threshold_separation (probability r) (probability_bounds r)]
  exact probability_lipschitz r hr c x y

end UniformKServer.HeavyRadius

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavySeparation
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Physical separation by the actual disjoint heavy balls. No factor equal
to the number of records is lost: for a short edge there is at most one
possible boundary ball, and its single birth-coordinate marginal is uniform. -/
noncomputable section
namespace UniformKServer.HeavyRecords
open Finset FiniteProbability
open scoped Classical
variable {X Λ I : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] [Fintype I] {r : ℝ}

attribute [local instance] OAI.UniformKServer.HeavyRecords.pairDecEq
attribute [local instance] OAI.UniformKServer.HeavyRecords.indexDecEq
omit [Fintype X] in
theorem key_eq_iff (S : State X Λ r) (hr : 0 ≤ r) (x y : X) :
    key S x=key S y ↔ ∀ l, covers S l x ↔ covers S l y := by
  constructor
  · intro he l
    rw [←key_some S hr x l,←key_some S hr y l,he]
  · intro he
    cases hx : key S x with
    | none =>
      symm
      apply (key_none S y).mpr
      rintro ⟨l,hl⟩
      have := (key_some S hr x l).mpr ((he l).mpr hl)
      rw [hx] at this
      cases this
    | some l =>
      symm
      exact (key_some S hr y l).mpr ((he l).mp ((key_some S hr x l).mp hx))

omit [Fintype X] in
theorem key_ne_witness (S : State X Λ r) (hr : 0 ≤ r) (x y : X)
    (hne : key S x ≠ key S y) : ∃ l ∈ S.present, ¬(covers S l x ↔ covers S l y) := by
  have hh : ¬∀ l, covers S l x ↔ covers S l y := fun h => hne ((key_eq_iff S hr x y).mpr h)
  push Not at hh
  obtain ⟨l,hl⟩ := hh
  have hnot : ¬(covers S l x ↔ covers S l y) := by tauto
  refine ⟨l,?_,hnot⟩
  by_contra hn
  exact hnot (by simp only [covers,hn,false_and])

theorem static_separation (hr : 0 < r) (H : Finset X) (hH : HeavySchedule.Separated r H)
    (birth : X → I) (S : (I → HeavyRadius.Sample (X:=X) r) → State X Λ r)
    (hcenters : ∀ ω, centers (S ω)=H)
    (hrad : ∀ ω l, l ∈ (S ω).present →
      (S ω).radius l=HeavyRadius.radius r (ω (birth ((S ω).center l)))) (x y : X) :
    (Law.pi (fun _ : I => HeavyRadius.law (X:=X) r)).expect
      (fun ω => if key (S ω) x ≠ key (S ω) y then (1:ℝ) else 0) ≤ dist x y/r := by
  let P := Law.pi (fun _ : I => HeavyRadius.law (X:=X) r)
  by_cases hd : dist x y < r
  · by_cases he : ∃ c ∈ H, dist c x ≤ 21*r
    · obtain ⟨c,hc,hcx⟩ := he
      have hb : ∀ ω, (if key (S ω) x ≠ key (S ω) y then (1:ℝ) else 0) ≤
          if (ω (birth c)).val (c,x) != (ω (birth c)).val (c,y) then 1 else 0 := by
        intro ω
        by_cases hk : key (S ω) x ≠ key (S ω) y
        · obtain ⟨l,hl,hm⟩ := key_ne_witness (S ω) hr.le x y hk
          have hc' : (S ω).center l ∈ H := by rw [←hcenters ω]; exact mem_image.mpr ⟨l,hl,rfl⟩
          have hnear := near_boundary (S ω) hr.le x y hd l hl hm
          have hcen : (S ω).center l=c := by
            apply HeavySchedule.intersect_unique r hr.le H hH x _ _ hc' hc <;>
              rw [dist_comm] <;> linarith
          have hcov (z : X) : covers (S ω) l z ↔ (ω (birth c)).val (c,z)=true := by
            rw [HeavyRadius.covers r hr]
            simp only [covers,hl,true_and,hrad ω l hl,hcen]
          have hbits : (ω (birth c)).val (c,x) ≠ (ω (birth c)).val (c,y) := by
            intro heq
            apply hm
            rw [hcov x,hcov y,heq]
          simp only [ite_eq_left hk]
          cases hx : (ω (birth c)).val (c,x) <;> cases hy : (ω (birth c)).val (c,y) <;> simp_all
        · simp only [ite_eq_right hk]
          split_ifs <;> norm_num
      have hh := P.expect_mono _ _ hb
      have hmarg := Law.expect_pi_coordinate (fun _ : I => HeavyRadius.law (X:=X) r) (birth c)
        (fun ω => if ω.val (c,x) != ω.val (c,y) then (1:ℝ) else 0)
      change P.expect _ = _ at hmarg
      rw [hmarg] at hh
      apply (hh.trans (HeavyRadius.separation r hr c x y)).trans
      exact div_le_div_of_nonneg_left dist_nonneg hr (by linarith)
    · have hz : ∀ ω, key (S ω) x=key (S ω) y := by
        intro ω
        by_contra hk
        obtain ⟨l,hl,hm⟩ := key_ne_witness (S ω) hr.le x y hk
        apply he
        refine ⟨(S ω).center l,?_,near_boundary (S ω) hr.le x y hd l hl hm⟩
        rw [←hcenters ω]
        exact mem_image.mpr ⟨l,hl,rfl⟩
      have heq : P.expect (fun ω => if key (S ω) x ≠ key (S ω) y then (1:ℝ) else 0)=0 := by
        simp only [hz,ne_eq,not_true_eq_false,ite_false, if_false,P.expect_const]
      change P.expect _ ≤ _
      rw [heq]
      positivity
  · have hb : ∀ ω, (if key (S ω) x ≠ key (S ω) y then (1:ℝ) else 0) ≤ 1 := by
      intro ω; split_ifs <;> norm_num
    have hh := P.expect_mono _ _ hb
    rw [P.expect_const] at hh
    exact hh.trans ((le_div_iff₀ hr).mpr (by linarith))

end UniformKServer.HeavyRecords

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyTape
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                
section

/-! Every time slice of the same finite product tape, not a new resampling of
old balls. The slot universe remains independent of the analysis horizon. -/
noncomputable section
namespace UniformKServer.HeavyProcess
open Finset HeavyRecords FiniteProbability
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}

attribute [local instance] OAI.UniformKServer.HeavyProcess.tapePairDecEq
local instance tapeFinDecEq_rdc08a4_1 (N : ℕ) : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
theorem at_separation (a : X) (hr : 0 < r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (N t : ℕ) (ht : t≤N) (y z : X) :
    (Law.pi (fun _ : Fin N => HeavyRadius.law (X:=X) r)).expect
      (fun ω => if key (slice a hr.le hΛ h x N ω t) y≠key (slice a hr.le hΛ h x N ω t) z then (1:ℝ) else 0)
      ≤ dist y z/r := by
  by_cases hN : 0<N
  · let birth : X → Fin N := fun c => if hc : births r h x t c<N then ⟨births r h x t c,hc⟩ else ⟨0,hN⟩
    exact static_separation hr (HeavySchedule.centers r h x t) (HeavySchedule.centers_separated r h x t)
      birth (fun ω => slice a hr.le hΛ h x N ω t)
      (fun ω => run_centers a hr.le hΛ h x (radiusStream r N ω) (radiusStream_bounds r hr.le N ω) t)
      (fun ω l hl => at_radius a hr.le hΛ h x N hN t ht ω l hl) y z
  · have ht0 : t=0 := by omega
    subst t
    have he (ω : Fin N → HeavyRadius.Sample (X:=X) r) (p : X) :
        key (slice a hr.le hΛ h x N ω 0) p=none := by
      apply (key_none _ p).mpr
      simp only [slice,run,runPair,empty,covers,notMem_empty,false_and,exists_false,not_false_eq_true]
    simp only [he,ne_eq,not_true_eq_false,ite_false, if_false,Law.expect_const]
    positivity

end UniformKServer.HeavyProcess

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierSchedule
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! The literal insertion schedule. It inspects chronological ages, not
realized lifetimes, and is defined before any radius or lifetime tape. -/
noncomputable section
namespace UniformKServer.TierSchedule
open Finset ChronologicalRoster
open scoped Classical
variable {X : Type*} [MetricSpace X] {N : ℕ}

theorem young_next_subset (r : ℝ) (K A : ℕ) (q : Fin N → Prop) (c : Fin N → X) (n : Fin N) :
    young (run r K q c (n.val+1)) c r A ⊆ insert n (young (run r K q c n.val) c r A) := by
  rw [run,dite_eq_left n.isLt]
  split_ifs
  · exact young_insert_subset _ _ _ _ _
  · exact subset_insert _ _

end UniformKServer.TierSchedule

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CooldownLabels
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Fixed finite label pools with a full preceding-step cooldown. No historical
label is globally reserved: only current and preceding record sets are excluded. -/
noncomputable section
namespace UniformKServer.CooldownLabels
open Finset
open scoped Classical
variable {I : Type*} [DecidableEq I]

theorem injective (M : ℕ) (S : ℕ → Finset I) (birth : ℕ → Option I)
    (hS : ∀ t, (S t).card≤M) (hzero : S 0=∅)
    (hnext : ∀ t, S (t+1)⊆match birth t with | none => S t | some n => insert n (S t))
    (_hnew : ∀ t n, birth t=some n → n∉S t) (t : ℕ) :
    Set.InjOn (run M S birth t).label (S t) := by
  induction t with
  | zero => simp only [hzero,coe_empty,Set.injOn_empty]
  | succ t ih =>
    cases hb : birth t with
    | none =>
      rw [label_none M S birth t hb]
      apply ih.mono
      intro i hi
      have hs : S (t+1)⊆S t := by simpa only [hb] using hnext t
      exact hs hi
    | some n =>
      have hs : S (t+1)⊆insert n (S t) := by simpa only [hb] using hnext t
      have hf := label_new_fresh M S birth hS t n hb
      intro i hi j hj he
      have hi' := hs hi
      have hj' := hs hj
      by_cases hin : i=n
      · subst i
        by_contra hnj
        have hjs : j∈S t := (mem_insert.mp hj').resolve_left (Ne.symm hnj)
        have hje := label_old M S birth t n j hb (Ne.symm hnj)
        exact hf (mem_union_right _ (mem_image.mpr ⟨j,hjs,by rw [←hje,he]⟩))
      · have his : i∈S t := (mem_insert.mp hi').resolve_left hin
        by_cases hjn : j=n
        · subst j
          have hie := label_old M S birth t n i hb hin
          exact (hf (mem_union_right _ (mem_image.mpr ⟨i,his,by rw [←hie,he]⟩))).elim
        · apply ih his ((mem_insert.mp hj').resolve_left hjn)
          simpa only [label_old M S birth t n i hb hin,label_old M S birth t n j hb hjn] using he

theorem common_anchor (M : ℕ) (S : ℕ → Finset I) (birth : ℕ → Option I)
    (hS : ∀ t, (S t).card≤M) (hzero : S 0=∅)
    (hnext : ∀ t, S (t+1)⊆match birth t with | none => S t | some n => insert n (S t))
    (hnew : ∀ t n, birth t=some n → n∉S t)
    (t : ℕ) (i j : I) (hi : i∈S t) (hj : j∈S (t+1))
    (he : (run M S birth t).label i=(run M S birth (t+1)).label j) : i=j := by
  have hinj := injective M S birth hS hzero hnext hnew t
  cases hb : birth t with
  | none =>
    have hs : S (t+1)⊆S t := by simpa only [hb] using hnext t
    exact hinj hi (hs hj) (by simpa only [label_none M S birth t hb] using he)
  | some n =>
    have hs : S (t+1)⊆insert n (S t) := by simpa only [hb] using hnext t
    have hjn : j≠n := by
      intro h; subst j
      have hf := label_new_fresh M S birth hS t n hb
      exact hf (mem_union_right _ (mem_image.mpr ⟨i,hi,he⟩))
    apply hinj hi ((mem_insert.mp (hs hj)).resolve_left hjn)
    simpa only [label_old M S birth t n j hb hjn] using he

end UniformKServer.CooldownLabels

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierLabels
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Actual horizon/law independent pool sizes; labels remain reserved after a
record retires or becomes shadowed. All births are chronological identities. -/
noncomputable section
namespace UniformKServer.TierLabels
open Finset ChronologicalRoster
attribute [local instance] Classical.propDecidable
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

theorem reserved_card (r : ℝ) (hr : 0 ≤ r) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) :
    (reserved r K q c t).card≤Fintype.card X*K^2 := global_young_count _ c r hr _

omit [Fintype X] in
theorem reserved_next (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) :
    reserved r K q c (t+1)⊆match birth r K q c t with
      | none => reserved r K q c t
      | some n => insert n (reserved r K q c t) := by
  by_cases ht : t<N
  · let n : Fin N := ⟨t,ht⟩
    by_cases hn : TierSchedule.trigger r K (TierSchedule.run r K q c t) q c n
    · have hb : birth r K q c t=some n := by rw [birth,dite_eq_left ht,ite_eq_left hn]
      rw [hb]
      have hy := TierSchedule.young_next_subset r K (K^2) q c n
      intro i hi
      rcases mem_insert.mp (hy hi) with h|h
      · exact mem_insert.mpr (Or.inl h)
      · exact mem_insert_of_mem h
    · have hb : birth r K q c t=none := by rw [birth,dite_eq_left ht,ite_eq_right hn]
      have hr : TierSchedule.run r K q c (t+1)=TierSchedule.run r K q c t := by
        rw [TierSchedule.run,dite_eq_left ht,ite_eq_right hn]
      rw [hb]
      exact le_of_eq (congrArg (fun s => young s c r (K^2)) hr)
  · have hb : birth r K q c t=none := by rw [birth,dite_eq_right ht]
    have hr : TierSchedule.run r K q c (t+1)=TierSchedule.run r K q c t := by
      rw [TierSchedule.run,dite_eq_right ht]
    rw [hb]
    exact le_of_eq (congrArg (fun s => young s c r (K^2)) hr)

theorem injective (r : ℝ) (hr : 0 ≤ r) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) :
    Set.InjOn (labels r K q c t).label (reserved r K q c t) :=
  CooldownLabels.injective (Fintype.card X*K^2) (reserved r K q c) (birth r K q c) (reserved_card r hr K q c) (reserved_zero r K q c)
    (fun t => by
      cases hb : birth r K q c t <;> simpa only [hb] using reserved_next r K q c t)
    (birth_new r K q c) t

theorem common_record (r : ℝ) (hr : 0 ≤ r) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X)
    (t : ℕ) (i j : Fin N) (hi : i∈reserved r K q c t) (hj : j∈reserved r K q c (t+1))
    (he : (labels r K q c t).label i=(labels r K q c (t+1)).label j) : i=j :=
  CooldownLabels.common_anchor (Fintype.card X*K^2) (reserved r K q c) (birth r K q c) (reserved_card r hr K q c) (reserved_zero r K q c)
    (fun t => by
      cases hb : birth r K q c t <;> simpa only [hb] using reserved_next r K q c t)
    (birth_new r K q c) t i j hi hj he

end UniformKServer.TierLabels

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierLabeledKeys
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

noncomputable section
namespace UniformKServer.TierLabeledKeys
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

local instance pairDecEq_rdc08a4_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
theorem anchor_record (a : X) (r : ℝ) (hr : 0 ≤ r) (K : ℕ) (q : Fin N → Prop)
    (c : Fin N → X) (t : ℕ) (i : Fin N) (hi : i∈TierLabels.reserved r K q c t) :
    anchor a r K q c t ((TierLabels.labels r K q c t).label i)=c i := by
  have he : ∃ j∈TierLabels.reserved r K q c t,
      (TierLabels.labels r K q c t).label j=(TierLabels.labels r K q c t).label i := ⟨i,hi,rfl⟩
  rw [anchor,dite_eq_left he]
  have hc := Classical.choose_spec he
  rw [TierLabels.injective r hr K q c t hc.1 hi hc.2]

theorem covers (a : X) (r : ℝ) (hr : 0 < r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (q : Fin N → Prop) (c : Fin N → X)
    (t : ℕ) (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r)
    (p : X) (l : Slot X K) (hl : key r K q c t τ ω p=some l) :
    dist p (anchor a r K q c t l)≤2*r := by
  obtain ⟨i,hi,hkey,rfl⟩ := key_witness r K hK hq q c t τ ω p l hl
  rw [anchor_record a r hr.le K q c t i hi]
  exact TierKeyProcess.covers r hr K hK q c t τ ω p i hkey

theorem common_anchor (a : X) (r : ℝ) (hr : 0 ≤ r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (q : Fin N → Prop) (c : Fin N → X)
    (t : ℕ) (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r)
    (x y : X) (l : Slot X K) (hx : key r K q c t τ ω x=some l)
    (hy : key r K q c (t+1) τ ω y=some l) :
    anchor a r K q c t l=anchor a r K q c (t+1) l := by
  obtain ⟨i,hi,hxi,hli⟩ := key_witness r K hK hq q c t τ ω x l hx
  obtain ⟨j,hj,hyj,hlj⟩ := key_witness r K hK hq q c (t+1) τ ω y l hy
  have hij := TierLabels.common_record r hr K q c t i j hi hj (hli.trans hlj.symm)
  rw [←hli,anchor_record a r hr K q c t i hi,hli,←hlj,anchor_record a r hr K q c (t+1) j hj,hij]

end UniformKServer.TierLabeledKeys

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelMap
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section

/-! The literal level key: heavy precedence, then chronological tiers in their
fixed order, then singleton fallback. Its alphabet is fixed by the instance,
not by the finite law or horizon used to analyze the independent tape. -/
noncomputable section
namespace UniformKServer.LevelMap
open Finset FiniteProbability
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

namespace Data

local instance indexDecEq_rdc08a4_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
attribute [local instance] OAI.UniformKServer.LevelMap.tierDecEq
attribute [local instance] OAI.UniformKServer.LevelMap.pairDecEq
theorem tier_covers (D : Data X N H) (ω : Tape D) (t : ℕ) (i : Fin H) (p : X) (l : Label D)
    (hl : D.tierKey ω t i p=some l) : dist p (D.anchor ω t l)≤2*D.r := by
  obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp hl
  exact TierLabeledKeys.covers D.base D.r D.positive (D.K i) (D.two i) (D.quota i)
    (D.qualify i) D.center t (ω.2 i).1 (ω.2 i).2 p a ha

theorem covers (D : Data X N H) (is : List (Fin H)) (ω : Tape D) (t : ℕ) (p : X) :
    dist p (D.anchor ω t (D.key is ω t p))≤20*D.r := by
  cases hh : D.heavyKey ω t p with
  | some l =>
    simpa only [key,hh,Option.some_or,Option.getD_some] using heavy_covers D ω t p l hh
  | none =>
    cases ht : FirstStructure.first is (fun i => D.tierKey ω t i p) with
    | none => simp only [key,hh,Option.none_or,ht,Option.getD_none,anchor,dist_self]; exact mul_nonneg (by norm_num) D.positive.le
    | some l =>
      obtain ⟨i,hi,hk⟩ := first_witness is _ l ht
      have hc := tier_covers D ω t i p l hk
      simp only [key,hh,Option.none_or,ht,Option.getD_some]
      linarith [D.positive]

theorem diameter (D : Data X N H) (is : List (Fin H)) (ω : Tape D) (t : ℕ) (p q : X)
    (he : D.key is ω t p=D.key is ω t q) : dist p q≤40*D.r := by
  have hp := covers D is ω t p
  have hq := covers D is ω t q
  rw [←he] at hq
  have ht := dist_triangle p (D.anchor ω t (D.key is ω t p)) q
  rw [dist_comm (D.anchor ω t (D.key is ω t p)) q] at ht
  linarith

end Data
end UniformKServer.LevelMap

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelSeparation
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

local instance indexDecEq_rdc08a4_2 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
attribute [local instance] OAI.UniformKServer.LevelMap.Data.tierDecEq
attribute [local instance] OAI.UniformKServer.LevelMap.Data.pairDecEq
theorem heavy_separation (D : Data X N H) (t : ℕ) (ht : t≤N) (p q : X) :
    D.law.expect (fun ω => indicator (D.heavyKey ω t p) (D.heavyKey ω t q))≤dist p q/D.r := by
  have hm := D.law.expect_mono _ _ (fun ω =>
    indicator_map (fun o => o.map (Sum.inl : HeavySlot X → Label D))
      (HeavyRecords.key (D.heavyState ω.1 t) p) (HeavyRecords.key (D.heavyState ω.1 t) q))
  change D.law.expect _≤D.law.expect (fun ω => indicator
    (HeavyRecords.key (D.heavyState ω.1 t) p) (HeavyRecords.key (D.heavyState ω.1 t) q)) at hm
  apply hm.trans
  rw [law,Law.expect_prod _ _ (fun a _ => indicator (HeavyRecords.key (D.heavyState a t) p) (HeavyRecords.key (D.heavyState a t) q))]
  simp only [Law.expect_const]
  have he := HeavyProcess.at_separation (Λ:=HeavySlot X) D.base D.positive (by simp [HeavySlot]) D.heavyFlag D.point N t ht p q
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply Law.expect_congr
  intro ω
  by_cases hh : HeavyRecords.key (D.heavyState ω t) p=HeavyRecords.key (D.heavyState ω t) q
  · simp only [indicator,heavyState] at hh ⊢
    simp only [hh,ne_eq,not_true_eq_false,ite_false, if_false,ite_true, if_true]
  · simp only [indicator,heavyState] at hh ⊢
    simp only [hh,ne_eq,not_false_eq_true,ite_true, if_true,ite_false, if_false]

/-- Only the prefix through a qualifying tier is charged. In particular this
is not the number of levels times a worst-case tier coefficient. -/
theorem prefix_separation (D : Data X N H) (is js : List (Fin H)) (n : Fin N)
    (hq : ∃ i∈is, D.qualify i n) (p : X) (hp : dist (D.center n) p<D.r/4) :
    D.law.expect (fun ω => indicator (D.key (is++js) ω (n.val+1) (D.center n))
      (D.key (is++js) ω (n.val+1) p))≤dist (D.center n) p/D.r+
        (is.map (fun i => 2*Real.log (1+(D.K i:ℝ)^2)*dist (D.center n) p/D.r)).sum := by
  have hm := D.law.expect_mono _ _ (fun ω => priority_bound D is js ω (n.val+1) (D.center n) p (by
    obtain ⟨i,hi,hqual⟩ := hq
    exact ⟨i,hi,tier_coverage D n i hqual ω⟩))
  rw [Law.expect_add,expect_list_sum] at hm
  apply hm.trans
  apply add_le_add (heavy_separation D (n.val+1) (by omega) (D.center n) p)
  clear hm hq
  induction is with
  | nil => simp only [List.map_nil,List.sum_nil,le_refl]
  | cons i is ih =>
    simp only [List.map_cons,List.sum_cons]
    exact add_le_add (tier_separation D (n.val+1) i (D.center n) p hp) ih

end UniformKServer.LevelMap.Data

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_DyadicTiers
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

/-! The source's dyadic tiers, including the minimal last tier and the sharp
prefix/unqualified sums. These coefficients are summed before summing scales. -/
noncomputable section
namespace UniformKServer.DyadicTiers
open Finset
open scoped Classical

theorem prefix_sum (L : ℝ) : (∑ i∈range (last L+1), value i)≤4*max 1 L := by
  rw [sum_exact,pow_succ]
  have h := last_bound L
  dsimp only [value] at h
  linarith

end UniformKServer.DyadicTiers

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionLevel
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Instantiation of the level construction from the true post-request GeometricMass.mass.
Tier qualifications are precisely the source exponential GeometricMass.mass test. -/
noncomputable section
namespace UniformKServer.PartitionLevel
open Finset FiniteProbability FirstStructure GeometricMass
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

namespace Input

local instance pairDecEq_rdc08a4_2 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance indexDecEq_rdc08a4_3 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
theorem localLog_bound (I : Input X N) (n : Fin N) : I.localLog n ≤ Real.log I.k := by
  have hi := I.inner_one n
  have hip : 0< GeometricMass.mass (I.μ n) (I.center n) (I.P.gammaL*I.r) := by linarith
  have ho := (mass_total (I.μ n) (I.μ_nonneg n) (I.center n) (20480000*I.r)).trans (I.μ_total n)
  apply Real.log_le_log (div_pos (I.outer_pos n) hip)
  apply (div_le_iff₀ hip).mpr
  have hk : (0:ℝ) ≤ I.k := Nat.cast_nonneg _
  nlinarith

def cutoff (I : Input X N) (n : Fin N) : ℕ := DyadicTiers.last (I.localLog n)+1

theorem cutoff_le (I : Input X N) (n : Fin N) : I.cutoff n ≤ I.height := by
  exact Nat.add_le_add_right (DyadicTiers.last_mono _ _ (I.localLog_bound n)) 1

theorem prefix_exists (I : Input X N) (n : Fin N) :
    ∃ i∈I.order.take (I.cutoff n), I.data.qualify i n := by
  let j : Fin (I.cutoff n) := ⟨DyadicTiers.last (I.localLog n),by simp [cutoff]⟩
  let i := j.castLE (I.cutoff_le n)
  refine ⟨i,?_,?_⟩
  · rw [order,←Fin.ofFn_take_eq_take_ofFn (I.cutoff_le n)]
    exact List.mem_ofFn.mpr ⟨j,rfl⟩
  · apply (I.qualification n i).mpr
    exact DyadicTiers.last_ge _

theorem prefix_sum (I : Input X N) (n : Fin N) :
    ((I.order.take (I.cutoff n)).map (fun i => DyadicTiers.value i.val)).sum ≤ 4*max 1 (I.localLog n) := by
  rw [order,List.map_take,List.map_ofFn,←Fin.ofFn_take_eq_take_ofFn (I.cutoff_le n),List.sum_ofFn]
  change (∑ j : Fin (I.cutoff n), DyadicTiers.value j.val) ≤ _
  rw [Fin.sum_univ_eq_sum_range]
  exact DyadicTiers.prefix_sum _

end Input
end UniformKServer.PartitionLevel

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionSeparation
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                          
section

/-! The actual one-level final-map separation estimate with its local mass
ratio, and the exact zero contribution at large heavy levels. -/
noncomputable section
namespace UniformKServer.PartitionLevel.Input
open Finset FiniteProbability FirstStructure GeometricMass
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

attribute [local instance] OAI.UniformKServer.PartitionLevel.Input.sepFinDecEq
local instance sepPairDecEq_rdc08a4_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
theorem log_prefix (I : Input X N) (n : Fin N) :
    ((I.order.take (I.cutoff n)).map (fun i => 2*Real.log (1+(I.data.K i:ℝ)^2))).sum ≤
      (16*I.C+32)*max 1 (I.localLog n) := by
  have hb (is : List (Fin I.height)) :
      (is.map (fun i => 2*Real.log (1+(I.data.K i:ℝ)^2))).sum ≤
        (4*I.C+8)*(is.map (fun i => DyadicTiers.value i.val)).sum := by
    induction is with
    | nil => simp
    | cons i is ih =>
      simp only [List.map_cons,List.sum_cons,mul_add]
      apply add_le_add _ ih
      have h := TierParameters.radius_parameter I.C (DyadicTiers.value i.val)
        I.C_one (DyadicTiers.one_le_value i.val)
      change 2*Real.log (1+(TierParameters.cutoff I.C (DyadicTiers.value i.val):ℝ)^2) ≤ _
      nlinarith only [h]
  have hp := mul_le_mul_of_nonneg_left (I.prefix_sum n) (by linarith [I.C_one] : 0 ≤ 4*I.C+8)
  exact (hb _).trans (by nlinarith only [hp])

theorem short_separation (I : Input X N) (n : Fin N) (p : X)
    (hp : dist (I.center n) p<I.r/4) :
    I.r*I.separation n p ≤ (16*I.C+33)*(1+I.localLog n)*dist (I.center n) p := by
  have h := LevelMap.Data.prefix_separation I.data (I.order.take (I.cutoff n))
    (I.order.drop (I.cutoff n)) n (I.prefix_exists n) p hp
  rw [List.take_append_drop] at h
  have he (is : List (Fin I.height)) :
      (is.map (fun i => 2*Real.log (1+(I.data.K i:ℝ)^2)*dist (I.center n) p/I.r)).sum=
        (is.map (fun i => 2*Real.log (1+(I.data.K i:ℝ)^2))).sum*(dist (I.center n) p/I.r) := by
    induction is with
    | nil => simp
    | cons i is ih => simp only [List.map_cons,List.sum_cons,ih] <;> ring
  change I.separation n p ≤ dist (I.center n) p/I.r+
    ((I.order.take (I.cutoff n)).map (fun i => 2*Real.log (1+(I.data.K i:ℝ)^2)*dist (I.center n) p/I.r)).sum at h
  rw [he] at h
  have hratio : 0 ≤ dist (I.center n) p/I.r := div_nonneg dist_nonneg I.r_pos.le
  have hb := mul_le_mul_of_nonneg_right (I.log_prefix n) hratio
  have hmax : max 1 (I.localLog n) ≤ 1+I.localLog n := by
    exact max_le (by linarith [I.localLog_nonneg n]) (by linarith)
  have hc : 0 ≤ 16*I.C+32 := by linarith [I.C_one]
  have hg := mul_le_mul_of_nonneg_left hmax hc
  have hcoef : 1+(16*I.C+32)*max 1 (I.localLog n) ≤ (16*I.C+33)*(1+I.localLog n) := by
    nlinarith only [hg,I.localLog_nonneg n]
  have hprod := mul_le_mul_of_nonneg_right hcoef hratio
  have hbound : I.separation n p ≤ ((16*I.C+33)*(1+I.localLog n)*dist (I.center n) p)/I.r := by
    change I.separation n p ≤ _ at h
    calc
      _ ≤ dist (I.center n) p/I.r+
        ((I.order.take (I.cutoff n)).map (fun i => 2*Real.log (1+(I.data.K i:ℝ)^2))).sum*
        (dist (I.center n) p/I.r) := h
      _ ≤ dist (I.center n) p/I.r+(16*I.C+32)*max 1 (I.localLog n)*(dist (I.center n) p/I.r) := by linarith only [hb]
      _ = (1+(16*I.C+32)*max 1 (I.localLog n))*(dist (I.center n) p/I.r) := by ring
      _ ≤ (16*I.C+33)*(1+I.localLog n)*(dist (I.center n) p/I.r) := hprod
      _ = _ := by ring
  have hfinal := (le_div_iff₀ I.r_pos).mp hbound
  nlinarith only [hfinal]

end UniformKServer.PartitionLevel.Input

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionScales
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Final-map separation summed over geometric scales. The additive one in
the level estimate is charged only at nonheavy scales, not at every scale. -/
noncomputable section
namespace UniformKServer.PartitionScales
open Finset FiniteProbability FirstStructure GeometricMass
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N J : ℕ}

namespace Input

theorem separation (I : Input X N J) (n : Fin N) (p : X) :
    (∑ j∈range J, (I.level j).r*(I.level j).separation n p) ≤
      I.coefficient*(1+Real.log I.k)*dist (I.center n) p := by
  let d := dist (I.center n) p
  let A := 16*I.C+33
  have hd : 0 ≤ d := dist_nonneg
  have hA : 0 ≤ A := by dsimp [A] <;> linarith [I.C_one]
  have hr (j : ℕ) : 0<(I.level j).r := (I.level j).r_pos
  have hL (j : ℕ) : 0 ≤ (I.level j).localLog n := (I.level j).localLog_nonneg n
  have hp (j : ℕ) : (I.level j).r*(I.level j).separation n p ≤
      (if (I.level j).r ≤ 4*d then (I.level j).r else 0)+
      A*d*((if I.isNonheavy n j then 1 else 0)+(I.level j).localLog n) := by
    by_cases hs : (I.level j).r ≤ 4*d
    · rw [ite_eq_left hs]
      have h := mul_le_mul_of_nonneg_left ((I.level j).separation_le_one n p) (hr j).le
      have hnn : 0 ≤ (if I.isNonheavy n j then (1:ℝ) else 0)+(I.level j).localLog n := by
        split_ifs <;> linarith [hL j]
      nlinarith only [h,mul_nonneg (mul_nonneg hA hd) hnn]
    · rw [ite_eq_right hs,zero_add]
      have hshort : d<(I.level j).r/4 := by linarith
      by_cases hn : I.isNonheavy n j
      · rw [ite_eq_left hn]
        have h := (I.level j).short_separation n p hshort
        change (I.level j).r*(I.level j).separation n p ≤ A*(1+(I.level j).localLog n)*d at h
        calc
          _ ≤ A*(1+(I.level j).localLog n)*d := h
          _ = _ := by ring
      · rw [ite_eq_right hn]
        have hh : (I.level j).data.heavy n := by
          exact not_not.mp (fun h => hn ((I.not_heavy n j).mpr h))
        have hz := (I.level j).heavy_zero n p hh (by change d ≤ _; nlinarith only [hshort,(hr j).le])
        rw [hz,mul_zero,zero_add]
        exact mul_nonneg (mul_nonneg hA hd) (hL j)
  have hsum := sum_le_sum (s:=range J) (fun j _ => hp j)
  rw [sum_add_distrib,←mul_sum,sum_add_distrib] at hsum
  have hcount : (∑ j∈range J, if I.isNonheavy n j then (1:ℝ) else 0)=
      ((range J).filter (I.isNonheavy n)).card := by
    rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one]
  rw [hcount] at hsum
  have hsmall : (∑ j∈range J, if (I.level j).r ≤ 4*d then (I.level j).r else 0) ≤ 8*d := by
    have hc := SmallScales.small (I.R*I.q) I.q (4*d) (mul_pos I.R_pos I.q_pos).le I.q_pos.le
      (by linarith [I.q_small]) (by positivity) J
    have he (j : ℕ) : (I.level j).r=(I.R*I.q)*I.q^j := by dsimp [level,radius]; rw [pow_succ]; ring
    simp only [he]
    apply hc.trans
    apply (div_le_iff₀ (by linarith [I.q_small] : 0<1-I.q)).mpr
    nlinarith [I.q_small]
  have hlog : 0 ≤ Real.log I.k := Real.log_nonneg (by exact_mod_cast (show 1 ≤ I.k from le_trans (by decide) I.two))
  have hdelta : 0<Real.log (1+I.P.deltaH) := Real.log_pos (by linarith [I.P.deltaH_pos])
  have htot := add_le_add (I.nonheavy_count n) (I.log_sum n)
  have hmul := mul_le_mul_of_nonneg_left htot (mul_nonneg hA hd)
  have hz : 0 ≤ A*(1+1/Real.log (1+I.P.deltaH))*d := by positivity
  change _ ≤ I.coefficient*(1+Real.log I.k)*d
  calc
    _ ≤ 8*d+A*d*(Real.log I.k/Real.log (1+I.P.deltaH)+Real.log I.k) := by linarith only [hsum,hsmall,hmul]
    _ ≤ I.coefficient*(1+Real.log I.k)*d := by
      dsimp [coefficient,A] at *
      have he : (8+(16*I.C+33)*(1+1/Real.log (1+I.P.deltaH)))*(1+Real.log I.k)*d-
          (8*d+(16*I.C+33)*d*(Real.log I.k/Real.log (1+I.P.deltaH)+Real.log I.k))=
          8*d*Real.log I.k+(16*I.C+33)*(1+1/Real.log (1+I.P.deltaH))*d := by ring
      have hn : 0 ≤ 8*d*Real.log I.k := by positivity
      linarith only [he,hn,hz]

end Input
end UniformKServer.PartitionScales

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualPartitions
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! The actual true-posterior partition, on every positive finite hidden law.
All inputs are the real post-request counts, not a fitted proxy mass. -/
noncomputable section
namespace UniformKServer.ActualPartitions
open Finset
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

namespace Config

theorem separation (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω : Ω) (n : Fin N) (p : X) :
    (∑ j∈range J, ((A.input (N:=N) (J:=J) D hk ω).level j).r*((A.input (N:=N) (J:=J) D hk ω).level j).separation n p)≤
      (A.input (N:=N) (J:=J) D hk ω).coefficient*(1+Real.log k)*dist (D.request n.val ω) p :=
  (A.input (N:=N) (J:=J) D hk ω).separation n p

end Config
end UniformKServer.ActualPartitions

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SideParameterChanges
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                           
section

/-! Prepared parameter jumps charged only to changed size coordinates (§04).
 Constants are independent of the number of children and of the smallest size. -/
noncomputable section
namespace UniformKServer.SideParameterChanges
open Finset UniformKServer.AdaptiveSide
open scoped Classical
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem same_sizes {p q : Config ι} (hp : valid p) (hq : valid q)
    (hA : p.A=q.A) (hl : p.ell=q.ell) (hc : p.cw=q.cw) (i : ι)
    (hs : size p i=size q i) : theta p i=theta q i ∧ offset p i=offset q i := by
  by_cases hi : i ∈ p.active
  · have hj : i ∈ q.active := by
      by_contra hn
      have he : p.a ⟨i,hi⟩=0 := by
        simpa [size,DomainTransport.extend,hi,hn] using hs
      linarith [(hp.2.2.2.2.1 ⟨i,hi⟩).1]
    have ha : p.a ⟨i,hi⟩=q.a ⟨i,hj⟩ := by
      simpa [size,DomainTransport.extend,hi,hj] using hs
    simp only [theta,offset,DomainTransport.extend,hi,hj,dite_true,ha,hA,hl,hc,and_self]
  · have hj : i ∉ q.active := by
      intro hj
      have he : 0=q.a ⟨i,hj⟩ := by
        simpa [size,DomainTransport.extend,hi,hj] using hs
      linarith [(hq.2.2.2.2.1 ⟨i,hj⟩).1]
    simp [theta,offset,DomainTransport.extend,hi,hj]

omit [Fintype ι] in
theorem coordinate_bound_all {p : Config ι} (hp : valid p) (i : ι) {w B D : ℝ}
    (hw : 0 ≤ w) (hwW : w ≤ 11) :
    |SideTracker.coordinate p.b (theta p i) (offset p i) 28 B D w| ≤
      slope p*(|D| *w+|B|) := by
  by_cases hi : i ∈ p.active
  · exact coordinate_bound hp ⟨i,hi⟩ hw hwW
  · simp only [theta,offset,DomainTransport.extend,hi,dite_false]
    simp only [SideTracker.coordinate,div_zero,mul_zero,zero_mul,add_zero,sub_zero,zero_div,abs_zero]
    exact mul_nonneg (slope_nonneg hp) (add_nonneg (mul_nonneg (abs_nonneg D) hw) (abs_nonneg B))

theorem parameter_jump {p q : Config ι} (hp : valid p) (hq : valid q)
    (hA : p.A=q.A) (hl : p.ell=q.ell) (hc : p.cw=q.cw) (hb : p.b=q.b)
    (B w : ι → ℝ) {D : ℝ} (hD : 0 ≤ D) (hB : ∀ i, 0 ≤ B i)
    (hw : DomainTransport.domain q.active 11 w)
    (hprep : ∀ i, D*w i ≤ 5*B i) :
    |potential q B D w-potential p B D w| ≤
      6*(slope p+slope q)*(∑ i, if size p i=size q i then 0 else B i) := by
  unfold potential SideTracker.potential
  rw [←sum_sub_distrib,mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  by_cases hs : size p i=size q i
  · obtain ⟨ht,hz⟩ := same_sizes hp hq hA hl hc i hs
    simp only [ite_eq_left hs,hb,ht,hz,sub_self,abs_zero,mul_zero,le_refl]
  · rw [ite_eq_right hs]
    have hp' := coordinate_bound_all hp i (hw.1 i) (coordinate_le_sum hw i) (B:=B i) (D:=D)
    have hq' := coordinate_bound_all hq i (hw.1 i) (coordinate_le_sum hw i) (B:=B i) (D:=D)
    rw [abs_of_nonneg hD,abs_of_nonneg (hB i)] at hp' hq'
    have hp'' := mul_le_mul_of_nonneg_left (hprep i) (slope_nonneg hp)
    have hq'' := mul_le_mul_of_nonneg_left (hprep i) (slope_nonneg hq)
    exact (abs_sub _ _).trans (by nlinarith)

omit [Fintype ι] in
theorem prepared_upper {p : Config ι} (hp : valid p) (B w : ι → ℝ) (D : ℝ)
    (hB : ∀ i, 0 ≤ B i) (hf : ∀ i, D*w i ≤ (p.b+theta p i)*B i) :
    ∀ i, D*w i ≤ 5*B i := by
  intro i
  have hθ : theta p i ≤ 1 := by
    by_cases hi : i ∈ p.active
    · exact theta_le hp ⟨i,hi⟩
    · rw [theta,DomainTransport.extend_supported _ _ i hi]; norm_num
  exact (hf i).trans (mul_le_mul_of_nonneg_right (by linarith [hp.2.2.2.1]) (hB i))

end UniformKServer.SideParameterChanges

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochSide
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                
section

/-! Exact side configuration of a marked held-vector epoch. An unmarked
star has the actual empty side domain. -/
noncomputable section
namespace UniformKServer.EpochSide
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem mem {a : ι → ℝ} {s : EpochGeometry.State ι} {i : ι} (hi : i ∈ active a s) :
    0 < a i ∧ EpochGeometry.dominant s ≠ some i := by
  unfold active at hi
  cases ho : EpochGeometry.dominant s with
  | none => simp [ho] at hi
  | some o =>
    rw [ho] at hi
    obtain ⟨hne,ha⟩ := mem_erase.mp hi
    exact ⟨EpochParameters.mem_active.mp ha,by simpa only [ho,ne_eq,Option.some.injEq] using hne.symm⟩

theorem valid {a : ι → ℝ} {s : EpochGeometry.State ι} (hs : EpochGeometry.valid a s)
    {ell cw b : ℝ} (hl : 1 ≤ ell) (hcw : 0 < cw) (hc : cw*50000 ≤ 1)
    (hb : 0 < b) (hb4 : b ≤ 4)
    (hh : ∀ i : active a s, SideParameters.height (EpochGeometry.total s.base) (a i) ≤ 50000*ell) :
    AdaptiveSide.valid (config a s ell cw b) := by
  refine ⟨hl,hcw,hb,hb4,?_,?_⟩
  · intro i
    have hi := mem i.property
    exact ⟨hi.1,(EpochGeometry.regular_size hs hi.2).trans
      (by change (86/100:ℝ)*EpochGeometry.total s.base ≤ EpochGeometry.total s.base; nlinarith [EpochGeometry.total_nonneg hs.1])⟩
  · intro i
    exact EpochAlpha.eta_bound hcw (by change 0 < ell; linarith) hc (hh i)

theorem size_formula {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (s : EpochGeometry.State ι)
    (ell cw b : ℝ) (i : ι) : SideParameterChanges.size (config a s ell cw b) i =
      match EpochGeometry.dominant s with
      | none => 0
      | some o => if i=o then 0 else a i := by
  unfold SideParameterChanges.size DomainTransport.extend config active
  dsimp only
  cases ho : EpochGeometry.dominant s with
  | none => simp
  | some o =>
    by_cases he : i=o
    · simp [he]
    · by_cases hp : 0 < a i
      · simp [he,EpochParameters.mem_active.mpr hp]
      · have hz : a i=0 := le_antisymm (le_of_not_gt hp) (ha i)
        simp [hz,he]

theorem size_same {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    {s r : EpochGeometry.State ι} (he : s.base=r.base) (ell cw v v' : ℝ)
    {i : ι} (hi : a i=b i) :
    SideParameterChanges.size (config a s ell cw v) i=SideParameterChanges.size (config b r ell cw v') i := by
  rw [size_formula ha,size_formula hb,EpochAlphaStatic.dominant_base he]
  cases EpochGeometry.dominant r <;> simp only [hi]

def param (a : ℕ → ι → ℝ) (p : ℕ → Bool) (ell cw : ℝ) (b : ℕ → ℝ) (t : ℕ) : AdaptiveSide.Config ι :=
  config (a t) (EpochGeometry.schedule a p t) ell cw (b t)

theorem schedule_valid {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (k : ℕ) {cw : ℝ} (hcw : 0 < cw) (hc : cw*50000 ≤ 1)
    (b : ℕ → ℝ) (hb : ∀ t, 0 < b t ∧ b t ≤ 4)
    (hm : ∀ t, EpochGeometry.total (a t) ≤ 2*k)
    (hmin : ∀ t i, 0 < a t i → (9/100000:ℝ) ≤ a t i) (t : ℕ) :
    AdaptiveSide.valid (param a p (EpochAlpha.ell k) cw b t) := by
  have hs := EpochGeometry.schedule_valid ha p t
  apply valid hs (EpochAlpha.ell_one k) hcw hc (hb t).1 (hb t).2
  intro i
  have hi := (mem i.property).1
  exact EpochAlpha.height_upper (EpochParameters.active_total_pos hs hi)
    (EpochAlphaSchedule.base_bound p hm t) (hmin t i hi)

end UniformKServer.EpochSide

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochOutputParameters
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                            
section

/-! Evaluation of the actual epoch proportion parameters in the feasibility
inequalities.  All formulas use the persistent vector epoch, and retain the
zero-side/singleton case. -/
noncomputable section
namespace UniformKServer.EpochOutputParameters
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem side_sum_bound {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) (ha : ∀ i, 0 ≤ a i)
    {ell cw : ℝ} (hl : 0 < ell) (hc : 0 ≤ cw) (b : ℝ)
    (o : ι) (ho : EpochGeometry.dominant s=some o) {U : ℝ}
    (hU : EpochParameters.sideReference a o U) :
    (∑ i ∈ univ.erase o, AdaptiveSide.theta (EpochSide.config a s ell cw b) i *
        AdaptiveSide.offset (EpochSide.config a s ell cw b) i) ≤
      (1001/1000)*cw/ell*(U/EpochGeometry.total s.base) := by
  rw [side_sum hs ha ell cw b o ho]
  have hp := (EpochGeometry.dominant_spec ho).1
  have h := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hU.2.2 hp.le)
    (div_nonneg hc hl.le)
  calc
    _ ≤ cw/ell*((1001/1000)*U/EpochGeometry.total s.base) := h
    _ = _ := by ring

end UniformKServer.EpochOutputParameters

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FineVariation
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Fine endpoint movement is charged once, without the logarithmic weight
of the proportion potentials. Trackers continue through every epoch. -/
noncomputable section
namespace UniformKServer.FineVariation
open Finset RankFunctions RankData RankTracking FlexEstimates CoarseData
open scoped Classical
variable {Ω A : Type*} [Fintype Ω] [Fintype A]

theorem flex_step (I : A → Input Ω) {β : ℝ} (hβ : allowed β) (ξ : ℝ) (t : ℕ) (ω : Ω) :
    |estimateFlex I β ξ (t+1) ω-estimateFlex I β ξ t ω| ≤
      endpointVariation I ξ t ω+coreChange I t ω := by
  unfold estimateFlex
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  unfold endpointVariation coreChange
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro a _
  have hm := masked_noncore (core (I a) t ω) (core (I a) (t+1) ω)
    (term_range (I a) hβ ξ t ω) (term_range (I a) hβ ξ (t+1) ω)
  have ht := FineCaps.interpolation_variation (a:=estimate (I a) (rank 3) ξ t ω)
    (b:=estimate (I a) (rank (3+1/100)) ξ t ω)
    (A:=estimate (I a) (rank 3) ξ (t+1) ω)
    (B:=estimate (I a) (rank (3+1/100)) ξ (t+1) ω) (mix_range hβ)
  apply hm.trans
  change |term (I a) β ξ (t+1) ω-term (I a) β ξ t ω| + _ ≤ _
  unfold term
  exact add_le_add ht le_rfl

theorem core_step (I : A → Input Ω) (t : ℕ) (ω : Ω) :
    |coreCount (fun a => core (I a) (t+1) ω)-coreCount (fun a => core (I a) t ω)| ≤
      coreChange I t ω := by
  unfold coreCount
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro a _
  cases ha : core (I a) t ω <;> cases hb : core (I a) (t+1) ω <;> simp [ha,hb]

theorem endpoint_budget (I : A → Input Ω) (w : Ω → ℝ) (hi : ∀ a, (I a).weight=w)
    {ξ : ℝ} (hξ : 0 < ξ) (hξ' : ξ < 1/2) (H : ℕ) :
    (∑ t ∈ range H, average w (endpointVariation I ξ t)) ≤
      (160/ξ)*(totalDrift I H+Fintype.card A) := by
  have he (β : ℝ) (hβ : allowed β) :
      (∑ a, ∑ t ∈ range H, average w (fun ω =>
        |estimate (I a) (rank β) ξ (t+1) ω-estimate (I a) (rank β) ξ t ω|)) ≤
      (80/ξ)*(totalDrift I H+Fintype.card A) := by
    calc
      _ ≤ ∑ a, (80/ξ)*(driftBudget (I a) H+1) := by
        apply sum_le_sum
        intro a _
        rw [←hi a]
        have h := (relative_tracker (I a) (rank β) ξ 4 hξ hξ' (by norm_num)
          (fun _ _ => rank_nonneg hβ) (fun _ hp _ hq => sqrt_rank_lipschitz hβ hp.1 hq.1)).2 H
        norm_num at h
        exact h
      _ = _ := by simp [totalDrift,←mul_sum,sum_add_distrib]
  have h0 := he 3 (by norm_num [allowed])
  have h1 := he (3+1/100) (by norm_num [allowed])
  have hid : (∑ t ∈ range H, average w (endpointVariation I ξ t)) =
      (∑ a, ∑ t ∈ range H, average w (fun ω =>
        |estimate (I a) (rank 3) ξ (t+1) ω-estimate (I a) (rank 3) ξ t ω|))+
      (∑ a, ∑ t ∈ range H, average w (fun ω =>
        |estimate (I a) (rank (3+1/100)) ξ (t+1) ω-estimate (I a) (rank (3+1/100)) ξ t ω|)) := by
    change (∑ t ∈ range H, average w (fun ω => ∑ a, _)) = _
    simp_rw [average_sum,average_add]
    rw [sum_comm (s:=range H)]
    simp_rw [sum_add_distrib]
  rw [hid,show (160:ℝ)/ξ=80/ξ+80/ξ by ring,add_mul]
  exact add_le_add h0 h1

theorem cap_step (I : A → Input Ω) {β factor : ℝ} (hβ : allowed β)
    (hf : factor ∈ Set.Icc (0:ℝ) 2) (ξ : ℝ) (t : ℕ) (ω : Ω) :
    |cap I β ξ factor (t+1) ω-cap I β ξ factor t ω| ≤
      2*endpointVariation I ξ t ω+3*coreChange I t ω := by
  calc
    _ = |(coreCount (fun a => core (I a) (t+1) ω)-coreCount (fun a => core (I a) t ω))+
      factor*(estimateFlex I β ξ (t+1) ω-estimateFlex I β ξ t ω)| := by unfold cap; congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ coreChange I t ω+2*|estimateFlex I β ξ (t+1) ω-estimateFlex I β ξ t ω| := by
      rw [abs_mul,abs_of_nonneg hf.1]
      exact add_le_add (core_step I t ω) (mul_le_mul_of_nonneg_right hf.2 (abs_nonneg _))
    _ ≤ _ := by linarith [flex_step I hβ ξ t ω]

end UniformKServer.FineVariation

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarRanks
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                
section

/-! The actual rank processes of a finite hidden count law on its positive
support. No martingale or allocation estimate is part of the data. -/
noncomputable section
namespace UniformKServer.StarRanks
open Finset ConditionalLaw RankData
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem rank_sum (d : Data Ω ι k) (t : ℕ) (ω : Ω) {β : ℝ}
    (hβ : RankFunctions.allowed β) :
    (∑ i, totalRank β (fun j => (input d i j).posterior t ω)) ≤
      totalRank β (fun j => (parentInput d j).posterior t ω) :=
  ConditionalRanks.rank_superadditivity d.weight (fun v => le_of_lt (d.positive v))
    (d.filtration t) ω (ne_of_gt (mass_pos d t ω)) (d.count t) k (d.bound t) β hβ

theorem held_min (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι)
    (hp : 0 < held d t ω i) : (9/100000:ℝ) ≤ held d t ω i :=
  CoarseBridge.held_min _ _ _ hp

theorem zero_flags (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι)
    (hz : held d t ω i=0) (j : Fin k) : flags d t ω i j=false :=
  CoarseBridge.held_zero_flags _ _ _ hz j

theorem core_bound (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) :
    coreInput d t ω i ≤ 40*held d t ω i :=
  CoarseBridge.core_input_bound _ _ _

end UniformKServer.StarRanks

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarParameters
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Logarithmic child/parent parameter gaps for the actual finite-count star.
The only epoch input is the invariant of the concrete held-size schedule. -/
noncomputable section
namespace UniformKServer.StarParameters
open Finset RankData RankTracking CoarseData StarRanks EpochGeometry
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem dominant_gap (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω)
    (s : State ι) (hs : valid (held d t ω) s) (o : ι) (ho : dominant s=some o)
    (U : ℝ) (hU : EpochParameters.sideReference (held d t ω) o U) :
    (ParentBeta.cBeta/3)/EpochAlpha.ell k*(U/total s.base) ≤
      ParentBeta.trueParam (input d o) k t ω-ParentBeta.trueParam (parentInput d) k t ω := by
  have hA := (dominant_spec ho).1
  have ha : 0 < held d t ω o := by have := (dominant_size hs ho).1; linarith
  have haA : held d t ω o ≤ (101/100)*total s.base := by
    have hi : held d t ω o ≤ total (held d t ω) :=
      single_le_sum (fun j _ => held_nonneg d t ω j) (mem_univ o)
    exact hi.trans (total_comparison hs).2
  have hUb : U ≤ (1001/1000)*side o (held d t ω) := by
    have hu := (div_le_iff₀ (show (0:ℝ)<1001/1000 by norm_num)).mp hU.2.1
    linarith
  have hr := ParameterGaps.dominant_ratio hA ha
    (EpochParameters.side_nonneg (held_nonneg d t ω) o) haA hUb (size_ratio d t ω o ha)
  have hlog := ParameterGaps.dominant_log (div_nonneg hU.1 hA.le)
    (EpochParameters.marked_u_upper hs ho hU).le hr
  rw [beta_difference d hk t ω o ha]
  have hcoeff : 0 ≤ ParentBeta.cBeta/EpochAlpha.ell k :=
    div_nonneg (by norm_num [ParentBeta.cBeta]) (le_trans (by norm_num) (EpochAlpha.ell_one k))
  have hm := mul_le_mul_of_nonneg_left hlog hcoeff
  calc
    _ = ParentBeta.cBeta/EpochAlpha.ell k*((U/total s.base)/3) := by ring
    _ ≤ _ := hm

end UniformKServer.StarParameters

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarSchedules
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! The source star's actual causal data: persistent held sizes, parent refresh,
epochs, upper parameter and coarse dominant flexible-mass tracker. -/
noncomputable section
namespace UniformKServer.StarSchedules
open Finset StarRanks RankTracking CoarseData
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem estimate_measurable (d : Data Ω ι k) (i : ι) (j : Fin k) (f : ℝ → ℝ) (ξ : ℝ)
    (t : ℕ) {ω v : Ω} (h : (d.filtration t).r ω v) :
    estimate (input d i j) f ξ t ω=estimate (input d i j) f ξ t v :=
  congrArg f (reference_measurable (input d i j) f ξ t ω v h)

theorem held_measurable (d : Data Ω ι k) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : held d t ω=held d t v := by
  funext i
  unfold held heldSize activeState
  congr 1
  apply CausalSchedules.active_congr
  intro s hs
  apply sum_congr rfl
  intro j _
  exact estimate_measurable d i j _ _ s (refining d hs h)

theorem parent_estimate_measurable (d : Data Ω ι k) (δ : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) :
    sizeEstimate (parentInput d) δ t ω=sizeEstimate (parentInput d) δ t v := by
  apply sum_congr rfl
  intro j _
  exact congrArg RankData.sizeRank (reference_measurable (parentInput d j) _ δ t ω v h)

theorem parent_reference_measurable (d : Data Ω ι k) (δ : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) :
    ParentScale.reference (parentInput d) δ t ω=ParentScale.reference (parentInput d) δ t v := by
  apply CausalSchedules.held_congr
  intro s hs
  unfold ParentScale.estimateX
  rw [parent_estimate_measurable d δ s (refining d hs h)]

theorem refresh_measurable (d : Data Ω ι k) (δ : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration (t+1)).r ω v) : parentRefresh d δ t ω=parentRefresh d δ t v := by
  unfold parentRefresh
  rw [parent_reference_measurable d δ (t+1) h,
    parent_reference_measurable d δ t (d.refines t ω v h)]

def epoch (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) : EpochGeometry.State ι :=
  EpochGeometry.schedule (fun s => held d s ω) (fun s => parentRefresh d δ s ω) t

theorem epoch_valid (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) :
    EpochGeometry.valid (held d t ω) (epoch d δ t ω) :=
  EpochGeometry.schedule_valid (fun s i => held_nonneg d s ω i) _ t

theorem epoch_measurable (d : Data Ω ι k) (δ : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : epoch d δ t ω=epoch d δ t v :=
  CausalSchedules.epoch_congr t (fun s hs => held_measurable d s (refining d hs h))
    (fun s hs => refresh_measurable d δ s (refining d (by omega) h))

theorem upper_measurable (d : Data Ω ι k) (δ : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : upper d δ t ω=upper d δ t v := by
  unfold upper ParentBeta.heldParam ParentScale.lowerX
  rw [parent_reference_measurable d δ t h]

theorem flag_measurable (d : Data Ω ι k) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : flags d t ω=flags d t v := by
  funext i j
  unfold flags RankData.core
  rw [absoluteReference_measurable (input d i j) (RankFunctions.pstar/8) t ω v h]

theorem flex_measurable (d : Data Ω ι k) (i : ι) (β ξ : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) :
    FlexEstimates.estimateFlex (input d i) β ξ t ω=FlexEstimates.estimateFlex (input d i) β ξ t v := by
  apply sum_congr rfl
  intro j _
  have hf := congrFun (congrFun (flag_measurable d t h) i) j
  change RankData.core (input d i j) t ω=RankData.core (input d i j) t v at hf
  simp only [hf,FlexEstimates.term,estimate_measurable d i j _ _ t h]

def deficit (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  match EpochGeometry.dominant (epoch d δ t ω) with
  | none => 0
  | some o => FlexEstimates.estimateFlex (input d o) 3 sizeTolerance t ω

theorem deficit_nonneg (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) :
    0 ≤ deficit d δ t ω := by
  unfold deficit
  split
  · rfl
  · apply sum_nonneg
    intro j _
    split_ifs
    · rfl
    · exact (FlexEstimates.term_range _ (by norm_num [RankFunctions.allowed]) _ _ _).1

theorem deficit_measurable (d : Data Ω ι k) (δ : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : deficit d δ t ω=deficit d δ t v := by
  unfold deficit
  rw [epoch_measurable d δ t h]
  split
  · rfl
  · exact flex_measurable d _ _ _ t h

theorem core_measurable (d : Data Ω ι k) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : coreInput d t ω=coreInput d t v := by
  funext i
  unfold coreInput
  rw [flag_measurable d t h]
  congr 1
  funext j
  exact (input d i j).posterior_measurable t ω v h

end UniformKServer.StarSchedules

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarCaps
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section

/-! The source's fine caps, instantiated with absolute tolerances and the
actual causal held-size epochs. Endpoint trackers are never restarted. -/
noncomputable section
namespace UniformKServer.StarCaps
open Finset StarRanks StarSchedules RankTracking RankData CoarseData FlexEstimates
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def flex (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  factor (epoch d StarConstants.delta t ω) k i * estimateFlex (input d i)
    (upper d StarConstants.delta t ω) (StarConstants.rho/EpochAlpha.ell k) t ω

def cap (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  coreCount (flags d t ω i)+flex d t ω i

def wholesale (d : Data Ω ι k) (t : ℕ) (ω : Ω) : Bool :=
  SideReferenceSchedule.reset (fun s => held d s ω) (fun s => parentRefresh d StarConstants.delta s ω) t

theorem cap_eq (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) :
    cap d t ω i = FineVariation.cap (input d i) (upper d StarConstants.delta t ω)
      (StarConstants.rho/EpochAlpha.ell k) (factor (epoch d StarConstants.delta t ω) k i) t ω := rfl

theorem cap_nonneg (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    0 ≤ cap d t ω i := by
  rw [cap_eq]
  exact ActualFineCaps.cap_nonneg _ (upper_allowed d StarConstants.delta_bounds.1 hk t ω)
    (factor_range _ k i).1 _ _ _

theorem cap_bound (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    cap d t ω i ≤ 120*held d t ω i := by
  rw [cap_eq]
  exact ActualFineCaps.cap_bound _ (upper_allowed d StarConstants.delta_bounds.1 hk t ω)
    (tolerance k).1 (tolerance k).2.le (factor_range _ k i) _ _

theorem inactive_cap (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (hi : held d t ω i=0) : cap d t ω i=0 := by
  have h := cap_bound d hk t ω i
  rw [hi,mul_zero] at h
  exact le_antisymm h (cap_nonneg d hk t ω i)

theorem regular (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (ha : 0 < held d t ω i) (hi : EpochGeometry.dominant (epoch d StarConstants.delta t ω) ≠ some i) :
    trueFlex (input d i) (ParentBeta.trueParam (input d i) k t ω) t ω ≤ flex d t ω i ∧
      flex d t ω i ≤ trueFlex (input d i) (ParentBeta.trueParam (parentInput d) k t ω) t ω := by
  simp only [flex,factor,ite_eq_right hi]
  exact ActualFineCaps.regular_comparison d hk StarConstants.delta_bounds.1 StarConstants.rho_bounds.1
    StarConstants.lam_bounds.1.le StarConstants.lam_bounds.2 StarConstants.fine_error
    StarConstants.fine_gap StarConstants.fine_eps t ω _ (epoch_valid d _ t ω) i ha hi

theorem dominant (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (hi : EpochGeometry.dominant (epoch d StarConstants.delta t ω)=some i) :
    trueFlex (input d i) (ParentBeta.trueParam (parentInput d) k t ω) t ω ≤ flex d t ω i ∧
      flex d t ω i ≤ (1+StarConstants.eps/EpochAlpha.ell k)*
        trueFlex (input d i) (ParentBeta.trueParam (parentInput d) k t ω) t ω := by
  have hb := ParentBeta.true_allowed (parentInput d) hk t ω (parent_size_bound d t ω)
  have he0 : 0 ≤ StarConstants.rho+4*ParentBeta.cBeta*StarConstants.delta := by
    norm_num [StarConstants.rho,ParentBeta.cBeta,StarConstants.delta]
  have h := (FineCaps.caps (γ:=4*StarConstants.lam)
    (f:=(1-4*StarConstants.lam/EpochAlpha.ell k)*trueFlex (input d i)
      (ParentBeta.trueParam (parentInput d) k t ω) t ω)
    (EpochAlpha.ell_one k) StarConstants.lam_bounds.1.le StarConstants.lam_bounds.2
    he0 StarConstants.fine_error le_rfl StarConstants.fine_eps (flex_nonneg _ hb t ω)
    (ActualFineCaps.held_error d hk StarConstants.delta_bounds.1 StarConstants.rho_bounds.1 t ω i) le_rfl).2
  simpa only [flex,factor,ite_eq_left hi,upper] using h

theorem deficit_comparison (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (hi : EpochGeometry.dominant (epoch d StarConstants.delta t ω)=some i) :
    trueFlex (input d i) (ParentBeta.trueParam (parentInput d) k t ω) t ω/2 ≤ deficit d StarConstants.delta t ω ∧
      deficit d StarConstants.delta t ω ≤ 2*trueFlex (input d i) (ParentBeta.trueParam (parentInput d) k t ω) t ω := by
  simp only [deficit,hi]
  exact ActualFineCaps.coarse_comparison _ (ParentBeta.true_allowed (parentInput d) hk t ω (parent_size_bound d t ω)) t ω

end UniformKServer.StarCaps

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarLower
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                
section

/-! Actual lower requirements of a finite-count star.  This connects the
rank superadditivity to the output formulas, and proves the marked slack
from the logarithmic parameter gap (including zero side mass). -/
noncomputable section
namespace UniformKServer.StarLower
open Finset StarRanks RankData RankFunctions FlexEstimates
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem parent_dominates (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    (∑ i, lower d (parentBeta d t ω) t ω i) ≤ parentLower d t ω :=
  rank_sum d t ω (parent_allowed d hk t ω)

/-- The source's dominant-output-slack inequality.  Its constant is explicit
and absolute, and the assertion retains u=0 and T=0. -/
theorem dominant_slack (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω)
    (s : EpochGeometry.State ι) (hs : EpochGeometry.valid (held d t ω) s)
    (o : ι) (ho : EpochGeometry.dominant s=some o) (U : ℝ)
    (hU : EpochParameters.sideReference (held d t ω) o U) :
    (ParentBeta.cBeta/288)*(U/EpochGeometry.total s.base)/EpochAlpha.ell k*
        trueFlex (input d o) (parentBeta d t ω) t ω ≤
      lower d (parentBeta d t ω) t ω o-lower d (childBeta d t ω o) t ω o := by
  have hg := StarParameters.dominant_gap d hk t ω s hs o ho U hU
  change (ParentBeta.cBeta/3)/EpochAlpha.ell k*(U/EpochGeometry.total s.base) ≤
    childBeta d t ω o-parentBeta d t ω at hg
  have hbn := sub_nonneg.mpr (parameter_le d hk t ω o)
  have hT := flex_nonneg (input d o) (parent_allowed d hk t ω) t ω
  have hgap := (gap_bounds (input d o) (parent_allowed d hk t ω) t ω).1
  have h1 := mul_le_mul_of_nonneg_left hgap hbn
  have h2 := mul_le_mul_of_nonneg_right hg (div_nonneg hT (by norm_num : (0:ℝ) ≤ 96))
  have h3 := mul_nonneg hbn (core_nonneg d t ω o)
  rw [lower_difference]
  calc
    _ = ((ParentBeta.cBeta/3)/EpochAlpha.ell k*(U/EpochGeometry.total s.base))*
        (trueFlex (input d o) (parentBeta d t ω) t ω/96) := by ring
    _ ≤ (childBeta d t ω o-parentBeta d t ω)*
        (trueFlex (input d o) (parentBeta d t ω) t ω/96) := h2
    _ ≤ _ := by nlinarith only [h1,h3]

end UniformKServer.StarLower

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SideRecurrence
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Persistent causal selection of the two actual side minimizers. Empty side
 domains and D=0 use the same compact update, with the source's free deletion. -/
noncomputable section
namespace UniformKServer.SideRecurrence
open Finset UniformKServer.AdaptiveSide
open scoped Classical
variable {ι : Type*} [Fintype ι]

def StepSpec (p q : Config ι) (Bstar Bnew old w v : ι → ℝ) (D S : ℝ) : Prop :=
  DomainTransport.domain q.active 11 w ∧ DomainTransport.domain q.active 11 v ∧
  (∀ i, D*w i ≤ (q.b+theta q i)*Bnew i) ∧
  (S ≤ 2*D → ∀ i, q.b*Bnew i-theta q i*offset q i*D ≤ D*w i) ∧
  (∀ i, D*v i ≤ (p.b+theta p i)*Bstar i) ∧
  D*SideTracker.movement w old ≤ potential p Bstar D old-potential q Bnew D w+
    (potential q Bstar D v-potential p Bstar D v)+slope q*(∑ i, |Bnew i-Bstar i|)

def chooseStep (p q : Config ι) (Bstar Bnew old : ι → ℝ) (D S : ℝ) : (ι → ℝ) × (ι → ℝ) :=
  if h : ∃ wv : (ι → ℝ) × (ι → ℝ), StepSpec p q Bstar Bnew old wv.1 wv.2 D S
    then h.choose else (fun _ => 0,fun _ => 0)

theorem chooseStep_spec {p q : Config ι} (hp : valid p) (hq : valid q)
    (Bstar Bnew old : ι → ℝ) (D S : ℝ) (hD : 0 ≤ D)
    (hB : ∀ i, 0 ≤ Bstar i) (hBn : ∀ i, 0 ≤ Bnew i) (hS : (∑ i, Bnew i) ≤ S)
    (hpB : DomainTransport.Supported p.active Bstar)
    (hqB : DomainTransport.Supported q.active Bstar)
    (hqN : DomainTransport.Supported q.active Bnew)
    (hold : DomainTransport.domain p.active 11 old) :
    StepSpec p q Bstar Bnew old (chooseStep p q Bstar Bnew old D S).1
      (chooseStep p q Bstar Bnew old D S).2 D S := by
  have hex : ∃ wv : (ι → ℝ) × (ι → ℝ), StepSpec p q Bstar Bnew old wv.1 wv.2 D S := by
    obtain ⟨w,v,h⟩ := AdaptiveSide.step hp hq Bstar Bnew old D S hD hB hBn hS hpB hqB hqN hold
    exact ⟨(w,v),h⟩
  unfold chooseStep
  rw [dite_eq_left hex]
  exact hex.choose_spec

def trajectory (p : ℕ → Config ι) (Bstar B : ℕ → ι → ℝ) (D S : ℕ → ℝ) : ℕ → ι → ℝ
  | 0 => fun _ => 0
  | t+1 => (chooseStep (p t) (p (t+1)) (Bstar t) (B (t+1))
      (trajectory p Bstar B D S t) (D (t+1)) (S (t+1))).1

def prepared (p : ℕ → Config ι) (Bstar B : ℕ → ι → ℝ) (D S : ℕ → ℝ) (t : ℕ) : ι → ℝ :=
  (chooseStep (p t) (p (t+1)) (Bstar t) (B (t+1))
      (trajectory p Bstar B D S t) (D (t+1)) (S (t+1))).2

def InputValid (p : ℕ → Config ι) (Bstar B : ℕ → ι → ℝ) (D S : ℕ → ℝ) : Prop :=
  (∀ t, valid (p t)) ∧ (∀ t, 0 ≤ D t) ∧ (∀ t i, 0 ≤ Bstar t i) ∧ (∀ t i, 0 ≤ B t i) ∧
  (∀ t, (∑ i, B t i) ≤ S t) ∧
  (∀ t, DomainTransport.Supported (p t).active (Bstar t)) ∧
  (∀ t, DomainTransport.Supported (p (t+1)).active (Bstar t)) ∧
  (∀ t, DomainTransport.Supported (p t).active (B t))

theorem trajectory_state {p : ℕ → Config ι} {Bstar B : ℕ → ι → ℝ} {D S : ℕ → ℝ}
    (h : InputValid p Bstar B D S) : ∀ t,
    DomainTransport.domain (p t).active 11 (trajectory p Bstar B D S t) := by
  rcases h with ⟨hp,hD,hB,hBn,hS,hpB,hqB,hqN⟩
  intro t
  induction t with
  | zero => exact zero_state _
  | succ t ih => exact (chooseStep_spec (hp t) (hp (t+1)) _ _ _ _ _ (hD (t+1))
      (hB t) (hBn (t+1)) (hS (t+1)) (hpB t) (hqB t) (hqN (t+1)) ih).1

theorem trajectory_step {p : ℕ → Config ι} {Bstar B : ℕ → ι → ℝ} {D S : ℕ → ℝ}
    (h : InputValid p Bstar B D S) (t : ℕ) :
    StepSpec (p t) (p (t+1)) (Bstar t) (B (t+1)) (trajectory p Bstar B D S t)
      (trajectory p Bstar B D S (t+1)) (prepared p Bstar B D S t) (D (t+1)) (S (t+1)) := by
  have hstate := trajectory_state h t
  obtain ⟨hp,hD,hB,hBn,hS,hpB,hqB,hqN⟩ := h
  exact chooseStep_spec (hp t) (hp (t+1)) _ _ _ _ _ (hD (t+1))
    (hB t) (hBn (t+1)) (hS (t+1)) (hpB t) (hqB t) (hqN (t+1)) hstate

theorem causal_through (p q : ℕ → Config ι) (F G B E : ℕ → ι → ℝ)
    (D S D' S' : ℕ → ℝ) (n : ℕ) (hp : ∀ t, t ≤ n → p t=q t)
    (hF : ∀ t, t < n → F t=G t) (hB : ∀ t, t ≤ n → B t=E t)
    (hD : ∀ t, t ≤ n → D t=D' t) (hS : ∀ t, t ≤ n → S t=S' t) :
    trajectory p F B D S n=trajectory q G E D' S' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he := ih (fun t ht => hp t (ht.trans (Nat.le_succ n)))
      (fun t ht => hF t (ht.trans (Nat.lt_succ_self n)))
      (fun t ht => hB t (ht.trans (Nat.le_succ n)))
      (fun t ht => hD t (ht.trans (Nat.le_succ n)))
      (fun t ht => hS t (ht.trans (Nat.le_succ n)))
    simp only [trajectory,hp n (Nat.le_succ n),hp (n+1) le_rfl,
      hF n (Nat.lt_succ_self n),hB (n+1) le_rfl,hD (n+1) le_rfl,hS (n+1) le_rfl,he]

end UniformKServer.SideRecurrence

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SideFiniteInput
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Actual posterior/core inputs in a finite reveal law. Conditions describe the
 held, measurable data, not a movement conclusion. Empty and null-fiber cases
 still use the zero conventions of the conditional kernel. -/
noncomputable section
namespace UniformKServer.SideFiniteInput
open Finset UniformKServer.AdaptiveSide UniformKServer.ConditionalLaw
open scoped Classical
variable {Ω ι R : Type*} [Fintype Ω] [Fintype ι] [Fintype R]

structure Data (Ω ι R : Type*) [Fintype Ω] [Fintype ι] [Fintype R] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  filtration : ℕ → Setoid Ω
  refines : ∀ t ω v, (filtration (t+1)).r ω v → (filtration t).r ω v
  hidden : ℕ → Ω → ι × R → ℝ
  hidden_range : ∀ t ω ir, hidden t ω ir ∈ Set.Icc (0:ℝ) 1
  param : ℕ → Ω → Config ι
  param_valid : ∀ t ω, valid (param t ω)
  param_measurable : ∀ t ω v, (filtration t).r ω v → param t ω=param t v
  flag : ℕ → Ω → ι → R → Bool
  flag_measurable : ∀ t ω v, (filtration t).r ω v → flag t ω=flag t v
  supported : ∀ t ω i, i ∉ (param t ω).active → ∀ r, flag t ω i r=false
  deficit : ℕ → Ω → ℝ
  deficit_nonneg : ∀ t ω, 0 ≤ deficit t ω
  deficit_measurable : ∀ t ω v, (filtration t).r ω v → deficit t ω=deficit t v
  mass : ℕ → Ω → ℝ
  mass_measurable : ∀ t ω v, (filtration t).r ω v → mass t ω=mass t v
  mass_bound : ∀ t ω, (∑ i, SyntheticCore.input
    (fun r => posterior weight (filtration t) (fun v => hidden t v (i,r)) ω) (flag t ω i)) ≤ mass t ω

def post (d : Data Ω ι R) (t : ℕ) (ω : Ω) (i : ι) (r : R) : ℝ :=
  posterior d.weight (d.filtration t) (fun v => d.hidden t v (i,r)) ω

def input (d : Data Ω ι R) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  SyntheticCore.input (post d t ω i) (d.flag t ω i)

def star (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ι → ℝ :=
  SyntheticCore.core (activeFlag (d.param t ω)) (activeFlag (d.param (t+1) ω))
    (post d (t+1) ω) (d.flag (t+1) ω)

def tracker (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ι → ℝ :=
  SideRecurrence.trajectory (fun s => d.param s ω) (fun s => star d s ω)
    (fun s => input d s ω) (fun s => d.deficit s ω) (fun s => d.mass s ω) t

def prepared (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ι → ℝ :=
  SideRecurrence.prepared (fun s => d.param s ω) (fun s => star d s ω)
    (fun s => input d s ω) (fun s => d.deficit s ω) (fun s => d.mass s ω) t

theorem post_range (d : Data Ω ι R) (t : ℕ) (ω : Ω) (i : ι) (r : R) :
    post d t ω i r ∈ Set.Icc (0:ℝ) 1 :=
  ⟨posterior_nonneg d.nonneg (fun v => (d.hidden_range t v (i,r)).1) _ ω,
    posterior_le_one d.nonneg (fun v => (d.hidden_range t v (i,r)).2) _ ω⟩

theorem input_nonneg (d : Data Ω ι R) (t : ℕ) (ω : Ω) (i : ι) : 0 ≤ input d t ω i :=
  SyntheticCore.input_nonneg (fun r => (post_range d t ω i r).1) _

theorem input_supported (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    DomainTransport.Supported ((d.param t ω).active) (input d t ω) := by
  intro i hi
  exact SyntheticCore.no_flags _ (d.supported t ω i hi)

theorem star_supported_old (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    DomainTransport.Supported ((d.param t ω).active) (star d t ω) := by
  intro i hi
  simp [star,SyntheticCore.core,activeFlag,hi]

theorem star_supported_new (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    DomainTransport.Supported ((d.param (t+1) ω).active) (star d t ω) := by
  intro i hi
  simp [star,SyntheticCore.core,activeFlag,hi]

theorem valid_input (d : Data Ω ι R) (ω : Ω) :
    SideRecurrence.InputValid (fun s => d.param s ω) (fun s => star d s ω)
      (fun s => input d s ω) (fun s => d.deficit s ω) (fun s => d.mass s ω) := by
  refine ⟨fun t => d.param_valid t ω,fun t => d.deficit_nonneg t ω,?_,
    fun t => input_nonneg d t ω,fun t => d.mass_bound t ω,
    fun t => star_supported_old d t ω,fun t => star_supported_new d t ω,
    fun t => input_supported d t ω⟩
  intro t i
  exact (SyntheticCore.core_le_new _ _ _ _ (fun i r => (post_range d (t+1) ω i r).1) i).1

theorem tracker_state (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    DomainTransport.domain (d.param t ω).active 11 (tracker d t ω) := SideRecurrence.trajectory_state (valid_input d ω) t

theorem step (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    SideRecurrence.StepSpec (d.param t ω) (d.param (t+1) ω) (star d t ω) (input d (t+1) ω)
      (tracker d t ω) (tracker d (t+1) ω) (prepared d t ω) (d.deficit (t+1) ω) (d.mass (t+1) ω) :=
  SideRecurrence.trajectory_step (valid_input d ω) t

theorem refining (d : Data Ω ι R) {s t : ℕ} (hst : s ≤ t) {ω v : Ω}
    (h : (d.filtration t).r ω v) : (d.filtration s).r ω v := by
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ t _ ih => exact ih (d.refines t ω v h)

theorem input_measurable (d : Data Ω ι R) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : input d t ω=input d t v := by
  funext i
  unfold input
  rw [d.flag_measurable t ω v h]
  congr 1
  funext r
  exact posterior_measurable _ _ _ ω v h

theorem star_measurable (d : Data Ω ι R) (t : ℕ) {ω v : Ω}
    (h : (d.filtration (t+1)).r ω v) : star d t ω=star d t v := by
  unfold star
  rw [d.param_measurable t ω v (d.refines t ω v h),
    d.param_measurable (t+1) ω v h,d.flag_measurable (t+1) ω v h]
  congr 1
  funext i r
  exact posterior_measurable _ _ _ ω v h

theorem tracker_measurable (d : Data Ω ι R) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : tracker d t ω=tracker d t v := by
  apply SideRecurrence.causal_through
  · intro s hs
    exact d.param_measurable s ω v (refining d hs h)
  · intro s hs
    exact star_measurable d s (refining d (Nat.succ_le_iff.mpr hs) h)
  · intro s hs
    exact input_measurable d s (refining d hs h)
  · intro s hs
    exact d.deficit_measurable s ω v (refining d hs h)
  · intro s hs
    exact d.mass_measurable s ω v (refining d hs h)

end UniformKServer.SideFiniteInput

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarTrackers
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! The recursive minimizers instantiated with the finite hidden-count law and
its literal held parameters, rather than an assumed allocator interface. -/
noncomputable section
namespace UniformKServer.StarTrackers
open Finset StarRanks StarSchedules
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def alphaParam (d : Data Ω ι k) (δ ct C : ℝ) (t : ℕ) (ω : Ω) : AlphaEmpty.Config ι :=
  EpochAlphaSchedule.schedule (fun s => held d s ω) (fun s => parentRefresh d δ s ω) k ct C t

theorem alphaParam_measurable (d : Data Ω ι k) (δ ct C : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : alphaParam d δ ct C t ω=alphaParam d δ ct C t v :=
  CausalSchedules.alpha_congr k ct C t (fun s hs => held_measurable d s (refining d hs h))
    (fun s hs => refresh_measurable d δ s (refining d (by omega) h))

theorem alphaParam_active (d : Data Ω ι k) (δ ct C : ℝ) (t : ℕ) (ω : Ω) :
    AlphaEmpty.active (alphaParam d δ ct C t ω)=EpochParameters.active (held d t ω) :=
  EpochAlphaSchedule.schedule_active (fun s i => held_nonneg d s ω i) _ _ _ _ _

def alphaData (d : Data Ω ι k) (δ : ℝ) {ct C : ℝ} (hc : 0 < ct) (hct : ct*50000 ≤ 1)
    (hC : 1000 < C*ct) : AlphaFiniteInput.Data Ω ι (Fin k) where
  weight := d.weight
  nonneg := fun ω => (d.positive ω).le
  filtration := d.filtration
  refines := d.refines
  hidden := fun t ω ir => ConditionalRank.indicator (d.count t ω ir.1) ir.2
  hidden_range := fun t ω ir => ConditionalRank.indicator_range _ _
  param := alphaParam d δ ct C
  param_valid := fun t ω => EpochAlphaSchedule.schedule_valid
    (fun s i => held_nonneg d s ω i) _ k hc hct hC
    (fun s => held_sum d s ω) (fun s i => held_min d s ω i) t
  param_measurable := fun t ω v h => alphaParam_measurable d δ ct C t h
  flag := flags d
  flag_measurable := fun t ω v h => flag_measurable d t h
  supported := by
    intro t ω i hi j
    rw [alphaParam_active] at hi
    apply zero_flags d t ω i _ j
    exact le_antisymm (le_of_not_gt (by simpa only [EpochParameters.mem_active] using hi))
      (held_nonneg d t ω i)

def sideParam (d : Data Ω ι k) (δ cw : ℝ) (t : ℕ) (ω : Ω) : AdaptiveSide.Config ι :=
  EpochSide.config (held d t ω) (epoch d δ t ω) (EpochAlpha.ell k) cw (upper d δ t ω)

theorem sideParam_measurable (d : Data Ω ι k) (δ cw : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : sideParam d δ cw t ω=sideParam d δ cw t v := by
  unfold sideParam
  rw [held_measurable d t h,epoch_measurable d δ t h,upper_measurable d δ t h]

def sideFlags (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) (i : ι) (j : Fin k) : Bool :=
  if i ∈ EpochSide.active (held d t ω) (epoch d δ t ω) then flags d t ω i j else false

theorem sideFlags_measurable (d : Data Ω ι k) (δ : ℝ) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : sideFlags d δ t ω=sideFlags d δ t v := by
  funext i j
  unfold sideFlags
  rw [held_measurable d t h,epoch_measurable d δ t h,flag_measurable d t h]

theorem side_core_le (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) (i : ι) :
    SyntheticCore.input (fun j => (input d i j).posterior t ω) (sideFlags d δ t ω i) ≤
      coreInput d t ω i := by
  unfold sideFlags coreInput
  by_cases hi : i ∈ EpochSide.active (held d t ω) (epoch d δ t ω)
  · simp only [hi,↓reduceIte,le_refl]
  · simp only [hi,↓reduceIte]
    rw [SyntheticCore.no_flags _ (fun _ => rfl)]
    exact SyntheticCore.input_nonneg (fun j => ((input d i j).posterior_range t ω).1) _

def sideData (d : Data Ω ι k) (hk : 1 ≤ k) {δ cw : ℝ} (hδ : 0 < δ)
    (hcw : 0 < cw) (hc : cw*50000 ≤ 1) : SideFiniteInput.Data Ω ι (Fin k) where
  weight := d.weight
  nonneg := fun ω => (d.positive ω).le
  filtration := d.filtration
  refines := d.refines
  hidden := fun t ω ir => ConditionalRank.indicator (d.count t ω ir.1) ir.2
  hidden_range := fun t ω ir => ConditionalRank.indicator_range _ _
  param := sideParam d δ cw
  param_valid := by
    intro t ω
    apply EpochSide.schedule_valid (fun s i => held_nonneg d s ω i) _ k hcw hc
      (fun s => upper d δ s ω) _ (fun s => held_sum d s ω) (fun s i => held_min d s ω i) t
    intro s
    have hb := upper_allowed d hδ hk s ω
    norm_num [RankFunctions.allowed] at hb
    constructor <;> linarith [hb.1,hb.2]
  param_measurable := fun t ω v h => sideParam_measurable d δ cw t h
  flag := sideFlags d δ
  flag_measurable := fun t ω v h => sideFlags_measurable d δ t h
  supported := by
    intro t ω i hi j
    exact ite_eq_right hi
  deficit := deficit d δ
  deficit_nonneg := deficit_nonneg d δ
  deficit_measurable := fun t ω v h => deficit_measurable d δ t h
  mass := fun t ω => ∑ i, coreInput d t ω i
  mass_measurable := by
    intro t ω v h
    rw [core_measurable d t h]
  mass_bound := fun t ω => sum_le_sum fun i _ => side_core_le d δ t ω i

end UniformKServer.StarTrackers

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarFeasibilityParameters
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                
section

/-! Explicit room for the actual held parameters in the two output rules.
The inequalities include arbitrarily small dominant side proportions. -/
noncomputable section
namespace UniformKServer.StarFeasibilityParameters
open Finset StarRanks StarSchedules StarLower
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def sideReference (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  SideReferenceSchedule.reference (fun s => held d s ω) (fun s => parentRefresh d δ s ω) t

theorem side_valid_reference (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) (o : ι)
    (ho : EpochGeometry.dominant (epoch d δ t ω)=some o) :
    EpochParameters.sideReference (held d t ω) o (sideReference d δ t ω) :=
  SideReferenceSchedule.reference_spec (fun s i => held_nonneg d s ω i) _ t ho

def alphaParam (d : Data Ω ι k) (t : ℕ) (ω : Ω) : AlphaEmpty.Config ι :=
  StarTrackers.alphaParam d StarConstants.delta StarConstants.ct StarConstants.multiplier t ω

def sideParam (d : Data Ω ι k) (t : ℕ) (ω : Ω) : AdaptiveSide.Config ι :=
  StarTrackers.sideParam d StarConstants.delta StarConstants.cw t ω

theorem alpha_valid (d : Data Ω ι k) (t : ℕ) (ω : Ω) : AlphaEmpty.valid (alphaParam d t ω) :=
  (StarTrackers.alphaData d StarConstants.delta StarConstants.ct_pos
    StarConstants.ct_height StarConstants.multiplier_bound).param_valid t ω

theorem regular_room (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (hai : 0 < held d t ω i)
    (hi : EpochGeometry.dominant (epoch d StarConstants.delta t ω) ≠ some i) :
    (parentBeta d t ω+4*StarConstants.eps/EpochAlpha.ell k)*
        (1+AlphaEmpty.eta (alphaParam d t ω) i) ≤ childBeta d t ω i := by
  have hs := epoch_valid d StarConstants.delta t ω
  have hl : 0 < EpochAlpha.ell k := lt_of_lt_of_le zero_lt_one (EpochAlpha.ell_one k)
  have he := EpochOutputParameters.eta_regular hs hl StarConstants.ct_pos.le i hai hi
    (U:=sideReference d StarConstants.delta t ω) (C:=StarConstants.multiplier)
  have hp := alpha_valid d t ω
  have hηn : 0 ≤ AlphaEmpty.eta (alphaParam d t ω) i := (EpochOutputParameters.eta_range hp i).1
  have hη1 : AlphaEmpty.eta (alphaParam d t ω) i ≤ 1 := (EpochOutputParameters.eta_range hp i).2
  have hb := parent_allowed d hk t ω
  exact regular_room_algebra hl (EpochParameters.regular_height hs hai hi)
    (by linarith [hb.1]) (by linarith [hb.2]) hηn hη1 he
    (StarParameters.regular_gap d hk t ω _ hs i hai hi)

theorem dominant_room (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (o : ι)
    (ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω)=some o) :
    parentBeta d t ω*(1+AlphaEmpty.eta (alphaParam d t ω) o) ≤ childBeta d t ω o := by
  have hs := epoch_valid d StarConstants.delta t ω
  have hU := side_valid_reference d StarConstants.delta t ω o ho
  have he := EpochOutputParameters.eta_dominant hs (sideReference d StarConstants.delta t ω)
    (EpochAlpha.ell k) StarConstants.ct StarConstants.multiplier o ho
  change AlphaEmpty.eta (alphaParam d t ω) o = _ at he
  rw [he]
  have hg := StarParameters.dominant_gap d hk t ω _ hs o ho _ hU
  change (ParentBeta.cBeta/3)/EpochAlpha.ell k*(_/_) ≤ childBeta d t ω o-parentBeta d t ω at hg
  have hb := parent_allowed d hk t ω
  have hl : 0 < EpochAlpha.ell k := lt_of_lt_of_le zero_lt_one (EpochAlpha.ell_one k)
  have hu := div_nonneg hU.1 (EpochGeometry.dominant_spec ho).1.le
  have hc : parentBeta d t ω*StarConstants.ct ≤ ParentBeta.cBeta/3 := by
    norm_num [ParentBeta.cBeta,StarConstants.ct]
    linarith [hb.2]
  have hh := mul_le_mul_of_nonneg_right hc (div_nonneg hu hl.le)
  calc
    _ = parentBeta d t ω+(parentBeta d t ω*StarConstants.ct)*
        ((sideReference d StarConstants.delta t ω/EpochGeometry.total (epoch d StarConstants.delta t ω).base)/EpochAlpha.ell k) := by ring
    _ ≤ parentBeta d t ω+(ParentBeta.cBeta/3)*
        ((sideReference d StarConstants.delta t ω/EpochGeometry.total (epoch d StarConstants.delta t ω).base)/EpochAlpha.ell k) := by linarith only [hh]
    _ ≤ childBeta d t ω o := by
      simp only [div_eq_mul_inv] at hg ⊢
      nlinarith only [hg]

theorem side_room (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (hi : i ∈ (sideParam d t ω).active) :
    (sideParam d t ω).b+AdaptiveSide.theta (sideParam d t ω) i ≤ childBeta d t ω i := by
  have hs := epoch_valid d StarConstants.delta t ω
  have hm := EpochSide.mem hi
  have hh := EpochParameters.regular_height hs hm.1 hm.2
  have hl : 0 < EpochAlpha.ell k := lt_of_lt_of_le zero_lt_one (EpochAlpha.ell_one k)
  have hg := StarParameters.regular_gap d hk t ω _ hs i hm.1 hm.2
  change (ParentBeta.cBeta/50)/EpochAlpha.ell k*_ ≤ childBeta d t ω i-parentBeta d t ω at hg
  have he := EpochOutputParameters.theta_active (EpochAlpha.ell k) StarConstants.cw
    (upper d StarConstants.delta t ω) hi
  change AdaptiveSide.theta (sideParam d t ω) i = _ at he
  have hp := (ParentBeta.parameter_accuracy (parentInput d) StarConstants.delta_bounds.1 hk t ω).2
  change (sideParam d t ω).b ≤ parentBeta d t ω+_ at hp
  rw [he]
  have hconst : 4*ParentBeta.cBeta*StarConstants.delta+
      StarConstants.cw*SideParameters.height (EpochGeometry.total (epoch d StarConstants.delta t ω).base) (held d t ω i) ≤
      (ParentBeta.cBeta/50)*SideParameters.height (EpochGeometry.total (epoch d StarConstants.delta t ω).base) (held d t ω i) := by
    have hh' := hh
    norm_num [ParentBeta.cBeta,StarConstants.delta,StarConstants.cw] at hh' ⊢
    linarith only [hh']
  have hdiv := div_le_div_of_nonneg_right hconst hl.le
  rw [add_div] at hdiv
  calc
    _ ≤ parentBeta d t ω+(4*ParentBeta.cBeta*StarConstants.delta)/EpochAlpha.ell k+
        StarConstants.cw*SideParameters.height (EpochGeometry.total (epoch d StarConstants.delta t ω).base) (held d t ω i)/EpochAlpha.ell k := by linarith only [hp]
    _ ≤ parentBeta d t ω+(ParentBeta.cBeta/50)*SideParameters.height (EpochGeometry.total (epoch d StarConstants.delta t ω).base) (held d t ω i)/EpochAlpha.ell k := by linarith only [hdiv]
    _ ≤ childBeta d t ω i := by
      simp only [div_eq_mul_inv] at hg ⊢
      nlinarith only [hg]


theorem side_slack (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (o : ι)
    (ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω)=some o) :
    deficit d StarConstants.delta t ω*(∑ i ∈ univ.erase o,
        AdaptiveSide.theta (sideParam d t ω) i*AdaptiveSide.offset (sideParam d t ω) i) ≤
      lower d (parentBeta d t ω) t ω o-lower d (childBeta d t ω o) t ω o := by
  have hs := epoch_valid d StarConstants.delta t ω
  have hU := side_valid_reference d StarConstants.delta t ω o ho
  have hl : 0 < EpochAlpha.ell k := lt_of_lt_of_le zero_lt_one (EpochAlpha.ell_one k)
  have hu := div_nonneg hU.1 (EpochGeometry.dominant_spec ho).1.le
  have hsum := EpochOutputParameters.side_sum_bound hs (held_nonneg d t ω)
    hl StarConstants.cw_pos.le (upper d StarConstants.delta t ω) o ho hU
  change (∑ i ∈ univ.erase o, AdaptiveSide.theta (sideParam d t ω) i*
    AdaptiveSide.offset (sideParam d t ω) i) ≤ _ at hsum
  have hD := (StarCaps.deficit_comparison d hk t ω o ho).2
  have hD0 := deficit_nonneg d StarConstants.delta t ω
  have hT := FlexEstimates.flex_nonneg (input d o) (parent_allowed d hk t ω) t ω
  have hK : 0 ≤ (1001/1000)*StarConstants.cw/EpochAlpha.ell k*
      (sideReference d StarConstants.delta t ω/EpochGeometry.total (epoch d StarConstants.delta t ω).base) :=
    mul_nonneg (div_nonneg (mul_nonneg (by norm_num) StarConstants.cw_pos.le) hl.le) hu
  have hc : 2*(1001/1000)*StarConstants.cw ≤ ParentBeta.cBeta/288 := by
    norm_num [StarConstants.cw,ParentBeta.cBeta]
  have hh := mul_le_mul_of_nonneg_right hc
    (mul_nonneg (div_nonneg hu hl.le) hT)
  calc
    _ ≤ deficit d StarConstants.delta t ω*((1001/1000)*StarConstants.cw/EpochAlpha.ell k*
        (sideReference d StarConstants.delta t ω/EpochGeometry.total (epoch d StarConstants.delta t ω).base)) :=
      mul_le_mul_of_nonneg_left hsum hD0
    _ ≤ (2*FlexEstimates.trueFlex (input d o) (parentBeta d t ω) t ω)*
        ((1001/1000)*StarConstants.cw/EpochAlpha.ell k*
        (sideReference d StarConstants.delta t ω/EpochGeometry.total (epoch d StarConstants.delta t ω).base)) :=
      mul_le_mul_of_nonneg_right hD hK
    _ ≤ (ParentBeta.cBeta/288)*(sideReference d StarConstants.delta t ω/
        EpochGeometry.total (epoch d StarConstants.delta t ω).base)/EpochAlpha.ell k*
        FlexEstimates.trueFlex (input d o) (parentBeta d t ω) t ω := by
      calc
        _ = (2*(1001/1000)*StarConstants.cw)*
            ((sideReference d StarConstants.delta t ω/EpochGeometry.total (epoch d StarConstants.delta t ω).base)/EpochAlpha.ell k*
              FlexEstimates.trueFlex (input d o) (parentBeta d t ω) t ω) := by ring
        _ ≤ (ParentBeta.cBeta/288)*
            ((sideReference d StarConstants.delta t ω/EpochGeometry.total (epoch d StarConstants.delta t ω).base)/EpochAlpha.ell k*
              FlexEstimates.trueFlex (input d o) (parentBeta d t ω) t ω) := hh
        _ = _ := by ring
    _ ≤ _ := dominant_slack d hk t ω _ hs o ho _ hU

end UniformKServer.StarFeasibilityParameters

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarOutputData
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Concrete data for the output rules, including the signed total cap error.
All rank and tracker quantities are derived from the finite hidden law. -/
noncomputable section
namespace UniformKServer.StarOutputData
open Finset StarRanks StarSchedules StarLower
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def error (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ :=
  match EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none => 0
  | some o => StarCaps.flex d t ω o-parentFlex d t ω o

def alphaData (d : Data Ω ι k) : AlphaFiniteInput.Data Ω ι (Fin k) :=
  StarTrackers.alphaData d StarConstants.delta StarConstants.ct_pos
    StarConstants.ct_height StarConstants.multiplier_bound

def sideData (d : Data Ω ι k) (hk : 1 ≤ k) : SideFiniteInput.Data Ω ι (Fin k) :=
  StarTrackers.sideData d hk StarConstants.delta_bounds.1 StarConstants.cw_pos StarConstants.cw_height

def alpha (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ι → ℝ := AlphaFiniteInput.alpha (alphaData d) t ω

def side (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) : ι → ℝ :=
  SideFiniteInput.tracker (sideData d hk) t ω

theorem parent_expand (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d t ω ≤ q) :
    (∑ i, (core d t ω i-parentBeta d t ω*coreInput d t ω i+parentFlex d t ω i)) ≤ q := by
  have h := (parent_dominates d hk t ω).trans hq
  simpa only [decomposition,core,parentFlex] using h

theorem flex_inactive (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) (hi : held d t ω i=0) :
    StarCaps.flex d t ω i=0 := by
  have h := StarCaps.inactive_cap d hk t ω i hi
  have hn : RankData.coreCount (flags d t ω i)=0 := by
    simp only [RankData.coreCount,zero_flags d t ω i hi,Bool.false_eq_true,ite_false, if_false,sum_const_zero]
  simpa only [StarCaps.cap,hn,zero_add] using h

theorem regular_flex (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (hi : EpochGeometry.dominant (epoch d StarConstants.delta t ω) ≠ some i) :
    childFlex d t ω i ≤ StarCaps.flex d t ω i ∧ StarCaps.flex d t ω i ≤ parentFlex d t ω i := by
  by_cases ha : 0 < held d t ω i
  · exact StarCaps.regular d hk t ω i ha hi
  · have hz := le_antisymm (le_of_not_gt ha) (held_nonneg d t ω i)
    rw [flex_inactive d hk t ω i hz]
    exact ⟨le_of_eq (StarLower.inactive d _ t ω i hz).2,
      le_of_eq ((StarLower.inactive d _ t ω i hz).2.symm)⟩

theorem cap_child (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    childFlex d t ω i ≤ StarCaps.flex d t ω i := by
  by_cases hi : EpochGeometry.dominant (epoch d StarConstants.delta t ω)=some i
  · exact (flex_mono d hk t ω i).trans (StarCaps.dominant d hk t ω i hi).1
  · exact (regular_flex d hk t ω i hi).1

theorem error_nonneg (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) : 0 ≤ error d t ω := by
  unfold error
  split
  · exact le_rfl
  · rename_i o ho
    exact sub_nonneg.mpr (StarCaps.dominant d hk t ω o ho).1

theorem error_sum (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    (∑ i, (StarCaps.flex d t ω i-parentFlex d t ω i)) ≤ error d t ω := by
  cases ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none =>
    simp only [error,ho]
    exact sum_nonpos fun i _ => sub_nonpos.mpr (regular_flex d hk t ω i (by rw [ho]; simp)).2
  | some o =>
    simp only [error,ho]
    rw [←sum_erase_add _ _ (mem_univ o)]
    have hs : (∑ i ∈ univ.erase o, (StarCaps.flex d t ω i-parentFlex d t ω i)) ≤ 0 := by
      apply sum_nonpos
      intro i hi
      apply sub_nonpos.mpr (regular_flex d hk t ω i ?_).2
      rw [ho]
      exact fun h => (ne_of_mem_erase hi) (Option.some.inj h).symm
    linarith

theorem error_rule_one (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω)
    (hreg : deficit d StarConstants.delta t ω/2 ≤ mass d t ω) :
    error d t ω ≤ (4*StarConstants.eps/EpochAlpha.ell k)*mass d t ω := by
  have hc : 0 ≤ StarConstants.eps/EpochAlpha.ell k := div_nonneg (by norm_num [StarConstants.eps])
    (le_trans (by norm_num) (EpochAlpha.ell_one k))
  cases ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none =>
    simp only [error,ho]
    exact mul_nonneg (by simpa only [mul_div_assoc] using mul_nonneg (show (0:ℝ) ≤ 4 by norm_num) hc) (mass_nonneg d t ω)
  | some o =>
    have ht := (StarCaps.deficit_comparison d hk t ω o ho).1
    have he := (StarCaps.dominant d hk t ω o ho).2
    change StarCaps.flex d t ω o ≤ (1+StarConstants.eps/EpochAlpha.ell k)*parentFlex d t ω o at he
    change parentFlex d t ω o/2 ≤ _ at ht
    have hh := mul_le_mul_of_nonneg_left (show parentFlex d t ω o ≤ 4*mass d t ω by linarith) hc
    simp only [error,ho]
    simp only [div_eq_mul_inv] at he hh ⊢
    nlinarith only [he,hh]

theorem required_holes (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d t ω ≤ q) :
    AllocationOutputs.excess (StarCaps.cap d t ω) q ≤ parentBeta d t ω*mass d t ω+error d t ω := by
  exact AllocationOutputs.required_holes (core d t ω) (coreInput d t ω) (parentFlex d t ω)
    (StarCaps.flex d t ω) (parentBeta d t ω) q (error d t ω)
    (core_nonneg d t ω) (by linarith [(parent_allowed d hk t ω).1])
    (error_nonneg d hk t ω) (parent_expand d hk t ω hq) (error_sum d hk t ω)

theorem alpha_nonneg (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : 0 ≤ alpha d t ω i :=
  (AlphaEmpty.state_interval (AlphaFiniteInput.alpha_state (alphaData d) t ω) i).1

theorem alpha_proportion (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) :
    mass d (t+1) ω*alpha d (t+1) ω i ≤
      (1+AlphaEmpty.eta (StarFeasibilityParameters.alphaParam d (t+1) ω) i)*coreInput d (t+1) ω i :=
  (AlphaFiniteInput.step (alphaData d) t ω).2.2.1 i

theorem alpha_supported (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) (hi : held d t ω i=0) :
    alpha d t ω i=0 := by
  have h := AlphaFiniteInput.alpha_state (alphaData d) t ω
  change AlphaEmpty.state (StarFeasibilityParameters.alphaParam d t ω) (alpha d t ω) at h
  have he := StarTrackers.alphaParam_active d StarConstants.delta StarConstants.ct StarConstants.multiplier t ω
  change AlphaEmpty.active (StarFeasibilityParameters.alphaParam d t ω)=_ at he
  have hn : i ∉ AlphaEmpty.active (StarFeasibilityParameters.alphaParam d t ω) := by
    rw [he,EpochParameters.mem_active,hi]
    exact lt_irrefl 0
  cases hp : StarFeasibilityParameters.alphaParam d t ω with
  | none => rw [hp] at h; rw [h]
  | some p => rw [hp] at h hn; exact h.2.1 i hn

theorem alpha_sum (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) (hi : 0 < held d t ω i) :
    (∑ j, alpha d t ω j)=1 := by
  have h := AlphaFiniteInput.alpha_state (alphaData d) t ω
  change AlphaEmpty.state (StarFeasibilityParameters.alphaParam d t ω) (alpha d t ω) at h
  have he := StarTrackers.alphaParam_active d StarConstants.delta StarConstants.ct StarConstants.multiplier t ω
  change AlphaEmpty.active (StarFeasibilityParameters.alphaParam d t ω)=_ at he
  have hm : i ∈ AlphaEmpty.active (StarFeasibilityParameters.alphaParam d t ω) := by
    rw [he,EpochParameters.mem_active]
    exact hi
  cases hp : StarFeasibilityParameters.alphaParam d t ω with
  | none => simp [hp,AlphaEmpty.active] at hm
  | some p => rw [hp] at h; exact h.2.2

theorem side_input_active (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (hi : i ∈ (StarFeasibilityParameters.sideParam d t ω).active) :
    SideFiniteInput.input (sideData d hk) t ω i=coreInput d t ω i := by
  change SyntheticCore.input (fun j => (input d i j).posterior t ω)
    (StarTrackers.sideFlags d StarConstants.delta t ω i)=_
  change i ∈ EpochSide.active (held d t ω) (epoch d StarConstants.delta t ω) at hi
  apply congrArg (SyntheticCore.input (fun j => (input d i j).posterior t ω))
  funext j
  exact ite_eq_left hi

theorem core_inactive (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) (hi : held d t ω i=0) :
    coreInput d t ω i=0 := by
  unfold coreInput
  exact SyntheticCore.no_flags _ (zero_flags d t ω i hi)

theorem side_nonneg (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    0 ≤ side d hk t ω i := (SideFiniteInput.tracker_state (sideData d hk) t ω).1 i

theorem side_supported (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (hi : i ∉ (StarFeasibilityParameters.sideParam d t ω).active) :
    side d hk t ω i=0 := (SideFiniteInput.tracker_state (sideData d hk) t ω).2.1 i hi

end UniformKServer.StarOutputData

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarOutputFeasibility
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                            
section

/-! Actual feasibility of both child-output formulas, at every positive time.
Regime inequalities are the literal hysteresis ranges. Degenerate active,
side, core and deficit values are not removed. -/
noncomputable section
namespace UniformKServer.StarOutputFeasibility
open Finset StarRanks StarSchedules StarLower StarOutputData
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def one (d : Data Ω ι k) (t : ℕ) (ω : Ω) (q : ℝ) : ι → ℝ :=
  AllocationOutputs.ruleOne (StarCaps.cap d t ω) (alpha d t ω) q

def two (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q : ℝ) (o : ι) : ι → ℝ :=
  AllocationOutputs.ruleTwo (StarCaps.cap d t ω) (side d hk t ω) q
    (deficit d StarConstants.delta t ω) o

theorem one_inactive (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q : ℝ) (i : ι)
    (hi : held d t ω i=0) : one d t ω q i=0 := by
  simp only [one,AllocationOutputs.ruleOne,StarCaps.inactive_cap d hk t ω i hi,
    alpha_supported d t ω i hi,mul_zero,sub_self]

theorem one_lower (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d (t+1) ω ≤ q)
    (hreg : deficit d StarConstants.delta (t+1) ω/2 ≤ StarOutputData.mass d (t+1) ω) (i : ι) :
    lower d (childBeta d (t+1) ω i) (t+1) ω i ≤ one d (t+1) ω q i := by
  by_cases ha : 0 < held d (t+1) ω i
  · rw [←child_expand]
    by_cases ho : EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω)=some i
    · exact AllocationOutputs.rule_one_dominant (core d (t+1) ω) (coreInput d (t+1) ω)
        (childFlex d (t+1) ω) (StarCaps.flex d (t+1) ω) (childBeta d (t+1) ω)
        (AlphaEmpty.eta (StarFeasibilityParameters.alphaParam d (t+1) ω)) (alpha d (t+1) ω)
        (parentBeta d (t+1) ω) q (error d (t+1) ω)
        (core_nonneg d (t+1) ω) (alpha_nonneg d (t+1) ω) (alpha_sum d (t+1) ω i ha)
        (by linarith [(parent_allowed d hk (t+1) ω).1]) (error_nonneg d hk (t+1) ω)
        (required_holes d hk (t+1) ω hq) (alpha_proportion d t ω) i
        (StarFeasibilityParameters.dominant_room d hk (t+1) ω i ho)
        (by simp only [error,ho]
            have h := flex_mono d hk (t+1) ω i
            change childFlex d (t+1) ω i ≤ parentFlex d (t+1) ω i at h
            linarith)
    · exact AllocationOutputs.rule_one_regular (core d (t+1) ω) (coreInput d (t+1) ω)
        (childFlex d (t+1) ω) (StarCaps.flex d (t+1) ω) (childBeta d (t+1) ω)
        (AlphaEmpty.eta (StarFeasibilityParameters.alphaParam d (t+1) ω)) (alpha d (t+1) ω)
        (parentBeta d (t+1) ω) q (error d (t+1) ω) (4*StarConstants.eps/EpochAlpha.ell k)
        (core_nonneg d (t+1) ω) (alpha_nonneg d (t+1) ω)
        (by have hb := (parent_allowed d hk (t+1) ω).1
            have he : 0 ≤ 4*StarConstants.eps/EpochAlpha.ell k := div_nonneg
              (by norm_num [StarConstants.eps]) (by linarith [EpochAlpha.ell_one k])
            linarith)
        (required_holes d hk (t+1) ω hq) (error_rule_one d hk (t+1) ω hreg)
        (alpha_proportion d t ω) i (StarFeasibilityParameters.regular_room d hk (t+1) ω i ha ho)
        (cap_child d hk (t+1) ω i)
  · have hz := le_antisymm (le_of_not_gt ha) (held_nonneg d (t+1) ω i)
    rw [one_inactive d hk (t+1) ω q i hz,(StarLower.inactive d _ (t+1) ω i hz).1]

theorem one_upper (d : Data Ω ι k) (t : ℕ) (ω : Ω) (q : ℝ) (i : ι) :
    one d t ω q i ≤ StarCaps.cap d t ω i :=
  AllocationOutputs.rule_one_upper _ _ _ (alpha_nonneg d t ω) i

theorem one_budget (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d t ω ≤ q) : (∑ i, one d t ω q i) ≤ q := by
  by_cases ha : ∃ i, 0 < held d t ω i
  · obtain ⟨i,hi⟩ := ha
    exact (AllocationOutputs.rule_one_budget (StarCaps.cap d t ω) (alpha d t ω) q
      (alpha_sum d t ω i hi)).le.trans (min_le_right _ _)
  · have hz : ∀ i, held d t ω i=0 := fun i => le_antisymm
      (le_of_not_gt (fun h => ha ⟨i,h⟩)) (held_nonneg d t ω i)
    simp only [one_inactive d hk t ω q _ (hz _),sum_const_zero]
    exact (parent_nonneg d hk t ω).trans hq

theorem side_upper (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    deficit d StarConstants.delta (t+1) ω*side d hk (t+1) ω i ≤
      childBeta d (t+1) ω i*coreInput d (t+1) ω i := by
  by_cases hi : i ∈ (StarFeasibilityParameters.sideParam d (t+1) ω).active
  · have h := (SideFiniteInput.step (sideData d hk) t ω).2.2.1 i
    rw [side_input_active d hk (t+1) ω i hi] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (StarFeasibilityParameters.side_room d hk (t+1) ω i hi) (core_nonneg d (t+1) ω i))
  · rw [side_supported d hk (t+1) ω i hi,mul_zero]
    exact mul_nonneg (by linarith [(child_allowed d hk (t+1) ω i).1]) (core_nonneg d (t+1) ω i)

theorem side_lower (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (o : ι)
    (ho : EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω)=some o)
    (hreg : StarOutputData.mass d (t+1) ω ≤ 2*deficit d StarConstants.delta (t+1) ω) (i : ι) (hi : i ≠ o) :
    (StarFeasibilityParameters.sideParam d (t+1) ω).b*coreInput d (t+1) ω i-
      deficit d StarConstants.delta (t+1) ω*AdaptiveSide.theta (StarFeasibilityParameters.sideParam d (t+1) ω) i*
        AdaptiveSide.offset (StarFeasibilityParameters.sideParam d (t+1) ω) i ≤
      deficit d StarConstants.delta (t+1) ω*side d hk (t+1) ω i := by
  by_cases ha : i ∈ (StarFeasibilityParameters.sideParam d (t+1) ω).active
  · have h := (SideFiniteInput.step (sideData d hk) t ω).2.2.2.1 hreg i
    rw [side_input_active d hk (t+1) ω i ha] at h
    change (StarFeasibilityParameters.sideParam d (t+1) ω).b*coreInput d (t+1) ω i-
      AdaptiveSide.theta (StarFeasibilityParameters.sideParam d (t+1) ω) i*
      AdaptiveSide.offset (StarFeasibilityParameters.sideParam d (t+1) ω) i*
      deficit d StarConstants.delta (t+1) ω ≤
      deficit d StarConstants.delta (t+1) ω*side d hk (t+1) ω i at h
    nlinarith only [h]
  · have hn : held d (t+1) ω i=0 := by
      have hh : ¬ 0 < held d (t+1) ω i := by
        intro hh
        apply ha
        change i ∈ EpochSide.active (held d (t+1) ω) (epoch d StarConstants.delta (t+1) ω)
        simp only [EpochSide.active,ho,mem_erase,EpochParameters.mem_active]
        exact ⟨hi,hh⟩
      exact le_antisymm (le_of_not_gt hh) (held_nonneg d (t+1) ω i)
    rw [core_inactive d (t+1) ω i hn,side_supported d hk (t+1) ω i ha]
    rw [AdaptiveSide.theta,DomainTransport.extend_supported _ _ i ha]
    simp

theorem two_lower (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d (t+1) ω ≤ q) (o : ι)
    (ho : EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω)=some o)
    (hreg : StarOutputData.mass d (t+1) ω ≤ 2*deficit d StarConstants.delta (t+1) ω) (i : ι) :
    lower d (childBeta d (t+1) ω i) (t+1) ω i ≤ two d hk (t+1) ω q o i := by
  rw [←child_expand]
  apply AllocationOutputs.rule_two_lower (core d (t+1) ω) (coreInput d (t+1) ω)
    (parentFlex d (t+1) ω) (childFlex d (t+1) ω) (StarCaps.flex d (t+1) ω)
    (childBeta d (t+1) ω) (side d hk (t+1) ω)
    (AdaptiveSide.theta (StarFeasibilityParameters.sideParam d (t+1) ω))
    (AdaptiveSide.offset (StarFeasibilityParameters.sideParam d (t+1) ω)) q
    (deficit d StarConstants.delta (t+1) ω) (parentBeta d (t+1) ω)
    (StarFeasibilityParameters.sideParam d (t+1) ω).b o
    (core_nonneg d (t+1) ω) (parent_expand d hk (t+1) ω hq)
    (ParentBeta.parameter_accuracy (parentInput d) StarConstants.delta_bounds.1 hk (t+1) ω).1
    (cap_child d hk (t+1) ω)
  · intro j hj
    apply (regular_flex d hk (t+1) ω j ?_).2
    rw [ho]
    exact fun h => hj (Option.some.inj h).symm
  · exact fun j _ => side_upper d hk t ω j
  · exact fun j hj => side_lower d hk t ω o ho hreg j hj
  · rw [child_expand]
    change _ ≤ RankData.coreCount (flags d (t+1) ω o)-parentBeta d (t+1) ω*coreInput d (t+1) ω o+
      FlexEstimates.trueFlex (input d o) (parentBeta d (t+1) ω) (t+1) ω-
        lower d (childBeta d (t+1) ω o) (t+1) ω o
    rw [←decomposition]
    exact StarFeasibilityParameters.side_slack d hk (t+1) ω o ho
  · linarith [(child_allowed d hk (t+1) ω o).1]

theorem two_upper (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q : ℝ) (o i : ι) :
    two d hk t ω q o i ≤ StarCaps.cap d t ω i :=
  AllocationOutputs.rule_two_upper _ _ _ _ _ _ (deficit_nonneg d StarConstants.delta t ω)
    (fun j _ => side_nonneg d hk t ω j)

theorem two_budget (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q : ℝ) (o : ι) :
    (∑ i, two d hk t ω q o i) ≤ q := AllocationOutputs.rule_two_budget ..

end UniformKServer.StarOutputFeasibility

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SwitchFinite
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Literal causal hysteresis under finite observation laws.  The old-rule
potential is filtered on every step, before the wholesale/reset decision. -/
noncomputable section
namespace UniformKServer.SwitchFinite
open Finset UniformKServer.AlphaFiniteInput UniformKServer.SwitchTracker
open scoped Classical
variable {Ω ι R : Type*} [Fintype Ω] [Fintype ι] [Fintype R]

def mass (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ := ∑ i, input d.core t ω i

def rule (d : Data Ω ι R) : ℕ → Ω → Rule
  | 0, ω => update .one (mass d 0 ω) (d.deficit 0 ω)
  | t+1, ω => update (if d.reset t ω then .one else rule d t ω)
      (mass d (t+1) ω) (d.deficit (t+1) ω)

def charge (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  if d.reset t ω then 0 else SwitchTracker.charge (rule d t ω) (mass d (t+1) ω) (d.deficit (t+1) ω)

theorem mass_nonneg (d : Data Ω ι R) (t : ℕ) (ω : Ω) : 0 ≤ mass d t ω :=
  sum_nonneg fun i _ => input_nonneg d.core t ω i

theorem rule_valid (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    valid (rule d t ω) (mass d t ω) (d.deficit t ω) := by
  cases t <;> exact update_valid _ (mass_nonneg d _ ω) (d.nonneg _ ω)

theorem mass_measurable (d : Data Ω ι R) (t : ℕ) {ω v : Ω}
    (h : (d.core.filtration t).r ω v) : mass d t ω=mass d t v := by
  unfold mass
  rw [input_measurable d.core t h]

theorem rule_measurable (d : Data Ω ι R) (t : ℕ) {ω v : Ω}
    (h : (d.core.filtration t).r ω v) : rule d t ω=rule d t v := by
  induction t with
  | zero => rw [rule,rule,mass_measurable d 0 h,d.measurable 0 ω v h]
  | succ t ih =>
    rw [rule,rule,d.reset_measurable t ω v h,ih (d.core.refines t ω v h),
      mass_measurable d (t+1) h,d.measurable (t+1) ω v h]

end UniformKServer.SwitchFinite

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarAllocator
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! The actual causal star allocator.  At time zero it uses the true lower
requirements, avoiding an unjustified feasibility claim for the arbitrary
initial minimizer states.  All subsequent outputs are the source's two rules. -/
noncomputable section
namespace UniformKServer.StarAllocator
open Finset StarRanks StarSchedules StarLower StarOutputData StarOutputFeasibility
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem wholesale_measurable (d : Data Ω ι k) (t : ℕ) {ω v : Ω}
    (h : (d.filtration (t+1)).r ω v) : StarCaps.wholesale d t ω=StarCaps.wholesale d t v := by
  apply CausalSchedules.reset_congr
  · intro s hs
    exact held_measurable d s (refining d hs h)
  · intro s hs
    exact refresh_measurable d StarConstants.delta s (refining d (by omega) h)

def switchData (d : Data Ω ι k) : SwitchFinite.Data Ω ι (Fin k) where
  core := alphaData d
  deficit := deficit d StarConstants.delta
  nonneg := deficit_nonneg d StarConstants.delta
  measurable := fun t _ _ h => deficit_measurable d StarConstants.delta t h
  reset := StarCaps.wholesale d
  reset_measurable := fun t _ _ h => wholesale_measurable d t h

def tag (d : Data Ω ι k) (t : ℕ) (ω : Ω) : SwitchTracker.Rule :=
  SwitchFinite.rule (switchData d) t ω

def ruleOutput (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q : ℝ) : ι → ℝ :=
  match EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none => one d t ω q
  | some o => match tag d t ω with
    | .one => one d t ω q
    | .two => two d hk t ω q o

def output (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q : ℝ) : ι → ℝ :=
  match t with
  | 0 => fun i => lower d (childBeta d 0 ω i) 0 ω i
  | t+1 => ruleOutput d hk (t+1) ω q

theorem tag_valid (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    SwitchTracker.valid (tag d t ω) (StarOutputData.mass d t ω) (deficit d StarConstants.delta t ω) :=
  SwitchFinite.rule_valid (switchData d) t ω

theorem rule_lower (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d (t+1) ω ≤ q) (i : ι) :
    lower d (childBeta d (t+1) ω i) (t+1) ω i ≤ ruleOutput d hk (t+1) ω q i := by
  have hv := tag_valid d (t+1) ω
  unfold ruleOutput
  cases ho : EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω) with
  | none =>
    apply one_lower d hk t ω hq
    simp only [deficit,ho,zero_div]
    exact mass_nonneg d (t+1) ω
  | some o =>
    cases hr : tag d (t+1) ω with
    | one => exact one_lower d hk t ω hq (by simpa only [hr,SwitchTracker.valid] using hv) i
    | two => exact two_lower d hk t ω hq o ho (by simpa only [hr,SwitchTracker.valid] using hv) i

theorem rule_upper (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q : ℝ) (i : ι) :
    ruleOutput d hk t ω q i ≤ StarCaps.cap d t ω i := by
  cases ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none => simpa only [ruleOutput,ho] using one_upper d t ω q i
  | some o =>
    cases hr : tag d t ω <;> simp only [ruleOutput,ho,hr]
    · exact one_upper d t ω q i
    · exact two_upper d hk t ω q o i

theorem rule_budget (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d t ω ≤ q) : (∑ i, ruleOutput d hk t ω q i) ≤ q := by
  cases ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none => simpa only [ruleOutput,ho] using one_budget d hk t ω hq
  | some o =>
    cases hr : tag d t ω <;> simp only [ruleOutput,ho,hr]
    · exact one_budget d hk t ω hq
    · exact two_budget d hk t ω q o

theorem lower_cap (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι) :
    lower d (childBeta d t ω i) t ω i ≤ StarCaps.cap d t ω i := by
  rw [decomposition]
  have h := cap_child d hk t ω i
  have hb : 0 ≤ childBeta d t ω i := by linarith [(child_allowed d hk t ω i).1]
  have hh := mul_nonneg hb (core_nonneg d t ω i)
  change _ ≤ RankData.coreCount (flags d t ω i)+StarCaps.flex d t ω i
  change FlexEstimates.trueFlex (input d i) (childBeta d t ω i) t ω ≤ _ at h
  linarith

theorem feasible (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q : ℝ}
    (hq : parentLower d t ω ≤ q) :
    (∀ i, lower d (childBeta d t ω i) t ω i ≤ output d hk t ω q i) ∧
    (∀ i, output d hk t ω q i ≤ StarCaps.cap d t ω i) ∧
    (∑ i, output d hk t ω q i) ≤ q := by
  cases t with
  | zero =>
    exact ⟨fun _ => le_rfl,lower_cap d hk 0 ω,
      (sum_le_sum (fun i _ => lower_mono d hk 0 ω i)).trans ((parent_dominates d hk 0 ω).trans hq)⟩
  | succ t => exact ⟨rule_lower d hk t ω hq,rule_upper d hk (t+1) ω q,rule_budget d hk (t+1) ω hq⟩

theorem cap_measurable (d : Data Ω ι k) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : StarCaps.cap d t ω=StarCaps.cap d t v := by
  funext i
  unfold StarCaps.cap StarCaps.flex
  rw [flag_measurable d t h,epoch_measurable d StarConstants.delta t h,
    upper_measurable d StarConstants.delta t h,flex_measurable d i _ _ t h]

theorem rule_measurable (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) (q : ℝ) : ruleOutput d hk t ω q=ruleOutput d hk t v q := by
  have htag : tag d t ω=tag d t v := SwitchFinite.rule_measurable (switchData d) t h
  have ha : alpha d t ω=alpha d t v := AlphaFiniteInput.alpha_measurable (alphaData d) t h
  have hs : side d hk t ω=side d hk t v := SideFiniteInput.tracker_measurable (sideData d hk) t h
  unfold ruleOutput one two
  rw [epoch_measurable d StarConstants.delta t h,htag,cap_measurable d t h,ha,hs,
    deficit_measurable d StarConstants.delta t h]

theorem measurable (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) (q : ℝ) : output d hk t ω q=output d hk t v q := by
  cases t with
  | zero => exact funext fun i => lower_measurable d 0 h i
  | succ t => exact rule_measurable d hk (t+1) h q

end UniformKServer.StarAllocator

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeAllocator
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Top-down propagation on the fixed finite tree, with literal causal star
outputs. Repeated and empty leaf counts are not excluded. -/
noncomputable section
namespace UniformKServer.TreeAllocator
open Finset TreeRounding TreeRankData
open scoped Classical
variable {Ω : Type*} [Fintype Ω] {n k : ℕ} {S : Shape n}

def amount (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (v : Vertex n) : ℝ :=
  if hv : v=0 then k else
    StarAllocator.output (star d (S.parent v)) hk t ω (amount d hk t ω (S.parent v)) ⟨v,hv,rfl⟩
termination_by v.val
decreasing_by exact S.earlier v hv

theorem root (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) : amount d hk t ω 0=k := by
  rw [amount,dite_eq_left rfl]

theorem child (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (v : Vertex n) (i : Children S v) :
    amount d hk t ω i.val=StarAllocator.output (star d v) hk t ω (amount d hk t ω v) i := by
  rcases i with ⟨u,hu,hp⟩
  subst v
  rw [amount,dite_eq_right hu]

theorem lower_le (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (v : Vertex n) :
    lower d v t ω ≤ amount d hk t ω v := by
  induction v using WellFounded.induction (measure Fin.val).wf with
  | h v ih =>
    by_cases hv : v=0
    · subst v
      rw [root]
      exact lower_bound d hk 0 t ω
    · let i : Children S (S.parent v) := ⟨v,hv,rfl⟩
      have hp := (parent_le_lower d hk (S.parent v) t ω).trans
        (ih (S.parent v) (S.earlier v hv))
      have h := (StarAllocator.feasible (star d (S.parent v)) hk t ω hp).1 i
      rw [child_lower] at h
      rw [←child d hk t ω (S.parent v) i] at h
      exact h

theorem parent_le (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (v : Vertex n) :
    StarLower.parentLower (star d v) t ω ≤ amount d hk t ω v :=
  (parent_le_lower d hk v t ω).trans (lower_le d hk t ω v)

theorem nonneg (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (v : Vertex n) :
    0 ≤ amount d hk t ω v := (lower_nonneg d hk v t ω).trans (lower_le d hk t ω v)

theorem budget (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (v : Vertex n) :
    (∑ i : Children S v, amount d hk t ω i.val) ≤ amount d hk t ω v := by
  simp only [child]
  exact (StarAllocator.feasible (star d v) hk t ω (parent_le d hk t ω v)).2.2

def allocation (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) : Allocation S k where
  amount := amount d hk t ω
  nonneg := nonneg d hk t ω
  park_nonneg := fun v => sub_nonneg.mpr (budget d hk t ω v)
  root := root d hk t ω

theorem measurable (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) {ω x : Ω}
    (hx : (d.filtration t).r ω x) (v : Vertex n) : amount d hk t ω v=amount d hk t x v := by
  induction v using WellFounded.induction (measure Fin.val).wf with
  | h v ih =>
    by_cases hv : v=0
    · subst v; rw [root,root]
    · conv_lhs => rw [amount]
      conv_rhs => rw [amount]
      rw [dite_eq_right hv,dite_eq_right hv,ih (S.parent v) (S.earlier v hv),
        StarAllocator.measurable (star d (S.parent v)) hk t hx]

end UniformKServer.TreeAllocator

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeCoverage
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! The allocation serves every request and is dominated by true posterior
counts. Positive parks therefore have validity witnesses; no impossible
history is used in either conclusion. -/
noncomputable section
namespace UniformKServer.TreeCoverage
open Finset TreeRounding TreeRankData
open scoped Classical
variable {Ω : Type*} [Fintype Ω] {n k : ℕ} {S : Shape n}

theorem nonroot_domination (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (v : Vertex n)
    (hv : v ≠ 0) : TreeAllocator.amount d hk t ω v ≤ 132*mean d t ω v := by
  let i : Children S (S.parent v) := ⟨v,hv,rfl⟩
  have hu := (StarAllocator.feasible (star d (S.parent v)) hk t ω
    (TreeAllocator.parent_le d hk t ω (S.parent v))).2.1 i
  have hc := StarCaps.cap_bound (star d (S.parent v)) hk t ω i
  have hs := child_size_bound d (S.parent v) i t ω
  rw [←TreeAllocator.child d hk t ω (S.parent v) i] at hu
  change TreeAllocator.amount d hk t ω v ≤ _ at hu
  change StarRanks.held (star d (S.parent v)) t ω i ≤ (11/10)*mean d t ω v at hs
  linarith

theorem domination (d : Data Ω S k) (hk : 1 ≤ k) (hroot : ∀ t x, d.count t x 0=k)
    (t : ℕ) (ω : Ω) (v : Vertex n) : TreeAllocator.amount d hk t ω v ≤ 132*mean d t ω v := by
  by_cases hv : v=0
  · subst v
    rw [TreeAllocator.root,root_mean d hroot]
    nlinarith [Nat.cast_nonneg (α:=ℝ) k]
  · exact nonroot_domination d hk t ω v hv

end UniformKServer.TreeCoverage

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreePosteriorRegions
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                           
section

/-! True posterior counts are exactly the mass of the current causal tree
region. This is an identity, not an auxiliary estimate assumed of a law. -/
noncomputable section
namespace UniformKServer.TreePosteriorRegions
open Finset TreeRounding TreeAncestry TreeLeaves ConditionalLaw
open scoped Classical
variable {X Ω : Type*} [Fintype X] [Fintype Ω] {n k : ℕ} {S : Shape n}

theorem domination (D : HiddenFlow.Data X Ω k) (M : TreeCountData.Map D S) (hk : 1 ≤ k)
    (t : ℕ) (ω : Ω) (u : Vertex n) :
    TreeAllocator.amount (TreeCountData.data D M) hk t ω u ≤
      132*ParkCapacity.mass (HiddenFlow.current D t ω) (region D M t ω u) := by
  rw [←mean_mass]
  exact TreeCoverage.domination _ hk (TreeCountData.root D M) t ω u

end UniformKServer.TreePosteriorRegions

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionTree
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! The actual fixed full-prefix tree associated with the literal partition.
The alphabet, tree and independent tape domains are instance-dependent but
law- and horizon-independent (apart from a finite tape restriction). -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

abbrev Label (X : Type) [Fintype X] (C : ℝ) (k : ℕ) :=
  LevelMap.HeavySlot X ⊕ ((i : Fin (height k)) × TierLabeledKeys.Slot X (TierParameters.cutoff C (DyadicTiers.value i.val))) ⊕ X

abbrev LevelTape (A : ActualPartitions.Config X) (k N j : ℕ) :=
  (Fin N→HeavyRadius.Sample (X:=X) (GeometricMass.radius A.R A.q j)) ×
    (∀ i : Fin (height k), TierLifetimes.Tape N × (Fin N→TierRadius.Sample (X:=X)
      (Real.log (1+(TierParameters.cutoff A.C (DyadicTiers.value i.val):ℝ)^2)) (GeometricMass.radius A.R A.q j)))
abbrev Tape (A : ActualPartitions.Config X) (k N J : ℕ) := ∀ j : Fin J, LevelTape A k N j.val
abbrev size (A : ActualPartitions.Config X) (k J : ℕ) := PrefixTree.size (Label X A.C k) J
def shape (A : ActualPartitions.Config X) (k J : ℕ) : Shape (size A k J) := PrefixTree.shape (Label X A.C k) J

def word (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (p : X) : Fin J→Label X A.C k := fun j =>
  ((A.input (N:=N) (J:=J) D hk ω).level j.val).data.key
    ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) t p

def map (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) : TreeCountData.Map D (shape A k J) where
  toLeaf t ω p := PrefixTree.endpoint (word A D hk z t ω p)
  leaf t ω p := PrefixTree.endpoint_leaf _
  causal t ω v he := by
    funext p
    apply congrArg PrefixTree.endpoint
    funext j
    exact A.key_measurable D hk ω v t j.val he (z j) p

def region (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J)) : Finset X :=
  TreePosteriorRegions.region D (map A D hk z) t ω v

theorem nested (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (u v : Vertex (size A k J))
    (huv : descends (shape A k J) u v) : region A D hk z t ω v⊆region A D hk z t ω u := by
  intro p hp
  simp only [region,TreePosteriorRegions.region,mem_filter,mem_univ,true_and] at hp ⊢
  exact huv.trans hp

theorem region_prefix (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J)) (p : X)
    (hp : p∈region A D hk z t ω v) :
    v=PrefixTree.atLevel (word A D hk z t ω p) (depth (shape A k J) v) (PrefixTree.depth_bound v) :=
  PrefixTree.desc_endpoint _ v (mem_filter.mp hp).2

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionGeometry
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                        
section

/-! Actual prefix region geometry and the shared parked subtree capacity. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

omit [MetricSpace X] in
theorem depth_positive (A : ActualPartitions.Config X) (v : Vertex (size A k J)) (hv : v≠0) :
    0<depth (shape A k J) v := by rw [depth_child v hv]; omega

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionAnchors
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! Literal last-key representatives and validity from actual posterior domination. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def lastLabel (A : ActualPartitions.Config X) (v : Vertex (size A k J)) : Label X A.C k :=
  lastWord (Sum.inr (Sum.inr A.base)) (PrefixTree.chart (Label X A.C k) J v)

omit [MetricSpace X] in
theorem last_at (A : ActualPartitions.Config X) (p : Fin J→Label X A.C k)
    (d : ℕ) (hd : d≤J) (hp : 0<d) :
    lastLabel A (PrefixTree.atLevel p d hd)=p ⟨d-1,by omega⟩ := by
  calc
    _ = lastWord (Sum.inr (Sum.inr A.base)) (PrefixTree.wordPrefix p d hd) :=
      congrArg (lastWord (Sum.inr (Sum.inr A.base)))
        ((PrefixTree.chart (Label X A.C k) J).apply_symm_apply _)
    _ = _ := by
      dsimp only [lastWord,PrefixTree.wordPrefix]
      split_ifs
      rfl

theorem last_region (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J)) (hv : v≠0)
    (p : X) (hp : p∈region A D hk z t ω v) :
    lastLabel A v=word A D hk z t ω p
      ⟨depth (shape A k J) v-1,by have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v; have := depth_positive A v hv; omega⟩ := by
  have hd := depth_positive A v hv
  have he := region_prefix A D hk z t ω v p hp
  calc
    lastLabel A v=lastLabel A (PrefixTree.atLevel (word A D hk z t ω p)
      (depth (shape A k J) v) (PrefixTree.depth_bound v)) := congrArg (lastLabel A) he
    _ = _ := last_at A _ _ _ hd

def anchor (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J)) : X :=
  if hv : v=0 then A.base else
    let j : Fin J := ⟨depth (shape A k J) v-1,by have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v; have := depth_positive A v hv; omega⟩
    ((A.input (N:=N) (J:=J) D hk ω).level j.val).data.anchor (z j) t (lastLabel A v)

theorem anchor_distance (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J)) (hv : v≠0)
    (p : X) (hp : p∈region A D hk z t ω v) :
    dist p (anchor A D hk z t ω v)≤20*radius A (depth (shape A k J) v) := by
  let j : Fin J := ⟨depth (shape A k J) v-1,by have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v; have := depth_positive A v hv; omega⟩
  have he := last_region A D hk z t ω v hv p hp
  rw [anchor,dite_eq_right hv]
  change dist p (((A.input (N:=N) (J:=J) D hk ω).level j.val).data.anchor (z j) t (lastLabel A v))≤_
  erw [he]
  have hh := LevelMap.Data.covers ((A.input (N:=N) (J:=J) D hk ω).level j.val).data
    ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) t p
  change dist p _≤20*(A.R*A.q^(j.val+1)) at hh
  have hj : j.val+1=depth (shape A k J) v := by dsimp [j]; have := depth_positive A v hv; omega
  simpa only [word,hj,radius] using hh

theorem witness (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J))
    (hp : 0<TreeAllocator.amount (TreeCountData.data D (map A D hk z)) (by omega) t ω v) :
    (region A D hk z t ω v).Nonempty := by
  by_contra he
  have hz := Finset.not_nonempty_iff_eq_empty.mp he
  have hd := TreePosteriorRegions.domination D (map A D hk z) (by omega) t ω v
  change _≤132*ParkCapacity.mass (HiddenFlow.current D t ω) (region A D hk z t ω v) at hd
  rw [hz,ParkCapacity.mass,sum_empty,mul_zero] at hd
  linarith

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochSideCharge
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Prepared side jumps: no parameter drift is charged at unchanged held
coordinates. Wholesale jumps use the actual prepared feasibility inequality. -/
noncomputable section
namespace UniformKServer.EpochSideCharge
open Finset UniformKServer.AdaptiveSide UniformKServer.EpochSide
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem whole {p q : Config ι} (hp : valid p) (hq : valid q)
    (B v : ι → ℝ) {D : ℝ} (hD : 0 ≤ D) (hB : ∀ i, 0 ≤ B i)
    (hv : DomainTransport.domain q.active 11 v)
    (hf : ∀ i, D*v i ≤ 5*B i) :
    |potential q B D v-potential p B D v| ≤ 6*(slope p+slope q)*(∑ i, B i) := by
  unfold potential SideTracker.potential
  rw [←sum_sub_distrib,mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  have hp' := SideParameterChanges.coordinate_bound_all hp i (hv.1 i) (coordinate_le_sum hv i) (B:=B i) (D:=D)
  have hq' := SideParameterChanges.coordinate_bound_all hq i (hv.1 i) (coordinate_le_sum hv i) (B:=B i) (D:=D)
  rw [abs_of_nonneg hD,abs_of_nonneg (hB i)] at hp' hq'
  have hp'' := mul_le_mul_of_nonneg_left (hf i) (slope_nonneg hp)
  have hq'' := mul_le_mul_of_nonneg_left (hf i) (slope_nonneg hq)
  exact (abs_sub _ _).trans (by nlinarith)

theorem jump {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i) (p : ℕ → Bool)
    (ell cw : ℝ) (b : ℕ → ℝ)
    (hb : ∀ t, SideReferenceSchedule.reset a p t=false → b t=b (t+1))
    (hp : ∀ t, AdaptiveSide.valid (param a p ell cw b t)) (t : ℕ) (B v : ι → ℝ)
    {D : ℝ} (hD : 0 ≤ D) (hB : ∀ i, 0 ≤ B i) (hBb : ∀ i, B i ≤ 40*a (t+1) i)
    (hv : DomainTransport.domain (param a p ell cw b (t+1)).active 11 v)
    (hf : ∀ i, D*v i ≤ ((param a p ell cw b t).b+theta (param a p ell cw b t) i)*B i) :
    |potential (param a p ell cw b (t+1)) B D v-potential (param a p ell cw b t) B D v| ≤
      480*(2000*(ell/cw+1))*(EpochAlphaCharge.sizeCharge (a t) (a (t+1))+
        SideReferenceSchedule.wholesale a p t) := by
  have hK : 0 ≤ 2000*(ell/cw+1) := slope_nonneg (hp t)
  have hprep := SideParameterChanges.prepared_upper (hp t) B v D hB hf
  by_cases hr : SideReferenceSchedule.reset a p t=true
  · have hh := whole (hp t) (hp (t+1)) B v hD hB hv hprep
    have hsb := sum_le_sum (s:=univ) (fun i _ => hBb i)
    rw [←mul_sum] at hsb
    change _ ≤ 40*EpochGeometry.total (a (t+1)) at hsb
    have hmul := mul_le_mul_of_nonneg_left hsb hK
    have hsz := mul_nonneg hK (EpochAlphaCharge.size_nonneg (ha t) (ha (t+1)))
    have ht := mul_nonneg hK (EpochGeometry.total_nonneg (ha t))
    change |potential (param a p ell cw b (t+1)) B D v-potential (param a p ell cw b t) B D v| ≤
      6*(2000*(ell/cw+1)+2000*(ell/cw+1))*(∑ i, B i) at hh
    rw [SideReferenceSchedule.wholesale,ite_eq_left hr]
    nlinarith
  · have hr' := Bool.eq_false_iff.mpr hr
    have he := EpochAlphaCharge.not_reset_base hr'
    have hh := SideParameterChanges.parameter_jump (hp t) (hp (t+1))
      (congrArg EpochGeometry.total he) rfl rfl (hb t hr') B v hD hB hv hprep
    have hsp : (∑ i, if SideParameterChanges.size (param a p ell cw b t) i=
        SideParameterChanges.size (param a p ell cw b (t+1)) i then 0 else B i) ≤
        ∑ i, if a t i=a (t+1) i then 0 else B i := by
      apply sum_le_sum
      intro i _
      by_cases hi : a t i=a (t+1) i
      · have hj := size_same (ha t) (ha (t+1)) he ell cw (b t) (b (t+1)) hi
        change SideParameterChanges.size (param a p ell cw b t) i=
          SideParameterChanges.size (param a p ell cw b (t+1)) i at hj
        simp only [ite_eq_left hi,ite_eq_left hj,le_refl]
      · simp only [ite_eq_right hi]
        split_ifs
        · exact hB i
        · exact le_rfl
    have hsp' := (hsp.trans (EpochAlphaCharge.sparse (ha t) hBb))
    have hmul := mul_le_mul_of_nonneg_left hsp' hK
    change |potential (param a p ell cw b (t+1)) B D v-potential (param a p ell cw b t) B D v| ≤
      6*(2000*(ell/cw+1)+2000*(ell/cw+1))*_ at hh
    rw [SideReferenceSchedule.wholesale,ite_eq_right hr,add_zero]
    nlinarith

end UniformKServer.EpochSideCharge

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochSideBudget
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Summed actual side parameter jumps, including wholesale epochs, with no
per-epoch additive loss. -/
noncomputable section
namespace UniformKServer.EpochSideBudget
open Finset UniformKServer.EpochSide
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem charge_budget {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i) (p : ℕ → Bool)
    {K : ℝ} (hK : 0 ≤ K) (H : ℕ) :
    (∑ t ∈ range H, 480*K*(EpochAlphaCharge.sizeCharge (a t) (a (t+1))+
      SideReferenceSchedule.wholesale a p t)) ≤
      97920*K*(∑ t ∈ range H, EpochAlphaCharge.sizeCharge (a t) (a (t+1)))+
      480*K*(∑ t ∈ range H, if p t then EpochGeometry.total (a t)+EpochGeometry.total (a (t+1)) else 0) := by
  have hV := sum_le_sum (s:=range H) (fun t _ => EpochAlphaBudget.variation_le (ha t) (ha (t+1)))
  have hW := SideReferenceSchedule.wholesale_budget ha p H
  have hV' := mul_le_mul_of_nonneg_left hV hK
  have hW' := mul_le_mul_of_nonneg_left hW hK
  simp only [←mul_sum,sum_add_distrib]
  nlinarith

theorem jump_budget {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i) (p : ℕ → Bool)
    (ell cw : ℝ) (b : ℕ → ℝ)
    (hb : ∀ t, SideReferenceSchedule.reset a p t=false → b t=b (t+1))
    (hp : ∀ t, AdaptiveSide.valid (param a p ell cw b t))
    (B v : ℕ → ι → ℝ) (D : ℕ → ℝ) (hD : ∀ t, 0 ≤ D t)
    (hB : ∀ t i, 0 ≤ B t i) (hBb : ∀ t i, B t i ≤ 40*a (t+1) i)
    (hv : ∀ t, DomainTransport.domain (param a p ell cw b (t+1)).active 11 (v t))
    (hf : ∀ t i, D t*v t i ≤ ((param a p ell cw b t).b+AdaptiveSide.theta (param a p ell cw b t) i)*B t i)
    (H : ℕ) :
    (∑ t ∈ range H, |AdaptiveSide.potential (param a p ell cw b (t+1)) (B t) (D t) (v t)-
        AdaptiveSide.potential (param a p ell cw b t) (B t) (D t) (v t)|) ≤
      97920*(2000*(ell/cw+1))*(∑ t ∈ range H, EpochAlphaCharge.sizeCharge (a t) (a (t+1)))+
      480*(2000*(ell/cw+1))*(∑ t ∈ range H, if p t then EpochGeometry.total (a t)+EpochGeometry.total (a (t+1)) else 0) := by
  exact (sum_le_sum (s:=range H) fun t _ => EpochSideCharge.jump ha p ell cw b hb hp t
    (B t) (v t) (hD t) (hB t) (hBb t) (hv t) (hf t)).trans
    (charge_budget ha p (AdaptiveSide.slope_nonneg (hp 0)) H)

end UniformKServer.EpochSideBudget

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionMovement
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                        
section

/-! Movement of the actual allocation on the actual common tree, reduced to
literal coordinate-key edits. All addends are uniform in hidden law/horizon. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def weight (A : ActualPartitions.Config X) (v : Vertex (size A k J)) : ℝ :=
  radius A (depth (shape A k J) v)

omit [MetricSpace X] in
theorem weight_separated (A : ActualPartitions.Config X) (v : Vertex (size A k J)) (hv : v≠0) :
    22*weight A v≤weight A ((shape A k J).parent v) := by
  unfold weight
  rw [depth_child v hv]
  exact radius_step A _

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualSizeBudget
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! The fixed-slot entropy refresh budget, instantiated with actual keys and
counted coupled hidden members, independent of the number of time steps. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry RankTracking TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def sizeEndpoint (A : ActualPartitions.Config X) (k J : ℕ) : ℝ :=
  (∑ j : Fin J,GeometricMass.radius A.R A.q j.val)*(Fintype.card (Label X A.C k):ℝ)*
    (288*(k+1)*(1+KeySizeTracker.ell (k+1)))

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyAnchorGeometry
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                          
section

/-! Literal moving-label geometry and potential release for one heavy update. -/
noncomputable section
namespace UniformKServer.HeavyProcess
open Finset HeavyRecords
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}

theorem moved_step (S T : State X Λ r) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X<Fintype.card Λ)
    (h : Prop) (x : X) (R : ℝ) (hR : R∈Set.Icc (16*r) (20*r)) (l : Λ)
    (ho : l∈S.present) (hn : l∈(step S T hr hΛ h x R hR).present)
    (hm : S.center l≠(step S T hr hΛ h x R hR).center l) :
    h ∧ (step S T hr hΛ h x R hR).center l=x ∧ 8*r<dist (S.center l) x ∧
      dist (S.center l) x≤40*r ∧
      ∀ p,covers (step S T hr hΛ h x R hR) l p↔dist x p≤R := by
  unfold step at hn hm ⊢
  split_ifs at hn hm ⊢ with ht
  · have he : l=chosen S x R (fresh S T hr hΛ) := by
      by_contra hl
      exact hm (by simp only [HeavyRecords.insert,Function.update_of_ne hl])
    have hd := ht.2 (S.center l) (mem_image.mpr ⟨l,ho,rfl⟩)
    have hu := reused_distance S hr x R hR _ (fresh_absent S T hr hΛ).1 l ho hn
    have ha : (HeavyRecords.insert S hr x R hR (fresh S T hr hΛ) (fresh_absent S T hr hΛ).1).center l=x := by
      simp only [HeavyRecords.insert,he,Function.update_self]
    rw [ha] at hu
    refine ⟨ht.1,ha,by simpa only [dist_comm] using hd,hu,?_⟩
    intro p
    rw [covers_insert_iff]
    have hs := chosen_not_survivor S hr x R hR.2 (fresh S T hr hΛ) (fresh_absent S T hr hΛ).1
    simp only [he,hs,true_and,false_and,or_false]
  · exact (hm rfl).elim

theorem release (S T : State X Λ r) (hr : 0 < r) (hΛ : 2*Fintype.card X<Fintype.card Λ)
    (h : Prop) (x : X) (R : ℝ) (hR : R∈Set.Icc (16*r) (20*r)) (l : Λ)
    (ho : l∈S.present) (hn : l∈(step S T hr.le hΛ h x R hR).present)
    (hm : S.center l≠(step S T hr.le hΛ h x R hR).center l)
    (μ : X→ℝ) (hμ : ∀ p,0≤μ p) (γ δ b u : ℝ) (hγ : γ<1) (hδ : δ≤1/100)
    (hb : 0≤b) (hu : 0<u)
    (hH : 1≤GeometricMass.mass μ x (γ*r))
    (hh : h→GeometricMass.mass μ x (51200*r)≤(1+δ)*GeometricMass.mass μ x (γ*r))
    (hd : u≤(6/5)*(1+∑ p∈univ.filter (covers (step S T hr.le hΛ h x R hR) l),μ p)) :
    r*b/u*(∑ p∈univ.filter (covers (step S T hr.le hΛ h x R hR) l),μ p*
      (AnchorRamp.value r ((step S T hr.le hΛ h x R hR).center l) p-AnchorRamp.value r (S.center l) p))≤
      -(1/4)*r*b := by
  obtain ⟨htrue,ha,hfar,_hclose,hcovers⟩ := moved_step S T hr.le hΛ h x R hR l ho hn hm
  let C := univ.filter (covers (step S T hr.le hΛ h x R hR) l)
  have hsub : AnchorRamp.ball x (γ*r)⊆C := by
    intro p hp
    apply mem_filter.mpr
    refine ⟨mem_univ _,(hcovers p).mpr ?_⟩
    have hg : γ*r≤R := by nlinarith [hR.1]
    exact (mem_filter.mp hp).2.trans hg
  have houter : C⊆AnchorRamp.ball x (51200*r) := by
    intro p hp
    exact mem_filter.mpr ⟨mem_univ _,((hcovers p).mp (mem_filter.mp hp).2).trans (by nlinarith [hR.2])⟩
  have hc : AnchorRamp.mass μ C≤GeometricMass.mass μ x (51200*r) := by
    rw [←geom_mass]
    exact sum_le_sum_of_subset_of_nonneg houter (fun p _ _=>hμ p)
  have hc' : AnchorRamp.mass μ C≤(1+δ)*AnchorRamp.mass μ (AnchorRamp.ball x (γ*r)) := by
    rw [geom_mass]
    exact hc.trans (hh htrue)
  have hdrop := AnchorRamp.integral_drop μ hμ C r γ δ hr hγ (S.center l) x hfar hsub hc'
  have hden : u≤(6/5)*(2+δ)*AnchorRamp.mass μ (AnchorRamp.ball x (γ*r)) := by
    rw [geom_mass] at hc' ⊢
    change u≤(6/5)*(1+AnchorRamp.mass μ C) at hd
    nlinarith only [hd,hc',hH]
  simpa only [ha] using AnchorRamp.payment r b u _ _ δ hr.le hb hu (by rw [geom_mass]; linarith) hδ hden hdrop

end UniformKServer.HeavyProcess

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelAnchorRelease
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

/-! The actual persistent level process releases potential on every retained
slot whose center moves. No independent event-conditional expectation is used. -/
noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

theorem anchor_release (D : LevelMap.Data X N H) (is : List (Fin H))
    (z : Tape D) (t : ℕ) (l : HeavySlot X)
    (ho : l∈(D.heavyState z.1 t).present) (hn : l∈(D.heavyState z.1 (t+1)).present)
    (hm : (D.heavyState z.1 t).center l≠(D.heavyState z.1 (t+1)).center l)
    (μ : X→ℝ) (hμ : ∀ p,0≤μ p) (γ δ b u : ℝ) (hγ : γ<1) (hδ : δ≤1/100)
    (hb : 0≤b) (hu : 0<u)
    (hH : 1≤GeometricMass.mass μ (D.point t) (γ*D.r))
    (hh : D.heavyFlag t→GeometricMass.mass μ (D.point t) (51200*D.r)≤
      (1+δ)*GeometricMass.mass μ (D.point t) (γ*D.r))
    (hd : u≤(6/5)*(1+∑ p∈univ.filter (fun p=>D.key is z (t+1) p=Sum.inl l),μ p)) :
    D.r*b/u*(∑ p∈univ.filter (fun p=>D.key is z (t+1) p=Sum.inl l),μ p*
      (AnchorRamp.value D.r ((D.heavyState z.1 (t+1)).center l) p-
       AnchorRamp.value D.r ((D.heavyState z.1 t).center l) p))≤-(1/4)*D.r*b := by
  have he : univ.filter (fun p=>D.key is z (t+1) p=Sum.inl l)=
      univ.filter (HeavyRecords.covers (D.heavyState z.1 (t+1)) l) := by
    apply filter_congr
    intro p _
    exact key_heavy_iff D is z (t+1) p l
  rw [he] at hd ⊢
  exact HeavyProcess.release (D.heavyState z.1 t)
    (HeavyProcess.runPair D.base D.positive.le (by simp [HeavySlot]) D.heavyFlag D.point
      (HeavyProcess.radiusStream D.r N z.1) (HeavyProcess.radiusStream_bounds D.r D.positive.le N z.1) t).1
    D.positive (by simp [HeavySlot]) (D.heavyFlag t) (D.point t)
    (HeavyProcess.radiusStream D.r N z.1 t) (HeavyProcess.radiusStream_bounds D.r D.positive.le N z.1 t)
    l ho hn hm μ hμ γ δ b u hγ hδ hb hu hH hh hd

end UniformKServer.LevelMap.Data

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualAnchorTravel
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

/-! Literal metric movement of retained heavy anchors, weighted by the new
parked mass. This is the travel used when projecting rounded tree servers. -/
noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

theorem anchor_distance (D : LevelMap.Data X N H) (z : Tape D) (t : ℕ)
    (l : HeavySlot X) (ho : l∈(D.heavyState z.1 t).present)
    (hn : l∈(D.heavyState z.1 (t+1)).present)
    (hm : (D.heavyState z.1 t).center l≠(D.heavyState z.1 (t+1)).center l) :
    dist ((D.heavyState z.1 t).center l) ((D.heavyState z.1 (t+1)).center l) ≤ 40*D.r := by
  have h := HeavyProcess.moved_step (D.heavyState z.1 t)
    (HeavyProcess.runPair D.base D.positive.le (by simp [HeavySlot]) D.heavyFlag D.point
      (HeavyProcess.radiusStream D.r N z.1) (HeavyProcess.radiusStream_bounds D.r D.positive.le N z.1) t).1
    D.positive.le (by simp [HeavySlot]) (D.heavyFlag t) (D.point t)
    (HeavyProcess.radiusStream D.r N z.1 t) (HeavyProcess.radiusStream_bounds D.r D.positive.le N z.1 t)
    l ho hn hm
  have ha : (D.heavyState z.1 (t+1)).center l=D.point t := h.2.1
  rw [ha]
  exact h.2.2.2.1

end UniformKServer.LevelMap.Data

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FlowAuxiliary
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Linear adapted auxiliary potentials commute with posterior filtering. -/
namespace UniformKServer.PilotEdits
open Finset
open scoped Classical
variable {X Ω : Type} [Fintype X] [Fintype Ω] {k : ℕ}

theorem linear_edits (F : Flow X Ω k) (H : ℕ) (b : ℕ→Ω→X→ℝ) (M : ℝ)
    (hb : ∀ t ω p,0≤b t ω p ∧ b t ω p≤M)
    (hmeas : ∀ t ω v,(F.filtration t).r ω v→b t ω=b t v)
    (cost allowance : ℕ→Ω→ℝ)
    (hstep : ∀ t<H,∀ ω,cost t ω+linearPotential (F.post (t+1) ω) (b (t+1) ω)-
      linearPotential (F.filtered t ω) (b t ω)≤allowance t ω) :
    (∑ t∈range H,average F.weight (cost t))≤
      (∑ t∈range H,average F.weight (allowance t))+k*M := by
  let Φ : ℕ→ℝ := fun t=>average F.weight (fun ω=>linearPotential (F.post t ω) (b t ω))
  have hs (t : ℕ) (ht : t<H) : average F.weight (cost t)+Φ (t+1)-Φ t≤average F.weight (allowance t) := by
    have h := average_mono F.weight _ _ F.weight_nonneg (hstep t ht)
    rw [average_sub,average_add,linear_filtering F t (b t) (hmeas t)] at h
    exact h
  have htel (T : ℕ) (hT : T≤H) :
      (∑ t∈range T,average F.weight (cost t))+Φ T≤Φ 0+(∑ t∈range T,average F.weight (allowance t)) := by
    induction T with
    | zero => simp
    | succ T ih =>
      have h := ih (by omega)
      have ht := hs T (by omega)
      rw [sum_range_succ,sum_range_succ]
      linarith
  have hn : 0≤Φ H := sum_nonneg (fun ω _=>mul_nonneg (F.weight_nonneg ω) (linear_bounds F H ω (b H ω) M (hb H ω)).1)
  have hi : Φ 0≤k*M := by
    have h := average_mono F.weight _ (fun _=>(k:ℝ)*M) F.weight_nonneg
      (fun ω=>(linear_bounds F 0 ω (b 0 ω) M (hb 0 ω)).2)
    simpa only [Φ,average,←sum_mul,F.weight_total,one_mul] using h
  have h := htel H le_rfl
  linarith

end UniformKServer.PilotEdits

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotFamily
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Uniform finite pilot family constants: the tier weights sum independently
of the number of tiers and of k. -/
namespace UniformKServer.PilotFamily
open Finset PilotEdits

theorem weight_sum (k : ℕ) : (∑ i : Index k, weight i)≤3 := by
  rw [Fintype.sum_option]
  change 1+(∑ i : Fin (DyadicTiers.last (Real.log k)+1), Real.exp (-DyadicTiers.value i.val))≤3
  rw [Fin.sum_univ_eq_sum_range (fun i => Real.exp (-DyadicTiers.value i))]
  linarith [DyadicTiers.exponential_sum (DyadicTiers.last (Real.log k)+1)]

theorem rate_bound (P : TierPilot.Parameters) (k : ℕ) :
    (∑ i : Index k, weight i*rate (template P i)) ≤ rateBound P := by
  rw [Fintype.sum_option]
  simp only [weight,template,one_mul]
  rw [←sum_mul,Fin.sum_univ_eq_sum_range (fun i => Real.exp (-DyadicTiers.value i))]
  have h := mul_le_mul_of_nonneg_right (DyadicTiers.exponential_sum (DyadicTiers.last (Real.log k)+1))
    (rate_nonneg (shortTemplate P))
  dsimp only [rateBound]
  linarith

end UniformKServer.PilotFamily

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualPilot
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The global pilot finance ledger for the literal partition. Constants do not
 depend on the input law, time horizon, or the number of scales. -/
namespace UniformKServer.ActualPartitions.Config
open Finset PilotEdits PilotCompact
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem pilot_finance (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k) (H : ℕ) :
    (∑ t∈range H, average D.weight (A.totalPilotCharge (N:=N) (J:=J) D hk t))≤
      (∑ i : PilotFamily.Index k, PilotFamily.weight i*rate (PilotFamily.template A.P i)) *
        (1+Real.log (k+1))*(∑ t∈range H, average D.weight (moverCost (HiddenFlow.flow D) t)) +
      2*k*(∑ i : PilotFamily.Index k, PilotFamily.weight i)*(∑ j∈range J, GeometricMass.radius A.R A.q j) := by
  have hτ : 2≤A.q⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ A.q_pos).mpr
    linarith [A.q_small]
  have he := pilot_edits hk (HiddenFlow.flow D) (PilotFamily.template A.P) PilotFamily.weight
    PilotFamily.weight_nonneg (A.R*A.q^J) A.q⁻¹ (mul_pos A.R_pos (pow_pos A.q_pos _)) hτ J H
    (A.pilotParameter (N:=N) (J:=J) D hk)
    (A.pilot_bounds D hk) (A.pilot_lip D hk)
    (fun t i j ω v h => A.pilot_measurable D hk t ω v h i j)
    (A.totalPilotCharge (N:=N) (J:=J) D hk)
    (fun t ω => sum_nonneg fun i _ => sum_nonneg fun j _ => A.pilot_charge_nonneg D hk t ω i j)
    (A.total_pilot_payment D hk)
  have hs : (∑ j∈range J, (A.R*A.q^J)*(A.q⁻¹)^j)=∑ j∈range J, GeometricMass.radius A.R A.q j := by
    calc
      _ = ∑ j∈range J, GeometricMass.radius A.R A.q (J-1-j) :=
        sum_congr rfl fun j hj => (GeometricMass.radius_reverse A.R A.q A.q_pos.ne' J j (mem_range.mp hj)).symm
      _ = _ := GeometricMass.reverse_sum _ _
  simpa only [hs,HiddenFlow.flow] using he

end UniformKServer.ActualPartitions.Config

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualEditFinance
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Integrated height-free key edits, financed by actual posterior pilots. -/
namespace UniformKServer.ActualPartitions.Config
open Finset PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem edit_finance (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k) :
    (∑ t∈range N,average D.weight (A.keyEditCost (N:=N) (J:=J) D hk t))≤
      A.editBound*(1+Real.log (k+1))*(∑ t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t))+
      A.editEndpoint k J := by
  let F := HiddenFlow.flow D
  let Q := ∑ t∈range N,average D.weight (moverCost F t)
  have hQ : 0≤Q := sum_nonneg (fun t _=>sum_nonneg (fun ω _=>mul_nonneg (D.positive ω).le
    (sum_nonneg (fun p _=>mul_nonneg (F.mover_nonneg t ω p) dist_nonneg))))
  have he := linear_edits F N (A.auxiliary (N:=N) (J:=J) D hk) (A.auxiliaryCap k J)
    (A.auxiliary_bounds D hk) (A.auxiliary_measurable D hk)
    (A.keyEditCost (N:=N) (J:=J) D hk)
    (fun t ω=>147*A.totalPilotCharge (N:=N) (J:=J) D hk t ω+A.editRate*(1+Real.log k)*moverCost F t ω)
    (fun t ht ω=>A.key_mass_step D hk ω ⟨t,ht⟩)
  simp only [average_add,average_smul,sum_add_distrib,←mul_sum] at he
  have hp := A.pilot_finance (N:=N) (J:=J) D hk N
  have hl : 0≤1+Real.log (k+1) := by
    have h : (1:ℝ)≤k+1 := by have := Nat.cast_nonneg (α:=ℝ) k; linarith
    linarith [Real.log_nonneg h]
  have hr := mul_le_mul_of_nonneg_right (PilotFamily.rate_bound A.P k) (mul_nonneg hl hQ)
  have hm := mul_le_mul_of_nonneg_left (PilotFamily.weight_sum k)
    (show 0≤(2:ℝ)*k*(∑ j∈range J,GeometricMass.radius A.R A.q j) by
      exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
        (sum_nonneg (fun j _=> (GeometricMass.radius_pos A.R A.q A.R_pos A.q_pos j).le)))
  have hlog : 1+Real.log k≤1+Real.log (k+1) := by
    have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
    linarith [Real.log_le_log hk' (show (k:ℝ)≤k+1 by linarith)]
  have hg := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog A.editRate_nonneg) hQ
  change (∑ t∈range N,average D.weight (A.keyEditCost (N:=N) (J:=J) D hk t))≤
    147*(∑ t∈range N,average D.weight (A.totalPilotCharge (N:=N) (J:=J) D hk t))+
      A.editRate*(1+Real.log k)*Q+k*A.auxiliaryCap k J at he
  change (∑ t∈range N,average D.weight (A.totalPilotCharge (N:=N) (J:=J) D hk t))≤
    (∑ i : PilotFamily.Index k,PilotFamily.weight i*rate (PilotFamily.template A.P i))*(1+Real.log (k+1))*Q+_ at hp
  unfold editBound editEndpoint
  dsimp only [Q] at *
  nlinarith only [he,hp,hr,hm,hg]

end UniformKServer.ActualPartitions.Config

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelAnchorContinuity
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                            
section

/-! Cross-time witnesses for a literal fixed-alphabet key. Tier labels cannot
be reassigned on consecutive supported maps; only retained heavy labels move. -/
noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

local instance ixAC_rdc08a4_1 (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairAC_rdc08a4_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
theorem supported_transition (D : LevelMap.Data X N H) (is : List (Fin H))
    (z : Tape D) (t : ℕ) (p q : X) (l : Label D)
    (hp : D.key is z t p=l) (hq : D.key is z (t+1) q=l) :
    D.anchor z t l=D.anchor z (t+1) l ∨
      ∃ a : HeavySlot X,l=Sum.inl a ∧ a∈(D.heavyState z.1 t).present ∧
        a∈(D.heavyState z.1 (t+1)).present := by
  rcases l with a|⟨i,l⟩|x
  · exact Or.inr ⟨a,rfl,((key_heavy_iff D is z t p a).mp hp).1,
      ((key_heavy_iff D is z (t+1) q a).mp hq).1⟩
  · left
    exact TierLabeledKeys.common_anchor D.base D.r D.positive.le (D.K i) (D.two i) (D.quota i)
      (D.qualify i) D.center t (z.2 i).1 (z.2 i).2 p q l
      (key_tier_witness D is z t p i l hp) (key_tier_witness D is z (t+1) q i l hq)
  · exact Or.inl rfl

theorem supported_distance (D : LevelMap.Data X N H) (is : List (Fin H))
    (z : Tape D) (t : ℕ) (p q : X) (l : Label D)
    (hp : D.key is z t p=l) (hq : D.key is z (t+1) q=l) :
    dist (D.anchor z t l) (D.anchor z (t+1) l)≤40*D.r := by
  obtain ha|⟨a,rfl,ho,hn⟩ := supported_transition D is z t p q l hp hq
  · rw [ha,dist_self]
    exact mul_nonneg (by norm_num) D.positive.le
  · by_cases he : (D.heavyState z.1 t).center a=(D.heavyState z.1 (t+1)).center a
    · change dist ((D.heavyState z.1 t).center a) ((D.heavyState z.1 (t+1)).center a)≤_
      rw [he,dist_self]
      exact mul_nonneg (by norm_num) D.positive.le
    · exact anchor_distance D z t a ho hn he

end UniformKServer.LevelMap.Data

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CommonAnchorTravel
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

/-! The diagonal term of tree matching is genuine retained heavy-anchor travel.
No claim is made about an unsupported prefix. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def actualAllocation (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) :=
  TreeAllocator.allocation (TreeCountData.data D (map A D hk z)) (by omega) t ω

theorem park_witness (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J))
    (hp : 0<park (shape A k J) (actualAllocation A D hk z t ω).amount v) :
    (region A D hk z t ω v).Nonempty := by
  apply witness A D hk z t ω v
  have hs := sum_nonneg (fun i (_ : i∈(univ : Finset (Children (shape A k J) v)))=>
    TreeAllocator.nonneg (TreeCountData.data D (map A D hk z)) (by omega) t ω i.val)
  change 0<TreeAllocator.amount (TreeCountData.data D (map A D hk z)) (by omega) t ω v-
    ∑ i : Children (shape A k J) v,TreeAllocator.amount (TreeCountData.data D (map A D hk z)) (by omega) t ω i.val at hp
  linarith

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionTransport
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

/-! Metric realization between occupied vertices in consecutive literal maps.
Intermediate nonexistent prefixes are never used as validity witnesses. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

attribute [local instance] OAI.UniformKServer.PartitionTree.ixPT
local instance pairPT_rdc08a4_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
theorem supported_anchor_step (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J))
    (p q : X) (hp : p∈region A D hk z t ω v) (hq : q∈region A D hk z (t+1) ω v) :
    dist (anchor A D hk z t ω v) (anchor A D hk z (t+1) ω v)≤40*radius A (depth (shape A k J) v) := by
  by_cases hv : v=0
  · subst v
    change dist A.base A.base≤40*radius A (depth (shape A k J) 0)
    rw [dist_self]
    exact mul_nonneg (by norm_num) (radius_nonneg A _)
  let j : Fin J := ⟨depth (shape A k J) v-1,by have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v; have := depth_positive A v hv; omega⟩
  have ho := last_region A D hk z t ω v hv p hp
  have hn := last_region A D hk z (t+1) ω v hv q hq
  have h := LevelMap.Data.supported_distance ((A.input (N:=N) (J:=J) D hk ω).level j.val).data
    ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) t p q (lastLabel A v) ho.symm hn.symm
  have hj : j.val+1=depth (shape A k J) v := by dsimp [j]; have := depth_positive A v hv; omega
  change dist _ _≤40*(A.R*A.q^(j.val+1)) at h
  simpa only [anchor,dite_eq_right hv,radius,hj] using h

theorem distinct_anchor_cost (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (u v : Vertex (size A k J)) (hne : u≠v)
    (hu : (region A D hk z t ω u).Nonempty) (hv : (region A D hk z (t+1) ω v).Nonempty)
    (hdiam : ∀ p q : X,dist p q≤40*A.R) :
    dist (anchor A D hk z t ω u) (anchor A D hk z (t+1) ω v)≤
      120*pathCost (S:=shape A k J) (weight A) u v := by
  obtain ⟨p,c,hpu,hpv,hc,hdep,hcut⟩ := separating_edge (S:=shape A k J) u v hne
  have hpedge := edge_le_path (weight A) (fun c=>radius_nonneg A _) u v c hc hcut
  have hed : depth (shape A k J) ((shape A k J).parent c)=depth (shape A k J) p := by
    rw [depth_child c hc] at hdep
    omega
  change radius A (depth (shape A k J) ((shape A k J).parent c))≤_ at hpedge
  rw [hed] at hpedge
  by_cases hp : p=0
  · subst p
    have hd := hdiam (anchor A D hk z t ω u) (anchor A D hk z (t+1) ω v)
    rw [depth_root,radius,pow_zero,mul_one] at hpedge
    nlinarith [A.R_pos]
  · obtain ⟨a,ha⟩ := hu
    obtain ⟨b,hb⟩ := hv
    have hap := nested A D hk z t ω p u hpu ha
    have hbp := nested A D hk z (t+1) ω p v hpv hb
    have hu0 : u≠0 := by intro he; subst u; have := desc_depth hpu; rw [depth_root] at this; have := depth_positive A p hp; omega
    have hv0 : v≠0 := by intro he; subst v; have := desc_depth hpv; rw [depth_root] at this; have := depth_positive A p hp; omega
    have hau := anchor_distance A D hk z t ω u hu0 a ha
    have hapd := anchor_distance A D hk z t ω p hp a hap
    have hbpd := anchor_distance A D hk z (t+1) ω p hp b hbp
    have hbv := anchor_distance A D hk z (t+1) ω v hv0 b hb
    have hpp := supported_anchor_step A D hk z t ω p a b hap hbp
    have hru := radius_antitone A (desc_depth hpu)
    have hrv := radius_antitone A (desc_depth hpv)
    have h₁ := dist_triangle (anchor A D hk z t ω u) a (anchor A D hk z t ω p)
    have h₂ := dist_triangle (anchor A D hk z t ω u) (anchor A D hk z t ω p) (anchor A D hk z (t+1) ω p)
    have h₃ := dist_triangle (anchor A D hk z t ω u) (anchor A D hk z (t+1) ω p) b
    have h₄ := dist_triangle (anchor A D hk z t ω u) b (anchor A D hk z (t+1) ω v)
    rw [dist_comm (anchor A D hk z t ω u) a] at h₁
    rw [dist_comm (anchor A D hk z (t+1) ω p) b] at h₃
    linarith

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualRoundingChain
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Adapted rounded joint laws for the literal partition/allocation process,
with the exact financed movement bound. -/
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry FiniteProbability
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem allocation_causal (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω v : Ω) (he : (D.filtration t).r ω v) :
    actualAllocation A D hk z t ω=actualAllocation A D hk z t v := by
  have heq : (actualAllocation A D hk z t ω).amount=(actualAllocation A D hk z t v).amount := by
    funext u
    exact TreeAllocator.measurable (TreeCountData.data D (map A D hk z)) (by omega) t he u
  cases h₁ : actualAllocation A D hk z t ω
  cases h₂ : actualAllocation A D hk z t v
  simp only [h₁,h₂] at heq
  cases heq
  rfl

theorem anchors_causal (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω v : Ω) (he : (D.filtration t).r ω v) :
    anchor A D hk z t ω=anchor A D hk z t v := by
  funext u
  unfold anchor
  split_ifs
  · rfl
  · exact A.anchor_measurable D hk ω v t _ he _ _

def roundingChain (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (hdiam : ∀ p q : X,dist p q≤40*A.R) : ChainInput (shape A k J) k X Ω where
  allocation := actualAllocation A D hk z
  anchors := anchor A D hk z
  filtration := D.filtration
  refines := D.refines
  allocation_causal := allocation_causal A D hk z
  anchors_causal := anchors_causal A D hk z
  weight := weight A
  weight_nonneg := fun v=>radius_nonneg A _
  weight_separated := weight_separated A
  factor := 120
  factor_nonneg := by norm_num
  geometry t ω u v hu hv hne := distinct_anchor_cost A D hk z t ω u v hne
    (park_witness A D hk z t ω u hu) (park_witness A D hk z (t+1) ω v hv) hdiam

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RoundingKernel
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The adapted joint repair gives genuine conditional state transitions, with
both marginal identities and their exact transport expectation. -/
namespace UniformKServer.TreeRounding.ChainInput
open Finset FiniteProbability
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X Ω : Type} [PseudoMetricSpace X]
variable (D : ChainInput S k X Ω)

def kernel (t : ℕ) (ω : Ω) (s : State S k) : FiniteProbability.Law (State S k) :=
  ((D.joint t ω).conditional Prod.fst (D.joint t ω) s).map Prod.snd

end UniformKServer.TreeRounding.ChainInput

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PublicRounding
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Causal rounded distributions are realized without exposing the hidden
trajectory. Only an observed request prefix selects the conditional rows. -/
namespace UniformKServer.TreeRounding
open Finset FiniteProbability
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X Ω : Type} [Fintype X] [MetricSpace X]

namespace PublicInput
variable {D : ChainInput S k X Ω} (O : PublicInput D)

def input : LazyMarkov.Input X (State S k) k where
  kernel w r := D.kernel w.length (O.pick (w++[r]))
  location w s i := D.anchors w.length (O.pick w) (s.realization.tuple i)

def initial (s : Fin k→X) : FiniteProbability.Law (State S k×(Fin k→X)) :=
  (D.distribution 0 O.default).law.map (fun v=>(v,s))

end PublicInput
end UniformKServer.TreeRounding

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PublicFlow
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! A rounded private process gives a literal nonnegative configuration/action
flow with legal zero-marginal rows and the same expected movement. -/
namespace UniformKServer.TreeRounding.PublicInput
open Finset FiniteProbability
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X Ω : Type} [Fintype X] [MetricSpace X]
attribute [local instance] OAI.UniformKServer.TreeRounding.PublicInput.configEq
variable {D : ChainInput S k X Ω} (O : PublicInput D)

def flow (hk : 0<k) (s : Fin k→X) : RealFlow.Data X (Fin k→X) (Fin k) :=
  (O.input.model hk).flow (O.initial s)

end UniformKServer.TreeRounding.PublicInput

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualPublicFlow
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Law-dependent but genuinely online configuration/action flows for the
actual pilot, partition, allocation, anchor, and rounding construction. -/

namespace UniformKServer.PartitionTree
open Finset FiniteProbability TreeRounding TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

attribute [local instance] OAI.UniformKServer.PartitionTree.configEq
def publicInput (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (hdiam : ∀ p q : X,dist p q≤40*A.R) (ω₀ : Ω) (hpublic : D.Public) :
    PublicInput (roundingChain A D hk z hdiam) where
  default := ω₀
  request := D.request
  trace := D.transcript
  trace_zero := D.transcript_zero
  trace_snoc := D.transcript_snoc
  trace_length := D.transcript_length
  reflects := hpublic

def componentFlow (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (hdiam : ∀ p q : X,dist p q≤40*A.R) (ω₀ : Ω) (hpublic : D.Public)
    (s : Fin k→X) : RealFlow.Data X (Fin k→X) (Fin k) :=
  (publicInput A D hk z hdiam ω₀ hpublic).flow (by omega) s

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionLaw
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! The multiscale independent partition tape; its law is input-law independent. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset FiniteProbability
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def staticLevel (A : ActualPartitions.Config X) (N k j : ℕ) : LevelMap.Data X N (height k) where
  r := GeometricMass.radius A.R A.q j
  positive := GeometricMass.radius_pos A.R A.q A.R_pos A.q_pos j
  K i := TierParameters.cutoff A.C (DyadicTiers.value i.val)
  two i := TierParameters.cutoff_two A.C _ A.C_one (DyadicTiers.one_le_value i.val)
  base := A.base
  center _ := A.base
  heavy _ := False
  qualify _ _ := False

attribute [local instance] OAI.UniformKServer.PartitionTree.ixPL
attribute [local instance] OAI.UniformKServer.PartitionTree.pairPL
def levelLaw (A : ActualPartitions.Config X) (N k j : ℕ) : Law (LevelTape A k N j) :=
  (staticLevel A N k j).law

def tapeLaw (A : ActualPartitions.Config X) (N k J : ℕ) : Law (Tape A k N J) :=
  Law.pi (fun j=>levelLaw A N k j.val)

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AnchorFinance
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Horizon-independent financing of literal retained-anchor metric travel.
All quantities here are expectations under the actual independent finite tape. -/
namespace UniformKServer.PartitionTree
open Finset FiniteProbability PilotEdits TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}
local instance ixAF_rdc08a4_1 (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairAF_rdc08a4_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
def allocationEndpoint (A : ActualPartitions.Config X) (k J : ℕ) : ℝ :=
  (8*(10:ℝ)^63/A.q)*EpochAlpha.ell k*A.editEndpoint k J+
    2*(10:ℝ)^63*EpochAlpha.ell k*allowance (shape A k J) k (weight A)
def anchorEndpoint (A : ActualPartitions.Config X) (k J : ℕ) : ℝ :=
  160*(((6/5)*132)*(1+288*KeySizeTracker.ell (k+1))*A.editEndpoint k J+
    ((6/5)*132)*sizeEndpoint A k J+(12/5)*(1+1/22)*allocationEndpoint A k J+(6/5)*A.R*k)

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochShadow
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.EpochShadow

def shadowTrace {n k : ℕ} (T : Selector n k) :
    List (Fin n) → Configuration n k → List (Fin n) → History n k
  | _, _, [] => []
  | p, c, r :: w => (r,T p c r) :: shadowTrace T (p ++ [r]) (serve c r (T p c r)) w


end UniformKServer.EpochShadow

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochTape
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.EpochTape
open EpochShadow EpochExpectation

def fullTrace {n k b H : ℕ} (hk : 0 < k) (M : ℕ)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (u : Configuration n k) (w : List (Fin n)) (coins : Fin H → Fin b → Bool) : History n k :=
  trace hk M (selector N hN (extend coins)) (initial u) ⟨u,0⟩ ∅ w

end UniformKServer.EpochTape

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteLawFinance
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The assembled finite-law bound: the policy is a legal causal flow, the
coefficient is absolute squared-logarithmic, and the additive quantity knows
neither the horizon nor the request law. -/
namespace UniformKServer.PartitionTree
open Finset FiniteProbability PilotEdits TreeRounding TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

attribute [local instance] OAI.UniformKServer.PartitionTree.ixFF
local instance pairFF_rdc08a4_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
attribute [local instance] OAI.UniformKServer.PartitionTree.configEqFF
def flowEndpoint (A : ActualPartitions.Config X) (k J : ℕ) : ℝ :=
  15840*allocationEndpoint A k J+anchorEndpoint A k J+k*(40*A.R)

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HiddenHistory
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Literal optimal labeled histories yield the public-prefix hidden law used
in the finite-law construction. After a word ends its chosen label stays put;
no future request is supplied to the online process. -/
namespace UniformKServer.HiddenHistory
open Finset
open scoped Classical
variable {n k : ℕ} [NeZero k]

def next (s : Configuration n k) (h : History n k) (t : ℕ) : Fin n×Fin k :=
  if ht : t<h.length then h[t] else (finish s h 0,0)

def location (s : Configuration n k) (h : History n k) (t : ℕ) : Configuration n k :=
  finish s (h.take t)

omit [NeZero k] in
theorem finish_append (s : Configuration n k) (g h : History n k) :
    finish s (g++h)=finish (finish s g) h := by
  induction g generalizing s with
  | nil => rfl
  | cons a g ih => cases a; simp only [List.cons_append,finish,ih]

theorem update (s : Configuration n k) (h : History n k) (t : ℕ) (a : Fin k) :
    location s h (t+1) a=if a=(next s h t).2 then (next s h t).1 else location s h t a := by
  by_cases ht : t<h.length
  · simp only [location,List.take_succ_eq_append_getElem ht,finish_append,finish,next,dite_eq_left ht]
    simp only [serve,Function.update_apply ]
  · have he : h.length≤t := Nat.le_of_not_gt ht
    simp only [location,List.take_of_length_le he,
      List.take_of_length_le (he.trans (Nat.le_succ t)),next,dite_eq_right ht]
    split_ifs with ha
    · subst a; rfl
    · rfl

def trace (s : Configuration n k) (h : History n k) (t : ℕ) : List (Fin n) :=
  List.ofFn (fun i : Fin t=>(next s h i.val).1)

theorem trace_snoc (s : Configuration n k) (h : History n k) (t : ℕ) :
    trace s h (t+1)=trace s h t++[(next s h t).1] := by
  simp only [trace,List.ofFn_succ',List.concat_eq_append,Fin.val_castSucc,Fin.val_last]

theorem trace_length (s : Configuration n k) (h : History n k) (t : ℕ) :
    (trace s h t).length=t := by simp only [trace,List.length_ofFn]

theorem trace_take (s : Configuration n k) (h : History n k) (t : ℕ) (ht : t≤h.length) :
    trace s h t=(h.take t).map Prod.fst := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hl : t<h.length := by omega
    rw [trace_snoc,ih (by omega),List.take_succ_eq_append_getElem hl]
    simp only [List.map_append,List.map_singleton,next,dite_eq_left hl]

theorem trace_full (s : Configuration n k) (h : History n k) :
    trace s h h.length=h.map Prod.fst := by
  rw [trace_take s h _ le_rfl,List.take_length]

theorem trace_prefix (s : Configuration n k) (h : History n k) (a b : ℕ) (hab : a≤b) :
    (trace s h a).IsPrefix (trace s h b) := by
  induction b with
  | zero =>
    have ha : a=0 := by omega
    subst a
    exact List.prefix_refl _
  | succ b ih =>
    by_cases he : a=b+1
    · subst a; exact List.prefix_refl _
    · exact (ih (by omega)).trans (by rw [trace_snoc]; exact List.prefix_append _ _)

variable {Ω : Type} [Fintype Ω]

def data (s : Configuration n k) (h : Ω→History n k) (w : Ω→ℝ)
    (hw : ∀ω,0<w ω) (ht : ∑ω,w ω=1) : HiddenFlow.Data (Fin n) Ω k where
  weight := w
  positive := hw
  total := ht
  filtration t := Setoid.ker (fun ω=>trace s (h ω) t)
  refines := by
    intro t ω v he
    change trace s (h ω) (t+1)=trace s (h v) (t+1) at he
    rw [trace_snoc,trace_snoc] at he
    exact (List.append_inj he (by rw [trace_length,trace_length])) |>.1
  position t ω := location s (h ω) t
  chosen t ω := (next s (h ω) t).2
  request t ω := (next s (h ω) t).1
  update t ω a := update s (h ω) t a
  request_measurable := by
    intro t ω v he
    change trace s (h ω) (t+1)=trace s (h v) (t+1) at he
    rw [trace_snoc,trace_snoc] at he
    have hh := (List.append_inj he (by rw [trace_length,trace_length])) |>.2
    exact List.singleton_inj.mp hh

theorem is_public (s : Configuration n k) (h : Ω→History n k) (w : Ω→ℝ)
    (hw : ∀ω,0<w ω) (ht : ∑ω,w ω=1) : (data s h w hw ht).Public := by
  intro t ω v he
  exact he

theorem paid_step (d : RationalMetric n) (s : Configuration n k) (h : History n k) (t : ℕ) :
    costAlong d s (h.take (t+1))=costAlong d s (h.take t)+
      (d.distance (location s h t (next s h t).2) (next s h t).1 : ℝ) := by
  by_cases ht : t<h.length
  · rw [List.take_succ_eq_append_getElem ht,RawBlockCharge.cost_append]
    simp only [next,dite_eq_left ht,costAlong,add_zero,location]
  · have he : h.length≤t := Nat.le_of_not_gt ht
    simp only [List.take_of_length_le (he.trans (Nat.le_succ t)),
      next,dite_eq_right ht,location]
    rw [List.take_of_length_le he,(d.eq_zero _ _).mpr rfl,Rat.cast_zero,add_zero]

theorem paid_sum (d : RationalMetric n) (s : Configuration n k) (h : History n k) (N : ℕ) :
    (∑t∈range N,(d.distance (location s h t (next s h t).2) (next s h t).1 : ℝ))=
      costAlong d s (h.take N) := by
  induction N with
  | zero => rfl
  | succ N ih => rw [sum_range_succ,ih,paid_step]

end UniformKServer.HiddenHistory

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OfflineLaw
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! No hidden-trajectory hypothesis is added: an optimal finite serving history
is selected for each atom of an arbitrary finite request law. -/
namespace UniformKServer.OfflineLaw
open Finset FiniteProbability PartitionTree PilotEdits
open scoped Classical
variable {n k N : ℕ} [NeZero k] {Ω : Type} [Fintype Ω]

def history (d : RationalMetric n) (s : Configuration n k) (w : List (Fin n)) : History n k :=
  (OfflineDynamic.optRat_attained d s w).choose

theorem history_map (d : RationalMetric n) (s : Configuration n k) (w : List (Fin n)) :
    (history d s w).map Prod.fst=w := (OfflineDynamic.optRat_attained d s w).choose_spec.1

theorem history_cost (d : RationalMetric n) (s : Configuration n k) (w : List (Fin n)) :
    costAlong d s (history d s w)=offlineCost d s w := by
  rw [OfflineDynamic.offline_eq_optRat]
  exact (OfflineDynamic.optRat_attained d s w).choose_spec.2

theorem history_length (d : RationalMetric n) (s : Configuration n k) (w : List (Fin n)) :
    (history d s w).length=w.length := by
  simpa only [List.length_map] using congrArg List.length (history_map d s w)

def data (d : RationalMetric n) (s : Configuration n k) (word : Ω→List (Fin n))
    (P : Law Ω) : HiddenFlow.Data (Fin n) (PositiveSupport.Support P.weight) k :=
  HiddenHistory.data s (fun ω=>history d s (word ω)) (fun ω=>P.weight ω)
    (fun ω=>ω.property) (PositiveSupport.total P.weight P.nonneg P.total)

theorem data_public (d : RationalMetric n) (s : Configuration n k) (word : Ω→List (Fin n))
    (P : Law Ω) : (data d s word P).Public := HiddenHistory.is_public _ _ _ _ _

theorem data_trace (d : RationalMetric n) (s : Configuration n k) (word : Ω→List (Fin n))
    (P : Law Ω) (ω : PositiveSupport.Support P.weight) :
    (data d s word P).transcript (word ω).length ω=word ω := by
  change HiddenHistory.trace s (history d s (word ω)) (word ω).length=word ω
  rw [←history_length d s (word ω),HiddenHistory.trace_full,history_map]

theorem data_cost (d : RationalMetric n) (s : Configuration n k) (word : Ω→List (Fin n))
    (P : Law Ω) (hb : ∀ω,(word ω).length≤N) :
    letI := d.metric
    (∑t∈range N,average (data d s word P).weight (moverCost (HiddenFlow.flow (data d s word P)) t))=
      P.expect (fun ω=>offlineCost d s (word ω)) := by
  let := d.metric
  simp only [average]
  simp_rw [HiddenFlow.expected_mover_cost]
  rw [sum_comm]
  have he (ω : PositiveSupport.Support P.weight) :
      (∑t∈range N,dist ((data d s word P).request t ω)
        ((data d s word P).position t ω ((data d s word P).chosen t ω)))=
          offlineCost d s (word ω) := by
    simp only [dist_comm]
    change (∑t∈range N,(d.distance
      (HiddenHistory.location s (history d s (word ω)) t (HiddenHistory.next s (history d s (word ω)) t).2)
      (HiddenHistory.next s (history d s (word ω)) t).1 : ℝ))=_
    rw [HiddenHistory.paid_sum,List.take_of_length_le (by rw [history_length]; exact hb ω),history_cost]
  simp_rw [←mul_sum,he]
  exact PositiveSupport.weighted_sum P.weight P.nonneg (fun ω=>offlineCost d s (word ω))

end UniformKServer.OfflineLaw

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteLawTheorem
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The finite-law theorem has arbitrary request atoms and literal offline OPT.
Its endpoint is fixed by the instance, before the law or horizon are chosen. -/
namespace UniformKServer.OfflineLaw
open Finset FiniteProbability PartitionTree PilotEdits TreeRounding
open scoped Classical
variable {n k : ℕ} [NeZero k]
local instance configEqFL : DecidableEq (Configuration n k) := fun a b=>Classical.propDecidable (a=b)

end UniformKServer.OfflineLaw

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HorizonPolicy
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! A single finite-horizon strongly lazy flow, now independent of the law. Its
additive endpoint is uniform over horizons and all words. -/
namespace UniformKServer.OfflineLaw
open Finset FiniteProbability PartitionTree FiniteFlowSpace RealFlow TreeRounding
open scoped Classical
variable {n k : ℕ} [NeZero k]
local instance configEqHP : DecidableEq (Configuration n k) := fun a b=>Classical.propDecidable (a=b)

end UniformKServer.OfflineLaw

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LiteralVector
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                    
section

namespace UniformKServer.LiteralVector
open Turing Turing.ToPartrec

 theorem active_eval (v : List.Vector ℕ 3) :
    Code.eval activeCode v.val=Part.some (RawProgram.run v).val :=
  Classical.choose_spec (code_exists RawProgram.run RawProgram.primitive_run) v

end UniformKServer.LiteralVector

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LiteralBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.LiteralBound
open Turing StackCompiler StackPrimitive
open scoped Classical

 theorem finishes_run (t u r a : ℕ) :
    finishes t u r a=(run program (Init u r a) (List.replicate t false)).yielded := by
  have h:=ofState_run program (literal_deterministic LiteralVector.activeCode) (Init u r a) (List.replicate t false)
  simpa only [List.length_replicate,finishes,ofState] using congrArg (fun s=>s.2.2) h.symm

 theorem exists_time (u r a : ℕ) : ∃t,finishes t u r a=true := by
  let v : List.Vector ℕ 3:=⟨[u,r,a],rfl⟩
  have he : (RawProgram.run v).val∈Turing.ToPartrec.Code.eval LiteralVector.activeCode v.val := by
    rw [LiteralVector.active_eval]
    exact Part.mem_some _
  obtain ⟨t,ht,hs⟩:=LiteralPartrec.halts he
  exact ⟨t,by simpa only [finishes_run,v] using ht⟩

end UniformKServer.LiteralBound

end

end OAI
end


