-- Prove2me | Definitions.Def_Q220Uk005
-- name    : Q220Uk005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T14:42:04.881206+00:00
-- url     : https://prove2.me/theorems/7ab6f467-7bd1-41e4-99c5-2eed61cb3d0c
-- title:
--   Definitions bundle Q220Uk005 of the split of OpenAI, Uniform computation of the squared-logarithmic k-server bound
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniformKServer.uniform_squared_logarithmic_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform computation of the squared-logarithmic k-server bound*, OpenAI Math Release, September 24, 2026, result family 110, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 485 declarations of OpenAI's Lean: 134 definitions, 5 inductive types or structures, 2 instances and 344 theorems. The definitions and types are `OAI.UniformKServer.AdaptiveLedger.drift`, `OAI.UniformKServer.AdaptiveLedger.increment`, `OAI.UniformKServer.AdaptiveLedger.post`, `OAI.UniformKServer.AdaptiveSide.offset`, `OAI.UniformKServer.AdaptiveSide.potential`, `OAI.UniformKServer.AdaptiveSide.theta`, `OAI.UniformKServer.AdaptiveSide.valid`, `OAI.UniformKServer.AllocationSchedule.potential`, `OAI.UniformKServer.AlphaFiniteInput.alpha`, `OAI.UniformKServer.AlphaFiniteInput.input`, `OAI.UniformKServer.AlphaFiniteInput.oldMask`, `OAI.UniformKServer.AlphaFiniteInput.post`, `OAI.UniformKServer.AlphaFiniteInput.prepared`, `OAI.UniformKServer.AlphaFiniteInput.star`, `OAI.UniformKServer.AlphaFiniteLedger.coefficient`, `OAI.UniformKServer.AlphaFiniteLedger.jump`, `OAI.UniformKServer.AlphaFiniteLedger.movement`, `OAI.UniformKServer.AlphaFiniteLedger.potential`, `OAI.UniformKServer.BalancedStar.clippedSet`, `OAI.UniformKServer.BalancedStar.imbalance`, `OAI.UniformKServer.BalancedStar.jointCost`, `OAI.UniformKServer.BalancedStar.preliminary`, `OAI.UniformKServer.BalancedStar.preliminaryCost`, `OAI.UniformKServer.BalancedStar.slots`, `OAI.UniformKServer.BinaryTape.coins`, `OAI.UniformKServer.CoarseData.coreChange`, `OAI.UniformKServer.CoarseData.totalDrift`, `OAI.UniformKServer.ComputedInstance.canonical`, `OAI.UniformKServer.ConstructorProgram.code`, `OAI.UniformKServer.ConstructorProgram.result`, `OAI.UniformKServer.ConstructorProgram.run`, `OAI.UniformKServer.ConstructorSearch.Cert`, `OAI.UniformKServer.ConstructorSearch.candidate`, `OAI.UniformKServer.ConstructorSearch.search`, `OAI.UniformKServer.ConstructorSearch.verify`, `OAI.UniformKServer.Covers`, `OAI.UniformKServer.EpochAlpha.marked`, `OAI.UniformKServer.EpochAlpha.regular`, `OAI.UniformKServer.EpochAlpha.singleton`, `OAI.UniformKServer.EpochAlphaCharge.param` and 99 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `UniformKServer_AdaptiveAlpha`, `UniformKServer_AdaptiveAlphaLinear`, `UniformKServer_AdaptiveLedger`, `UniformKServer_AdaptiveSide`, `UniformKServer_AllocationEpoch`, `UniformKServer_AllocationMovement`, `UniformKServer_AllocationOutputs`, `UniformKServer_AllocationSchedule`, `UniformKServer_AlphaEmpty`, `UniformKServer_AlphaEmptyLinear`, `UniformKServer_AlphaFiniteInput`, `UniformKServer_AlphaFiniteLedger`, `UniformKServer_AlphaParameterChanges`, `UniformKServer_AlphaPrepared`, `UniformKServer_AlphaRecurrence`, `UniformKServer_AlphaStability`, `UniformKServer_AlphaTracker`, `UniformKServer_AnchorPotential`, `UniformKServer_AnchorRamp`, `UniformKServer_AnchorScalar`, `UniformKServer_BalancedRepair`, `UniformKServer_BalancedStar`, `UniformKServer_BinaryTape`, `UniformKServer_CausalLevel`, `UniformKServer_CausalSchedules`, `UniformKServer_ChronologicalBound`, `UniformKServer_CoarseBridge`, `UniformKServer_CoarseData`, `UniformKServer_ComputedInstance`, `UniformKServer_ConditionalLaw`, `UniformKServer_ConditionalRank`, `UniformKServer_ConditionalRanks`, `UniformKServer_ConstructorProgram`, `UniformKServer_ConstructorSearch`, `UniformKServer_CooldownLabels`, `UniformKServer_CoreFiltering`, `UniformKServer_CrossRule`, `UniformKServer_DyadicTiers`, `UniformKServer_EpochAlpha`, `UniformKServer_EpochAlphaBudget`, `UniformKServer_EpochAlphaCharge`, `UniformKServer_EpochAlphaJump`, `UniformKServer_EpochAlphaPieces`, `UniformKServer_EpochAlphaSchedule`, `UniformKServer_EpochAlphaStatic`, `UniformKServer_EpochControl`, `UniformKServer_EpochExpectation`, `UniformKServer_EpochFinite`, `UniformKServer_EpochGeometry`, `UniformKServer_EpochOutputParameters`, `UniformKServer_EpochParameters`, `UniformKServer_EpochShadow`, `UniformKServer_EpochSide`, `UniformKServer_Epochs`, `UniformKServer_FirstStructure`, `UniformKServer_FlowAuxiliary`, `UniformKServer_HeavyBirths`, `UniformKServer_HeavyRadius`, `UniformKServer_HeavySchedule`, `UniformKServer_HeavySeparation`, `UniformKServer_HeavyTape`, `UniformKServer_HeldRelative`, `UniformKServer_KeySizeTracker`, `UniformKServer_LevelHeavy`, `UniformKServer_LevelSeparation`, `UniformKServer_LiteralBound`, `UniformKServer_LiteralVector`, `UniformKServer_PartitionCausal`, `UniformKServer_PartitionSeparation`, `UniformKServer_PartitionTree`, `UniformKServer_PilotExtension`, `UniformKServer_PilotTemplates`, `UniformKServer_ProportionParameters`, `UniformKServer_RankData`, `UniformKServer_RankFunctions`, `UniformKServer_RankTracking`, `UniformKServer_RawControl`, `UniformKServer_RawExpansion`, `UniformKServer_RawFilter`, `UniformKServer_RawGlobal`, `UniformKServer_RawProgram`, `UniformKServer_RuntimeCertificate`, `UniformKServer_SideParameters`, `UniformKServer_SideReferenceSchedule`, `UniformKServer_TapeController`.
--
--   **Imports.** It imports the published bundle `Def_UniformKServer`; the bundles `Q220Uk000`, `Q220Uk001` and `Q220Uk002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q220Uk007` and `Q220Uk008`.
-- source:
--   OpenAI, Uniform computation of the squared-logarithmic k-server bound, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 110; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_UniformKServer
import Definitions.Def_Q220Uk000
import Definitions.Def_Q220Uk001
import Definitions.Def_Q220Uk002

section
-- module Solutions.Q220_UK.UniformKServer_AlphaTracker
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace UniformKServer.AlphaTracker
open Set Filter
open scoped Topology
open UniformKServer.Denominators UniformKServer.LogPrimitive UniformKServer.SimplexTracker
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem marked_update (o : ι) (u c Z : ℝ) (h B a₀ : ι → ℝ) (ell ct C E : ℝ)
    (hu : 0 < u) (hu₁ : u ≤ 1) (hc₀ : 0 < c) (hc₁ : c ≤ 1) (hZ : 0 ≤ Z)
    (ho : h o = u) (hh : ∀ i, i ≠ o → 1 ≤ h i)
    (hhc : ∀ i, i ≠ o → c*height u ≤ h i)
    (he : (∑ i ∈ Finset.univ.erase o, Real.exp (-h i)) ≤ Z*u)
    (hB : ∀ i, 0 ≤ B i) (hl : 0 < ell) (hct : 0 < ct) (hE : 0 ≤ E)
    (heta : ∀ i, ct*h i/ell ≤ E) (hm : 2*(25+(2+32*Z)/c)*(1+E) < C*ct)
    (ha₀ : simplex a₀) : UpdateConclusion (markedG o u h B ell ct C) B h ell ct a₀ := by
  have hp : ∀ i, 0 < h i := by
    intro i
    by_cases hi : i = o
    · simpa [hi, ho] using hu
    · linarith [hh i hi]
  apply update _ B h (markedF o u h) ell ct C (25+(2+32*Z)/c) E _ a₀ ha₀
  apply analytic_data hB hp hl hct (by positivity) hE heta hm
  · intro i x hx hx₁
    by_cases hi : i = o
    · simp only [markedF, hi]
      exact marked_pos hu hu₁ hx.le hx₁
    · simp only [markedF, ite_eq_right hi]
      exact regular_pos (hp i) hx.le hx₁
  · intro a ha
    exact marked_simplex o u c Z h a hu hu₁ hc₀ hc₁ hZ ho hh hhc he ha.1 ha.2
  · intro i
    by_cases hi : i = o
    · have hf : markedF o u h i = marked u := by funext x; simp [markedF, hi]
      simpa only [markedG, hf, ite_eq_left hi] using
        marked_contract u (C*ell) (∑ r, B r) ((1+ct*h i/ell)*B i) hu hu₁
    · have hf : markedF o u h i = regular (h i) := by funext x; simp [markedF, hi]
      simpa only [markedG, hf, ite_eq_right hi] using
        regular_contract (h i) (C*ell) (∑ r, B r) ((1+ct*h i/ell)*B i) (hh i hi)
end UniformKServer.AlphaTracker

end


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_Epochs
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer

def Covers {n k : ℕ} (e : Entry n k) (r : Fin n) : Prop := ∃ j, e.position j = r
instance instDecidableCovers {n k : ℕ} (e : Entry n k) (r : Fin n) : Decidable (Covers e r) :=
  inferInstanceAs (Decidable (∃ j, e.position j = r))

theorem treeBudget_pos (k m : ℕ) : 0 < treeBudget k m := by
  cases m <;> simp [treeBudget]

def expand {n k : ℕ} (M : ℕ) (r : Fin n) (e : Entry n k) : List (Entry n k) :=
  if Covers e r then [e]
  else if e.moves < M then
    (List.finRange k).map fun j => ⟨Function.update e.position j r, e.moves + 1⟩
  else []

def births {n k : ℕ} (M : ℕ) (r : Fin n) (e : Entry n k) : ℕ :=
  if Covers e r then 0 else if e.moves < M then k else 0

def futureMass {n k : ℕ} (M : ℕ) (es : List (Entry n k)) : ℕ :=
  (es.map fun e => weight M e - 1).sum

structure FilterState (n k : ℕ) where
  live : List (Entry n k)
  kept : List (Fin n)
  created : ℕ

def step {n k : ℕ} (M : ℕ) (s : FilterState n k) (r : Fin n) : FilterState n k :=
  if ∀ e ∈ s.live, Covers e r then s else
  { live := s.live.flatMap (expand M r)
    kept := s.kept ++ [r]
    created := s.created + (s.live.map (births M r)).sum }

def initial {n k : ℕ} (u : Configuration n k) : FilterState n k :=
  { live := [⟨u, 0⟩], kept := [], created := 1 }

def runFilter {n k : ℕ} (M : ℕ) (u : Configuration n k) (raw : List (Fin n)) :
    FilterState n k := raw.foldl (step M) (initial u)

theorem treeBudget_eq_horizon (k M : ℕ) : treeBudget k M = horizon k M := by
  induction M with
  | zero => simp [horizon]
  | succ M ih =>
    simp only [treeBudget_succ, ih]
    unfold horizon
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [pow_zero, pow_succ', ← Finset.mul_sum]
    omega

theorem length_le_mass {n k : ℕ} (M : ℕ) (es : List (Entry n k)) :
    es.length ≤ mass M es := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have hp : 0 < weight M e := treeBudget_pos _ _
    simp only [List.length_cons, mass_cons]
    omega

theorem expand_valid {n k : ℕ} (M : ℕ) (r : Fin n) (e : Entry n k)
    (he : e.moves ≤ M) : ∀ e' ∈ expand M r e, e'.moves ≤ M := by
  unfold expand
  split_ifs with hc hm
  · simpa using he
  · intro e' he'
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp he'
    dsimp
    omega
  · simp

theorem mass_expand {n k : ℕ} (M : ℕ) (r : Fin n) (e : Entry n k)
    (he : e.moves ≤ M) :
    mass M (expand M r e) + (if Covers e r then 0 else 1) = weight M e := by
  unfold expand
  split_ifs with hc hm
  · simp [mass]
  · have hsub : M - e.moves = (M - (e.moves + 1)) + 1 := by omega
    simp [mass, weight, Function.comp_def, hsub, List.sum_replicate]; omega
  · have heq : e.moves = M := by omega
    simp [mass, weight, heq]


theorem futureMass_add_length {n k : ℕ} (M : ℕ) (es : List (Entry n k)) :
    futureMass M es + es.length = mass M es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have hp : 1 ≤ weight M e := treeBudget_pos _ _
    simp only [futureMass, List.map_cons, List.sum_cons, List.length_cons] at *
    simp only [mass_cons]
    omega

theorem futureMass_expand {n k : ℕ} (M : ℕ) (r : Fin n) (e : Entry n k)
    (he : e.moves ≤ M) :
    futureMass M (expand M r e) + births M r e = weight M e - 1 := by
  have hm := mass_expand M r e he
  have hf := futureMass_add_length M (expand M r e)
  by_cases hc : Covers e r
  · simp [expand, births, hc, futureMass]
  · by_cases hlt : e.moves < M
    · have hl : (expand M r e).length = k := by simp [expand, hc, hlt]
      simp only [hc, ↓reduceIte] at hm
      simp only [births, hc, hlt, ↓reduceIte]
      omega
    · have heq : e.moves = M := by omega
      simp [expand, births, hc, futureMass, weight, heq]

def misses {n k : ℕ} (r : Fin n) (es : List (Entry n k)) : ℕ :=
  (es.map fun e => if Covers e r then 0 else 1).sum

theorem misses_zero_iff {n k : ℕ} (r : Fin n) (es : List (Entry n k)) :
    misses r es = 0 ↔ ∀ e ∈ es, Covers e r := by
  induction es with
  | nil => simp [misses]
  | cons e es ih =>
    by_cases hc : Covers e r <;> simp_all [misses]

theorem mass_expansion {n k : ℕ} (M : ℕ) (r : Fin n) (es : List (Entry n k))
    (hvalid : ∀ e ∈ es, e.moves ≤ M) :
    mass M (es.flatMap (expand M r)) + misses r es = mass M es := by
  induction es with
  | nil => simp [misses]
  | cons e es ih =>
    have he : e.moves ≤ M := hvalid e (by simp)
    have hv : ∀ e ∈ es, e.moves ≤ M := fun e he => hvalid e (by simp [he])
    have hm := mass_expand M r e he
    have hi := ih hv
    simp only [List.flatMap_cons, mass_append, mass_cons]
    simp only [misses, List.map_cons, List.sum_cons]
    unfold misses at hi
    omega

@[simp] theorem futureMass_append {n k : ℕ} (M : ℕ) (a b : List (Entry n k)) :
    futureMass M (a ++ b) = futureMass M a + futureMass M b := by simp [futureMass]

theorem futureMass_expansion {n k : ℕ} (M : ℕ) (r : Fin n) (es : List (Entry n k))
    (hvalid : ∀ e ∈ es, e.moves ≤ M) :
    futureMass M (es.flatMap (expand M r)) + (es.map (births M r)).sum =
      futureMass M es := by
  induction es with
  | nil => simp [futureMass]
  | cons e es ih =>
    have he : e.moves ≤ M := hvalid e (by simp)
    have hv : ∀ e ∈ es, e.moves ≤ M := fun e he => hvalid e (by simp [he])
    have hm := futureMass_expand M r e he
    have hi := ih hv
    simp only [List.flatMap_cons, futureMass_append, List.map_cons, List.sum_cons]
    change _ = (weight M e - 1) + futureMass M es
    omega

def Good {n k : ℕ} (M B : ℕ) (s : FilterState n k) : Prop :=
  (∀ e ∈ s.live, e.moves ≤ M) ∧
  s.kept.length + mass M s.live ≤ B ∧
  s.created + futureMass M s.live = B

theorem step_good {n k : ℕ} (M B : ℕ) (s : FilterState n k) (r : Fin n)
    (hs : Good M B s) : Good M B (step M s r) := by
  unfold step
  split_ifs with hc
  · exact hs
  · rcases hs with ⟨hv, hb, hf⟩
    have hm := mass_expansion M r s.live hv
    have hfuture := futureMass_expansion M r s.live hv
    have hmiss : 0 < misses r s.live := by
      have hn : misses r s.live ≠ 0 := fun h => hc ((misses_zero_iff r s.live).mp h)
      exact Nat.pos_of_ne_zero hn
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      obtain ⟨old, hold, he⟩ := List.mem_flatMap.mp he
      exact expand_valid M r old (hv old hold) e he
    · dsimp
      simp only [List.length_append, List.length_singleton]
      omega
    · dsimp
      omega

theorem runFilter_good {n k : ℕ} (M : ℕ) (u : Configuration n k)
    (raw : List (Fin n)) : Good M (treeBudget k M) (runFilter M u raw) := by
  have hi : Good M (treeBudget k M) (initial u) := by
    refine ⟨?_, ?_, ?_⟩
    · simp [initial]
    · simp [initial, mass, weight]
    · have hp := treeBudget_pos k M
      dsimp [initial, futureMass, weight]
      simp only [Nat.sub_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
  have hfold : ∀ (rs : List (Fin n)) (s : FilterState n k),
      Good M (treeBudget k M) s → Good M (treeBudget k M) (rs.foldl (step M) s) := by
    intro rs
    induction rs with
    | nil => intro s hs; exact hs
    | cons r rs ih =>
      intro s hs
      exact ih (step M s r) (step_good M _ s r hs)
  exact hfold raw (initial u) hi

/-- The source's strongly lazy rule: a hit changes nothing; a miss chooses
exactly one label and counts one positive move. -/
def LazyStep {n k : ℕ} (e : Entry n k) (r : Fin n) (e' : Entry n k) : Prop :=
  if Covers e r then e' = e else
    ∃ j : Fin k, e' = ⟨Function.update e.position j r, e.moves + 1⟩

/-- Endpoints of complete strongly lazy paths, with no cap imposed in the relation. -/
inductive LazyPath {n k : ℕ} (u : Configuration n k) :
    List (Fin n) → Entry n k → Prop
  | nil : LazyPath u [] ⟨u, 0⟩
  | snoc {w : List (Fin n)} {e e' : Entry n k} {r : Fin n} :
      LazyPath u w e → LazyStep e r e' → LazyPath u (w ++ [r]) e'

@[simp] theorem lazyPath_nil_iff {n k : ℕ} (u : Configuration n k) (e : Entry n k) :
    LazyPath u [] e ↔ e = ⟨u, 0⟩ := by
  constructor
  · intro h
    generalize hw : ([] : List (Fin n)) = w at h
    cases h with
    | nil => rfl
    | snoc hp hs => simp at hw
  · rintro rfl
    exact LazyPath.nil

end UniformKServer



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AlphaStability
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Companion §04: exact primitive input slopes on the entire simplex.  The
 constants do not depend on the number of children.  These estimates apply to
 the old flags after filtering, without requiring feasibility of that input. -/
namespace UniformKServer.AlphaStability
noncomputable section
open Set MeasureTheory Finset
open UniformKServer.LogPrimitive UniformKServer.Denominators UniformKServer.AlphaBounds

variable {ι : Type*} [Fintype ι]

/-- The marked primitive retains a dimension-free input bound as u tends to
 zero. The estimate does not require input feasibility at the old state. -/
theorem marked_input [DecidableEq ι] (o : ι) (h η a B B' : ι → ℝ) (scale E u : ℝ)
    (hu : 0 < u) (hu₁ : u ≤ 1) (hh : ∀ i, i ≠ o → 1 ≤ h i)
    (ha : ∀ i, a i ∈ Icc (0:ℝ) 1) (hasum : ∑ i, a i=1)
    (hη : ∀ i, 0 ≤ η i) (hηE : ∀ i, η i ≤ E) :
    |(∑ i, mixedPrimitive o u h η B scale a i)-
      (∑ i, mixedPrimitive o u h η B' scale a i)| ≤
      |scale| * (11+4*E)*(∑ i, |B i-B' i|) := by
  let D := |(∑ i, B i)-(∑ i, B' i)|
  let V := ∑ i, |B i-B' i|
  let R (i : ι) := |scale| * (D*a i+(1+E)*|B i-B' i|)
  let M := 3*|scale| * (2*D+(1+E)*V)
  have hE : 0 ≤ E := (hη o).trans (hηE o)
  have hDV : D ≤ V := sum_difference B B'
  have hD : 0 ≤ D := abs_nonneg _
  have hV : 0 ≤ V := sum_nonneg fun i _ => abs_nonneg _
  have hiV (i : ι) : |B i-B' i| ≤ V := single_le_sum (fun j _ => abs_nonneg (B j-B' j)) (mem_univ i)
  have hQ (i : ι) : |(1+η i)*B i-(1+η i)*B' i| ≤ (1+E)*|B i-B' i| := by
    rw [←mul_sub,abs_mul,abs_of_nonneg (by linarith [hη i] : 0 ≤ 1+η i)]
    exact mul_le_mul_of_nonneg_right (by linarith [hηE i]) (abs_nonneg _)
  have hc (i : ι) : |mixedPrimitive o u h η B scale a i-
      mixedPrimitive o u h η B' scale a i| ≤ R i+(if i=o then M else 0) := by
    by_cases hi : i=o
    · subst i
      simp only [mixedPrimitive,ite_true, if_true]
      have hb := marked_difference hu hu₁ (ha o) scale (∑ i, B i) ((1+η o)*B o)
        (∑ i, B' i) ((1+η o)*B' o)
      have htri := abs_sub ((∑ i, B i)-(∑ i, B' i)) (((1+η o)*B o)-((1+η o)*B' o))
      have hqo : |(1+η o)*B o-(1+η o)*B' o| ≤ (1+E)*V :=
        (hQ o).trans (mul_le_mul_of_nonneg_left (hiV o) (by linarith))
      have hd : D*(1-a o) ≤ D := by nlinarith [(ha o).1]
      have ht : |(∑ i, B i)-(∑ i, B' i)-((1+η o)*B o-(1+η o)*B' o)| ≤ D+(1+E)*V := by
        exact htri.trans (add_le_add_right hqo D)
      have hm : |primitive (marked u) 1 scale (∑ i, B i) ((1+η o)*B o) (a o)-
          primitive (marked u) 1 scale (∑ i, B' i) ((1+η o)*B' o) (a o)| ≤ M :=
        hb.trans (mul_le_mul_of_nonneg_left (by dsimp [D] at hd ht ⊢ <;> linarith) (by positivity))
      have hr : 0 ≤ R o := mul_nonneg (abs_nonneg scale)
        (add_nonneg (mul_nonneg hD (ha o).1) (mul_nonneg (by linarith) (abs_nonneg _)))
      exact hm.trans (le_add_of_nonneg_left hr)
    · simp only [mixedPrimitive,ite_eq_right hi,add_zero]
      exact (regular_difference (hh i hi) (ha i) ..).trans
        (mul_le_mul_of_nonneg_left (add_le_add_right (hQ i) _) (abs_nonneg _))
  rw [←sum_sub_distrib]
  calc
    _ ≤ ∑ i, |mixedPrimitive o u h η B scale a i-mixedPrimitive o u h η B' scale a i| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (R i+if i=o then M else 0) := sum_le_sum fun i _ => hc i
    _ = |scale| * (D+(1+E)*V)+M := by
      rw [sum_add_distrib,sum_ite_eq',ite_eq_left (Finset.mem_univ o)]
      dsimp [R,V]
      rw [←mul_sum,sum_add_distrib,←mul_sum,hasum,mul_one,←mul_sum]
    _ ≤ |scale| * (11+4*E)*V := by dsimp [M]; nlinarith [mul_le_mul_of_nonneg_left hDV (abs_nonneg scale)]


end
end UniformKServer.AlphaStability

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ProportionParameters
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                           
section

/-! Exact compact alpha update uniformly across unmarked, marked, and automatic
singleton stars. The fixed numerical envelopes are justified by the actual
held epoch geometry in EpochParameters; they are not competitive assumptions. -/
noncomputable section
namespace UniformKServer.ProportionParameters
open Finset
open scoped Classical
open UniformKServer.SimplexTracker UniformKServer.AlphaTracker
variable {ι : Type*} [Fintype ι]

theorem update {p : Parameters ι} (hp : valid p) (B a₀ : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (ha₀ : simplex a₀) :
    ∃ a, simplex a ∧ (∀ i, (∑ j, B j)*a i ≤ (1+eta p i)*B i) ∧
      (∑ j, B j)*movement a a₀ ≤ potential p B a₀-potential p B a := by
  rcases hp with ⟨hl,hc,hC,hη,hk⟩
  cases he : p.kind with
  | regular =>
    simp only [he] at hk
    have hu := regular_update p.h B a₀ p.ell p.ct p.C 1 2 hB hk.1 hl hc
      (by norm_num) (by norm_num) hη (by linarith) hk.2 ha₀
    obtain ⟨a,ha,_,hf,hm⟩ := hu
    exact ⟨a,ha,hf,by simpa only [potential,component,he] using hm⟩
  | marked o u =>
    simp only [he] at hk
    have hu := marked_update o u (1/2) 2 p.h B a₀ p.ell p.ct p.C 1
      hk.1 hk.2.1 (by norm_num) (by norm_num) (by norm_num) hk.2.2.1
      hk.2.2.2.1 hk.2.2.2.2.1 hk.2.2.2.2.2 hB hl hc (by norm_num) hη
      (by norm_num <;> linarith) ha₀
    obtain ⟨a,ha,_,hf,hm⟩ := hu
    exact ⟨a,ha,hf,by simpa only [potential,component,he] using hm⟩
  | singleton o =>
    simp only [he] at hk
    refine ⟨a₀,ha₀,?_,?_⟩
    · intro i
      have ha : a₀ i=1 := (singleton_sum o hk.1 a₀ i).symm.trans ha₀.2
      rw [singleton_sum o hk.1 B i,ha]
      simp [eta,hk.2 i]
    · simp [movement,potential,component,he]

/-- The same bound works on the entire old compact simplex, even when the
 filtered core input violates current coordinate feasibility. -/
theorem input_bound {p : Parameters ι} (hp : valid p) (B B' a : ι → ℝ)
    (ha : simplex a) :
    |potential p B a-potential p B' a| ≤
      15*(p.C*p.ell)*(∑ i, |B i-B' i|) := by
  have hC := C_pos hp
  have hscale : 0 ≤ p.C*p.ell := mul_nonneg hC.le hp.1.le
  have ha' : ∀ i, a i ∈ Set.Icc (0:ℝ) 1 :=
    fun i => ⟨ha.1 i,coordinate_le_one ha i⟩
  have hη := eta_nonneg hp
  have hη' := hp.2.2.2.1
  have hk := hp.2.2.2.2
  cases he : p.kind with
  | regular =>
    simp only [he] at hk
    have hb := AlphaStability.regular_input p.h (eta p) a B B' (p.C*p.ell) 1
      hk.1 ha' ha.2 hη hη'
    rw [abs_of_nonneg hscale] at hb
    change |(∑ i, regularG p.h B p.ell p.ct p.C i (a i))-
      (∑ i, regularG p.h B' p.ell p.ct p.C i (a i))| ≤ _ at hb
    have heq : potential p B a=∑ i, regularG p.h B p.ell p.ct p.C i (a i) := by simp [potential,component,he]
    have heq' : potential p B' a=∑ i, regularG p.h B' p.ell p.ct p.C i (a i) := by simp [potential,component,he]
    rw [heq,heq']
    refine hb.trans ?_
    have hn : 0 ≤ ∑ i, |B i-B' i| := sum_nonneg fun i _ => abs_nonneg _
    nlinarith
  | marked o u =>
    simp only [he] at hk
    have hb := AlphaStability.marked_input o p.h (eta p) a B B' (p.C*p.ell) 1 u
      hk.1 hk.2.1 hk.2.2.2.1 ha' ha.2 hη hη'
    rw [abs_of_nonneg hscale] at hb
    norm_num at hb
    simpa only [potential,component_mixed he,mul_comm (p.C*p.ell) 15] using hb
  | singleton o =>
    simp only [potential,component,he,sum_const_zero,sub_self,abs_zero]
    positivity

end UniformKServer.ProportionParameters

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AdaptiveAlpha
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! The two compact minimizations and intermediate common-core transport of
 companion §04, on a fixed child set. All movement estimates use the actual
 weighted L1 distance, including changing active domains and singleton states. -/
noncomputable section
namespace UniformKServer.AdaptiveAlpha
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem update {p : Config ι} (hp : valid p) (B a₀ : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hs : DomainTransport.Supported p.active B)
    (ha₀ : DomainTransport.simplex p.active a₀) :
    ∃ a, DomainTransport.simplex p.active a ∧
      (∀ i, (∑ j, B j)*a i ≤ (1+eta p i)*B i) ∧
      (∑ j, B j)*SimplexTracker.movement a a₀ ≤ potential p B a₀-potential p B a := by
  obtain ⟨a,ha,hf,hm⟩ := ProportionParameters.update hp.2 (fun i => B i)
    (fun i => a₀ i) (fun i => hB i) (DomainTransport.restrict_simplex ha₀)
  refine ⟨DomainTransport.extend p.active a,DomainTransport.extend_simplex ha,?_,?_⟩
  · intro i
    by_cases hi : i ∈ p.active
    · have h := hf ⟨i,hi⟩
      rw [DomainTransport.sum_restrict hs] at h
      simpa only [eta,DomainTransport.extend,hi,dite_true] using h
    · rw [DomainTransport.extend_supported p.active a i hi,hs i hi,mul_zero,mul_zero]
  · rw [DomainTransport.sum_restrict hs] at hm
    rw [DomainTransport.movement_extend p.active a ha₀.2.1]
    have he : (fun i : p.active => DomainTransport.extend p.active a i)=a := by
      funext i
      exact DomainTransport.extend_apply _ _ _
    simpa only [potential,he] using hm

theorem input_bound {p : Config ι} (hp : valid p) (B B' a : ι → ℝ)
    (ha : DomainTransport.simplex p.active a) :
    |potential p B a-potential p B' a| ≤ 15*scale p*(∑ i, |B i-B' i|) := by
  have h := ProportionParameters.input_bound hp.2 (fun i => B i) (fun i => B' i)
    (fun i => a i) (DomainTransport.restrict_simplex ha)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) (scale_nonneg hp)))
  rw [sum_coe_sort p.active (fun i : ι => |B i-B' i|)]
  exact sum_le_univ_sum_of_nonneg (fun i => abs_nonneg (B i-B' i))

/-- The first minimizer and genuine (possibly zero-weight) domain transport.
 Feasibility is proved before changing domains, not imposed on the old state. -/
theorem prepare {p q : Config ι} (hp : valid p) (hq : valid q)
    (B a₀ : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hpB : DomainTransport.Supported p.active B) (hqB : DomainTransport.Supported q.active B)
    (ha₀ : DomainTransport.simplex p.active a₀) :
    ∃ a b, DomainTransport.simplex p.active a ∧ DomainTransport.simplex q.active b ∧
      (∀ i, (∑ j, B j)*a i ≤ (1+eta p i)*B i) ∧
      (∑ j, B j)*SimplexTracker.movement a a₀ ≤ potential p B a₀-potential p B a ∧
      (∑ j, B j)*SimplexTracker.movement b a=0 ∧
      potential p B b=potential p B a ∧
      (∀ i, (∑ j, B j)*b i ≤ (1+eta p i)*B i) := by
  obtain ⟨a,ha,hf,hm⟩ := update hp B a₀ hB hpB ha₀
  have hS : 0 ≤ ∑ j, B j := sum_nonneg fun i _ => hB i
  rcases hS.eq_or_lt with hz | hpos
  · have hBzero : B=fun _ => 0 := by
      funext i
      have hi := single_le_sum (s:=univ) (f:=B) (fun j _ => hB j) (mem_univ i)
      exact le_antisymm (by linarith) (hB i)
    obtain ⟨b,hb⟩ := DomainTransport.exists_simplex hq.1
    refine ⟨a,b,ha,hb,hf,hm,?_,?_,?_⟩
    · rw [←hz,zero_mul]
    · rw [hBzero,potential_zero,potential_zero]
    · intro i; rw [←hz,zero_mul,hBzero]; simp
  · have hs : DomainTransport.Supported q.active a := by
      intro i hi
      have h := hf i
      rw [hqB i hi,mul_zero] at h
      exact le_antisymm (by nlinarith : a i ≤ 0) (ha.1 i)
    refine ⟨a,a,ha,⟨ha.1,hs,ha.2.2⟩,hf,hm,?_,rfl,hf⟩
    simp [SimplexTracker.movement]

/-- Complete deterministic minimizing part of one nonswitch step. `jump` is
 not a hypothesis: it is the actual prepared parameter-potential difference,
 available next for componentwise size-charge estimates. -/
theorem step {p q : Config ι} (hp : valid p) (hq : valid q)
    (Bstar Bnew a₀ : ι → ℝ) (hB : ∀ i, 0 ≤ Bstar i) (hBn : ∀ i, 0 ≤ Bnew i)
    (hST : (∑ i, Bstar i) ≤ ∑ i, Bnew i)
    (hpB : DomainTransport.Supported p.active Bstar)
    (hqB : DomainTransport.Supported q.active Bstar)
    (hqN : DomainTransport.Supported q.active Bnew)
    (ha₀ : DomainTransport.simplex p.active a₀) :
    ∃ a b, DomainTransport.simplex q.active a ∧ DomainTransport.simplex q.active b ∧
      (∀ i, (∑ j, Bnew j)*a i ≤ (1+eta q i)*Bnew i) ∧
      (∀ i, (∑ j, Bstar j)*b i ≤ (1+eta p i)*Bstar i) ∧
      (∑ j, Bnew j)*SimplexTracker.movement a a₀ ≤
        potential p Bstar a₀-potential q Bnew a+
        (potential q Bstar b-potential p Bstar b)+
        15*scale q*(∑ i, |Bnew i-Bstar i|)+4*((∑ i, Bnew i)-(∑ i, Bstar i)) := by
  obtain ⟨a₁,b,ha₁,hb,hf,hm,hfree,he,hfb⟩ := prepare hp hq Bstar a₀ hB hpB hqB ha₀
  obtain ⟨a,ha,hn,hmn⟩ := update hq Bnew b hBn hqN hb
  refine ⟨a,b,ha,hb,hn,hfb,?_⟩
  have hc := weight_comparison (sum_nonneg fun i _ => hB i) hST ha₀ hb ha hfree
  have hi := input_bound hq Bnew Bstar b hb
  have hi' := (le_abs_self _).trans hi
  rw [←he] at hm
  linarith

end UniformKServer.AdaptiveAlpha

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ConditionalLaw
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Finite posterior calculus for the finite-law construction.  All conditional
 laws are computed from fiber weights, including the zero-probability fibers.
 This supplies, rather than assumes, the all-step filtering identities. -/
namespace UniformKServer.ConditionalLaw
noncomputable section
attribute [local instance] Classical.propDecidable
open Finset
variable {Ω : Type*} [Fintype Ω]

theorem posterior_sub (w : Ω → ℝ) (F : Setoid Ω) (X Y : Ω → ℝ) (ω : Ω) :
    posterior w F (fun v => X v-Y v) ω = posterior w F X ω-posterior w F Y ω := by
  simp only [posterior,mul_sub,sum_sub_distrib]

theorem posterior_abs {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω)
    (X : Ω → ℝ) (ω : Ω) : |posterior w F X ω| ≤ posterior w F (fun v => |X v|) ω := by
  unfold posterior
  refine (abs_sum_le_sum_abs _ _).trans_eq ?_
  apply sum_congr rfl
  intro v _
  rw [abs_mul,abs_of_nonneg (kernel_nonneg hw F ω v)]

theorem expected_contraction {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω)
    (X Y : Ω → ℝ) :
    (∑ ω, w ω*|posterior w F X ω-posterior w F Y ω|) ≤
      ∑ ω, w ω*|X ω-Y ω| := by
  calc
    _ ≤ ∑ ω, w ω*posterior w F (fun v => |X v-Y v|) ω := sum_le_sum fun ω _ =>
      mul_le_mul_of_nonneg_left (by rw [←posterior_sub]; exact posterior_abs hw F _ ω) (hw ω)
    _ = _ := by
      simpa only [mul_one] using test_identity hw F (fun _ => 1) (fun v => |X v-Y v|) (by intro ω v _; rfl)

end
end UniformKServer.ConditionalLaw

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AdaptiveLedger
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Finite adaptive all-step accounting. This is the filtering telescope used
 twice in the allocation proof (primitive trackers and output-rule switching).
 No martingale assertion is conditioned on the later event being charged. -/
namespace UniformKServer.AdaptiveLedger
noncomputable section
open Finset UniformKServer.ConditionalLaw
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

def post (w : Ω → ℝ) (F : Setoid Ω) (X : Ω → ι → ℝ) (ω : Ω) (i : ι) : ℝ :=
  posterior w F (fun v => X v i) ω

def increment (w : Ω → ℝ) (F G : Setoid Ω) (a X : Ω → ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i, a ω i*(post w G X ω i-post w F X ω i)

def drift (w : Ω → ℝ) (F : Setoid Ω) (a X Y : Ω → ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i, a ω i*(post w F Y ω i-post w F X ω i)

/-- Expected filtering vanishes for old-history coefficients even if the
 subsequent domains, stopping events and output rules are chosen adaptively. -/
theorem filtering_zero {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F G : Setoid Ω)
    (hGF : ∀ ω v, G.r ω v → F.r ω v) (a X : Ω → ι → ℝ)
    (ha : ∀ i, measurable F (fun ω => a ω i)) :
    expect w (increment w F G a X)=0 := by
  simp only [expect,increment,mul_sum]
  rw [sum_comm]
  apply sum_eq_zero
  intro i _
  simpa only [post,mul_assoc] using filtering hw F G hGF (fun ω => a ω i) (fun ω => X ω i) (ha i)

/-- Hidden drift is evaluated at the new information, while old coefficient
 bounds alone suffice. The L1 contraction has coefficient one. -/
theorem drift_bound {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω)
    (a X Y : Ω → ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ ω i, |a ω i| ≤ C) :
    expect w (drift w F a X Y) ≤ C*expect w (fun ω => ∑ i, |Y ω i-X ω i|) := by
  have hp (ω : Ω) : drift w F a X Y ω ≤ C*(∑ i, |post w F Y ω i-post w F X ω i|) := by
    unfold drift
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (ha ω i) (abs_nonneg _))
  refine (expect_mono hw hp).trans ?_
  have hex : expect w (fun ω => ∑ i, |post w F Y ω i-post w F X ω i|) ≤
      expect w (fun ω => ∑ i, |Y ω i-X ω i|) := by
    simp only [expect,mul_sum]
    rw [sum_comm,sum_comm (s := univ) (t := univ) (f := fun ω i => w ω*|Y ω i-X ω i|)]
    apply sum_le_sum
    intro i _
    exact expected_contraction hw F (fun ω => Y ω i) (fun ω => X ω i)
  have he (Z : Ω → ℝ) : expect w (fun ω => C*Z ω)=C*expect w Z := by
    simp only [expect,mul_sum]
    apply sum_congr rfl
    intro ω _
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hex hC

/-- Generic ledger with genuine filtering increments and hidden L1 drift.
 One-step inequalities are deterministic algorithmic obligations, not a
 substitute for an assumed competitive bound. The conclusion sums all steps. -/
theorem telescope {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (F : ℕ → Setoid Ω) (hF : ∀ t ω v, (F (t+1)).r ω v → (F t).r ω v)
    (a X : ℕ → Ω → ι → ℝ) (P M Q : ℕ → Ω → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ t ω i, |a t ω i| ≤ C)
    (hmeas : ∀ t i, measurable (F t) (fun ω => a t ω i))
    (hstep : ∀ t ω, M t ω ≤ P t ω-P (t+1) ω+
      increment w (F t) (F (t+1)) (a t) (X t) ω+
      drift w (F (t+1)) (a t) (X t) (X (t+1)) ω+Q t ω) (H : ℕ) :
    (∑ t ∈ range H, expect w (M t)) ≤ expect w (P 0)-expect w (P H)+
      C*(∑ t ∈ range H, expect w (fun ω => ∑ i, |X (t+1) ω i-X t ω i|))+
      ∑ t ∈ range H, expect w (Q t) := by
  have hs (t : ℕ) : expect w (M t) ≤ expect w (P t)-expect w (P (t+1))+
      C*expect w (fun ω => ∑ i, |X (t+1) ω i-X t ω i|)+expect w (Q t) := by
    have h := expect_mono hw (hstep t)
    rw [expect_add,expect_add,expect_add,expect_sub,filtering_zero hw _ _ (hF t) _ _ (hmeas t),add_zero] at h
    have hd := drift_bound hw (F (t+1)) (a t) (X t) (X (t+1)) hC (ha t)
    linarith
  induction H with
  | zero => simp
  | succ H ih =>
    rw [sum_range_succ,sum_range_succ,sum_range_succ]
    have h := hs H
    linarith

end
end UniformKServer.AdaptiveLedger

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CoreFiltering
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Source §04, filtering with held core flags.  The old-state coefficients
are tested on every step, before selecting any refresh or active-domain event. -/
namespace UniformKServer.CoreFiltering
noncomputable section
open Finset UniformKServer.ConditionalLaw UniformKServer.AdaptiveLedger
variable {Ω ι R : Type*} [Fintype Ω] [Fintype ι] [Fintype R]

omit [Fintype Ω] [Fintype ι] [Fintype R] in
theorem lift_measurable (F : Setoid Ω) (a : Ω → ι → ℝ)
    (flag : Ω → ι → R → Bool)
    (ha : ∀ i, measurable F (fun ω => a ω i))
    (hf : ∀ ω v, F.r ω v → ∀ i r, flag ω i r=flag v i r) :
    ∀ ir, measurable F (fun ω => liftCoefficient a flag ω ir) := by
  intro ir ω v h
  simp only [liftCoefficient, hf ω v h,ha ir.1 ω v h]

end
end UniformKServer.CoreFiltering

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AdaptiveAlphaLinear
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                          
section

/-! Exact affine old-state alpha coefficients on changing active domains.
 These are computed from the genuine regular/marked improper primitives.
 Their uniform bound is used before, not after, testing refresh events. -/
noncomputable section

namespace UniformKServer.AdaptiveAlphaLinear
open Finset AdaptiveAlpha
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem bound {p : Config ι} (hp : valid p) (a : ι → ℝ)
    (ha : DomainTransport.simplex p.active a) (i : ι) :
    |coefficient p a i| ≤ 15*scale p := by
  have hai (j : ι) : a j ∈ Set.Icc (0:ℝ) 1 :=
    ⟨ha.1 j,by linarith [single_le_sum (s:=univ) (f:=a) (fun l _ => ha.1 l) (mem_univ j),ha.2.2]⟩
  exact AlphaLinear.coefficient_of_lipschitz (fun B => potential p B a) (coefficient p a)
    (15*scale p) (fun B => affine hp B a hai) (fun B B' => input_bound hp B B' a ha) i

end UniformKServer.AdaptiveAlphaLinear

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SideParameters
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Exact held side parameters and their uniform logarithmic bounds, companion
 §04. No lower bound on a side proportion and no cardinality factor is used. -/
namespace UniformKServer.SideParameters
noncomputable section

def offset (A a : ℝ) : ℝ := a/(A*height A a)
def slack (ell cw A a : ℝ) : ℝ := cw*height A a/ell

theorem offset_pos {A a : ℝ} (ha : 0 < a) (haA : a ≤ A) : 0 < offset A a := by
  have hA : 0 < A := ha.trans_le haA
  have hh : 0 < height A a := lt_of_lt_of_le zero_lt_one (height_ge_one ha haA)
  exact div_pos ha (mul_pos hA hh)

theorem offset_inverse {A a : ℝ} (ha : 0 < a) (haA : a ≤ A) :
    1/offset A a = height A a*(A/a) := by
  have hA : 0 < A := ha.trans_le haA
  have hh : 0 < height A a := lt_of_lt_of_le zero_lt_one (height_ge_one ha haA)
  unfold offset
  field_simp

/-- The side logarithm is at most (W+2)h throughout its compact domain. -/
theorem log_bound {A a s W : ℝ} (ha : 0 < a) (haA : a ≤ A)
    (hs : 0 ≤ s) (hsW : s ≤ W) :
    Real.log (1+s/offset A a) ≤ (W+2)*height A a := by
  have hA : 0 < A := ha.trans_le haA
  have hh := height_ge_one ha haA
  have hh₀ : 0 < height A a := by linarith
  have hz := offset_pos ha haA
  have hq : 1 ≤ A/a := (one_le_div ha).mpr haA
  have hp : 1 ≤ height A a*(A/a) := one_le_mul_of_one_le_of_one_le hh hq
  have ht : 1+s/offset A a ≤ (1+s)*height A a*(A/a) := by
    rw [div_eq_mul_one_div s,offset_inverse ha haA]
    nlinarith
  have hl := Real.log_le_log (by positivity : 0 < 1+s/offset A a) ht
  rw [Real.log_mul (by positivity : (1+s)*height A a ≠ 0) (div_pos hA ha).ne',
    Real.log_mul (by positivity : 1+s ≠ 0) hh₀.ne'] at hl
  have hl₁ := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+s)
  have hl₂ := Real.log_le_sub_one_of_pos hh₀
  have he : Real.log (A/a)=height A a-1 := by unfold height; ring
  rw [he] at hl
  have hW : 0 ≤ W := hs.trans hsW
  nlinarith

theorem slack_pos {ell cw A a : ℝ} (hell : 0 < ell) (hcw : 0 < cw)
    (ha : 0 < a) (haA : a ≤ A) : 0 < slack ell cw A a := by
  have hh : 0 < height A a := lt_of_lt_of_le zero_lt_one (height_ge_one ha haA)
  exact div_pos (mul_pos hcw hh) hell

theorem inverse_slack {ell cw A a : ℝ} (hell : 0 < ell) (hcw : 0 < cw)
    (ha : 0 < a) (haA : a ≤ A) :
    1/slack ell cw A a ≤ ell/cw := by
  have hh := height_ge_one ha haA
  have hh₀ : 0 < height A a := by linarith
  unfold slack
  rw [one_div_div]
  apply div_le_div_of_nonneg_left hell.le hcw
  nlinarith

theorem logarithm_over_slack {ell cw A a s W : ℝ} (hell : 0 < ell) (hcw : 0 < cw)
    (ha : 0 < a) (haA : a ≤ A) (hs : 0 ≤ s) (hsW : s ≤ W) :
    Real.log (1+s/offset A a)/slack ell cw A a ≤ (W+2)*ell/cw := by
  have hh₀ : 0 < height A a := lt_of_lt_of_le zero_lt_one (height_ge_one ha haA)
  have hslack := slack_pos hell hcw ha haA
  apply (div_le_iff₀ hslack).mpr
  calc
    _ ≤ (W+2)*height A a := log_bound ha haA hs hsW
    _ = _ := by unfold slack; field_simp

end
end UniformKServer.SideParameters

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AdaptiveSide
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Actual side-domain update with the exact held height/offset parameters.
 The source leaves fixed absolute constants flexible; W=11, C'=28 apply in
 the eventual b≤4, θ≤1 parameter interval. Empty side domains are included. -/
noncomputable section
namespace UniformKServer.AdaptiveSide
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

def theta (p : Config ι) : ι → ℝ := DomainTransport.extend p.active
  (fun i => SideParameters.slack p.ell p.cw p.A (p.a i))
def offset (p : Config ι) : ι → ℝ := DomainTransport.extend p.active
  (fun i => SideParameters.offset p.A (p.a i))

def valid (p : Config ι) : Prop := 1 ≤ p.ell ∧ 0 < p.cw ∧ 0 < p.b ∧ p.b ≤ 4 ∧
  (∀ i, 0 < p.a i ∧ p.a i ≤ p.A) ∧
  (∀ i, SideParameters.slack p.ell p.cw p.A (p.a i) ≤ 1)

def potential (p : Config ι) (B : ι → ℝ) (D : ℝ) (w : ι → ℝ) : ℝ :=
  SideTracker.potential p.b 28 D (theta p) (offset p) B w

omit [Fintype ι] in
theorem theta_pos {p : Config ι} (hp : valid p) (i : p.active) : 0 < theta p i := by
  rw [theta,DomainTransport.extend_apply]
  exact SideParameters.slack_pos (by linarith [hp.1]) hp.2.1
    (hp.2.2.2.2.1 i).1 (hp.2.2.2.2.1 i).2

omit [Fintype ι] in
theorem offset_pos {p : Config ι} (hp : valid p) (i : p.active) : 0 < offset p i := by
  rw [offset,DomainTransport.extend_apply]
  exact SideParameters.offset_pos (hp.2.2.2.2.1 i).1 (hp.2.2.2.2.1 i).2

omit [Fintype ι] in
theorem theta_le {p : Config ι} (hp : valid p) (i : p.active) : theta p i ≤ 1 := by
  rw [theta,DomainTransport.extend_apply]
  exact hp.2.2.2.2.2 i

omit [Fintype ι] in
theorem slope_nonneg {p : Config ι} (hp : valid p) : 0 ≤ slope p := by
  have hq : 0 ≤ p.ell/p.cw := div_nonneg (by linarith [hp.1]) hp.2.1.le
  unfold slope
  positivity

theorem restrict_potential {p : Config ι} (B w : ι → ℝ) (D : ℝ)
    (hw : DomainTransport.Supported p.active w) :
    potential p B D w = SideTracker.potential p.b 28 D (fun i : p.active => theta p i)
      (fun i => offset p i) (fun i => B i) (fun i => w i) := by
  exact (DomainTransport.potential_restrict
    (fun i => SideTracker.coordinate p.b (theta p i) (offset p i) 28 (B i) D)
    hw (fun _ _ => coordinate_zero ..)).symm

theorem update {p : Config ι} (hp : valid p) (B w₀ : ι → ℝ) (D S : ℝ)
    (hD : 0 ≤ D) (hB : ∀ i, 0 ≤ B i) (hs : DomainTransport.Supported p.active B)
    (hS : (∑ i, B i) ≤ S) (hw₀ : DomainTransport.domain p.active 11 w₀) :
    ∃ w, DomainTransport.domain p.active 11 w ∧
      (∀ i, D*w i ≤ (p.b+theta p i)*B i) ∧
      (S ≤ 2*D → ∀ i, p.b*B i-theta p i*offset p i*D ≤ D*w i) ∧
      D*SideTracker.movement w w₀ ≤ potential p B D w₀-potential p B D w := by
  obtain ⟨w,hw,hf,hl,hm⟩ := SideTracker.side_update p.b 28 D 11 5 S
    (fun i : p.active => theta p i) (fun i => offset p i) (fun i => B i) (fun i => w₀ i)
    hp.2.2.1 hD (by norm_num) (by norm_num) (theta_pos hp) (offset_pos hp)
    (fun i => hB i) (by rw [DomainTransport.sum_restrict hs]; exact hS)
    (fun i => by linarith [hp.2.2.2.1,theta_le hp i])
    (fun i => by linarith [hp.2.2.2.1,theta_le hp i]) (restrict_domain hw₀)
  refine ⟨DomainTransport.extend p.active w,extend_domain hw,?_,?_,?_⟩
  · intro i
    by_cases hi : i ∈ p.active
    · simpa only [DomainTransport.extend,hi,dite_true] using hf ⟨i,hi⟩
    · rw [hs i hi,DomainTransport.extend_supported p.active w i hi,mul_zero,mul_zero]
  · intro hSD i
    by_cases hi : i ∈ p.active
    · simpa only [DomainTransport.extend,hi,dite_true] using hl hSD ⟨i,hi⟩
    · rw [hs i hi,DomainTransport.extend_supported p.active w i hi]
      simp [theta,DomainTransport.extend,hi]
  · rw [restrict_potential B w₀ D hw₀.2.1,
      restrict_potential B (DomainTransport.extend p.active w) D (DomainTransport.extend_supported _ _)]
    have he : (fun i : p.active => DomainTransport.extend p.active w i)=w := by
      funext i
      exact DomainTransport.extend_apply _ _ _
    rw [he]
    change D*SimplexTracker.movement (DomainTransport.extend p.active w) w₀ ≤ _
    rw [DomainTransport.movement_extend p.active w hw₀.2.1]
    exact hm

omit [Fintype ι] in
theorem parameter_bounds {p : Config ι} (hp : valid p) (i : p.active) {s : ℝ}
    (hs : 0 ≤ s) (hsW : s ≤ 11) :
    1/theta p i ≤ p.ell/p.cw ∧
      Real.log (1+s/offset p i)/theta p i ≤ 13*(p.ell/p.cw) ∧
      p.b+theta p i/2 ≤ 5 := by
  have hθ := theta_le hp i
  refine ⟨?_,?_,by linarith [hp.2.2.2.1]⟩
  · rw [theta,DomainTransport.extend_apply]
    exact SideParameters.inverse_slack (by linarith [hp.1]) hp.2.1
      (hp.2.2.2.2.1 i).1 (hp.2.2.2.2.1 i).2
  · rw [theta,offset,DomainTransport.extend_apply,DomainTransport.extend_apply]
    have h := SideParameters.logarithm_over_slack (by linarith [hp.1] : 0 < p.ell) hp.2.1
      (hp.2.2.2.2.1 i).1 (hp.2.2.2.2.1 i).2 hs hsW
    norm_num at h
    simpa only [mul_div_assoc] using h

omit [Fintype ι] in
theorem coordinate_bound {p : Config ι} (hp : valid p) (i : p.active) {w B D : ℝ}
    (hw : 0 ≤ w) (hwW : w ≤ 11) :
    |SideTracker.coordinate p.b (theta p i) (offset p i) 28 B D w| ≤
      slope p*(|D| *w+|B|) := by
  obtain ⟨hT,hJ,hQ⟩ := parameter_bounds hp i hw hwW
  have h := SideStability.coordinate_bound hp.2.2.1.le (theta_pos hp i) (offset_pos hp i)
    hw hT hJ hQ 28 B D
  rw [abs_of_pos (by norm_num : (0:ℝ)<28)] at h
  refine h.trans ?_
  have hq : 0 ≤ p.ell/p.cw := div_nonneg (by linarith [hp.1]) hp.2.1.le
  have hD := abs_nonneg D
  have hB := abs_nonneg B
  have hDw := mul_nonneg hD hw
  unfold slope
  nlinarith

theorem input_bound {p : Config ι} (hp : valid p) (B B' w : ι → ℝ) (D D' : ℝ)
    (hw : DomainTransport.domain p.active 11 w) :
    |potential p B D w-potential p B' D' w| ≤
      slope p*((∑ i, |B i-B' i|)+|D-D'|) := by
  rw [restrict_potential B w D hw.2.1,restrict_potential B' w D' hw.2.1]
  have hq : 0 ≤ p.ell/p.cw := div_nonneg (by linarith [hp.1]) hp.2.1.le
  have hb (i : p.active) := parameter_bounds hp i (hw.1 i) (coordinate_le_sum hw i)
  have h := SideStability.input_bound p.b 28 D D' (p.ell/p.cw) (13*(p.ell/p.cw)) 5 11
    (fun i : p.active => theta p i) (fun i => offset p i) (fun i => B i)
    (fun i => B' i) (fun i => w i) hp.2.2.1.le (theta_pos hp) (offset_pos hp)
    (restrict_domain hw) (fun i => (hb i).1) (fun i => (hb i).2.1)
    (fun i => (hb i).2.2) (by linarith)
  rw [abs_of_pos (by norm_num : (0:ℝ)<28)] at h
  have hsum : (∑ i : p.active, |B i-B' i|) ≤ ∑ i, |B i-B' i| := by
    rw [sum_coe_sort p.active (fun i : ι => |B i-B' i|)]
    exact sum_le_univ_sum_of_nonneg (fun i => abs_nonneg (B i-B' i))
  have hn : 0 ≤ ∑ i, |B i-B' i| := sum_nonneg fun _ _ => abs_nonneg _
  have hd := abs_nonneg (D-D')
  refine h.trans ?_
  unfold slope
  nlinarith [mul_le_mul_of_nonneg_left hsum hq, mul_nonneg hq hn, mul_nonneg hq hd]

theorem prepare {p q : Config ι} (hp : valid p) (B w₀ : ι → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hB : ∀ i, 0 ≤ B i)
    (hpB : DomainTransport.Supported p.active B) (hqB : DomainTransport.Supported q.active B)
    (hw₀ : DomainTransport.domain p.active 11 w₀) :
    ∃ w b, DomainTransport.domain p.active 11 w ∧ DomainTransport.domain q.active 11 b ∧
      (∀ i, D*b i ≤ (p.b+theta p i)*B i) ∧
      D*SideTracker.movement w w₀ ≤ potential p B D w₀-potential p B D w ∧
      D*SideTracker.movement b w=0 ∧ potential p B D b=potential p B D w := by
  obtain ⟨w,hw,hf,_,hm⟩ := update hp B w₀ D (∑ i, B i) hD hB hpB le_rfl hw₀
  obtain ⟨hb,hfree,he⟩ := DomainTransport.prepared_side hw hD hqB
    (fun i _ => hf i)
  refine ⟨w,DomainTransport.delete q.active w,hw,hb,?_,hm,hfree,he⟩
  intro i
  unfold DomainTransport.delete
  split_ifs with hi
  · exact hf i
  · rw [hqB i hi,mul_zero,mul_zero]

/-- Actual two-minimizer nonswitch operation. Parameter change is left as the
 exact prepared difference for the following size-charge lemma, not an assumed
 movement estimate. Both minimizations use the new nonnegative D. -/
theorem step {p q : Config ι} (hp : valid p) (hq : valid q)
    (Bstar Bnew w₀ : ι → ℝ) (D S : ℝ) (hD : 0 ≤ D)
    (hB : ∀ i, 0 ≤ Bstar i) (hBn : ∀ i, 0 ≤ Bnew i)
    (hS : (∑ i, Bnew i) ≤ S)
    (hpB : DomainTransport.Supported p.active Bstar)
    (hqB : DomainTransport.Supported q.active Bstar)
    (hqN : DomainTransport.Supported q.active Bnew)
    (hw₀ : DomainTransport.domain p.active 11 w₀) :
    ∃ w b, DomainTransport.domain q.active 11 w ∧ DomainTransport.domain q.active 11 b ∧
      (∀ i, D*w i ≤ (q.b+theta q i)*Bnew i) ∧
      (S ≤ 2*D → ∀ i, q.b*Bnew i-theta q i*offset q i*D ≤ D*w i) ∧
      (∀ i, D*b i ≤ (p.b+theta p i)*Bstar i) ∧
      D*SideTracker.movement w w₀ ≤ potential p Bstar D w₀-potential q Bnew D w+
        (potential q Bstar D b-potential p Bstar D b)+slope q*(∑ i, |Bnew i-Bstar i|) := by
  obtain ⟨w₁,b,hw₁,hb,hf,hm,hfree,he⟩ := prepare hp Bstar w₀ D hD hB hpB hqB hw₀
  obtain ⟨w,hw,hu,hl,hmn⟩ := update hq Bnew b D S hD hBn hqN hS hb
  refine ⟨w,b,hw,hb,hu,hl,hf,?_⟩
  have ht := mul_le_mul_of_nonneg_left (triangle w b w₀) hD
  have hp' := mul_le_mul_of_nonneg_left (triangle b w₁ w₀) hD
  rw [mul_add,hfree,zero_add] at hp'
  have hi := input_bound hq Bnew Bstar b D D hb
  rw [sub_self,abs_zero,add_zero] at hi
  have hi' := (le_abs_self _).trans hi
  rw [←he] at hm
  nlinarith

end UniformKServer.AdaptiveSide

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AllocationEpoch
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Source companion §03, cumulative-variation epochs.  Variation credit is
carried in one potential; a forced parent refresh discards unused credit, and
never creates a fresh initialization allowance. -/
namespace UniformKServer.AllocationEpoch
noncomputable section
open Finset

theorem credit_step {x y d : ℝ} {s : State} (hs : valid x s)
    (hd : |y-x| ≤ d) (parent : Bool) :
    charge s x y d parent + 203*(update s y d parent).credit ≤
      203*s.credit+203*d+(if parent then x+y else 0) := by
  classical
  by_cases h : fires s d parent
  · simp only [charge,update,ite_eq_left h,initial,mul_zero,add_zero]
    cases parent with
    | false =>
      have hf : s.base/100 < s.credit+d := by simpa [fires] using h
      have hh := wholesale_bound hs hd hf
      simp only [Bool.false_eq_true,↓reduceIte]
      linarith
    | true =>
      simp only [↓reduceIte]
      have hdn : 0 ≤ d := (abs_nonneg _).trans hd
      linarith [hs.2.1]
  · simp only [charge,update,ite_eq_right h,zero_add]
    have hp : parent = false := by
      cases parent <;> simp_all [fires]
    rw [hp]
    simp only [Bool.false_eq_true,↓reduceIte,add_zero]
    ring_nf
    exact le_rfl

theorem schedule_budget {x d : ℕ → ℝ} (hx : ∀ t, 0 ≤ x t)
    (hd : ∀ t, |x (t+1)-x t| ≤ d t) (parent : ℕ → Bool) (H : ℕ) :
    (∑ t ∈ range H, charge (schedule x d parent t) (x t) (x (t+1)) (d t) (parent t)) ≤
      203*(∑ t ∈ range H, d t)+
        ∑ t ∈ range H, (if parent t then x t+x (t+1) else 0) := by
  have hsum : ∀ H,
      (∑ t ∈ range H, charge (schedule x d parent t) (x t) (x (t+1)) (d t) (parent t)) +
        203*(schedule x d parent H).credit ≤
      203*(∑ t ∈ range H, d t)+
        ∑ t ∈ range H, (if parent t then x t+x (t+1) else 0) := by
    intro H
    induction H with
    | zero => simp [schedule,initial]
    | succ H ih =>
      rw [sum_range_succ,sum_range_succ,sum_range_succ]
      have ht := credit_step (schedule_valid hx hd parent H) (hd H) (parent H)
      change charge (schedule x d parent H) (x H) (x (H+1)) (d H) (parent H) +
        203*(schedule x d parent (H+1)).credit ≤ _ at ht
      linarith
  have hv := (schedule_valid hx hd parent H).2.1
  linarith [hsum H]

end
end UniformKServer.AllocationEpoch

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AllocationOutputs
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                        
section

/-! Exact two child-output rules of companion §05.  The estimates retain one
copy of the parent variation; this coefficient must be independent of k for
the tree absorption.  Input inequalities below are the explicit rank, cap,
and proportion conditions, not an assumed output feasibility statement. -/
namespace UniformKServer.AllocationOutputs
noncomputable section
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rule_two_side (d w : ι → ℝ) (q D : ℝ) (o i : ι) (hi : i ≠ o) :
    ruleTwo d w q D o i = d i-D*w i := ite_eq_right hi

theorem rule_two_budget (d w : ι → ℝ) (q D : ℝ) (o : ι) :
    (∑ i, ruleTwo d w q D o i) ≤ q := by
  rw [←sum_erase_add _ _ (mem_univ o)]
  have hs : (∑ i ∈ univ.erase o, ruleTwo d w q D o i) =
      ∑ i ∈ univ.erase o, (d i-D*w i) := by
    apply sum_congr rfl
    intro i hi
    exact rule_two_side d w q D o i (ne_of_mem_erase hi)
  rw [hs]
  simp only [ruleTwo,ite_true, if_true]
  linarith [min_le_right (d o) (q-∑ i ∈ univ.erase o, (d i-D*w i))]

theorem rule_two_upper (d w : ι → ℝ) (q D : ℝ) (o i : ι)
    (hD : 0 ≤ D) (hw : ∀ i, i ≠ o → 0 ≤ w i) :
    ruleTwo d w q D o i ≤ d i := by
  by_cases hi : i=o
  · subst i
    simp only [ruleTwo,ite_true, if_true]
    exact min_le_left _ _
  · rw [rule_two_side d w q D o i hi]
    exact sub_le_self _ (mul_nonneg hD (hw i hi))

/-- Exact lower bounds of Rule II, with the side lower tracker inequality
and the aggregate side slack paid from the dominant parameter gap. -/
theorem rule_two_lower (n B fp fc b β : ι → ℝ) (w θ z : ι → ℝ)
    (q D βv βplus : ℝ) (o : ι)
    (hB : ∀ i, 0 ≤ B i) (hparent : (∑ i, (n i-βv*B i+fp i)) ≤ q)
    (hparam : βv ≤ βplus)
    (hcap : ∀ i, fc i ≤ b i)
    (hsideCap : ∀ i, i ≠ o → b i ≤ fp i)
    (hupper : ∀ i, i ≠ o → D*w i ≤ β i*B i)
    (hlower : ∀ i, i ≠ o → βplus*B i-D*θ i*z i ≤ D*w i)
    (hslack : D*(∑ i ∈ univ.erase o, θ i*z i) ≤
      (n o-βv*B o+fp o)-lower n B fc β o)
    (hβo : 0 ≤ β o) :
    ∀ i, lower n B fc β i ≤ ruleTwo (fun i => n i+b i) w q D o i := by
  intro i
  by_cases hi : i=o
  · subst i
    simp only [ruleTwo,ite_true, if_true]
    apply le_min
    · dsimp [lower]
      nlinarith [hcap o,mul_nonneg hβo (hB o)]
    · have hs : (∑ i ∈ univ.erase o, (n i+b i-D*w i)) ≤
          (∑ i ∈ univ.erase o, (n i-βv*B i+fp i))+
            D*(∑ i ∈ univ.erase o, θ i*z i) := by
        rw [mul_sum,←sum_add_distrib]
        apply sum_le_sum
        intro i hi
        have hio := ne_of_mem_erase hi
        have hp := mul_le_mul_of_nonneg_right hparam (hB i)
        nlinarith [hsideCap i hio,hlower i hio]
      rw [←sum_erase_add _ _ (mem_univ o)] at hparent
      linarith
  · rw [rule_two_side _ _ _ _ _ _ hi]
    dsimp [lower]
    linarith [hupper i hi,hcap i]

end
end UniformKServer.AllocationOutputs

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AllocationMovement
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

/-! Companion §05, the exact non-wholesale hole identities and movement
bounds. The coefficient of the parent variation is exactly one. -/
namespace UniformKServer.AllocationOutputs
noncomputable section
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem holes_two_movement (a b : ι → ℝ) (p q : ℝ) (o : ι) :
    variation (holesTwo p a o) (holesTwo q b o) ≤ |q-p|+2*sideVariation a b o := by
  rw [variation,←sum_erase_add _ _ (mem_univ o)]
  have hs : (∑ i ∈ univ.erase o, |holesTwo q b o i-holesTwo p a o i|) =
      sideVariation a b o := by
    apply sum_congr rfl
    intro i hi
    simp only [holesTwo,ite_eq_right (ne_of_mem_erase hi)]
  rw [hs]
  simp only [holesTwo,ite_true, if_true]
  have hm := abs_max_sub_max_le_abs (q-sideTotal b o) (p-sideTotal a o) 0
  have he : (q-sideTotal b o)-(p-sideTotal a o) = (q-p)-(sideTotal b o-sideTotal a o) := by ring
  rw [he] at hm
  have ht := (abs_sub (q-p) (sideTotal b o-sideTotal a o)).trans
    (add_le_add le_rfl (side_total_difference a b o))
  linarith

theorem rule_two_holes (d w : ι → ℝ) (q D : ℝ) (o i : ι)
    (hw : 0 ≤ sideTotal (fun j => D*w j) o) :
    d i-ruleTwo d w q D o i = holesTwo (excess d q) (fun j => D*w j) o i := by
  by_cases hi : i=o
  · subst i
    simp only [ruleTwo,holesTwo,ite_true, if_true]
    have he : (∑ i, d i)-q-sideTotal (fun j => D*w j) o =
        d o-(q-∑ j ∈ univ.erase o, (d j-D*w j)) := by
      rw [←sum_erase_add _ _ (mem_univ o),sum_sub_distrib]
      unfold sideTotal
      ring
    have hm : d o-min (d o) (q-∑ j ∈ univ.erase o, (d j-D*w j)) =
        max (d o-(q-∑ j ∈ univ.erase o, (d j-D*w j))) 0 := by
      rcases le_total (d o) (q-∑ j ∈ univ.erase o, (d j-D*w j)) with h|h
      · rw [min_eq_left h,max_eq_right (sub_nonpos.mpr h),sub_self]
      · rw [min_eq_right h,max_eq_left (sub_nonneg.mpr h)]
    rw [hm,←he]
    unfold excess
    by_cases hh : 0 ≤ (∑ i, d i)-q
    · rw [max_eq_left hh]
    · have hz : (∑ i, d i)-q ≤ 0 := le_of_not_ge hh
      rw [max_eq_right hz,max_eq_right (by linarith),max_eq_right (by linarith)]
  · simp only [ruleTwo,holesTwo,ite_eq_right hi]
    ring

theorem rule_two_movement (d₀ d₁ w₀ w₁ : ι → ℝ) (q₀ q₁ D₀ D₁ : ℝ) (o : ι)
    (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁) (hw₀ : ∀ i, 0 ≤ w₀ i) (hw₁ : ∀ i, 0 ≤ w₁ i) :
    variation (ruleTwo d₀ w₀ q₀ D₀ o) (ruleTwo d₁ w₁ q₁ D₁ o) ≤
      |q₁-q₀|+2*variation d₀ d₁+2*D₁*variation w₀ w₁+2*|D₁-D₀| *(∑ i, w₀ i) := by
  have hω₀ : 0 ≤ sideTotal (fun i => D₀*w₀ i) o :=
    sum_nonneg (fun i _ => mul_nonneg hD₀ (hw₀ i))
  have hω₁ : 0 ≤ sideTotal (fun i => D₁*w₁ i) o :=
    sum_nonneg (fun i _ => mul_nonneg hD₁ (hw₁ i))
  have he₀ : ruleTwo d₀ w₀ q₀ D₀ o = fun i => d₀ i-holesTwo (excess d₀ q₀) (fun j => D₀*w₀ j) o i := by
    funext i
    linarith [rule_two_holes d₀ w₀ q₀ D₀ o i hω₀]
  have he₁ : ruleTwo d₁ w₁ q₁ D₁ o = fun i => d₁ i-holesTwo (excess d₁ q₁) (fun j => D₁*w₁ j) o i := by
    funext i
    linarith [rule_two_holes d₁ w₁ q₁ D₁ o i hω₁]
  rw [he₀,he₁]
  have hm := outputs_from_holes d₀ d₁ (holesTwo (excess d₀ q₀) (fun j => D₀*w₀ j) o)
    (holesTwo (excess d₁ q₁) (fun j => D₁*w₁ j) o)
  have hh := holes_two_movement (fun j => D₀*w₀ j) (fun j => D₁*w₁ j) (excess d₀ q₀) (excess d₁ q₁) o
  have hs := side_variation_le (fun j => D₀*w₀ j) (fun j => D₁*w₁ j) o
  have hv := scalar_vector_movement w₀ w₁ D₀ D₁ hD₁ hw₀
  have he := excess_difference d₀ d₁ q₀ q₁
  nlinarith

end
end UniformKServer.AllocationOutputs

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AllocationSchedule
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

/-! Exact coarse held-size schedule in companion §03. The deterministic
potential below pays relative refreshes and both hysteretic on/off transitions
from variation of the underlying persistent rank estimates. In particular it
does not restart any initialization allowance when a child becomes active. -/
namespace UniformKServer.AllocationSchedule
noncomputable section
open Finset

def potential (K c x : ℝ) (s : Option ℝ) : ℝ :=
  K*|x-size s| + match s with | none => 0 | some _ => 2*(K+1)*c

theorem failure_cost {δ b x K : ℝ} (hδ : 0 < δ) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (hK : 1+2/δ ≤ K) (hf : ¬compared δ b x) : b+x ≤ K*|x-b| := by
  have hd : 2 ≤ (K-1)*δ := (div_le_iff₀ hδ).mp (by linarith : 2/δ ≤ K-1)
  have hK' : δ+2 ≤ K*δ := by nlinarith
  unfold compared at hf
  push Not at hf
  by_cases h : x ≤ (1+δ)*b
  · have h' := hf h
    have hbx : x ≤ b := by nlinarith
    rw [abs_of_nonpos (by linarith)]
    have hgap : δ*x ≤ b-x := by nlinarith
    have hbound := mul_le_mul_of_nonneg_right hK' (sub_nonneg.mpr hbx)
    have hδb : δ*(b+x) ≤ (δ+2)*(b-x) := by nlinarith
    nlinarith
  · have h' : (1+δ)*b < x := lt_of_not_ge h
    have hbx : b ≤ x := by nlinarith
    rw [abs_of_nonneg (by linarith)]
    have hbound := mul_le_mul_of_nonneg_right hK' (sub_nonneg.mpr hbx)
    have hδb : δ*(b+x) ≤ (δ+2)*(x-b) := by nlinarith
    nlinarith

theorem relative_drop {δ b x K : ℝ} (hδ : 0 < δ) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (hK : 1+2/δ ≤ K) :
    charge b (relativeUpdate δ b x)+K*|x-relativeUpdate δ b x| ≤ K*|x-b| := by
  unfold relativeUpdate
  split
  · rw [charge_self,zero_add]
  · rename_i hf
    rw [sub_self,abs_zero,mul_zero,add_zero]
    exact (charge_le hb hx).trans (failure_cost hδ hb hx hK hf)

theorem potential_nonneg {K c x : ℝ} (s : Option ℝ) (hK : 0 ≤ K) (hc : 0 ≤ c) :
    0 ≤ potential K c x s := by
  cases s <;> dsimp [potential] <;> positivity

theorem update_drop {c δ K : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hK : 3 ≤ K) (hKδ : 1+2/δ ≤ K) (s : Option ℝ) {x : ℝ}
    (hs : 0 ≤ size s) (hx : 0 ≤ x) :
    charge (size s) (size (update c δ s x))+potential K c x (update c δ s x) ≤
      potential K c x s := by
  cases s with
  | none =>
    simp only [update]
    split
    · rename_i hxhigh
      have hch : charge 0 x ≤ x := by simpa using charge_le (le_refl (0:ℝ)) hx
      simp only [size,potential,sub_self,abs_zero,mul_zero,zero_add,sub_zero,abs_of_nonneg hx,add_zero]
      have hm := mul_nonneg (by linarith : 0 ≤ K-1) (by linarith : 0 ≤ x-5*c)
      have hh := mul_nonneg (by linarith : 0 ≤ 3*K-7) hc
      nlinarith
    · simp only [size,charge_self,potential,zero_add]
      exact le_rfl
  | some b =>
    have hb : 0 ≤ b := hs
    simp only [update]
    split
    · rename_i hxlow
      have hch : charge b 0 ≤ b := by simpa using charge_le hb (le_refl (0:ℝ))
      simp only [size,potential,sub_zero,abs_of_nonneg hx,add_zero]
      have htri : b ≤ |x-b|+x := by linarith [neg_le_abs (x-b)]
      have hm := mul_nonneg (by linarith : 0 ≤ K-1) (abs_nonneg (x-b))
      have hh := mul_le_mul_of_nonneg_left hxlow (by linarith : 0 ≤ K+1)
      linarith
    · simp only [size,potential]
      linarith [relative_drop hδ hb hx hKδ]

theorem potential_change {K c x y : ℝ} (s : Option ℝ) (hK : 0 ≤ K) :
    potential K c y s ≤ potential K c x s+K*|y-x| := by
  have ht : |y-size s| ≤ |x-size s|+|y-x| := by
    convert abs_add_le (x-size s) (y-x) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_left ht hK
  unfold potential
  linarith

theorem update_step {c δ K : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hK : 3 ≤ K) (hKδ : 1+2/δ ≤ K) (s : Option ℝ) {x y : ℝ}
    (hs : 0 ≤ size s) (hy : 0 ≤ y) :
    charge (size s) (size (update c δ s y))+potential K c y (update c δ s y) ≤
      potential K c x s+K*|y-x| :=
  (update_drop hc hδ hK hKδ s hs hy).trans (potential_change s (by linarith))

theorem schedule_budget {c δ K : ℝ} {x : ℕ → ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hK : 3 ≤ K) (hKδ : 1+2/δ ≤ K) (hx : ∀ t, 0 ≤ x t) (H : ℕ) :
    (∑ t ∈ range H, charge (size (schedule c δ x t)) (size (schedule c δ x (t+1)))) ≤
      K*(∑ t ∈ range H, |x (t+1)-x t|)+potential K c (x 0) (schedule c δ x 0) := by
  have hsum : ∀ H,
      (∑ t ∈ range H, charge (size (schedule c δ x t)) (size (schedule c δ x (t+1)))) +
        potential K c (x H) (schedule c δ x H) ≤
      K*(∑ t ∈ range H, |x (t+1)-x t|)+potential K c (x 0) (schedule c δ x 0) := by
    intro H
    induction H with
    | zero => simp
    | succ H ih =>
      rw [sum_range_succ,sum_range_succ]
      have ht := update_step hc hδ hK hKδ (schedule c δ x H) (x:=x H)
        (schedule_nonneg hx H) (hx (H+1))
      change charge (size (schedule c δ x H)) (size (schedule c δ x (H+1))) +
        potential K c (x (H+1)) (schedule c δ x (H+1)) ≤
        potential K c (x H) (schedule c δ x H)+K*|x (H+1)-x H| at ht
      nlinarith
  have hp := potential_nonneg (schedule c δ x H) (by linarith : 0 ≤ K) hc (x:=x H)
  linarith [hsum H]

theorem held_nonneg {δ : ℝ} {x : ℕ → ℝ} (hx : ∀ t, 0 ≤ x t) :
    ∀ t, 0 ≤ held δ x t := by
  intro t
  induction t with
  | zero => exact hx 0
  | succ t ih => exact relative_nonneg ih (hx (t+1))

theorem relative_step {δ K x y b : ℝ} (hδ : 0 < δ) (hK : 1+2/δ ≤ K)
    (hb : 0 ≤ b) (hy : 0 ≤ y) :
    charge b (relativeUpdate δ b y)+K*|y-relativeUpdate δ b y| ≤
      K*|x-b|+K*|y-x| := by
  have hKpos : 0 ≤ K := by have := div_pos (by norm_num : (0:ℝ)<2) hδ; linarith
  have htri : |y-b| ≤ |x-b|+|y-x| := by
    convert abs_add_le (x-b) (y-x) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  exact (relative_drop hδ hb hy hK).trans (by nlinarith [mul_le_mul_of_nonneg_left htri hKpos])

theorem held_budget {δ K : ℝ} {x : ℕ → ℝ} (hδ : 0 < δ)
    (hK : 1+2/δ ≤ K) (hx : ∀ t, 0 ≤ x t) (H : ℕ) :
    (∑ t ∈ range H, charge (held δ x t) (held δ x (t+1))) ≤
      K*(∑ t ∈ range H, |x (t+1)-x t|) := by
  have hKpos : 0 ≤ K := by have := div_pos (by norm_num : (0:ℝ)<2) hδ; linarith
  have hsum : ∀ H,
      (∑ t ∈ range H, charge (held δ x t) (held δ x (t+1))) +
        K*|x H-held δ x H| ≤ K*(∑ t ∈ range H, |x (t+1)-x t|) := by
    intro H
    induction H with
    | zero => simp [held]
    | succ H ih =>
      rw [sum_range_succ,sum_range_succ]
      have ht := relative_step (x:=x H) hδ hK (held_nonneg (δ:=δ) hx H) (hx (H+1))
      change charge (held δ x H) (held δ x (H+1)) + K*|x (H+1)-held δ x (H+1)| ≤
        K*|x H-held δ x H|+K*|x (H+1)-x H| at ht
      nlinarith
  nlinarith [hsum H,mul_nonneg hKpos (abs_nonneg (x H-held δ x H))]

theorem initial_potential_bound {c δ K x : ℝ} (hc : 0 ≤ c) (hK : 1 ≤ K)
    (hx : 0 ≤ x) : potential K c x (update c δ none x) ≤ 5*K*c := by
  simp only [update]
  split
  · simp only [potential,size,sub_self,abs_zero,mul_zero,zero_add]
    nlinarith
  · simp only [potential,size,sub_zero,abs_of_nonneg hx,add_zero]
    nlinarith

/-- Side charge uses actual totals, not the held values. -/
theorem side_charge {δ b x y : ℝ} (hδ : 0 ≤ δ) (hy : 0 ≤ y)
    (hcmp : compared δ b x) : x+y ≤ (1+δ)*(b+y) := by
  rcases hcmp with ⟨hx,_⟩
  nlinarith

end
end UniformKServer.AllocationSchedule

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AlphaEmpty
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Empty active domains are genuine zero states, not a hidden nonempty
 hypothesis. They occur only at wholesale changes in the derived schedule;
 the algebra here incurs no restart allowance. -/
noncomputable section
namespace UniformKServer.AlphaEmpty
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem input_bound {p : Config ι} (hp : valid p) (B B' a : ι → ℝ)
    (ha : state p a) :
    |potential p B a-potential p B' a| ≤ 15*scale p*(∑ i, |B i-B' i|) := by
  cases p with
  | none => simp [potential,scale]
  | some p => exact AdaptiveAlpha.input_bound hp B B' a ha

theorem update {p : Config ι} (hp : valid p) (B a₀ : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hs : DomainTransport.Supported (active p) B)
    (ha₀ : state p a₀) :
    ∃ a, state p a ∧ (∀ i, (∑ j, B j)*a i ≤ (1+eta p i)*B i) ∧
      (∑ j, B j)*SimplexTracker.movement a a₀ ≤ potential p B a₀-potential p B a := by
  cases p with
  | none =>
    have he := zero_supported hs
    refine ⟨fun _ => 0,rfl,?_,?_⟩
    · intro i; simp [eta,he]
    · simp [he,potential]
  | some p => exact AdaptiveAlpha.update hp B a₀ hB hs ha₀

/-- Two actual minimizing updates whenever both domains are nonempty.
 At an empty endpoint, actual zero input supplies the same ledger. -/
theorem step {p q : Config ι} (hp : valid p) (hq : valid q)
    (Bstar Bnew a₀ : ι → ℝ) (hB : ∀ i, 0 ≤ Bstar i) (hBn : ∀ i, 0 ≤ Bnew i)
    (hST : (∑ i, Bstar i) ≤ ∑ i, Bnew i)
    (hpB : DomainTransport.Supported (active p) Bstar)
    (hqB : DomainTransport.Supported (active q) Bstar)
    (hqN : DomainTransport.Supported (active q) Bnew)
    (ha₀ : state p a₀) :
    ∃ a b, state q a ∧ state q b ∧
      (∀ i, (∑ j, Bnew j)*a i ≤ (1+eta q i)*Bnew i) ∧
      (∀ i, (∑ j, Bstar j)*b i ≤ (1+eta p i)*Bstar i) ∧
      (∑ j, Bnew j)*SimplexTracker.movement a a₀ ≤
        potential p Bstar a₀-potential q Bnew a+
        (potential q Bstar b-potential p Bstar b)+
        15*scale q*(∑ i, |Bnew i-Bstar i|)+4*((∑ i, Bnew i)-(∑ i, Bstar i)) := by
  cases p with
  | none =>
    have hzero := zero_supported hpB
    have haold : a₀=fun _ => 0 := ha₀
    obtain ⟨b,hb⟩ := exists_state hq
    obtain ⟨a,ha,hf,_⟩ := update hq Bnew b hBn hqN hb
    refine ⟨a,b,ha,hb,hf,?_,?_⟩
    · intro i; simp [hzero]
    · have hi := input_bound hq Bnew (fun _ => 0) a ha
      rw [potential_zero,sub_zero] at hi
      have hsum : (∑ i, |Bnew i|)=∑ i, Bnew i := sum_congr rfl fun i _ => abs_of_nonneg (hBn i)
      simp only [sub_zero] at hi
      rw [hsum] at hi
      have hm : SimplexTracker.movement a a₀ ≤ 1 := by
        rw [haold]
        cases q with
        | none => rw [ha]; simp [SimplexTracker.movement]
        | some q =>
          change DomainTransport.simplex q.active a at ha
          simp only [SimplexTracker.movement,sub_zero,abs_of_nonneg (ha.1 _),ha.2.2]
          exact le_rfl
      have hT : 0 ≤ ∑ i, Bnew i := sum_nonneg fun i _ => hBn i
      have hmul := mul_le_mul_of_nonneg_left hm hT
      rw [hzero,potential_zero,potential_zero,potential_zero]
      change (∑ j, Bnew j)*SimplexTracker.movement a a₀ ≤
        0-potential q Bnew a+(0-0)+
        15*scale q*(∑ i, |Bnew i-0|)+4*((∑ i, Bnew i)-(∑ _i : ι, (0:ℝ)))
      simp only [sub_zero,sub_self,add_zero,sum_const_zero]
      rw [hsum]
      linarith [le_abs_self (potential q Bnew a)]
  | some p =>
    cases q with
    | none =>
      have hz := zero_supported hqB
      have hn := zero_supported hqN
      refine ⟨fun _ => 0,fun _ => 0,rfl,rfl,?_,?_,?_⟩
      · intro i; simp [hn,eta]
      · intro i; simp [hz]
      · simp [hz,hn,potential,scale,AdaptiveAlpha.potential_zero]
    | some q => exact AdaptiveAlpha.step hp hq Bstar Bnew a₀ hB hBn hST hpB hqB hqN ha₀

end UniformKServer.AlphaEmpty

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AlphaEmptyLinear
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! The true affine potential extended to empty domains. -/
noncomputable section
namespace UniformKServer.AlphaEmptyLinear
open Finset UniformKServer.AlphaEmpty
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem bound {p : Config ι} (hp : valid p) (a : ι → ℝ)
    (ha : state p a) (i : ι) : |coefficient p a i| ≤ 15*scale p := by
  cases p with
  | none => simp [coefficient,scale]
  | some p => exact AdaptiveAlphaLinear.bound hp a ha i

end UniformKServer.AlphaEmptyLinear

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AlphaRecurrence
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! A single deterministic selection of the two proven minimizations. This
 supplies causal states, rather than postulating a trajectory satisfying the
 desired movement bound. The fallback branch is never used on valid input. -/
noncomputable section
namespace UniformKServer.AlphaRecurrence
open Finset UniformKServer.AlphaEmpty
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem initial_spec {p : Config ι} (hp : valid p) : state p (initial p) := by
  unfold initial
  rw [dite_eq_left (exists_state hp)]
  exact (exists_state hp).choose_spec

theorem chooseStep_spec {p q : Config ι} (hp : valid p) (hq : valid q)
    (Bstar Bnew old : ι → ℝ) (hB : ∀ i, 0 ≤ Bstar i) (hBn : ∀ i, 0 ≤ Bnew i)
    (hST : (∑ i, Bstar i) ≤ ∑ i, Bnew i)
    (hpB : DomainTransport.Supported (active p) Bstar)
    (hqB : DomainTransport.Supported (active q) Bstar)
    (hqN : DomainTransport.Supported (active q) Bnew) (hold : state p old) :
    StepSpec p q Bstar Bnew old (chooseStep p q Bstar Bnew old).1
      (chooseStep p q Bstar Bnew old).2 := by
  have hex : ∃ ab : (ι → ℝ) × (ι → ℝ), StepSpec p q Bstar Bnew old ab.1 ab.2 := by
    obtain ⟨a,b,h⟩ := AlphaEmpty.step hp hq Bstar Bnew old hB hBn hST hpB hqB hqN hold
    exact ⟨(a,b),h⟩
  unfold chooseStep
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem trajectory_state {p : ℕ → Config ι} {Bstar B : ℕ → ι → ℝ}
    (h : InputValid p Bstar B) : ∀ t, state (p t) (trajectory p Bstar B t) := by
  intro t
  induction t with
  | zero => exact initial_spec (h.1 0)
  | succ t ih => exact (chooseStep_spec (h.1 t) (h.1 (t+1)) _ _ _ (h.2.1 t)
      (h.2.2.1 (t+1)) (h.2.2.2.1 t) (h.2.2.2.2.1 t) (h.2.2.2.2.2.1 t)
      (h.2.2.2.2.2.2 (t+1)) ih).1

theorem trajectory_step {p : ℕ → Config ι} {Bstar B : ℕ → ι → ℝ}
    (h : InputValid p Bstar B) (t : ℕ) :
    StepSpec (p t) (p (t+1)) (Bstar t) (B (t+1)) (trajectory p Bstar B t)
      (trajectory p Bstar B (t+1)) (prepared p Bstar B t) :=
  chooseStep_spec (h.1 t) (h.1 (t+1)) _ _ _ (h.2.1 t)
    (h.2.2.1 (t+1)) (h.2.2.2.1 t) (h.2.2.2.2.1 t) (h.2.2.2.2.2.1 t)
    (h.2.2.2.2.2.2 (t+1)) (trajectory_state h t)

end UniformKServer.AlphaRecurrence

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochGeometry
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Actual held vector epochs and persistent dominant identity of companion §03.
 The scalar cumulative-credit budget is linked by an exact projection. -/
noncomputable section
namespace UniformKServer.EpochGeometry
open Finset
variable {ι : Type*} [Fintype ι]

def initial (a : ι → ℝ) : State ι := ⟨a,0⟩
def scalar (s : State ι) : AllocationEpoch.State := ⟨total s.base,s.credit⟩

def update (s : State ι) (a b : ι → ℝ) (parent : Bool) : State ι := by
  classical
  exact if AllocationEpoch.fires (scalar s) (variation a b) parent then initial b
    else ⟨s.base,s.credit+variation a b⟩

theorem variation_nonneg (a b : ι → ℝ) : 0 ≤ variation a b := sum_nonneg fun i _ => abs_nonneg (b i-a i)
theorem variation_self (a : ι → ℝ) : variation a a=0 := by simp [variation]
theorem variation_triangle (a b c : ι → ℝ) : variation a c ≤ variation a b+variation b c := by
  unfold variation
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro i _
  calc
    |c i-a i| = |(b i-a i)+(c i-b i)| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _

theorem initial_valid {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) : valid a (initial a) := by
  refine ⟨ha,le_rfl,?_,?_⟩
  · exact div_nonneg (total_nonneg ha) (by norm_num)
  · simp [initial,variation_self]

theorem update_valid {a b : ι → ℝ} {s : State ι} (hs : valid a s)
    (hb : ∀ i, 0 ≤ b i) (parent : Bool) : valid b (update s a b parent) := by
  unfold update
  split
  · exact initial_valid hb
  · rename_i h
    have hh : s.credit+variation a b ≤ total s.base/100 :=
      le_of_not_gt (fun hh => h (Or.inr hh))
    exact ⟨hs.1,add_nonneg hs.2.1 (variation_nonneg a b),hh,
      (variation_triangle s.base a b).trans (by linarith [hs.2.2.2])⟩

theorem scalar_update (s : State ι) (a b : ι → ℝ) (parent : Bool) :
    scalar (update s a b parent) = AllocationEpoch.update (scalar s) (total b) (variation a b) parent := by
  classical
  unfold update AllocationEpoch.update
  split <;> rfl

def schedule (a : ℕ → ι → ℝ) (parent : ℕ → Bool) : ℕ → State ι
  | 0 => initial (a 0)
  | t+1 => update (schedule a parent t) (a t) (a (t+1)) (parent t)

theorem schedule_valid {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i) (parent : ℕ → Bool) :
    ∀ t, valid (a t) (schedule a parent t) := by
  intro t
  induction t with
  | zero => exact initial_valid (ha 0)
  | succ t ih => exact update_valid ih (ha (t+1)) (parent t)

theorem scalar_schedule (a : ℕ → ι → ℝ) (parent : ℕ → Bool) : ∀ t,
    scalar (schedule a parent t) = AllocationEpoch.schedule (fun t => total (a t))
      (fun t => variation (a t) (a (t+1))) parent t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [schedule,scalar_update,AllocationEpoch.schedule,ih]

theorem wholesale_budget {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (parent : ℕ → Bool) (H : ℕ) :
    (∑ t ∈ range H, AllocationEpoch.charge (scalar (schedule a parent t))
      (total (a t)) (total (a (t+1))) (variation (a t) (a (t+1))) (parent t)) ≤
      203*(∑ t ∈ range H, variation (a t) (a (t+1)))+
        ∑ t ∈ range H, (if parent t then total (a t)+total (a (t+1)) else 0) := by
  simp_rw [scalar_schedule]
  exact AllocationEpoch.schedule_budget (fun t => total_nonneg (ha t))
    (fun t => total_difference (a t) (a (t+1))) parent H

theorem side_difference (a b : ι → ℝ) (o : ι) : |side o b-side o a| ≤ variation a b := by
  classical
  unfold side variation
  rw [←sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  apply sum_le_sum
  intro i _
  by_cases h : i=o
  · simp [h]
  · simp [h]

theorem dominant_size {s : State ι} {a : ι → ℝ} (hs : valid a s) {o : ι}
    (ho : dominant s=some o) : (84/100)*total s.base ≤ a o ∧
      side o a ≤ (16/100)*total s.base := by
  have hb := dominant_spec ho
  have hd := coordinate_difference s.base a o
  have hneg := neg_le_abs (a o-s.base o)
  have hsides := side_difference s.base a o
  have hside := le_abs_self (side o a-side o s.base)
  have htotal := total_with_side s.base o
  constructor <;> linarith [hs.2.2.1,hs.2.2.2]

end UniformKServer.EpochGeometry

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochParameters
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Parameters on the actual positive held-size domain of one vector epoch.
These are the geometric hypotheses of the logarithmic proportion minimizer. -/
noncomputable section
namespace UniformKServer.EpochParameters
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem active_sum {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    (∑ i : active a, a i) = EpochGeometry.total a := by
  classical
  rw [sum_coe_sort]
  unfold active EpochGeometry.total
  rw [sum_filter]
  apply sum_congr rfl
  intro i _
  split_ifs with h
  · rfl
  · exact le_antisymm (ha i) (not_lt.mp h)

theorem exp_height {A a : ℝ} (hA : 0 < A) (ha : 0 < a) :
    Real.exp (-SideParameters.height A a) = Real.exp (-1)*(a/A) := by
  unfold SideParameters.height
  rw [neg_add,Real.exp_add]
  rw [Real.exp_neg (Real.log (A/a)),Real.exp_log (div_pos hA ha)]
  congr 1
  field_simp

theorem exp_height_le {A a : ℝ} (hA : 0 < A) (ha : 0 < a) :
    Real.exp (-SideParameters.height A a) ≤ a/A := by
  rw [exp_height hA ha]
  exact mul_le_of_le_one_left (div_nonneg ha.le hA.le)
    (Real.exp_le_one_iff.mpr (by norm_num))

theorem active_total_pos {s : EpochGeometry.State ι} {a : ι → ℝ}
    (hs : EpochGeometry.valid a s) {i : ι} (ha : 0 < a i) :
    0 < EpochGeometry.total s.base := by
  have hd := EpochGeometry.coordinate_difference s.base a i
  have hb : s.base i ≤ EpochGeometry.total s.base :=
    single_le_sum (fun j _ => hs.1 j) (mem_univ i)
  have hp := le_abs_self (a i-s.base i)
  linarith [hs.2.2.1,hs.2.2.2]

theorem regular_exponential_sum {s : EpochGeometry.State ι} {a : ι → ℝ}
    (hs : EpochGeometry.valid a s) (ha : ∀ i, 0 ≤ a i)
    (hA : 0 < EpochGeometry.total s.base) :
    (∑ i : active a, Real.exp (-SideParameters.height (EpochGeometry.total s.base) (a i))) ≤ 2 := by
  calc
    _ ≤ ∑ i : active a, a i/EpochGeometry.total s.base :=
      sum_le_sum fun i _ => exp_height_le hA (mem_active.mp i.property)
    _ = EpochGeometry.total a/EpochGeometry.total s.base := by rw [←sum_div,active_sum ha]
    _ ≤ 2 := (div_le_iff₀ hA).mpr (by linarith [(EpochGeometry.total_comparison hs).2])

theorem side_coordinate {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) {o i : ι} (hi : i ≠ o) :
    a i ≤ EpochGeometry.side o a := by
  classical
  have h := single_le_sum (s:=univ) (f:=fun j => if j=o then 0 else a j)
    (fun j _ => by split_ifs <;> first | exact ha j | norm_num) (mem_univ i)
  simpa [EpochGeometry.side,hi] using h

def sideReference (a : ι → ℝ) (o : ι) (U : ℝ) : Prop :=
  0 ≤ U ∧ U/(1001/1000) ≤ EpochGeometry.side o a ∧
    EpochGeometry.side o a ≤ (1001/1000)*U

theorem marked_u_upper {s : EpochGeometry.State ι} {a : ι → ℝ} {o : ι} {U : ℝ}
    (hs : EpochGeometry.valid a s) (ho : EpochGeometry.dominant s=some o)
    (hU : sideReference a o U) : U/EpochGeometry.total s.base < 1/4 := by
  have hA := (EpochGeometry.dominant_spec ho).1
  have hd := (EpochGeometry.dominant_size hs ho).2
  have hU' := (div_le_iff₀ (by norm_num : (0:ℝ)<1001/1000)).mp hU.2.1
  apply (div_lt_iff₀ hA).mpr
  linarith

/-- The logarithmic side weight controls the approaching-simplex-vertex height.
The estimate keeps the factor independent of the number of inactive children. -/
theorem marked_height_lower {A ai U : ℝ} (hA : 0 < A) (hai : 0 < ai)
    (haiU : ai ≤ (1001/1000)*U) (hu : U/A ≤ 1) (hU : 0 < U) :
    (1/2)*(1+Real.log (1/(U/A))) ≤ SideParameters.height A ai := by
  have hua : 0 < U/A := div_pos hU hA
  have hlogu := Real.log_nonneg ((one_le_div hua).mpr hu)
  have hratio : A/((1001/1000)*U) ≤ A/ai :=
    div_le_div_of_nonneg_left hA.le hai haiU
  have hlog := Real.log_le_log (div_pos hA (by positivity : (0:ℝ)<(1001/1000)*U)) hratio
  rw [Real.log_div hA.ne' (by positivity : (1001/1000)*U ≠ (0:ℝ)),
    Real.log_mul (by norm_num : (1001/1000:ℝ) ≠ 0) hU.ne'] at hlog
  have he : Real.log (1/(U/A)) = Real.log A-Real.log U := by
    rw [one_div_div,Real.log_div hA.ne' hU.ne']
  rw [he] at hlogu ⊢
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1001/1000)
  unfold SideParameters.height
  linarith

theorem side_exp_sum {s : EpochGeometry.State ι} {a : ι → ℝ} {o : ι} {U : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hA : 0 < EpochGeometry.total s.base)
    (hU : sideReference a o U) :
    (∑ i : {i : active a // (i : ι) ≠ o},
      Real.exp (-SideParameters.height (EpochGeometry.total s.base) (a i.1))) ≤
        2*(U/EpochGeometry.total s.base) := by
  classical
  have hsum : (∑ i : {i : active a // (i : ι) ≠ o}, a i.1) = EpochGeometry.side o a := by
    rw [←Finset.sum_subtype (univ.filter fun i : active a => (i:ι) ≠ o)
      (by simp) (fun i => a i),sum_filter]
    rw [sum_coe_sort (active a) (fun i : ι => if i ≠ o then a i else 0)]
    unfold active EpochGeometry.side
    rw [sum_filter]
    apply sum_congr rfl
    intro i _
    by_cases hi : i=o
    · simp [hi]
    · by_cases hp : 0 < a i
      · simp [hi,hp]
      · have hz : a i=0 := le_antisymm (not_lt.mp hp) (ha i)
        simp [hz,hi]
  calc
    _ ≤ ∑ i : {i : active a // (i : ι) ≠ o}, a i.1/EpochGeometry.total s.base :=
      sum_le_sum fun i _ => exp_height_le hA (mem_active.mp i.1.property)
    _ = EpochGeometry.side o a/EpochGeometry.total s.base := by rw [←sum_div,hsum]
    _ ≤ 2*(U/EpochGeometry.total s.base) := by
      apply (div_le_iff₀ hA).mpr
      have he : 2*(U/EpochGeometry.total s.base)*EpochGeometry.total s.base=2*U := by field_simp
      rw [he]
      linarith [hU.2.2,hU.1]

end UniformKServer.EpochParameters

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochAlpha
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Source logarithmic configurations are built on the actual active-size
 domain, including the automatic one-point domain. -/
noncomputable section
namespace UniformKServer.EpochAlpha
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem height_upper {A ai : ℝ} {k : ℕ} (hA : 0 < A)
    (hAk : A ≤ 2*k) (hai : (9/100000:ℝ) ≤ ai) :
    SideParameters.height A ai ≤ 50000*ell k := by
  have hkp : (0:ℝ) < k+1 := by positivity
  have hip : 0 < ai := by linarith
  have hrat : A/ai ≤ 40000*(k+1) := by
    apply (div_le_iff₀ hip).mpr
    have hkn : (0:ℝ) ≤ k := by positivity
    have hmul := mul_le_mul_of_nonneg_left hai (show 0 ≤ 40000*((k:ℝ)+1) by positivity)
    nlinarith
  have hlog := Real.log_le_log (div_pos hA hip) hrat
  rw [Real.log_mul (by norm_num : (40000:ℝ) ≠ 0) hkp.ne'] at hlog
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<40000)
  have hl := Real.log_nonneg (show (1:ℝ) ≤ k+1 by linarith [Nat.cast_nonneg (α:=ℝ) k])
  unfold SideParameters.height ell
  linarith

/-- Exact h on all regular coordinates; no clamped-log discrepancy occurs
 because the epoch geometry proves ai < A. -/
def regular (a : ι → ℝ) (A ell ct C : ℝ) : AdaptiveAlpha.Config ι where
  active := EpochParameters.active a
  param := ⟨.regular,fun i => SideParameters.height A (a i),ell,ct,C⟩

def marked (a : ι → ℝ) (A U ell ct C : ℝ) (o : EpochParameters.active a) :
    AdaptiveAlpha.Config ι := by
  exact ⟨EpochParameters.active a,
    ⟨.marked o (U/A),fun i => if i=o then U/A else SideParameters.height A (a i),ell,ct,C⟩⟩

def singleton (a : ι → ℝ) (ell ct C : ℝ) (o : EpochParameters.active a) :
    AdaptiveAlpha.Config ι where
  active := EpochParameters.active a
  param := ⟨.singleton o,fun _ => 0,ell,ct,C⟩

theorem regular_valid {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) (ha : ∀ i, 0 ≤ a i)
    (hne : (EpochParameters.active a).Nonempty) (ho : EpochGeometry.dominant s=none)
    {ell ct C : ℝ} (hl : 0 < ell) (hc : 0 < ct) (hct : ct*50000 ≤ 1)
    (hC : 1000 < C*ct)
    (hheight : ∀ i : EpochParameters.active a,
      SideParameters.height (EpochGeometry.total s.base) (a i) ≤ 50000*ell) :
    AdaptiveAlpha.valid (regular a (EpochGeometry.total s.base) ell ct C) := by
  have hA : 0 < EpochGeometry.total s.base := by
    obtain ⟨i,hi⟩ := hne
    exact EpochParameters.active_total_pos hs (EpochParameters.mem_active.mp hi)
  refine ⟨hne,hl,hc,hC,?_,?_,?_⟩
  · intro i
    exact eta_bound hc hl hct (hheight i)
  · intro i
    exact EpochParameters.regular_height hs (EpochParameters.mem_active.mp i.property) (by simp [ho])
  · exact EpochParameters.regular_exponential_sum hs ha hA

theorem marked_valid {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) (ha : ∀ i, 0 ≤ a i)
    (o : EpochParameters.active a) (ho : EpochGeometry.dominant s=some o.val)
    {U ell ct C : ℝ} (hU : EpochParameters.sideReference a o U) (hUp : 0 < U)
    (hl : 1 ≤ ell) (hc : 0 < ct) (hct : ct*50000 ≤ 1) (hC : 1000 < C*ct)
    (hheight : ∀ i : EpochParameters.active a,
      SideParameters.height (EpochGeometry.total s.base) (a i) ≤ 50000*ell) :
    AdaptiveAlpha.valid (marked a (EpochGeometry.total s.base) U ell ct C o) := by
  have hA := (EpochGeometry.dominant_spec ho).1
  have hu := EpochParameters.marked_u_upper hs ho hU
  have hu' : U/EpochGeometry.total s.base ≤ 1 := by linarith
  have hlp : 0 < ell := by linarith
  refine ⟨⟨o,o.property⟩,hlp,hc,hC,?_,div_pos hUp hA,hu',?_,?_,?_,?_⟩
  · intro i
    apply eta_bound hc hlp hct
    unfold marked
    dsimp only
    split_ifs
    · linarith
    · exact hheight i
  · simp [marked]
  · intro i hi
    have hio : (i:ι) ≠ o.val := fun h => hi (Subtype.ext h)
    have hh := EpochParameters.regular_height hs (EpochParameters.mem_active.mp i.property)
      (by simpa only [ho,ne_eq,Option.some.injEq] using hio.symm)
    unfold marked
    dsimp only
    split_ifs with he
    · exact False.elim (hi he)
    · exact hh
  · intro i hi
    have hio : (i:ι) ≠ o.val := fun h => hi (Subtype.ext h)
    have haiU := (EpochParameters.side_coordinate ha hio).trans hU.2.2
    have hh := EpochParameters.marked_height_lower hA (EpochParameters.mem_active.mp i.property)
      haiU hu' hUp
    unfold marked
    dsimp only
    split_ifs with he
    · exact False.elim (hi he)
    · exact hh
  · let : DecidableEq (EpochParameters.active a) := fun i j => Classical.propDecidable (i=j)
    have hsum := EpochParameters.side_exp_sum ha hA hU
    have he : (∑ i ∈ univ.erase o,
        Real.exp (- (if i=o then U/EpochGeometry.total s.base else
          SideParameters.height (EpochGeometry.total s.base) (a i)))) =
        ∑ i : {i : EpochParameters.active a // (i : ι) ≠ o.val},
          Real.exp (-SideParameters.height (EpochGeometry.total s.base) (a i.1)) := by
      have hmem (i : EpochParameters.active a) : i ∈ univ.erase o ↔ (i:ι) ≠ o.val := by
        simp only [mem_erase,mem_univ,and_true]
        exact not_congr Subtype.ext_iff
      rw [←Finset.sum_subtype (univ.erase o) hmem (fun i : EpochParameters.active a =>
          Real.exp (-SideParameters.height (EpochGeometry.total s.base) (a i)))]
      apply sum_congr rfl
      intro i hi
      rw [ite_eq_right (mem_erase.mp hi).1]
    apply le_trans (le_of_eq ?_) (he.le.trans hsum)
    apply sum_congr rfl
    intro i _
    unfold marked
    dsimp only
    split_ifs <;> rfl

theorem singleton_valid {a : ι → ℝ} (o : EpochParameters.active a)
    (ha : ∀ i : EpochParameters.active a, i=o) {ell ct C : ℝ}
    (hl : 0 < ell) (hc : 0 < ct) (hC : 1000 < C*ct) :
    AdaptiveAlpha.valid (singleton a ell ct C o) := by
  refine ⟨⟨o,o.property⟩,hl,hc,hC,?_,ha,fun _ => rfl⟩
  intro i
  change ct*0/ell ≤ 1
  norm_num

theorem side_zero_singleton {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (o : EpochParameters.active a) {U : ℝ} (hU : EpochParameters.sideReference a o U)
    (hzero : U=0) : ∀ i : EpochParameters.active a, i=o := by
  intro i
  by_contra hi
  have hio : (i:ι) ≠ o.val := fun h => hi (Subtype.ext h)
  have hside := EpochParameters.side_coordinate ha hio
  have hsize := EpochParameters.mem_active.mp i.property
  have hupp := hU.2.2
  rw [hzero,mul_zero] at hupp
  linarith

end UniformKServer.EpochAlpha

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeldRelative
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Held scalar references with forced epoch resets. The potential is not
 restarted: its nonnegative value is discarded on a wholesale step, while
 the full new installation is charged to that step. -/
noncomputable section
namespace UniformKServer.HeldRelative
open Finset AllocationSchedule

def update (δ b x : ℝ) (reset : Bool) : ℝ :=
  if reset then x else relativeUpdate δ b x

def schedule (δ : ℝ) (x : ℕ → ℝ) (reset : ℕ → Bool) : ℕ → ℝ
  | 0 => x 0
  | t+1 => update δ (schedule δ x reset t) (x (t+1)) (reset t)

theorem update_nonneg {δ b x : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) (r : Bool) :
    0 ≤ update δ b x r := by
  cases r
  · exact relative_nonneg hb hx
  · exact hx

theorem update_compared {δ b x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) (r : Bool) :
    compared δ (update δ b x r) x := by
  cases r
  · exact relative_compared hδ hx
  · change compared δ x x
    constructor <;> nlinarith

theorem schedule_nonneg {δ : ℝ} {x : ℕ → ℝ} (hx : ∀ t, 0 ≤ x t)
    (reset : ℕ → Bool) : ∀ t, 0 ≤ schedule δ x reset t := by
  intro t
  induction t with
  | zero => exact hx 0
  | succ t ih => exact update_nonneg ih (hx (t+1)) (reset t)

theorem schedule_compared {δ : ℝ} {x : ℕ → ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ t, 0 ≤ x t) (reset : ℕ → Bool) :
    ∀ t, compared δ (schedule δ x reset t) (x t) := by
  intro t
  cases t with
  | zero =>
    change compared δ (x 0) (x 0)
    constructor <;> nlinarith [hx 0]
  | succ t => exact update_compared hδ (hx (t+1)) (reset t)

theorem step {δ K b x y : ℝ} (hδ : 0 < δ) (hK : 1+2/δ ≤ K)
    (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) (hcmp : compared δ b x) (r : Bool) :
    charge b (update δ b y r)+K*|y-update δ b y r| ≤
      K*|x-b|+(if r then (1+δ)*(x+y) else K*|y-x|) := by
  have hKpos : 0 ≤ K := by
    have := div_pos (by norm_num : (0:ℝ)<2) hδ
    linarith
  cases r
  · exact relative_step hδ hK hb hy
  · simp only [update, ite_true, if_true, sub_self, abs_zero, mul_zero, add_zero]
    have hch := charge_le hb hy
    have hp := mul_nonneg hKpos (abs_nonneg (x-b))
    have hdy := mul_nonneg hδ.le hy
    have hdx := mul_nonneg hδ.le hx
    have hc := hcmp.2
    nlinarith

theorem budget {δ K : ℝ} {x : ℕ → ℝ} (hδ : 0 < δ) (hK : 1+2/δ ≤ K)
    (hx : ∀ t, 0 ≤ x t) (reset : ℕ → Bool) (H : ℕ) :
    (∑ t ∈ range H, charge (schedule δ x reset t) (schedule δ x reset (t+1))) ≤
      ∑ t ∈ range H, expenditure δ K x reset t := by
  have hKpos : 0 ≤ K := by
    have := div_pos (by norm_num : (0:ℝ)<2) hδ
    linarith
  have hsum : ∀ H,
      (∑ t ∈ range H, charge (schedule δ x reset t) (schedule δ x reset (t+1)))+
        K*|x H-schedule δ x reset H| ≤
      ∑ t ∈ range H, expenditure δ K x reset t := by
    intro H
    induction H with
    | zero => simp [schedule]
    | succ H ih =>
      rw [sum_range_succ, sum_range_succ]
      have ht := step hδ hK (schedule_nonneg hx reset H) (hx H) (hx (H+1))
        (schedule_compared hδ.le hx reset H) (reset H)
      change charge (schedule δ x reset H) (schedule δ x reset (H+1))+
        K*|x (H+1)-schedule δ x reset (H+1)| ≤
        K*|x H-schedule δ x reset H|+expenditure δ K x reset H at ht
      linarith
  have hp := mul_nonneg hKpos (abs_nonneg (x H-schedule δ x reset H))
  linarith [hsum H]

/-- The source charges true side sizes, rather than the held reference.
 On an unforced refresh those true sizes are controlled by the paid charge. -/
theorem true_charge {δ b x y : ℝ} (hδ : 0 ≤ δ) (hy : 0 ≤ y)
    (hcmp : compared δ b x) (hne : b ≠ relativeUpdate δ b y) :
    x+y ≤ (1+δ)*charge b (relativeUpdate δ b y) := by
  have he : relativeUpdate δ b y=y := by
    unfold relativeUpdate at *
    split_ifs at * <;> simp_all
  rw [he, charge, ite_eq_right (he ▸ hne)]
  exact side_charge hδ hy hcmp

end UniformKServer.HeldRelative

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SideReferenceSchedule
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                            
section

/-! Actual persistent U schedule, including changes of dominant identity.
 It has no per-epoch additive charge, and its non-wholesale changes are paid
 by held-size variation plus the existing wholesale ledger. -/
noncomputable section
namespace UniformKServer.SideReferenceSchedule
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

def reset (a : ℕ → ι → ℝ) (p : ℕ → Bool) (t : ℕ) : Bool :=
  decide (AllocationEpoch.fires (EpochGeometry.scalar (EpochGeometry.schedule a p t))
    (EpochGeometry.variation (a t) (a (t+1))) (p t))

def side (a : ℕ → ι → ℝ) (p : ℕ → Bool) (t : ℕ) : ℝ :=
  match EpochGeometry.dominant (EpochGeometry.schedule a p t) with
  | none => 0
  | some o => EpochGeometry.side o (a t)

def reference (a : ℕ → ι → ℝ) (p : ℕ → Bool) : ℕ → ℝ :=
  HeldRelative.schedule (1/1000) (side a p) (reset a p)

def wholesale (a : ℕ → ι → ℝ) (p : ℕ → Bool) (t : ℕ) : ℝ :=
  if reset a p t then EpochGeometry.total (a t)+EpochGeometry.total (a (t+1)) else 0

def charge (a : ℕ → ι → ℝ) (p : ℕ → Bool) (t : ℕ) : ℝ :=
  if reset a p t then 0 else
    if reference a p t = reference a p (t+1) then 0 else side a p t+side a p (t+1)

theorem side_nonneg {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i) (p : ℕ → Bool) (t : ℕ) :
    0 ≤ side a p t := by
  unfold side
  split
  · exact le_rfl
  · exact EpochParameters.side_nonneg (ha t) _

theorem side_le_total {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (t : ℕ) : side a p t ≤ EpochGeometry.total (a t) := by
  unfold side
  split
  · exact EpochGeometry.total_nonneg (ha t)
  · rename_i o _
    rw [EpochGeometry.total_with_side (a t) o]
    linarith [ha t o]

theorem not_reset_dominant {a : ℕ → ι → ℝ} {p : ℕ → Bool} {t : ℕ}
    (h : reset a p t = false) :
    EpochGeometry.dominant (EpochGeometry.schedule a p (t+1))=
      EpochGeometry.dominant (EpochGeometry.schedule a p t) := by
  have hf : ¬ AllocationEpoch.fires (EpochGeometry.scalar (EpochGeometry.schedule a p t))
      (EpochGeometry.variation (a t) (a (t+1))) (p t) := by
    simpa only [reset,decide_eq_false_iff_not] using h
  rw [EpochGeometry.schedule,EpochGeometry.update,ite_eq_right hf]
  rfl

theorem side_difference {a : ℕ → ι → ℝ} {p : ℕ → Bool} {t : ℕ}
    (h : reset a p t=false) :
    |side a p (t+1)-side a p t| ≤ EpochGeometry.variation (a t) (a (t+1)) := by
  unfold side
  rw [not_reset_dominant h]
  split
  · simp only [sub_self,abs_zero]
    exact EpochGeometry.variation_nonneg _ _
  · exact EpochGeometry.side_difference _ _ _

theorem reference_nonneg {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (t : ℕ) : 0 ≤ reference a p t :=
  HeldRelative.schedule_nonneg (side_nonneg ha p) (reset a p) t

theorem reference_compared {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (t : ℕ) :
    AllocationSchedule.compared (1/1000) (reference a p t) (side a p t) :=
  HeldRelative.schedule_compared (by norm_num) (side_nonneg ha p) (reset a p) t

theorem reference_spec {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (t : ℕ) {o : ι}
    (ho : EpochGeometry.dominant (EpochGeometry.schedule a p t)=some o) :
    EpochParameters.sideReference (a t) o (reference a p t) := by
  have hc := reference_compared ha p t
  simp only [AllocationSchedule.compared,side,ho] at hc
  refine ⟨reference_nonneg ha p t,?_,?_⟩
  · apply (div_le_iff₀ (by norm_num : (0:ℝ)<1001/1000)).mpr
    linarith [hc.2]
  · linarith [hc.1]

theorem wholesale_budget {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (H : ℕ) :
    (∑ t ∈ range H, wholesale a p t) ≤
      203*(∑ t ∈ range H, EpochGeometry.variation (a t) (a (t+1)))+
      ∑ t ∈ range H, (if p t then EpochGeometry.total (a t)+EpochGeometry.total (a (t+1)) else 0) := by
  simpa only [wholesale,reset,decide_eq_true_eq,AllocationEpoch.charge] using
    EpochGeometry.wholesale_budget ha p H

theorem charge_bound {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (t : ℕ) :
    charge a p t ≤ (1001/1000)*AllocationSchedule.charge (reference a p t) (reference a p (t+1)) := by
  have hn0 := reference_nonneg ha p t
  have hn1 := reference_nonneg ha p (t+1)
  have hc := reference_compared ha p t
  unfold charge
  split_ifs with hr he
  · exact mul_nonneg (by norm_num) (by
      unfold AllocationSchedule.charge
      split_ifs
      · exact le_rfl
      · exact add_nonneg hn0 hn1)
  · rw [←he,AllocationSchedule.charge_self,mul_zero]
  · have hr' : reset a p t=false := Bool.eq_false_iff.mpr hr
    have hu : reference a p (t+1)=AllocationSchedule.relativeUpdate (1/1000)
        (reference a p t) (side a p (t+1)) := by
      simp only [reference,HeldRelative.schedule,HeldRelative.update,hr',Bool.false_eq_true,ite_false, if_false]
    rw [hu] at he ⊢
    convert HeldRelative.true_charge (by norm_num : (0:ℝ)≤1/1000)
      (side_nonneg ha p (t+1)) hc he using 1
    all_goals try with_reducible_and_instances rfl
    norm_num

theorem expenditure_bound {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (t : ℕ) :
    HeldRelative.expenditure (1/1000) 2001 (side a p) (reset a p) t ≤
      2001*EpochGeometry.variation (a t) (a (t+1))+(1001/1000)*wholesale a p t := by
  unfold HeldRelative.expenditure wholesale
  split_ifs with hr
  · have h0 := side_le_total ha p t
    have h1 := side_le_total ha p (t+1)
    have hd := EpochGeometry.variation_nonneg (a t) (a (t+1))
    nlinarith
  · have hh := side_difference (Bool.eq_false_iff.mpr hr)
    nlinarith

theorem budget {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (H : ℕ) :
    (∑ t ∈ range H, charge a p t) ≤
      2004*(∑ t ∈ range H, EpochGeometry.variation (a t) (a (t+1)))+
      2*(∑ t ∈ range H, wholesale a p t) := by
  have hc := sum_le_sum (s:=range H) (fun t _ => charge_bound ha p t)
  have hb := HeldRelative.budget (δ:=1/1000) (K:=2001) (by norm_num) (by norm_num)
    (side_nonneg ha p) (reset a p) H
  have he := sum_le_sum (s:=range H) (fun t _ => expenditure_bound ha p t)
  rw [←mul_sum] at hc
  rw [sum_add_distrib,←mul_sum,←mul_sum] at he
  change (∑ t ∈ range H, AllocationSchedule.charge (reference a p t) (reference a p (t+1))) ≤ _ at hb
  have hv : 0 ≤ ∑ t ∈ range H, EpochGeometry.variation (a t) (a (t+1)) :=
    sum_nonneg fun t _ => EpochGeometry.variation_nonneg _ _
  have hw : 0 ≤ ∑ t ∈ range H, wholesale a p t := by
    apply sum_nonneg
    intro t _
    unfold wholesale
    split_ifs
    · exact add_nonneg (EpochGeometry.total_nonneg (ha t)) (EpochGeometry.total_nonneg (ha (t+1)))
    · exact le_rfl
  nlinarith

end UniformKServer.SideReferenceSchedule

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochAlphaSchedule
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

/-! Actual total choice of the epoch proportions, including the empty branch.
 Validity is derived from the persistent epoch and forced side-reference
 recurrences; the inactive or zero-side cases are not excluded. -/
noncomputable section
namespace UniformKServer.EpochAlphaSchedule
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

def config (a : ι → ℝ) (s : EpochGeometry.State ι) (U ell ct C : ℝ) : AlphaEmpty.Config ι :=
  if (EpochParameters.active a).Nonempty then
    match EpochGeometry.dominant s with
    | none => some (EpochAlpha.regular a (EpochGeometry.total s.base) ell ct C)
    | some o => if ho : o ∈ EpochParameters.active a then
        if U=0 then some (EpochAlpha.singleton a ell ct C ⟨o,ho⟩)
        else some (EpochAlpha.marked a (EpochGeometry.total s.base) U ell ct C ⟨o,ho⟩)
      else none
  else none

theorem dominant_active {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) {o : ι} (ho : EpochGeometry.dominant s=some o) :
    o ∈ EpochParameters.active a := by
  apply EpochParameters.mem_active.mpr
  have hp := (EpochGeometry.dominant_spec ho).1
  have hl := (EpochGeometry.dominant_size hs ho).1
  linarith

theorem active_eq {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) (U ell ct C : ℝ) :
    AlphaEmpty.active (config a s U ell ct C)=EpochParameters.active a := by
  unfold config
  split
  · rename_i hn
    cases ho : EpochGeometry.dominant s with
    | none => rfl
    | some o =>
      simp only [dite_eq_left (dominant_active hs ho)]
      split_ifs <;> rfl
  · rename_i hn
    exact (Finset.not_nonempty_iff_eq_empty.mp hn).symm

theorem valid_config {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) (ha : ∀ i, 0 ≤ a i)
    {U ell ct C : ℝ} (hl : 1 ≤ ell) (hc : 0 < ct) (hct : ct*50000 ≤ 1)
    (hC : 1000 < C*ct)
    (hheight : ∀ i : EpochParameters.active a,
      SideParameters.height (EpochGeometry.total s.base) (a i) ≤ 50000*ell)
    (hU : ∀ o, EpochGeometry.dominant s=some o → EpochParameters.sideReference a o U) :
    AlphaEmpty.valid (config a s U ell ct C) := by
  unfold config
  split
  · rename_i hn
    cases ho : EpochGeometry.dominant s with
    | none => exact EpochAlpha.regular_valid hs ha hn ho (by linarith) hc hct hC hheight
    | some o =>
      have hoa := dominant_active hs ho
      simp only [dite_eq_left hoa]
      split_ifs with hz
      · exact EpochAlpha.singleton_valid ⟨o,hoa⟩
          (EpochAlpha.side_zero_singleton ha ⟨o,hoa⟩ (hU o ho) hz) (by linarith) hc hC
      · exact EpochAlpha.marked_valid hs ha ⟨o,hoa⟩ ho (hU o ho)
          (lt_of_le_of_ne (hU o ho).1 (Ne.symm hz)) hl hc hct hC hheight
  · exact True.intro

theorem base_bound {a : ℕ → ι → ℝ} (p : ℕ → Bool) {K : ℝ}
    (ha : ∀ t, EpochGeometry.total (a t) ≤ K) : ∀ t,
    EpochGeometry.total (EpochGeometry.schedule a p t).base ≤ K := by
  intro t
  induction t with
  | zero => exact ha 0
  | succ t ih =>
    unfold EpochGeometry.schedule EpochGeometry.update
    split_ifs
    · exact ha (t+1)
    · exact ih

def schedule (a : ℕ → ι → ℝ) (p : ℕ → Bool) (k : ℕ) (ct C : ℝ) (t : ℕ) :
    AlphaEmpty.Config ι :=
  config (a t) (EpochGeometry.schedule a p t) (SideReferenceSchedule.reference a p t)
    (EpochAlpha.ell k) ct C

theorem schedule_valid {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (k : ℕ) {ct C : ℝ} (hc : 0 < ct) (hct : ct*50000 ≤ 1)
    (hC : 1000 < C*ct) (hsize : ∀ t, EpochGeometry.total (a t) ≤ 2*k)
    (hmin : ∀ t i, 0 < a t i → (9/100000:ℝ) ≤ a t i) (t : ℕ) :
    AlphaEmpty.valid (schedule a p k ct C t) := by
  have hv := EpochGeometry.schedule_valid ha p t
  apply valid_config hv (ha t) (EpochAlpha.ell_one k) hc hct hC
  · intro i
    have hai := EpochParameters.mem_active.mp i.property
    exact EpochAlpha.height_upper (EpochParameters.active_total_pos hv hai)
      (base_bound p hsize t) (hmin t i hai)
  · exact fun o ho => SideReferenceSchedule.reference_spec ha p t ho

theorem schedule_active {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (k : ℕ) (ct C : ℝ) (t : ℕ) :
    AlphaEmpty.active (schedule a p k ct C t)=EpochParameters.active (a t) :=
  active_eq (EpochGeometry.schedule_valid ha p t) _ _ _ _

end UniformKServer.EpochAlphaSchedule

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CausalSchedules
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Prefix extensionality of the concrete epoch recurrences. This supplies
filtration measurability without making future parameters available early. -/
noncomputable section
namespace UniformKServer.CausalSchedules
variable {ι : Type*} [Fintype ι]

theorem active_congr (c δ : ℝ) {x y : ℕ → ℝ} (t : ℕ)
    (h : ∀ s, s ≤ t → x s=y s) :
    AllocationSchedule.schedule c δ x t=AllocationSchedule.schedule c δ y t := by
  induction t with
  | zero => simp only [AllocationSchedule.schedule,h 0 le_rfl]
  | succ t ih =>
    simp only [AllocationSchedule.schedule,ih (fun s hs => h s (by omega)),h (t+1) le_rfl]

theorem held_congr (δ : ℝ) {x y : ℕ → ℝ} (t : ℕ)
    (h : ∀ s, s ≤ t → x s=y s) :
    AllocationSchedule.held δ x t=AllocationSchedule.held δ y t := by
  induction t with
  | zero => exact h 0 le_rfl
  | succ t ih =>
    simp only [AllocationSchedule.held,ih (fun s hs => h s (by omega)),h (t+1) le_rfl]

theorem forced_congr (δ : ℝ) {x y : ℕ → ℝ} {p q : ℕ → Bool} (t : ℕ)
    (h : ∀ s, s ≤ t → x s=y s) (hp : ∀ s, s < t → p s=q s) :
    HeldRelative.schedule δ x p t=HeldRelative.schedule δ y q t := by
  induction t with
  | zero => exact h 0 le_rfl
  | succ t ih =>
    simp only [HeldRelative.schedule,ih (fun s hs => h s (by omega))
      (fun s hs => hp s (by omega)),h (t+1) le_rfl,hp t (by omega)]

theorem epoch_congr {a b : ℕ → ι → ℝ} {p q : ℕ → Bool} (t : ℕ)
    (h : ∀ s, s ≤ t → a s=b s) (hp : ∀ s, s < t → p s=q s) :
    EpochGeometry.schedule a p t=EpochGeometry.schedule b q t := by
  induction t with
  | zero => simp only [EpochGeometry.schedule,h 0 le_rfl]
  | succ t ih =>
    simp only [EpochGeometry.schedule,ih (fun s hs => h s (by omega))
      (fun s hs => hp s (by omega)),h t (by omega),h (t+1) le_rfl,hp t (by omega)]

theorem side_congr {a b : ℕ → ι → ℝ} {p q : ℕ → Bool} (t : ℕ)
    (h : ∀ s, s ≤ t → a s=b s) (hp : ∀ s, s < t → p s=q s) :
    SideReferenceSchedule.side a p t=SideReferenceSchedule.side b q t := by
  simp only [SideReferenceSchedule.side,epoch_congr t h hp,h t le_rfl]

theorem reset_congr {a b : ℕ → ι → ℝ} {p q : ℕ → Bool} (t : ℕ)
    (h : ∀ s, s ≤ t+1 → a s=b s) (hp : ∀ s, s ≤ t → p s=q s) :
    SideReferenceSchedule.reset a p t=SideReferenceSchedule.reset b q t := by
  unfold SideReferenceSchedule.reset
  rw [epoch_congr t (fun s hs => h s (by omega))
    (fun s hs => hp s (by omega)),h t (by omega),h (t+1) le_rfl,hp t le_rfl]

theorem side_reference_congr {a b : ℕ → ι → ℝ} {p q : ℕ → Bool} (t : ℕ)
    (h : ∀ s, s ≤ t → a s=b s) (hp : ∀ s, s < t → p s=q s) :
    SideReferenceSchedule.reference a p t=SideReferenceSchedule.reference b q t := by
  apply forced_congr
  · intro s hs
    exact side_congr s (fun r hr => h r (by omega)) (fun r hr => hp r (by omega))
  · intro s hs
    exact reset_congr s (fun r hr => h r (by omega)) (fun r hr => hp r (by omega))

theorem alpha_congr {a b : ℕ → ι → ℝ} {p q : ℕ → Bool} (k : ℕ) (ct C : ℝ) (t : ℕ)
    (h : ∀ s, s ≤ t → a s=b s) (hp : ∀ s, s < t → p s=q s) :
    EpochAlphaSchedule.schedule a p k ct C t=EpochAlphaSchedule.schedule b q k ct C t := by
  simp only [EpochAlphaSchedule.schedule,h t le_rfl,epoch_congr t h hp,side_reference_congr t h hp]

end UniformKServer.CausalSchedules

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

theorem h_diff {p q : ℝ} (hpq : p ≤ q) : h p-h q ≤ q-p := by
  unfold h
  by_cases hp : p ≤ sstar
  · rw [max_eq_left (sub_nonneg.mpr hp)]
    have hq := le_max_left (sstar-q) 0
    linarith
  · rw [max_eq_right (by linarith : sstar-p ≤ 0)]
    have hq := le_max_right (sstar-q) 0
    linarith

theorem h_bound {p : ℝ} (hp : pstar ≤ p) : h p ≤ 7/12 := by
  unfold h pstar sstar at *
  apply max_le <;> linarith

theorem middle_drop {β p q : ℝ} (hβ : allowed β) (hp : pstar ≤ p) (hpq : p ≤ q) :
    middle β p-middle β q ≤ β*(q-p) := by
  have hc := coeff_bounds hβ
  have hx₀ := h_nonneg p
  have hy₀ := h_nonneg q
  have hx := h_bound hp
  have hxy := h_antitone hpq
  have hy := hxy.trans hx
  have hs : h p^2-h q^2 ≤ 2*(7/12)*(h p-h q) := by
    have := mul_le_mul_of_nonneg_left (show h p+h q ≤ 2*(7/12) by linarith)
      (sub_nonneg.mpr hxy)
    nlinarith
  have hp2 : h p^2 ≤ (7/12)^2 := by nlinarith
  have hq2 : h q^2 ≤ (7/12)^2 := by nlinarith
  have hpq2 : h p*h q ≤ (7/12)^2 := by nlinarith
  have ht : h p^3-h q^3 ≤ 3*(7/12)^2*(h p-h q) := by
    have := mul_le_mul_of_nonneg_left (show h p^2+h p*h q+h q^2 ≤ 3*(7/12)^2 by linarith)
      (sub_nonneg.mpr hxy)
    nlinarith
  calc
    middle β p-middle β q ≤ (2*A β*(7/12)+3*B β*(7/12)^2)*(h p-h q) := by
      have := mul_le_mul_of_nonneg_left hs (show 0 ≤ A β by linarith [hc.1])
      have := mul_le_mul_of_nonneg_left ht hc.2.1
      unfold middle
      nlinarith
    _ = β*(h p-h q) := by rw [hc.2.2.2.2]
    _ ≤ β*(q-p) := mul_le_mul_of_nonneg_left (h_diff hpq) (by linarith [hβ.1])

theorem h_convex : ConvexOn ℝ Set.univ h := by
  have hf : ConvexOn ℝ Set.univ (fun p : ℝ => sstar-p) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    nlinarith [congrArg (fun z : ℝ => sstar*z) hab]
  exact hf.sup (convexOn_const 0 convex_univ)

theorem middle_convex {β : ℝ} (hβ : allowed β) : ConvexOn ℝ Set.univ (middle β) := by
  have hc := coeff_bounds hβ
  have h2 := (h_convex.pow (fun x _ => h_nonneg x) 2).smul (show 0 ≤ A β by linarith [hc.1])
  have h3 := (h_convex.pow (fun x _ => h_nonneg x) 3).smul hc.2.1
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  exact (h2.add h3).2 hx hy ha hb hab

theorem rank_convex {β : ℝ} (hβ : allowed β) : ConvexOn ℝ Set.univ (rank β) := by
  let F : ℝ → ℝ := fun p => middle β p+β*p-1
  have hlin : ConvexOn ℝ Set.univ (fun p : ℝ => β*p-1) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    nlinarith
  have hF : ConvexOn ℝ (Set.Ici pstar) F := by
    have := (middle_convex hβ).add hlin
    refine ⟨convex_Ici _, ?_⟩
    intro x hx y hy a b ha hb hab
    simpa [F, Pi.add_apply, sub_eq_add_neg, add_assoc] using
      this.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  have hm : MonotoneOn F (Set.Ici pstar) := by
    intro p hp q hq hpq
    have := middle_drop hβ hp hpq
    dsimp [F] <;> linarith
  have he : (0 : ℝ) = F pstar := by
    dsimp [F]; rw [middle_match]; ring
  have hg := convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici
    (convexOn_const (0 : ℝ) (convex_Iic pstar)) hF (fun _ _ _ _ _ => le_refl _) hm he
  have hlin' : ConvexOn ℝ Set.univ (fun p : ℝ => 1-β*p) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    nlinarith
  have heq : rank β = (Set.Iic pstar).piecewise (fun _ => 0) F + (fun p => 1-β*p) := by
    ext p
    simp only [Pi.add_apply, Set.piecewise, Set.mem_Iic]
    by_cases hp : p ≤ pstar
    · simp [hp, rank]
    · simp only [ite_eq_right hp]
      rw [rank_middle (by linarith : pstar ≤ p)]
      dsimp [F] <;> ring
  rw [heq]
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  exact (hg.add hlin').2 hx hy ha hb hab

end UniformKServer.RankFunctions

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RankTracking
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

                                                                    
                                                                          
                                                                              
                                                                     
namespace UniformKServer.RankTracking

variable {Ω : Type*} [Fintype Ω]

def driftBudget (I : Input Ω) (H : ℕ) : ℝ :=
  ∑ t ∈ Finset.range H,
    average I.weight (fun ω => |I.posterior (t + 1) ω - I.filtered (t + 1) ω|)


theorem average_add (μ X Y : Ω → ℝ) :
    average μ (fun ω => X ω + Y ω) = average μ X + average μ Y := by
  simp [average, mul_add, Finset.sum_add_distrib]

theorem average_mono {μ X Y : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (h : ∀ ω, X ω ≤ Y ω) :
    average μ X ≤ average μ Y := by
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (hμ ω)

theorem credit_step (I : Input Ω) (r : ℕ → Ω → ℝ)
    (hrange : ∀ t ω, r t ω ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ t, measurableAt I.filtration t (r t))
    (hstep : ∀ t ω, r (t+1) ω = r t ω ∨ r (t+1) ω = I.posterior (t+1) ω)
    (t : ℕ) :
    average I.weight (fun ω => potential (I.posterior (t+1) ω) (r (t+1) ω)) +
      average I.weight (fun ω => (r (t+1) ω - r t ω)^2) ≤
    average I.weight (fun ω => potential (I.posterior t ω) (r t ω)) +
      average I.weight (fun ω => |I.posterior (t+1) ω - I.filtered (t+1) ω|) := by
  have hmart := I.filtering t (fun ω => 1 - 2*r t ω) (by
    intro ω ω' hω
    change 1 - 2*r t ω = 1 - 2*r t ω'
    rw [hmeas t ω ω' hω])
  rw [← average_add]
  calc
    _ = average I.weight (fun ω => potential (I.posterior t ω) (r t ω) +
        (1-2*r t ω)*(I.filtered (t+1) ω - I.posterior t ω) +
        (1-2*r t ω)*(I.posterior (t+1) ω - I.filtered (t+1) ω)) := by
          congr 1
          funext ω
          exact reset_identity _ _ _ _ _ (hstep t ω)
    _ ≤ average I.weight (fun ω => potential (I.posterior t ω) (r t ω) +
        (1-2*r t ω)*(I.filtered (t+1) ω - I.posterior t ω) +
        |I.posterior (t+1) ω - I.filtered (t+1) ω|) := by
          apply average_mono I.weight_nonneg
          intro ω
          gcongr
          exact drift_slope (hrange t ω)
    _ = _ := by rw [average_add, average_add, hmart, add_zero]

theorem reset_credit (I : Input Ω) (r : ℕ → Ω → ℝ)
    (hrange : ∀ t ω, r t ω ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ t, measurableAt I.filtration t (r t))
    (hstep : ∀ t ω, r (t+1) ω = r t ω ∨ r (t+1) ω = I.posterior (t+1) ω)
    (H : ℕ) :
    (∑ t ∈ Finset.range H, average I.weight (fun ω => (r (t+1) ω - r t ω)^2)) ≤
      driftBudget I H + 1 := by
  have telescope : ∀ H, (∑ t ∈ Finset.range H,
      average I.weight (fun ω => (r (t+1) ω - r t ω)^2)) +
      average I.weight (fun ω => potential (I.posterior H ω) (r H ω)) ≤
      driftBudget I H + average I.weight (fun ω => potential (I.posterior 0 ω) (r 0 ω)) := by
    intro H
    induction H with
    | zero => simp [driftBudget]
    | succ H ih =>
      have hs := credit_step I r hrange hmeas hstep H
      simp only [Finset.sum_range_succ, driftBudget] at *
      linarith
  have hlo : 0 ≤ average I.weight (fun ω => potential (I.posterior H ω) (r H ω)) := by
    exact Finset.sum_nonneg fun ω _ => mul_nonneg (I.weight_nonneg ω)
      (potential_range (I.posterior_range H ω) (hrange H ω)).1
  have hhi : average I.weight (fun ω => potential (I.posterior 0 ω) (r 0 ω)) ≤ 1 := by
    calc
      _ ≤ average I.weight (fun _ => 1) := average_mono I.weight_nonneg
        (fun ω => (potential_range (I.posterior_range 0 ω) (hrange 0 ω)).2)
      _ = 1 := by simp [average, I.weight_total]
  linarith [telescope H]


theorem reference_measurable (I : Input Ω) (f : ℝ → ℝ) (ξ : ℝ) :
    ∀ t, measurableAt I.filtration t (reference I f ξ t) := by
  intro t
  induction t with
  | zero => exact I.posterior_measurable 0
  | succ t ih =>
    intro ω ω' hω
    have hp := I.posterior_measurable (t+1) ω ω' hω
    have hr := ih ω ω' (I.refines t ω ω' hω)
    simp only [reference, hp, hr]

theorem reference_step (I : Input Ω) (f : ℝ → ℝ) (ξ : ℝ) (t : ℕ) (ω : Ω) :
    reference I f ξ (t+1) ω = reference I f ξ t ω ∨
      reference I f ξ (t+1) ω = I.posterior (t+1) ω := by
  rw [reference]
  split <;> simp

theorem estimate_step (I : Input Ω) (f : ℝ → ℝ) (ξ K : ℝ)
    (hξ : 0 < ξ) (hξ' : ξ < 1/2) (hK : 0 ≤ K)
    (hf : ∀ p ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f p)
    (hLip : ∀ p ∈ Set.Icc (0 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1,
      |Real.sqrt (f p) - Real.sqrt (f q)| ≤ K * |p - q|)
    (t : ℕ) (ω : Ω) :
    |estimate I f ξ (t+1) ω - estimate I f ξ t ω| ≤
      (5*K^2/ξ)*(reference I f ξ (t+1) ω - reference I f ξ t ω)^2 := by
  have hpos := I.posterior_range (t+1) ω
  have hprev := reference_range I f ξ t ω
  unfold estimate
  rw [reference]
  split_ifs with h
  · simp
  · have hfails := square_root_failure (hf _ hpos) (hf _ hprev) hξ hξ' h
    have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hK (abs_nonneg _))).mpr
      (hLip _ hpos _ hprev)
    simp only [mul_pow, sq_abs] at hsq
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hξ).mpr
    nlinarith


theorem average_mul (μ X : Ω → ℝ) (C : ℝ) :
    average μ (fun ω => C * X ω) = C * average μ X := by
  simp only [average, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Source Lemma lem:rank-tracking, with the absolute constant made explicit
as five times the common squared Lipschitz constant of the square root. -/
theorem relative_tracker (I : Input Ω) (f : ℝ → ℝ) (ξ K : ℝ)
    (hξ : 0 < ξ) (hξ' : ξ < 1/2) (hK : 0 ≤ K)
    (hf : ∀ p ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f p)
    (hLip : ∀ p ∈ Set.Icc (0 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1,
      |Real.sqrt (f p) - Real.sqrt (f q)| ≤ K * |p - q|) :
    (∀ t ω, (1+ξ)⁻¹ * f (I.posterior t ω) ≤ estimate I f ξ t ω ∧
      estimate I f ξ t ω ≤ (1+ξ) * f (I.posterior t ω)) ∧
    (∀ H, (∑ t ∈ Finset.range H, average I.weight
      (fun ω => |estimate I f ξ (t+1) ω - estimate I f ξ t ω|)) ≤
      (5*K^2/ξ) * (driftBudget I H + 1)) := by
  constructor
  · exact estimate_spec I f ξ hξ hf
  · intro H
    have hC : 0 ≤ 5*K^2/ξ := div_nonneg (by positivity) hξ.le
    calc
      _ ≤ ∑ t ∈ Finset.range H, (5*K^2/ξ) * average I.weight
          (fun ω => (reference I f ξ (t+1) ω - reference I f ξ t ω)^2) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [← average_mul]
        exact average_mono I.weight_nonneg (estimate_step I f ξ K hξ hξ' hK hf hLip t)
      _ = (5*K^2/ξ) * ∑ t ∈ Finset.range H, average I.weight
          (fun ω => (reference I f ξ (t+1) ω - reference I f ξ t ω)^2) := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (reset_credit I (reference I f ξ) (reference_range I f ξ)
          (reference_measurable I f ξ) (reference_step I f ξ) H) hC


noncomputable def refreshCount (I : Input Ω) (δ : ℝ) (H : ℕ) : ℝ :=
  ∑ t ∈ Finset.range H, average I.weight (fun ω =>
    if absoluteReference I δ (t+1) ω = absoluteReference I δ t ω then 0 else 1)


theorem absoluteReference_range (I : Input Ω) (δ : ℝ) :
    ∀ t ω, absoluteReference I δ t ω ∈ Set.Icc (0 : ℝ) 1 := by
  intro t
  induction t with
  | zero => exact I.posterior_range 0
  | succ t ih =>
    intro ω
    rw [absoluteReference]
    split
    · exact ih ω
    · exact I.posterior_range (t+1) ω

theorem absoluteReference_measurable (I : Input Ω) (δ : ℝ) :
    ∀ t, measurableAt I.filtration t (absoluteReference I δ t) := by
  intro t
  induction t with
  | zero => exact I.posterior_measurable 0
  | succ t ih =>
    intro ω ω' hω
    have hp := I.posterior_measurable (t+1) ω ω' hω
    have hr := ih ω ω' (I.refines t ω ω' hω)
    simp only [absoluteReference, hp, hr]

theorem absoluteReference_step (I : Input Ω) (δ : ℝ) (t : ℕ) (ω : Ω) :
    absoluteReference I δ (t+1) ω = absoluteReference I δ t ω ∨
      absoluteReference I δ (t+1) ω = I.posterior (t+1) ω := by
  rw [absoluteReference]
  split <;> simp

theorem absolute_refresh_charge (I : Input Ω) (δ : ℝ) (hδ : 0 < δ) (t : ℕ) (ω : Ω) :
    (if absoluteReference I δ (t+1) ω = absoluteReference I δ t ω then (0 : ℝ) else 1) ≤
      (δ^2)⁻¹ * (absoluteReference I δ (t+1) ω - absoluteReference I δ t ω)^2 := by
  rw [absoluteReference]
  split_ifs with h hsame
  · positivity
  · simp at hsame
  · positivity
  · have hl : δ < |I.posterior (t+1) ω - absoluteReference I δ t ω| := lt_of_not_ge h
    have hs : δ^2 ≤ (I.posterior (t+1) ω - absoluteReference I δ t ω)^2 := by
      nlinarith [sq_abs (I.posterior (t+1) ω - absoluteReference I δ t ω)]
    have hd : 0 < δ^2 := sq_pos_of_pos hδ
    calc
      1 = (δ^2)⁻¹ * δ^2 := (inv_mul_cancel₀ (ne_of_gt hd)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hd.le)

/-- The fixed absolute threshold part of source Lemma lem:rank-tracking. -/
theorem absolute_tracker (I : Input Ω) (δ : ℝ) (hδ : 0 < δ) :
    (∀ t ω, |I.posterior t ω - absoluteReference I δ t ω| ≤ δ) ∧
    (∀ H, refreshCount I δ H ≤ (δ^2)⁻¹ * (driftBudget I H + 1)) := by
  constructor
  · exact absoluteReference_spec I δ hδ.le
  · intro H
    calc
      _ ≤ ∑ t ∈ Finset.range H, (δ^2)⁻¹ * average I.weight
          (fun ω => (absoluteReference I δ (t+1) ω - absoluteReference I δ t ω)^2) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [← average_mul]
        exact average_mono I.weight_nonneg (absolute_refresh_charge I δ hδ t)
      _ = (δ^2)⁻¹ * ∑ t ∈ Finset.range H, average I.weight
          (fun ω => (absoluteReference I δ (t+1) ω - absoluteReference I δ t ω)^2) := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (reset_credit I (absoluteReference I δ) (absoluteReference_range I δ)
          (absoluteReference_measurable I δ) (absoluteReference_step I δ) H)
        (inv_nonneg.mpr (sq_nonneg δ))

end UniformKServer.RankTracking

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RankData
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section

/-! Exact size rank and held core flags from companion §03. -/
noncomputable section
namespace UniformKServer.RankData
open RankFunctions

theorem sizeRank_sqrt (p : ℝ) : Real.sqrt (sizeRank p) = max (3/4-p) 0 / (3/4) := by
  rw [sizeRank, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (le_max_right _ _)]
  norm_num

theorem sizeRank_sqrt_lipschitz (p q : ℝ) :
    |Real.sqrt (sizeRank p)-Real.sqrt (sizeRank q)| ≤ (4/3)*|p-q| := by
  rw [sizeRank_sqrt, sizeRank_sqrt, ← sub_div, abs_div]
  have hm := abs_max_sub_max_le_max (3/4-p) (0 : ℝ) (3/4-q) 0
  have he : |(3/4-p)-(3/4-q)| = |p-q| := by
    rw [show (3/4-p)-(3/4-q) = -(p-q) by ring, abs_neg]
  rw [he, sub_self, abs_zero, max_eq_left (abs_nonneg (p-q))] at hm
  norm_num
  nlinarith

variable {Ω : Type*} [Fintype Ω]

theorem core_refresh (I : RankTracking.Input Ω) (t : ℕ) (ω : Ω) :
    (if core I (t+1) ω = core I t ω then (0 : ℝ) else 1) ≤
      (if RankTracking.absoluteReference I (pstar/8) (t+1) ω =
        RankTracking.absoluteReference I (pstar/8) t ω then (0 : ℝ) else 1) := by
  split_ifs with hc hr hr
  · rfl
  · norm_num
  · exact (hc (by simp only [core, hr])).elim
  · rfl

variable {A : Type*} [Fintype A]

theorem core_mass_bounds (c : A → Bool) (p : A → ℝ)
    (hp : ∀ a, p a ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ coreMass c p ∧ coreMass c p ≤ coreCount c := by
  constructor
  · exact Finset.sum_nonneg fun a _ => by split <;> simp_all
  · apply Finset.sum_le_sum
    intro a ha
    split <;> simp_all

end UniformKServer.RankData

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CoarseData
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Persistent size/core elementary trackers, and their actual held active
 states.  Constants and initialization allowances are uniform in the law and
 horizon. Companion §03, equations active-size-accuracy and coarse-data-budget. -/
noncomputable section
namespace UniformKServer.CoarseData
open Finset RankTracking RankData
variable {Ω A : Type*} [Fintype Ω] [Fintype A]

def totalDrift (I : A → Input Ω) (H : ℕ) : ℝ := ∑ a, driftBudget (I a) H

theorem average_sum (w : Ω → ℝ) (X : A → Ω → ℝ) :
    average w (fun ω => ∑ a, X a ω) = ∑ a, average w (X a) := by
  simp only [average,mul_sum]
  exact sum_comm

theorem sizeEstimate_budget (I : A → Input Ω) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hi : ∀ a, (I a).weight=w)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/2) (H : ℕ) :
    (∑ t ∈ range H, average w (fun ω =>
      |sizeEstimate I δ (t+1) ω-sizeEstimate I δ t ω|)) ≤
      (5*(4/3)^2/δ)*(totalDrift I H+Fintype.card A) := by
  calc
    _ ≤ ∑ t ∈ range H, ∑ a, average w (fun ω =>
        |estimate (I a) sizeRank δ (t+1) ω-estimate (I a) sizeRank δ t ω|) := by
      apply sum_le_sum
      intro t _
      rw [← average_sum]
      apply average_mono hw
      intro ω
      rw [sizeEstimate,sizeEstimate,←sum_sub_distrib]
      exact abs_sum_le_sum_abs _ _
    _ = ∑ a, ∑ t ∈ range H, average w (fun ω =>
        |estimate (I a) sizeRank δ (t+1) ω-estimate (I a) sizeRank δ t ω|) := sum_comm
    _ ≤ ∑ a, (5*(4/3)^2/δ)*(driftBudget (I a) H+1) := by
      apply sum_le_sum
      intro a _
      rw [← hi a]
      exact (relative_tracker (I a) sizeRank δ (4/3) hδ hδ' (by norm_num)
        (fun p _ => sizeRank_nonneg p) (fun p _ q _ => sizeRank_sqrt_lipschitz p q)).2 H
    _ = _ := by simp [totalDrift,←mul_sum,sum_add_distrib]

def coreChange (I : A → Input Ω) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a, if core (I a) (t+1) ω = core (I a) t ω then 0 else 1

theorem coreChange_budget (I : A → Input Ω) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hi : ∀ a, (I a).weight=w) (H : ℕ) :
    (∑ t ∈ range H, average w (coreChange I t)) ≤
      36864*(totalDrift I H+Fintype.card A) := by
  calc
    _ ≤ ∑ t ∈ range H, ∑ a, average w (fun ω =>
        if absoluteReference (I a) (RankFunctions.pstar/8) (t+1) ω =
          absoluteReference (I a) (RankFunctions.pstar/8) t ω then 0 else 1) := by
      apply sum_le_sum
      intro t _
      rw [← average_sum]
      exact average_mono hw (fun ω => sum_le_sum fun a _ => core_refresh (I a) t ω)
    _ = ∑ a, refreshCount (I a) (RankFunctions.pstar/8) H := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      simp only [refreshCount,hi a]
    _ ≤ ∑ a, 36864*(driftBudget (I a) H+1) := by
      apply sum_le_sum
      intro a _
      have h := (absolute_tracker (I a) (RankFunctions.pstar/8)
        (by norm_num [RankFunctions.pstar])).2 H
      norm_num [RankFunctions.pstar] at h
      have he : RankFunctions.pstar/8=(1/192 : ℝ) := by norm_num [RankFunctions.pstar]
      rw [he]
      exact h
    _ = _ := by simp [totalDrift,←mul_sum,sum_add_distrib]

theorem heldSize_path_budget (I : A → Input Ω) (H : ℕ) (ω : Ω) :
    (∑ t ∈ range H, AllocationSchedule.charge (heldSize I t ω) (heldSize I (t+1) ω)) ≤
    2001*(∑ t ∈ range H, |sizeEstimate I sizeTolerance (t+1) ω-sizeEstimate I sizeTolerance t ω|)+
      5*2001*cutoff := by
  have h := AllocationSchedule.schedule_budget (show 0 ≤ cutoff by norm_num [cutoff])
    (show 0 < sizeTolerance by norm_num [sizeTolerance]) (show (3:ℝ) ≤ 2001 by norm_num)
    (show 1+2/sizeTolerance ≤ 2001 by norm_num [sizeTolerance])
    (fun s => sizeEstimate_nonneg I sizeTolerance s ω) H
  have hi := AllocationSchedule.initial_potential_bound (δ:=sizeTolerance)
    (show 0 ≤ cutoff by norm_num [cutoff]) (show (1:ℝ) ≤ 2001 by norm_num)
    (sizeEstimate_nonneg I sizeTolerance 0 ω)
  change _ ≤ _ + AllocationSchedule.potential 2001 cutoff (sizeEstimate I sizeTolerance 0 ω)
    (AllocationSchedule.update cutoff sizeTolerance none (sizeEstimate I sizeTolerance 0 ω)) at h
  exact h.trans (by linarith [hi])


theorem average_range_sum (w : Ω → ℝ) (X : ℕ → Ω → ℝ) (H : ℕ) :
    average w (fun ω => ∑ t ∈ range H, X t ω) = ∑ t ∈ range H, average w (X t) := by
  simp only [average,mul_sum]
  exact sum_comm

theorem average_const (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (c : ℝ) :
    average w (fun _ => c) = c := by rw [average,←sum_mul,hw,one_mul]

theorem heldSize_budget (I : A → Input Ω) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (htotal : ∑ ω, w ω=1)
    (hi : ∀ a, (I a).weight=w) (H : ℕ) :
    (∑ t ∈ range H, average w (fun ω =>
      AllocationSchedule.charge (heldSize I t ω) (heldSize I (t+1) ω))) ≤
      (2001*(5*(4/3)^2/sizeTolerance))*(totalDrift I H+Fintype.card A)+5*2001*cutoff := by
  have h := average_mono hw (heldSize_path_budget I H)
  rw [average_range_sum,average_add,average_mul,average_const w htotal,average_range_sum] at h
  have hb := sizeEstimate_budget I w hw hi (show 0 < sizeTolerance by norm_num [sizeTolerance])
    (show sizeTolerance < 1/2 by norm_num [sizeTolerance]) H
  nlinarith

end UniformKServer.CoarseData

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CoarseBridge
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Pointwise held-size/core bridges for the actual persistent rank trackers. -/
noncomputable section
namespace UniformKServer.CoarseBridge
open Finset UniformKServer.CoarseData UniformKServer.RankData
open scoped Classical
variable {Ω R : Type*} [Fintype Ω] [Fintype R]

theorem held_min (I : R → RankTracking.Input Ω) (t : ℕ) (ω : Ω)
    (hp : 0 < heldSize I t ω) : (9/100000:ℝ) ≤ heldSize I t ω := by
  cases hb : activeState I t ω with
  | none => rw [held_none I t ω hb] at hp; exact (lt_irrefl _ hp).elim
  | some b =>
    rw [held_some I t ω hb]
    have ha := active_accuracy I t ω hb
    norm_num [cutoff] at ha
    linarith

theorem inactive_flags (I : R → RankTracking.Input Ω) (t : ℕ) (ω : Ω)
    (hb : activeState I t ω=none) (r : R) : core (I r) t ω=false := by
  have hz := (inactive_zero I t ω 3 hb).1
  have h : (if core (I r) t ω then (1:ℝ) else 0) ≤ coreCount (fun j => core (I j) t ω) :=
    single_le_sum (f:=fun j => if core (I j) t ω then (1:ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) (mem_univ r)
  rw [hz] at h
  cases hf : core (I r) t ω
  · rfl
  · simp only [hf,ite_true, if_true] at h
    norm_num at h

theorem held_zero_flags (I : R → RankTracking.Input Ω) (t : ℕ) (ω : Ω)
    (hz : heldSize I t ω=0) (r : R) : core (I r) t ω=false := by
  cases hb : activeState I t ω with
  | none => exact inactive_flags I t ω hb r
  | some b =>
    have ha := active_accuracy I t ω hb
    rw [held_some I t ω hb] at hz
    norm_num [cutoff] at ha
    exfalso
    nlinarith [ha.1,ha.2.2]

theorem core_count_bound (I : R → RankTracking.Input Ω) (t : ℕ) (ω : Ω) :
    coreCount (fun r => core (I r) t ω) ≤ 40*heldSize I t ω := by
  cases hb : activeState I t ω with
  | none =>
    rw [(inactive_zero I t ω 3 hb).1,held_none I t ω hb,mul_zero]
  | some b =>
    have hd := core_flex_domination (fun r => core (I r) t ω) 3
      (fun r => (I r).posterior t ω) (by norm_num [RankFunctions.allowed])
      (fun r => ((I r).posterior_range t ω).1) (fun r hr => by
        have hh := core_small (I r) t ω hr
        norm_num [RankFunctions.pstar] at hh ⊢
        linarith)
    have hf : 0 ≤ flex (fun r => core (I r) t ω) 3 (fun r => (I r).posterior t ω) := by
      apply sum_nonneg
      intro r _
      split_ifs
      · exact le_rfl
      · exact RankFunctions.rank_nonneg (by norm_num [RankFunctions.allowed])
    have ha := (active_accuracy I t ω hb).1
    rw [held_some I t ω hb]
    linarith

theorem core_input_bound (I : R → RankTracking.Input Ω) (t : ℕ) (ω : Ω) :
    SyntheticCore.input (fun r => (I r).posterior t ω) (fun r => core (I r) t ω) ≤ 40*heldSize I t ω :=
  (core_mass_bounds (fun r => core (I r) t ω) (fun r => (I r).posterior t ω)
    (fun r => (I r).posterior_range t ω)).2.trans (core_count_bound I t ω)

end UniformKServer.CoarseBridge

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ConditionalRank
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Source §02/§03: the rank-tracker input is constructed from a hidden count,
 not obtained by assuming a martingale. Summed posterior rank drift is bounded
 by the actual count drift, with coefficient one. -/
namespace UniformKServer.ConditionalRank
noncomputable section
open Finset ConditionalLaw
variable {Ω : Type*} [Fintype Ω]

theorem indicator_distance_ordered {n m k : ℕ} (hnm : n ≤ m) (hm : m ≤ k) :
    (∑ j ∈ range k, |indicator n j-indicator m j|) = (m:ℝ)-n := by
  have he (j : ℕ) : |indicator n j-indicator m j| = indicator n j-indicator m j := by
    apply abs_of_nonneg
    unfold indicator
    split_ifs <;> norm_num at *
    omega
  simp_rw [he]
  rw [sum_sub_distrib,indicator_sum (hnm.trans hm),indicator_sum hm]
  ring

theorem indicator_distance {n m k : ℕ} (hn : n ≤ k) (hm : m ≤ k) :
    (∑ j ∈ range k, |indicator n j-indicator m j|) = |(n:ℝ)-m| := by
  rcases le_total n m with h|h
  · rw [indicator_distance_ordered h hm,abs_of_nonpos (by exact_mod_cast (show (n:ℤ)-m ≤ 0 by omega))]
    ring
  · simp_rw [abs_sub_comm (indicator n _) (indicator m _)]
    rw [indicator_distance_ordered h hn,abs_of_nonneg (by exact_mod_cast (show (0:ℤ) ≤ (n:ℤ)-m by omega))]

theorem total_drift {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω)
    (N M : Ω → ℕ) (k : ℕ) (hN : ∀ ω, N ω ≤ k) (hM : ∀ ω, M ω ≤ k) :
    (∑ j ∈ range k, ∑ ω, w ω *
      |posterior w F (fun v => indicator (N v) j) ω-
       posterior w F (fun v => indicator (M v) j) ω|) ≤
      ∑ ω, w ω*|(N ω:ℝ)-M ω| := by
  calc
    _ ≤ ∑ j ∈ range k, ∑ ω, w ω*|indicator (N ω) j-indicator (M ω) j| := by
      apply sum_le_sum
      intro j _
      exact expected_contraction hw F _ _
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro ω _
      rw [←mul_sum,indicator_distance (hN ω) (hM ω)]

end
end UniformKServer.ConditionalRank

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ConditionalRanks
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! The source rank and size inequalities for the actual finite conditional
 law, with normalization proved on every positive-ConditionalLaw.mass history.  Null histories
 are not silently assigned a normalized law. -/
noncomputable section
namespace UniformKServer.ConditionalRanks
open Finset ConditionalLaw RankData
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

theorem rank_superadditivity (w : Ω → ℝ) (hw : ∀ v, 0 ≤ w v)
    (F : Setoid Ω) (ω : Ω) (hm : ConditionalLaw.mass w F ω ≠ 0) (N : Ω → ι → ℕ) (k : ℕ)
    (hN : ∀ v, ∑ i, N v i ≤ k) (β : ℝ) (hβ : RankFunctions.allowed β) :
    (∑ i, totalRank β (fun j : Fin k => rankProbability w F (fun v => N v i) ω j)) ≤
      totalRank β (fun j : Fin k => rankProbability w F (fun v => ∑ i, N v i) ω j) := by
  apply conditional_convex_superadditivity w hw F ω hm N k hN (RankFunctions.rank β)
    ((RankFunctions.rank_convex hβ).subset (Set.subset_univ _) (convex_Icc _ _))
  exact RankFunctions.rank_beyond (by norm_num [RankFunctions.sstar])

/-- The required first rank is zero on positive-weight atoms of the observed
 history; no assertion is inserted for impossible hidden configurations. -/
theorem required_probability_zero (w : Ω → ℝ) (F : Setoid Ω) (ω : Ω) (N : Ω → ℕ)
    (hN : ∀ v, F.r ω v → w v ≠ 0 → 1 ≤ N v) : rankProbability w F N ω 0 = 0 := by
  unfold rankProbability posterior
  apply sum_eq_zero
  intro v _
  by_cases hf : F.r ω v
  · by_cases hw : w v = 0
    · simp only [kernel,ite_eq_left hf,hw,zero_div,zero_mul]
    · have hn := hN v hf hw
      simp only [ConditionalRank.indicator,ite_eq_right (by omega : ¬N v ≤ 0),mul_zero]
  · simp only [kernel,ite_eq_right hf,zero_mul]

theorem required_rank_lower (w : Ω → ℝ) (F : Setoid Ω) (ω : Ω) (N : Ω → ℕ)
    (hN : ∀ v, F.r ω v → w v ≠ 0 → 1 ≤ N v) (k : ℕ) (hk : 0 < k)
    (β : ℝ) (hβ : RankFunctions.allowed β) :
    1 ≤ totalRank β (fun j : Fin k => rankProbability w F N ω j) := by
  have h := single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin k))) =>
    RankFunctions.rank_nonneg (p:=rankProbability w F N ω j) hβ) (mem_univ (⟨0,hk⟩ : Fin k))
  simpa only [totalRank,required_probability_zero w F ω N hN,RankFunctions.rank_zero] using h

end UniformKServer.ConditionalRanks

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AlphaFiniteInput
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
namespace UniformKServer.AlphaFiniteInput
open Finset UniformKServer.AlphaEmpty UniformKServer.ConditionalLaw
open scoped Classical
variable {Ω ι R : Type*} [Fintype Ω] [Fintype ι] [Fintype R]

def post (d : Data Ω ι R) (t : ℕ) (ω : Ω) (i : ι) (r : R) : ℝ :=
  posterior d.weight (d.filtration t) (fun v => d.hidden t v (i,r)) ω

def input (d : Data Ω ι R) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  SyntheticCore.input (post d t ω i) (d.flag t ω i)

def star (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ι → ℝ :=
  SyntheticCore.core (activeFlag (d.param t ω)) (activeFlag (d.param (t+1) ω))
    (post d (t+1) ω) (d.flag (t+1) ω)

def oldMask (d : Data Ω ι R) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  SyntheticCore.input (post d (t+1) ω i) (d.flag t ω i)

def alpha (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ι → ℝ :=
  AlphaRecurrence.trajectory (fun s => d.param s ω) (fun s => star d s ω)
    (fun s => input d s ω) t

def prepared (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ι → ℝ :=
  AlphaRecurrence.prepared (fun s => d.param s ω) (fun s => star d s ω)
    (fun s => input d s ω) t

theorem post_range (d : Data Ω ι R) (t : ℕ) (ω : Ω) (i : ι) (r : R) :
    post d t ω i r ∈ Set.Icc (0:ℝ) 1 :=
  ⟨posterior_nonneg d.nonneg (fun v => (d.hidden_range t v (i,r)).1) _ ω,
    posterior_le_one d.nonneg (fun v => (d.hidden_range t v (i,r)).2) _ ω⟩

theorem input_nonneg (d : Data Ω ι R) (t : ℕ) (ω : Ω) (i : ι) : 0 ≤ input d t ω i :=
  SyntheticCore.input_nonneg (fun r => (post_range d t ω i r).1) _

theorem input_supported (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    DomainTransport.Supported (active (d.param t ω)) (input d t ω) := by
  intro i hi
  exact SyntheticCore.no_flags _ (d.supported t ω i hi)

theorem star_supported_old (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    DomainTransport.Supported (active (d.param t ω)) (star d t ω) := by
  intro i hi
  simp [star,SyntheticCore.core,activeFlag,hi]

theorem star_supported_new (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    DomainTransport.Supported (active (d.param (t+1) ω)) (star d t ω) := by
  intro i hi
  simp [star,SyntheticCore.core,activeFlag,hi]

theorem valid_input (d : Data Ω ι R) (ω : Ω) :
    AlphaRecurrence.InputValid (fun s => d.param s ω) (fun s => star d s ω)
      (fun s => input d s ω) := by
  refine ⟨fun t => d.param_valid t ω,?_,fun t => input_nonneg d t ω,?_,
    fun t => star_supported_old d t ω,fun t => star_supported_new d t ω,
    fun t => input_supported d t ω⟩
  · intro t i
    exact (SyntheticCore.core_le_new _ _ _ _ (fun i r => (post_range d (t+1) ω i r).1) i).1
  · intro t
    exact sum_le_sum fun i _ => (SyntheticCore.core_le_new _ _ _ _
      (fun i r => (post_range d (t+1) ω i r).1) i).2

theorem errors (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    (∑ i, |oldMask d t ω i-star d t ω i|) ≤ changes d t ω ∧
    (∑ i, |input d (t+1) ω i-star d t ω i|) ≤ changes d t ω ∧
    0 ≤ (∑ i, input d (t+1) ω i)-(∑ i, star d t ω i) ∧
    (∑ i, input d (t+1) ω i)-(∑ i, star d t ω i) ≤ changes d t ω :=
  SyntheticCore.errors _ _ _ _ _ (post_range d (t+1) ω)
    (flag_supported d t ω) (flag_supported d (t+1) ω)

theorem alpha_state (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    state (d.param t ω) (alpha d t ω) := AlphaRecurrence.trajectory_state (valid_input d ω) t

theorem step (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    AlphaRecurrence.StepSpec (d.param t ω) (d.param (t+1) ω) (star d t ω) (input d (t+1) ω)
      (alpha d t ω) (alpha d (t+1) ω) (prepared d t ω) :=
  AlphaRecurrence.trajectory_step (valid_input d ω) t

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

theorem alpha_measurable (d : Data Ω ι R) (t : ℕ) {ω v : Ω}
    (h : (d.filtration t).r ω v) : alpha d t ω=alpha d t v := by
  apply AlphaRecurrence.causal_through
  · intro s hs
    exact d.param_measurable s ω v (refining d hs h)
  · intro s hs
    exact star_measurable d s (refining d (Nat.succ_le_iff.mpr hs) h)
  · intro s hs
    exact input_measurable d s (refining d hs h)

end UniformKServer.AlphaFiniteInput

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AlphaFiniteLedger
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                        
section

/-! The actual alpha trajectory has an all-step finite-law movement ledger.
 Filtering coefficients are the primitives' proved affine coefficients and are
 measured before refresh tests. Parameter jumps remain their exact signed
 values for the subsequent sparse-charge estimate. -/
noncomputable section
namespace UniformKServer.AlphaFiniteLedger
open Finset UniformKServer.AlphaEmpty UniformKServer.AlphaFiniteInput
open scoped Classical
variable {Ω ι R : Type*} [Fintype Ω] [Fintype ι] [Fintype R]

def potential (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  AlphaEmpty.potential (d.param t ω) (input d t ω) (alpha d t ω)

def movement (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  (∑ i, input d (t+1) ω i)*SimplexTracker.movement (alpha d (t+1) ω) (alpha d t ω)

def jump (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  AlphaEmpty.potential (d.param (t+1) ω) (star d t ω) (prepared d t ω)-
    AlphaEmpty.potential (d.param t ω) (star d t ω) (prepared d t ω)

def coefficient (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ι × R → ℝ :=
  CoreFiltering.liftCoefficient (fun v => AlphaEmptyLinear.coefficient (d.param t v) (alpha d t v))
    (d.flag t) ω

theorem coefficient_bound (d : Data Ω ι R) {K : ℝ} (hK : 0 ≤ K)
    (hk : ∀ t ω, scale (d.param t ω) ≤ K) (t : ℕ) (ω : Ω) (ir : ι × R) :
    |coefficient d t ω ir| ≤ 15*K := by
  apply CoreFiltering.lift_bound _ _ (by positivity) _ ω ir
  intro v i
  exact (AlphaEmptyLinear.bound (d.param_valid t v) _ (alpha_state d t v) i).trans
    (mul_le_mul_of_nonneg_left (hk t v) (by norm_num))

theorem coefficient_measurable (d : Data Ω ι R) (t : ℕ) (ir : ι × R) :
    ConditionalLaw.measurable (d.filtration t) (fun ω => coefficient d t ω ir) := by
  apply CoreFiltering.lift_measurable
  · intro i ω v h
    dsimp only
    rw [d.param_measurable t ω v h,alpha_measurable d t h]
  · intro ω v h i r
    rw [d.flag_measurable t ω v h]

theorem frozen_change (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    AlphaEmpty.potential (d.param t ω) (oldMask d t ω) (alpha d t ω)-potential d t ω =
      AdaptiveLedger.increment d.weight (d.filtration t) (d.filtration (t+1))
        (coefficient d t) (d.hidden t) ω+
      AdaptiveLedger.drift d.weight (d.filtration (t+1))
        (coefficient d t) (d.hidden t) (d.hidden (t+1)) ω := by
  have ha := AlphaEmpty.state_interval (alpha_state d t ω)
  unfold potential
  rw [AlphaEmptyLinear.affine (d.param_valid t ω) _ _ ha,
    AlphaEmptyLinear.affine (d.param_valid t ω) _ _ ha]
  have hnew : oldMask d t ω = CoreFiltering.masked (d.flag t)
      (AdaptiveLedger.post d.weight (d.filtration (t+1)) (d.hidden (t+1))) ω := rfl
  have hold : input d t ω = CoreFiltering.masked (d.flag t)
      (AdaptiveLedger.post d.weight (d.filtration t) (d.hidden t)) ω := rfl
  rw [hnew,hold,CoreFiltering.masked_linear
    (fun v => AlphaEmptyLinear.coefficient (d.param t v) (alpha d t v)),
    CoreFiltering.masked_linear
    (fun v => AlphaEmptyLinear.coefficient (d.param t v) (alpha d t v))]
  simp only [AdaptiveLedger.increment,AdaptiveLedger.drift,←sum_add_distrib,←sum_sub_distrib]
  apply sum_congr rfl
  intro ir _
  change coefficient d t ω ir * _-coefficient d t ω ir * _ = _
  ring

theorem step_bound (d : Data Ω ι R) {K : ℝ}
    (hk : ∀ t ω, scale (d.param t ω) ≤ K) (t : ℕ) (ω : Ω) :
    movement d t ω ≤ potential d t ω-potential d (t+1) ω+
      AdaptiveLedger.increment d.weight (d.filtration t) (d.filtration (t+1))
        (coefficient d t) (d.hidden t) ω+
      AdaptiveLedger.drift d.weight (d.filtration (t+1))
        (coefficient d t) (d.hidden t) (d.hidden (t+1)) ω+
      (jump d t ω+(30*K+4)*changes d t ω) := by
  have hs := (AlphaFiniteInput.step d t ω).2.2.2.2
  have he := errors d t ω
  have ho := AlphaEmpty.input_bound (d.param_valid t ω) (star d t ω) (oldMask d t ω)
    (alpha d t ω) (alpha_state d t ω)
  have hdiff : (∑ i, |star d t ω i-oldMask d t ω i|) ≤ changes d t ω := by
    simpa only [abs_sub_comm] using he.1
  have hr : 0 ≤ changes d t ω := sum_nonneg fun i _ => SyntheticCore.changes_nonneg _ _
  have hold : AlphaEmpty.potential (d.param t ω) (star d t ω) (alpha d t ω) ≤
      AlphaEmpty.potential (d.param t ω) (oldMask d t ω) (alpha d t ω)+15*K*changes d t ω := by
    have hb := (le_abs_self _).trans (ho.trans (mul_le_mul_of_nonneg_left hdiff
      (mul_nonneg (by norm_num) (scale_nonneg (d.param_valid t ω)))))
    have hb' := mul_le_mul_of_nonneg_right (hk t ω) hr
    nlinarith
  have hnew : 15*scale (d.param (t+1) ω)*(∑ i, |input d (t+1) ω i-star d t ω i|) ≤
      15*K*changes d t ω := by
    apply (mul_le_mul_of_nonneg_left he.2.1
      (mul_nonneg (by norm_num) (scale_nonneg (d.param_valid (t+1) ω)))).trans
    have hb := mul_le_mul_of_nonneg_right (hk (t+1) ω) hr
    nlinarith
  have hf := frozen_change d t ω
  change movement d t ω ≤ _ at hs
  change _ - potential d t ω = _ at hf
  dsimp only [jump,potential,movement] at *
  nlinarith [he.2.2.2]

theorem budget (d : Data Ω ι R) {K : ℝ} (hK : 0 ≤ K)
    (hk : ∀ t ω, scale (d.param t ω) ≤ K) (H : ℕ) :
    (∑ t ∈ range H, AdaptiveLedger.expect d.weight (movement d t)) ≤
      AdaptiveLedger.expect d.weight (potential d 0)-AdaptiveLedger.expect d.weight (potential d H)+
      15*K*(∑ t ∈ range H, AdaptiveLedger.expect d.weight
        (fun ω => ∑ ir, |d.hidden (t+1) ω ir-d.hidden t ω ir|))+
      ∑ t ∈ range H, AdaptiveLedger.expect d.weight
        (fun ω => jump d t ω+(30*K+4)*changes d t ω) :=
  AdaptiveLedger.telescope d.nonneg d.filtration d.refines (coefficient d) d.hidden
    (potential d) (movement d) (fun t ω => jump d t ω+(30*K+4)*changes d t ω)
    (by positivity) (coefficient_bound d hK hk) (coefficient_measurable d)
    (step_bound d hk) H

end UniformKServer.AlphaFiniteLedger

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AlphaParameterChanges
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                            
section

/-! Prepared logarithmic parameter changes. All bounds concern the actual
 improper primitives, with constants uniform at vanishing side mass. -/
noncomputable section
namespace UniformKServer.AlphaParameterChanges
open Finset UniformKServer.AdaptiveAlpha
open scoped Classical
variable {ι : Type*} [Fintype ι]

/-- A regular epoch, including additions/removals, charges only the coordinates
 whose parameter piece changes. The indicator is later identified with held
 size refreshes; no degree factor appears. -/
theorem regular_jump {p q : Config ι} (hp : valid p) (hq : valid q)
    (hep : p.param.kind=.regular) (heq : q.param.kind=.regular)
    (B a : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hsp : DomainTransport.Supported p.active B) (hsq : DomainTransport.Supported q.active B)
    (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1)
    (hf : ∀ i, (∑ j, B j)*a i ≤ 2*B i)
    (changed : ι → Prop) [DecidablePred changed]
    (same : ∀ i, ¬changed i → piece p B a i=piece q B a i) :
    |potential q B a-potential p B a| ≤
      4*(scale p+scale q)*(∑ i, if changed i then B i else 0) := by
  have bound (r : Config ι) (hr : valid r) (he : r.param.kind=.regular)
      (hs : DomainTransport.Supported r.active B) (i : ι) :
      |piece r B a i| ≤ 4*scale r*B i := by
    by_cases hi : i ∈ r.active
    · apply regular_piece hr B a hB hs ha hf ⟨i,hi⟩
      · simp [ProportionParameters.component,he]
      · have hk := hr.2.2.2.2.2
        simp only [he] at hk
        exact hk.1 ⟨i,hi⟩
    · rw [piece_outside _ _ _ _ hi,abs_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) (scale_nonneg hr)) (hB i)
  rw [←sum_piece,←sum_piece,←sum_sub_distrib,mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  by_cases hi : changed i
  · rw [ite_eq_left hi]
    exact (abs_sub _ _).trans (by nlinarith [bound p hp hep hsp i,bound q hq heq hsq i])
  · rw [ite_eq_right hi,same i hi,sub_self,abs_zero,mul_zero]

/-- Whole marked potential on a prepared state. In particular only side input
 and u times total input are charged when the distinguished parameter changes. -/
theorem marked_prepared {p : Config ι} (hp : valid p) (o : p.active) (u : ℝ)
    (he : p.param.kind=.marked o u) (B a : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hs : DomainTransport.Supported p.active B)
    (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1) (hasum : ∑ i, a i=1)
    (hf : ∀ i, (∑ j, B j)*a i ≤ 2*B i) :
    |potential p B a| ≤ 13*scale p*((∑ i, B i)-B o)+
      3*scale p*(p.param.ct/p.param.ell)*u*(∑ i, B i) := by
  have hk := hp.2.2.2.2.2
  simp only [he] at hk
  have hS : 0 ≤ ∑ i, B i := sum_nonneg fun i _ => hB i
  have hBo : B o ≤ ∑ i, B i := single_le_sum (fun j _ => hB j) (mem_univ o.val)
  have hηo : ProportionParameters.eta p.param o=(p.param.ct/p.param.ell)*u := by
    unfold ProportionParameters.eta
    rw [hk.2.2.1]; ring
  have hmark := AlphaStability.marked_prepared_component (E:=1) hk.1 hk.2.1 (ha o) hS (hB o) hBo
    (ProportionParameters.eta_nonneg hp.2 o) (le_of_eq hηo) (by convert prepared_side B a hasum hf o using 1; norm_num) (scale p)
  rw [abs_of_nonneg (scale_nonneg hp)] at hmark
  have hpo : piece p B a o=LogPrimitive.primitive (Denominators.marked u) 1 (scale p)
      (∑ i, B i) ((1+ProportionParameters.eta p.param o)*B o) (a o) := by
    rw [piece_inside]
    unfold ProportionParameters.component
    rw [he]
    unfold AlphaTracker.markedG AlphaTracker.markedF
    simp only [ite_true, if_true]
    rw [DomainTransport.sum_restrict hs]
    rfl
  have hreg (i : ι) (hi : i ≠ o.val) : |piece p B a i| ≤ 4*scale p*B i := by
    by_cases hip : i ∈ p.active
    · have hio : (⟨i,hip⟩ : p.active) ≠ o := by intro h; exact hi (congrArg Subtype.val h)
      apply regular_piece hp B a hB hs ha hf ⟨i,hip⟩
      · unfold ProportionParameters.component
        rw [he]
        unfold AlphaTracker.markedG AlphaTracker.markedF AlphaTracker.regularG
        simp only [ite_eq_right hio]
      · exact hk.2.2.2.1 _ hio
    · rw [piece_outside _ _ _ _ hip,abs_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) (scale_nonneg hp)) (hB i)
  have h := sum_le_sum (s:=univ.erase o.val) (fun i hi => hreg i (mem_erase.mp hi).1)
  rw [←mul_sum] at h
  rw [←hpo] at hmark
  calc
    _ = |(∑ i ∈ univ.erase o.val, piece p B a i)+piece p B a o| := by
      rw [sum_erase_add _ _ (mem_univ o.val),sum_piece]
    _ ≤ (∑ i ∈ univ.erase o.val, |piece p B a i|)+|piece p B a o| :=
      (abs_add_le _ _).trans (add_le_add (abs_sum_le_sum_abs _ _) le_rfl)
    _ ≤ 4*scale p*(∑ i ∈ univ.erase o.val, B i)+
        3*scale p*((2+1)*((∑ i, B i)-B o)+(p.param.ct/p.param.ell)*u*(∑ i, B i)) :=
      add_le_add h hmark
    _ = _ := by rw [sum_erase_eq_sub (mem_univ o.val)]; ring

/-- The distinguished summand does not move when its held ratio is unchanged.
Only regular side summands remain in a size-refresh charge. -/
theorem marked_sparse_jump {p q : Config ι} (hp : valid p) (hq : valid q)
    (op : p.active) (oq : q.active) (u : ℝ)
    (hep : p.param.kind=.marked op u) (heq : q.param.kind=.marked oq u)
    (ho : op.val=oq.val) (B a : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hsp : DomainTransport.Supported p.active B) (hsq : DomainTransport.Supported q.active B)
    (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1)
    (hf : ∀ i, (∑ j, B j)*a i ≤ 2*B i)
    (changed : ι → Prop) [DecidablePred changed]
    (same : ∀ i, ¬changed i → piece p B a i=piece q B a i)
    (mark : ¬changed op.val) :
    |potential q B a-potential p B a| ≤
      4*(scale p+scale q)*(∑ i, if changed i then B i else 0) := by
  have bound (r : Config ι) (hr : valid r) (o : r.active)
      (he : r.param.kind=.marked o u) (hs : DomainTransport.Supported r.active B)
      (i : ι) (hio : i ≠ o.val) : |piece r B a i| ≤ 4*scale r*B i := by
    by_cases hi : i ∈ r.active
    · have hne : (⟨i,hi⟩ : r.active) ≠ o := by
        intro h; exact hio (congrArg Subtype.val h)
      apply regular_piece hr B a hB hs ha hf ⟨i,hi⟩
      · unfold ProportionParameters.component
        rw [he]
        unfold AlphaTracker.markedG AlphaTracker.markedF AlphaTracker.regularG
        simp only [ite_eq_right hne]
      · have hk := hr.2.2.2.2.2
        simp only [he] at hk
        exact hk.2.2.2.1 _ hne
    · rw [piece_outside _ _ _ _ hi,abs_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) (scale_nonneg hr)) (hB i)
  rw [←sum_piece,←sum_piece,←sum_sub_distrib,mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  by_cases hi : changed i
  · rw [ite_eq_left hi]
    have hio : i ≠ op.val := by rintro rfl; exact mark hi
    have hio' : i ≠ oq.val := by simpa only [←ho] using hio
    have hpbound := bound p hp op hep hsp i hio
    have hqbound := bound q hq oq heq hsq i hio'
    exact (abs_sub _ _).trans (by nlinarith)
  · rw [ite_eq_right hi,same i hi,sub_self,abs_zero,mul_zero]

end UniformKServer.AlphaParameterChanges

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AlphaPrepared
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Common-core prepared states can be evaluated in either parameter domain.
 The zero-weight case is proved separately; there is no hidden division by a
 small core mass. -/
noncomputable section
namespace UniformKServer.AlphaPrepared
open Finset UniformKServer.AlphaEmpty
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem bound {p q : Config ι} (hp : valid p) (B b : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hs : DomainTransport.Supported (active p) B)
    (hqB : DomainTransport.Supported (active q) B) (hb : state q b)
    (hf : ∀ i, (∑ j, B j)*b i ≤ (1+eta p i)*B i) :
    |potential p B b| ≤ 15*scale p*(∑ i, B i) := by
  have hS : 0 ≤ ∑ i, B i := sum_nonneg fun i _ => hB i
  rcases hS.eq_or_lt with hz | hpos
  · have he := zero_of_sum hB hz.symm
    rw [he,potential_zero,abs_zero,sum_const_zero,mul_zero]
  · have ho := prepared_state hpos hs hqB hb hf
    have h := input_bound hp B (fun _ => 0) b ho
    simpa only [potential_zero,sub_zero,abs_of_nonneg (hB _)] using h

theorem jump {p q : Config ι} (hp : valid p) (hq : valid q) (B b : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hs : DomainTransport.Supported (active p) B)
    (hqB : DomainTransport.Supported (active q) B) (hb : state q b)
    (hf : ∀ i, (∑ j, B j)*b i ≤ (1+eta p i)*B i) :
    |potential q B b-potential p B b| ≤ 15*(scale p+scale q)*(∑ i, B i) := by
  have h := bound hp B b hB hs hqB hb hf
  have h' := input_bound hq B (fun _ => 0) b hb
  simp only [potential_zero,sub_zero,abs_of_nonneg (hB _)] at h'
  exact (abs_sub _ _).trans (by nlinarith)

end UniformKServer.AlphaPrepared

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AnchorRamp
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Exact clipped ramp and retained-heavy-anchor release. All integrals here
are finite weighted sums on the original finite metric. -/
noncomputable section
namespace UniformKServer.AnchorRamp
open Finset
open scoped Classical

variable {X : Type*} [MetricSpace X]

theorem change (r : ℝ) (hr : 0 < r) (a y z : X) :
    r*max (value r a z-value r a y) 0 ≤
      if dist a y < 7*r then dist y z/3 else 0 := by
  by_cases hy : dist a y < 7*r
  · rw [ite_eq_left hy]
    have hL := lipschitz (dist a z/r) (dist a y/r)
    have hd : |dist a z-dist a y| ≤ dist y z := by
      simpa only [dist_comm] using abs_dist_sub_le z y a
    have hd' : |dist a z/r-dist a y/r| ≤ dist y z/r := by
      rw [←sub_div,abs_div,abs_of_pos hr]
      exact div_le_div_of_nonneg_right hd hr.le
    have h : value r a z-value r a y ≤ dist y z/r/3 := by
      exact (le_abs_self _).trans (hL.trans (div_le_div_of_nonneg_right hd' (by norm_num)))
    have hm : max (value r a z-value r a y) 0 ≤ dist y z/r/3 :=
      max_le h (by positivity)
    have hh := mul_le_mul_of_nonneg_left hm hr.le
    calc
      _ ≤ r*(dist y z/r/3) := hh
      _ = _ := by field_simp
  · rw [ite_eq_right hy]
    have ho : value r a y=1 := one _ ((le_div_iff₀ hr).2 (by linarith))
    rw [ho,max_eq_right (by linarith [(value_range r a z).2]),mul_zero]

variable [Fintype X]

theorem integral_drop (μ : X → ℝ) (hμ : ∀ z, 0 ≤ μ z) (C : Finset X)
    (r γ δ : ℝ) (hr : 0 < r) (hγ : γ < 1) (a x : X)
    (ha : 8*r < dist a x) (hC : ball x (γ*r) ⊆ C)
    (hm : mass μ C ≤ (1+δ)*mass μ (ball x (γ*r))) :
    (∑ z ∈ C, μ z*(value r x z-value r a z)) ≤ -(1-δ)*mass μ (ball x (γ*r)) := by
  have hp (z : X) : value r x z-value r a z ≤ if z ∈ ball x (γ*r) then -1 else 1 := by
    by_cases hz : z ∈ ball x (γ*r)
    · rw [ite_eq_left hz]
      exact (inner_change r γ hr hγ a x z ha (mem_filter.mp hz).2).le
    · rw [ite_eq_right hz]
      linarith [(value_range r x z).2,(value_range r a z).1]
  have hs := sum_le_sum (fun z (_ : z ∈ C) => mul_le_mul_of_nonneg_left (hp z) (hμ z))
  have he : (∑ z ∈ C, μ z*(if z ∈ ball x (γ*r) then -1 else 1))=
      mass μ C-2*mass μ (ball x (γ*r)) := by
    have ht (z : X) : μ z*(if z ∈ ball x (γ*r) then -1 else 1)=μ z-2*(if z ∈ ball x (γ*r) then μ z else 0) := by
      split_ifs <;> ring
    simp_rw [ht]
    rw [sum_sub_distrib,←mul_sum,←sum_filter]
    congr 2
    rw [filter_mem_eq_inter,inter_eq_right.mpr hC]
    rfl
  rw [he] at hs
  nlinarith

end UniformKServer.AnchorRamp

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AnchorScalar
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! The signed scalar accounting inequalities for the reference, park and
hidden-key substeps of the retained-anchor potential. -/
noncomputable section
namespace UniformKServer.AnchorScalar
open Finset
open scoped Classical

variable {X H T : Type*} [MetricSpace X]

theorem member (r C : ℝ) (hr : 0 < r) (c : H→ℝ) (a : H→X) (hc : ∀ h,0 ≤ c h)
    (hC : 0≤C) (hcC : ∀ h,c h≤C) (l m : H⊕T) (y z : X) :
    r*(value r c a m z-value r c a l y)≤
      C*r*(if l=m then 0 else 1)+dist y z/3*near r c a l y := by
  by_cases he : l=m
  · subst m
    rw [ite_eq_left rfl,mul_zero,zero_add]
    cases l with
    | inr _ => simp only [value,near,sub_self,mul_zero]; exact le_rfl
    | inl h =>
      have hp := AnchorRamp.change r hr (a h) y z
      have hm := mul_le_mul_of_nonneg_left hp (hc h)
      have hle := mul_le_mul_of_nonneg_left
        (le_max_left (AnchorRamp.value r (a h) z-AnchorRamp.value r (a h) y) 0)
        (mul_nonneg (hc h) hr.le)
      dsimp only [value,near]
      split_ifs with hd
      · rw [ite_eq_left hd] at hm
        nlinarith only [hm,hle]
      · rw [ite_eq_right hd] at hm
        simp only [mul_zero] at hm ⊢
        nlinarith only [hm,hle]
  · rw [ite_eq_right he,mul_one]
    have hm := value_bound r C c a hc hC hcC m z
    have hl := value_nonneg r c a hc l y
    have hnear := near_nonneg r c a hc l y
    have hd : 0≤dist y z/3*near r c a l y := mul_nonneg (by positivity) hnear
    nlinarith

end UniformKServer.AnchorScalar

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

structure Input (Ω : Type*) [Fintype Ω] (K : ℝ) where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω=1
  filtration : ℕ → Setoid Ω
  refines : ∀ t ω v, (filtration (t+1)).r ω v → (filtration t).r ω v
  size : ℕ → Ω → ℝ
  filtered : ℕ → Ω → ℝ
  range : ∀ t ω, size t ω ∈ Set.Icc 1 K
  measurable : ∀ t, measurableAt filtration t (size t)
  filtering : ∀ t a, measurableAt filtration t a →
    average weight (fun ω => a ω*(filtered (t+1) ω-size t ω))=0

variable {K : ℝ}

def held (I : Input Ω K) : ℕ → Ω → ℝ
  | 0, ω => I.size 0 ω
  | t+1, ω => if keep (I.size (t+1) ω) (held I t ω) then held I t ω else I.size (t+1) ω

def charge (I : Input Ω K) (t : ℕ) (ω : Ω) : ℝ :=
  if keep (I.size (t+1) ω) (held I t ω) then 0 else held I t ω+held I (t+1) ω

theorem held_range (I : Input Ω K) (t : ℕ) (ω : Ω) : held I t ω ∈ Set.Icc 1 K := by
  induction t with
  | zero => exact I.range 0 ω
  | succ t ih => simp only [held]; split_ifs; exact ih; exact I.range _ _

end UniformKServer.KeySizeTracker

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AnchorPotential
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Finite heavy-slot potentials and the non-event-conditioned parameter
substeps. This is scalar accounting, not an assumption of the travel budget. -/
noncomputable section
namespace UniformKServer.AnchorPotential
open Finset
open scoped Classical
variable {X H T Ω : Type*} [Fintype H] [MetricSpace X] [Fintype Ω]

theorem regroup [Fintype X] (r : ℝ) (μ : X→ℝ) (c : H→ℝ) (a : H→X) (key : X→H⊕T) :
    (∑ l : H,c l*integral r μ (univ.filter (fun p=>key p=Sum.inl l)) (a l))=
      ∑ p,μ p*AnchorScalar.value r c a (key p) p := by
  simp only [integral,sum_filter,mul_sum,mul_ite,mul_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  cases he : key p with
  | inr b => simp only [Sum.inr_ne_inl,ite_false, if_false,sum_const_zero,AnchorScalar.value,mul_zero]
  | inl l =>
    simp only [Sum.inl.injEq]
    rw [sum_ite_eq,ite_eq_left (mem_univ l)]
    simp only [AnchorScalar.value]
    ring

theorem reference {K : ℝ} (I : KeySizeTracker.Input Ω K) (r b M V C : ℝ)
    (t : ℕ) (ω : Ω) (hr : 0 ≤ r) (hb : 0 ≤ b) (hV : 0 ≤ V) (hVM : V ≤ M)
    (hs : I.size (t+1) ω=1+M) (hbC : b ≤ C*KeySizeTracker.held I t ω) (hC : 0 ≤ C) :
    r*b/KeySizeTracker.held I (t+1) ω*V-r*b/KeySizeTracker.held I t ω*V ≤ 
      r*C*KeySizeTracker.charge I t ω := by
  by_cases he : KeySizeTracker.keep (I.size (t+1) ω) (KeySizeTracker.held I t ω)
  · simp only [KeySizeTracker.held,ite_eq_left he,KeySizeTracker.charge,sub_self,mul_zero,le_refl]
  · have hu : 0<KeySizeTracker.held I t ω := by have := (KeySizeTracker.held_range I t ω).1; linarith
    have hspos : 0<I.size (t+1) ω := by have := (I.range (t+1) ω).1; linarith
    have h := AnchorScalar.reference r b V M (KeySizeTracker.held I t ω) (I.size (t+1) ω) C
      hr hb hV hVM hu hs hspos hbC hC
    simpa only [KeySizeTracker.held,ite_eq_right he,KeySizeTracker.charge] using h

end UniformKServer.AnchorPotential

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BalancedRepair
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

                                                                      
                                                                        
                                                                  
namespace UniformKServer.BalancedRepair
open scoped symmDiff
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]

omit [Fintype Ω] in
theorem transfer_admissible {μ : Ω → ℝ} {r : Ω → ℕ} {g : Joint Ω ι}
    (hg : admissible μ r g) (q q' : Ω × Finset ι) (ε : ℝ)
    (hε : 0 ≤ ε) (hbound : ε ≤ g q) (hstate : q.1 = q'.1)
    (hcard : q'.2.card = r q'.1) :
    admissible μ r (transfer g q q' ε) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    dsimp [transfer]
    have hsub : 0 ≤ g z - (if z = q then ε else 0) := by
      split_ifs with h
      · subst z; exact sub_nonneg.mpr hbound
      · simpa using hg.1 z
    exact add_nonneg hsub (by split <;> positivity)
  · intro ω
    simp only [transfer, Finset.sum_add_distrib, Finset.sum_sub_distrib, hg.2.1]
    have he : ∀ a : Ω × Finset ι, (∑ A : Finset ι, if (ω,A) = a then ε else 0) =
        if ω = a.1 then ε else 0 := by
      intro a
      rcases a with ⟨ω', A'⟩
      by_cases h : ω = ω'
      · subst ω'; simp
      · simp [h]
    rw [he, he, hstate]
    ring
  · intro z hz
    have hnew : z ≠ q' := by intro h; subst z; exact hz hcard
    have hold : z = q → ε = 0 := by
      intro h
      subst z
      have hzero := hg.2.2 q hz
      linarith
    simp only [transfer, hg.2.2 z hz, ite_eq_right hnew, add_zero, zero_sub]
    split_ifs with h
    · simp [hold h]
    · simp


omit [Fintype Ω] in
theorem swap_admissible {μ : Ω → ℝ} {r : Ω → ℕ} {g : Joint Ω ι}
    (hg : admissible μ r g) (ω : Ω) (A : Finset ι) (i j : ι) (ε : ℝ)
    (hε : 0 ≤ ε) (hbound : ε ≤ g (ω,A)) (hcard : A.card = r ω)
    (hi : i ∈ A) (hj : j ∉ A) : admissible μ r (swap g ω A i j ε) := by
  apply transfer_admissible hg (ω,A) (ω,exchange A i j) ε hε hbound rfl
  simpa [exchange_card hi hj] using hcard

theorem minimizer_exact (μ : Ω → ℝ) (r : Ω → ℕ) (base : Ω → Finset ι) (f : ι → ℝ)
    (hμsum : ∑ ω, μ ω = 1) (s : ℕ) (hr : ∀ ω, r ω = s ∨ r ω = s+1)
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1)
    (hsum : ∑ i, f i = ∑ ω, μ ω * (r ω : ℝ))
    (g : Joint Ω ι) (hg : admissible μ r g)
    (hmin : ∀ g', admissible μ r g' → objective base f g ≤ objective base f g') :
    ∀ i, marginal g i = f i := by
  by_contra hne
  obtain ⟨i,j,hi,hj⟩ := discrepancy_pair ((sum_marginal hg).trans hsum.symm) hne
  have hij : i ≠ j := by intro h; subst j; linarith
  by_cases hdirect : ∃ q : Ω × Finset ι, 0 < g q ∧ i ∈ q.2 ∧ j ∉ q.2
  · obtain ⟨q,hq,hiA,hjA⟩ := hdirect
    obtain ⟨ε,hε,heq,_,hei,hej⟩ := four_positive hq hq (sub_pos.mpr hi) (sub_pos.mpr hj)
    let g' := swap g q.1 q.2 i j ε
    have hg' : admissible μ r g' := swap_admissible hg _ _ _ _ _ hε.le heq
      (supported_card hg hq) hiA hjA
    have hmarg := swap_marginal g q.1 q.2 i j ε hiA hjA
    have hd := discrepancy_transfer hij hε.le hei hej hmarg
    have hc := swap_cost base g q.1 q.2 i j ε hε.le
    have hm := hmin g' hg'
    change cost base g + 10*discrepancy f g ≤ cost base g' + 10*discrepancy f g' at hm
    change discrepancy f g' = _ at hd
    change cost base g' ≤ _ at hc
    rw [hd] at hm
    linarith
  · obtain ⟨a,ha,hia⟩ := supported_mem hg (lt_of_le_of_lt (hf i).1 hi)
    have hja : j ∈ a.2 := by
      by_contra h
      exact hdirect ⟨a,ha,hia,h⟩
    obtain ⟨b,hb,hjb⟩ := supported_notMem hg hμsum (lt_of_lt_of_le hj (hf j).2)
    have hib : i ∉ b.2 := by
      intro h
      exact hdirect ⟨b,hb,h,hjb⟩
    have hca := supported_card hg ha
    have hcb := supported_card hg hb
    have hcards : a.2.card ≤ b.2.card + 1 := by
      rcases hr a.1 with h | h <;> rcases hr b.1 with h' | h' <;> omega
    obtain ⟨h,hhb,hha⟩ := exchange_intermediate hij hia hja hib hjb hcards
    have hih : i ≠ h := by intro he; subst h; exact hha hia
    have hjh : j ≠ h := by intro he; subst h; exact hha hja
    obtain ⟨ε,hε,hea,heb,hei,hej⟩ := four_positive ha hb (sub_pos.mpr hi) (sub_pos.mpr hj)
    let g₁ := swap g a.1 a.2 i h ε
    have hg₁ : admissible μ r g₁ := swap_admissible hg _ _ _ _ _ hε.le hea hca hia hha
    have hneq₀ : (b.1,b.2) ≠ (a.1,a.2) := by
      intro he
      have he' := congrArg Prod.snd he
      exact hjb (he' ▸ hja)
    have hneq₁ : (b.1,b.2) ≠ (a.1,exchange a.2 i h) := by
      intro he
      have he' := congrArg Prod.snd he
      apply hjb
      rw [he']
      simp [exchange, Ne.symm hij, hja]
    have hgb : g₁ (b.1,b.2) = g b := by
      simp [g₁, swap, transfer, hneq₀, hneq₁]
    let g₂ := swap g₁ b.1 b.2 h j ε
    have hg₂ : admissible μ r g₂ := swap_admissible hg₁ _ _ _ _ _ hε.le
      (by simpa [hgb] using heb) hcb hhb hjb
    have hmarg : ∀ l, marginal g₂ l = marginal g l +
        ε*((if l = j then 1 else 0) - (if l = i then 1 else 0)) := by
      intro l
      rw [show marginal g₂ l = _ from swap_marginal g₁ b.1 b.2 h j ε hhb hjb l,
        show marginal g₁ l = _ from swap_marginal g a.1 a.2 i h ε hia hha l]
      ring
    have hd := discrepancy_transfer hij hε.le hei hej hmarg
    have hc₁ := swap_cost base g a.1 a.2 i h ε hε.le
    have hc₂ := swap_cost base g₁ b.1 b.2 h j ε hε.le
    change cost base g₁ ≤ cost base g + 2*ε at hc₁
    change cost base g₂ ≤ cost base g₁ + 2*ε at hc₂
    have hm := hmin g₂ hg₂
    change cost base g + 10*discrepancy f g ≤ cost base g₂ + 10*discrepancy f g₂ at hm
    rw [hd] at hm
    linarith

/-- A finite kernel repairs all coordinate means while keeping each actual
state's prescribed total, even when the total is correlated with the old vector. -/
theorem repair (μ : Ω → ℝ) (r : Ω → ℕ) (base : Ω → Finset ι) (f : ι → ℝ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (hbase : ∀ ω, (base ω).card = r ω)
    (s : ℕ) (hr : ∀ ω, r ω = s ∨ r ω = s+1)
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1)
    (hsum : ∑ i, f i = ∑ ω, μ ω * (r ω : ℝ)) :
    ∃ g : Joint Ω ι, admissible μ r g ∧ (∀ i, marginal g i = f i) ∧
      cost base g ≤ 10 * discrepancy f (initial μ base) := by
  obtain ⟨g,hg,hmin⟩ := minimizer_exists μ r base f hμ hbase
  have hexact := minimizer_exact μ r base f hμsum s hr hf hsum g hg hmin
  refine ⟨g,hg,hexact,?_⟩
  have hm := hmin (initial μ base) (initial_admissible μ r base hμ hbase)
  simpa [objective, discrepancy, hexact, initial_cost] using hm

end UniformKServer.BalancedRepair


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BalancedStar
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.BalancedStar
open UniformKServer.BalancedRepair
open scoped symmDiff
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]

def imbalance (I : Input Ω ι) : ℝ :=
  ∑ ω, I.μ ω * |(I.N ω : ℝ) - ∑ i, (I.X ω i : ℝ)|

noncomputable def jointCost (I : Input Ω ι) (g : Joint Ω ι) : ℝ :=
  ∑ q, g q * ∑ i, |(realized I.b q.2 i : ℝ) - (I.X q.1 i : ℝ)|

noncomputable def clippedSet (b : ι → ℝ) (X : ι → ℤ) : Finset ι :=
  Finset.univ.filter (fun i => ⌊b i⌋ < clip (b i) (X i))
noncomputable def slots (b : ι → ℝ) (N : ℤ) : ℕ := (N - lowerSum b).toNat

omit [DecidableEq ι] in
theorem clippedSet_subset (b : ι → ℝ) (X : ι → ℤ) : clippedSet b X ⊆ upperSet b := by
  intro i hi
  simp only [clippedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [upperSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hi.trans_le (balanced_bounds (clip_balanced (b i) (X i))).2

theorem represented_clip (b : ι → ℝ) (X : ι → ℤ) (i : ι) :
    realized b (clippedSet b X) i = clip (b i) (X i) := by
  have hb := balanced_bounds (clip_balanced (b i) (X i))
  have hc := Int.ceil_le_floor_add_one (b i)
  simp only [realized, clippedSet, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> omega

theorem subset_balanced (b : ι → ℝ) {A : Finset ι} (hA : A ⊆ upperSet b) (i : ι) :
    Balanced (b i) (realized b A i) := by
  unfold realized
  by_cases hi : i ∈ A
  · rw [ite_eq_left hi]
    right
    have h := hA hi
    simp only [upperSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
    have hc := Int.ceil_le_floor_add_one (b i)
    omega
  · exact Or.inl (by simp [hi])

omit [DecidableEq ι] in
theorem lowerSum_le_floor (b : ι → ℝ) : lowerSum b ≤ ⌊∑ i, b i⌋ := by
  apply Int.le_floor.mpr
  simp only [lowerSum, Int.cast_sum]
  exact Finset.sum_le_sum fun i _ => Int.floor_le (b i)

theorem slots_spec (b : ι → ℝ) (N : ℤ) (hN : Balanced (∑ i, b i) N) :
    (slots b N : ℤ) = N - lowerSum b ∧ slots b N ≤ (upperSet b).card := by
  have hbounds := balanced_bounds hN
  have hlo := lowerSum_le_floor b
  have hhi := ceil_le_sum b
  rw [ceil_sum] at hhi
  have hn : 0 ≤ N - lowerSum b := by omega
  constructor
  · exact Int.toNat_of_nonneg hn
  · dsimp [slots]
    omega

omit [DecidableEq ι] in
theorem slots_two (b : ι → ℝ) (N : ℤ) (hN : Balanced (∑ i, b i) N) :
    slots b N = (⌊∑ i, b i⌋ - lowerSum b).toNat ∨
      slots b N = (⌊∑ i, b i⌋ - lowerSum b).toNat + 1 := by
  have hbounds := balanced_bounds hN
  have hlo := lowerSum_le_floor b
  have hc := Int.ceil_le_floor_add_one (∑ i, b i)
  dsimp [slots]
  omega

theorem realized_distance (b : ι → ℝ) (A B : Finset ι) :
    (∑ i, |(realized b A i : ℝ) - (realized b B i : ℝ)|) = ((A ∆ B).card : ℝ) := by
  have he : ∀ i, |(realized b A i : ℝ) - (realized b B i : ℝ)| =
      if i ∈ A ∆ B then (1 : ℝ) else 0 := by
    intro i
    by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;>
      simp [realized, Finset.mem_symmDiff, ha, hb]
  simp [he]

theorem preliminary_exists (b : ι → ℝ) (X : ι → ℤ) (N : ℤ)
    (hN : Balanced (∑ i, b i) N) :
    ∃ A : Finset ι, A ⊆ upperSet b ∧ A.card = slots b N ∧
      (∑ i, |(realized b A i : ℝ) - (clip (b i) (X i) : ℝ)|) =
        |(N : ℝ) - ∑ i, (clip (b i) (X i) : ℝ)| := by
  obtain ⟨A,hA,hcard,hd⟩ := choose_subset_close (upperSet b) (clippedSet b X) (slots b N)
    (clippedSet_subset b X) (slots_spec b N hN).2
  refine ⟨A,hA,hcard,?_⟩
  simp_rw [← represented_clip b X]
  rw [realized_distance, hd, ← Int.cast_sum, sum_realized, Int.cast_add, Int.cast_natCast]
  have hc : (slots b N : ℝ) = (N : ℝ) - (lowerSum b : ℝ) := by
    exact_mod_cast (slots_spec b N hN).1
  rw [hc]
  congr 1
  ring

noncomputable def preliminary (I : Input Ω ι) (ω : Ω) : Finset ι :=
  (preliminary_exists I.b (I.X ω) (I.N ω) (I.N_balanced ω)).choose

omit [DecidableEq Ω] in
theorem preliminary_spec (I : Input Ω ι) (ω : Ω) :
    preliminary I ω ⊆ upperSet I.b ∧ (preliminary I ω).card = slots I.b (I.N ω) ∧
      (∑ i, |(realized I.b (preliminary I ω) i : ℝ) - (clip (I.b i) (I.X ω i) : ℝ)|) =
        |(I.N ω : ℝ) - ∑ i, (clip (I.b i) (I.X ω i) : ℝ)| :=
  (preliminary_exists I.b (I.X ω) (I.N ω) (I.N_balanced ω)).choose_spec


omit [DecidableEq Ω] [DecidableEq ι] in
theorem weighted_abs_le (I : Input Ω ι) (x : Ω → ℝ) :
    |∑ ω, I.μ ω * x ω| ≤ ∑ ω, I.μ ω * |x ω| := by
  calc
    _ ≤ ∑ ω, |I.μ ω * x ω| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp_rw [abs_mul, abs_of_nonneg (I.nonneg _)]

noncomputable def preliminaryCost (I : Input Ω ι) : ℝ :=
  ∑ ω, I.μ ω * ∑ i, |(realized I.b (preliminary I ω) i : ℝ) - (I.X ω i : ℝ)|

omit [DecidableEq Ω] in
theorem preliminaryCost_le (I : Input Ω ι) :
    preliminaryCost I ≤ 2*T I + imbalance I := by
  have hp (ω : Ω) :
      (∑ i, |(realized I.b (preliminary I ω) i : ℝ) - (I.X ω i : ℝ)|) ≤
        2*(∑ i, |(clip (I.b i) (I.X ω i) : ℝ) - (I.X ω i : ℝ)|) +
        |(I.N ω : ℝ) - ∑ i, (I.X ω i : ℝ)| := by
    have htri := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      abs_sub_le (realized I.b (preliminary I ω) i : ℝ)
        (clip (I.b i) (I.X ω i) : ℝ) (I.X ω i : ℝ)
    rw [Finset.sum_add_distrib, (preliminary_spec I ω).2.2] at htri
    have hsum := abs_sum_sub_le (fun i => (I.X ω i : ℝ))
      (fun i => (clip (I.b i) (I.X ω i) : ℝ))
    simp_rw [abs_sub_comm (I.X ω _ : ℝ)] at hsum
    have ht := abs_sub_le (I.N ω : ℝ) (∑ i, (I.X ω i : ℝ))
      (∑ i, (clip (I.b i) (I.X ω i) : ℝ))
    linarith
  calc
    preliminaryCost I ≤ ∑ ω, I.μ ω *
        (2*(∑ i, |(clip (I.b i) (I.X ω i) : ℝ) - (I.X ω i : ℝ)|) +
          |(I.N ω : ℝ) - ∑ i, (I.X ω i : ℝ)|) :=
      Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hp ω) (I.nonneg ω)
    _ = 2*clipCost I + imbalance I := by
      simp only [clipCost, imbalance, mul_add, Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _; ring
    _ ≤ 2*T I + imbalance I := by linarith [clipCost_le I]

omit [DecidableEq Ω] in
theorem initial_marginal (I : Input Ω ι) (i : ι) :
    marginal (BalancedRepair.initial I.μ (preliminary I)) i =
      ∑ ω, I.μ ω * (if i ∈ preliminary I ω then 1 else 0) := by
  simp only [marginal, Fintype.sum_prod_type, BalancedRepair.initial]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.sum_eq_single (preliminary I ω)]
  · simp only [ite_true, if_true]
  · intro A _ hA; simp [hA]
  · simp

omit [DecidableEq Ω] in
theorem initial_realized_mean (I : Input Ω ι) (i : ι) :
    (∑ ω, I.μ ω * (realized I.b (preliminary I ω) i : ℝ)) =
      (⌊I.b i⌋ : ℝ) + marginal (BalancedRepair.initial I.μ (preliminary I)) i := by
  simp only [realized, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero,
    mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, I.total, one_mul, initial_marginal]

omit [DecidableEq Ω] in
theorem discrepancy_le (I : Input Ω ι) :
    discrepancy (fraction I.b) (BalancedRepair.initial I.μ (preliminary I)) ≤ preliminaryCost I + T I := by
  have hp (i : ι) :
      |marginal (BalancedRepair.initial I.μ (preliminary I)) i - fraction I.b i| ≤
        (∑ ω, I.μ ω * |(realized I.b (preliminary I ω) i : ℝ) - (I.X ω i : ℝ)|) +
        |I.a i-I.b i| := by
    have hm : marginal (BalancedRepair.initial I.μ (preliminary I)) i - fraction I.b i =
        (∑ ω, I.μ ω * ((realized I.b (preliminary I ω) i : ℝ) - (I.X ω i : ℝ))) +
        (I.a i-I.b i) := by
      rw [Finset.sum_congr rfl (fun ω _ => mul_sub _ _ _), Finset.sum_sub_distrib,
        initial_realized_mean, I.X_mean]
      dsimp only [fraction, Int.fract] <;> ring
    rw [hm]
    exact (abs_add_le _ _).trans (add_le_add (weighted_abs_le I _) le_rfl)
  calc
    _ ≤ ∑ i, ((∑ ω, I.μ ω *
        |(realized I.b (preliminary I ω) i : ℝ) - (I.X ω i : ℝ)|) + |I.a i-I.b i|) :=
      Finset.sum_le_sum fun i _ => hp i
    _ = preliminaryCost I + T I := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp [preliminaryCost, T, Finset.mul_sum]

omit [DecidableEq Ω] in
theorem slots_mean (I : Input Ω ι) :
    (∑ ω, I.μ ω * (slots I.b (I.N ω) : ℝ)) = ∑ i, fraction I.b i := by
  have hs (ω : Ω) : (slots I.b (I.N ω) : ℝ) =
      (I.N ω : ℝ) - (lowerSum I.b : ℝ) := by
    exact_mod_cast (slots_spec I.b (I.N ω) (I.N_balanced ω)).1
  simp only [hs, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, I.total, one_mul, I.N_mean]
  simp only [fraction, lowerSum, Int.cast_sum, Finset.sum_sub_distrib]

omit [DecidableEq Ω] in
theorem marginal_realized_mean (I : Input Ω ι) (g : Joint Ω ι)
    (hg : ∑ q, g q = 1) (i : ι) :
    (∑ q, g q * (realized I.b q.2 i : ℝ)) = (⌊I.b i⌋ : ℝ) + marginal g i := by
  simp only [realized, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero,
    mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hg, one_mul]
  rfl

omit [DecidableEq Ω] in
theorem support_subset (I : Input Ω ι) (g : Joint Ω ι)
    (hg : ∀ q, 0 ≤ g q) (hm : ∀ i, marginal g i = fraction I.b i)
    (q : Ω × Finset ι) (hq : 0 < g q) : q.2 ⊆ upperSet I.b := by
  intro i hi
  simp only [upperSet, Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra hn
  have he : ⌊I.b i⌋ = ⌈I.b i⌉ := le_antisymm (Int.floor_le_ceil _) (by omega)
  have hf : fraction I.b i = 0 := by
    have hl := Int.floor_le (I.b i)
    have hu := Int.le_ceil (I.b i)
    rw [← he] at hu
    dsimp only [fraction, Int.fract] <;> linarith
  have hle : g q ≤ marginal g i := by
    calc
      g q = g q * (if i ∈ q.2 then 1 else 0) := by simp [hi]
      _ ≤ marginal g i := Finset.single_le_sum (f := fun z => g z * if i ∈ z.2 then 1 else 0)
        (fun z _ => mul_nonneg (hg z) (by split_ifs <;> norm_num)) (Finset.mem_univ q)
  rw [hm, hf] at hle
  linarith

omit [DecidableEq Ω] in
theorem cost_transfer (I : Input Ω ι) (g : Joint Ω ι)
    (hg : admissible I.μ (slots I.b ∘ I.N) g) :
    jointCost I g ≤ cost (preliminary I) g + preliminaryCost I := by
  have hp (q : Ω × Finset ι) :
      (∑ i, |(realized I.b q.2 i : ℝ) - (I.X q.1 i : ℝ)|) ≤
        hamming (preliminary I) q +
        ∑ i, |(realized I.b (preliminary I q.1) i : ℝ) - (I.X q.1 i : ℝ)| := by
    have ht := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      abs_sub_le (realized I.b q.2 i : ℝ) (realized I.b (preliminary I q.1) i : ℝ)
        (I.X q.1 i : ℝ)
    rwa [Finset.sum_add_distrib, realized_distance] at ht
  calc
    _ ≤ ∑ q, g q * (hamming (preliminary I) q +
        ∑ i, |(realized I.b (preliminary I q.1) i : ℝ) - (I.X q.1 i : ℝ)|) :=
      Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hp q) (hg.1 q)
    _ = cost (preliminary I) g + preliminaryCost I := by
      simp only [mul_add, Finset.sum_add_distrib, cost]
      congr 1
      rw [Fintype.sum_prod_type]
      simp only [← Finset.sum_mul, hg.2.1]
      rfl

theorem rounding_star (I : Input Ω ι) :
    (∀ ω, ∃ A, Valid I ω A) ∧
    ∃ g : Joint Ω ι, (∀ q, 0 ≤ g q) ∧
      (∀ ω, ∑ A : Finset ι, g (ω,A) = I.μ ω) ∧
      (∀ q, 0 < g q → Valid I q.1 q.2) ∧
      (∀ i, ∑ q, g q * (realized I.b q.2 i : ℝ) = I.b i) ∧
      jointCost I g ≤ 32*T I + 11*imbalance I := by
  have hv (ω : Ω) (A : Finset ι) (hA : A ⊆ upperSet I.b)
      (hc : A.card = slots I.b (I.N ω)) : Valid I ω A := by
    refine ⟨subset_balanced I.b hA, ?_⟩
    rw [sum_realized, hc, (slots_spec I.b (I.N ω) (I.N_balanced ω)).1]
    ring
  constructor
  · intro ω
    exact ⟨preliminary I ω, hv ω _ (preliminary_spec I ω).1 (preliminary_spec I ω).2.1⟩
  obtain ⟨g,hg,hm,hcost⟩ := repair I.μ (slots I.b ∘ I.N) (preliminary I) (fraction I.b)
    I.nonneg I.total (fun ω => (preliminary_spec I ω).2.1)
    (⌊∑ i, I.b i⌋ - lowerSum I.b).toNat
    (fun ω => slots_two I.b (I.N ω) (I.N_balanced ω))
    (fraction_bounds I.b) (slots_mean I).symm
  refine ⟨g,hg.1,hg.2.1,?_,?_,?_⟩
  · intro q hq
    apply hv q.1 q.2 (support_subset I g hg.1 hm q hq)
    by_contra hn
    have hz := hg.2.2 q hn
    linarith
  · intro i
    rw [marginal_realized_mean I g (by rw [total_mass hg, I.total]), hm]
    dsimp only [fraction, Int.fract] <;> ring
  · have h₁ := cost_transfer I g hg
    have h₂ := discrepancy_le I
    have h₃ := preliminaryCost_le I
    linarith

end UniformKServer.BalancedStar

/-! One conditional update of the complete finite tree rounding process.
The arbitrary supported old law includes every correlation produced by earlier
ancestor roundings; no conditional independence is imposed. -/

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

abbrev Selector (n k : ℕ) := List (Fin n) → Configuration n k → Fin n → Fin k

def StronglyLazy {n k : ℕ} (T : Selector n k) : Prop :=
  ∀ (w : List (Fin n)) (c : Configuration n k) (r : Fin n),
    (∃ j, c j = r) → c (T w c r) = r

def keptTail {n k : ℕ} (M : ℕ) : FilterState n k → List (Fin n) → List (Fin n)
  | _, [] => []
  | f, r :: w => if ∀ e ∈ f.live, Covers e r then keptTail M f w
    else r :: keptTail M (UniformKServer.step M f r) w

def nextEntry {n k : ℕ} (e : Entry n k) (r : Fin n) (j : Fin k) : Entry n k :=
  ⟨serve e.position r j, e.moves + if e.position j = r then 0 else 1⟩

/-- The literal one-epoch virtual routine. The deterministic filter continues
independently through fallback; its discarded final state has no effect on
service. Its full kept word is provided separately by `keptTail`. -/
def trace {n k : ℕ} (hk : 0 < k) (M : ℕ) (T : Selector n k) :
    FilterState n k → Entry n k → Finset (Fin n) → List (Fin n) → History n k
  | _, _, _, [] => []
  | f, e, seen, r :: w =>
      let seen' := bookStep (k:=k) seen r
      if ∀ z ∈ f.live, Covers z r then
        let j := Fallback.pick hk (Fallback.coverers e.position r)
        (r,j) :: trace hk M T f e seen' w
      else
        let j := T f.kept e.position r
        let e' := nextEntry e r j
        (r,j) :: if e'.moves ≤ M then
          trace hk M T (UniformKServer.step M f r) e' seen' w
        else Fallback.rawTrace hk ⟨⟨e'.position,∅⟩,seen',0⟩ w



end UniformKServer.EpochShadow

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochExpectation
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.EpochExpectation
open EpochShadow

abbrev BState (n k : ℕ) := List (Fin n) × Configuration n k

def next {n k : ℕ} (s : BState n k) (r : Fin n) (j : Fin k) : BState n k :=
  (s.1 ++ [r], serve s.2 r j)

def charge {n k : ℕ} (d : RationalMetric n) (s : BState n k) (r : Fin n) (j : Fin k) : ℝ :=
  d.distance (s.2 j) r

def selector {n k b : ℕ} (N : BState n k → Fin n → Fin k → ℕ)
    (hN : ∀ s r, ∑ j, N s r j = 2^b) (coins : ℕ → Fin b → Bool) : Selector n k :=
  fun p c r => BitSampling.row (N (p,c) r) (hN (p,c) r) (coins p.length)

/-- Exact finite product of the fresh bits assigned to the deterministic kept
word. Extra shadow bits after a switch are analytical only. -/
def epochTrace {n k b : ℕ} (hk : 0 < k) (M : ℕ)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀ s r, ∑ j, N s r j = 2^b)
    (u : Configuration n k) (raw : List (Fin n))
    (coins : Fin (keptTail M (initial u) raw).length → Fin b → Bool) : History n k :=
  trace hk M (selector N hN (extend coins)) (initial u) ⟨u,0⟩ ∅ raw

end UniformKServer.EpochExpectation



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochControl
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                   
section

namespace UniformKServer.EpochControl
open EpochShadow

structure State (n k : ℕ) where
  filter : FilterState n k
  virtual : Entry n k
  marked : Finset (Fin k)
  seen : Finset (Fin n)
  fallback : Bool

def asRaw {n k : ℕ} (s : State n k) : Fallback.RawState n k :=
  ⟨⟨s.virtual.position,s.marked⟩,s.seen,0⟩

def initial {n k : ℕ} (u : Configuration n k) : State n k :=
  ⟨UniformKServer.initial u,⟨u,0⟩,∅,∅,false⟩

def label {n k : ℕ} (hk : 0 < k) (T : Selector n k) (s : State n k) (r : Fin n) : Fin k :=
  if s.fallback then Fallback.rawChoice hk (asRaw s) r
  else if ∀z ∈ s.filter.live,Covers z r then
    Fallback.pick hk (Fallback.coverers s.virtual.position r)
  else T s.filter.kept s.virtual.position r

def step {n k : ℕ} (hk : 0 < k) (M : ℕ) (T : Selector n k)
    (s : State n k) (r : Fin n) : State n k :=
  if s.fallback then
    let raw := Fallback.rawStep hk (asRaw s) r
    ⟨UniformKServer.step M s.filter r,⟨raw.marking.position,s.virtual.moves⟩,
      raw.marking.marked,raw.seen,true⟩
  else if ∀z ∈ s.filter.live,Covers z r then
    {s with seen := bookStep (k:=k) s.seen r}
  else
    let e := nextEntry s.virtual r (T s.filter.kept s.virtual.position r)
    ⟨UniformKServer.step M s.filter r,e,∅,bookStep (k:=k) s.seen r,decide (M<e.moves)⟩

def runTrace {n k : ℕ} (hk : 0 < k) (M : ℕ) (T : Selector n k) :
    State n k → List (Fin n) → History n k
  | _,[] => []
  | s,r::w => (r,label hk T s r)::runTrace hk M T (step hk M T s r) w

end UniformKServer.EpochControl

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochFinite
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawFallback.nextSeen_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                  
section

namespace UniformKServer.EpochControl
open EpochShadow

def Bounded {n k : ℕ} (M : ℕ) (s : State n k) : Prop :=
  Good M (horizon k M) s.filter ∧ s.virtual.moves ≤ M+1 ∧
    (s.fallback=false → s.virtual.moves ≤ M)

theorem bounded_initial {n k : ℕ} (M : ℕ) (u : Configuration n k) :
    Bounded M (initial u) := by
  have hf := runFilter_good M u []
  rw [treeBudget_eq_horizon] at hf
  exact ⟨hf,Nat.zero_le _,fun _ => Nat.zero_le _⟩

theorem bounded_step {n k : ℕ} (hk : 0 < k) (M : ℕ) (T : Selector n k)
    (s : State n k) (r : Fin n) (hb : Bounded M s) :
    Bounded M (step hk M T s r) := by
  have hf := step_good M (horizon k M) s.filter r hb.1
  by_cases ht : s.fallback=true
  · simp only [step,ht,ite_true, if_true]
    exact ⟨hf,hb.2.1,by simp⟩
  · have ht' : s.fallback=false := Bool.eq_false_iff.mpr ht
    by_cases hc : ∀z ∈ s.filter.live,Covers z r
    · simp only [step,ht',Bool.false_eq_true,ite_false, if_false,ite_eq_left hc]
      exact ⟨hb.1,hb.2.1,fun _ => hb.2.2 ht'⟩
    · have hv := hb.2.2 ht'
      have hm : (nextEntry s.virtual r (T s.filter.kept s.virtual.position r)).moves ≤ M+1 := by
        simp only [nextEntry]
        split_ifs <;> omega
      simp only [step,ht',Bool.false_eq_true,ite_false, if_false,ite_eq_right hc]
      refine ⟨hf,hm,?_⟩
      intro hh
      have hnot : ¬ M < (nextEntry s.virtual r (T s.filter.kept s.virtual.position r)).moves :=
        of_decide_eq_false hh
      change (nextEntry s.virtual r (T s.filter.kept s.virtual.position r)).moves ≤ M
      omega

abbrev Packed (n k M : ℕ) :=
  BList (Configuration n k × Fin (M+1)) (horizon k M) ×
  BList (Fin n) (horizon k M) × Fin (horizon k M+1) ×
  (Configuration n k × Fin (M+2)) × Finset (Fin k) × Finset (Fin n) × Bool

def pack {n k M : ℕ} (s : {s : State n k // Bounded M s}) : Packed n k M :=
  let hb := s.property
  (⟨s.val.filter.live.attach.map (fun e =>
        (e.val.position,⟨e.val.moves,Nat.lt_succ_of_le (hb.1.1 e.val e.property)⟩)),by
      simp only [List.length_map,List.length_attach]
      exact (length_le_mass M s.val.filter.live).trans (by have hh := hb.1.2.1; omega)⟩,
   ⟨s.val.filter.kept,by have hh := hb.1.2.1; omega⟩,
   ⟨s.val.filter.created,by have hh := hb.1.2.2; omega⟩,
   (s.val.virtual.position,⟨s.val.virtual.moves,by have hh := hb.2.1; omega⟩),
   s.val.marked,s.val.seen,s.val.fallback)

def unpack {n k M : ℕ} (p : Packed n k M) : State n k :=
  ⟨⟨p.1.val.map (fun e => ⟨e.1,e.2.val⟩),p.2.1.val,p.2.2.1.val⟩,
    ⟨p.2.2.2.1.1,p.2.2.2.1.2.val⟩,p.2.2.2.2.1,p.2.2.2.2.2.1,p.2.2.2.2.2.2⟩

/-- A bounded-state one-epoch transducer. Neither its state bound nor its
transition function contains a raw word or a request horizon. -/
def boundedStep {n k : ℕ} (hk : 0 < k) (M : ℕ) (T : Selector n k)
    (s : {s : State n k // Bounded M s}) (r : Fin n) : {s : State n k // Bounded M s} :=
  ⟨step hk M T s.val r,bounded_step hk M T s.val r s.property⟩

end UniformKServer.EpochControl

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawExpansion
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

namespace UniformKServer.RawExpansion
open RawArithmetic RawWords RawTable RawPath RawTyped
abbrev State (n k : ℕ) := List (Fin n) × Configuration n k

end UniformKServer.RawExpansion

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawFilter
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.RawFilter
open RawTyped
def entry {n k : ℕ} (e : UniformKServer.Entry n k) : E := (config e.position,e.moves)
def state {n k : ℕ} (s : UniformKServer.FilterState n k) : F :=
  (s.live.map entry,requests s.kept,s.created)

@[simp] theorem cover_entry {n k : ℕ} (e : UniformKServer.Entry n k) (r : Fin n) :
    cover (entry e) r.val=decide (Covers e r) := by
  apply Bool.eq_iff_iff.mpr
  simp [cover,entry,config,List.any_eq_true,Covers,Fin.ext_iff]

@[simp] theorem allCover_state {n k : ℕ} (s : UniformKServer.FilterState n k) (r : Fin n) :
    allCover (state s) r.val=decide (∀e∈s.live,Covers e r) := by
  apply Bool.eq_iff_iff.mpr
  simp [allCover,state,List.all_eq_true]

@[simp] theorem births_entry {n k : ℕ} (M : ℕ) (r : Fin n) (e : UniformKServer.Entry n k) :
    births k M r.val (entry e)=UniformKServer.births M r e := by
  rw [births,cover_entry]
  simp only [Bool.cond_decide]
  rfl

section Primitive
open Primrec
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_cover (e : α→E) (r : α→ℕ) (he : Primrec e) (hr : Primrec r) :
    Primrec (fun x=>cover (e x) (r x)) := by
  simp only [cover, List.any_eq_not_all_not]
  fun_prop
@[fun_prop] theorem primitive_allCover (s : α→F) (r : α→ℕ) (hs : Primrec s) (hr : Primrec r) :
    Primrec (fun x=>allCover (s x) (r x)) := by unfold allCover;fun_prop
@[fun_prop] theorem primitive_expand (k M r : α→ℕ) (e : α→E)
    (hk : Primrec k) (hM : Primrec M) (hr : Primrec r) (he : Primrec e) :
    Primrec (fun x=>expand (k x) (M x) (r x) (e x)) := by
  unfold expand
  apply Primrec.cond
  · fun_prop
  · fun_prop
  · exact Primrec.cond (by fun_prop) (by fun_prop) (by fun_prop)
@[fun_prop] theorem primitive_births (k M r : α→ℕ) (e : α→E)
    (hk : Primrec k) (hM : Primrec M) (hr : Primrec r) (he : Primrec e) :
    Primrec (fun x=>births (k x) (M x) (r x) (e x)) := by
  unfold births
  apply Primrec.cond
  · fun_prop
  · fun_prop
  · exact Primrec.cond (by fun_prop) hk (by fun_prop)
@[fun_prop] theorem primitive_step (k M : α→ℕ) (s : α→F) (r : α→ℕ)
    (hk : Primrec k) (hM : Primrec M) (hs : Primrec s) (hr : Primrec r) :
    Primrec (fun x=>step (k x) (M x) (s x) (r x)) := by
  unfold step
  exact Primrec.cond (by fun_prop) hs (by fun_prop)
end Primitive
end UniformKServer.RawFilter

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawControl
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                 
section

namespace UniformKServer.RawControl
open RawTyped RawMarks
abbrev S := RawFilter.F×RawFilter.E×List Bool×List Bool×Bool

def state {n k : ℕ} (s : EpochControl.State n k) : S :=
  (RawFilter.state s.filter,RawFilter.entry s.virtual,bits s.marked,bits s.seen,s.fallback)
def initial (n k : ℕ) (u : List ℕ) : S :=
  (([(u,0)],[],1),(u,0),empty k,empty n,false)
def trackingLabel (k : ℕ) (T coins : List ℕ) (s : S) (r : ℕ) : ℕ :=
  RawRowSelect.choose k T s.1.2.1 s.2.1.1 r (coins.getD s.1.2.1.length 0)
def label (k : ℕ) (T coins : List ℕ) (s : S) (r : ℕ) : ℕ :=
  bif s.2.2.2.2 then RawFallback.label k s.2.1.1 s.2.2.1 s.2.2.2.1 r
  else bif RawFilter.allCover s.1 r then pick (covers s.2.1.1 r)
  else trackingLabel k T coins s r

def nextEntry (e : RawFilter.E) (r j : ℕ) : RawFilter.E :=
  (e.1.set j r,e.2+(bif decide (e.1.getD j 0=r) then 0 else 1))

def step (n k M : ℕ) (T coins : List ℕ) (s : S) (r : ℕ) : S :=
  bif s.2.2.2.2 then
    let j:=RawFallback.label k s.2.1.1 s.2.2.1 s.2.2.2.1 r
    (RawFilter.step k M s.1 r,(s.2.1.1.set j r,s.2.1.2),
      RawFallback.nextMarked k s.2.2.1 s.2.2.2.1 r j,
      RawFallback.nextSeen n k s.2.2.2.1 r,true)
  else bif RawFilter.allCover s.1 r then
    (s.1,s.2.1,s.2.2.1,RawFallback.nextSeen n k s.2.2.2.1 r,s.2.2.2.2)
  else
    let e:=nextEntry s.2.1 r (trackingLabel k T coins s r)
    (RawFilter.step k M s.1 r,e,empty k,RawFallback.nextSeen n k s.2.2.2.1 r,decide (M<e.2))

@[simp] theorem initial_state {n k : ℕ} (u : Configuration n k) :
    initial n k (config u)=state (EpochControl.initial u) := by
  simp only [initial,empty_bits,state,EpochControl.initial,RawFilter.state,
    UniformKServer.initial,List.map_cons,List.map_nil,RawFilter.entry,requests]

section Primitive
open Primrec
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_initial (n k : α→ℕ) (u : α→List ℕ)
    (hn : Primrec n) (hk : Primrec k) (hu : Primrec u) :
    Primrec (fun x=>initial (n x) (k x) (u x)) := by unfold initial;fun_prop
@[fun_prop] theorem primitive_tracking (k : α→ℕ) (T coins : α→List ℕ) (s : α→S) (r : α→ℕ)
    (hk : Primrec k) (hT : Primrec T) (hcoins : Primrec coins) (hs : Primrec s) (hr : Primrec r) :
    Primrec (fun x=>trackingLabel (k x) (T x) (coins x) (s x) (r x)) := by unfold trackingLabel;fun_prop
@[fun_prop] theorem primitive_label (k : α→ℕ) (T coins : α→List ℕ) (s : α→S) (r : α→ℕ)
    (hk : Primrec k) (hT : Primrec T) (hcoins : Primrec coins) (hs : Primrec s) (hr : Primrec r) :
    Primrec (fun x=>label (k x) (T x) (coins x) (s x) (r x)) := by
  unfold label
  exact Primrec.cond (by fun_prop) (by fun_prop)
    (Primrec.cond (by fun_prop) (by fun_prop) (by fun_prop))
@[fun_prop] theorem primitive_nextEntry (e : α→RawFilter.E) (r j : α→ℕ)
    (he : Primrec e) (hr : Primrec r) (hj : Primrec j) :
    Primrec (fun x=>nextEntry (e x) (r x) (j x)) := by
  unfold nextEntry
  exact Primrec.pair (by fun_prop) (Primrec.nat_add.comp (by fun_prop)
    (Primrec.cond (by fun_prop) (by fun_prop) (by fun_prop)))
@[fun_prop] theorem primitive_step (n k M : α→ℕ) (T coins : α→List ℕ) (s : α→S) (r : α→ℕ)
    (hn : Primrec n) (hk : Primrec k) (hM : Primrec M) (hT : Primrec T)
    (hcoins : Primrec coins) (hs : Primrec s) (hr : Primrec r) :
    Primrec (fun x=>step (n x) (k x) (M x) (T x) (coins x) (s x) (r x)) := by
  unfold step
  exact Primrec.cond (by fun_prop) (by fun_prop)
    (Primrec.cond (by fun_prop) (by fun_prop) (by fun_prop))
end Primitive
end UniformKServer.RawControl

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TapeController
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                     
section

namespace UniformKServer.TapeController
open EpochShadow EpochExpectation

structure State (n k M R b : ℕ) where
  localState : {s : EpochControl.State n k // EpochControl.Bounded M s}
  completed : Fin R
  tape : Option (Tape k M b)

def initial {n k M R b : ℕ} (hR : 0<R) (u : Configuration n k) : State n k M R b :=
  ⟨⟨EpochControl.initial u,EpochControl.bounded_initial M u⟩,⟨0,hR⟩,none⟩

def boundary {n k M R b : ℕ} (s : State n k M R b) (r : Fin n) : Prop :=
  k<(insert r s.localState.val.seen).card ∧ s.completed.val+1=R

instance instDecidableBoundary {n k M R b : ℕ} (s : State n k M R b) (r : Fin n) : Decidable (boundary s r) :=
  inferInstanceAs (Decidable (_ ∧ _))

def chosen {n k M R b : ℕ} (s : State n k M R b) (fresh : Tape k M b) : Tape k M b :=
  s.tape.getD fresh

end UniformKServer.TapeController

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawGlobal
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.RawGlobal
open RawTyped
abbrev S := RawControl.S×ℕ×Option (List ℕ)

def state {n k M R b : ℕ} (s : TapeController.State n k M R b) : S :=
  (RawControl.state s.localState.val,s.completed.val,s.tape.map RawTape.tape)
def initial (n k : ℕ) : S := (RawControl.initial n k (List.range k),0,none)
def chosen (s : S) (fresh : List ℕ) : List ℕ := s.2.2.getD fresh
def boundary (k R : ℕ) (s : S) (r : ℕ) : Bool :=
  RawFallback.endpoint k s.1.2.2.2.1 r && decide (s.2.1+1=R)
def label (k : ℕ) (T : List ℕ) (s : S) (r : ℕ) (fresh : List ℕ) : ℕ :=
  RawControl.label k T (chosen s fresh) s.1 r

def step (n k M R : ℕ) (T : List ℕ) (s : S) (r : ℕ) (fresh : List ℕ) : S :=
  bif boundary k R s r then initial n k else
    (RawControl.step n k M T (chosen s fresh) s.1 r,
      s.2.1+(bif RawFallback.endpoint k s.1.2.2.2.1 r then 1 else 0),some (chosen s fresh))

@[simp] theorem initial_state {n k M R b : ℕ} (hkn : k≤n) (hR : 0<R) :
    initial n k=state (TapeController.initial (M:=M) (b:=b) hR
      (fun j : Fin k=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩)) := by
  unfold initial state TapeController.initial
  have hu : config (fun j : Fin k => (⟨j.val,lt_of_lt_of_le j.isLt hkn⟩ : Fin n))=List.range k := by
    simpa only [config] using (RawExpansion.range_eq_ofFn k).symm
  rw [←hu,RawControl.initial_state]
  rfl

@[simp] theorem chosen_state {n k M R b : ℕ} (s : TapeController.State n k M R b)
    (fresh : TapeController.Tape k M b) :
    chosen (state s) (RawTape.tape fresh)=RawTape.tape (TapeController.chosen s fresh) := by
  simp only [chosen,state,TapeController.chosen]
  cases s.tape <;> rfl

@[simp] theorem boundary_state {n k M R b : ℕ} (s : TapeController.State n k M R b) (r : Fin n) :
    boundary k R (state s) r.val=decide (TapeController.boundary s r) := by
  apply Bool.eq_iff_iff.mpr
  simp only [boundary,Bool.and_eq_true,decide_eq_true_eq]
  change (RawFallback.endpoint k (RawMarks.bits s.localState.val.seen) r.val=true ∧
    s.completed.val+1=R)↔TapeController.boundary s r
  rw [RawFallback.endpoint_bits]
  simp only [decide_eq_true_eq,TapeController.boundary]

section Primitive
open Primrec
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_initial (n k : α→ℕ) (hn : Primrec n) (hk : Primrec k) :
    Primrec (fun x=>initial (n x) (k x)) := by unfold initial;fun_prop
@[fun_prop] theorem primitive_chosen (s : α→S) (f : α→List ℕ) (hs : Primrec s) (hf : Primrec f) :
    Primrec (fun x=>chosen (s x) (f x)) := by
  unfold chosen
  exact Primrec.option_getD.comp (by fun_prop) hf
@[fun_prop] theorem primitive_boundary (k R : α→ℕ) (s : α→S) (r : α→ℕ)
    (hk : Primrec k) (hR : Primrec R) (hs : Primrec s) (hr : Primrec r) :
    Primrec (fun x=>boundary (k x) (R x) (s x) (r x)) := by unfold boundary;fun_prop
@[fun_prop] theorem primitive_label (k : α→ℕ) (T : α→List ℕ) (s : α→S) (r : α→ℕ) (f : α→List ℕ)
    (hk : Primrec k) (hT : Primrec T) (hs : Primrec s) (hr : Primrec r) (hf : Primrec f) :
    Primrec (fun x=>label (k x) (T x) (s x) (r x) (f x)) := by unfold label;fun_prop
@[fun_prop] theorem primitive_step (n k M R : α→ℕ) (T : α→List ℕ) (s : α→S) (r : α→ℕ) (f : α→List ℕ)
    (hn : Primrec n) (hk : Primrec k) (hM : Primrec M) (hR : Primrec R)
    (hT : Primrec T) (hs : Primrec s) (hr : Primrec r) (hf : Primrec f) :
    Primrec (fun x=>step (n x) (k x) (M x) (R x) (T x) (s x) (r x) (f x)) := by
  unfold step
  apply Primrec.cond (by fun_prop) (by fun_prop)
  apply Primrec.pair (by fun_prop)
  apply Primrec.pair
  · exact Primrec.nat_add.comp (by fun_prop) (Primrec.cond (by fun_prop) (by fun_prop) (by fun_prop))
  · exact Primrec.option_some.comp (by fun_prop)
end Primitive
end UniformKServer.RawGlobal

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawProgram
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                 
section

namespace UniformKServer.RawProgram
open Primrec RawCertificate
attribute [fun_prop] RawBits.primitive_bits

abbrev Payload := ℕ×ℕ×Certificate×RawGlobal.S

def payload (n k : ℕ) (v : Certificate) (s : RawGlobal.S) : Payload := (n,k,v,s)
def initial (n k : ℕ) (v : Certificate) : Payload := payload n k v (RawGlobal.initial n k)
def unpack (a : ℕ) : Payload := (Encodable.decode a).getD default

def chosen (p : Payload) (r a : ℕ) : ℕ :=
  RawGlobal.label p.2.1 (table p.2.2.1) p.2.2.2 (request r)
    (fresh p.2.1 (cap p.2.2.1) (bits p.2.2.1) a)

def next (p : Payload) (r a : ℕ) : Payload :=
  payload p.1 p.2.1 p.2.2.1
    (RawGlobal.step p.1 p.2.1 (cap p.2.2.1) (restart p.2.2.1) (table p.2.2.1)
      p.2.2.2 (request r) (fresh p.2.1 (cap p.2.2.1) (bits p.2.2.1) a))

def randomCount (p : Payload) : ℕ := RawCertificate.horizon p.2.1 (cap p.2.2.1)*bits p.2.2.1

def run (v : List.Vector ℕ 3) : List.Vector ℕ 3 :=
  let p:=unpack (v.get 0)
  ⟨[chosen p (v.get 1) (v.get 2),2^randomCount p,
      Encodable.encode (next p (v.get 1) (v.get 2))],rfl⟩

section Primitive
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_unpack (a : α→ℕ) (ha : Primrec a) :
    Primrec (fun x=>unpack (a x)) :=
  Primrec.option_getD.comp (Primrec.decode.comp ha) (Primrec.const default)
@[fun_prop] theorem primitive_chosen (p : α→Payload) (r a : α→ℕ)
    (hp : Primrec p) (hr : Primrec r) (ha : Primrec a) :
    Primrec (fun x=>chosen (p x) (r x) (a x)) := by unfold chosen table cap bits;fun_prop
@[fun_prop] theorem primitive_next (p : α→Payload) (r a : α→ℕ)
    (hp : Primrec p) (hr : Primrec r) (ha : Primrec a) :
    Primrec (fun x=>next (p x) (r x) (a x)) := by unfold next payload table cap restart bits;fun_prop
@[fun_prop] theorem primitive_randomCount (p : α→Payload) (hp : Primrec p) :
    Primrec (fun x=>randomCount (p x)) := by unfold randomCount cap bits;fun_prop
 theorem primitive_run : Primrec run := by
  apply Primrec.vector_toList_iff.mp
  change Primrec (fun v : List.Vector ℕ 3=>
    [chosen (unpack (v.get 0)) (v.get 1) (v.get 2),2^randomCount (unpack (v.get 0)),
      Encodable.encode (next (unpack (v.get 0)) (v.get 1) (v.get 2))])
  fun_prop
end Primitive

@[simp] theorem unpack_encode (p : Payload) : unpack (Encodable.encode p)=p := by
  simp [unpack]

end UniformKServer.RawProgram

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BinaryTape
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                 
section

namespace UniformKServer.BinaryTape
open RawBinary

 def coins (k M b a : ℕ) : TapeController.Tape k M b :=
  fun i j=>(a.bits.drop (b*i.val)).getD j.val false

end UniformKServer.BinaryTape

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

/-- Domination by the old measure turns the mover's first moment into an
inner-ball mass lower bound, without a cardinality or aspect-ratio loss. -/
theorem inner_mass_half (r γ : ℝ) (hr : 0 < r) (hγ : 0 < γ)
    (μ ν : X → ℝ) (_hμ : ∀ y, 0 ≤ μ y) (hν : ∀ y, 0 ≤ ν y)
    (hν1 : ∑ y, ν y = 1) (hνμ : ∀ y, ν y ≤ μ y) (x : X)
    (he : 2*(∑ y, ν y*dist x y) ≤ γ*r) :
    1/2 ≤ ballMass r γ μ x := by
  have hp : 0 < γ*r := mul_pos hγ hr
  have hy : ∀ y, (γ*r)*ν y ≤ (γ*r)*(if dist x y ≤ γ*r then μ y else 0)+ν y*dist x y := by
    intro y
    by_cases hd : dist x y ≤ γ*r
    · rw [ite_eq_left hd]
      have hm := mul_le_mul_of_nonneg_left (hνμ y) hp.le
      have hn : 0 ≤ ν y*dist x y := mul_nonneg (hν y) dist_nonneg
      linarith
    · rw [ite_eq_right hd, mul_zero, zero_add]
      nlinarith [mul_le_mul_of_nonneg_left (le_of_not_ge hd) (hν y)]
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset X)) => hy y)
  rw [←Finset.mul_sum, hν1, mul_one, Finset.sum_add_distrib, ←Finset.mul_sum] at hsum
  change γ*r ≤ (γ*r)*ballMass r γ μ x + ∑ y, ν y*dist x y at hsum
  nlinarith


end
end UniformKServer.PilotCompact


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavySchedule
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! The literal deterministic heavy-center recursion of companion §07.
The update decision depends only on the request, posterior, and old centers,
not on any radius, lifetime, allocation, or rounding variable. -/
noncomputable section
namespace UniformKServer.HeavySchedule
open Finset
open scoped Classical
variable {X : Type*} [MetricSpace X]

theorem update_separated (r : ℝ) (H : Finset X) (x : X) (hs : Separated r H) :
    Separated r (HeavyPilot.updateCenters r H x) := by
  intro a ha b hb hne
  simp only [HeavyPilot.updateCenters,mem_insert,mem_filter] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact (hne rfl).elim
    · exact hb.2
  · rcases hb with rfl | hb
    · simpa only [dist_comm] using ha.2
    · exact hs a ha.1 b hb.1 hne

theorem step_separated (r : ℝ) (h : Prop) (H : Finset X) (x : X) (hs : Separated r H) :
    Separated r (step r h H x) := by
  unfold step
  split_ifs
  · exact update_separated r H x hs
  · exact hs

theorem centers_separated (r : ℝ) (h : ℕ → Prop) (x : ℕ → X) (t : ℕ) :
    Separated r (centers r h x t) := by
  induction t with
  | zero => intro a ha; exact (notMem_empty a ha).elim
  | succ t ih => exact step_separated r (h t) _ _ ih

end UniformKServer.HeavySchedule

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

theorem chooseSlot_not_mem (M : ℕ) (S : Finset (Slot M)) (hS : S.card<4*M+4) :
    chooseSlot M S∉S := by
  have he : ∃ a : Slot M, a∉S := by
    by_contra! h
    have hs : S=univ := eq_univ_of_forall h
    have hc : S.card=4*M+4 := by rw [hs,card_univ,Fintype.card_fin]
    omega
  exact by rw [chooseSlot,dite_eq_left he]; exact Classical.choose_spec he

theorem previous_card (M : ℕ) (S : ℕ → Finset I) (birth : ℕ → Option I)
    (hS : ∀ t, (S t).card≤M) (t : ℕ) : (run M S birth t).previous.card≤M := by
  cases t with
  | zero => simp [run]
  | succ t => exact (card_image_le).trans (hS t)

theorem chosen_fresh (M : ℕ) (S : ℕ → Finset I) (birth : ℕ → Option I)
    (hS : ∀ t, (S t).card≤M) (t : ℕ) :
    chooseSlot M ((run M S birth t).previous ∪ (S t).image (run M S birth t).label)∉
      (run M S birth t).previous ∪ (S t).image (run M S birth t).label := by
  apply chooseSlot_not_mem
  have hc := card_union_le (run M S birth t).previous ((S t).image (run M S birth t).label)
  have hp := previous_card M S birth hS t
  have hi := (card_image_le (f:=(run M S birth t).label) (s:=S t)).trans (hS t)
  omega

theorem label_new_fresh (M : ℕ) (S : ℕ → Finset I) (birth : ℕ → Option I)
    (hS : ∀ t, (S t).card≤M) (t : ℕ) (n : I) (hb : birth t=some n) :
    (run M S birth (t+1)).label n∉
      (run M S birth t).previous ∪ (S t).image (run M S birth t).label := by
  simpa only [run,step,hb,Function.update_self] using chosen_fresh M S birth hS t

end UniformKServer.CooldownLabels

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ChronologicalBound
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

noncomputable section
namespace UniformKServer.ChronologicalRoster
open Finset
open scoped Classical
variable {I X : Type*} [LinearOrder I] [Fintype X] [MetricSpace X]

theorem global_young_count (S : Finset I) (c : I → X) (r : ℝ) (hr : 0 ≤ r) (A : ℕ) :
    (young S c r A).card ≤ Fintype.card X*A := by
  have hf (x : X) : ((young S c r A).filter (fun i => c i=x)).card ≤ A := by
    apply local_age_count S _ c r A
    · intro i hi
      exact (mem_filter.mp (mem_filter.mp hi).1).1
    · intro i hi
      exact (mem_filter.mp (mem_filter.mp hi).1).2
    · intro i hi j hj
      rw [(mem_filter.mp hi).2,(mem_filter.mp hj).2,dist_self]
      positivity
  have hc := sum_le_sum (s:=univ) (fun x _ => hf x)
  rw [←card_eq_sum_card_fiberwise (f:=c) (s:=young S c r A) (t:=univ) (fun _ _ => mem_univ _)] at hc
  simpa using hc

omit [Fintype X] in
theorem age_mono {S T : Finset I} (hST : S ⊆ T) (c : I → X) (r : ℝ) (i : I) :
    age S c r i ≤ age T c r i := by
  apply card_le_card
  intro j hj
  obtain ⟨hj,hj'⟩ := mem_filter.mp hj
  exact mem_filter.mpr ⟨hST hj,hj'⟩

omit [Fintype X] in
theorem young_insert_subset (S : Finset I) (c : I → X) (r : ℝ) (A : ℕ) (n : I) :
    young (insert n S) c r A ⊆ insert n (young S c r A) := by
  intro i hi
  obtain ⟨hi,ha⟩ := mem_filter.mp hi
  rcases mem_insert.mp hi with he|hi
  · exact mem_insert.mpr (Or.inl he)
  · exact mem_insert_of_mem (mem_filter.mpr ⟨hi,lt_of_le_of_lt (age_mono (subset_insert n S) c r i) ha⟩)

end UniformKServer.ChronologicalRoster

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FirstStructure
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Precedence across heavy balls, chronological tiers, and singleton fallback.
A qualifying prefix covers the request, so fallback does not contribute to the
short-edge separation estimate. -/
noncomputable section
namespace UniformKServer.FirstStructure
open scoped Classical
variable {I J : Type*}

def key (is : List I) (f : I → Option J) (z : J) : J := (first is f).getD z

theorem first_append (is js : List I) (f : I → Option J) :
    first (is++js) f=(first is f).or (first js f) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append,first,ih]
    cases f i <;> rfl

theorem first_eq_some (is : List I) (f : I → Option J)
    (h : ∃ i∈is, (f i).isSome=true) : ∃ j, first is f=some j := by
  induction is with
  | nil => simp at h
  | cons i is ih =>
    cases he : f i with
    | some j => exact ⟨j,by simp only [first,he,Option.some_or]⟩
    | none =>
      have ht : ∃ j∈is, (f j).isSome=true := by
        obtain ⟨j,hj,hf⟩ := h
        rcases List.mem_cons.mp hj with rfl|hj
        · simp only [he,Option.isSome_none,Bool.false_eq_true] at hf
        · exact ⟨j,hj,hf⟩
      obtain ⟨j,hj⟩ := ih ht
      exact ⟨j,by simp only [first,he,Option.none_or,hj]⟩

theorem equal_covered_prefix (is js : List I) (f g : I → Option J) (x y : J)
    (h : ∀ i∈is, f i=g i) (hc : ∃ i∈is, (f i).isSome=true) :
    key (is++js) f x=key (is++js) g y := by
  have he : first is f=first is g := by
    clear hc
    induction is with
    | nil => rfl
    | cons i is ih =>
      rw [first,first,h i (by simp),ih (fun j hj => h j (by simp [hj]))]
  obtain ⟨j,hj⟩ := first_eq_some is f hc
  simp only [key,first_append,hj,←he,Option.some_or,Option.getD_some]

theorem covered_prefix_bound (is js : List I) (f g : I → Option J) (x y : J)
    (hc : ∃ i∈is, (f i).isSome=true) :
    indicator (key (is++js) f x) (key (is++js) g y)≤
      (is.map (fun i => indicator (f i) (g i))).sum := by
  by_cases he : ∀ i∈is, f i=g i
  · rw [equal_covered_prefix is js f g x y he hc]
    simp only [indicator]
    exact List.sum_nonneg (fun a ha => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
      exact (indicator_bounds _ _).1)
  · push Not at he
    obtain ⟨i,hi,hne⟩ := he
    apply (indicator_bounds _ _).2.trans
    have hm : indicator (f i) (g i) ∈ is.map (fun j => indicator (f j) (g j)) := List.mem_map.mpr ⟨i,hi,rfl⟩
    have hs := List.single_le_sum (l:=is.map (fun j => indicator (f j) (g j)))
      (fun a ha => by
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
        exact (indicator_bounds _ _).1) (indicator (f i) (g i)) hm
    simpa only [indicator,ite_eq_right hne] using hs

end UniformKServer.FirstStructure

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyBirths
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

/-! Input-determined birth times for current heavy centers. Labels and radii may
be random, but their center's birth coordinate never depends on that randomness. -/
noncomputable section
namespace UniformKServer.HeavyProcess
open Finset HeavyRecords
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}

def births (r : ℝ) (h : ℕ → Prop) (x : ℕ → X) : ℕ → X → ℕ
  | 0 => fun _ => 0
  | t+1 => if HeavySchedule.trigger r (h t) (HeavySchedule.centers r h x t) (x t)
    then Function.update (births r h x t) (x t) t else births r h x t

theorem run_birth (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (R : ℕ → ℝ) (hR : ∀ t, R t ∈ Set.Icc (16*r) (20*r))
    (t : ℕ) : ∀ l ∈ (run a hr hΛ h x R hR t).present,
      births r h x t ((run a hr hΛ h x R hR t).center l)<t ∧
      (run a hr hΛ h x R hR t).radius l=R (births r h x t ((run a hr hΛ h x R hR t).center l)) := by
  induction t with
  | zero => simp [run,runPair,empty]
  | succ t ih =>
    intro l hl
    let S := run a hr hΛ h x R hR t
    let T := (runPair a hr hΛ h x R hR t).1
    have hc : centers S=HeavySchedule.centers r h x t := run_centers _ _ _ _ _ _ _ _
    change l ∈ (step S T hr hΛ (h t) (x t) (R t) (hR t)).present at hl
    change births r h x (t+1) ((step S T hr hΛ (h t) (x t) (R t) (hR t)).center l)<t+1 ∧
      (step S T hr hΛ (h t) (x t) (R t) (hR t)).radius l=
        R (births r h x (t+1) ((step S T hr hΛ (h t) (x t) (R t) (hR t)).center l))
    by_cases ht : HeavySchedule.trigger r (h t) (centers S) (x t)
    · have ht' : HeavySchedule.trigger r (h t) (HeavySchedule.centers r h x t) (x t) := hc ▸ ht
      simp only [step,ite_eq_left ht] at hl ⊢
      simp only [births,ite_eq_left ht']
      change l ∈ Insert.insert _ (survivors S (x t)) at hl
      rcases mem_insert.mp hl with he | hs
      · subst l
        simp only [HeavyRecords.insert,Function.update_self]
        exact ⟨Nat.lt_succ_self t,trivial⟩
      · have hn : l ≠ chosen S (x t) (R t) (fresh S T hr hΛ) := by
          intro he
          exact chosen_not_survivor S hr (x t) (R t) (hR t).2 _ (fresh_absent S T hr hΛ).1 (he ▸ hs)
        have hx : S.center l ≠ x t := by
          intro he
          have hd := (mem_filter.mp hs).2
          rw [he,dist_self] at hd
          linarith
        simp only [HeavyRecords.insert,Function.update_of_ne hn,Function.update_of_ne hx]
        have hi := ih l (mem_filter.mp hs).1
        exact ⟨hi.1.trans_le (Nat.le_succ t),hi.2⟩
    · have ht' : ¬HeavySchedule.trigger r (h t) (HeavySchedule.centers r h x t) (x t) := hc ▸ ht
      simp only [step,ite_eq_right ht] at hl ⊢
      simp only [births,ite_eq_right ht']
      have hi := ih l hl
      exact ⟨hi.1.trans_le (Nat.le_succ t),hi.2⟩

end UniformKServer.HeavyProcess

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
omit [Fintype X] in
theorem signature_eq (r : ℝ) (ω : Sample (X:=X) r) :
    ω.val=FiniteThreshold.threshold (probability r) (scalar r ω) :=
  (Classical.choose_spec ω.property).2

omit [Fintype X] in
theorem covers (r : ℝ) (hr : 0 < r) (ω : Sample (X:=X) r) (c p : X) :
    ω.val (c,p)=true ↔ dist c p ≤ radius r ω := by
  rw [signature_eq]
  simp only [FiniteThreshold.threshold,decide_eq_true_eq,probability,le_max_iff,le_min_iff]
  have hu := scalar_mem r ω
  rw [or_iff_right (not_le_of_gt hu.1),and_iff_right hu.2,le_div_iff₀ (by positivity : 0 < 4*r)]
  dsimp [radius]
  constructor <;> intro h <;> linarith

omit [Fintype X] in
theorem probability_lipschitz (r : ℝ) (hr : 0 < r) (c x y : X) :
    |probability r (c,x)-probability r (c,y)| ≤ dist x y/(4*r) := by
  have hmax := abs_max_sub_max_le_max (0:ℝ) (min 1 ((20*r-dist c x)/(4*r)))
    0 (min 1 ((20*r-dist c y)/(4*r)))
  have hmin := abs_min_sub_min_le_max (1:ℝ) ((20*r-dist c x)/(4*r))
    1 ((20*r-dist c y)/(4*r))
  rw [sub_self,abs_zero,max_eq_right (abs_nonneg (min 1 ((20*r-dist c x)/(4*r))-min 1 ((20*r-dist c y)/(4*r))))] at hmax
  rw [sub_self,abs_zero,max_eq_right (abs_nonneg ((20*r-dist c x)/(4*r)-(20*r-dist c y)/(4*r)))] at hmin
  have hd : |dist c y-dist c x| ≤ dist x y := by
    simpa only [dist_comm] using abs_dist_sub_le y x c
  calc
    _ ≤ |(20*r-dist c x)/(4*r)-(20*r-dist c y)/(4*r)| := hmax.trans hmin
    _ = |dist c y-dist c x|/(4*r) := by
      rw [←sub_div,show (20*r-dist c x)-(20*r-dist c y)=dist c y-dist c x by ring,
        abs_div,abs_of_pos (by positivity : 0 < 4*r)]
    _ ≤ _ := div_le_div_of_nonneg_right hd (by positivity)

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
omit [Fintype X] [Fintype Λ] in
theorem near_boundary (S : State X Λ r) (hr : 0 ≤ r) (x y : X) (hd : dist x y < r)
    (l : Λ) (hl : l ∈ S.present) (hm : ¬(covers S l x ↔ covers S l y)) :
    dist (S.center l) x ≤ 21*r := by
  by_cases hx : covers S l x
  · linarith [hx.2,(S.radius_bounds l hl).2]
  · have hy : covers S l y := by tauto
    have ht := dist_triangle (S.center l) y x
    rw [dist_comm y x] at ht
    linarith [hy.2,(S.radius_bounds l hl).2]

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
local instance tapeFinDecEq_r896544_1 (N : ℕ) : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
theorem at_radius (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (N : ℕ) (hN : 0<N) (t : ℕ) (ht : t≤N)
    (ω : Fin N → HeavyRadius.Sample (X:=X) r) (l : Λ) (hl : l∈(slice a hr hΛ h x N ω t).present) :
    (slice a hr hΛ h x N ω t).radius l=HeavyRadius.radius r
      (ω (if hc : births r h x t ((slice a hr hΛ h x N ω t).center l)<N
        then ⟨births r h x t ((slice a hr hΛ h x N ω t).center l),hc⟩ else ⟨0,hN⟩)) := by
  have hb := run_birth a hr hΛ h x (radiusStream r N ω) (radiusStream_bounds r hr N ω) t l hl
  have hn : births r h x t ((slice a hr hΛ h x N ω t).center l)<N := lt_of_lt_of_le hb.1 ht
  have hrad : (slice a hr hΛ h x N ω t).radius l=radiusStream r N ω
      (births r h x t ((slice a hr hΛ h x N ω t).center l)) := hb.2
  rw [hrad]
  simp only [radiusStream,dite_eq_left hn]

end UniformKServer.HeavyProcess

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CausalLevel
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

/-! Causal dependence of the actual level keys and all their occupied anchors. -/
noncomputable section
namespace UniformKServer.LevelMap.Data
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

lemma key_inputs (D : LevelMap.Data X N H) (c d : Fin N → X)
    (h v : Fin N → Prop) (q u : Fin H → Fin N → Prop) (t : ℕ)
    (hc : ∀ i : Fin N, i.val<t → c i=d i) (hh : ∀ i : Fin N, i.val<t → (h i ↔ v i))
    (hq : ∀ a (i : Fin N), i.val<t → (q a i ↔ u a i))
    (is : List (Fin H)) (ω : LevelMap.Tape D) (p : X) :
    (D.inputs c h q).key is ω t p=(D.inputs d v u).key is ω t p := by
  unfold key heavyKey
  rw [heavy_inputs D c d h v q u t hc hh ω.1]
  have ht : (fun i => (D.inputs c h q).tierKey ω t i p)=
      (fun i => (D.inputs d v u).tierKey ω t i p) := by
    funext i
    unfold tierKey inputs
    rw [CausalRosters.labeled_inputs D.r (D.K i) (q i) (u i) c d t (hq i) hc]
  rw [ht]
  rfl

end UniformKServer.LevelMap.Data

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ComputedInstance
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace UniformKServer.ComputedInstance
open EffectiveLP EpochShadow EpochPartition

variable {n k : ℕ}

def canonical (hkn : k ≤ n) : Config n k :=
  ⟨Fin.castLE hkn, Fin.castLE_injective hkn⟩

end UniformKServer.ComputedInstance

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelHeavy
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

local instance heavyPairDecEq_r896544_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance heavyIndexDecEq_r896544_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance heavyTierDecEq_r896544_1 : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
theorem heavy_same_key (D : Data X N H) (is : List (Fin H)) (n : Fin N) (hh : D.heavy n)
    (ω : Tape D) (p : X) (hp : dist (D.center n) p ≤ 8*D.r) :
    D.key is ω (n.val+1) (D.center n)=D.key is ω (n.val+1) p := by
  obtain ⟨l,hx,hp'⟩ := heavy_agreement D n hh ω p hp
  simp only [key,hx,hp',Option.some_or,Option.getD_some]

end UniformKServer.LevelMap.Data

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

def component (D : Data X N H) (ω : Tape D) (t : ℕ) (p : X) : Option (Fin H) → Option (Label D)
  | none => D.heavyKey ω t p
  | some i => D.tierKey ω t i p

theorem first_components (D : Data X N H) (is : List (Fin H)) (ω : Tape D) (t : ℕ) (p : X) :
    first (is.map some) (D.component ω t p)=first is (fun i => D.tierKey ω t i p) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [List.map_cons,first,component,ih]

local instance indexDecEq_r896544_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
attribute [local instance] OAI.UniformKServer.LevelMap.Data.tierDecEq
attribute [local instance] OAI.UniformKServer.LevelMap.Data.pairDecEq
theorem priority_bound (D : Data X N H) (is js : List (Fin H)) (ω : Tape D) (t : ℕ) (p q : X)
    (hc : ∃ i∈is, (D.tierKey ω t i p).isSome=true) :
    indicator (D.key (is++js) ω t p) (D.key (is++js) ω t q)≤
      indicator (D.heavyKey ω t p) (D.heavyKey ω t q)+
        (is.map (fun i => indicator (D.tierKey ω t i p) (D.tierKey ω t i q))).sum := by
  have hcov : ∃ i∈none::is.map some, ((D.component ω t p) i).isSome=true := by
    obtain ⟨i,hi,hf⟩ := hc
    exact ⟨some i,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,hi,rfl⟩),hf⟩
  have hb := covered_prefix_bound (none::is.map some) (js.map some)
    (D.component ω t p) (D.component ω t q) (Sum.inr (Sum.inr p)) (Sum.inr (Sum.inr q)) hcov
  have hmap : (is.map some).map (fun i => indicator (D.component ω t p i) (D.component ω t q i))=
      is.map (fun i => indicator (D.tierKey ω t i p) (D.tierKey ω t i q)) := by
    simp only [List.map_map,Function.comp_def,component]
  simpa only [List.cons_append,←List.map_append,FirstStructure.key,first,component,
    first_components,List.map_cons,List.sum_cons,hmap,Data.key,List.map_map,Function.comp_def] using hb

theorem expect_list_sum {Ω I : Type*} [Fintype Ω] (P : Law Ω) (is : List I) (f : I → Ω → ℝ) :
    P.expect (fun ω => (is.map (fun i => f i ω)).sum)=(is.map (fun i => P.expect (f i))).sum := by
  induction is with
  | nil => simp only [List.map_nil,List.sum_nil,Law.expect_const]
  | cons i is ih => simp only [List.map_cons,List.sum_cons,Law.expect_add,ih]

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

theorem last_ge (L : ℝ) : L≤value (last L) := Nat.find_spec (unbounded L)

theorem before_last (L : ℝ) (i : ℕ) (hi : i<last L) : value i<L := by
  exact lt_of_not_ge (Nat.find_min (unbounded L) hi)

theorem last_mono (A B : ℝ) (hAB : A≤B) : last A≤last B := by
  exact Nat.find_min' (unbounded A) (hAB.trans (last_ge B))

theorem last_bound (L : ℝ) : value (last L)≤2*max 1 L := by
  cases he : last L with
  | zero => simp only [value,pow_zero] <;> linarith [le_max_left (1:ℝ) L]
  | succ i =>
    have hi := before_last L i (by omega)
    simp only [value,pow_succ] at hi ⊢
    linarith [le_max_right (1:ℝ) L]

theorem exponential_sum (n : ℕ) : (∑ i∈range n, Real.exp (-value i))≤2 := by
  apply le_trans (sum_le_sum (fun i _ => ?_)) (sum_geometric_two_le n)
  have hi : (i:ℝ)≤value i := by
    dsimp only [value]
    exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self) : i≤2^i)
  have hl : Real.log 2≤1 := by have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have harg : -(value i)≤-(i:ℝ)*Real.log 2 := by
    have hn : (0:ℝ)≤ i := Nat.cast_nonneg _
    nlinarith
  have he := Real.exp_le_exp.mpr harg
  rw [show -(i:ℝ)*Real.log 2=(i:ℝ)*(-Real.log 2) by ring,Real.exp_nat_mul] at he
  simpa only [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2),one_div] using he

end UniformKServer.DyadicTiers

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
local instance sepPairDecEq_r896544_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
def separation (I : Input X N) (n : Fin N) (p : X) : ℝ :=
  I.data.law.expect (fun ω => indicator (I.data.key I.order ω (n.val+1) (I.center n))
    (I.data.key I.order ω (n.val+1) p))

theorem separation_le_one (I : Input X N) (n : Fin N) (p : X) : I.separation n p ≤ 1 := by
  have h := I.data.law.expect_mono (fun ω => indicator (I.data.key I.order ω (n.val+1) (I.center n))
    (I.data.key I.order ω (n.val+1) p)) (fun _ => 1) (fun ω => by
    show indicator _ _ ≤ (1:ℝ)
    unfold indicator
    split_ifs <;> norm_num)
  simpa only [separation,Law.expect_const] using h

theorem heavy_zero (I : Input X N) (n : Fin N) (p : X) (hh : I.data.heavy n)
    (hp : dist (I.center n) p ≤ 8*I.r) : I.separation n p=0 := by
  unfold separation
  have he (ω : LevelMap.Tape I.data) := LevelMap.Data.heavy_same_key I.data I.order n hh ω p hp
  change ∀ ω, I.data.key I.order ω (n.val+1) (I.center n)=I.data.key I.order ω (n.val+1) p at he
  simp only [he,indicator,ite_true, if_true,Law.expect_const]

end UniformKServer.PartitionLevel.Input

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionCausal
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Filtration measurability of actual partition keys, anchors, and pilot
parameters, with a common initially sampled finite tape. -/
noncomputable section
namespace UniformKServer.ActualPartitions.Config
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem key_measurable (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω v : Ω) (t j : ℕ) (he : (D.filtration t).r ω v)
    (z : LevelMap.Tape ((A.input (N:=N) (J:=J) D hk ω).level j).data) (p : X) :
    ((A.input (N:=N) (J:=J) D hk ω).level j).data.key ((A.input (N:=N) (J:=J) D hk ω).level j).order z t p=
      ((A.input (N:=N) (J:=J) D hk v).level j).data.key ((A.input (N:=N) (J:=J) D hk v).level j).order z t p := by
  let I := ((A.input (N:=N) (J:=J) D hk ω).level j).data
  let V := ((A.input (N:=N) (J:=J) D hk v).level j).data
  exact LevelMap.Data.key_inputs I I.center V.center I.heavy V.heavy I.qualify V.qualify t
    (A.past_centers (J:=J) D hk ω v t he) (A.past_heavy (J:=J) D hk ω v t j he)
    (A.past_qualify (J:=J) D hk ω v t j he) _ z p

end UniformKServer.ActualPartitions.Config

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochAlphaPieces
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! Full-child formulas for the epoch primitives. They make genuinely
 changing active subtypes transparent and prove that a held coordinate has
 unchanged potential piece when A, mark and U are fixed. -/
noncomputable section
namespace UniformKServer.EpochAlphaPieces
open Finset UniformKServer.AdaptiveAlpha UniformKServer.AlphaParameterChanges
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem regular_piece (a : ι → ℝ) (A ell ct C : ℝ) (B v : ι → ℝ)
    (hs : DomainTransport.Supported (EpochParameters.active a) B) (i : EpochParameters.active a) :
    piece (EpochAlpha.regular a A ell ct C) B v i =
      LogPrimitive.primitive (Denominators.regular (SideParameters.height A (a i))) 0
        (C*ell) (∑ j, B j) ((1+ct*SideParameters.height A (a i)/ell)*B i) (v i) := by
  rw [piece_inside (EpochAlpha.regular a A ell ct C) B v i]
  change LogPrimitive.primitive _ _ _ (∑ j : EpochParameters.active a, B j) _ _ = _
  rw [DomainTransport.sum_restrict hs]
  rfl

theorem marked_piece (a : ι → ℝ) (A U ell ct C : ℝ) (o : EpochParameters.active a)
    (B v : ι → ℝ) (hs : DomainTransport.Supported (EpochParameters.active a) B)
    (i : EpochParameters.active a) :
    piece (EpochAlpha.marked a A U ell ct C o) B v i =
      LogPrimitive.primitive
        (fun x => if i.val=o.val then Denominators.marked (U/A) x
          else Denominators.regular (SideParameters.height A (a i)) x)
        (if i.val=o.val then 1 else 0) (C*ell) (∑ j, B j)
        ((1+ct*(if i.val=o.val then U/A else SideParameters.height A (a i))/ell)*B i) (v i) := by
  rw [piece_inside (EpochAlpha.marked a A U ell ct C o) B v i]
  unfold ProportionParameters.component EpochAlpha.marked
  dsimp only
  unfold AlphaTracker.markedG AlphaTracker.markedF
  rw [DomainTransport.sum_restrict hs]
  by_cases hi : i=o
  · subst i
    simp only [ite_true, if_true]
  · have hv : i.val ≠ o.val := fun h => hi (Subtype.ext h)
    simp only [ite_eq_right hi,ite_eq_right hv]

theorem regular_same (a b : ι → ℝ) (A ell ct C : ℝ) (B v : ι → ℝ)
    (ha : DomainTransport.Supported (EpochParameters.active a) B)
    (hb : DomainTransport.Supported (EpochParameters.active b) B)
    (i : ι) (hi : a i=b i) :
    piece (EpochAlpha.regular a A ell ct C) B v i=
      piece (EpochAlpha.regular b A ell ct C) B v i := by
  by_cases ha' : i ∈ EpochParameters.active a
  · have hb' : i ∈ EpochParameters.active b := EpochParameters.mem_active.mpr
      (by simpa only [←hi] using EpochParameters.mem_active.mp ha')
    rw [regular_piece a A ell ct C B v ha ⟨i,ha'⟩,
      regular_piece b A ell ct C B v hb ⟨i,hb'⟩]
    simp only [hi]
  · have hb' : i ∉ EpochParameters.active b := by
      simpa only [EpochParameters.mem_active,←hi] using ha'
    rw [piece_outside _ _ _ _ ha',piece_outside _ _ _ _ hb']

theorem marked_same (a b : ι → ℝ) (A U ell ct C : ℝ)
    (oa : EpochParameters.active a) (ob : EpochParameters.active b) (ho : oa.val=ob.val)
    (B v : ι → ℝ) (ha : DomainTransport.Supported (EpochParameters.active a) B)
    (hb : DomainTransport.Supported (EpochParameters.active b) B)
    (i : ι) (hi : a i=b i ∨ i=oa.val) :
    piece (EpochAlpha.marked a A U ell ct C oa) B v i=
      piece (EpochAlpha.marked b A U ell ct C ob) B v i := by
  have hactive : i ∈ EpochParameters.active a ↔ i ∈ EpochParameters.active b := by
    rcases hi with he | he
    · simp only [EpochParameters.mem_active,he]
    · subst i
      exact iff_of_true oa.property (by simpa only [ho] using ob.property)
  by_cases ha' : i ∈ EpochParameters.active a
  · have hb' := hactive.mp ha'
    rw [marked_piece a A U ell ct C oa B v ha ⟨i,ha'⟩,
      marked_piece b A U ell ct C ob B v hb ⟨i,hb'⟩]
    dsimp only
    rw [←ho]
    rcases hi with he | he
    · rw [he]
    · simp only [he,ite_true, if_true]
  · rw [piece_outside _ _ _ _ ha',piece_outside _ _ _ _ (mt hactive.mpr ha')]

end UniformKServer.EpochAlphaPieces

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochAlphaJump
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! The actual held-size epoch jump is charged to sparse size changes, a
 side-reference refresh, or a wholesale epoch. All primitives are evaluated at
 the common-core prepared state, including the zero-input boundary. -/
noncomputable section
namespace UniformKServer.EpochAlphaJump
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

 theorem regular {a b : ι → ℝ} {A ell ct C : ℝ}
    (hp : AdaptiveAlpha.valid (EpochAlpha.regular a A ell ct C))
    (hq : AdaptiveAlpha.valid (EpochAlpha.regular b A ell ct C))
    (B v : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hpa : DomainTransport.Supported (EpochParameters.active a) B)
    (hqa : DomainTransport.Supported (EpochParameters.active b) B)
    (hv : ∀ i, v i ∈ Set.Icc (0:ℝ) 1)
    (hf : ∀ i, (∑ j, B j)*v i ≤ 2*B i) :
    |AdaptiveAlpha.potential (EpochAlpha.regular b A ell ct C) B v-
      AdaptiveAlpha.potential (EpochAlpha.regular a A ell ct C) B v| ≤
      8*(C*ell)*(∑ i, if a i=b i then 0 else B i) := by
  have h := AlphaParameterChanges.regular_jump hp hq rfl rfl B v hB hpa hqa hv hf
    (fun i => a i ≠ b i) (fun i hi => EpochAlphaPieces.regular_same a b A ell ct C B v hpa hqa i (not_not.mp hi))
  simpa only [AdaptiveAlpha.scale,EpochAlpha.regular,ite_not,show 4*(C*ell+C*ell)=8*(C*ell) by ring] using h

 theorem marked {a b : ι → ℝ} {A U ell ct C : ℝ}
    (oa : EpochParameters.active a) (ob : EpochParameters.active b) (ho : oa.val=ob.val)
    (hp : AdaptiveAlpha.valid (EpochAlpha.marked a A U ell ct C oa))
    (hq : AdaptiveAlpha.valid (EpochAlpha.marked b A U ell ct C ob))
    (B v : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hpa : DomainTransport.Supported (EpochParameters.active a) B)
    (hqa : DomainTransport.Supported (EpochParameters.active b) B)
    (hv : ∀ i, v i ∈ Set.Icc (0:ℝ) 1)
    (hf : ∀ i, (∑ j, B j)*v i ≤ 2*B i) :
    |AdaptiveAlpha.potential (EpochAlpha.marked b A U ell ct C ob) B v-
      AdaptiveAlpha.potential (EpochAlpha.marked a A U ell ct C oa) B v| ≤
      8*(C*ell)*(∑ i, if a i=b i then 0 else B i) := by
  have h := AlphaParameterChanges.marked_sparse_jump hp hq oa ob (U/A) rfl rfl ho B v hB hpa hqa hv hf
    (fun i => a i ≠ b i ∧ i ≠ oa.val) (fun i hi => EpochAlphaPieces.marked_same a b A U ell ct C oa ob ho
      B v hpa hqa i (by tauto)) (by simp)
  have hm : (∑ i, if a i ≠ b i ∧ i ≠ oa.val then B i else 0) ≤
      ∑ i, if a i=b i then 0 else B i := by
    apply sum_le_sum
    intro i _
    split_ifs <;> simp_all
  have hc : 0 ≤ 8*(C*ell) := by
    have := AdaptiveAlpha.scale_nonneg hp
    change 0 ≤ C*ell at this
    positivity
  have h' := mul_le_mul_of_nonneg_left hm hc
  change |_-_| ≤ 4*(C*ell+C*ell)*_ at h
  nlinarith

 theorem scale_bound (a : ι → ℝ) (s : EpochGeometry.State ι) (U ell ct C : ℝ)
    (hc : 0 ≤ C*ell) : AlphaEmpty.scale (EpochAlphaSchedule.config a s U ell ct C) ≤ C*ell := by
  unfold EpochAlphaSchedule.config
  split
  · split
    · exact le_rfl
    · split
      · split_ifs <;> exact le_rfl
      · exact hc
  · exact hc

 theorem total_upper {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) : EpochGeometry.total a ≤ (101/100)*EpochGeometry.total s.base := by
  have ht := EpochGeometry.total_difference s.base a
  have hc := hs.2.2.2.trans hs.2.2.1
  have := (le_abs_self _).trans (ht.trans hc)
  linarith

 theorem reference_upper {a : ι → ℝ} {o : ι} {U : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hU : EpochParameters.sideReference a o U) :
    U ≤ 2*EpochGeometry.side o a := by
  have hu := (div_le_iff₀ (by norm_num : (0:ℝ)<1001/1000)).mp hU.2.1
  linarith [EpochParameters.side_nonneg ha o]

 theorem side_input {b B : ι → ℝ} (hb : ∀ i, B i ≤ 40*b i) (o : ι) :
    (∑ i, B i)-B o ≤ 40*EpochGeometry.side o b := by
  have h := sum_le_sum (s:=univ.erase o) (fun i _ => hb i)
  rw [←mul_sum,sum_erase_eq_sub (mem_univ o)] at h
  have he : (∑ i ∈ univ.erase o, b i)=EpochGeometry.side o b := by
    rw [EpochGeometry.side]
    simp_rw [show ∀ i : ι, (if i=o then (0:ℝ) else b i)=(if i≠o then b i else 0) by intro i; split_ifs <;> simp_all]
    rw [←sum_filter]
    apply sum_congr
    · ext i; simp
    · intro i _; rfl
  rwa [he] at h

 theorem marked_sized {a b B : ι → ℝ} {s : EpochGeometry.State ι} {U ell ct C : ℝ}
    (ha : ∀ i, 0 ≤ a i)
    (hb : EpochGeometry.total b ≤ (101/100)*EpochGeometry.total s.base)
    (oa : EpochParameters.active a)
    (hA : 0 < EpochGeometry.total s.base)
    (hU : EpochParameters.sideReference a oa U) (hct : ct/ell ≤ 1)
    (hp : AdaptiveAlpha.valid (EpochAlpha.marked a (EpochGeometry.total s.base) U ell ct C oa))
    (v : ι → ℝ) (hB : ∀ i, 0 ≤ B i) (hBb : ∀ i, B i ≤ 40*b i)
    (hs : DomainTransport.Supported (EpochParameters.active a) B)
    (hv : ∀ i, v i ∈ Set.Icc (0:ℝ) 1) (hsum : ∑ i, v i=1)
    (hf : ∀ i, (∑ j, B j)*v i ≤ 2*B i) :
    |AdaptiveAlpha.potential (EpochAlpha.marked a (EpochGeometry.total s.base) U ell ct C oa) B v| ≤
      (C*ell)*(520*EpochGeometry.side oa.val b+246*EpochGeometry.side oa.val a) := by
  have h := AlphaParameterChanges.marked_prepared hp oa (U/EpochGeometry.total s.base) rfl B v hB hs hv hsum hf
  have hsc : 0 ≤ C*ell := AdaptiveAlpha.scale_nonneg hp
  have hS : 0 ≤ ∑ i, B i := sum_nonneg fun i _ => hB i
  have hSb : (∑ i, B i) ≤ 41*EpochGeometry.total s.base := by
    have hh := sum_le_sum (s:=univ) (fun i _ => hBb i)
    rw [←mul_sum] at hh
    have ht := hb
    change _ ≤ 40*EpochGeometry.total b at hh
    nlinarith [hA.le]
  have huS : (U/EpochGeometry.total s.base)*(∑ i, B i) ≤ 82*EpochGeometry.side oa.val a := by
    have h1 := mul_le_mul_of_nonneg_left hSb (div_nonneg hU.1 hA.le)
    have he : U/EpochGeometry.total s.base*(41*EpochGeometry.total s.base)=41*U := by field_simp
    rw [he] at h1
    linarith [reference_upper ha hU]
  have hc := mul_le_mul_of_nonneg_right hct (mul_nonneg (div_nonneg hU.1 hA.le) hS)
  simp only [one_mul] at hc
  have hside := side_input hBb oa.val
  have h1 := mul_le_mul_of_nonneg_left hside hsc
  have h2 := mul_le_mul_of_nonneg_left (hc.trans huS) hsc
  change |AdaptiveAlpha.potential (EpochAlpha.marked a (EpochGeometry.total s.base) U ell ct C oa) B v| ≤
    13*(C*ell)*((∑ i, B i)-B oa)+3*(C*ell)*(ct/ell)*(U/EpochGeometry.total s.base)*(∑ i, B i) at h
  nlinarith

end UniformKServer.EpochAlphaJump

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochAlphaStatic
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! Parameter changes inside one actual held-vector epoch: sparse coordinates
when the held side reference is unchanged, side mass otherwise. -/
noncomputable section
namespace UniformKServer.EpochAlphaStatic
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem dominant_base {s r : EpochGeometry.State ι} (h : s.base=r.base) :
    EpochGeometry.dominant s=EpochGeometry.dominant r := by
  unfold EpochGeometry.dominant
  rw [h]

theorem config_regular {s : EpochGeometry.State ι} {a : ι → ℝ}
    (hn : (EpochParameters.active a).Nonempty) (ho : EpochGeometry.dominant s=none)
    (U ell ct C : ℝ) : EpochAlphaSchedule.config a s U ell ct C=
      some (EpochAlpha.regular a (EpochGeometry.total s.base) ell ct C) := by
  simp only [EpochAlphaSchedule.config,ite_eq_left hn,ho]

theorem config_marked {s : EpochGeometry.State ι} {a : ι → ℝ} {o : ι}
    (hi : o ∈ EpochParameters.active a) (ho : EpochGeometry.dominant s=some o)
    {U ell ct C : ℝ} (hU : U ≠ 0) : EpochAlphaSchedule.config a s U ell ct C=
      some (EpochAlpha.marked a (EpochGeometry.total s.base) U ell ct C ⟨o,hi⟩) := by
  have hn : (EpochParameters.active a).Nonempty := ⟨o,hi⟩
  simp only [EpochAlphaSchedule.config,ite_eq_left hn,ho,dite_eq_left hi,ite_eq_right hU]

theorem config_singleton {s : EpochGeometry.State ι} {a : ι → ℝ} {o : ι}
    (hi : o ∈ EpochParameters.active a) (ho : EpochGeometry.dominant s=some o)
    (ell ct C : ℝ) : EpochAlphaSchedule.config a s 0 ell ct C=
      some (EpochAlpha.singleton a ell ct C ⟨o,hi⟩) := by
  have hn : (EpochParameters.active a).Nonempty := ⟨o,hi⟩
  simp only [EpochAlphaSchedule.config,ite_eq_left hn,ho,dite_eq_left hi,ite_true, if_true]

theorem singleton_zero (a B v : ι → ℝ) (ell ct C : ℝ)
    (o : EpochParameters.active a) :
    AdaptiveAlpha.potential (EpochAlpha.singleton a ell ct C o) B v=0 :=
  AlphaParameterChanges.singleton_potential o rfl B v

theorem nonempty_of_input {a B : ι → ℝ}
    (hs : DomainTransport.Supported (EpochParameters.active a) B)
    (hS : 0 < ∑ i, B i) : (EpochParameters.active a).Nonempty := by
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  have hz : B=fun _ => 0 := by
    funext i
    exact hs i (by simp [he])
  simp only [hz,sum_const_zero,lt_self_iff_false] at hS

theorem marked_bound {a b B : ι → ℝ} {s : EpochGeometry.State ι}
    (ha : ∀ i, 0 ≤ a i) (hb : EpochGeometry.total b ≤ (101/100)*EpochGeometry.total s.base)
    {o : ι} (hi : o ∈ EpochParameters.active a) (ho : EpochGeometry.dominant s=some o)
    {U ell ct C : ℝ} (hU : EpochParameters.sideReference a o U) (hct : ct/ell ≤ 1)
    (hsc : 0 ≤ C*ell) (hp : AlphaEmpty.valid (EpochAlphaSchedule.config a s U ell ct C))
    (v : ι → ℝ) (hB : ∀ i, 0 ≤ B i) (hBb : ∀ i, B i ≤ 40*b i)
    (hs : DomainTransport.Supported (EpochParameters.active a) B)
    (hv : ∀ i, v i ∈ Set.Icc (0:ℝ) 1) (hsum : ∑ i, v i=1)
    (hf : ∀ i, (∑ j, B j)*v i ≤ 2*B i) :
    |AlphaEmpty.potential (EpochAlphaSchedule.config a s U ell ct C) B v| ≤
      (C*ell)*(520*EpochGeometry.side o b+246*EpochGeometry.side o a) := by
  by_cases hz : U=0
  · rw [hz,config_singleton hi ho]
    change |AdaptiveAlpha.potential (EpochAlpha.singleton a ell ct C ⟨o,hi⟩) B v| ≤ _
    rw [singleton_zero,abs_zero]
    have hbside : 0 ≤ EpochGeometry.side o b := by
      have h := EpochAlphaJump.side_input hBb o
      have h0 : 0 ≤ (∑ i, B i)-B o := by
        have hh := single_le_sum (s:=univ) (f:=B) (fun i _ => hB i) (mem_univ o)
        linarith
      linarith
    exact mul_nonneg hsc (by linarith [EpochParameters.side_nonneg ha o])
  · rw [config_marked hi ho hz] at hp ⊢
    exact EpochAlphaJump.marked_sized ha hb ⟨o,hi⟩ (EpochGeometry.dominant_spec ho).1
      hU hct hp v hB hBb hs hv hsum hf

theorem same_epoch {a b B : ι → ℝ} {s r : EpochGeometry.State ι}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hs : EpochGeometry.valid a s) (hr : EpochGeometry.valid b r) (he : s.base=r.base)
    {U V ell ct C : ℝ} (hsc : 0 ≤ C*ell) (hct : ct/ell ≤ 1)
    (hU : ∀ o, EpochGeometry.dominant s=some o → EpochParameters.sideReference a o U)
    (hV : ∀ o, EpochGeometry.dominant r=some o → EpochParameters.sideReference b o V)
    (hp : AlphaEmpty.valid (EpochAlphaSchedule.config a s U ell ct C))
    (hq : AlphaEmpty.valid (EpochAlphaSchedule.config b r V ell ct C))
    (v : ι → ℝ) (hS : 0 < ∑ i, B i) (hB : ∀ i, 0 ≤ B i)
    (hBb : ∀ i, B i ≤ 40*b i)
    (hpa : DomainTransport.Supported (EpochParameters.active a) B)
    (hqa : DomainTransport.Supported (EpochParameters.active b) B)
    (hv : ∀ i, v i ∈ Set.Icc (0:ℝ) 1) (hsum : ∑ i, v i=1)
    (hf : ∀ i, (∑ j, B j)*v i ≤ 2*B i) :
    |AlphaEmpty.potential (EpochAlphaSchedule.config b r V ell ct C) B v-
      AlphaEmpty.potential (EpochAlphaSchedule.config a s U ell ct C) B v| ≤
      8*(C*ell)*(∑ i, if a i=b i then 0 else B i)+
      (if U=V then 0 else match EpochGeometry.dominant s with
        | none => 0
        | some o => 1600*(C*ell)*(EpochGeometry.side o a+EpochGeometry.side o b)) := by
  have hna := nonempty_of_input hpa hS
  have hnb := nonempty_of_input hqa hS
  have hd := dominant_base he
  have hchg : 0 ≤ 8*(C*ell)*(∑ i, if a i=b i then 0 else B i) := by
    exact mul_nonneg (by positivity) (sum_nonneg fun i _ => by split_ifs; exact le_rfl; exact hB i)
  cases ho : EpochGeometry.dominant s with
  | none =>
    have ho' : EpochGeometry.dominant r=none := hd.symm.trans ho
    rw [config_regular hna ho] at hp
    rw [config_regular hnb ho'] at hq
    rw [config_regular hna ho,config_regular hnb ho']
    have h := EpochAlphaJump.regular hp (by simpa only [←he,AlphaEmpty.valid] using hq) B v hB hpa hqa hv hf
    simp only [AlphaEmpty.potential,←he,ho] at *
    split_ifs <;> simpa using h
  | some o =>
    have ho' : EpochGeometry.dominant r=some o := hd.symm.trans ho
    have hia := EpochAlphaSchedule.dominant_active hs ho
    have hib := EpochAlphaSchedule.dominant_active hr ho'
    by_cases hUV : U=V
    · rw [ite_eq_left hUV]
      rw [←hUV] at hq ⊢
      by_cases hz : U=0
      · rw [hz,config_singleton hia ho,config_singleton hib ho']
        simp only [AlphaEmpty.potential,singleton_zero,sub_self,abs_zero,add_zero]
        exact hchg
      · rw [config_marked hia ho hz] at hp
        rw [config_marked hib ho' hz] at hq
        rw [config_marked hia ho hz,config_marked hib ho' hz]
        have h := EpochAlphaJump.marked ⟨o,hia⟩ ⟨o,hib⟩ rfl hp
          (by simpa only [←he,AlphaEmpty.valid] using hq) B v hB hpa hqa hv hf
        simpa only [AlphaEmpty.potential,←he,add_zero] using h
    · simp only [ite_eq_right hUV]
      have ht := EpochAlphaJump.total_upper hr
      have hp' := marked_bound ha (by simpa only [he] using ht) hia ho (hU o ho) hct hsc hp
        v hB hBb hpa hv hsum hf
      have hq' := marked_bound hb ht hib ho' (hV o ho') hct hsc hq
        v hB hBb hqa hv hsum hf
      have hh := abs_sub (AlphaEmpty.potential (EpochAlphaSchedule.config b r V ell ct C) B v)
        (AlphaEmpty.potential (EpochAlphaSchedule.config a s U ell ct C) B v)
      have hsa := mul_nonneg hsc (EpochParameters.side_nonneg ha o)
      have hsb := mul_nonneg hsc (EpochParameters.side_nonneg hb o)
      nlinarith

end UniformKServer.EpochAlphaStatic

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

def active (a : ι → ℝ) (s : EpochGeometry.State ι) : Finset ι :=
  match EpochGeometry.dominant s with
  | none => ∅
  | some o => (EpochParameters.active a).erase o

def config (a : ι → ℝ) (s : EpochGeometry.State ι) (ell cw b : ℝ) : AdaptiveSide.Config ι where
  active := active a s
  A := EpochGeometry.total s.base
  a := fun i => a i
  ell := ell
  cw := cw
  b := b

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

omit [Fintype ι] in
theorem eta_range {p : AlphaEmpty.Config ι} (hp : AlphaEmpty.valid p) (i : ι) :
    AlphaEmpty.eta p i ∈ Set.Icc (0:ℝ) 1 := by
  cases p with
  | none => simp [AlphaEmpty.eta]
  | some p =>
    change AdaptiveAlpha.valid p at hp
    change DomainTransport.extend p.active (ProportionParameters.eta p.param) i ∈ Set.Icc (0:ℝ) 1
    unfold DomainTransport.extend
    split_ifs with hi
    · exact ⟨ProportionParameters.eta_nonneg hp.2 ⟨i,hi⟩, hp.2.2.2.2.1 ⟨i,hi⟩⟩
    · simp

theorem eta_regular {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) {U ell ct C : ℝ} (hl : 0 < ell) (hc : 0 ≤ ct)
    (i : ι) (hai : 0 < a i) (hi : EpochGeometry.dominant s ≠ some i) :
    AlphaEmpty.eta (EpochAlphaSchedule.config a s U ell ct C) i ≤
      ct*SideParameters.height (EpochGeometry.total s.base) (a i)/ell := by
  have hia := EpochParameters.mem_active.mpr hai
  have hn : (EpochParameters.active a).Nonempty := ⟨i,hia⟩
  have hh := EpochParameters.regular_height hs hai hi
  unfold EpochAlphaSchedule.config
  rw [ite_eq_left hn]
  cases ho : EpochGeometry.dominant s with
  | none =>
    simp [AlphaEmpty.eta,AdaptiveAlpha.eta,EpochAlpha.regular,DomainTransport.extend,
      ProportionParameters.eta,hia]
  | some o =>
    have hoa := EpochAlphaSchedule.dominant_active hs ho
    have hio : i ≠ o := by intro he; apply hi; simpa [he] using ho
    simp only [dite_eq_left hoa]
    split_ifs with hz
    · simp only [AlphaEmpty.eta,AdaptiveAlpha.eta,EpochAlpha.singleton,
        DomainTransport.extend,dite_eq_left hia,ProportionParameters.eta,mul_zero,zero_div]
      exact div_nonneg (mul_nonneg hc (by linarith)) hl.le
    · simp [AlphaEmpty.eta,AdaptiveAlpha.eta,EpochAlpha.marked,DomainTransport.extend,
        ProportionParameters.eta,hia,hio,Subtype.ext_iff]

theorem eta_dominant {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) (U ell ct C : ℝ) (o : ι)
    (ho : EpochGeometry.dominant s=some o) :
    AlphaEmpty.eta (EpochAlphaSchedule.config a s U ell ct C) o =
      ct*(U/EpochGeometry.total s.base)/ell := by
  have hoa := EpochAlphaSchedule.dominant_active hs ho
  have hn : (EpochParameters.active a).Nonempty := ⟨o,hoa⟩
  unfold EpochAlphaSchedule.config
  rw [ite_eq_left hn,ho]
  simp only [dite_eq_left hoa]
  split_ifs with hz
  · simp [AlphaEmpty.eta,AdaptiveAlpha.eta,EpochAlpha.singleton,DomainTransport.extend,
      ProportionParameters.eta,hoa,hz]
  · simp [AlphaEmpty.eta,AdaptiveAlpha.eta,EpochAlpha.marked,DomainTransport.extend,
      ProportionParameters.eta,hoa]

theorem theta_active {a : ι → ℝ} {s : EpochGeometry.State ι}
    (ell cw b : ℝ) {i : ι} (hi : i ∈ EpochSide.active a s) :
    AdaptiveSide.theta (EpochSide.config a s ell cw b) i =
      cw*SideParameters.height (EpochGeometry.total s.base) (a i)/ell := by
  simp [AdaptiveSide.theta,EpochSide.config,DomainTransport.extend,hi,SideParameters.slack]

theorem side_product {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) (ha : ∀ i, 0 ≤ a i)
    (ell cw b : ℝ) (o : ι) (ho : EpochGeometry.dominant s=some o) (i : ι) :
    AdaptiveSide.theta (EpochSide.config a s ell cw b) i *
        AdaptiveSide.offset (EpochSide.config a s ell cw b) i =
      cw/ell*((if i=o then 0 else a i)/EpochGeometry.total s.base) := by
  by_cases hi : i=o
  · subst i
    simp [AdaptiveSide.theta,AdaptiveSide.offset,EpochSide.config,EpochSide.active,ho,
      DomainTransport.extend]
  · by_cases hai : 0 < a i
    · have hmem : i ∈ EpochSide.active a s := by
        simp [EpochSide.active,ho,hi,EpochParameters.mem_active.mpr hai]
      have hreg : EpochGeometry.dominant s ≠ some i := by simpa [ho] using Ne.symm hi
      have hh : SideParameters.height (EpochGeometry.total s.base) (a i) ≠ 0 :=
        ne_of_gt (lt_of_lt_of_le zero_lt_one (EpochParameters.regular_height hs hai hreg))
      simp [AdaptiveSide.theta,AdaptiveSide.offset,EpochSide.config,DomainTransport.extend,
        hmem,SideParameters.slack,SideParameters.offset,hi]
      field_simp [hh]
    · have hz : a i=0 := le_antisymm (le_of_not_gt hai) (ha i)
      have hmem : i ∉ EpochSide.active a s := by
        simp [EpochSide.active,ho,EpochParameters.mem_active,hz]
      simp [AdaptiveSide.theta,AdaptiveSide.offset,EpochSide.config,DomainTransport.extend,
        hmem,hi,hz]

theorem side_sum {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) (ha : ∀ i, 0 ≤ a i)
    (ell cw b : ℝ) (o : ι) (ho : EpochGeometry.dominant s=some o) :
    (∑ i ∈ univ.erase o, AdaptiveSide.theta (EpochSide.config a s ell cw b) i *
        AdaptiveSide.offset (EpochSide.config a s ell cw b) i) =
      cw/ell*(EpochGeometry.side o a/EpochGeometry.total s.base) := by
  have he : (∑ i ∈ univ.erase o, if i=o then (0:ℝ) else a i) = EpochGeometry.side o a := by
    rw [EpochGeometry.side,←sum_erase_add _ _ (mem_univ o)]
    simp
  simp_rw [side_product hs ha ell cw b o ho]
  rw [←mul_sum,←sum_div,he]

end UniformKServer.EpochOutputParameters

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

def height (k : ℕ) : ℕ := DyadicTiers.last (Real.log k)+1

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochAlphaCharge
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! Actual epoch schedule charging of the prepared alpha jump. The zero core
mass branch is free; sparse refreshes and wholesale charges are distinct. -/
noncomputable section
namespace UniformKServer.EpochAlphaCharge
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

def sizeCharge (a b : ι → ℝ) : ℝ := ∑ i, AllocationSchedule.charge (a i) (b i)
def param (a : ℕ → ι → ℝ) (p : ℕ → Bool) (ell ct C : ℝ) (t : ℕ) : AlphaEmpty.Config ι :=
  EpochAlphaSchedule.config (a t) (EpochGeometry.schedule a p t) (SideReferenceSchedule.reference a p t) ell ct C

omit [Fintype ι] in
theorem eta_le {P : AlphaEmpty.Config ι} (hp : AlphaEmpty.valid P) (i : ι) : AlphaEmpty.eta P i ≤ 1 := by
  cases P with
  | none => norm_num [AlphaEmpty.eta]
  | some P =>
    change DomainTransport.extend P.active (ProportionParameters.eta P.param) i ≤ 1
    unfold DomainTransport.extend
    split_ifs with hi
    · exact hp.2.2.2.2.1 ⟨i,hi⟩
    · norm_num

theorem side_nonneg (a : ℕ → ι → ℝ) (p : ℕ → Bool) (ha : ∀ t i, 0 ≤ a t i) (t : ℕ) :
    0 ≤ SideReferenceSchedule.charge a p t := by
  unfold SideReferenceSchedule.charge
  split_ifs
  · exact le_rfl
  · exact le_rfl
  · exact add_nonneg (SideReferenceSchedule.side_nonneg ha p t) (SideReferenceSchedule.side_nonneg ha p (t+1))

theorem size_nonneg {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) : 0 ≤ sizeCharge a b := by
  apply sum_nonneg
  intro i _
  unfold AllocationSchedule.charge
  split_ifs
  · exact le_rfl
  · exact add_nonneg (ha i) (hb i)

theorem sparse {a b B : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hB : ∀ i, B i ≤ 40*b i) :
    (∑ i, if a i=b i then 0 else B i) ≤ 40*sizeCharge a b := by
  rw [sizeCharge,mul_sum]
  apply sum_le_sum
  intro i _
  unfold AllocationSchedule.charge
  split_ifs
  · norm_num
  · linarith [hB i,ha i]

theorem not_reset_base {a : ℕ → ι → ℝ} {p : ℕ → Bool} {t : ℕ}
    (h : SideReferenceSchedule.reset a p t=false) :
    (EpochGeometry.schedule a p t).base=(EpochGeometry.schedule a p (t+1)).base := by
  have hf : ¬AllocationEpoch.fires (EpochGeometry.scalar (EpochGeometry.schedule a p t))
      (EpochGeometry.variation (a t) (a (t+1))) (p t) := by
    simpa only [SideReferenceSchedule.reset,decide_eq_false_iff_not] using h
  rw [EpochGeometry.schedule,EpochGeometry.update,ite_eq_right hf]

theorem jump {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i) (p : ℕ → Bool)
    {ell ct C : ℝ} (hsc : 0 ≤ C*ell) (hct : ct/ell ≤ 1)
    (hp : ∀ t, AlphaEmpty.valid (param a p ell ct C t)) (t : ℕ) (B v : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hBb : ∀ i, B i ≤ 40*a (t+1) i)
    (hpa : DomainTransport.Supported (AlphaEmpty.active (param a p ell ct C t)) B)
    (hqa : DomainTransport.Supported (AlphaEmpty.active (param a p ell ct C (t+1))) B)
    (hv : AlphaEmpty.state (param a p ell ct C (t+1)) v)
    (hf : ∀ i, (∑ j, B j)*v i ≤ (1+AlphaEmpty.eta (param a p ell ct C t) i)*B i) :
    |AlphaEmpty.potential (param a p ell ct C (t+1)) B v-
      AlphaEmpty.potential (param a p ell ct C t) B v| ≤
      320*(C*ell)*sizeCharge (a t) (a (t+1))+
      1600*(C*ell)*SideReferenceSchedule.charge a p t+
      1200*(C*ell)*SideReferenceSchedule.wholesale a p t := by
  have hsz := size_nonneg (ha t) (ha (t+1))
  have hsd := side_nonneg a p ha t
  have ht0 := EpochGeometry.total_nonneg (ha t)
  have ht1 := EpochGeometry.total_nonneg (ha (t+1))
  by_cases hr : SideReferenceSchedule.reset a p t=true
  · have hh := AlphaPrepared.jump (hp t) (hp (t+1)) B v hB hpa hqa hv hf
    have hs0 := EpochAlphaJump.scale_bound (a t) (EpochGeometry.schedule a p t)
      (SideReferenceSchedule.reference a p t) ell ct C hsc
    have hs1 := EpochAlphaJump.scale_bound (a (t+1)) (EpochGeometry.schedule a p (t+1))
      (SideReferenceSchedule.reference a p (t+1)) ell ct C hsc
    change AlphaEmpty.scale (param a p ell ct C t) ≤ C*ell at hs0
    change AlphaEmpty.scale (param a p ell ct C (t+1)) ≤ C*ell at hs1
    have hS : 0 ≤ ∑ i, B i := sum_nonneg fun i _ => hB i
    have hsb := sum_le_sum (s:=univ) (fun i _ => hBb i)
    rw [←mul_sum] at hsb
    change _ ≤ 40*EpochGeometry.total (a (t+1)) at hsb
    have h1 := mul_le_mul_of_nonneg_right (add_le_add hs0 hs1) hS
    have h2 := mul_le_mul_of_nonneg_left hsb hsc
    have h3 := mul_nonneg hsc ht0
    have hz := mul_nonneg hsc hsz
    have hside := mul_nonneg hsc hsd
    rw [SideReferenceSchedule.wholesale,ite_eq_left hr]
    nlinarith
  · have hr' := Bool.eq_false_iff.mpr hr
    rw [SideReferenceSchedule.wholesale,ite_eq_right hr,mul_zero,add_zero]
    have hS : 0 ≤ ∑ i, B i := sum_nonneg fun i _ => hB i
    rcases hS.eq_or_lt with hz | hpos
    · have he := AlphaPrepared.zero_of_sum hB hz.symm
      rw [he,AlphaEmpty.potential_zero,AlphaEmpty.potential_zero,sub_self,abs_zero]
      positivity
    · have hs := EpochGeometry.schedule_valid ha p t
      have hs' := EpochGeometry.schedule_valid ha p (t+1)
      have he := not_reset_base hr'
      have hpa' : DomainTransport.Supported (EpochParameters.active (a t)) B := by
        simpa only [param,EpochAlphaSchedule.active_eq hs] using hpa
      have hqa' : DomainTransport.Supported (EpochParameters.active (a (t+1))) B := by
        simpa only [param,EpochAlphaSchedule.active_eq hs'] using hqa
      have hsum : ∑ i, v i=1 := by
        cases heq : param a p ell ct C (t+1) with
        | none =>
          have hzB : B=fun _ => 0 := AlphaEmpty.zero_supported (by simpa only [heq,AlphaEmpty.active] using hqa)
          simp only [hzB,sum_const_zero,lt_self_iff_false] at hpos
        | some q =>
          rw [heq] at hv
          exact hv.2.2
      have hf2 (i : ι) : (∑ j, B j)*v i ≤ 2*B i := by
        have hh := mul_le_mul_of_nonneg_right (eta_le (hp t) i) (hB i)
        nlinarith [hf i]
      have hh := EpochAlphaStatic.same_epoch (ha t) (ha (t+1)) hs hs' he hsc hct
        (fun o ho => SideReferenceSchedule.reference_spec ha p t ho)
        (fun o ho => SideReferenceSchedule.reference_spec ha p (t+1) ho)
        (hp t) (hp (t+1)) v hpos hB hBb hpa' hqa' (AlphaEmpty.state_interval hv) hsum hf2
      have hc : (if SideReferenceSchedule.reference a p t=SideReferenceSchedule.reference a p (t+1) then 0
          else match EpochGeometry.dominant (EpochGeometry.schedule a p t) with
          | none => 0
          | some o => 1600*(C*ell)*(EpochGeometry.side o (a t)+EpochGeometry.side o (a (t+1)))) =
          1600*(C*ell)*SideReferenceSchedule.charge a p t := by
        unfold SideReferenceSchedule.charge SideReferenceSchedule.side
        rw [ite_eq_right hr,SideReferenceSchedule.not_reset_dominant hr']
        split_ifs
        · ring
        · cases hd : EpochGeometry.dominant (EpochGeometry.schedule a p t) <;> ring
      have hsp := mul_le_mul_of_nonneg_left (sparse (ha t) hBb) hsc
      calc
        _ ≤ 8*(C*ell)*(∑ i, if a t i=a (t+1) i then 0 else B i)+
            (if SideReferenceSchedule.reference a p t=SideReferenceSchedule.reference a p (t+1) then 0
            else match EpochGeometry.dominant (EpochGeometry.schedule a p t) with
            | none => 0
            | some o => 1600*(C*ell)*(EpochGeometry.side o (a t)+EpochGeometry.side o (a (t+1)))) := hh
        _ = 8*(C*ell)*(∑ i, if a t i=a (t+1) i then 0 else B i)+
            1600*(C*ell)*SideReferenceSchedule.charge a p t := congrArg (fun z => _+z) hc
        _ ≤ _ := by nlinarith


end UniformKServer.EpochAlphaCharge

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochAlphaBudget
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! Summing actual sparse, side-reference and wholesale alpha jump charges.
There is no additive restart amount for individual epochs. -/
noncomputable section
namespace UniformKServer.EpochAlphaBudget
open Finset UniformKServer.EpochAlphaCharge
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem variation_le {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    EpochGeometry.variation a b ≤ sizeCharge a b := by
  apply sum_le_sum
  intro i _
  unfold AllocationSchedule.charge
  split_ifs with he
  · simp [he]
  · exact (abs_sub _ _).trans (by rw [abs_of_nonneg (hb i),abs_of_nonneg (ha i)]; ring_nf; rfl)

theorem charge_budget {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i) (p : ℕ → Bool)
    {K : ℝ} (hK : 0 ≤ K) (H : ℕ) :
    (∑ t ∈ range H, (320*K*sizeCharge (a t) (a (t+1))+
        1600*K*SideReferenceSchedule.charge a p t+1200*K*SideReferenceSchedule.wholesale a p t)) ≤
      4100000*K*(∑ t ∈ range H, sizeCharge (a t) (a (t+1)))+
      4400*K*(∑ t ∈ range H, if p t then EpochGeometry.total (a t)+EpochGeometry.total (a (t+1)) else 0) := by
  have hV := sum_le_sum (s:=range H) (fun t _ => variation_le (ha t) (ha (t+1)))
  have hS := SideReferenceSchedule.budget ha p H
  have hW := SideReferenceSchedule.wholesale_budget ha p H
  have hV' := mul_le_mul_of_nonneg_left hV hK
  have hS' := mul_le_mul_of_nonneg_left hS hK
  have hW' := mul_le_mul_of_nonneg_left hW hK
  have hx : 0 ≤ K*(∑ t ∈ range H, sizeCharge (a t) (a (t+1))) :=
    mul_nonneg hK (sum_nonneg fun t _ => size_nonneg (ha t) (ha (t+1)))
  simp only [sum_add_distrib,←mul_sum]
  nlinarith

theorem jump_budget {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i) (p : ℕ → Bool)
    {ell ct C : ℝ} (hsc : 0 ≤ C*ell) (hct : ct/ell ≤ 1)
    (hp : ∀ t, AlphaEmpty.valid (param a p ell ct C t)) (B v : ℕ → ι → ℝ)
    (hB : ∀ t i, 0 ≤ B t i) (hBb : ∀ t i, B t i ≤ 40*a (t+1) i)
    (hpa : ∀ t, DomainTransport.Supported (AlphaEmpty.active (param a p ell ct C t)) (B t))
    (hqa : ∀ t, DomainTransport.Supported (AlphaEmpty.active (param a p ell ct C (t+1))) (B t))
    (hv : ∀ t, AlphaEmpty.state (param a p ell ct C (t+1)) (v t))
    (hf : ∀ t i, (∑ j, B t j)*v t i ≤ (1+AlphaEmpty.eta (param a p ell ct C t) i)*B t i)
    (H : ℕ) :
    (∑ t ∈ range H, |AlphaEmpty.potential (param a p ell ct C (t+1)) (B t) (v t)-
        AlphaEmpty.potential (param a p ell ct C t) (B t) (v t)|) ≤
      4100000*(C*ell)*(∑ t ∈ range H, sizeCharge (a t) (a (t+1)))+
      4400*(C*ell)*(∑ t ∈ range H, if p t then EpochGeometry.total (a t)+EpochGeometry.total (a (t+1)) else 0) := by
  exact (sum_le_sum (s:=range H) fun t _ => jump ha p hsc hct hp t (B t) (v t)
    (hB t) (hBb t) (hpa t) (hqa t) (hv t) (hf t)).trans (charge_budget ha p hsc H)

end UniformKServer.EpochAlphaBudget

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CrossRule
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                
section

/-! The two actual hysteresis crossings in the star outputs. In contrast to
 comparing with an unused old rule, these bounds use only the states that
 actually existed. The coefficient of parent variation stays exactly one. -/
namespace UniformKServer.AllocationOutputs
noncomputable section
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem holes_two_total (R : ℝ) (ω : ι → ℝ) (o : ι) :
    (∑ i, holesTwo R ω o i)=max R (sideTotal ω o) := by
  rw [←sum_erase_add _ _ (mem_univ o)]
  have he : (∑ i ∈ univ.erase o, holesTwo R ω o i)=sideTotal ω o := by
    apply sum_congr rfl
    intro i hi
    simp only [holesTwo,ite_eq_right (ne_of_mem_erase hi)]
  rw [he]
  simp only [holesTwo,ite_true, if_true]
  rcases le_total R (sideTotal ω o) with h|h
  · rw [max_eq_right (sub_nonpos.mpr h),max_eq_right h,add_zero]
  · rw [max_eq_left (sub_nonneg.mpr h),max_eq_left h]
    ring

theorem rule_two_eq_holes (d w : ι → ℝ) (q D : ℝ) (o : ι)
    (h : 0 ≤ sideTotal (fun i => D*w i) o) :
    ruleTwo d w q D o = fun i => d i-holesTwo (excess d q) (fun i => D*w i) o i := by
  funext i
  linarith [rule_two_holes d w q D o i h]

/-- I-to-II: the new D suffices, even though no old side vector was output. -/
theorem downcross (d₀ d₁ α₀ w₁ : ι → ℝ) (q₀ q₁ D₁ L W : ℝ) (o : ι)
    (hα : ∀ i, 0 ≤ α₀ i) (hsum : ∑ i, α₀ i=1)
    (hD : 0 ≤ D₁) (hw : ∀ i, 0 ≤ w₁ i) (hW : ∑ i, w₁ i ≤ W)
    (hR : excess d₁ q₁ ≤ L*D₁) :
    variation (ruleOne d₀ α₀ q₀) (ruleTwo d₁ w₁ q₁ D₁ o) ≤
      |q₁-q₀|+2*variation d₀ d₁+(2*L+W)*D₁ := by
  obtain ⟨hside,hside'⟩ := side_scalar_bound D₁ W w₁ o hD hw hW
  have hω (i : ι) : 0 ≤ D₁*w₁ i := mul_nonneg hD (hw i)
  have hm := nonnegative_movement (fun i => excess d₀ q₀*α₀ i)
    (holesTwo (excess d₁ q₁) (fun i => D₁*w₁ i) o)
    (fun i => mul_nonneg (excess_nonneg _ _) (hα i)) (holes_two_nonneg _ _ _ hω)
  rw [←mul_sum,hsum,mul_one,holes_two_total] at hm
  have ht : max (excess d₁ q₁) (sideTotal (fun i => D₁*w₁ i) o) ≤ excess d₁ q₁+D₁*W := by
    apply max_le
    · linarith [hside.trans hside']
    · linarith [excess_nonneg d₁ q₁]
  have hRdiff : excess d₀ q₀ ≤ excess d₁ q₁+|excess d₁ q₁-excess d₀ q₀| := by
    linarith [neg_le_abs (excess d₁ q₁-excess d₀ q₀)]
  have he := excess_difference d₀ d₁ q₀ q₁
  have hret := outputs_from_holes d₀ d₁ (fun i => excess d₀ q₀*α₀ i)
    (holesTwo (excess d₁ q₁) (fun i => D₁*w₁ i) o)
  rw [rule_two_eq_holes _ _ _ _ _ hside]
  change variation (fun i => d₀ i-excess d₀ q₀*α₀ i)
    (fun i => d₁ i-holesTwo (excess d₁ q₁) (fun i => D₁*w₁ i) o i) ≤ _
  nlinarith

/-- II-to-I: the new S plus held-D variation suffices, without evaluating
 the old simplex state as though Rule I had been in force there. -/
theorem upcross (d₀ d₁ w₀ α₁ : ι → ℝ) (q₀ q₁ D₀ D₁ S₁ L W : ℝ) (o : ι)
    (hα : ∀ i, 0 ≤ α₁ i) (hsum : ∑ i, α₁ i=1)
    (hD₀ : 0 ≤ D₀) (hw : ∀ i, 0 ≤ w₀ i) (hW : ∑ i, w₀ i ≤ W)
    (hR : excess d₁ q₁ ≤ L*S₁) (hSD : D₁ ≤ S₁/2) :
    variation (ruleTwo d₀ w₀ q₀ D₀ o) (ruleOne d₁ α₁ q₁) ≤
      |q₁-q₀|+2*variation d₀ d₁+(2*L+W/2)*S₁+W*|D₁-D₀| := by
  obtain ⟨hside,hside'⟩ := side_scalar_bound D₀ W w₀ o hD₀ hw hW
  have hW₀ : 0 ≤ W := (sum_nonneg fun i _ => hw i).trans hW
  have hω (i : ι) : 0 ≤ D₀*w₀ i := mul_nonneg hD₀ (hw i)
  have hm := nonnegative_movement (holesTwo (excess d₀ q₀) (fun i => D₀*w₀ i) o)
    (fun i => excess d₁ q₁*α₁ i) (holes_two_nonneg _ _ _ hω)
    (fun i => mul_nonneg (excess_nonneg _ _) (hα i))
  rw [holes_two_total,←mul_sum,hsum,mul_one] at hm
  have ht : max (excess d₀ q₀) (sideTotal (fun i => D₀*w₀ i) o) ≤ excess d₀ q₀+D₀*W := by
    apply max_le
    · linarith [hside.trans hside']
    · linarith [excess_nonneg d₀ q₀]
  have hRdiff : excess d₀ q₀ ≤ excess d₁ q₁+|excess d₁ q₁-excess d₀ q₀| := by
    linarith [neg_le_abs (excess d₁ q₁-excess d₀ q₀)]
  have hDdiff : D₀ ≤ D₁+|D₁-D₀| := by linarith [neg_le_abs (D₁-D₀)]
  have hDnew := mul_le_mul_of_nonneg_right hSD hW₀
  have hDold := mul_le_mul_of_nonneg_right hDdiff hW₀
  have he := excess_difference d₀ d₁ q₀ q₁
  have hret := outputs_from_holes d₀ d₁ (holesTwo (excess d₀ q₀) (fun i => D₀*w₀ i) o)
    (fun i => excess d₁ q₁*α₁ i)
  rw [rule_two_eq_holes _ _ _ _ _ hside]
  change variation (fun i => d₀ i-holesTwo (excess d₀ q₀) (fun i => D₀*w₀ i) o i)
    (fun i => d₁ i-excess d₁ q₁*α₁ i) ≤ _
  nlinarith

end
end UniformKServer.AllocationOutputs

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotTemplates
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Actual admissible pilot templates; no drift/pilot premise is added to the
partition construction. The constants are independent of the finite law. -/
noncomputable section
namespace UniformKServer.PilotEdits
open PilotCompact

theorem rate_nonneg (T : Template) : 0 ≤ rate T := by
  have hσ := T.sigma_pos
  have hγ := T.gamma_pos
  have hδ := T.delta_pos
  have hL := T.L_nonneg
  unfold rate driftConstant localSlopeConstant
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  positivity

end UniformKServer.PilotEdits

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

theorem linear_filtering (F : Flow X Ω k) (t : ℕ) (b : Ω→X→ℝ)
    (hb : ∀ ω v, (F.filtration t).r ω v→b ω=b v) :
    average F.weight (fun ω=>linearPotential (F.filtered t ω) (b ω))=
      average F.weight (fun ω=>linearPotential (F.post t ω) (b ω)) := by
  have hp (p : X) := F.filtering t (fun ω=>b ω p) (fun ω v hv=>congrFun (hb ω v hv) p) p
  unfold average linearPotential
  simp only [mul_sum]
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro p _
  have he : (∑ ω,F.weight ω*b ω p*(F.filtered t ω p-F.post t ω p))=
      (∑ ω,F.weight ω*(F.filtered t ω p*b ω p))-
      (∑ ω,F.weight ω*(F.post t ω p*b ω p)) := by
    rw [←sum_sub_distrib]
    apply sum_congr rfl
    intro ω _
    ring
  linarith only [hp p,he]

end UniformKServer.PilotEdits

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

noncomputable def activeCode : Code := Classical.choose (code_exists RawProgram.run RawProgram.primitive_run)

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

abbrev program := LiteralPartrec.processor LiteralVector.activeCode
abbrev Init (u r a : ℕ) := LiteralPartrec.input LiteralVector.activeCode [u,r,a]

def finishes (t u r a : ℕ) : Bool :=
  ((advance program)^[t] (ofState (Init u r a))).2.2

 theorem primitive_finishes : Primrec (fun p : ℕ×ℕ×ℕ×ℕ=>finishes p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold finishes
  exact Primrec.snd.comp (Primrec.snd.comp ((iter_primitive program).comp Primrec.fst
    ((LiteralInput.primitive_input LiteralVector.activeCode).comp (by fun_prop))))

end UniformKServer.LiteralBound

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RuntimeCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.RuntimeCertificate
open RawProgram RawCertificate RawFinite Primrec
open scoped Classical
def B (k : ℕ) (v : Certificate) : ℕ := RawCertificate.horizon k (cap v)*bits v

def item (k : ℕ) (S : List ℕ) (T u r a : ℕ) : Bool :=
  decide (chosen (unpack u) (requestToken r) a<k) &&
  has S (Encodable.encode (next (unpack u) (requestToken r) a)) &&
  decide ((chosen (unpack u) (requestToken r) a).bits.length≤T) &&
  LiteralBound.finishes T u (requestToken r) a

def row (k b : ℕ) (S : List ℕ) (T u r : ℕ) : Bool :=
  decide ((natCode (r+1)).length+1≤T) &&
    (List.range (2^(b+1))).all (fun a=>item k S T u r a)

def node (n k b : ℕ) (S : List ℕ) (T u : ℕ) : Bool :=
  decide (u.bits.length+1≤T) && (List.range n).all (fun r=>row k b S T u r)

def verify (n k : ℕ) (v : Certificate) (c : Cert) : Bool :=
  has c.1 (Encodable.encode (RawProgram.initial n k v)) && decide (B k v+1 ≤ c.2) &&
  c.1.all (fun u=>node n k (B k v) c.1 c.2 u)

section Primitive
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_B (k : α→ℕ) (v : α→Certificate) (hk : Primrec k) (hv : Primrec v) :
    Primrec (fun x=>B (k x) (v x)) := by unfold B cap bits;fun_prop
@[fun_prop] theorem primitive_initial (n k : α→ℕ) (v : α→Certificate)
    (hn : Primrec n) (hk : Primrec k) (hv : Primrec v) :
    Primrec (fun x=>RawProgram.initial (n x) (k x) (v x)) := by unfold RawProgram.initial payload;fun_prop
@[fun_prop] theorem primitive_finishes (t u r a : α→ℕ)
    (ht : Primrec t) (hu : Primrec u) (hr : Primrec r) (ha : Primrec a) :
    Primrec (fun x=>LiteralBound.finishes (t x) (u x) (r x) (a x)) :=
  LiteralBound.primitive_finishes.comp (ht.pair (hu.pair (hr.pair ha)))
@[fun_prop] theorem primitive_item (k : α→ℕ) (S : α→List ℕ) (T u r a : α→ℕ)
    (hk : Primrec k) (hS : Primrec S) (hT : Primrec T) (hu : Primrec u) (hr : Primrec r) (ha : Primrec a) :
    Primrec (fun x=>item (k x) (S x) (T x) (u x) (r x) (a x)) := by
  have hp:=RawProgram.primitive_unpack u hu
  have hq:=primitive_requestToken r hr
  have hc:=RawProgram.primitive_chosen _ _ _ hp hq ha
  have hn:=RawProgram.primitive_next _ _ _ hp hq ha
  unfold item
  apply PrimitiveRules.bool_and
  · apply PrimitiveRules.bool_and
    · apply PrimitiveRules.bool_and
      · exact PrimitiveRules.lts _ _ hc hk
      · exact primitive_has _ _ hS (Primrec.encode.comp hn)
    · exact PrimitiveRules.les _ _ (Primrec.list_length.comp (RawBits.primitive_bits.comp hc)) hT
  · exact primitive_finishes _ _ _ _ hT hu hq ha
@[fun_prop] theorem primitive_row (k b : α→ℕ) (S : α→List ℕ) (T u r : α→ℕ)
    (hk : Primrec k) (hb : Primrec b) (hS : Primrec S) (hT : Primrec T) (hu : Primrec u) (hr : Primrec r) :
    Primrec (fun x=>row (k x) (b x) (S x) (T x) (u x) (r x)) := by unfold row;fun_prop
@[fun_prop] theorem primitive_node (n k b : α→ℕ) (S : α→List ℕ) (T u : α→ℕ)
    (hn : Primrec n) (hk : Primrec k) (hb : Primrec b) (hS : Primrec S) (hT : Primrec T) (hu : Primrec u) :
    Primrec (fun x=>node (n x) (k x) (b x) (S x) (T x) (u x)) := by unfold node;fun_prop
 theorem primitive_verify : Primrec (fun p : (ℕ×ℕ×Certificate)×Cert=>verify p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold verify
  apply PrimitiveRules.bool_and
  · apply PrimitiveRules.bool_and
    · apply primitive_has
      · exact Primrec.fst.comp Primrec.snd
      · exact Primrec.encode.comp (primitive_initial _ _ _ (by fun_prop) (by fun_prop) (by fun_prop))
    · exact PrimitiveRules.les _ _
        (Primrec.succ.comp (primitive_B _ _ (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))) (Primrec.snd.comp Primrec.snd)
  · apply PrimitiveRules.bool_all
    · exact Primrec.fst.comp Primrec.snd
    · exact primitive_node _ _ _ _ _ _
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        (primitive_B _ _ (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
end Primitive

end UniformKServer.RuntimeCertificate

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ConstructorSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.ConstructorSearch
open RawCertificate
open scoped Classical
abbrev Cert := Certificate×RuntimeCertificate.Cert

def verify (mult : ℕ) (i : Input) (v : Cert) : Bool :=
  RawCertificate.verify mult i v.1 && RuntimeCertificate.verify i.1 i.2.1 v.1 v.2

def candidate (mult : ℕ) (i : Input) (a : ℕ) : Option Cert :=
  (Encodable.decode a).bind fun v=>if verify mult i v then some v else none

def search (mult : ℕ) (i : Input) : Part Cert := Nat.rfindOpt (candidate mult i)

theorem primitive_verify (mult : ℕ) : Primrec₂ (verify mult) := by
  unfold verify
  apply PrimitiveRules.bool_and
  · exact (RawCertificate.primitive_verify mult).comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  · exact RuntimeCertificate.primitive_verify.comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair (Primrec.fst.comp Primrec.snd)) |>.pair
          (Primrec.snd.comp Primrec.snd))

theorem candidate_primrec (mult : ℕ) : Primrec₂ (candidate mult) := by
  have hd : Primrec (fun p : Input×ℕ=>(Encodable.decode p.2 : Option Cert)) := Primrec.decode.comp Primrec.snd
  have hg : Primrec (fun p : (Input×ℕ)×Cert=>if verify mult p.1.1 p.2 then some p.2 else none) := by
    rw [show (fun p : (Input×ℕ)×Cert=>if verify mult p.1.1 p.2 then some p.2 else none)=
      (fun p=>bif verify mult p.1.1 p.2 then some p.2 else none) from by funext p;rw [Bool.cond_eq_ite]]
    exact Primrec.cond ((primitive_verify mult).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  exact Primrec.option_bind hd hg.to₂

theorem search_partrec (mult : ℕ) : Partrec (search mult) :=
  Partrec.rfindOpt (candidate_primrec mult).to_comp

end UniformKServer.ConstructorSearch

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ConstructorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.ConstructorProgram
open RawCertificate
open scoped Classical

def result (i : Input) (v : ConstructorSearch.Cert) : List.Vector ℕ 3 :=
  ⟨[2^(2^v.2.2),2^(RuntimeCertificate.B i.2.1 v.1),
    Encodable.encode (RawProgram.initial i.1 i.2.1 v.1)],rfl⟩

def run (mult : ℕ) (a : List.Vector ℕ 1) : Part (List.Vector ℕ 3) :=
  (ConstructorSearch.search mult (read a.head)).map (result (read a.head))

theorem primitive_read : Primrec read :=
  RawBinary.primitive_input _ RawBits.primitive_bits

theorem primitive_result : Primrec₂ result := by
  apply Primrec.vector_toList_iff.mp
  change Primrec (fun p : Input×ConstructorSearch.Cert=>[2^(2^p.2.2.2),2^(RuntimeCertificate.B p.1.2.1 p.2.1),Encodable.encode (RawProgram.initial p.1.1 p.1.2.1 p.2.1)])
  fun_prop

theorem run_partrec (mult : ℕ) : Partrec (run mult) := by
  have h : Partrec (fun a : List.Vector ℕ 1=>ConstructorSearch.search mult (read a.head)) :=
    (ConstructorSearch.search_partrec mult).comp (primitive_read.comp Primrec.vector_head).to_comp
  exact h.map (primitive_result.comp
    (primitive_read.comp (Primrec.vector_head.comp Primrec.fst)) Primrec.snd).to_comp.to₂

def code (mult : ℕ) : Turing.ToPartrec.Code :=
  Classical.choose (LiteralVector.partial_code_exists (run mult) (run_partrec mult))

end UniformKServer.ConstructorProgram

end

end OAI
end


