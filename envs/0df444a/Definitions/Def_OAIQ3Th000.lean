-- Prove2me | Definitions.Def_OAIQ3Th000
-- name    : OAIQ3Th000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T03:03:48.314485+00:00
-- url     : https://prove2.me/theorems/1666c1c9-100f-4b72-ad98-8251736afc93
-- title:
--   Definitions bundle OAIQ3Th000 of the split of OpenAI, Optimal-order mixing of the Thorp shuffle
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ThorpResults.remaining_main`, carved from OpenAI's openai/math development (OpenAI, *Optimal-order mixing of the Thorp shuffle*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 755 declarations of OpenAI's Lean: 416 definitions, 7 inductive types or structures, 27 instances and 305 theorems. The definitions and types are `OAI.Thorp.Block.complement`, `OAI.Thorp.Block.complementIn`, `OAI.Thorp.Block.discarded`, `OAI.Thorp.Block.domain`, `OAI.Thorp.Block.eightEquiv`, `OAI.Thorp.Block.embedding`, `OAI.Thorp.Block.extract`, `OAI.Thorp.Block.fiberEquiv`, `OAI.Thorp.Block.fullRate`, `OAI.Thorp.Block.hom`, `OAI.Thorp.Block.orderedRestriction`, `OAI.Thorp.Block.ordering`, `OAI.Thorp.Block.perm`, `OAI.Thorp.Block.restriction`, `OAI.Thorp.Conditional.CenteredState`, `OAI.Thorp.Conditional.CenteredState.raw`, `OAI.Thorp.Conditional.RawState`, `OAI.Thorp.Conditional.bandEnergy`, `OAI.Thorp.Conditional.centeredPoint`, `OAI.Thorp.Conditional.character`, `OAI.Thorp.Conditional.coefficient`, `OAI.Thorp.Conditional.coinHalfMarker`, `OAI.Thorp.Conditional.completeTest`, `OAI.Thorp.Conditional.expectedBand`, `OAI.Thorp.Conditional.expectedEnergy`, `OAI.Thorp.Conditional.expectedNoise`, `OAI.Thorp.Conditional.firstMean`, `OAI.Thorp.Conditional.flow`, `OAI.Thorp.Conditional.freeCount`, `OAI.Thorp.Conditional.freeOf`, `OAI.Thorp.Conditional.freePairMask`, `OAI.Thorp.Conditional.halfEnergy`, `OAI.Thorp.Conditional.halfHistory`, `OAI.Thorp.Conditional.halfMarker`, `OAI.Thorp.Conditional.halfPositionEquiv`, `OAI.Thorp.Conditional.halfRaw`, `OAI.Thorp.Conditional.initialState`, `OAI.Thorp.Conditional.insertBit`, `OAI.Thorp.Conditional.iterateState`, `OAI.Thorp.Conditional.marginalRate` and 383 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/ThorpResults, in whole or in part: `ThorpRouting_Harmonic_AlternatingPerm`, `ThorpRouting_Harmonic_AssignmentSlots`, `ThorpRouting_Harmonic_AverageMap`, `ThorpRouting_Harmonic_BlockProduct`, `ThorpRouting_Harmonic_Coins`, `ThorpRouting_Harmonic_CutoffMass`, `ThorpRouting_Harmonic_ExposedCoins`, `ThorpRouting_Harmonic_InputTree`, `ThorpRouting_Harmonic_InsertionPerm`, `ThorpRouting_Harmonic_Model`, `ThorpRouting_Harmonic_ModifiedReverseCoins`, `ThorpRouting_Harmonic_ModifiedRoutingMoment`, `ThorpRouting_Harmonic_PairAssembleEquiv`, `ThorpRouting_Harmonic_PalindromeFamilyCost`, `ThorpRouting_Harmonic_ParallelFollow`, `ThorpRouting_Harmonic_PriorPaths`, `ThorpRouting_Harmonic_RotationMeeting`, `ThorpRouting_Harmonic_SandwichShuffle`, `ThorpRouting_Harmonic_Shapes`, `ThorpRouting_Harmonic_Site`, `ThorpRouting_Harmonic_TailShapes`, `ThorpRouting_Harmonic_ZeroExtend`, `ThorpRouting_TraceDecay`, `ThorpRouting_TraceModel`, `ThorpShuffle_BlockEmbedding`, `ThorpShuffle_BlockFibers`, `ThorpShuffle_Classification`, `ThorpShuffle_ConditionalFlow`, `ThorpShuffle_ConditionalLaw`, `ThorpShuffle_Cyclic`, `ThorpShuffle_DegreeBounds`, `ThorpShuffle_EightBlocks`, `ThorpShuffle_EnergyDecay`, `ThorpShuffle_ExtensionBounds`, `ThorpShuffle_FiniteExpectation`, `ThorpShuffle_FiniteLaw`, `ThorpShuffle_FixedLists_Asymptotics`, `ThorpShuffle_FourierBounds`, `ThorpShuffle_FourierFamilies`, `ThorpShuffle_FreshCoins`, `ThorpShuffle_HalfHistories`, `ThorpShuffle_Irreducibility`, `ThorpShuffle_JointProjectors`, `ThorpShuffle_LinearExtensions`, `ThorpShuffle_MarginalBounds`, `ThorpShuffle_MarginalEnergy`, `ThorpShuffle_MaskedResampling`, `ThorpShuffle_Model`, `ThorpShuffle_NoiseEnergy`, `ThorpShuffle_PairAveraging`, `ThorpShuffle_Parity`, `ThorpShuffle_PartitionBounds`, `ThorpShuffle_PermutationCharacters`, `ThorpShuffle_Polytabloids`, `ThorpShuffle_ProductProjectors`, `ThorpShuffle_Reachability`, `ThorpShuffle_ReciprocalDegrees`, `ThorpShuffle_Reynolds`, `ThorpShuffle_Specht`, `ThorpShuffle_Support`, `ThorpShuffle_SymmetricFamilies`, `ThorpShuffle_Tableaux`, `ThorpShuffle_TaggedCompletion`, `ThorpShuffle_Trimming`, `ThorpShuffle_Walsh`, `ThorpShuffle_WalshFlow`.
--
--   **Imports.** It imports the published bundle `Def_ThorpRemaining`.
--
--   **Imported by** (directly, in this split): the statements `OAI_ThorpNine_Harmonic_Thorp_Specht_spectral_regimes` and `OAI.ThorpNine.Harmonic.Thorp.Specht.spectral_regimes_q3`; the proofs of `OAI_ThorpNine_Harmonic_Thorp_Specht_spectral_regimes`, `OAI.ThorpNine.Harmonic.Thorp.Specht.spectral_regimes_q3`, `OAI.ThorpResults.remaining_main`, `OAI_Thorp_deterministic_coordinate_information_main`, `OAI.Thorp.deterministic_coordinate_information_main_q3`, `OAI_Thorp_mixingTime_isTheta_log`, `OAI.Thorp.mixingTime_isTheta_log_q3`, `OAI_Thorp_random_coordinate_frames_main` and `OAI.Thorp.random_coordinate_frames_main_q3`.
-- source:
--   OpenAI, Optimal-order mixing of the Thorp shuffle, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Optimal-order-mixing-of-the-Thorp-shuffle-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/ThorpResults at commit adc7f12

import Mathlib
import Definitions.Def_ThorpRemaining

section
-- module Solutions.OAIQ3_Thorp.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp
open scoped BigOperators
open Filter

def Butterfly : ℕ → Type
  | 0 => Unit
  | d + 1 => (Card d → Bool) × (Bool → Butterfly d)

def childLift {d : ℕ} (p : Bool → Equiv.Perm (Card d)) : Equiv.Perm (Card (d + 1)) where
  toFun x := Fin.cons (x 0) (p (x 0) (Fin.tail x))
  invFun x := Fin.cons (x 0) ((p (x 0)).symm (Fin.tail x))
  left_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.symm_apply_apply, Fin.cons_self_tail]
  right_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.apply_symm_apply, Fin.cons_self_tail]

def butterflyPerm : (d : ℕ) → Butterfly d → Equiv.Perm (Card d)
  | 0, _ => 1
  | d + 1, b => pairSwitch b.1 * childLift (fun ε => butterflyPerm d (b.2 ε))

noncomputable def finiteMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

def SwitchIndex : ℕ → Type
  | 0 => Empty
  | d + 1 => Sum (Card d) (Bool × SwitchIndex d)

instance instFintypeSwitchIndex (d : ℕ) : Fintype (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ d ih => exact inferInstanceAs (Fintype (Sum (Card d) (Bool × SwitchIndex d)))

instance instDecidableEqSwitchIndex (d : ℕ) : DecidableEq (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq Empty)
  | succ d ih => exact inferInstanceAs (DecidableEq (Sum (Card d) (Bool × SwitchIndex d)))

def decodeButterfly : (d : ℕ) → (SwitchIndex d → Bool) → Butterfly d
  | 0, _ => ()
  | d + 1, ω => (fun y => ω (Sum.inl y), fun ε =>
      decodeButterfly d (fun i => ω (Sum.inr (ε,i))))

end Thorp

namespace Thorp.PairRouting
open scoped BigOperators
open Filter
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

noncomputable def tupleProbability {Ω β : Type*} [Fintype Ω] [DecidableEq β]
    (P : Ω → Equiv.Perm β) (x y : ι → β) : ℝ := by
  classical
  exact finiteMean (fun ω => if ∀ i, P ω (x i) = y i then 1 else 0)

end Thorp.PairRouting

namespace Thorp
open scoped BigOperators
open Filter

abbrev BenesCoins (d : ℕ) := (SwitchIndex d → Bool) × (SwitchIndex d → Bool)

def palindromePerm (d : ℕ) (ω : BenesCoins d) : Equiv.Perm (Card d) :=
  butterflyPerm d (decodeButterfly d ω.1) * (butterflyPerm d (decodeButterfly d ω.2)).symm

end Thorp

namespace Thorp.Casimir
open scoped BigOperators Classical
open Filter

noncomputable def levelScale (n k : ℕ) : ℝ :=
  (k:ℝ) * (1 + Real.log ((n:ℝ)/(k:ℝ)))

noncomputable def K (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) :
    Specht.hilbertSpace μ →L[ℂ] Specht.hilbertSpace μ :=
  UnitaryFinite.sampleOperator (V := Specht.hilbertSpace μ)
    (Specht.relabelledUnitary μ e) (palindromePerm d)

end Thorp.Casimir

namespace Thorp.HarmonicBounds
open scoped BigOperators Classical
open Casimir

noncomputable def W (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) : ℝ := ‖K d μ e‖

end Thorp.HarmonicBounds

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_Coins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp

open scoped BigOperators
open Filter

noncomputable def distance (d t : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ g : Equiv.Perm (Card d),
    |law d t g - 1 / (Nat.factorial (2 ^ d) : ℝ)|

lemma entropy_chord (p : ℝ) (hp : 0 ≤ p) (hq : p ≤ 1 / 2) :
    2 * p * Real.log 2 ≤ Real.binEntropy p := by
  have hc := Real.strictConcave_binEntropy.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    (show (2 : ℝ)⁻¹ ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    (show 0 ≤ 1 - 2 * p by linarith)
    (show 0 ≤ 2 * p by positivity)
    (show (1 - 2 * p) + 2 * p = 1 by ring)
  simpa only [Real.binEntropy_zero, Real.binEntropy_two_inv,
    smul_eq_mul, mul_zero, zero_add, show 2 * p * (2 : ℝ)⁻¹ = p by ring] using hc

lemma split_entropy_lower (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * min a b * Real.log 2 ≤
      (a + b) * Real.log (a + b) - a * Real.log a - b * Real.log b := by
  wlog hab : a ≤ b generalizing a b
  · have hba := this b a hb ha (le_of_not_ge hab)
    simpa only [min_comm, add_comm b a] using hba.trans_eq (show (b + a) * Real.log (b + a) - b * Real.log b - a * Real.log a =
      (a + b) * Real.log (a + b) - a * Real.log a - b * Real.log b by rw [add_comm b a]; ring)
  rw [min_eq_left hab]
  by_cases hz : a = 0
  · subst a
    simp
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
  have hbp : 0 < b := hap.trans_le hab
  have hs : 0 < a + b := add_pos hap hbp
  have hp : 0 ≤ a / (a + b) := div_nonneg ha hs.le
  have hq : a / (a + b) ≤ 1 / 2 := (div_le_iff₀ hs).mpr (by linarith)
  have hc := mul_le_mul_of_nonneg_left (entropy_chord (a / (a + b)) hp hq) hs.le
  have he : (a + b) * Real.binEntropy (a / (a + b)) =
      (a + b) * Real.log (a + b) - a * Real.log a - b * Real.log b := by
    unfold Real.binEntropy
    rw [show 1 - a / (a + b) = b / (a + b) by field_simp; ring]
    simp only [Real.log_inv]
    rw [Real.log_div (ne_of_gt hap) (ne_of_gt hs),
      Real.log_div (ne_of_gt hbp) (ne_of_gt hs)]
    field_simp
    ring
  rw [he] at hc
  calc
    2 * a * Real.log 2 = (a + b) * (2 * (a / (a + b)) * Real.log 2) := by
      field_simp
    _ ≤ _ := hc

noncomputable def childMarks {d : ℕ} (s : Finset (Card (d + 1))) (ε : Bool) :
    Finset (Card d) := (s.filter (fun x => x 0 = ε)).image Fin.tail

lemma card_childMarks {d : ℕ} (s : Finset (Card (d + 1))) (ε : Bool) :
    (childMarks s ε).card = (s.filter (fun x => x 0 = ε)).card := by
  classical
  unfold childMarks
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  have hx0 := (Finset.mem_filter.mp hx).2
  have hy0 := (Finset.mem_filter.mp hy).2
  rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, hx0, hy0, hxy]

lemma card_childMarks_add {d : ℕ} (s : Finset (Card (d + 1))) :
    (childMarks s false).card + (childMarks s true).card = s.card := by
  classical
  rw [card_childMarks, card_childMarks]
  simpa only [Bool.not_eq_false] using
    (Finset.card_filter_add_card_filter_not (s := s) (fun x => x 0 = false))

noncomputable def topMeetings {d : ℕ} (b : Butterfly (d + 1))
    (s : Finset (Card (d + 1))) : Finset (Card d) :=
  ((childMarks s false).image (butterflyPerm d (b.2 false))) ∩
    ((childMarks s true).image (butterflyPerm d (b.2 true)))

lemma card_topMeetings_le {d : ℕ} (b : Butterfly (d + 1)) (s : Finset (Card (d + 1))) :
    (topMeetings b s).card ≤ min (childMarks s false).card (childMarks s true).card := by
  classical
  apply le_min
  · exact (Finset.card_le_card Finset.inter_subset_left).trans_eq
      (Finset.card_image_of_injective _ (butterflyPerm d (b.2 false)).injective)
  · exact (Finset.card_le_card Finset.inter_subset_right).trans_eq
      (Finset.card_image_of_injective _ (butterflyPerm d (b.2 true)).injective)

noncomputable def encounters : (d : ℕ) → Butterfly d → Finset (Card d) → ℕ
  | 0, _, _ => 0
  | d + 1, b, s => encounters d (b.2 false) (childMarks s false) +
      encounters d (b.2 true) (childMarks s true) + (topMeetings b s).card

lemma butterfly_encounters (d : ℕ) (b : Butterfly d) (s : Finset (Card d)) :
    (encounters d b s : ℝ) ≤ (s.card : ℝ) * Real.log s.card / (2 * Real.log 2) := by
  induction d with
  | zero =>
    simp only [encounters, Nat.cast_zero]
    have hs : s.card ≤ 1 := by
      simpa [Card] using Finset.card_le_univ s
    interval_cases s.card <;> simp
  | succ d ih =>
    have h₀ := ih (b.2 false) (childMarks s false)
    have h₁ := ih (b.2 true) (childMarks s true)
    have ht : ((topMeetings b s).card : ℝ) ≤
        min ((childMarks s false).card : ℝ) ((childMarks s true).card : ℝ) := by
      exact_mod_cast card_topMeetings_le b s
    have he := split_entropy_lower ((childMarks s false).card : ℝ)
      ((childMarks s true).card : ℝ) (by positivity) (by positivity)
    have hs : ((childMarks s false).card : ℝ) + (childMarks s true).card = s.card := by
      exact_mod_cast card_childMarks_add s
    rw [hs] at he
    have hL : 0 < 2 * Real.log 2 := by positivity
    rw [le_div_iff₀ hL] at h₀ h₁ ⊢
    simp only [encounters, Nat.cast_add]
    nlinarith [mul_le_mul_of_nonneg_right ht hL.le]

def CylinderBound {α : Type*} (m : Finset α → ℝ) (p : α → ℝ) : Prop :=
  ∀ s, m s ≤ ∏ i ∈ s, p i

noncomputable def inclusionMoment {α Ω : Type*} [Fintype Ω]
    (F : Ω → Finset α) (s : Finset α) : ℝ := by
  classical
  exact finiteMean (fun ω => if s ⊆ F ω then 1 else 0)

inductive QueryTree (ι : Type*)
  | reject : QueryTree ι
  | accept : QueryTree ι
  | branch (i : ι) (zero one : QueryTree ι) : QueryTree ι
  | force (i : ι) (b : Bool) (next : QueryTree ι) : QueryTree ι

namespace QueryTree

variable {ι : Type*} [DecidableEq ι]

def queries : QueryTree ι → Finset ι
  | reject => ∅
  | accept => ∅
  | branch i zero one => insert i (queries zero ∪ queries one)
  | force i _ next => insert i (queries next)

def Fresh : QueryTree ι → Prop
  | reject => True
  | accept => True
  | branch i zero one => i ∉ queries zero ∧ i ∉ queries one ∧ Fresh zero ∧ Fresh one
  | force i _ next => i ∉ queries next ∧ Fresh next

def weighted : QueryTree ι → (ι → Bool) → ℝ
  | reject, _ => 0
  | accept, _ => 1
  | branch i zero one, ω => if ω i then weighted one ω else weighted zero ω
  | force i b next, ω => if ω i = b then 2 * weighted next ω else 0

def flipCoin (i : ι) : Equiv.Perm (ι → Bool) :=
  (show Function.Involutive (fun ω : ι → Bool => Function.update ω i (!(ω i))) from by
    intro ω
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [Function.update_of_ne h]).toPerm

def succeeds : QueryTree ι → (ι → Bool) → Bool
  | reject, _ => false
  | accept, _ => true
  | branch i zero one, ω => if ω i then succeeds one ω else succeeds zero ω
  | force i b next, ω => if ω i = b then succeeds next ω else false

def charge : QueryTree ι → (ι → Bool) → ℕ
  | reject, _ => 0
  | accept, _ => 0
  | branch i zero one, ω => if ω i then charge one ω else charge zero ω
  | force i b next, ω => if ω i = b then charge next ω + 1 else 0

end QueryTree

def encodeButterfly : (d : ℕ) → Butterfly d → SwitchIndex d → Bool
  | 0, _, i => nomatch i
  | _d + 1, b, Sum.inl y => b.1 y
  | d + 1, b, Sum.inr (ε,i) => encodeButterfly d (b.2 ε) i

lemma decode_encodeButterfly (d : ℕ) (b : Butterfly d) :
    decodeButterfly d (encodeButterfly d b) = b := by
  induction d with
  | zero => exact Unit.ext _ _
  | succ d ih =>
    apply Prod.ext
    · rfl
    · funext ε
      exact ih (b.2 ε)

lemma encode_decodeButterfly (d : ℕ) (ω : SwitchIndex d → Bool) :
    encodeButterfly d (decodeButterfly d ω) = ω := by
  induction d with
  | zero => funext i; exact Empty.elim i
  | succ d ih =>
    funext i
    cases i with
    | inl y => rfl
    | inr z => exact congrFun (ih (fun i => ω (Sum.inr (z.1,i)))) z.2

def butterflyCoinEquiv (d : ℕ) : (SwitchIndex d → Bool) ≃ Butterfly d where
  toFun := decodeButterfly d
  invFun := encodeButterfly d
  left_inv := encode_decodeButterfly d
  right_inv := decode_encodeButterfly d

noncomputable def routeDomain : (d : ℕ) → Card d → Card d → Finset (SwitchIndex d)
  | 0, _, _ => ∅
  | d + 1, x, y => by
      classical
      exact insert (Sum.inl (Fin.tail y))
        ((routeDomain d (Fin.tail x) (Fin.tail y)).image (fun i => Sum.inr (x 0,i)))

def routeValue : (d : ℕ) → Card d → Card d → SwitchIndex d → Bool
  | 0, _, _, i => nomatch i
  | _d + 1, x, y, Sum.inl _ => Bool.xor (x 0) (y 0)
  | d + 1, x, y, Sum.inr (_,i) => routeValue d (Fin.tail x) (Fin.tail y) i

end Thorp

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_ExposedCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp
open scoped BigOperators
open Filter

lemma card_routeDomain (d : ℕ) (x y : Card d) : (routeDomain d x y).card = d := by
  classical
  induction d with
  | zero => rfl
  | succ d ih =>
    change (insert (Sum.inl (Fin.tail y))
      ((routeDomain d (Fin.tail x) (Fin.tail y)).image
        (fun i => (Sum.inr (x 0,i) : Sum (Card d) (Bool × SwitchIndex d)))) :
      Finset (Sum (Card d) (Bool × SwitchIndex d))).card = d + 1
    rw [Finset.card_insert_of_notMem (by simp)]
    rw [Finset.card_image_of_injective _ (by intro i j h; cases h; rfl), ih]

lemma xor_eq_iff (a b c : Bool) : Bool.xor a b = c ↔ b = Bool.xor a c := by
  cases a <;> cases b <;> cases c <;> decide

lemma butterfly_endpoint_iff (d : ℕ) (ω : SwitchIndex d → Bool) (x y : Card d) :
    butterflyPerm d (decodeButterfly d ω) x = y ↔
      ∀ i ∈ routeDomain d x y, ω i = routeValue d x y i := by
  classical
  induction d with
  | zero =>
    have he : butterflyPerm 0 (decodeButterfly 0 ω) x = y := Subsingleton.elim _ _
    simp [he, routeDomain]
  | succ d ih =>
    let v := butterflyPerm d (decodeButterfly d (fun i => ω (Sum.inr (x 0,i)))) (Fin.tail x)
    change Fin.cons (Bool.xor (x 0) (ω (Sum.inl v))) v = y ↔ _
    have hv : v = Fin.tail y ↔
        ∀ i ∈ routeDomain d (Fin.tail x) (Fin.tail y),
          ω (Sum.inr (x 0,i)) = routeValue d (Fin.tail x) (Fin.tail y) i :=
      ih _ _ _
    constructor
    · intro h i hi
      have ht : v = Fin.tail y := by simpa using congrArg Fin.tail h
      have hh : ω (Sum.inl (Fin.tail y)) = Bool.xor (x 0) (y 0) := by
        have he := congrFun h 0
        simp only [Fin.cons_zero, ht] at he
        exact (xor_eq_iff _ _ _).mp he
      rcases Finset.mem_insert.mp hi with htop | hchild
      · subst i
        exact hh
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hchild
        exact hv.mp ht j hj
    · intro h
      have hh := h (Sum.inl (Fin.tail y)) (Finset.mem_insert_self _ _)
      have ht : v = Fin.tail y := hv.mpr (fun i hi =>
        h (Sum.inr (x 0,i)) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hi)))
      have hh' : Bool.xor (x 0) (ω (Sum.inl (Fin.tail y))) = y 0 :=
        (xor_eq_iff _ _ _).mpr hh
      rw [ht, hh', Fin.cons_self_tail]

def switchUsers : (d : ℕ) → Butterfly d → SwitchIndex d → Card d × Card d
  | 0, _, i => nomatch i
  | d + 1, b, Sum.inl y =>
      (Fin.cons false ((butterflyPerm d (b.2 false)).symm y),
       Fin.cons true ((butterflyPerm d (b.2 true)).symm y))
  | d + 1, b, Sum.inr (ε,i) =>
      (Fin.cons ε (switchUsers d (b.2 ε) i).1,
       Fin.cons ε (switchUsers d (b.2 ε) i).2)

lemma switchUsers_ne (d : ℕ) (b : Butterfly d) (i : SwitchIndex d) :
    (switchUsers d b i).1 ≠ (switchUsers d b i).2 := by
  induction d with
  | zero => exact Empty.elim i
  | succ d ih =>
    cases i with
    | inl y =>
      intro h
      have := congrFun h 0
      simp only [switchUsers, Fin.cons_zero] at this
      exact Bool.false_ne_true this
    | inr z =>
      intro h
      exact ih (b.2 z.1) z.2 (by simpa only [switchUsers, Fin.tail_cons] using congrArg Fin.tail h)

lemma cons_eq_iff {d : ℕ} (ε : Bool) (a : Card d) (x : Card (d + 1)) :
    Fin.cons ε a = x ↔ ε = x 0 ∧ a = Fin.tail x := by
  constructor
  · intro h
    exact ⟨by simpa only [Fin.cons_zero] using congrFun h 0,
      by simpa only [Fin.tail_cons] using congrArg Fin.tail h⟩
  · rintro ⟨rfl,rfl⟩
    exact Fin.cons_self_tail x

lemma mem_routeDomain_iff_user (d : ℕ) (b : Butterfly d) (x : Card d) (i : SwitchIndex d) :
    i ∈ routeDomain d x (butterflyPerm d b x) ↔
      (switchUsers d b i).1 = x ∨ (switchUsers d b i).2 = x := by
  classical
  induction d with
  | zero => exact Empty.elim i
  | succ d ih =>
    cases i with
    | inl y =>
      change Sum.inl y ∈ insert (Sum.inl (Fin.tail (butterflyPerm (d+1) b x)))
        ((routeDomain d (Fin.tail x) (Fin.tail (butterflyPerm (d+1) b x))).image
          (fun i => (Sum.inr (x 0,i) : Sum (Card d) (Bool × SwitchIndex d)))) ↔ _
      simp only [Finset.mem_insert, Sum.inl.injEq, Finset.mem_image,
        Sum.inr_ne_inl, and_false, exists_false, or_false]
      change y = butterflyPerm d (b.2 (x 0)) (Fin.tail x) ↔ _
      simp only [switchUsers, cons_eq_iff]
      cases x 0 <;> simp [Equiv.symm_apply_eq]
    | inr z =>
      obtain ⟨ε,i⟩ := z
      change Sum.inr (ε,i) ∈ insert (Sum.inl (Fin.tail (butterflyPerm (d+1) b x)))
        ((routeDomain d (Fin.tail x) (Fin.tail (butterflyPerm (d+1) b x))).image
          (fun i => (Sum.inr (x 0,i) : Sum (Card d) (Bool × SwitchIndex d)))) ↔ _
      simp only [Finset.mem_insert, Sum.inr_ne_inl, false_or, Finset.mem_image,
        Sum.inr.injEq, Prod.mk.injEq]
      change (∃ j, j ∈ routeDomain d (Fin.tail x) (butterflyPerm d (b.2 (x 0)) (Fin.tail x)) ∧
        x 0 = ε ∧ j = i) ↔ _
      simp only [switchUsers, cons_eq_iff]
      constructor
      · rintro ⟨j,hj,hε,rfl⟩
        subst ε
        rcases (ih (b.2 (x 0)) (Fin.tail x) j).mp hj with h | h
        · exact Or.inl ⟨rfl,h⟩
        · exact Or.inr ⟨rfl,h⟩
      · rintro (⟨hε,h⟩ | ⟨hε,h⟩)
        · subst ε
          exact ⟨i,(ih (b.2 (x 0)) (Fin.tail x) i).mpr (Or.inl h),rfl,rfl⟩
        · subst ε
          exact ⟨i,(ih (b.2 (x 0)) (Fin.tail x) i).mpr (Or.inr h),rfl,rfl⟩

lemma mem_childMarks {d : ℕ} (s : Finset (Card (d + 1))) (ε : Bool) (x : Card d) :
    x ∈ childMarks s ε ↔ Fin.cons ε x ∈ s := by
  classical
  constructor
  · intro h
    obtain ⟨y,hy,hxy⟩ := Finset.mem_image.mp h
    obtain ⟨hys,hyε⟩ := Finset.mem_filter.mp hy
    rw [← hxy, ← hyε, Fin.cons_self_tail]
    exact hys
  · intro h
    exact Finset.mem_image.mpr ⟨Fin.cons ε x,
      Finset.mem_filter.mpr ⟨h,by simp⟩,by simp⟩

lemma mem_topMeetings {d : ℕ} (b : Butterfly (d + 1))
    (s : Finset (Card (d + 1))) (y : Card d) :
    y ∈ topMeetings b s ↔
      (switchUsers (d+1) b (Sum.inl y)).1 ∈ s ∧
      (switchUsers (d+1) b (Sum.inl y)).2 ∈ s := by
  classical
  have he (ε : Bool) : y ∈ (childMarks s ε).image (butterflyPerm d (b.2 ε)) ↔
      (butterflyPerm d (b.2 ε)).symm y ∈ childMarks s ε := by
    constructor
    · intro h
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp h
      simpa only [Equiv.symm_apply_apply] using hx
    · intro h
      exact Finset.mem_image.mpr ⟨_,h,Equiv.apply_symm_apply _ _⟩
  simp only [topMeetings, Finset.mem_inter, he, mem_childMarks, switchUsers]

lemma encounters_eq_switch_sum (d : ℕ) (b : Butterfly d) (s : Finset (Card d)) :
    encounters d b s = ∑ i : SwitchIndex d,
      if (switchUsers d b i).1 ∈ s ∧ (switchUsers d b i).2 ∈ s then 1 else 0 := by
  classical
  induction d with
  | zero =>
    simp only [encounters]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact Empty.elim i
  | succ d ih =>
    change encounters d (b.2 false) (childMarks s false) +
      encounters d (b.2 true) (childMarks s true) + (topMeetings b s).card =
        ∑ i : Sum (Card d) (Bool × SwitchIndex d), _
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    rw [ih,ih]
    have ht : (∑ y : Card d,
        if (switchUsers (d+1) b (Sum.inl y)).1 ∈ s ∧
          (switchUsers (d+1) b (Sum.inl y)).2 ∈ s then 1 else 0) =
        (topMeetings b s).card := by
      simp only [← mem_topMeetings]
      simp
    rw [ht]
    simp only [mem_childMarks, switchUsers]
    ac_rfl

lemma marked_switch_entropy_bound (d : ℕ) (b : Butterfly d) (s : Finset (Card d)) :
    (∑ i : SwitchIndex d,
      if (switchUsers d b i).1 ∈ s ∧ (switchUsers d b i).2 ∈ s then (1:ℝ) else 0) ≤
      (s.card : ℝ) * Real.log s.card / (2 * Real.log 2) := by
  classical
  have he : (encounters d b s : ℝ) =
      ∑ i : SwitchIndex d,
        if (switchUsers d b i).1 ∈ s ∧ (switchUsers d b i).2 ∈ s then (1:ℝ) else 0 := by
    rw [encounters_eq_switch_sum, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [← he]
  exact butterfly_encounters d b s

namespace QueryTree
variable {ι : Type*} [DecidableEq ι]

def memo : QueryTree ι → Finset ι → (ι → Bool) → QueryTree ι
  | reject, _, _ => reject
  | accept, _, _ => accept
  | branch i zero one, R, η =>
      if i ∈ R then (if η i then memo one R η else memo zero R η) else
      branch i (memo zero (insert i R) (Function.update η i false))
        (memo one (insert i R) (Function.update η i true))
  | force i b next, R, η =>
      if i ∈ R then (if η i = b then memo next R η else reject) else
      force i b (memo next (insert i R) (Function.update η i b))

def freshCharge : QueryTree ι → Finset ι → (ι → Bool) → ℕ
  | reject, _, _ => 0
  | accept, _, _ => 0
  | branch i zero one, R, ω => if ω i then freshCharge one (insert i R) ω else freshCharge zero (insert i R) ω
  | force i b next, R, ω => if ω i = b then
      freshCharge next (insert i R) ω + (if i ∈ R then 0 else 1) else 0


def followPath : (d : ℕ) → (SwitchIndex d → ι) → Card d →
    (Card d → QueryTree ι) → QueryTree ι
  | 0, _, x, k => k x
  | d + 1, e, x, k => followPath d (fun i => e (Sum.inr (x 0,i))) (Fin.tail x)
      (fun y => branch (e (Sum.inl y))
        (k (Fin.cons (Bool.xor (x 0) false) y))
        (k (Fin.cons (Bool.xor (x 0) true) y)))

omit [DecidableEq ι] in
lemma followPath_succeeds (d : ℕ) (e : SwitchIndex d → ι) (x : Card d)
    (k : Card d → QueryTree ι) (ω : ι → Bool) :
    (followPath d e x k).succeeds ω =
      (k (butterflyPerm d (decodeButterfly d (ω ∘ e)) x)).succeeds ω := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [followPath, ih]
    let y := butterflyPerm d
      (decodeButterfly d (fun i => ω (e (Sum.inr (x 0,i))))) (Fin.tail x)
    change (if ω (e (Sum.inl y)) then
      (k (Fin.cons (Bool.xor (x 0) true) y)).succeeds ω else
      (k (Fin.cons (Bool.xor (x 0) false) y)).succeeds ω) =
      (k (Fin.cons (Bool.xor (x 0) (ω (e (Sum.inl y)))) y)).succeeds ω
    cases ω (e (Sum.inl y)) <;> rfl

lemma followPath_charge (d : ℕ) (e : SwitchIndex d → ι) (x : Card d)
    (k : Card d → QueryTree ι) (R : Finset ι) (ω : ι → Bool) :
    freshCharge (followPath d e x k) R ω =
      freshCharge (k (butterflyPerm d (decodeButterfly d (ω ∘ e)) x))
        (R ∪ (routeDomain d x (butterflyPerm d (decodeButterfly d (ω ∘ e)) x)).image e) ω := by
  classical
  induction d generalizing R with
  | zero => simp only [followPath, routeDomain, Finset.image_empty, Finset.union_empty]; rfl
  | succ d ih =>
    rw [followPath, ih]
    let y := butterflyPerm d
      (decodeButterfly d (fun i => ω (e (Sum.inr (x 0,i))))) (Fin.tail x)
    let S := (routeDomain d (Fin.tail x) y).image (fun i => e (Sum.inr (x 0,i)))
    change (if ω (e (Sum.inl y)) then
      freshCharge (k (Fin.cons (Bool.xor (x 0) true) y)) (insert (e (Sum.inl y)) (R ∪ S)) ω else
      freshCharge (k (Fin.cons (Bool.xor (x 0) false) y)) (insert (e (Sum.inl y)) (R ∪ S)) ω) =
      freshCharge (k (Fin.cons (Bool.xor (x 0) (ω (e (Sum.inl y)))) y))
        (R ∪ (routeDomain (d+1) x
          (Fin.cons (Bool.xor (x 0) (ω (e (Sum.inl y)))) y)).image e) ω
    have hs : (routeDomain (d+1) x
        (Fin.cons (Bool.xor (x 0) (ω (e (Sum.inl y)))) y)).image e =
        insert (e (Sum.inl y)) S := by
      let e' : Sum (Card d) (Bool × SwitchIndex d) → ι := e
      change (insert (Sum.inl y)
        ((routeDomain d (Fin.tail x) y).image
          (fun i => (Sum.inr (x 0,i) : Sum (Card d) (Bool × SwitchIndex d)))) :
          Finset (Sum (Card d) (Bool × SwitchIndex d))).image e' = _
      rw [Finset.image_insert, Finset.image_image]
      rfl
    rw [hs,Finset.union_insert]
    cases ω (e (Sum.inl y)) <;> rfl

def forceList : List ι → (ι → Bool) → QueryTree ι → QueryTree ι
  | [], _, k => k
  | i :: L, v, k => force i (v i) (forceList L v k)

omit [DecidableEq ι] in
lemma forceList_succeeds (L : List ι) (v : ι → Bool) (k : QueryTree ι) (ω : ι → Bool) :
    (forceList L v k).succeeds ω =
      if ∀ i ∈ L, ω i = v i then k.succeeds ω else false := by
  induction L with
  | nil => simp [forceList]
  | cons i L ih =>
    simp only [forceList,succeeds,ih,List.mem_cons,forall_eq_or_imp]
    by_cases h : ω i = v i <;> simp [h]

lemma forceList_charge (L : List ι) (v : ι → Bool) (k : QueryTree ι)
    (R : Finset ι) (ω : ι → Bool) (h : ∀ i ∈ L, ω i = v i) :
    freshCharge (forceList L v k) R ω =
      freshCharge k (R ∪ L.toFinset) ω + (L.toFinset \ R).card := by
  induction L generalizing R with
  | nil => simp [forceList]
  | cons i L ih =>
    rw [forceList,freshCharge,ite_eq_left (h i List.mem_cons_self),
      ih (insert i R) (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    simp only [List.toFinset_cons]
    have hs : insert i R ∪ L.toFinset = R ∪ insert i L.toFinset := by ext j; simp
    rw [hs]
    by_cases hi : i ∈ R
    · rw [ite_eq_left hi]
      have he : L.toFinset \ insert i R = insert i L.toFinset \ R := by
        ext j
        by_cases hji : j = i
        · subst j; simp [hi]
        · simp [hji]
      rw [he,Nat.add_zero]
    · rw [ite_eq_right hi]
      have he : insert i L.toFinset \ R = insert i (L.toFinset \ insert i R) := by
        ext j
        by_cases hji : j = i
        · subst j; simp [hi]
        · simp [hji]
      rw [he, Finset.card_insert_of_notMem (by simp)]
      omega


def staleCharge : QueryTree ι → Finset ι → (ι → Bool) → ℕ
  | reject, _, _ => 0
  | accept, _, _ => 0
  | branch i zero one, R, ω => if ω i then staleCharge one (insert i R) ω
      else staleCharge zero (insert i R) ω
  | force i b next, R, ω => if ω i = b then
      staleCharge next (insert i R) ω + (if i ∈ R then 1 else 0) else 0

lemma fresh_add_stale (T : QueryTree ι) (R : Finset ι) (ω : ι → Bool) :
    T.freshCharge R ω + T.staleCharge R ω = T.charge ω := by
  induction T generalizing R with
  | reject => rfl
  | accept => rfl
  | branch i zero one ih₀ ih₁ =>
    cases hb : ω i <;> simp [freshCharge,staleCharge,charge,hb,ih₀,ih₁]
  | force i b next ih =>
    by_cases hb : ω i = b
    · simp only [freshCharge,staleCharge,charge,hb,↓reduceIte]
      have he := ih (insert i R)
      by_cases hi : i ∈ R <;> simp only [hi,↓reduceIte] <;> omega
    · simp [freshCharge,staleCharge,charge,hb]

omit [DecidableEq ι] in
lemma followPath_raw_charge (d : ℕ) (e : SwitchIndex d → ι) (x : Card d)
    (k : Card d → QueryTree ι) (ω : ι → Bool) :
    (followPath d e x k).charge ω =
      (k (butterflyPerm d (decodeButterfly d (ω ∘ e)) x)).charge ω := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [followPath, ih]
    let y := butterflyPerm d
      (decodeButterfly d (fun i => ω (e (Sum.inr (x 0,i))))) (Fin.tail x)
    change (if ω (e (Sum.inl y)) then
      (k (Fin.cons (Bool.xor (x 0) true) y)).charge ω else
      (k (Fin.cons (Bool.xor (x 0) false) y)).charge ω) =
      (k (Fin.cons (Bool.xor (x 0) (ω (e (Sum.inl y)))) y)).charge ω
    cases ω (e (Sum.inl y)) <;> rfl

omit [DecidableEq ι] in
lemma forceList_raw_charge (L : List ι) (v : ι → Bool) (k : QueryTree ι) (ω : ι → Bool)
    (h : ∀ i ∈ L, ω i = v i) :
    (forceList L v k).charge ω = k.charge ω + L.length := by
  induction L with
  | nil => simp [forceList]
  | cons i L ih =>
    rw [forceList,charge,ite_eq_left (h i List.mem_cons_self),
      ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    simp only [List.length_cons,Nat.add_assoc]

end QueryTree

lemma finiteMean_sum {Ω α : Type*} [Fintype Ω] (s : Finset α) (f : α → Ω → ℝ) :
    finiteMean (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, finiteMean (f i) := by
  simp only [finiteMean,Finset.sum_div]
  exact Finset.sum_comm

end Thorp

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_RotationMeeting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp
open scoped BigOperators
open Filter

section OrbitCore
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def orbitSet (p : Equiv.Perm α) (x : α) : Finset α :=
  Finset.univ.filter (p.SameCycle x)

@[simp] lemma mem_orbitSet (p : Equiv.Perm α) (x y : α) :
    y ∈ orbitSet p x ↔ p.SameCycle x y := by
  classical
  simp [orbitSet]

lemma orbitSet_nonempty (p : Equiv.Perm α) (x : α) : (orbitSet p x).Nonempty :=
  ⟨x,(mem_orbitSet _ _ _).mpr (Equiv.Perm.SameCycle.refl _ _)⟩

lemma orbitSet_eq (p : Equiv.Perm α) {x y : α} (h : p.SameCycle x y) :
    orbitSet p x = orbitSet p y := by
  ext z
  simp only [mem_orbitSet]
  exact ⟨fun hz => h.symm.trans hz,fun hz => h.trans hz⟩

@[simp] lemma orbitSet_apply (p : Equiv.Perm α) (x : α) : orbitSet p (p x) = orbitSet p x := by
  ext y
  simp only [mem_orbitSet,Equiv.Perm.sameCycle_apply_left]

def walkSet (p : Equiv.Perm α) (r : ℕ) (x : α) : Finset α :=
  (Finset.range r).image (fun n => p^[n] x)

omit [Fintype α] in
@[simp] lemma mem_walkSet (p : Equiv.Perm α) (r : ℕ) (x y : α) :
    y ∈ walkSet p r x ↔ ∃ n < r, p^[n] x = y := by
  simp [walkSet]

omit [Fintype α] in
@[simp] lemma walkSet_zero (p : Equiv.Perm α) (x : α) : walkSet p 0 x = ∅ := by
  simp [walkSet]

def cycleTrace (p : Equiv.Perm α) (S : Finset α) (a : α) :
    ℕ → α → Finset α → Option (Finset α × α)
  | 0, x, V => if x ∈ S ∧ x ∉ V ∧ p x = a then some (insert x V,x) else none
  | r+1, x, V => if x ∈ S ∧ x ∉ V then cycleTrace p S a r (p x) (insert x V) else none

end OrbitCore

namespace QueryTree

lemma followPath_stale_charge {ι : Type*} [DecidableEq ι]
    (d : ℕ) (e : SwitchIndex d → ι) (x : Card d)
    (k : Card d → QueryTree ι) (R : Finset ι) (ω : ι → Bool) :
    staleCharge (followPath d e x k) R ω =
      staleCharge (k (butterflyPerm d (decodeButterfly d (ω ∘ e)) x))
        (R ∪ (routeDomain d x (butterflyPerm d (decodeButterfly d (ω ∘ e)) x)).image e) ω := by
  have h₀ := fresh_add_stale (followPath d e x k) R ω
  have h₁ := fresh_add_stale (k (butterflyPerm d (decodeButterfly d (ω ∘ e)) x))
    (R ∪ (routeDomain d x (butterflyPerm d (decodeButterfly d (ω ∘ e)) x)).image e) ω
  rw [followPath_charge,followPath_raw_charge] at h₀
  omega

end QueryTree

section Collections
variable {d A : ℕ}

noncomputable def rotationLower (d : ℕ) {A : ℕ} (r : Fin A → ℕ) : ℝ :=
  Real.exp (-Real.log 2 * ((A:ℝ)*d/2 + ∑ i : Fin A, Real.log (r i+1) / (2 * Real.log 2)))

noncomputable def collectionWeight (d : ℕ) {A : ℕ} (r : Fin A → ℕ) : ℝ :=
  ((2:ℝ)^d)^A * (∏ i : Fin A, (r i+1 : ℝ)) * rotationLower d r

end Collections

variable {d A : ℕ}

abbrev SelectedCycle (p : Equiv.Perm (Card d)) (S : Finset (Card d)) :=
  {C : Finset (Card d) // (∃ x, C = orbitSet p x) ∧ C ⊆ S}

noncomputable instance instFintypeSelectedCycle (p : Equiv.Perm (Card d)) (S : Finset (Card d)) :
    Fintype (SelectedCycle p S) := Fintype.ofFinite _

end Thorp

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_AssignmentSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp
open scoped BigOperators
open Filter

structure RoutingNetwork (α ι : Type*) [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι] (d : ℕ) where
  perm : (ι → Bool) → Equiv.Perm α
  path : (ι → Bool) → α → Finset ι
  users : (ι → Bool) → ι → α × α
  users_ne : ∀ ω i, (users ω i).1 ≠ (users ω i).2
  mem_path : ∀ ω x i, i ∈ path ω x ↔ (users ω i).1 = x ∨ (users ω i).2 = x
  card_path : ∀ ω x, (path ω x).card = d
  entropy : ∀ ω (S : Finset α),
    (∑ i : ι, if (users ω i).1 ∈ S ∧ (users ω i).2 ∈ S then (1:ℝ) else 0) ≤
      (S.card : ℝ) * Real.log S.card / (2 * Real.log 2)
  follow : α → (α → QueryTree ι) → QueryTree ι
  close : α → α → QueryTree ι → QueryTree ι
  follow_succeeds : ∀ x k ω, (follow x k).succeeds ω = (k (perm ω x)).succeeds ω
  follow_raw_charge : ∀ x k ω, (follow x k).charge ω = (k (perm ω x)).charge ω
  follow_stale_charge : ∀ x k R ω,
    (follow x k).staleCharge R ω = (k (perm ω x)).staleCharge (R ∪ path ω x) ω
  close_succeeds : ∀ x y k ω,
    (close x y k).succeeds ω = if perm ω x = y then k.succeeds ω else false
  close_raw_charge : ∀ x y k ω, perm ω x = y → (close x y k).charge ω = k.charge ω + d
  close_stale_charge : ∀ x y k R ω, perm ω x = y →
    (close x y k).staleCharge R ω = k.staleCharge (R ∪ path ω x) ω + (path ω x ∩ R).card

namespace RoutingNetwork
variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
  {d : ℕ} (R : RoutingNetwork α ι d)

section Rotation
variable {A : ℕ}

def cycleFiber (o : α → Option (Fin A)) (i : Fin A) : Finset (α) := by
  classical
  exact Finset.univ.filter (fun x => o x = some i)

omit [DecidableEq α] in
@[simp] lemma mem_cycleFiber (o : α → Option (Fin A)) (i : Fin A) (x : α) :
    x ∈ cycleFiber o i ↔ o x = some i := by
  classical
  simp [cycleFiber]

abbrev Terminal (o : α → Option (Fin A)) := ∀ i : Fin A, {x : α // o x = some i}

noncomputable def slotWeight (o : α → Option (Fin A)) (i : Fin A) : ℝ :=
  1 / (cycleFiber o i).card

noncomputable def pathWeight (o : α → Option (Fin A)) (x : α) : ℝ :=
  match o x with
  | none => 0
  | some i => slotWeight o i

noncomputable def withinWeight (o : α → Option (Fin A)) (u v : α) : ℝ :=
  match o u, o v with
  | some i, some j => if i = j then slotWeight o i else 0
  | _, _ => 0

noncomputable def rotationMeeting (o : α → Option (Fin A)) (z : Terminal o)
    (u v : α) : ℝ :=
  match o u, o v with
  | some i, some j => if i < j then (if (z j).val = v then 1 else 0)
      else if j < i then (if (z i).val = u then 1 else 0)
      else (if (z i).val = u then 1 else 0) + (if (z i).val = v then 1 else 0)
  | _, _ => 0

noncomputable def rotationCharge (o : α → Option (Fin A)) (b : ι → Bool)
    (z : Terminal o) : ℝ :=
  ∑ s : ι, rotationMeeting o z (R.users b s).1 (R.users b s).2

end Rotation

namespace QueryTree
open Thorp.QueryTree

noncomputable def seekCycle (R : RoutingNetwork α ι d) (S : Finset (α)) (a : α) :
    ℕ → α → Finset (α) → (Finset (α) → QueryTree (ι)) →
      QueryTree (ι)
  | 0, x, V, k => if x ∈ S ∧ x ∉ V then R.close x a (k (insert x V)) else reject
  | r + 1, x, V, k => if x ∈ S ∧ x ∉ V then R.follow x
      (fun y => seekCycle R S a r y (insert x V) k) else reject

noncomputable def seekCycles (R : RoutingNetwork α ι d) (S : Finset (α)) :
    List (α × ℕ) → Finset (α) → QueryTree (ι)
  | [], _ => accept
  | (a,r) :: L, V => seekCycle R S a r a V (fun V => seekCycles R S L V)

end QueryTree
noncomputable def exposedPaths (b : ι → Bool) (V : Finset (α)) :
    Finset (ι) :=
  V.biUnion (fun x => R.path b x)

@[simp] lemma exposedPaths_empty (b : ι → Bool) : exposedPaths R b ∅ = ∅ := by
  classical
  simp [exposedPaths]

noncomputable def terminalCharge (b : ι → Bool) (z : α) (V : Finset (α)) : ℕ :=
  (R.path b z ∩ exposedPaths R b V).card

end RoutingNetwork
end Thorp

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_PriorPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp
open scoped BigOperators
open Filter
namespace RoutingNetwork
variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
  {d : ℕ} (R : RoutingNetwork α ι d)

noncomputable def priorPaths {A : ℕ} (o : α → Option (Fin A)) (t : ℕ) : Finset (α) :=
  Finset.univ.filter (fun x => ∃ i : Fin A, o x = some i ∧ i.val < t)

omit [DecidableEq α] in
@[simp] lemma mem_priorPaths {A : ℕ} (o : α → Option (Fin A)) (t : ℕ) (x : α) :
    x ∈ priorPaths o t ↔ ∃ i : Fin A, o x = some i ∧ i.val < t := by
  classical
  simp [priorPaths]

omit [DecidableEq α] in
@[simp] lemma priorPaths_zero {A : ℕ} (o : α → Option (Fin A)) : priorPaths o 0 = ∅ := by
  classical
  ext x
  simp

section Collections
variable {A : ℕ}

def ValidCycleSlots (p : Equiv.Perm (α)) (S : Finset (α)) (r : Fin A → ℕ)
    (o : α → Option (Fin A)) : Prop :=
  (∀ i, (cycleFiber o i).card = r i + 1) ∧
  (∀ i, cycleFiber o i ⊆ S) ∧
  (∀ i x, o x = some i → orbitSet p x = cycleFiber o i)

abbrev CycleSlots (p : Equiv.Perm (α)) (S : Finset (α)) (r : Fin A → ℕ) :=
  {o : α → Option (Fin A) // ValidCycleSlots p S r o}

noncomputable instance instFintypeCycleSlots (p : Equiv.Perm (α)) (S : Finset (α)) (r : Fin A → ℕ) :
    Fintype (CycleSlots p S r) := Fintype.ofFinite _

lemma CycleSlots.terminal_nonempty {p : Equiv.Perm (α)} {S : Finset (α)} {r : Fin A → ℕ}
    (c : CycleSlots p S r) (i : Fin A) : Nonempty {x : α // c.val x = some i} := by
  have hn : (cycleFiber c.val i).Nonempty := Finset.card_pos.mp (by rw [c.property.1]; omega)
  obtain ⟨x,hx⟩ := hn
  exact ⟨x,(mem_cycleFiber _ _ _).mp hx⟩

omit [DecidableEq α] in
lemma owner_ext {o o' : α → Option (Fin A)}
    (h : ∀ i, cycleFiber o i = cycleFiber o' i) : o = o' := by
  funext x
  have he (i : Fin A) : o x = some i ↔ o' x = some i := by
    simpa only [mem_cycleFiber] using (Finset.ext_iff.mp (h i) x)
  cases ho : o x with
  | some i => exact ((he i).mp ho).symm
  | none =>
    cases ho' : o' x with
    | none => rfl
    | some i => have hn := (he i).mpr ho'; rw [ho] at hn; contradiction

abbrev RootedSlots (p : Equiv.Perm (α)) (S : Finset (α)) (r : Fin A → ℕ) :=
  Σ c : CycleSlots p S r, Terminal c.val

noncomputable def rootedStart {p : Equiv.Perm (α)} {S : Finset (α)} {r : Fin A → ℕ}
    (c : RootedSlots p S r) : Fin A → S := fun i =>
  ⟨p (c.2 i).val,c.1.property.2.1 i (by
    rw [←c.1.property.2.2 i (c.2 i).val (c.2 i).property]
    exact (mem_orbitSet _ _ _).mpr (Equiv.Perm.SameCycle.apply_right (Equiv.Perm.SameCycle.refl p _)))⟩

end Collections

section CycleCounting
variable {A : ℕ}

abbrev SelectedCycle (p : Equiv.Perm (α)) (S : Finset (α)) :=
  {C : Finset (α) // (∃ x, C = orbitSet p x) ∧ C ⊆ S}

noncomputable instance instFintypeSelectedCycle (p : Equiv.Perm (α)) (S : Finset (α)) :
    Fintype (SelectedCycle p S) := Fintype.ofFinite _

lemma SelectedCycle.nonempty {p : Equiv.Perm (α)} {S : Finset (α)}
    (C : SelectedCycle p S) : C.val.Nonempty := by
  obtain ⟨x,hx⟩ := C.property.1
  rw [hx]
  exact orbitSet_nonempty p x

lemma SelectedCycle.orbit_eq {p : Equiv.Perm (α)} {S : Finset (α)}
    (C : SelectedCycle p S) {x : α} (hx : x ∈ C.val) : orbitSet p x = C.val := by
  obtain ⟨y,hy⟩ := C.property.1
  rw [hy] at hx ⊢
  exact (orbitSet_eq p ((mem_orbitSet _ _ _).mp hx)).symm

lemma SelectedCycle.eq_of_mem {p : Equiv.Perm (α)} {S : Finset (α)}
    (C D : SelectedCycle p S) {x : α} (hC : x ∈ C.val) (hD : x ∈ D.val) : C = D := by
  apply Subtype.ext
  exact (C.orbit_eq hC).symm.trans (D.orbit_eq hD)

abbrev SlotAssignment (p : Equiv.Perm (α)) (S : Finset (α)) (r : Fin A → ℕ) :=
  {f : Fin A → SelectedCycle p S // Function.Injective f ∧ ∀ i, (f i).val.card = r i+1}

noncomputable instance instFintypeSlotAssignment (p : Equiv.Perm (α)) (S : Finset (α)) (r : Fin A → ℕ) :
    Fintype (SlotAssignment p S r) := Fintype.ofFinite _

noncomputable def slotsToAssignment {p : Equiv.Perm (α)} {S : Finset (α)} {r : Fin A → ℕ}
    (c : CycleSlots p S r) : SlotAssignment p S r := by
  classical
  let f (i : Fin A) : SelectedCycle p S := ⟨cycleFiber c.val i,by
    obtain ⟨x,hx⟩ := c.terminal_nonempty i
    exact ⟨⟨x,(c.property.2.2 i x hx).symm⟩,c.property.2.1 i⟩⟩
  refine ⟨f,?_,fun i => c.property.1 i⟩
  intro i j hij
  have he : cycleFiber c.val i = cycleFiber c.val j := congrArg Subtype.val hij
  obtain ⟨x,hx⟩ := c.terminal_nonempty i
  have hxi : x ∈ cycleFiber c.val i := (mem_cycleFiber _ _ _).mpr hx
  rw [he] at hxi
  exact Option.some.inj (hx.symm.trans ((mem_cycleFiber _ _ _).mp hxi))

noncomputable def assignmentOwner {p : Equiv.Perm (α)} {S : Finset (α)} {r : Fin A → ℕ}
    (f : SlotAssignment p S r) (x : α) : Option (Fin A) := by
  classical
  exact if h : ∃ i, x ∈ (f.val i).val then some (Classical.choose h) else none

lemma assignmentOwner_eq_some {p : Equiv.Perm (α)} {S : Finset (α)} {r : Fin A → ℕ}
    (f : SlotAssignment p S r) (x : α) (i : Fin A) :
    assignmentOwner f x = some i ↔ x ∈ (f.val i).val := by
  classical
  unfold assignmentOwner
  split_ifs with h
  · constructor
    · intro hi
      have hx := Classical.choose_spec h
      rw [Option.some.inj hi] at hx
      exact hx
    · intro hx
      have he := (f.val (Classical.choose h)).eq_of_mem (f.val i) (Classical.choose_spec h) hx
      exact congrArg some (f.property.1 he)
  · constructor
    · intro hi; contradiction
    · intro hx; exact (h ⟨i,hx⟩).elim

lemma assignmentOwner_fiber {p : Equiv.Perm (α)} {S : Finset (α)} {r : Fin A → ℕ}
    (f : SlotAssignment p S r) (i : Fin A) : cycleFiber (assignmentOwner f) i = (f.val i).val := by
  ext x
  simp only [mem_cycleFiber,assignmentOwner_eq_some]

noncomputable def assignmentToSlots {p : Equiv.Perm (α)} {S : Finset (α)} {r : Fin A → ℕ}
    (f : SlotAssignment p S r) : CycleSlots p S r :=
  ⟨assignmentOwner f,by
    refine ⟨?_,?_,?_⟩
    · intro i
      rw [assignmentOwner_fiber]
      exact f.property.2 i
    · intro i
      rw [assignmentOwner_fiber]
      exact (f.val i).property.2
    · intro i x hx
      rw [assignmentOwner_fiber]
      exact (f.val i).orbit_eq ((assignmentOwner_eq_some f x i).mp hx)⟩

noncomputable def cycleSlotsEquivAssignments (p : Equiv.Perm (α)) (S : Finset (α)) (r : Fin A → ℕ) :
    CycleSlots p S r ≃ SlotAssignment p S r where
  toFun := slotsToAssignment
  invFun := assignmentToSlots
  left_inv c := by
    apply Subtype.ext
    apply owner_ext
    intro i
    rw [assignmentToSlots,assignmentOwner_fiber]
    rfl
  right_inv f := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact assignmentOwner_fiber f i

end CycleCounting

section AllLengths
variable {A : ℕ}

noncomputable def assignmentRelabel (p : Equiv.Perm (α)) (S : Finset (α))
    (r : Fin A → ℕ) (e : Equiv.Perm (Fin A)) :
    SlotAssignment p S r ≃ SlotAssignment p S (r ∘ e) where
  toFun f := ⟨f.val ∘ e, f.property.1.comp e.injective, fun i => f.property.2 (e i)⟩
  invFun f := ⟨f.val ∘ e.symm, f.property.1.comp e.symm.injective, fun i => by
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using f.property.2 (e.symm i)⟩
  left_inv f := by apply Subtype.ext; funext i; simp
  right_inv f := by apply Subtype.ext; funext i; simp

abbrev ShortCycle (p : Equiv.Perm (α)) (S : Finset (α)) (J : ℕ) :=
  {C : SelectedCycle p S // C.val.card ≤ J}

noncomputable instance instFintypeShortCycle (p : Equiv.Perm (α)) (S : Finset (α)) (J : ℕ) :
    Fintype (ShortCycle p S J) := Fintype.ofFinite _

noncomputable def shortCycleLength {p : Equiv.Perm (α)} {S : Finset (α)} {J : ℕ}
    (C : ShortCycle p S J) : Fin J :=
  ⟨C.val.val.card-1, by have := C.val.nonempty.card_pos; have := C.property; omega⟩

lemma shortCycleLength_add_one {p : Equiv.Perm (α)} {S : Finset (α)} {J : ℕ}
    (C : ShortCycle p S J) : (shortCycleLength C : ℕ)+1 = C.val.val.card := by
  have := C.val.nonempty.card_pos
  simp only [shortCycleLength]
  omega

noncomputable def shortEmbeddingEquiv (p : Equiv.Perm (α)) (S : Finset (α)) (J : ℕ) :
    (Fin A ↪ ShortCycle p S J) ≃
      Σ r : Fin A → Fin J, SlotAssignment p S (fun i => (r i : ℕ)) where
  toFun f := ⟨fun i => shortCycleLength (f i),
    ⟨fun i => (f i).val, fun i j h => f.injective (Subtype.ext h),
      fun i => (shortCycleLength_add_one (f i)).symm⟩⟩
  invFun c :=
    { toFun := fun i => ⟨c.2.val i, by rw [c.2.property.2]; exact (c.1 i).isLt⟩
      inj' := fun _i _j h => c.2.property.1 (congrArg Subtype.val h) }
  left_inv f := by
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv c := by
    rcases c with ⟨r,f⟩
    have he : (fun i => shortCycleLength (⟨f.val i, by rw [f.property.2]; exact (r i).isLt⟩ : ShortCycle p S J)) = r := by
      funext i
      apply Fin.ext
      simp only [shortCycleLength,f.property.2,Nat.add_sub_cancel]
    apply Sigma.ext he
    apply (Subtype.heq_iff_coe_eq (by
      intro x
      change (Function.Injective x ∧ ∀ i, (x i).val.card = (f.val i).val.card - 1 + 1) ↔ _
      simp only [f.property.2,Nat.add_sub_cancel])).mpr
    rfl

end AllLengths

section CycleMGF

noncomputable def cycleMass (p : Equiv.Perm (α)) (S : Finset (α)) : ℕ :=
  ∑ C : SelectedCycle p S, C.val.card

end CycleMGF


abbrev LongCycle (p : Equiv.Perm (α)) (S : Finset (α)) (J : ℕ) :=
  {C : SelectedCycle p S // ¬ C.val.card ≤ J}
noncomputable instance instFintypeLongCycle (p : Equiv.Perm (α)) (S : Finset (α)) (J : ℕ) :
    Fintype (LongCycle p S J) := Fintype.ofFinite _


end RoutingNetwork

variable {α B : Type*} [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] {d : ℕ}

def parallelPerm (ω : B × SwitchIndex d → Bool) : Equiv.Perm (B × Card d) where
  toFun x := (x.1,butterflyPerm d (decodeButterfly d (fun i => ω (x.1,i))) x.2)
  invFun y := (y.1,(butterflyPerm d (decodeButterfly d (fun i => ω (y.1,i)))).symm y.2)
  left_inv x := by simp
  right_inv y := by simp

def relabeledPerm (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (ω : B × SwitchIndex d → Bool) : Equiv.Perm α :=
  (pre.trans (parallelPerm ω)).trans post

noncomputable def parallelPath (pre : α ≃ B × Card d)
    (ω : B × SwitchIndex d → Bool) (x : α) : Finset (B × SwitchIndex d) :=
  (routeDomain d (pre x).2
    (butterflyPerm d (decodeButterfly d (fun i => ω ((pre x).1,i))) (pre x).2)).image
      (fun i => ((pre x).1,i))

def parallelUsers (pre : α ≃ B × Card d) (ω : B × SwitchIndex d → Bool)
    (i : B × SwitchIndex d) : α × α :=
  let u := switchUsers d (decodeButterfly d (fun j => ω (i.1,j))) i.2
  (pre.symm (i.1,u.1),pre.symm (i.1,u.2))

omit [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] in
lemma parallelUsers_ne (pre : α ≃ B × Card d) (ω : B × SwitchIndex d → Bool)
    (i : B × SwitchIndex d) : (parallelUsers pre ω i).1 ≠ (parallelUsers pre ω i).2 := by
  intro h
  exact switchUsers_ne d _ _ (congrArg Prod.snd (pre.symm.injective h))

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma mem_parallelPath (pre : α ≃ B × Card d) (ω : B × SwitchIndex d → Bool)
    (x : α) (i : B × SwitchIndex d) :
    i ∈ parallelPath pre ω x ↔ (parallelUsers pre ω i).1 = x ∨ (parallelUsers pre ω i).2 = x := by
  classical
  obtain ⟨b,j⟩ := i
  simp only [parallelPath,Finset.mem_image,Prod.mk.injEq]
  constructor
  · rintro ⟨k,hk,hb,rfl⟩
    subst b
    rcases (mem_routeDomain_iff_user d _ _ _).mp hk with h | h
    · left
      apply pre.injective
      change pre (pre.symm ((pre x).1,_)) = pre x
      rw [Equiv.apply_symm_apply]
      exact Prod.ext rfl h
    · right
      apply pre.injective
      change pre (pre.symm ((pre x).1,_)) = pre x
      rw [Equiv.apply_symm_apply]
      exact Prod.ext rfl h
  · intro h
    have hh : (b,(switchUsers d (decodeButterfly d (fun j => ω (b,j))) j).1) = pre x ∨
        (b,(switchUsers d (decodeButterfly d (fun j => ω (b,j))) j).2) = pre x := by
      rcases h with h | h
      · exact Or.inl (by simpa only [parallelUsers,Equiv.apply_symm_apply] using congrArg pre h)
      · exact Or.inr (by simpa only [parallelUsers,Equiv.apply_symm_apply] using congrArg pre h)
    have hb : b = (pre x).1 := hh.elim (congrArg Prod.fst) (congrArg Prod.fst)
    subst b
    refine ⟨j,?_,rfl,rfl⟩
    apply (mem_routeDomain_iff_user d _ _ _).mpr
    exact hh.elim (fun h => Or.inl (congrArg Prod.snd h)) (fun h => Or.inr (congrArg Prod.snd h))

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma card_parallelPath (pre : α ≃ B × Card d) (ω : B × SwitchIndex d → Bool) (x : α) :
    (parallelPath pre ω x).card = d := by
  classical
  rw [parallelPath,Finset.card_image_of_injective _ (fun _ _ h => Prod.mk.inj h |>.2),card_routeDomain]

noncomputable def blockMarks (pre : α ≃ B × Card d) (S : Finset α) (b : B) : Finset (Card d) :=
  Finset.univ.filter (fun x => pre.symm (b,x) ∈ S)

omit [Fintype α] [Fintype B] [DecidableEq B] in
@[simp] lemma mem_blockMarks (pre : α ≃ B × Card d) (S : Finset α) (b : B) (x : Card d) :
    x ∈ blockMarks pre S b ↔ pre.symm (b,x) ∈ S := by
  classical
  simp [blockMarks]

omit [DecidableEq B] in
lemma sum_card_blockMarks (pre : α ≃ B × Card d) (S : Finset α) :
    ∑ b : B, (blockMarks pre S b).card = S.card := by
  classical
  calc
    _ = ∑ b : B, ∑ x : Card d, if pre.symm (b,x) ∈ S then 1 else 0 := by
      simp only [blockMarks,Finset.card_filter]
    _ = ∑ u : B × Card d, if pre.symm u ∈ S then 1 else 0 := (Fintype.sum_prod_type (fun u : B × Card d => if pre.symm u ∈ S then (1:ℕ) else 0)).symm
    _ = ∑ x : α, if x ∈ S then 1 else 0 := Equiv.sum_comp pre.symm (fun x : α => if x ∈ S then (1:ℕ) else 0)
    _ = _ := by simp

omit [DecidableEq B] in
lemma card_blockMarks_le (pre : α ≃ B × Card d) (S : Finset α) (b : B) :
    (blockMarks pre S b).card ≤ S.card := by
  rw [←sum_card_blockMarks pre S]
  exact Finset.single_le_sum (f := fun b : B => (blockMarks pre S b).card) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)

end Thorp

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_ParallelFollow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp
open scoped BigOperators
open Filter
section ParallelButterfly
variable {α B : Type*} [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] {d : ℕ}
omit [DecidableEq B] in
lemma parallel_entropy (pre : α ≃ B × Card d) (ω : B × SwitchIndex d → Bool) (S : Finset α) :
    (∑ i : B × SwitchIndex d,
      if (parallelUsers pre ω i).1 ∈ S ∧ (parallelUsers pre ω i).2 ∈ S then (1:ℝ) else 0) ≤
      (S.card : ℝ) * Real.log S.card / (2 * Real.log 2) := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ b : B, (blockMarks pre S b).card * Real.log (blockMarks pre S b).card / (2*Real.log 2) := by
      apply Finset.sum_le_sum
      intro b _
      simpa only [←mem_blockMarks,parallelUsers] using
        marked_switch_entropy_bound d (decodeButterfly d (fun i => ω (b,i))) (blockMarks pre S b)
    _ ≤ ∑ b : B, (blockMarks pre S b).card * Real.log S.card / (2*Real.log 2) := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hz : (blockMarks pre S b).card = 0
      · simp [hz]
      · apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz)
          (by exact_mod_cast card_blockMarks_le pre S b)
    _ = _ := by rw [←Finset.sum_div,←Finset.sum_mul,←Nat.cast_sum,sum_card_blockMarks]

noncomputable def parallelFollow (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x : α) (k : α → QueryTree (B × SwitchIndex d)) : QueryTree (B × SwitchIndex d) :=
  QueryTree.followPath d (fun i => ((pre x).1,i)) (pre x).2 (fun y => k (post ((pre x).1,y)))

omit [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] in
lemma parallelFollow_succeeds (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x : α) (k : α → QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool) :
    (parallelFollow pre post x k).succeeds ω = (k (relabeledPerm pre post ω x)).succeeds ω := by
  exact QueryTree.followPath_succeeds _ _ _ _ _

omit [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] in
lemma parallelFollow_raw_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x : α) (k : α → QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool) :
    (parallelFollow pre post x k).charge ω = (k (relabeledPerm pre post ω x)).charge ω := by
  exact QueryTree.followPath_raw_charge _ _ _ _ _

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelFollow_stale_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x : α) (k : α → QueryTree (B × SwitchIndex d)) (R : Finset (B × SwitchIndex d))
    (ω : B × SwitchIndex d → Bool) :
    (parallelFollow pre post x k).staleCharge R ω =
      (k (relabeledPerm pre post ω x)).staleCharge (R ∪ parallelPath pre ω x) ω := by
  exact QueryTree.followPath_stale_charge _ _ _ _ _ _

noncomputable def closingDomain (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) : Finset (B × SwitchIndex d) :=
  (routeDomain d (pre x).2 (post.symm y).2).image (fun i => ((pre x).1,i))

def closingValue (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (i : B × SwitchIndex d) : Bool := routeValue d (pre x).2 (post.symm y).2 i.2

omit [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] in
lemma relabeled_endpoint_pair (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (ω : B × SwitchIndex d → Bool) (x y : α) :
    relabeledPerm pre post ω x = y ↔
      (pre x).1 = (post.symm y).1 ∧
      butterflyPerm d (decodeButterfly d (fun i => ω ((pre x).1,i))) (pre x).2 = (post.symm y).2 := by
  change post ((pre x).1,_) = y ↔ _
  rw [←post.eq_symm_apply,Prod.mk.injEq]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma relabeled_endpoint_iff (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (ω : B × SwitchIndex d → Bool) (x y : α) :
    relabeledPerm pre post ω x = y ↔
      (pre x).1 = (post.symm y).1 ∧
        ∀ i ∈ closingDomain pre post x y, ω i = closingValue pre post x y i := by
  classical
  rw [relabeled_endpoint_pair,butterfly_endpoint_iff]
  simp only [closingDomain,Finset.forall_mem_image,closingValue]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma closingDomain_eq (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (ω : B × SwitchIndex d → Bool) (x y : α) (h : relabeledPerm pre post ω x = y) :
    closingDomain pre post x y = parallelPath pre ω x := by
  rw [closingDomain,parallelPath,(relabeled_endpoint_pair _ _ _ _ _).mp h |>.2]

noncomputable def parallelClose (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) : QueryTree (B × SwitchIndex d) :=
  if (pre x).1 = (post.symm y).1 then
    QueryTree.forceList (closingDomain pre post x y).toList (closingValue pre post x y) k
  else QueryTree.reject

omit [Fintype α] in
lemma parallelClose_succeeds (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool) :
    (parallelClose pre post x y k).succeeds ω =
      if relabeledPerm pre post ω x = y then k.succeeds ω else false := by
  classical
  simp only [relabeled_endpoint_iff,parallelClose]
  by_cases hb : (pre x).1 = (post.symm y).1
  · rw [ite_eq_left hb,QueryTree.forceList_succeeds]
    simp only [Finset.mem_toList,hb,true_and]
  · simp [hb,QueryTree.succeeds]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_raw_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (ω : B × SwitchIndex d → Bool)
    (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).charge ω = k.charge ω + d := by
  have hh := (relabeled_endpoint_iff _ _ _ _ _).mp h
  rw [parallelClose,ite_eq_left hh.1,QueryTree.forceList_raw_charge _ _ _ _
    (by simpa only [Finset.mem_toList] using hh.2),Finset.length_toList,
    closingDomain_eq _ _ _ _ _ h,card_parallelPath]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_fresh_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (R : Finset (B × SwitchIndex d))
    (ω : B × SwitchIndex d → Bool) (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).freshCharge R ω =
      k.freshCharge (R ∪ parallelPath pre ω x) ω + (parallelPath pre ω x \ R).card := by
  have hh := (relabeled_endpoint_iff _ _ _ _ _).mp h
  rw [parallelClose,ite_eq_left hh.1,QueryTree.forceList_charge _ _ _ _ _
    (by simpa only [Finset.mem_toList] using hh.2),Finset.toList_toFinset,
    closingDomain_eq _ _ _ _ _ h]

omit [Fintype α] [DecidableEq α] [Fintype B] in
lemma parallelClose_stale_charge (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (x y : α) (k : QueryTree (B × SwitchIndex d)) (R : Finset (B × SwitchIndex d))
    (ω : B × SwitchIndex d → Bool) (h : relabeledPerm pre post ω x = y) :
    (parallelClose pre post x y k).staleCharge R ω =
      k.staleCharge (R ∪ parallelPath pre ω x) ω + (parallelPath pre ω x ∩ R).card := by
  have h₀ := QueryTree.fresh_add_stale (parallelClose pre post x y k) R ω
  have h₁ := QueryTree.fresh_add_stale k (R ∪ parallelPath pre ω x) ω
  rw [parallelClose_raw_charge _ _ _ _ _ _ h,parallelClose_fresh_charge _ _ _ _ _ _ _ h] at h₀
  have h₂ : (parallelPath pre ω x \ R).card + (parallelPath pre ω x ∩ R).card = d := by
    rw [Finset.card_sdiff_add_card_inter,card_parallelPath]
  omega

noncomputable def parallelNetwork (pre : α ≃ B × Card d) (post : B × Card d ≃ α) :
    RoutingNetwork α (B × SwitchIndex d) d where
  perm := relabeledPerm pre post
  path := parallelPath pre
  users := parallelUsers pre
  users_ne := parallelUsers_ne pre
  mem_path := mem_parallelPath pre
  card_path := card_parallelPath pre
  entropy := parallel_entropy pre
  follow := parallelFollow pre post
  close := parallelClose pre post
  follow_succeeds := parallelFollow_succeeds pre post
  follow_raw_charge := parallelFollow_raw_charge pre post
  follow_stale_charge := parallelFollow_stale_charge pre post
  close_succeeds := parallelClose_succeeds pre post
  close_raw_charge := parallelClose_raw_charge pre post
  close_stale_charge := parallelClose_stale_charge pre post

end ParallelButterfly

def cardSplit : (r s : ℕ) → Card (s+r) ≃ Card r × Card s
  | 0, s =>
    { toFun := fun x => ((fun i => Fin.elim0 i), x)
      invFun := fun x => x.2
      left_inv := fun _ => rfl
      right_inv := fun x => by
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · rfl }
  | r+1, s =>
    { toFun := fun x => (Fin.cons (x 0) ((cardSplit r s (Fin.tail x)).1),
        (cardSplit r s (Fin.tail x)).2)
      invFun := fun x => Fin.cons (x.1 0) ((cardSplit r s).symm (Fin.tail x.1,x.2))
      left_inv := by
        intro x
        simp only [Fin.cons_zero, Fin.tail_cons, Prod.mk.eta, Equiv.symm_apply_apply, Fin.cons_self_tail]
      right_inv := by
        intro x
        simp only [Fin.cons_zero, Fin.tail_cons, Equiv.apply_symm_apply, Fin.cons_self_tail] }

def assembleBits : (r s : ℕ) → (Card r × SwitchIndex s → Bool) →
    (Card s × SwitchIndex r → Bool) → SwitchIndex (s+r) → Bool
  | 0, _, lo, _, i => lo ((fun j => Fin.elim0 j), i)
  | r+1, s, _, hi, Sum.inl y => hi ((cardSplit r s y).2,Sum.inl (cardSplit r s y).1)
  | r+1, s, lo, hi, Sum.inr (b,i) => assembleBits r s
      (fun j => lo (Fin.cons b j.1,j.2)) (fun j => hi (j.1,Sum.inr (b,j.2))) i

def splitSwitch : (r s : ℕ) → SwitchIndex (s+r) ≃
    (Card r × SwitchIndex s) ⊕ (Card s × SwitchIndex r)
  | 0, _ =>
    { toFun := fun i => Sum.inl ((fun j => Fin.elim0 j),i)
      invFun := fun i => match i with
        | Sum.inl (_,j) => j
        | Sum.inr (_,j) => nomatch j
      left_inv := fun _ => rfl
      right_inv := by
        intro i
        rcases i with ⟨x,j⟩ | ⟨x,j⟩
        · exact congrArg Sum.inl (Prod.ext (Subsingleton.elim _ _) rfl)
        · exact Empty.elim j }
  | r+1, s =>
    { toFun := fun i => match i with
        | Sum.inl y => Sum.inr ((cardSplit r s y).2,Sum.inl (cardSplit r s y).1)
        | Sum.inr (b,j) => match splitSwitch r s j with
          | Sum.inl (p,j) => Sum.inl (Fin.cons b p,j)
          | Sum.inr (q,j) => Sum.inr (q,Sum.inr (b,j))
      invFun := fun i => match i with
        | Sum.inl (p,j) => Sum.inr (p 0,(splitSwitch r s).symm (Sum.inl (Fin.tail p,j)))
        | Sum.inr (q,Sum.inl p) => Sum.inl ((cardSplit r s).symm (p,q))
        | Sum.inr (q,Sum.inr (b,j)) => Sum.inr (b,(splitSwitch r s).symm (Sum.inr (q,j)))
      left_inv := by
        intro i
        rcases i with y | ⟨b,j⟩
        · dsimp only
          rw [Prod.mk.eta, Equiv.symm_apply_apply]
        · dsimp only
          cases hz : splitSwitch r s j with
          | inl z =>
            rcases z with ⟨p,k⟩
            simp only [Fin.cons_zero, Fin.tail_cons]
            rw [←hz,Equiv.symm_apply_apply]
          | inr z =>
            rcases z with ⟨q,k⟩
            dsimp only
            rw [←hz,Equiv.symm_apply_apply]
      right_inv := by
        intro i
        rcases i with ⟨p,j⟩ | ⟨q,j⟩
        · simp only [Equiv.apply_symm_apply, Fin.cons_self_tail]
        · rcases j with p | ⟨b,j⟩ <;> simp only [Equiv.apply_symm_apply] }

def splitCoinEquiv (r s : ℕ) :
    ((Card r × SwitchIndex s → Bool) × (Card s × SwitchIndex r → Bool)) ≃
      (SwitchIndex (s+r) → Bool) :=
  (Equiv.sumArrowEquivProdArrow _ _ Bool).symm.trans
    (Equiv.arrowCongr (splitSwitch r s).symm (Equiv.refl Bool))

section PartiallyExposed
variable {α : Type*} {r s : ℕ}

def freshPre (pre : α ≃ Card (s+r)) (lo : Card r × SwitchIndex s → Bool) :
    α ≃ Card s × Card r :=
  ((pre.trans (cardSplit r s)).trans (parallelPerm lo)).trans (Equiv.prodComm _ _)

def freshPost (post : Card (s+r) ≃ α) : Card s × Card r ≃ α :=
  ((Equiv.prodComm _ _).trans (cardSplit r s).symm).trans post

end PartiallyExposed

lemma finiteMean_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    finiteMean (fun _ : Ω => c) = c := by
  simp only [finiteMean,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_div_cancel_left₀ c (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

section ParallelFairLayer
variable {β : Type*} [Fintype β] [DecidableEq β]

def pairLayer (ξ : β → Bool) : Equiv.Perm (Bool × β) where
  toFun x := (Bool.xor x.1 (ξ x.2),x.2)
  invFun x := (Bool.xor x.1 (ξ x.2),x.2)
  left_inv x := by
    rcases x with ⟨b,x⟩
    change (Bool.xor (Bool.xor b (ξ x)) (ξ x),x) = (b,x)
    cases b <;> cases ξ x <;> rfl
  right_inv x := by
    rcases x with ⟨b,x⟩
    change (Bool.xor (Bool.xor b (ξ x)) (ξ x),x) = (b,x)
    cases b <;> cases ξ x <;> rfl

noncomputable def pairFiber (S : Finset (Bool × β)) (b : β) : Finset Bool :=
  Finset.univ.filter (fun ε => (ε,b) ∈ S)

end ParallelFairLayer

section JoinChildren
variable {β : Type*} [DecidableEq β]

noncomputable def childJoin (A B : Finset β) : Finset (Bool × β) :=
  A.image (fun x => (false,x)) ∪ B.image (fun x => (true,x))

lemma mem_childJoin (A B : Finset β) (b : Bool) (x : β) :
    (b,x) ∈ childJoin A B ↔ (if b then x ∈ B else x ∈ A) := by
  cases b <;> simp [childJoin]

noncomputable def boolFiber (S : Finset (Bool × β)) (b : Bool) : Finset β :=
  (S.filter (fun x => x.1 = b)).image Prod.snd

lemma mem_boolFiber (S : Finset (Bool × β)) (b : Bool) (x : β) :
    x ∈ boolFiber S b ↔ (b,x) ∈ S := by
  constructor
  · intro h
    obtain ⟨⟨c,y⟩,hy,hxy⟩ := Finset.mem_image.mp h
    obtain ⟨hy,hc⟩ := Finset.mem_filter.mp hy
    change c = b at hc
    change y = x at hxy
    simpa only [hc,hxy] using hy
  · intro h
    exact Finset.mem_image.mpr ⟨(b,x),Finset.mem_filter.mpr ⟨h,rfl⟩,rfl⟩

end JoinChildren

def coinStepEquiv (d : ℕ) : (SwitchIndex (d+1) → Bool) ≃
    ((SwitchIndex d → Bool) × (SwitchIndex d → Bool)) × (Card d → Bool) where
  toFun ω := ((fun i => ω (Sum.inr (false,i)),fun i => ω (Sum.inr (true,i))),
    fun x => ω (Sum.inl x))
  invFun ω := Sum.elim ω.2 (fun bi => if bi.1 then ω.1.2 bi.2 else ω.1.1 bi.2)
  left_inv ω := by
    funext i
    cases i with
    | inl x => rfl
    | inr bi => cases bi with | mk b i => cases b <;> rfl
  right_inv ω := by
    rcases ω with ⟨⟨ω₀,ω₁⟩,ξ⟩
    rfl

def headTailEquiv (d : ℕ) : Card (d+1) ≃ Bool × Card d :=
  (Fin.consEquiv (fun _ : Fin (d+1) => Bool)).symm

namespace CycleColoring
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Coloring (p : Equiv.Perm α) (S : Finset α) :=
  {f : α → Bool // (∀ x, x ∉ S → f x = false) ∧
    ∀ x ∈ S, p x ∈ S → f (p x) = f x}

noncomputable instance instFintypeColoring (p : Equiv.Perm α) (S : Finset α) : Fintype (Coloring p S) :=
  Fintype.ofFinite _

noncomputable def boundary (p : Equiv.Perm α) (S : Finset α) : Finset α :=
  S.filter (fun x => p.symm x ∉ S)

noncomputable def root {p : Equiv.Perm α} {S : Finset α}
    (C : RoutingNetwork.SelectedCycle p S) : α := C.nonempty.choose

abbrev Seed (p : Equiv.Perm α) (S : Finset α) :=
  {x // x ∈ boundary p S} ⊕ RoutingNetwork.SelectedCycle p S

noncomputable def record {p : Equiv.Perm α} {S : Finset α}
    (f : Coloring p S) : Seed p S → Bool :=
  Sum.elim (fun x => f.val x.val) (fun C => f.val (root C))


abbrev OppositeColoring (p : Equiv.Perm α) (S : Finset α) :=
  {f : α → Bool // (∀ x, x ∉ S → f x = false) ∧
    ∀ x ∈ S, p x ∈ S → f (p x) = !(f x)}

noncomputable instance instFintypeOppositeColoring (p : Equiv.Perm α) (S : Finset α) : Fintype (OppositeColoring p S) :=
  Fintype.ofFinite _

noncomputable def bipartitionFlip (p : Equiv.Perm α) (S : Finset α)
    (χ : α → Bool) (hχ : ∀ x, χ (p x) = !(χ x))
    (f : OppositeColoring p S) : Coloring p S := by
  classical
  refine ⟨(fun x => if x ∈ S then Bool.xor (f.val x) (χ x) else false),?_,?_⟩
  · intro x hx
    exact ite_eq_right hx
  · intro x hx hpx
    simp only [ite_eq_left hx,ite_eq_left hpx,f.property.2 x hx hpx,hχ x]
    cases f.val x <;> cases χ x <;> rfl

end CycleColoring
end Thorp

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_AlternatingPerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp
open scoped BigOperators
open Filter
namespace CycleColoring
variable {α : Type*} [Fintype α] [DecidableEq α]

def alternatingPerm (p : Equiv.Perm α) : Equiv.Perm (Bool × α) where
  toFun x := if x.1 then (false,p x.2) else (true,x.2)
  invFun x := if x.1 then (false,x.2) else (true,p.symm x.2)
  left_inv x := by rcases x with ⟨b,x⟩; cases b <;> simp
  right_inv x := by rcases x with ⟨b,x⟩; cases b <;> simp

omit [Fintype α] [DecidableEq α] in
lemma alternating_step_sameCycle (p : Equiv.Perm α) (x : Bool × α) :
    p.SameCycle x.2 (alternatingPerm p x).2 := by
  rcases x with ⟨b,x⟩
  cases b
  · exact Equiv.Perm.SameCycle.refl p x
  · exact (Equiv.Perm.SameCycle.refl p x).apply_right

omit [DecidableEq α] in
lemma alternating_sameCycle_snd (p : Equiv.Perm α) {x y : Bool × α}
    (h : (alternatingPerm p).SameCycle x y) : p.SameCycle x.2 y.2 := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  have hp (k : ℕ) : p.SameCycle x.2 (((alternatingPerm p)^k) x).2 := by
    induction k with
    | zero => exact Equiv.Perm.SameCycle.refl p x.2
    | succ k ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      exact ih.trans (alternating_step_sameCycle p _)
  exact hn ▸ hp n

omit [DecidableEq α] in
lemma alternating_zero_sameCycle (p : Equiv.Perm α) {x y : α}
    (h : p.SameCycle x y) : (alternatingPerm p).SameCycle (false,x) (false,y) := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  have hp (k : ℕ) : (alternatingPerm p).SameCycle (false,x) (false,(p^k) x) := by
    induction k with
    | zero => exact Equiv.Perm.SameCycle.refl _ _
    | succ k ih =>
      have hs := ih.apply_right.apply_right
      simpa only [pow_succ',Equiv.Perm.mul_apply,alternatingPerm,Equiv.coe_fn_mk,
        Bool.false_eq_true,↓reduceIte] using hs
  simpa only [hn] using hp n

omit [Fintype α] [DecidableEq α] in
lemma alternating_sameCycle_zero (p : Equiv.Perm α) (x : Bool × α) :
    (alternatingPerm p).SameCycle x (false,x.2) := by
  rcases x with ⟨b,x⟩
  cases b
  · exact Equiv.Perm.SameCycle.refl _ _
  · exact ((Equiv.Perm.SameCycle.refl (alternatingPerm p) (false,x)).apply_right).symm

omit [DecidableEq α] in
lemma alternating_sameCycle_iff (p : Equiv.Perm α) (x y : Bool × α) :
    (alternatingPerm p).SameCycle x y ↔ p.SameCycle x.2 y.2 := by
  constructor
  · exact alternating_sameCycle_snd p
  · intro h
    exact (alternating_sameCycle_zero p x).trans
      ((alternating_zero_sameCycle p h).trans (alternating_sameCycle_zero p y).symm)

lemma orbit_alternating (p : Equiv.Perm α) (x : Bool × α) :
    orbitSet (alternatingPerm p) x = childJoin (orbitSet p x.2) (orbitSet p x.2) := by
  ext ⟨b,y⟩
  simp only [mem_orbitSet,alternating_sameCycle_iff,mem_childJoin,ite_self]

omit [Fintype α] in
lemma boolFiber_childJoin (A B : Finset α) (b : Bool) :
    boolFiber (childJoin A B) b = if b then B else A := by
  ext x
  cases b <;> simp only [mem_boolFiber,mem_childJoin,Bool.false_eq_true,↓reduceIte]

noncomputable def projectCycle (p : Equiv.Perm α) (A B : Finset α)
    (C : RoutingNetwork.SelectedCycle (alternatingPerm p) (childJoin A B)) :
    RoutingNetwork.SelectedCycle p A := by
  refine ⟨boolFiber C.val false,?_,?_⟩
  · obtain ⟨x,hx⟩ := C.property.1
    refine ⟨x.2,?_⟩
    rw [hx,orbit_alternating,boolFiber_childJoin]
    rfl
  · intro x hx
    exact (mem_childJoin A B false x).mp (C.property.2 ((mem_boolFiber _ _ _).mp hx))

end CycleColoring

lemma finiteMean_nonneg {Ω : Type*} [Fintype Ω] {f : Ω → ℝ}
    (h : ∀ ω, 0 ≤ f ω) : 0 ≤ finiteMean f := by
  exact div_nonneg (Finset.sum_nonneg (fun ω _ => h ω)) (Nat.cast_nonneg _)

noncomputable def headAverage {d : ℕ} (p : Card (d+1) → ℝ) (y : Card d) : ℝ :=
  (p (Fin.cons false y)+p (Fin.cons true y))/2

noncomputable def inverseButterflyMarks (d : ℕ) (A : Finset (Card d))
    (ω : SwitchIndex d → Bool) : Finset (Card d) :=
  A.image (butterflyPerm d (decodeButterfly d ω)).symm

namespace PairRouting

section
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

noncomputable def occupied (x : ι → Bool × α) : Finset α :=
  Finset.univ.image (fun i => (x i).2)

def required (x : ι → Bool × α) (c : ι → Bool) (i : ι) : Bool := Bool.xor (x i).1 (c i)

def Compatible (x : ι → Bool × α) (c : ι → Bool) : Prop :=
  ∀ i j, (x i).2 = (x j).2 → required x c i = required x c j

def colors (x : ι → Bool × α) (ξ : α → Bool) (i : ι) : Bool :=
  Bool.xor (x i).1 (ξ (x i).2)

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma required_colors (x : ι → Bool × α) (ξ : α → Bool) (i : ι) :
    required x (colors x ξ) i = ξ (x i).2 := by
  simp only [required,colors]
  cases (x i).1 <;> cases ξ (x i).2 <;> rfl

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma colors_compatible (x : ι → Bool × α) (ξ : α → Bool) : Compatible x (colors x ξ) := by
  intro i j he
  simp only [required_colors,he]

noncomputable def chosenCoin (x : ι → Bool × α) (c : ι → Bool) (y : α) : Bool := by
  classical
  exact if h : ∃ i, (x i).2 = y then required x c (Classical.choose h) else false

noncomputable instance instDecidableCompatible (x : ι → Bool × α) (c : ι → Bool) : Decidable (Compatible x c) :=
  Classical.propDecidable _

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma Compatible.tail_injective {x : ι ↪ Bool × α} {c : ι → Bool} (hc : Compatible x c) (b : Bool) :
    Function.Injective (fun i : {i : ι // c i = b} => (x i.val).2) := by
  intro i j he
  apply Subtype.ext
  apply x.injective
  apply Prod.ext
  · have hh := hc i j he
    simp only [required,i.property,j.property] at hh
    cases h₀ : (x i.val).1 <;> cases h₁ : (x j.val).1 <;> cases b <;> simp_all
  · exact he

def childEmbedding (x : ι ↪ Bool × α) (c : ι → Bool) (hc : Compatible x c) (b : Bool) :
    {i : ι // c i = b} ↪ α := ⟨fun i => (x i.val).2,hc.tail_injective b⟩


def lift (p : Bool → Equiv.Perm α) : Equiv.Perm (Bool × α) where
  toFun x := (x.1,p x.1 x.2)
  invFun x := (x.1,(p x.1).symm x.2)
  left_inv x := by simp
  right_inv x := by simp

def sandwich (ξ η : α → Bool) (p : Bool → Equiv.Perm α) : Equiv.Perm (Bool × α) :=
  pairLayer η * lift p * pairLayer ξ

def ChildMatches (p : Bool → Equiv.Perm α) (x y : ι → Bool × α) (c : ι → Bool) : Prop :=
  ∀ i, p (c i) (x i).2 = (y i).2

noncomputable instance instDecidableChildMatches (p : Bool → Equiv.Perm α) (x y : ι → Bool × α) (c : ι → Bool) :
    Decidable (ChildMatches p x y c) := Classical.propDecidable _


abbrev BothAssignments (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :=
  {c : ι → Bool // Compatible e c ∧ Compatible (fun i => lift p (e i)) c}

noncomputable instance instFintypeBothAssignments (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) :
    Fintype (BothAssignments e p) := Fintype.ofFinite _

noncomputable def labelSet (e : ι ↪ Bool × α) : Finset (Bool × α) := Finset.univ.image e

def alternatingProjection (p : Bool → Equiv.Perm α) : Equiv.Perm α := (p false).symm * p true

noncomputable def assignmentColoring (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α)
    (c : BothAssignments e p) : CycleColoring.OppositeColoring
      (CycleColoring.alternatingPerm (alternatingProjection p)) (labelSet e) := by
  classical
  refine ⟨Function.extend e c.val (fun _ => false),?_,?_⟩
  · intro z hz
    apply Function.extend_apply'
    rintro ⟨i,rfl⟩
    exact hz (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  · intro z hz hnext
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hz
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hnext
    have hfi := e.injective.extend_apply c.val (fun _ => false) i
    have hfj := e.injective.extend_apply c.val (fun _ => false) j
    rw [hi] at hfi
    rw [hj] at hfj
    rw [hfi,hfj]
    rcases z with ⟨b,a⟩
    cases b
    · have hj' : e j = (true,a) := hj
      have ht : (e i).2 = (e j).2 := by rw [hi,hj']
      have hh := c.property.1 i j ht
      simp only [required,hi,hj'] at hh
      revert hh
      generalize c.val i = bi
      generalize c.val j = bj
      cases bi <;> cases bj <;> decide
    · have hj' : e j = (false,alternatingProjection p a) := hj
      have ht : (lift p (e i)).2 = (lift p (e j)).2 := by
        simp only [hi,hj',lift,Equiv.coe_fn_mk,alternatingProjection,Equiv.Perm.coe_mul,
          Function.comp_apply,Equiv.apply_symm_apply]
      have hh := c.property.2 i j ht
      simp only [required,hi,hj',lift,Equiv.coe_fn_mk] at hh
      revert hh
      generalize c.val i = bi
      generalize c.val j = bj
      cases bi <;> cases bj <;> decide

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma compatible_pairLayer_iff (x : ι → Bool × α) (c : ι → Bool) (ξ : α → Bool) :
    Compatible (fun i => pairLayer ξ (x i)) c ↔ Compatible x c := by
  have he (i j : ι) (ht : (x i).2 = (x j).2) :
      required (fun i => pairLayer ξ (x i)) c i = required (fun i => pairLayer ξ (x i)) c j ↔
      required x c i = required x c j := by
    simp only [required,pairLayer,Equiv.coe_fn_mk,ht]
    cases (x i).1 <;> cases (x j).1 <;> cases c i <;> cases c j <;> cases ξ (x j).2 <;> decide
  constructor
  · intro h i j ht
    exact (he i j ht).mp (h i j ht)
  · intro h i j ht
    exact (he i j ht).mpr (h i j ht)


noncomputable def alternatingCycles (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) : ℕ :=
  Fintype.card (RoutingNetwork.SelectedCycle
    (CycleColoring.alternatingPerm (alternatingProjection p)) (labelSet e))

abbrev Assignments (x y : ι → Bool × α) :=
  {c : ι → Bool // Compatible x c ∧ Compatible y c}

noncomputable instance instFintypeAssignments (x y : ι → Bool × α) : Fintype (Assignments x y) := Fintype.ofFinite _

def switchedEmbedding (e : ι ↪ Bool × α) (ξ : α → Bool) : ι ↪ Bool × α :=
  e.trans (pairLayer ξ).toEmbedding

def routedEmbedding (e : ι ↪ Bool × α) (ξ η : α → Bool) (p : Bool → Equiv.Perm α) :
    ι ↪ Bool × α := e.trans (sandwich ξ η p).toEmbedding

noncomputable def assignmentsEquiv (e : ι ↪ Bool × α) (ξ η : α → Bool)
    (p : Bool → Equiv.Perm α) :
    Assignments e (routedEmbedding e ξ η p) ≃ BothAssignments (switchedEmbedding e ξ) p := by
  apply Equiv.subtypeEquivRight
  intro c
  change Compatible e c ∧ Compatible (fun i => pairLayer η (lift p (pairLayer ξ (e i)))) c ↔ _
  rw [compatible_pairLayer_iff]
  exact and_congr (compatible_pairLayer_iff e c ξ).symm Iff.rfl

end
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [DecidableEq ι]

noncomputable def compatibleSet (x y : ι → Bool × α) : Finset (ι → Bool) := by
  classical
  exact Finset.univ.filter (fun c => Compatible x c ∧ Compatible y c)

omit [Fintype α] [DecidableEq α] in
lemma mem_compatibleSet (x y : ι → Bool × α) (c : ι → Bool) :
    c ∈ compatibleSet x y ↔ Compatible x c ∧ Compatible y c := by
  classical
  simp only [compatibleSet,Finset.mem_filter,Finset.mem_univ,true_and]

noncomputable def outerWeight (x y : ι → Bool × α) : ℝ :=
  1/(2:ℝ)^((occupied x).card+(occupied y).card)

end PairRouting
end Thorp

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_SandwichShuffle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp
open scoped BigOperators
open Filter

def sandwichShuffle {A B C D E F : Type*} :
    ((A × B) × C) × ((D × E) × F) ≃ ((A × D) × (B × E)) × (F × C) where
  toFun x := (((x.1.1.1,x.2.1.1),(x.1.1.2,x.2.1.2)),(x.2.2,x.1.2))
  invFun x := (((x.1.1.1,x.1.2.1),x.2.2),((x.1.1.2,x.1.2.2),x.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

def benesStepEquiv (d : ℕ) : BenesCoins (d+1) ≃
    (BenesCoins d × BenesCoins d) × ((Card d → Bool) × (Card d → Bool)) :=
  (Equiv.prodCongr (coinStepEquiv d) (coinStepEquiv d)).trans sandwichShuffle

lemma childLift_mul (d : ℕ) (p q : Bool → Equiv.Perm (Card d)) :
    childLift p * childLift q = childLift (fun b => p b * q b) := by
  ext x i
  simp only [Equiv.Perm.mul_apply,childLift,Equiv.coe_fn_mk,Fin.cons_zero,Fin.tail_cons]

noncomputable def palindromeCost : (d : ℕ) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card d) → BenesCoins d → ℕ
  | 0, _, _, _, _ => 0
  | d+1, _, _, e, ω =>
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
          (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1)) +
        palindromeCost d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        palindromeCost d (PairRouting.childEmbedding x c hc true) σ.1.2

namespace PairRouting

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [DecidableEq ι]

noncomputable def coloredEmbedding (x : ι ↪ Bool × α) (c : ι → Bool) (_hc : Compatible x c) :
    ι ↪ Bool × α := switchedEmbedding x (chosenCoin x c)

end PairRouting

noncomputable def assignmentCost (d : ℕ) {ι : Type*} [Fintype ι]
    (x : ι ↪ Bool × Card d) (c : ι → Bool) (hc : PairRouting.Compatible x c)
    (ω : BenesCoins d × BenesCoins d) : ℕ :=
  PairRouting.alternatingCycles (PairRouting.coloredEmbedding x c hc)
      (fun b => palindromePerm d (if b then ω.2 else ω.1)) +
    palindromeCost d (PairRouting.childEmbedding x c hc false) ω.1 +
    palindromeCost d (PairRouting.childEmbedding x c hc true) ω.2

noncomputable def routingMoment (d : ℕ) {ι : Type*} [Fintype ι]
    (e f : ι ↪ Card d) (a : ℝ) : ℝ := by
  classical
  exact finiteMean (fun ω : BenesCoins d =>
    if ∀ i, palindromePerm d ω (e i) = f i then (2:ℝ)^((palindromeCost d e ω:ℝ)*a) else 0)

noncomputable def palindromeRowMoment (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (a : ℝ) : ℝ :=
  finiteMean (fun f : ι ↪ Card d =>
    ((Fintype.card (ι ↪ Card d):ℝ)*PairRouting.tupleProbability (palindromePerm d) e f)^(1+a))

end Thorp
namespace Thorp


noncomputable def sparseCoefficient {α : Type*} (w : ℝ) (T : Finset α) : ℝ :=
  if T.card = 1 then 0 else w^T.card


noncomputable def sparseMass {α β : Type*} [DecidableEq α] [Fintype β]
    (D : β → Finset α) (A : Finset α) : ℕ :=
  ∑ b, if 2 ≤ (D b ∩ A).card then (D b ∩ A).card else 0


def crowdedMass (h : ℕ) : ℕ := if 2 ≤ h then h else 0

noncomputable def palindromeLowCost (H : ℕ) : (d : ℕ) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card d) → BenesCoins d → ℕ
  | 0, _, _, _, _ => 0
  | d+1, _, _, e, ω =>
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      (if d+1 ≤ H then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
          (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1)) else 0) +
        palindromeLowCost H d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        palindromeLowCost H d (PairRouting.childEmbedding x c hc true) σ.1.2

end Thorp

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_CutoffMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp

noncomputable def cutoffMass (H : ℕ) : (d : ℕ) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card d) → BenesCoins d → ℕ
  | 0, _, _, _, _ => 0
  | d+1, ι, _, e, ω =>
      if d+1 ≤ H then crowdedMass (Fintype.card ι) else
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      cutoffMass H d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        cutoffMass H d (PairRouting.childEmbedding x c hc true) σ.1.2


noncomputable def centralBlock (r H : ℕ) (b : Card r) : Finset (Card (H+r)) :=
  Finset.univ.image (fun z : Card H => (cardSplit r H).symm (b,z))

end Thorp
namespace Thorp
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma orbitSet_conjugate (p g : Equiv.Perm α) (x : α) :
    orbitSet (g*p*g⁻¹) (g x) = (orbitSet p x).image g := by
  ext y
  simp only [mem_orbitSet,Finset.mem_image]
  rw [Equiv.Perm.sameCycle_conj]
  change p.SameCycle (g.symm (g x)) (g.symm y) ↔ ∃ z, p.SameCycle x z ∧ g z = y
  rw [Equiv.symm_apply_apply]
  constructor
  · intro h
    exact ⟨g.symm y,h,g.apply_symm_apply y⟩
  · rintro ⟨z,hz,rfl⟩
    simpa only [Equiv.symm_apply_apply] using hz

noncomputable def conjugateCycle (p g : Equiv.Perm α) (S : Finset α)
    (C : RoutingNetwork.SelectedCycle p S) :
    RoutingNetwork.SelectedCycle (g*p*g⁻¹) (S.image g) := by
  refine ⟨C.val.image g,?_,Finset.image_subset_image C.property.2⟩
  obtain ⟨x,hx⟩ := C.property.1
  exact ⟨g x,by rw [hx,orbitSet_conjugate]⟩

end Thorp
namespace Thorp

noncomputable def cycleCoefficient (r J : ℕ) (q : ℝ) : ℝ :=
  Real.log q / J + 2*q*Real.sqrt J/Real.sqrt ((2:ℝ)^r)


def highStepEquiv (r s : ℕ) : (Card s × SwitchIndex (r+1) → Bool) ≃
    (((Card s × SwitchIndex r → Bool) × (Card s × SwitchIndex r → Bool)) ×
      (Card s × Card r → Bool)) where
  toFun hi := ((fun j => hi (j.1,Sum.inr (false,j.2)),
    fun j => hi (j.1,Sum.inr (true,j.2))),fun j => hi (j.1,Sum.inl j.2))
  invFun c := fun j => match j.2 with
    | Sum.inl y => c.2 (j.1,y)
    | Sum.inr (b,i) => if b then c.1.2 (j.1,i) else c.1.1 (j.1,i)
  left_inv hi := by
    funext j
    rcases j with ⟨z,y|⟨b,i⟩⟩
    · rfl
    · cases b <;> rfl
  right_inv c := by
    rcases c with ⟨⟨h₀,h₁⟩,η⟩
    rfl

noncomputable def palindromeLevelCost (t : ℕ) : (d : ℕ) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card d) → BenesCoins d → ℕ
  | 0, _, _, _, _ => 0
  | d+1, _, _, e, ω =>
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      if t = d+1 then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
          (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1)) else
        palindromeLevelCost t d (PairRouting.childEmbedding x c hc false) σ.1.1 +
          palindromeLevelCost t d (PairRouting.childEmbedding x c hc true) σ.1.2


def switchHeight : (d : ℕ) → SwitchIndex d → ℕ
  | 0, i => nomatch i
  | d+1, Sum.inl _ => d+1
  | d+1, Sum.inr (_,i) => switchHeight d i

def AgreeThrough (d s : ℕ) (Y Y' : SwitchIndex d → Bool) : Prop :=
  ∀ i, switchHeight d i ≤ s → Y i = Y' i

def LayerAdapted (d s : ℕ) {β : Type*} (f : (SwitchIndex d → Bool) → β) : Prop :=
  ∀ Y Y', AgreeThrough d s Y Y' → f Y = f Y'

noncomputable def palindromeSlabCost (l d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : ℕ :=
  ∑ i : Fin l, palindromeLevelCost (l+i.1+1) d e ω

def familyEnd (L n : ℕ) : ℕ := if n = 0 then 0 else 2*(L*4^(n-1))

end Thorp

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_PalindromeFamilyCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp

noncomputable def palindromeFamilyCost (L n d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : ℕ :=
  ∑ j ∈ Finset.range n, palindromeSlabCost (L*4^j) d e ω


noncomputable def heightDecay (H : ℕ) : ℝ :=
  68*Real.exp (-(H:ℝ)/64)/(1-Real.exp (-(1:ℝ)/64))

noncomputable def momentBase : ℝ := (2:ℝ)^(1/1000:ℝ)


noncomputable def densityCutoff (p : ℝ) : ℕ := ⌊-Real.log p/(4*Real.log 2)⌋₊

noncomputable def densityTailConstant : ℝ :=
  68*Real.exp (1/64)/(1-Real.exp (-(1:ℝ)/64))

noncomputable def densityConstant : ℝ :=
  256*(1+heightDecay 1)+1+densityTailConstant

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma orbitSet_eq_of_agree (p q : Equiv.Perm α) (x : α)
    (h : ∀ z ∈ orbitSet p x, p z = q z) : orbitSet p x = orbitSet q x := by
  have hp (n : ℕ) : (p^n) x ∈ orbitSet p x := by
    apply (mem_orbitSet _ _ _).mpr
    exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  have he (n : ℕ) : (p^n) x = (q^n) x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ',pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,←ih]
      exact h _ (hp n)
  ext y
  simp only [mem_orbitSet]
  constructor
  · intro hy
    obtain ⟨n,hn⟩ := hy.exists_nat_pow_eq
    rw [←hn,he]
    exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  · intro hy
    obtain ⟨n,hn⟩ := hy.exists_nat_pow_eq
    rw [←hn,←he]
    exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)

noncomputable def survivingCycle (p q : Equiv.Perm α) (S B : Finset α)
    (h : ∀ x ∉ B, p x = q x) (C : RoutingNetwork.SelectedCycle p S)
    (hC : ∀ x ∈ C.val, x ∉ B) : RoutingNetwork.SelectedCycle q S := by
  refine ⟨C.val,?_,C.property.2⟩
  obtain ⟨x,hx⟩ := C.property.1
  refine ⟨x,hx.trans (orbitSet_eq_of_agree p q x ?_)⟩
  intro z hz
  exact h z (hC z (hx ▸ hz))

noncomputable def perturbCycleMap (p q : Equiv.Perm α) (S B : Finset α)
    (h : ∀ x ∉ B, p x = q x) (C : RoutingNetwork.SelectedCycle p S) :
    RoutingNetwork.SelectedCycle q S ⊕ {x // x ∈ B} := by
  classical
  by_cases hb : ∃ x ∈ C.val, x ∈ B
  · exact Sum.inr ⟨hb.choose,hb.choose_spec.2⟩
  · exact Sum.inl (survivingCycle p q S B h C (by simpa only [not_exists,not_and] using hb))


noncomputable def permDistance (p q : Equiv.Perm α) : ℕ :=
  (Finset.univ.filter (fun x => p x ≠ q x)).card

end Thorp
namespace Thorp

noncomputable def centralDistance (L r : ℕ) (C D : Card r → Equiv.Perm (Card L)) : ℕ :=
  ∑ u : Card r, permDistance (C u) (D u)

end Thorp

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_InputTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp


inductive InputTree : ℕ → Type
  | tip {d : ℕ} (p : Equiv.Perm (Card d)) : InputTree d
  | node {d : ℕ} (ξ : Card d → Bool) (T : Bool → InputTree d) : InputTree (d+1)

def InputTree.perm : {d : ℕ} → InputTree d → Equiv.Perm (Card d)
  | _, .tip p => p
  | _, .node ξ T => pairSwitch ξ * childLift (fun b => (T b).perm)

noncomputable def InputTree.levelCost (t : ℕ) : {d : ℕ} → InputTree d →
    {ι : Type*} → [Fintype ι] → (ι ↪ Card d) → (SwitchIndex d → Bool) → ℕ
  | _, .tip _, _, _, _, _ => 0
  | d+1, .node ξ T, _, _, e, Y =>
    let x := e.trans (headTailEquiv d).toEmbedding
    let c := PairRouting.colors x ξ
    let hc := PairRouting.colors_compatible x ξ
    let σ := coinStepEquiv d Y
    if t = d+1 then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x ξ)
      (fun b => if b then butterflyPerm d (decodeButterfly d σ.1.2) * (T true).perm⁻¹
        else butterflyPerm d (decodeButterfly d σ.1.1) * (T false).perm⁻¹)
    else (T false).levelCost t (PairRouting.childEmbedding x c hc false) σ.1.1 +
      (T true).levelCost t (PairRouting.childEmbedding x c hc true) σ.1.2


noncomputable def InputTree.slabCost (l d : ℕ) (T : InputTree d) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) : ℕ :=
  ∑ i : Fin l, T.levelCost (l+i.1+1) e Y


def boundaryTree (L : ℕ) : (r : ℕ) → (Card r → Equiv.Perm (Card L)) →
    (SwitchIndex (L+r) → Bool) → InputTree (L+r)
  | 0, U, _ => .tip (U (fun j => Fin.elim0 j))
  | r+1, U, X => .node (coinStepEquiv (L+r) X).2 (fun b =>
      boundaryTree L r (fun u => U (Fin.cons b u))
        (if b then (coinStepEquiv (L+r) X).1.2 else (coinStepEquiv (L+r) X).1.1))

def boundaryOutput (L : ℕ) : (r : ℕ) → (SwitchIndex (L+r) → Bool) →
    Card r → Equiv.Perm (Card L)
  | 0, Y, _ => butterflyPerm L (decodeButterfly L Y)
  | r+1, Y, u => boundaryOutput L r
      (if u 0 then (coinStepEquiv (L+r) Y).1.2 else (coinStepEquiv (L+r) Y).1.1) (Fin.tail u)

noncomputable def modifiedBoundary (L r : ℕ) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (Y : SwitchIndex (L+r) → Bool) :
    Card r → Equiv.Perm (Card L) := fun u => if u ∈ E then boundaryOutput L r Y u else U u

noncomputable def InputTree.familyCost (L n d : ℕ)
    (T : (SwitchIndex d → Bool) → InputTree d) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) : ℕ :=
  ∑ j ∈ Finset.range n, InputTree.slabCost (L*4^j) d (T Y) e Y


noncomputable def modifiedInputTree (L r : ℕ) (E : Finset (Card r))
    (U : Card r → Equiv.Perm (Card L)) (X Y : SwitchIndex (L+r) → Bool) : InputTree (L+r) :=
  boundaryTree L r (modifiedBoundary L r E U Y) X

noncomputable def InputTree.lowCost (H d : ℕ) (T : InputTree d)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (Y : SwitchIndex d → Bool) : ℕ :=
  ∑ i ∈ Finset.range H, T.levelCost (i+1) e Y


noncomputable def exceptionChild {r : ℕ} (E : Finset (Card (r+1))) (b : Bool) : Finset (Card r) :=
  Finset.univ.filter (fun u => Fin.cons b u ∈ E)

def seedSplitEquiv (r : ℕ) (A : Type*) : (Card (r+1) → A) ≃ (Card r → A) × (Card r → A) where
  toFun U := (fun u => U (Fin.cons false u),fun u => U (Fin.cons true u))
  invFun U := fun u => if u 0 then U.2 (Fin.tail u) else U.1 (Fin.tail u)
  left_inv U := by
    funext u
    dsimp only
    split_ifs with h
    · rw [←h,Fin.cons_self_tail]
    · have h' : u 0 = false := by cases hh : u 0 <;> simp_all
      rw [←h',Fin.cons_self_tail]
  right_inv U := by simp only [Fin.cons_zero,Fin.tail_cons,Bool.false_eq_true,↓reduceIte]

def seedSandwichShuffle {A B C D E : Type*} :
    (A × B) × ((C × D) × E) ≃ ((A × C) × (B × D)) × E where
  toFun x := (((x.1.1,x.2.1.1),(x.1.2,x.2.1.2)),x.2.2)
  invFun x := ((x.1.1.1,x.1.2.1),((x.1.1.2,x.1.2.2),x.2))
  left_inv _ := rfl
  right_inv _ := rfl

abbrev ModifiedCoins (L r : ℕ) := (Card r → Equiv.Perm (Card L)) × BenesCoins (L+r)

def modifiedStepEquiv (L r : ℕ) : ModifiedCoins L (r+1) ≃
    (ModifiedCoins L r × ModifiedCoins L r) × ((Card (L+r) → Bool) × (Card (L+r) → Bool)) :=
  (Equiv.prodCongr (seedSplitEquiv r (Equiv.Perm (Card L))) (benesStepEquiv (L+r))).trans
    seedSandwichShuffle

noncomputable def modifiedPerm (L r : ℕ) (E : Finset (Card r)) (ω : ModifiedCoins L r) :
    Equiv.Perm (Card (L+r)) :=
  butterflyPerm (L+r) (decodeButterfly (L+r) ω.2.1) *
    (modifiedInputTree L r E ω.1 ω.2.2 ω.2.1).perm⁻¹

noncomputable def modifiedCost (L r : ℕ) (E : Finset (Card r))
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (L+r)) (ω : ModifiedCoins L r) : ℕ :=
  InputTree.lowCost (L+r) (L+r) (modifiedInputTree L r E ω.1 ω.2.2 ω.2.1) e ω.2.1

noncomputable def modifiedAssignmentCost (L r : ℕ) (E : Finset (Card (r+1)))
    {ι : Type*} [Fintype ι] (x : ι ↪ Bool × Card (L+r)) (c : ι → Bool)
    (hc : PairRouting.Compatible x c) (ω : ModifiedCoins L r × ModifiedCoins L r) : ℕ :=
  PairRouting.alternatingCycles (PairRouting.coloredEmbedding x c hc)
    (fun b => modifiedPerm L r (exceptionChild E b) (if b then ω.2 else ω.1)) +
  modifiedCost L r (exceptionChild E false) (PairRouting.childEmbedding x c hc false) ω.1 +
  modifiedCost L r (exceptionChild E true) (PairRouting.childEmbedding x c hc true) ω.2

noncomputable def centralFactor (L r : ℕ) (E : Finset (Card r)) (a : ℝ) : ℝ :=
  (Nat.factorial (2^L):ℝ)^(-((2:ℝ)^r-E.card)*a)

end Thorp

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_ModifiedRoutingMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp

noncomputable def modifiedRoutingMoment (L r : ℕ) (E : Finset (Card r))
    {ι : Type*} [Fintype ι] (e f : ι ↪ Card (L+r)) (a : ℝ) : ℝ := by
  classical
  exact finiteMean (fun ω : ModifiedCoins L r =>
    if ∀ i, modifiedPerm L r E ω (e i) = f i then (2:ℝ)^((modifiedCost L r E e ω:ℝ)*a) else 0)

noncomputable def modifiedRowMoment (L r : ℕ) (E : Finset (Card r)) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card (L+r)) (a : ℝ) : ℝ :=
  finiteMean (fun f : ι ↪ Card (L+r) =>
    ((Fintype.card (ι ↪ Card (L+r)):ℝ)*PairRouting.tupleProbability (modifiedPerm L r E) e f)^(1+a))

noncomputable def modifiedNormalization (L r : ℕ) (E : Finset (Card r)) : ℝ :=
  (Nat.factorial (2^(L+r)):ℝ) /
    (((2:ℝ)^r)^(2^(L+r)) * (Nat.factorial (2^L):ℝ)^(2^r-E.card))

noncomputable def modifiedOverhead (L r : ℕ) : ℝ :=
  (((L+r:ℕ):ℝ)*Real.log 2+1)/((2:ℝ)^(L+r)*1000)


namespace DensityTransfer
open scoped BigOperators

noncomputable def applyKernel {X : Type*} [Fintype X] (P : X → X → ℝ)
    (v : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => ∑ y, (P x y : ℂ)*v y)

noncomputable def tailKernel {X : Type*} [Fintype X] (P : X → X → ℝ) (z : ℝ) : X → X → ℝ :=
  fun x y => if z < (Fintype.card X:ℝ)*P x y then P x y else 0

noncomputable def headKernel {X : Type*} [Fintype X] (P : X → X → ℝ) (z : ℝ) : X → X → ℝ :=
  fun x y => if z < (Fintype.card X:ℝ)*P x y then 0 else P x y

end DensityTransfer

end Thorp

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_ModifiedReverseCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp

noncomputable def modifiedReverseCoins (L : ℕ) : (r : ℕ) → ModifiedCoins L r → ModifiedCoins L r
  | 0, ω => ((fun u => butterflyPerm L (decodeButterfly L ω.2.1) * (ω.1 u)⁻¹ *
      butterflyPerm L (decodeButterfly L ω.2.1)),ω.2)
  | r+1, ω =>
      let z := modifiedStepEquiv L r ω
      (modifiedStepEquiv L r).symm
        ((modifiedReverseCoins L r z.1.1,modifiedReverseCoins L r z.1.2),(z.2.2,z.2.1))

lemma modifiedReverseCoins_involutive (L r : ℕ) :
    Function.Involutive (modifiedReverseCoins L r) := by
  induction r with
  | zero =>
      intro ω
      apply Prod.ext
      · funext u
        simp only [modifiedReverseCoins,mul_inv_rev,inv_inv]
        simp [mul_assoc]
      · rfl
  | succ r ih =>
      change ∀ ω, modifiedReverseCoins L r (modifiedReverseCoins L r ω) = ω at ih
      intro ω
      simp only [modifiedReverseCoins,Equiv.apply_symm_apply,ih]
      exact (modifiedStepEquiv L r).symm_apply_apply ω

noncomputable def modifiedReverseEquiv (L r : ℕ) : Equiv.Perm (ModifiedCoins L r) where
  toFun := modifiedReverseCoins L r
  invFun := modifiedReverseCoins L r
  left_inv := modifiedReverseCoins_involutive L r
  right_inv := modifiedReverseCoins_involutive L r

end Thorp

namespace Thorp.Specht
open scoped BigOperators Classical

noncomputable def columnEquiv (μ : YoungDiagram) (j : ℕ) :
    {x : Cell μ // col x = j} ≃ Fin (μ.colLen j) where
  toFun x := ⟨row x.1, by simpa [x.2] using row_lt_colLen x.1⟩
  invFun i := ⟨⟨(i,j), YoungDiagram.mem_iff_lt_colLen.mpr i.2⟩, rfl⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl x.2.symm
  right_inv i := by rfl

noncomputable def columnValues {μ : YoungDiagram} (f : Cell μ → ℕ) (j : ℕ) : Finset ℕ :=
  (Finset.univ.filter (fun x => col x = j)).image f

lemma mem_columnValues {μ : YoungDiagram} (f : Cell μ → ℕ) (x : Cell μ) :
    f x ∈ columnValues f (col x) := by
  classical
  exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩

lemma card_columnValues {μ : YoungDiagram} (f : Cell μ → ℕ)
    (hf : ∀ x y, col x = col y → f x = f y → x = y) (j : ℕ) :
    (columnValues f j).card = μ.colLen j := by
  classical
  rw [columnValues, Finset.card_image_iff.mpr]
  · rw [← Fintype.card_subtype]
    exact Fintype.card_congr (columnEquiv μ j) |>.trans (Fintype.card_fin _)
  intro x hx y hy he
  exact hf x y ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) he

noncomputable def rankCell {μ : YoungDiagram} (f : Cell μ → ℕ)
    (hf : ∀ x y, col x = col y → f x = f y → x = y) (x : Cell μ) : Cell μ :=
  let k := ((columnValues f (col x)).orderIsoOfFin (card_columnValues f hf (col x))).symm
    ⟨f x, mem_columnValues f x⟩
  ⟨(k.val,col x), YoungDiagram.mem_iff_lt_colLen.mpr k.isLt⟩

@[simp] lemma rankCell_col {μ : YoungDiagram} (f : Cell μ → ℕ)
    (hf : ∀ x y, col x = col y → f x = f y → x = y) (x : Cell μ) :
    col (rankCell f hf x) = col x := rfl

lemma rankCell_orderEmb {μ : YoungDiagram} (f : Cell μ → ℕ)
    (hf : ∀ x y, col x = col y → f x = f y → x = y) (x : Cell μ) :
    (columnValues f (col x)).orderEmbOfFin (card_columnValues f hf (col x))
      ⟨row (rankCell f hf x), row_lt_colLen (rankCell f hf x)⟩ = f x := by
  change ((columnValues f (col x)).orderIsoOfFin (card_columnValues f hf (col x))
    (((columnValues f (col x)).orderIsoOfFin (card_columnValues f hf (col x))).symm
      ⟨f x, mem_columnValues f x⟩)).val = f x
  simp

lemma rankCell_injective {μ : YoungDiagram} (f : Cell μ → ℕ)
    (hf : ∀ x y, col x = col y → f x = f y → x = y) :
    Function.Injective (rankCell f hf) := by
  intro x y h
  have hc : col x = col y := by simpa only [rankCell_col] using congrArg (fun z : Cell μ => col z) h
  apply hf x y hc
  have hx := rankCell_orderEmb f hf x
  have hy := rankCell_orderEmb f hf y
  change (columnValues f (col (rankCell f hf x))).orderEmbOfFin
    (card_columnValues f hf (col (rankCell f hf x)))
      ⟨row (rankCell f hf x), row_lt_colLen (rankCell f hf x)⟩ = f x at hx
  rw [h] at hx
  exact hx.symm.trans hy

noncomputable def rankPerm {μ : YoungDiagram} (f : Cell μ → ℕ)
    (hf : ∀ x y, col x = col y → f x = f y → x = y) : Equiv.Perm (Cell μ) :=
  Equiv.ofBijective (rankCell f hf) ((Finite.injective_iff_bijective).mp (rankCell_injective f hf))


@[simp] lemma tabloidAct_inv {μ : YoungDiagram} (p : Equiv.Perm (Cell μ)) :
    tabloidAct p⁻¹ = (tabloidAct p)⁻¹ := by
  ext f x
  simp [tabloidAct,Equiv.Perm.inv_def]

@[simp] lemma tabloidRep_apply {μ : YoungDiagram} (p : Equiv.Perm (Cell μ))
    (v : Tabloid μ → ℂ) (f : Tabloid μ) : tabloidRep μ p v f = v (tabloidAct p⁻¹ f) := rfl

@[simp] lemma mem_colGroup {μ : YoungDiagram} (p : Equiv.Perm (Cell μ)) :
    p ∈ colGroup μ ↔ ∀ x, col (p x) = col x := Iff.rfl


@[simp] lemma permSign_one {α : Type*} [Fintype α] [DecidableEq α] :
    permSign (1 : Equiv.Perm α) = 1 := by simp [permSign]
@[simp] lemma permSign_mul {α : Type*} [Fintype α] [DecidableEq α] (p q : Equiv.Perm α) :
    permSign (p*q) = permSign p * permSign q := by simp [permSign]
@[simp] lemma permSign_inv {α : Type*} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) :
    permSign p⁻¹ = permSign p := by simp [permSign,Equiv.Perm.inv_def]
@[simp] lemma permSign_swap {α : Type*} [Fintype α] [DecidableEq α] {x y : α} (h : x ≠ y) :
    permSign (Equiv.swap x y) = -1 := by simp [permSign, h]
@[simp] lemma conj_permSign {α : Type*} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) :
    starRingEnd ℂ (permSign p) = permSign p := by simp [permSign]

end Thorp.Specht
namespace Thorp.Specht
open scoped BigOperators Classical


noncomputable def pairing {μ : YoungDiagram} (v w : Tabloid μ → ℂ) : ℂ :=
  ∑ f, w f * starRingEnd ℂ (v f)


section Symmetrizer
variable {α V : Type*} [Fintype α] [DecidableEq α] [AddCommGroup V] [Module ℂ V]

noncomputable def symmetrizer (H : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) : Module.End ℂ V :=
  ∑ h : H, ρ h

noncomputable def fiberGroup {β : Type*} (f : α → β) : Subgroup (Equiv.Perm α) where
  carrier := {p | ∀ x, f (p x) = f x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro p q hp hq x; exact (hp (q x)).trans (hq x)
  inv_mem' := by intro p hp x; simpa using (hp (p⁻¹ x)).symm

end Symmetrizer


noncomputable def rowEquiv (μ : YoungDiagram) (i : ℕ) :
    {x : Cell μ // row x = i} ≃ Fin (μ.rowLen i) where
  toFun x := ⟨col x.1, by
    have h := YoungDiagram.mem_iff_lt_rowLen.mp x.1.2
    change col x.1 < μ.rowLen (row x.1) at h
    simpa only [x.2] using h⟩
  invFun j := ⟨⟨(i,j),YoungDiagram.mem_iff_lt_rowLen.mpr j.2⟩,rfl⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.2.symm rfl
  right_inv j := rfl

def rowCost (μ : YoungDiagram) : ℕ := ∑ x : Cell μ, row x

end Thorp.Specht

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_Shapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.Specht
open scoped BigOperators Classical

noncomputable def conjugacyPartition {α : Type*} [Fintype α] [DecidableEq α] :
    ConjClasses (Equiv.Perm α) → Nat.Partition (Fintype.card α) :=
  Quotient.lift Equiv.Perm.partition (fun _ _ hpq => (Equiv.Perm.partition_eq_of_isConj).mp hpq)

end Thorp.Specht

namespace Thorp.FiniteCharacters
open scoped BigOperators Classical

section Group
variable {G : Type*} [Group G] [Fintype G]

noncomputable def classRep (c : ConjClasses G) : G := (ConjClasses.exists_rep c).choose
omit [Fintype G] in
lemma classRep_spec (c : ConjClasses G) : ConjClasses.mk (classRep c) = c :=
  (ConjClasses.exists_rep c).choose_spec

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

noncomputable def characterClass (ρ : Representation ℂ G V) : ConjClasses G → ℂ :=
  fun c => ρ.character (classRep c)

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma characterClass_mk (ρ : Representation ℂ G V) (g : G) :
    characterClass ρ (ConjClasses.mk g) = ρ.character g := by
  have h := ConjClasses.mk_eq_mk_iff_isConj.mp (classRep_spec (ConjClasses.mk g))
  obtain ⟨p,hp⟩ := isConj_iff.mp h
  change ρ.character (classRep (ConjClasses.mk g)) = ρ.character g
  exact (Representation.char_conj ρ _ p).symm.trans (congrArg ρ.character hp)

noncomputable def characterDual (ρ : Representation ℂ G V) :
    (ConjClasses G → ℂ) →ₗ[ℂ] ℂ where
  toFun f := (Nat.card G : ℂ)⁻¹ * ∑ g, f (ConjClasses.mk g) * ρ.character g⁻¹
  map_add' f h := by simp [Finset.sum_add_distrib,add_mul,mul_add]
  map_smul' a f := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp_rw [mul_assoc]
    rw [←Finset.mul_sum]
    ring

lemma characterDual_characterClass (ρ : Representation ℂ G V)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ] :
    characterDual ρ (characterClass σ) = if Nonempty (Representation.Equiv ρ σ) then 1 else 0 := by
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := G)).ne')
  change (Nat.card G : ℂ)⁻¹ * ∑ g, characterClass σ (ConjClasses.mk g) * ρ.character g⁻¹ = _
  simp only [characterClass_mk]
  exact Representation.char_orthonormal σ ρ

end Group

end Thorp.FiniteCharacters

namespace Thorp.PermutationHilbert

section
open scoped BigOperators ComplexConjugate Classical
open Complex

variable {X : Type*} [Fintype X]

noncomputable def act (p : Equiv.Perm X) : H X ≃ₗᵢ[ℂ] H X :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ p

@[simp] lemma act_apply (p : Equiv.Perm X) (v : H X) (x : X) :
    act p v x = v (p⁻¹ x) := rfl

end
open scoped BigOperators Classical

end Thorp.PermutationHilbert
namespace Thorp.Specht
open scoped BigOperators Classical

lemma hilbert_action (μ : YoungDiagram) (p : Equiv.Perm (Cell μ)) (v : Tabloid μ → ℂ) :
    hilbertEquiv μ (tabloidRep μ p v) =
      PermutationHilbert.act (tabloidAct p) (hilbertEquiv μ v) := by
  ext f
  simp [hilbertEquiv,PermutationHilbert.act_apply]


section FiberGroup
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

noncomputable def fiberGroupEquiv (f : α → β) :
    fiberGroup f ≃ (∀ b, Equiv.Perm {x // f x = b}) where
  toFun p b :=
    { toFun x := ⟨p.1 x.1,(p.2 x.1).trans x.2⟩
      invFun x := ⟨p.1⁻¹ x.1, by
        have hh := p.2 (p.1⁻¹ x.1)
        simp only [Equiv.Perm.inv_def,Equiv.apply_symm_apply] at hh
        exact hh.symm.trans x.2⟩
      left_inv x := by apply Subtype.ext; simp
      right_inv x := by apply Subtype.ext; simp }
  invFun q :=
    ⟨(Equiv.sigmaFiberEquiv f).permCongr (Equiv.Perm.sigmaCongrRight q),
      fun x => (q (f x) ⟨x,rfl⟩).2⟩
  left_inv p := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rfl
  right_inv q := by
    funext b
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (q (f x.1) ⟨x.1,rfl⟩).1 = (q b x).1
    cases x with
    | mk x hx => dsimp only at *; subst b; rfl

end FiberGroup

noncomputable def rowGroup (μ : YoungDiagram) : Subgroup (Equiv.Perm (Cell μ)) :=
  fiberGroup (rowIndex (μ := μ))

noncomputable def colIndex {μ : YoungDiagram} (x : Cell μ) : Fin (μ.rowLen 0) :=
  ⟨col x, (YoungDiagram.mem_iff_lt_rowLen.mp x.2).trans_le (μ.rowLen_anti 0 (row x) (Nat.zero_le _))⟩

noncomputable instance tabloidMulAction (μ : YoungDiagram) : MulAction (Equiv.Perm (Cell μ)) (Tabloid μ) where
  smul p f := tabloidAct p f
  one_smul f := by change tabloidAct 1 f = f; rw [tabloidAct_one]; rfl
  mul_smul p q f := by change tabloidAct (p*q) f = tabloidAct p (tabloidAct q f); rw [tabloidAct_mul]; rfl

abbrev Tail (μ : YoungDiagram) := {x : Cell μ // row x ≠ 0}

lemma rowLen_zero_le_card (μ : YoungDiagram) : μ.rowLen 0 ≤ μ.card := by
  have h := Fintype.card_subtype_le (fun x : Cell μ => row x=0)
  rwa [Fintype.card_congr (rowEquiv μ 0),Fintype.card_fin,card_cell] at h

noncomputable def tailColumnEquiv (μ : YoungDiagram) (j : Fin (μ.rowLen 0)) :
    {x : Tail μ // colIndex x.1 = j} ≃ Fin (μ.colLen j-1) where
  toFun x := ⟨row x.1.1-1, by
    have hx := row_lt_colLen x.1.1
    have hc : col x.1.1 = j := congrArg Fin.val x.2
    rw [hc] at hx
    have hz := x.1.2
    omega⟩
  invFun i := ⟨⟨⟨(i+1,j),YoungDiagram.mem_iff_lt_colLen.mpr (by omega)⟩,by simp [row]⟩,rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change row x.1.1 - 1 + 1 = row x.1.1
      have := x.1.2
      omega
    · exact (congrArg Fin.val x.2).symm
  right_inv i := by apply Fin.ext; simp [row]

noncomputable def tailSet {μ : YoungDiagram} (f : Tabloid μ) : Finset (Cell μ) :=
  Finset.univ.filter (fun x => (f.1 x).val ≠ 0)

@[simp] lemma mem_tailSet {μ : YoungDiagram} (f : Tabloid μ) (x : Cell μ) :
    x ∈ tailSet f ↔ (f.1 x).val ≠ 0 := by simp [tailSet]

noncomputable def footprint (μ : YoungDiagram) (A : Finset (Cell μ)) : Finset (Tabloid μ) :=
  Finset.univ.filter (fun f => tailSet f ⊆ A)

noncomputable def fixedHilbert (μ : YoungDiagram) (A : Finset (Cell μ)) :
    Submodule ℂ (PermutationHilbert.H (Tabloid μ)) where
  carrier := {v | v ∈ hilbertSpace μ ∧ ∀ p : Equiv.Perm (Cell μ),
    (∀ x ∈ A, p x=x) → PermutationHilbert.act (tabloidAct p) v=v}
  zero_mem' := ⟨Submodule.zero_mem _,fun p hp => map_zero _⟩
  add_mem' := fun hv hw => ⟨Submodule.add_mem _ hv.1 hw.1,fun p hp => by
    rw [map_add,hv.2 p hp,hw.2 p hp]⟩
  smul_mem' := fun c v hv => ⟨Submodule.smul_mem _ c hv.1,fun p hp => by
    rw [map_smul,hv.2 p hp]⟩

end Thorp.Specht

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

def IsUnitary (ρ : Representation ℂ G V) : Prop :=
  ∀ g v w, inner ℂ (ρ g v) (ρ g w) = inner ℂ v w

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma unitary_inner_inv (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) (v w : V) :
    inner ℂ v (ρ g⁻¹ w) = inner ℂ (ρ g v) w := by
  have h := hρ g v (ρ g⁻¹ w)
  have he : ρ g (ρ g⁻¹ w) = w := by
    change (ρ g * ρ g⁻¹) w = w
    rw [←map_mul,mul_inv_cancel,map_one]
    rfl
  rw [he] at h
  exact h.symm

end Thorp.UnitaryFinite

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_AverageMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

noncomputable def averageMap (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (A : V →ₗ[ℂ] W) : Representation.IntertwiningMap ρ σ where
  toLinearMap := ∑ g, (σ g).comp (A.comp (ρ g⁻¹))
  isIntertwining' h := by
    ext v
    simp only [LinearMap.comp_apply,LinearMap.sum_apply,map_sum]
    apply Fintype.sum_equiv (Equiv.mulLeft h⁻¹)
    intro g
    simp only [Equiv.coe_mulLeft,mul_inv_rev,inv_inv,map_mul,Module.End.mul_apply]
    have hh (w : W) : σ h (σ h⁻¹ w)=w := by
      change (σ h*σ h⁻¹) w=w
      rw [←map_mul,mul_inv_cancel,map_one]
      rfl
    rw [hh]

omit [FiniteDimensional ℂ V] in
lemma averageMap_self_trace (ρ : Representation ℂ G V) (A : Module.End ℂ V) :
    LinearMap.trace ℂ V (averageMap ρ ρ A).toLinearMap =
      (Fintype.card G:ℂ) * LinearMap.trace ℂ V A := by
  change LinearMap.trace ℂ V (∑ g, ρ g * A * ρ g⁻¹) = _
  rw [map_sum]
  have hj (g : G) : LinearMap.trace ℂ V (ρ g*A*ρ g⁻¹) = LinearMap.trace ℂ V A := by
    rw [LinearMap.trace_mul_cycle,←map_mul,inv_mul_cancel,map_one,one_mul]
  simp only [hj,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

lemma averageMap_scalar (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (A : Module.End ℂ V) :
    ∃ c : ℂ, (averageMap ρ ρ A).toLinearMap = c • LinearMap.id ∧
      c * (Module.finrank ℂ V:ℂ) = (Fintype.card G:ℂ)*LinearMap.trace ℂ V A := by
  obtain ⟨c,hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).surjective (averageMap ρ ρ A)
  have he : (averageMap ρ ρ A).toLinearMap = c • LinearMap.id := by
    rw [←hc]
    rfl
  refine ⟨c,he,?_⟩
  rw [←averageMap_self_trace ρ A,he,map_smul,LinearMap.trace_id,smul_eq_mul]

theorem coefficient_orthogonality (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (u v w z : V) :
    (Module.finrank ℂ V:ℂ) * ∑ g, inner ℂ u (ρ g v) * inner ℂ (ρ g w) z =
      (Fintype.card G:ℂ) * inner ℂ w v * inner ℂ u z := by
  obtain ⟨c,hc,htrace⟩ := averageMap_scalar ρ (InnerProductSpace.rankOne ℂ v w).toLinearMap
  rw [InnerProductSpace.trace_rankOne] at htrace
  have happ := congrArg (fun A : Module.End ℂ V => inner ℂ u (A z)) hc
  change inner ℂ u ((∑ g, ρ g * (InnerProductSpace.rankOne ℂ v w).toLinearMap * ρ g⁻¹) z) = _ at happ
  simp only [LinearMap.sum_apply,Module.End.mul_apply,ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply,map_smul,unitary_inner_inv ρ hρ,inner_sum,
    inner_smul_right,LinearMap.smul_apply,LinearMap.id_apply] at happ
  have hsum : ∑ g, inner ℂ u (ρ g v) * inner ℂ (ρ g w) z = c * inner ℂ u z := by
    simpa only [mul_comm] using happ
  rw [hsum]
  calc
    _ = (c*(Module.finrank ℂ V:ℂ))*inner ℂ u z := by ring
    _ = _ := by rw [htrace]

end Thorp.UnitaryFinite
namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G X : Type*} [Group G] [Fintype G] [Fintype X]
  (a : G →* Equiv.Perm X) (x₀ : X) (ha : ∀ x, ∃ g, a g x₀=x)

noncomputable def representative (x : X) : G := Classical.choose (ha x)

omit [Fintype G] [Fintype X] in
lemma representative_apply (x : X) : a (representative a x₀ ha x) x₀=x :=
  Classical.choose_spec (ha x)

include ha in
lemma orbit_sum (F : X → ℂ) :
    (Fintype.card X:ℂ)*∑ g, F (a g x₀) = (Fintype.card G:ℂ)*∑ x, F x := by
  have ht (x : X) : ∑ g, F (a g x)=∑ g, F (a g x₀) := by
    obtain ⟨t,rfl⟩ := ha x
    symm
    apply Fintype.sum_equiv (Equiv.mulRight t⁻¹)
    intro g
    simp
  calc
    _ = ∑ x : X, ∑ g : G, F (a g x) := by simp only [ht,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ = ∑ g : G, ∑ x : X, F (a g x) := Finset.sum_comm
    _ = ∑ g : G, ∑ x : X, F x := by
      apply Finset.sum_congr rfl
      intro g _
      exact Equiv.sum_comp (a g) F
    _ = _ := by simp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

def IsFixed (w : V) : Prop := ∀ g, a g x₀=x₀ → ρ g w=w

noncomputable def coefficient (w v : V) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => inner ℂ (ρ (representative a x₀ ha x) w) v)

omit [Fintype G] [Fintype X] [FiniteDimensional ℂ V] in
lemma coefficient_at (w : V) (hw : IsFixed a x₀ ρ w) (v : V) (g : G) :
    coefficient a x₀ ha ρ w v (a g x₀) = inner ℂ (ρ g w) v := by
  let r := representative a x₀ ha (a g x₀)
  have hr : a r x₀=a g x₀ := representative_apply a x₀ ha _
  have hs : a (g⁻¹*r) x₀=x₀ := by
    simp only [map_mul,Equiv.Perm.mul_apply]
    rw [hr,←Equiv.Perm.mul_apply,←map_mul,inv_mul_cancel,map_one]
    rfl
  have he := congrArg (ρ g) (hw (g⁻¹*r) hs)
  have hh : ρ r w=ρ g w := by
    simpa only [map_mul,Module.End.mul_apply,←Module.End.mul_apply,←map_mul,
      mul_inv_cancel_left] using he
  change inner ℂ (ρ r w) v= _
  rw [hh]

lemma coefficient_inner [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    (w z : V) (hw : IsFixed a x₀ ρ w) (hz : IsFixed a x₀ ρ z) (v t : V) :
    (Module.finrank ℂ V:ℂ)*inner ℂ (coefficient a x₀ ha ρ w v) (coefficient a x₀ ha ρ z t) =
      (Fintype.card X:ℂ)*inner ℂ z w*inner ℂ v t := by
  have hs := orbit_sum a x₀ ha (fun x => star (coefficient a x₀ ha ρ w v x)*coefficient a x₀ ha ρ z t x)
  simp only [coefficient_at a x₀ ha ρ w hw,coefficient_at a x₀ ha ρ z hz] at hs
  simp only [←starRingEnd_apply,inner_conj_symm] at hs
  simp only [starRingEnd_apply] at hs
  have ho := coefficient_orthogonality ρ hρ v w z t
  have hcard : (Fintype.card G:ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hcard
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply,starRingEnd_apply]
  have hsum : ∑ x, coefficient a x₀ ha ρ z t x * star (coefficient a x₀ ha ρ w v x) =
      ∑ x, star (coefficient a x₀ ha ρ w v x)*coefficient a x₀ ha ρ z t x := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum]
  calc
    _ = (Module.finrank ℂ V:ℂ)*((Fintype.card G:ℂ)*∑ x,
        star (coefficient a x₀ ha ρ w v x)*coefficient a x₀ ha ρ z t x) := by ring
    _ = (Fintype.card X:ℂ)*((Module.finrank ℂ V:ℂ)*∑ g,
        inner ℂ v (ρ g w)*inner ℂ (ρ g z) t) := by rw [←hs]; ring
    _ = _ := by rw [ho]; ring

noncomputable def normalizedCoefficient (w v : V) : EuclideanSpace ℂ X :=
  (Real.sqrt ((Module.finrank ℂ V:ℝ)/(Fintype.card X:ℝ)) : ℂ) • coefficient a x₀ ha ρ w v

lemma normalizedCoefficient_inner [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    (w z : V) (hw : IsFixed a x₀ ρ w) (hz : IsFixed a x₀ ρ z) (v t : V) :
    inner ℂ (normalizedCoefficient a x₀ ha ρ w v) (normalizedCoefficient a x₀ ha ρ z t) =
      inner ℂ z w*inner ℂ v t := by
  let : Nonempty X := ⟨x₀⟩
  have hX : (Fintype.card X:ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (Real.sqrt ((Module.finrank ℂ V:ℝ)/(Fintype.card X:ℝ)) : ℂ)^2 =
      (Module.finrank ℂ V:ℂ)/(Fintype.card X:ℂ) := by
    rw [←Complex.ofReal_pow,Real.sq_sqrt (by positivity)]
    simp
  simp only [normalizedCoefficient,inner_smul_left,inner_smul_right]
  simp only [Complex.conj_ofReal]
  rw [←mul_assoc,←pow_two,hs]
  have hi := coefficient_inner a x₀ ha ρ hρ w z hw hz v t
  field_simp
  simpa only [mul_assoc] using hi

end Thorp.UnitaryFinite

namespace Thorp.FiniteConvolution
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]

noncomputable def conv (p q : G → ℝ) (g : G) : ℝ := ∑ h, p h*q (h⁻¹*g)
noncomputable def power (p : G → ℝ) : ℕ → G → ℝ
  | 0 => fun g => if g=1 then 1 else 0
  | n+1 => conv p (power p n)

lemma conv_nonneg {p q : G → ℝ} (hp : ∀ g, 0 ≤ p g) (hq : ∀ g, 0 ≤ q g) :
    ∀ g, 0 ≤ conv p q g := fun _ => Finset.sum_nonneg (fun h _ => mul_nonneg (hp h) (hq _))

lemma conv_pos_of {p q : G → ℝ} (hp : ∀ g, 0 ≤ p g) (hq : ∀ g, 0 ≤ q g)
    {a b : G} (ha : 0 < p a) (hb : 0 < q b) : 0 < conv p q (a*b) := by
  apply lt_of_lt_of_le (mul_pos ha hb)
  have h := Finset.single_le_sum (fun g _ => mul_nonneg (hp g) (hq (g⁻¹*(a*b))))
    (Finset.mem_univ a)
  simpa [conv] using h

lemma sum_conv (p q : G → ℝ) : ∑ g, conv p q g=(∑ g,p g)*(∑ g,q g) := by
  unfold conv
  rw [Finset.sum_comm,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  rw [←Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ (fun _ => rfl)

lemma power_nonneg {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) : ∀ n g, 0 ≤ power p n g := by
  intro n
  induction n with
  | zero => intro g; simp only [power]; split_ifs  <;> norm_num
  | succ n ih => exact conv_nonneg hp ih

lemma sum_power {p : G → ℝ} (hp : ∑ g,p g=1) : ∀ n, ∑ g,power p n g=1 := by
  intro n
  induction n with
  | zero => simp [power]
  | succ n ih => rw [power,sum_conv,hp,ih,one_mul]

lemma power_list_pos {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (l : List G)
    (hl : ∀ g ∈ l, 0 < p g) : 0 < power p l.length l.prod := by
  induction l with
  | nil => simp [power]
  | cons a l ih =>
    simpa only [List.length_cons,List.prod_cons,power] using
      conv_pos_of hp (power_nonneg hp l.length) (hl a (by simp))
        (ih (fun g hg => hl g (by simp [hg])))

lemma power_pos_mono {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (h1 : 0 < p 1)
    {n m : ℕ} (hnm : n ≤ m) {g : G} (hg : 0 < power p n g) : 0 < power p m g := by
  induction m, hnm using Nat.le_induction with
  | base => exact hg
  | succ m _ ih =>
    simpa only [one_mul,power] using conv_pos_of hp (power_nonneg hp m) h1 ih

theorem exists_positive_power {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (h1 : 0 < p 1)
    (hgen : Subgroup.closure {g | 0 < p g}=⊤) :
    ∃ n : ℕ, ∀ g, 0 < power p (2^n) g := by
  have hx (g : G) : g ∈ Submonoid.closure {g | 0 < p g} := by
    rw [←Subgroup.closure_toSubmonoid_of_finite,hgen]
    trivial
  choose l hl hprod using fun g => Submonoid.exists_list_of_mem_closure (hx g)
  let n := Finset.univ.sup (fun g => (l g).length)
  refine ⟨n,fun g => ?_⟩
  have hlen : (l g).length ≤ n := Finset.le_sup (f := fun g => (l g).length) (Finset.mem_univ g)
  have hpow : n ≤ 2^n := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hpos := power_list_pos hp (l g) (hl g)
  rw [hprod g] at hpos
  exact power_pos_mono hp h1 (hlen.trans hpow) hpos

structure Minorant (p : G → ℝ) where
  exponent : ℕ
  mass : ℝ
  mass_pos : 0 < mass
  mass_le_one : mass ≤ 1
  lower : ∀ g, mass/(Fintype.card G:ℝ) ≤ power p (2^exponent) g

noncomputable def minorant {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (hsum : ∑ g,p g=1)
    (h1 : 0 < p 1) (hgen : Subgroup.closure {g | 0 < p g}=⊤) : Minorant p := by
  let n := Classical.choose (exists_positive_power hp h1 hgen)
  have hn := Classical.choose_spec (exists_positive_power hp h1 hgen)
  let a := Finset.univ.inf' Finset.univ_nonempty (power p (2^n))
  have ha : 0 < a := (Finset.lt_inf'_iff _).mpr (fun g _ => hn g)
  have hag (g : G) : a ≤ power p (2^n) g := Finset.inf'_le _ (Finset.mem_univ g)
  have hN : (0:ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  have hsum' := Finset.sum_le_sum (s := Finset.univ) (fun g _ => hag g)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,sum_power hsum] at hsum'
  refine ⟨n,(Fintype.card G:ℝ)*a,mul_pos hN ha,hsum',fun g => ?_⟩
  have he : (Fintype.card G:ℝ)*a/(Fintype.card G:ℝ)=a := by field_simp
  rw [he]
  exact hag g

end Thorp.FiniteConvolution
namespace Thorp.UnitaryFinite

section
open scoped BigOperators ComplexConjugate Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] in
@[simp] lemma continuousRepresentation_apply (ρ : Representation ℂ G V) (g : G) (v : V) :
    continuousRepresentation ρ g v=ρ g v := rfl

noncomputable def weightedOperator (ρ : Representation ℂ G V) (p : G → ℝ) : V →L[ℂ] V :=
  ∑ g, (p g : ℂ) • continuousRepresentation ρ g

noncomputable def uniformOperator (ρ : Representation ℂ G V) : V →L[ℂ] V :=
  weightedOperator ρ (fun _ => (Fintype.card G:ℝ)⁻¹)

end
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def minorantGap {p : G → ℝ} (c : FiniteConvolution.Minorant p) : ℝ :=
  1-c.mass/(2*(2:ℝ)^c.exponent)

end Thorp.UnitaryFinite
namespace Thorp
open scoped BigOperators Classical

def butterflyIdentity : (d : ℕ) → Butterfly d
  | 0 => ()
  | d+1 => (fun _ => false,fun _ => butterflyIdentity d)

lemma pairSwitch_false (d : ℕ) : pairSwitch (d := d) (fun _ => false)=1 := by
  apply Equiv.ext
  intro x
  change switchFun (fun _ => false) x=x
  simp [switchFun]

lemma childLift_one (d : ℕ) : childLift (d := d) (fun _ => 1)=1 := by
  ext x i
  simp [childLift]

lemma butterflyIdentity_perm (d : ℕ) : butterflyPerm d (butterflyIdentity d)=1 := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [butterflyIdentity,butterflyPerm,ih,pairSwitch_false,childLift_one,mul_one]

noncomputable def childInjection (d : ℕ) (b : Bool) : Equiv.Perm (Card d) →* Equiv.Perm (Card (d+1)) where
  toFun p := childLift (fun c => if c=b then p else 1)
  map_one' := by simpa only [ite_self] using childLift_one d
  map_mul' p q := by
    rw [childLift_mul]
    congr 1
    funext c
    split_ifs <;> simp

lemma childInjection_swap (d : ℕ) (b : Bool) (u v : Card d) :
    childInjection d b (Equiv.swap u v)=Equiv.swap (Fin.cons b u) (Fin.cons b v) := by
  apply Equiv.ext
  intro x
  obtain ⟨c,w,rfl⟩ : ∃ c w, x=Fin.cons c w := ⟨x 0,Fin.tail x,(Fin.cons_self_tail x).symm⟩
  change (Fin.cons c ((if c=b then Equiv.swap u v else 1) w) : Card (d+1))=_
  by_cases hc : c=b
  · subst c
    simp only [↓reduceIte]
    rw [Equiv.swap_apply_def]
    split_ifs with h₁ h₂
    · subst w; simp
    · subst w; simp
    · rw [Equiv.swap_apply_of_ne_of_ne]
      · exact fun h => h₁ (by simpa using congrArg Fin.tail h)
      · exact fun h => h₂ (by simpa using congrArg Fin.tail h)
  · rw [ite_eq_right hc,Equiv.Perm.one_apply,Equiv.swap_apply_of_ne_of_ne]
    · intro h; exact hc (by simpa using congrArg (fun z => z 0) h)
    · intro h; exact hc (by simpa using congrArg (fun z => z 0) h)

lemma pairSwitch_single (d : ℕ) (u : Card d) :
    pairSwitch (fun v => decide (v=u))=Equiv.swap (Fin.cons false u) (Fin.cons true u) := by
  apply Equiv.ext
  intro x
  obtain ⟨c,w,rfl⟩ : ∃ c w, x=Fin.cons c w := ⟨x 0,Fin.tail x,(Fin.cons_self_tail x).symm⟩
  change switchFun (fun v => decide (v=u)) (Fin.cons c w)=_
  by_cases h : w=u
  · subst w
    cases c <;> simp [switchFun]
  · have ha : (Fin.cons c w : Card (d+1))≠Fin.cons false u := fun he => h (by simpa using congrArg Fin.tail he)
    have hb : (Fin.cons c w : Card (d+1))≠Fin.cons true u := fun he => h (by simpa using congrArg Fin.tail he)
    simp [switchFun,h,Equiv.swap_apply_of_ne_of_ne ha hb]

theorem butterfly_generates (d : ℕ) (H : Subgroup (Equiv.Perm (Card d)))
    (hH : ∀ ω : Butterfly d, butterflyPerm d ω∈H) : H=⊤ := by
  induction d with
  | zero =>
    apply top_unique
    intro p _
    have hp : p=1 := Subsingleton.elim _ _
    rw [hp]
    exact H.one_mem
  | succ d ih =>
    have hchild (b : Bool) (p : Equiv.Perm (Card d)) : childInjection d b p∈H := by
      have hc : H.comap (childInjection d b)=⊤ := by
        apply ih
        intro ω
        change childLift (fun c => if c=b then butterflyPerm d ω else 1)∈H
        have h := hH ((fun _ => false),fun c => if c=b then ω else butterflyIdentity d)
        simpa only [butterflyPerm,pairSwitch_false,one_mul,apply_ite,butterflyIdentity_perm] using h
      have hp : p∈H.comap (childInjection d b) := by rw [hc]; trivial
      exact hp
    have hpair (u : Card d) : Equiv.swap (Fin.cons false u) (Fin.cons true u)∈H := by
      rw [←pairSwitch_single]
      have h := hH ((fun v => decide (v=u)),fun _ => butterflyIdentity d)
      simpa only [butterflyPerm,butterflyIdentity_perm,childLift_one,mul_one] using h
    have hswap (x y : Card (d+1)) : Equiv.swap x y∈H := by
      have ht (a b : Bool) (u : Card d) : Equiv.swap (Fin.cons a u) (Fin.cons b u)∈H := by
        cases a <;> cases b
        · rw [Equiv.swap_self]; exact H.one_mem
        · exact hpair _
        · rw [Equiv.swap_comm]; exact hpair _
        · rw [Equiv.swap_self]; exact H.one_mem
      have h₁ : Equiv.swap x (Fin.cons (y 0) (Fin.tail x))∈H := by
        convert ht (x 0) (y 0) (Fin.tail x) using 1
        rw [Fin.cons_self_tail]
      have h₂ := hchild (y 0) (Equiv.swap (Fin.tail x) (Fin.tail y))
      rw [childInjection_swap,Fin.cons_self_tail] at h₂
      exact SubmonoidClass.swap_mem_trans H h₁ h₂
    rw [eq_top_iff,←Equiv.Perm.closure_isSwap,Subgroup.closure_le]
    rintro _ ⟨x,y,_,rfl⟩
    exact hswap x y

variable {Ω G : Type*} [Fintype Ω] [Fintype G]

noncomputable def sampleLaw (P : Ω → G) (g : G) : ℝ :=
  finiteMean (fun ω => if P ω=g then 1 else 0)

omit [Fintype G] in
lemma sampleLaw_nonneg (P : Ω → G) (g : G) : 0 ≤ sampleLaw P g :=
  finiteMean_nonneg (fun _ => by split_ifs <;> norm_num)

lemma sampleLaw_sum [Nonempty Ω] (P : Ω → G) : ∑ g,sampleLaw P g=1 := by
  unfold sampleLaw
  rw [←finiteMean_sum]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte,finiteMean_const]

omit [Fintype G] in
lemma sampleLaw_pos_iff [Nonempty Ω] (P : Ω → G) (g : G) :
    0<sampleLaw P g ↔ ∃ ω,P ω=g := by
  unfold sampleLaw finiteMean
  rw [div_pos_iff_of_pos_right (Nat.cast_pos.mpr Fintype.card_pos)]
  rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => by split_ifs <;> norm_num)]
  simp only [Finset.mem_univ,true_and]
  apply exists_congr
  intro ω
  split_ifs <;> simp_all

end Thorp

namespace Thorp
open scoped BigOperators Classical

lemma palindrome_identity (d : ℕ) : ∃ ω,palindromePerm d ω=1 := by
  refine ⟨((butterflyCoinEquiv d).symm (butterflyIdentity d),
    (butterflyCoinEquiv d).symm (butterflyIdentity d)),?_⟩
  exact mul_inv_cancel _

lemma palindrome_range_contains_butterfly (d : ℕ) (ω : Butterfly d) :
    ∃ ξ,palindromePerm d ξ=butterflyPerm d ω := by
  refine ⟨((butterflyCoinEquiv d).symm ω,(butterflyCoinEquiv d).symm (butterflyIdentity d)),?_⟩
  unfold palindromePerm
  have h (β : Butterfly d) : decodeButterfly d ((butterflyCoinEquiv d).symm β)=β :=
    (butterflyCoinEquiv d).apply_symm_apply β
  rw [h,h,butterflyIdentity_perm,show (1 : Equiv.Perm (Card d)).symm=1 from rfl,mul_one]

lemma palindrome_support_generates (d : ℕ) :
    Subgroup.closure {g | 0<sampleLaw (palindromePerm d) g}=⊤ := by
  apply butterfly_generates
  intro ω
  apply Subgroup.subset_closure
  exact (sampleLaw_pos_iff _ _).mpr (palindrome_range_contains_butterfly d ω)

noncomputable def palindromeMinorant (d : ℕ) :
    FiniteConvolution.Minorant (sampleLaw (palindromePerm d)) :=
  FiniteConvolution.minorant (sampleLaw_nonneg _) (sampleLaw_sum _)
    ((sampleLaw_pos_iff _ _).mpr (palindrome_identity d)) (palindrome_support_generates d)

noncomputable def blockGap (d : ℕ) : ℝ := UnitaryFinite.minorantGap (palindromeMinorant d)

end Thorp

namespace Thorp.CommutingBlocks
open scoped BigOperators Classical
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {ι : Type*} [Fintype ι]

variable [DecidableEq ι]
variable (P : ι → V →L[ℂ] V) (hcomm : ∀ i j, Commute (P i) (P j))

noncomputable def choice (E : Finset ι) (i : ι) : V →L[ℂ] V :=
  if i∈E then 1-P i else P i

include hcomm
omit [CompleteSpace V] [Fintype ι] in
lemma choice_commute (E F : Finset ι) (i j : ι) :
    Commute (choice P E i) (choice P F j) := by
  unfold choice
  split_ifs
  · exact (Commute.one_left _).sub_left ((Commute.one_right _).sub_right (hcomm i j))
  · exact (Commute.one_left _).sub_left (hcomm i j)
  · exact (Commute.one_right _).sub_right (hcomm i j)
  · exact hcomm i j

noncomputable def sector (s E : Finset ι) : V →L[ℂ] V :=
  s.noncommProd (choice P E) (fun i _ j _ _ => choice_commute P hcomm E E i j)

end Thorp.CommutingBlocks

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_BlockProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.CommutingBlocks
open scoped BigOperators Classical
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {ι : Type*} [Fintype ι]
variable [DecidableEq ι]
variable (P : ι → V →L[ℂ] V) (hcomm : ∀ i j, Commute (P i) (P j))
include hcomm

noncomputable def blockProduct (A : ι → V →L[ℂ] V)
    (hA : ∀ i j, Commute (A i) (A j)) (s : Finset ι) : V →L[ℂ] V :=
  s.noncommProd A (fun i _ j _ _ => hA i j)

noncomputable def blocks (A : ι → V →L[ℂ] V) (hA : ∀ i j, Commute (A i) (A j)) : V →L[ℂ] V :=
  blockProduct A hA Finset.univ

noncomputable def coarse (E : Finset ι) : V →L[ℂ] V :=
  Eᶜ.noncommProd P (fun i _ j _ _ => hcomm i j)


end Thorp.CommutingBlocks

namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma sampleOperator_uniform (ρ : Representation ℂ G V) : sampleOperator ρ (id : G → G)=uniformOperator ρ := by
  simp only [sampleOperator,uniformOperator,weightedOperator,Complex.ofReal_inv,Complex.ofReal_natCast,
    Finset.smul_sum,id_eq]

end Thorp.UnitaryFinite

namespace Thorp.FiniteAverage
open scoped BigOperators Classical
variable {I Ω A : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    [Ring A] [Algebra ℂ A]

noncomputable def orderedProduct : MultilinearMap ℂ (fun _ : I => A) A :=
  MultilinearMap.domDomCongr (Fintype.equivFin I).symm
    (MultilinearMap.mkPiAlgebraFin ℂ (Fintype.card I) A)

end Thorp.FiniteAverage
namespace Thorp.FiniteCharacters
open Module
open scoped BigOperators Classical

variable {G ι : Type*} [Group G] [Fintype G] [Fintype ι]
variable (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
variable (ρ : ∀ i, Representation ℂ G (V i)) [∀ i, Representation.IsIrreducible (ρ i)]
variable (hneq : ∀ i j, i≠j → ¬Nonempty (Representation.Equiv (ρ i) (ρ j)))
  (hcard : Nat.card (ConjClasses G)≤Fintype.card ι)
include hneq hcard

lemma character_expansion (f : ConjClasses G → ℂ) :
    f=∑ i, characterDual (ρ i) f • characterClass (ρ i) := by
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  have horth (i j : ι) : characterDual (ρ i) (characterClass (ρ j))=if i=j then 1 else 0 := by
    rw [characterDual_characterClass]
    by_cases h : i=j
    · subst j; rw [ite_eq_left ⟨Representation.Equiv.refl _⟩,ite_eq_left rfl]
    · rw [ite_eq_right h,ite_eq_right (hneq i j h)]
  have hLI : LinearIndependent ℂ (fun i => characterClass (ρ i)) := by
    apply LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun i => characterDual (ρ i))
    · intro i j hij; exact (horth i j).trans (ite_eq_right hij)
    · intro i; simpa using horth i i
  have heq : Fintype.card ι=Module.finrank ℂ (ConjClasses G → ℂ) := by
    apply Nat.le_antisymm hLI.fintype_card_le_finrank
    simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
      smul_eq_mul,mul_one,Nat.card_eq_fintype_card] using hcard
  let b := Basis.mk hLI (by rw [hLI.span_eq_top_of_card_eq_finrank' heq])
  have hb (i : ι) : b i=characterClass (ρ i) := Basis.mk_apply _ _ _
  have hd (i : ι) : b.coord i=characterDual (ρ i) := by
    apply b.ext
    intro j
    rw [hb,horth]
    simp only [←hb,Basis.coord_apply,Basis.repr_self,Finsupp.single_apply]
    split_ifs <;> simp_all
  have h := b.sum_repr f
  simpa only [hb,show ∀ i,b.repr f i=characterDual (ρ i) f from fun i => congrArg (fun l => l f) (hd i)] using h.symm

theorem sum_dimension_sq : ∑ i, (Module.finrank ℂ (V i))^2=Fintype.card G := by
  let f : ConjClasses G → ℂ := fun c => if c=ConjClasses.mk (1:G) then 1 else 0
  have hf (g : G) : f (ConjClasses.mk g)=if g=1 then 1 else 0 := by
    simp only [f,ConjClasses.mk_eq_mk_iff_isConj,isConj_one_left]
  have hd (i : ι) : characterDual (ρ i) f=(Fintype.card G:ℂ)⁻¹*(Module.finrank ℂ (V i):ℂ) := by
    change (Nat.card G:ℂ)⁻¹ * ∑ g, f (ConjClasses.mk g)*(ρ i).character g⁻¹=_
    simp only [hf,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte,inv_one,
      Representation.char_one,Nat.card_eq_fintype_card]
  have he := congrFun (character_expansion V ρ hneq hcard f) (ConjClasses.mk (1:G))
  rw [hf,ite_eq_left rfl] at he
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hd,characterClass_mk,Representation.char_one] at he
  have hN : (Fintype.card G:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (∑ i,(Module.finrank ℂ (V i):ℂ)^2)=(Fintype.card G:ℂ) := by
    calc
      _ = (Fintype.card G:ℂ) * ∑ i,(Fintype.card G:ℂ)⁻¹ *
          (Module.finrank ℂ (V i):ℂ)*(Module.finrank ℂ (V i):ℂ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        field_simp
      _ = _ := by rw [←he,mul_one]
  exact_mod_cast hs

end Thorp.FiniteCharacters

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
  [InnerProductSpace ℂ V] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma averageMap_zero (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ]
    (hne : ¬Nonempty (Representation.Equiv ρ σ)) (A : V →ₗ[ℂ] W) :
    averageMap ρ σ A=0 := by
  rcases Representation.IsIrreducible.bijective_or_eq_zero (averageMap ρ σ A) with h|h
  · exact (hne ⟨Representation.IntertwiningMap.ofBijective _ h⟩).elim
  · exact h

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma coefficient_cross_orthogonality (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ]
    (hρ : IsUnitary ρ) (hne : ¬Nonempty (Representation.Equiv ρ σ))
    (u z : W) (v w : V) :
    ∑ g, inner ℂ u (σ g z)*inner ℂ (ρ g w) v=0 := by
  have he := averageMap_zero ρ σ hne (InnerProductSpace.rankOne ℂ z w).toLinearMap
  have hv := congrArg (fun T : Representation.IntertwiningMap ρ σ => inner ℂ u (T v)) he
  change inner ℂ u ((∑ g, (σ g).comp ((InnerProductSpace.rankOne ℂ z w).toLinearMap.comp (ρ g⁻¹))) v)=_ at hv
  simpa only [LinearMap.sum_apply,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply,map_smul,unitary_inner_inv ρ hρ,inner_sum,
    inner_smul_right,Representation.IntertwiningMap.coe_zero,Pi.zero_apply,inner_zero_right,mul_comm] using hv

end Thorp.UnitaryFinite
namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G : Type*} [Group G] [Fintype G]

def regularAction : G →* Equiv.Perm G where
  toFun := Equiv.mulLeft
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

omit [Fintype G] in
lemma regular_transitive (x : G) : ∃ g,regularAction g (1:G)=x := ⟨x,mul_one x⟩

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma regular_fixed (ρ : Representation ℂ G V) (w : V) : IsFixed regularAction (1:G) ρ w := by
  intro g hg
  have he : g=1 := by simpa only [regularAction,MonoidHom.coe_mk,OneHom.coe_mk,Equiv.coe_mulLeft,mul_one] using hg
  subst g
  simp

noncomputable def regularCoefficient (ρ : Representation ℂ G V) (w v : V) : EuclideanSpace ℂ G :=
  normalizedCoefficient regularAction 1 regular_transitive ρ w v

omit [FiniteDimensional ℂ V] in
lemma regularCoefficient_apply (ρ : Representation ℂ G V) (w v : V) (g : G) :
    regularCoefficient ρ w v g = (Real.sqrt ((Module.finrank ℂ V:ℝ)/(Fintype.card G:ℝ)):ℂ)*inner ℂ (ρ g w) v := by
  unfold regularCoefficient normalizedCoefficient
  simp only [PiLp.smul_apply,smul_eq_mul]
  congr 1
  have he := coefficient_at regularAction 1 regular_transitive ρ w (regular_fixed ρ w) v g
  simpa only [regularAction,MonoidHom.coe_mk,OneHom.coe_mk,Equiv.coe_mulLeft,mul_one] using he

lemma regularCoefficient_inner (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (w z v t : V) :
    inner ℂ (regularCoefficient ρ w v) (regularCoefficient ρ z t)=inner ℂ z w*inner ℂ v t :=
  normalizedCoefficient_inner regularAction 1 regular_transitive ρ hρ w z
    (regular_fixed ρ w) (regular_fixed ρ z) v t

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma regularCoefficient_cross (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ]
    (hσ : IsUnitary σ) (hne : ¬Nonempty (Representation.Equiv σ ρ))
    (w v : V) (z t : W) : inner ℂ (regularCoefficient ρ w v) (regularCoefficient σ z t)=0 := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply,regularCoefficient_apply,map_mul,Complex.conj_ofReal,
    inner_conj_symm]
  have he := coefficient_cross_orthogonality σ ρ hσ hne v w t z
  calc
    _ = ((Real.sqrt ((Module.finrank ℂ V:ℝ)/(Fintype.card G:ℝ)):ℂ)*
        (Real.sqrt ((Module.finrank ℂ W:ℝ)/(Fintype.card G:ℝ)):ℂ)) *
        ∑ g,inner ℂ v (ρ g w)*inner ℂ (σ g z) t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = 0 := by rw [he,mul_zero]

end Thorp.UnitaryFinite

namespace Thorp.FiniteFourier
open scoped BigOperators ComplexConjugate Classical
open UnitaryFinite
variable {G ι : Type*} [Group G] [Fintype G] [Fintype ι]
variable (V : ι → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
variable (ρ : ∀ i, Representation ℂ G (V i)) [∀ i, Representation.IsIrreducible (ρ i)]
variable (hρ : ∀ i, IsUnitary (ρ i))
variable (hneq : ∀ i j, i≠j → ¬Nonempty (Representation.Equiv (ρ i) (ρ j)))
  (hcard : Nat.card (ConjClasses G)≤Fintype.card ι)


abbrev CoefficientIndex := Σ i,Fin (Module.finrank ℂ (V i)) × Fin (Module.finrank ℂ (V i))

noncomputable def coefficientFamily (a : CoefficientIndex V) : EuclideanSpace ℂ G :=
  regularCoefficient (ρ a.1) (stdOrthonormalBasis ℂ (V a.1) a.2.1) (stdOrthonormalBasis ℂ (V a.1) a.2.2)

omit [Fintype ι] in
include hρ hneq in
lemma coefficientFamily_orthonormal : Orthonormal ℂ (coefficientFamily V ρ) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i,a,b⟩ ⟨j,c,d⟩
  dsimp only [coefficientFamily]
  by_cases hij : i=j
  · subst j
    rw [regularCoefficient_inner _ (hρ i)]
    simp only [(stdOrthonormalBasis ℂ (V i)).inner_eq_ite]
    by_cases hac : a=c <;> by_cases hbd : b=d <;> simp [hac,hbd,eq_comm]
  · rw [regularCoefficient_cross _ _ (hρ j) (hneq j i (Ne.symm hij))]
    rw [ite_eq_right (by intro h; exact hij (congrArg Sigma.fst h))]

include ρ hneq hcard in
lemma coefficientIndex_card : Fintype.card (CoefficientIndex V)=Fintype.card G := by
  simp only [CoefficientIndex,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,←pow_two]
  exact FiniteCharacters.sum_dimension_sq V ρ hneq hcard

noncomputable def coefficientBasis : OrthonormalBasis (CoefficientIndex V) ℂ (EuclideanSpace ℂ G) :=
  OrthonormalBasis.mk (coefficientFamily_orthonormal V ρ hρ hneq)
    (by rw [(coefficientFamily_orthonormal V ρ hρ hneq).linearIndependent.span_eq_top_of_card_eq_finrank'
          (by rw [coefficientIndex_card V ρ hneq hcard,finrank_euclideanSpace])])


noncomputable def realVector (p : G → ℝ) : EuclideanSpace ℂ G := WithLp.toLp 2 (fun g => (p g:ℂ))

end Thorp.FiniteFourier

namespace Thorp.ParallelBlocks
open scoped BigOperators Classical
variable {B X : Type*}

def lift : (B → Equiv.Perm X) →* Equiv.Perm (B × X) where
  toFun p :=
    { toFun := fun x => (x.1,p x.1 x.2)
      invFun := fun x => (x.1,(p x.1).symm x.2)
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma lift_apply (p : B → Equiv.Perm X) (x : B × X) : lift p x=(x.1,p x.1 x.2) := rfl

noncomputable def injection (b : B) : Equiv.Perm X →* Equiv.Perm (B × X) :=
  lift.comp
    { toFun := fun p c => if c=b then p else 1
      map_one' := by funext c; simp
      map_mul' := by intro p q; funext c; by_cases h : c=b <;> simp [h] }

@[simp] lemma injection_apply (b : B) (p : Equiv.Perm X) (x : B × X) :
    injection b p x=(x.1,if x.1=b then p x.2 else x.2) := by
  simp only [injection,MonoidHom.comp_apply,lift_apply]
  by_cases h : x.1=b <;> simp [h]

lemma injection_commute {b c : B} (h : b≠c) (p q : Equiv.Perm X) :
    Commute (injection b p) (injection c q) := by
  apply Equiv.ext
  intro x
  simp only [Equiv.Perm.mul_apply,injection_apply]
  by_cases hb : x.1=b <;> by_cases hc : x.1=c <;> simp_all

end Thorp.ParallelBlocks
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {G H : Type*} [Group G] [Group H]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma sampleOperator_comp (ρ : Representation ℂ G V) (φ : H →* G) (P : Ω → H) :
    sampleOperator (ρ.comp φ) P=sampleOperator ρ (φ ∘ P) := rfl

lemma sampleOperator_commute (ρ : Representation ℂ G V) (P : Ω → G) (Q : Ξ → G)
    (h : ∀ ω ξ, Commute (P ω) (Q ξ)) :
    Commute (sampleOperator ρ P) (sampleOperator ρ Q) := by
  unfold sampleOperator
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.sum_left
  intro ω _
  apply Commute.sum_right
  intro ξ _
  exact (h ω ξ).map (continuousRepresentation ρ)

end Thorp.UnitaryFinite
namespace Thorp.ParallelBlocks
open scoped BigOperators Classical
open UnitaryFinite
variable {B X Ω : Type*} [Fintype B] [DecidableEq B] [Fintype Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype B] [DecidableEq B] in
lemma local_average_commute (ρ : Representation ℂ (Equiv.Perm (B × X)) V)
    (P : B → Ω → Equiv.Perm X) (b c : B) :
    Commute (sampleOperator (ρ.comp (injection b)) (P b))
      (sampleOperator (ρ.comp (injection c)) (P c)) := by
  by_cases h : b=c
  · subst c; exact Commute.refl _
  · rw [sampleOperator_comp,sampleOperator_comp]
    exact sampleOperator_commute ρ _ _ (fun _ _ => injection_commute h _ _)

end Thorp.ParallelBlocks
namespace Thorp
open scoped BigOperators Classical

noncomputable def splitPerm (r L : ℕ) : Equiv.Perm (Card (L+r)) ≃* Equiv.Perm (Card r × Card L) :=
  (cardSplit r L).permCongrHom

noncomputable def outerPerm (r L : ℕ) (hi : Card L × SwitchIndex r → Bool) :
    Equiv.Perm (Card r × Card L) :=
  (Equiv.prodComm (Card L) (Card r)).permCongrHom
    (ParallelBlocks.lift (fun x => butterflyPerm r (decodeButterfly r (fun i => hi (x,i)))))


abbrev OuterCoins (r L : ℕ) := Card L × SwitchIndex r → Bool
abbrev LocalCoins (L : ℕ) := SwitchIndex L → Bool

def parallelSplitCoinEquiv (r L : ℕ) :
    ((Card r → LocalCoins L) × OuterCoins r L) ≃ LocalCoins (L+r) :=
  (Equiv.prodCongr (Equiv.curry (Card r) (SwitchIndex L) Bool).symm (Equiv.refl _)).trans
    (splitCoinEquiv r L)

end Thorp

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_PairAssembleEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp
open scoped BigOperators Classical

def pairAssembleEquiv (B C H : Type*) :
    ((H × (B → C × C)) × H) ≃ (((B → C) × H) × ((B → C) × H)) where
  toFun w := (((fun b => (w.1.2 b).1),w.1.1),((fun b => (w.1.2 b).2),w.2))
  invFun w := ((w.1.2,fun b => (w.1.1 b,w.2.1 b)),w.2.2)
  left_inv _w := rfl
  right_inv _w := rfl

def palindromeStageEquiv (r L : ℕ) :
    ((OuterCoins r L × (Card r → BenesCoins L)) × OuterCoins r L) ≃ BenesCoins (L+r) :=
  (pairAssembleEquiv _ _ _).trans
    (Equiv.prodCongr (parallelSplitCoinEquiv r L) (parallelSplitCoinEquiv r L))

def modifiedAssembleEquiv (B C H U : Type*) :
    ((H × (B → U × (C × C))) × H) ≃ (B → U) × (((B → C) × H) × ((B → C) × H)) where
  toFun w := ((fun b => (w.1.2 b).1),
    (((fun b => (w.1.2 b).2.1),w.1.1),((fun b => (w.1.2 b).2.2),w.2)))
  invFun w := ((w.2.1.2,fun b => (w.1 b,(w.2.1.1 b,w.2.2.1 b))),w.2.2.2)
  left_inv _w := rfl
  right_inv _w := rfl

def modifiedStageEquiv (r L : ℕ) :
    ((OuterCoins r L × (Card r → Equiv.Perm (Card L) × BenesCoins L)) × OuterCoins r L) ≃
      ModifiedCoins L r :=
  (modifiedAssembleEquiv _ _ _ _).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (parallelSplitCoinEquiv r L) (parallelSplitCoinEquiv r L)))

noncomputable def localModifiedPerm (L : ℕ) (e : Bool)
    (w : Equiv.Perm (Card L) × BenesCoins L) : Equiv.Perm (Card L) :=
  if e then 1 else butterflyPerm L (decodeButterfly L w.2.1)*w.1⁻¹

end Thorp
namespace Thorp.CommutingBlocks
open scoped BigOperators Classical
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def retain (P : ι → V →L[ℂ] V) (E : Finset ι) (i : ι) : V →L[ℂ] V :=
  if i∈E then 1 else P i

omit [CompleteSpace V] [Fintype ι] in
lemma retain_commute (P : ι → V →L[ℂ] V) (hP : ∀ i j, Commute (P i) (P j))
    (E : Finset ι) (i j : ι) : Commute (retain P E i) (retain P E j) := by
  unfold retain
  split_ifs <;> first | exact Commute.one_left _ | exact Commute.one_right _ | exact hP _ _

end Thorp.CommutingBlocks

namespace Thorp.ParallelBlocks
open scoped BigOperators Classical
open UnitaryFinite
variable {B X : Type*} [Fintype B] [Fintype X] [DecidableEq X]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def centralProjection (ρ : Representation ℂ (Equiv.Perm (B × X)) V) (b : B) : V →L[ℂ] V :=
  uniformOperator (ρ.comp (injection b))

omit [Fintype B] in
lemma centralProjection_commute (ρ : Representation ℂ (Equiv.Perm (B × X)) V) (b c : B) :
    Commute (centralProjection ρ b) (centralProjection ρ c) := by
  simpa only [centralProjection,sampleOperator_uniform] using
    local_average_commute ρ (fun _ => id : B → Equiv.Perm X → Equiv.Perm X) b c

end Thorp.ParallelBlocks

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G X Ω : Type*} [Group G] [Fintype G] [Fintype X] [Fintype Ω]

noncomputable def actionKernel (a : G →* Equiv.Perm X) (P : Ω → G) (x y : X) : ℝ :=
  finiteMean (fun ω => if a (P ω) x=y then 1 else 0)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def randomOperator (ρ : Representation ℂ G V) (P : Ω → G) : Module.End ℂ V :=
  (Fintype.card Ω:ℂ)⁻¹ • ∑ ω, ρ (P ω)⁻¹

noncomputable def fixedSpace (a : G →* Equiv.Perm X) (x₀ : X) (ρ : Representation ℂ G V) :
    Submodule ℂ V where
  carrier := {w | IsFixed a x₀ ρ w}
  zero_mem' := fun g hg => map_zero _
  add_mem' := fun hw hz g hg => by rw [map_add,hw g hg,hz g hg]
  smul_mem' := fun c w hw g hg => by rw [map_smul,hw g hg]

end Thorp.UnitaryFinite
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {α ι : Type*} [Fintype α] [Fintype ι]

def tupleAction : Equiv.Perm α →* Equiv.Perm (ι ↪ α) where
  toFun p :=
    { toFun := fun e => e.trans p.toEmbedding
      invFun := fun e => e.trans p.symm.toEmbedding
      left_inv := fun e => by ext i; exact p.symm_apply_apply (e i)
      right_inv := fun e => by ext i; exact p.apply_symm_apply (e i) }
  map_one' := by ext e i; rfl
  map_mul' p q := by ext e i; rfl

omit [Fintype α] [Fintype ι] in
@[simp] lemma tupleAction_apply (p : Equiv.Perm α) (e : ι ↪ α) (i : ι) :
    tupleAction p e i=p (e i) := rfl

omit [Fintype α] in
lemma tupleAction_fixed_iff [DecidableEq α] (e : ι ↪ α) (p : Equiv.Perm α) :
    tupleAction p e=e ↔ ∀ x ∈ Finset.univ.image e, p x=x := by
  constructor
  · intro h x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact congrArg (fun f : ι ↪ α => f i) h
  · intro h
    ext i
    exact h (e i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

end Thorp.UnitaryFinite

namespace Thorp.Specht
open scoped BigOperators Classical

lemma unitaryRepresentation_coe (μ : YoungDiagram) (p : Equiv.Perm (Cell μ))
    (v : hilbertSpace μ) :
    (unitaryRepresentation μ p v : PermutationHilbert.H (Tabloid μ)) =
      PermutationHilbert.act (tabloidAct p) v := by
  obtain ⟨w,rfl⟩ := (spaceHilbertEquiv μ).surjective v
  change hilbertEquiv μ (tabloidRep μ p w) = _
  exact hilbert_action μ p w

noncomputable def unitaryEquiv (μ : YoungDiagram) :
    Representation.Equiv (representation μ) (unitaryRepresentation μ) :=
  Representation.Equiv.mk (spaceHilbertEquiv μ) (by
    intro p
    apply LinearMap.ext
    intro v
    change spaceHilbertEquiv μ (representation μ p v) =
      spaceHilbertEquiv μ (representation μ p ((spaceHilbertEquiv μ).symm (spaceHilbertEquiv μ v)))
    rw [LinearEquiv.symm_apply_apply])


noncomputable def tupleFixedEquiv (μ : YoungDiagram) {ι : Type*} [Fintype ι]
    (e : ι ↪ Cell μ) :
    UnitaryFinite.fixedSpace (V := hilbertSpace μ) UnitaryFinite.tupleAction e (unitaryRepresentation μ) ≃ₗ[ℂ]
      fixedHilbert μ (Finset.univ.image e) where
  toFun v := ⟨v.1.1,v.1.2,by
    intro p hp
    have h := v.2 p ((UnitaryFinite.tupleAction_fixed_iff e p).mpr hp)
    exact (unitaryRepresentation_coe μ p v.1).symm.trans (congrArg Subtype.val h)⟩
  invFun v := ⟨⟨v.1,v.2.1⟩,by
    intro p hp
    apply Subtype.ext
    exact (unitaryRepresentation_coe μ p _).trans
      (v.2.2 p ((UnitaryFinite.tupleAction_fixed_iff e p).mp hp))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Thorp.Specht
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {G H X Ω : Type*} [Group G] [Group H] [Fintype G] [Fintype X] [Fintype Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] [Fintype X] [Fintype Ω] [FiniteDimensional ℂ V] in
noncomputable def subrepresentationEquiv (ρ : Representation ℂ G V) (e : H ≃* G) :
    Subrepresentation (ρ.comp e.toMonoidHom) ≃o Subrepresentation ρ where
  toFun U :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := fun g v hv => by
        have h := U.apply_mem_toSubmodule (e.symm g) hv
        change ρ (e (e.symm g)) v∈U.toSubmodule at h
        simpa only [e.apply_symm_apply] using h }
  invFun U :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := fun h _ hv => U.apply_mem_toSubmodule (e h) hv }
  left_inv U := by apply Subrepresentation.toSubmodule_injective; rfl
  right_inv U := by apply Subrepresentation.toSubmodule_injective; rfl
  map_rel_iff' := Iff.rfl

end Thorp.UnitaryFinite

namespace Thorp.Specht
open scoped BigOperators Classical

variable {α ι : Type*} [Fintype α] [Fintype ι]

noncomputable def relabelledTupleFixed (μ : YoungDiagram) (e : α ≃ Cell μ) (f : ι ↪ α) :
    UnitaryFinite.fixedSpace (V := hilbertSpace μ) UnitaryFinite.tupleAction f (relabelledUnitary μ e) ≃ₗ[ℂ]
    UnitaryFinite.fixedSpace (V := hilbertSpace μ) UnitaryFinite.tupleAction (f.trans e.toEmbedding) (unitaryRepresentation μ) where
  toFun v := ⟨v.1,by
    intro g hg
    have hp : UnitaryFinite.tupleAction (e.symm.permCongr g) f=f := by
      apply Function.Embedding.ext
      intro i
      have hh := congrArg (fun f : ι ↪ Cell μ => f i) hg
      change g (e (f i))=e (f i) at hh
      simp only [UnitaryFinite.tupleAction_apply,Equiv.permCongr_apply,Equiv.symm_symm,e.symm_apply_apply,hh]
    have hh := v.2 (e.symm.permCongr g) hp
    change unitaryRepresentation μ (e.permCongr (e.symm.permCongr g)) v=v at hh
    have he : e.permCongr (e.symm.permCongr g)=g := by
      apply Equiv.ext
      intro x
      simp only [Equiv.permCongr_apply,Equiv.symm_symm,e.apply_symm_apply]
    simpa only [he] using hh⟩
  invFun v := ⟨v.1,by
    intro g hg
    have hp : UnitaryFinite.tupleAction (e.permCongr g) (f.trans e.toEmbedding)=f.trans e.toEmbedding := by
      apply Function.Embedding.ext
      intro i
      have hh := congrArg (fun f : ι ↪ α => f i) hg
      change g (f i)=f i at hh
      simp only [UnitaryFinite.tupleAction_apply,Function.Embedding.trans_apply,
        Equiv.toEmbedding_apply,Equiv.permCongr_apply,e.symm_apply_apply,hh]
    exact v.2 (e.permCongr g) hp⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Thorp.Specht

namespace Thorp.SparseContact
open scoped BigOperators Classical

noncomputable def pointStabilizer {α : Type*} (A : Finset α) : Subgroup (Equiv.Perm α) where
  carrier := {p | ∀ x ∈ A, p x = x}
  one_mem' := by intro x _; rfl
  mul_mem' := by intro p q hp hq x hx; change p (q x) = x; rw [hq x hx, hp x hx]
  inv_mem' := by intro p hp x hx; exact (Equiv.Perm.inv_eq_iff_eq).mpr (hp x hx).symm

end Thorp.SparseContact

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_ZeroExtend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.DimensionEstimates
open scoped BigOperators

variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
open scoped Classical

noncomputable def fiberWeight (f : X → I) (i : I) : ℝ := Fintype.card {x // f x=i}

end Thorp.DimensionEstimates

namespace Thorp.DimensionEstimates
open scoped BigOperators Classical

noncomputable def entropyGap : ℝ := Real.log (32/27:ℝ)/3

open Filter

noncomputable def nearPower : ℝ := 1/2048
noncomputable def nearFraction : ℝ := 1/4096
noncomputable def tailPower : ℝ := 1535/1048576

noncomputable def chosenTuple (N j : ℕ) : ℕ :=
  ⌈(j:ℝ)*((N:ℝ)/j)^nearPower⌉₊

end Thorp.DimensionEstimates

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_InsertionPerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp
open scoped BigOperators Classical

def insertionPerm (d : ℕ) (i : Fin (d+1)) : Equiv.Perm (Card (d+1)) :=
  (Fin.consEquiv (fun _ : Fin (d+1) => Bool)).symm.trans
    (Fin.insertNthEquiv (fun _ : Fin (d+1) => Bool) i)

end Thorp

namespace Thorp
open scoped BigOperators Classical
open UnitaryFinite

def carryCoins (d : ℕ) (i : Fin (d+1)) : (Bool → Coins (d+1)) ≃ Coins (d+2) where
  toFun ξ y := ξ (y i) (Fin.removeNth i y)
  invFun ξ b y := ξ (Fin.insertNth i b y)
  left_inv ξ := by funext b y; simp
  right_inv ξ := by funext y; simp

end Thorp


end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_TailShapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.Specht
open scoped BigOperators Classical

lemma rowLens_headD (μ : YoungDiagram) : μ.rowLens.headD 0=μ.rowLen 0 := by
  cases he : μ.rowLens with
  | nil =>
    have hc := sum_rowLens μ
    rw [he,List.sum_nil] at hc
    have hr := rowLen_zero_le_card μ
    simp only [List.headD_nil]
    omega
  | cons a l =>
    have hh := YoungDiagram.get_rowLens (μ := μ) (i := 0) (h := by simp [he])
    simpa only [he,List.getElem_cons_zero,List.headD_cons] using hh

lemma rowLens_tail_sum (μ : YoungDiagram) : μ.rowLens.tail.sum=μ.card-μ.rowLen 0 := by
  have hh := rowLens_headD μ
  have hc := sum_rowLens μ
  cases he : μ.rowLens with
  | nil => simp only [he,List.headD_nil] at hh; simp only [he,List.sum_nil] at hc; simp [←hc]
  | cons a l =>
    simp only [he,List.headD_cons] at hh
    simp only [he,List.sum_cons] at hc
    simp only [List.tail_cons]
    omega

abbrev TailShapes (N j : ℕ) := {μ : Shapes N // μ.1.card-μ.1.rowLen 0=j}

noncomputable def tailShapePartition (N j : ℕ) (μ : TailShapes N j) : Nat.Partition j where
  parts := μ.1.1.rowLens.tail
  parts_pos := fun {x} hx => μ.1.1.pos_of_mem_rowLens x (List.mem_of_mem_tail (by simpa using hx))
  parts_sum := by simpa using (rowLens_tail_sum μ.1.1).trans μ.2

end Thorp.Specht

namespace Thorp
open scoped BigOperators Classical

lemma tail_preserving_pairSwitch (d : ℕ) (p : Equiv.Perm (Card (d+1)))
    (hp : ∀ x, Fin.tail (p x)=Fin.tail x) :
    pairSwitch (fun u => p (Fin.cons false u) 0)=p := by
  apply Equiv.ext
  intro x
  rw [←Fin.cons_self_tail x]
  generalize x 0=b
  generalize Fin.tail x=u
  apply funext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Bool.xor b (p (Fin.cons false u) 0)=p (Fin.cons b u) 0
    cases b with
    | false => simp
    | true =>
      have hn : p (Fin.cons false u) 0 ≠ p (Fin.cons true u) 0 := by
        intro he
        have hh : p (Fin.cons false u)=p (Fin.cons true u) := by
          rw [←Fin.cons_self_tail (p (Fin.cons false u)),←Fin.cons_self_tail (p (Fin.cons true u)),
            hp,hp,Fin.tail_cons,Fin.tail_cons,he]
        have hh := congrFun (p.injective hh) 0
        simp only [Fin.cons_zero] at hh
        contradiction
      cases h0 : p (Fin.cons false u) 0 <;> cases h1 : p (Fin.cons true u) 0 <;> simp_all
  · change u j=p (Fin.cons b u) j.succ
    have h := congrFun (hp (Fin.cons b u)) j
    simpa only [Fin.tail_cons,Fin.tail,Fin.cons_succ] using h.symm

lemma pairSwitch_injective (d : ℕ) : Function.Injective (pairSwitch (d := d)) := by
  intro ξ η h
  funext u
  have hh := congrArg (fun p : Equiv.Perm (Card (d+1)) => p (Fin.cons false u) 0) h
  change Bool.xor false (ξ u)=Bool.xor false (η u) at hh
  simpa only [Bool.false_xor] using hh

end Thorp
namespace Thorp.Specht
open scoped BigOperators Classical

noncomputable def pairFiberEquiv (d : ℕ) (μ : YoungDiagram) (e : Card (d+1) ≃ Cell μ) :
    (Card d → Bool) ≃ fiberGroup (fun x => Fin.tail (e.symm x)) :=
  Equiv.ofBijective (fun ξ => ⟨e.permCongr (pairSwitch ξ),by
    intro x
    simp only [Equiv.permCongr_apply,e.symm_apply_apply]
    exact Fin.tail_cons _ _⟩)
    ⟨fun ξ η h => pairSwitch_injective d (e.permCongr.injective (congrArg Subtype.val h)),by
      intro p
      let q := e.symm.permCongr p.1
      have hq : ∀ x, Fin.tail (q x)=Fin.tail x := by
        intro x
        have h := p.2 (e x)
        simpa only [q,Equiv.permCongr_apply,Equiv.symm_symm,e.symm_apply_apply] using h
      refine ⟨fun u => q (Fin.cons false u) 0,?_⟩
      apply Subtype.ext
      change e.permCongr (pairSwitch (fun u => q (Fin.cons false u) 0))=p.1
      rw [tail_preserving_pairSwitch d q hq]
      apply Equiv.ext
      intro x
      simp only [q,Equiv.permCongr_apply,Equiv.symm_symm,e.apply_symm_apply]⟩

open UnitaryFinite

end Thorp.Specht

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_Harmonic_Site
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.Casimir
open scoped BigOperators Classical

section
open Filter

noncomputable def fromDistance (d t : ℕ) (σ : Equiv.Perm (Card d)) : ℝ :=
  (1/2:ℝ) * ∑ g : Equiv.Perm (Card d),
    |law d t (g*σ⁻¹) - 1/(Nat.factorial (2^d):ℝ)|

end

end Thorp.Casimir

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_TraceModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.LowPlanes
open scoped BigOperators Classical
open Casimir Specht UnitaryFinite

def MainStatement : Prop :=
  ∃ P : ℝ, 2 ≤ P ∧ ∀ d : ℕ, 1 ≤ d →
    regularTrace d P ≤ 1 + ((2 : ℝ)^d) ^ (-10 : ℤ) ∧
    ∀ v : ℤ, P ≤ 2 * (v : ℝ) → ∀ σ : Equiv.Perm (Card d),
      sweepDistance d v.toNat σ ≤ (1/2 : ℝ) * ((2 : ℝ)^d) ^ (-5 : ℤ)

end Thorp.LowPlanes

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpRouting_TraceDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.LowPlanes
open scoped BigOperators Classical
open Casimir Specht UnitaryFinite

attribute [local instance] hsNorm hsInner hsFinite

noncomputable def tailBound (d v : ℕ) : ℝ :=
  ∑ μ : Shapes (2^d), if μ.1.card - μ.1.rowLen 0 = 0 then 0 else
    (Module.finrank ℂ (hilbertSpace μ.1) : ℝ)^2 * ‖K d μ.1 (cardLabels d μ)‖^v

end Thorp.LowPlanes

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

noncomputable section
open scoped BigOperators
open Filter

namespace Thorp

def supportThreshold (d : ℕ) : ℤ :=
  ⌈(2 / (2 ^ d : ℝ)) * Real.logb 2 (3 * ((2 ^ d).factorial : ℝ) / 4)⌉

def orderFunction (d : ℕ) : ℝ := d

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_PairAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uΩ uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def mean {Ω : Type uΩ} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

def sign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> norm_num [sign]

@[simp] theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> norm_num [sign]

@[simp] theorem sign_mul_self (b : Bool) : sign b * sign b = 1 := by
  simpa only [pow_two] using sign_sq b

def toggleCoin {α : Type uα} [DecidableEq α] (i : α) : Equiv.Perm (α → Bool) :=
  Function.Involutive.toPerm (fun c => Function.update c i (!(c i))) (by
    intro c
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h])

@[simp] theorem toggleCoin_apply {α : Type uα} [DecidableEq α]
    (i : α) (c : α → Bool) (j : α) :
    toggleCoin i c j = Function.update c i (!(c i)) j := rfl

def pairUpdate (free₀ free₁ : Bool) (a b : ℝ) (coin : Bool) : ℝ × ℝ :=
  if free₀ && free₁ then ((a + b) / 2, (a + b) / 2)
  else if coin then (b, a) else (a, b)

@[simp] theorem pairUpdate_sum (free₀ free₁ : Bool) (a b : ℝ) (coin : Bool) :
    (pairUpdate free₀ free₁ a b coin).1 + (pairUpdate free₀ free₁ a b coin).2 = a + b := by
  cases free₀ <;> cases free₁ <;> cases coin <;> simp [pairUpdate] <;> ring

def flow {α : Type uα} (B : Bool × α → Bool) (w : Bool × α → ℝ)
    (c : α → Bool) (x : Bool × α) : ℝ :=
  let p := pairUpdate (B (false, x.2)) (B (true, x.2))
    (w (false, x.2)) (w (true, x.2)) (c x.2)
  if x.1 then p.2 else p.1

def oddCoefficient {α : Type uα} [Fintype α] (ε : α → ℝ) (w : Bool × α → ℝ) : ℝ :=
  ∑ i, ε i * (w (false, i) - w (true, i))

end Conditional

namespace Conditional

def pairMap {α : Type uα} (c : α → Bool) (x : Bool × α) : Bool × α :=
  (x.1 ^^ c x.2, x.2)

theorem flow_support {α : Type uα} (B : Bool × α → Bool) (w : Bool × α → ℝ)
    (hw : ∀ x, B x = false → w x = 0) (c : α → Bool) (x : Bool × α)
    (hx : B (pairMap c x) = false) : flow B w c x = 0 := by
  rcases x with ⟨b, i⟩
  have h₀ := hw (false, i)
  have h₁ := hw (true, i)
  cases b <;> cases hb₀ : B (false, i) <;> cases hb₁ : B (true, i) <;>
    cases hc : c i <;> simp_all [flow, pairUpdate, pairMap]

theorem flow_sum {α : Type uα} [Fintype α] (B : Bool × α → Bool)
    (w : Bool × α → ℝ) (c : α → Bool) :
    (∑ x, flow B w c x) = ∑ x, w x := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [flow, Bool.false_eq_true, ↓reduceIte, add_comm] using
    (pairUpdate_sum (B (false, i)) (B (true, i)) (w (false, i)) (w (true, i)) (c i))

theorem pairUpdate_energy_le (free₀ free₁ : Bool) (a b : ℝ) (coin : Bool) :
    (pairUpdate free₀ free₁ a b coin).1 ^ 2 +
        (pairUpdate free₀ free₁ a b coin).2 ^ 2 ≤ a ^ 2 + b ^ 2 := by
  have h := sq_nonneg (a - b)
  cases free₀ <;> cases free₁ <;> cases coin <;> simp [pairUpdate] <;> nlinarith

theorem flow_energy_le {α : Type uα} [Fintype α] (B : Bool × α → Bool)
    (w : Bool × α → ℝ) (c : α → Bool) :
    (∑ x, flow B w c x ^ 2) ≤ ∑ x, w x ^ 2 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [flow, Bool.false_eq_true, ↓reduceIte, add_comm] using
    pairUpdate_energy_le (B (false, i)) (B (true, i)) (w (false, i)) (w (true, i)) (c i)

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Walsh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uκ

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def character {ι : Type uι} [Fintype ι] (a x : ι → Bool) : ℝ :=
  ∏ i, if a i then sign (x i) else 1

@[simp] theorem character_false {ι : Type uι} [Fintype ι] (x : ι → Bool) :
    character (fun _ => false) x = 1 := by
  simp [character]

@[simp] theorem character_sq {ι : Type uι} [Fintype ι] (a x : ι → Bool) :
    character a x ^ 2 = 1 := by
  unfold character
  rw [← Finset.prod_pow]
  have h (i : ι) : (if a i then sign (x i) else (1 : ℝ)) ^ 2 = 1 := by
    cases a i <;> simp
  simp only [h, Finset.prod_const_one]

def coefficient {ι : Type uι} [Fintype ι] [DecidableEq ι] (w : (ι → Bool) → ℝ) (a : ι → Bool) : ℝ :=
  ∑ x, w x * character a x

@[simp] theorem coefficient_false {ι : Type uι} [Fintype ι] [DecidableEq ι] (w : (ι → Bool) → ℝ) :
    coefficient w (fun _ => false) = ∑ x, w x := by
  simp [coefficient]

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uΩ uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

@[simp] theorem card_position (d : ℕ) : Fintype.card (Position d) = 2 ^ d := by
  simp [Position]

@[simp] theorem card_state (d : ℕ) : Fintype.card (State d) = (2 ^ d).factorial := by
  classical
  rw [Fintype.card_perm, card_position]

@[simp] theorem card_coins_succ (d : ℕ) : Fintype.card (Coins (d + 1)) = 2 ^ (2 ^ d) := by
  simp [Coins]

@[simp] theorem card_history_succ (d t : ℕ) :
    Fintype.card (History (d + 1) t) = 2 ^ (2 ^ d * t) := by
  simp [History, ← pow_mul]

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_ConditionalFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def splitPosition (d : ℕ) : Position (d + 1) ≃ Bool × Position d :=
  (Fin.consEquiv (fun _ : Fin (d + 1) => Bool)).symm

def scatterPosition (d : ℕ) : Bool × Position d ≃ Position (d + 1) :=
  (splitPosition d).symm.trans (rotate (d + 1))

def physicalFlow (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Coins (d + 1)) (x : Position (d + 1)) : ℝ :=
  flow (B ∘ (splitPosition d).symm) (w ∘ (splitPosition d).symm) c
    ((scatterPosition d).symm x)

def physicalFree (d : ℕ) (B : Position (d + 1) → Bool)
    (c : Coins (d + 1)) (x : Position (d + 1)) : Bool :=
  B ((step (d + 1) c).symm x)

theorem step_symm_scatter (d : ℕ) (c : Coins (d + 1)) (p : Bool × Position d) :
    (step (d + 1) c).symm (scatterPosition d p) =
      (splitPosition d).symm (pairMap c p) := by
  simp [step, scatterPosition, splitPosition, pairSwitch, pairMap]

@[simp] theorem physicalFlow_scatter (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Coins (d + 1)) (p : Bool × Position d) :
    physicalFlow d B w c (scatterPosition d p) =
      flow (B ∘ (splitPosition d).symm) (w ∘ (splitPosition d).symm) c p := by
  simp [physicalFlow]

@[simp] theorem physicalFree_scatter (d : ℕ) (B : Position (d + 1) → Bool)
    (c : Coins (d + 1)) (p : Bool × Position d) :
    physicalFree d B c (scatterPosition d p) =
      B ((splitPosition d).symm (pairMap c p)) := by
  rw [physicalFree, step_symm_scatter]

theorem physicalFlow_sum (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Coins (d + 1)) :
    (∑ x, physicalFlow d B w c x) = ∑ x, w x := by
  calc
    _ = ∑ p, physicalFlow d B w c (scatterPosition d p) :=
      (Equiv.sum_comp (scatterPosition d) (physicalFlow d B w c)).symm
    _ = ∑ p, w ((splitPosition d).symm p) := by
      simp only [physicalFlow_scatter]
      exact flow_sum (B ∘ (splitPosition d).symm)
        (w ∘ (splitPosition d).symm) c
    _ = _ := Equiv.sum_comp (splitPosition d).symm w

theorem physicalFlow_energy_le (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Coins (d + 1)) :
    (∑ x, physicalFlow d B w c x ^ 2) ≤ ∑ x, w x ^ 2 := by
  calc
    _ = ∑ p, physicalFlow d B w c (scatterPosition d p) ^ 2 :=
      (Equiv.sum_comp (scatterPosition d) (fun x => physicalFlow d B w c x ^ 2)).symm
    _ ≤ ∑ p, w ((splitPosition d).symm p) ^ 2 := by
      simp only [physicalFlow_scatter]
      exact flow_energy_le (B ∘ (splitPosition d).symm)
        (w ∘ (splitPosition d).symm) c
    _ = _ := Equiv.sum_comp (splitPosition d).symm (fun x => w x ^ 2)

theorem physicalFlow_support (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (hw : ∀ x, B x = false → w x = 0)
    (c : Coins (d + 1)) (x : Position (d + 1))
    (hx : physicalFree d B c x = false) : physicalFlow d B w c x = 0 := by
  obtain ⟨p, rfl⟩ := (scatterPosition d).surjective x
  rw [physicalFree_scatter] at hx
  rw [physicalFlow_scatter]
  exact flow_support _ _ (fun p => hw ((splitPosition d).symm p)) c p hx

def freeCount {α : Type uα} [Fintype α] (B : α → Bool) : ℕ :=
  (Finset.univ.filter (fun x => B x = true)).card

def centeredPoint {α : Type uα} [Fintype α] [DecidableEq α]
    (B : α → Bool) (tag : α) (x : α) : ℝ :=
  (if x = tag then 1 else 0) - (1 / (freeCount B : ℝ)) * (if B x then 1 else 0)

theorem freeCount_pos {α : Type uα} [Fintype α] (B : α → Bool) (tag : α)
    (ht : B tag = true) : 0 < freeCount B := by
  apply Finset.card_pos.mpr
  exact ⟨tag, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩

theorem sum_free_indicator {α : Type uα} [Fintype α] (B : α → Bool) :
    (∑ x : α, if B x then (1 : ℝ) else 0) = freeCount B := by
  exact Finset.sum_boole _ _

theorem centeredPoint_sum {α : Type uα} [Fintype α] [DecidableEq α]
    (B : α → Bool) (tag : α) (ht : B tag = true) :
    (∑ x, centeredPoint B tag x) = 0 := by
  have hm : (freeCount B : ℝ) ≠ 0 := by exact_mod_cast (freeCount_pos B tag ht).ne'
  unfold centeredPoint
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_free_indicator]
  simp [hm]

theorem centeredPoint_support {α : Type uα} [Fintype α] [DecidableEq α]
    (B : α → Bool) (tag : α) (ht : B tag = true)
    (x : α) (hx : B x = false) : centeredPoint B tag x = 0 := by
  have hxt : x ≠ tag := by intro h; subst x; simp_all
  simp [centeredPoint, hx, hxt]

theorem centeredPoint_energy {α : Type uα} [Fintype α] [DecidableEq α]
    (B : α → Bool) (tag : α) (ht : B tag = true) :
    (∑ x, centeredPoint B tag x ^ 2) = 1 - 1 / (freeCount B : ℝ) := by
  have hm : (freeCount B : ℝ) ≠ 0 := by exact_mod_cast (freeCount_pos B tag ht).ne'
  have hpoint (x : α) : centeredPoint B tag x ^ 2 =
      (if x = tag then (1 - 2 / (freeCount B : ℝ)) else 0) +
        (1 / (freeCount B : ℝ)) ^ 2 * (if B x then 1 else 0) := by
    by_cases hx : x = tag
    · subst x
      simp [centeredPoint, ht]
      ring
    · cases hB : B x <;> simp [centeredPoint, hx, hB]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_free_indicator]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  field_simp
  ring

structure CenteredState (d : ℕ) where
  free : Position d → Bool
  weight : Position d → ℝ
  mass_zero : ∑ x, weight x = 0
  supported : ∀ x, free x = false → weight x = 0
  energy_le_one : ∑ x, weight x ^ 2 ≤ 1

def initialState (d : ℕ) (B : Position d → Bool) (tag : Position d)
    (ht : B tag = true) : CenteredState d where
  free := B
  weight := centeredPoint B tag
  mass_zero := centeredPoint_sum B tag ht
  supported := centeredPoint_support B tag ht
  energy_le_one := by
    rw [centeredPoint_energy B tag ht]
    exact sub_le_self _ (by positivity)

def nextState (d : ℕ) (v : CenteredState (d + 1)) (c : Coins (d + 1)) :
    CenteredState (d + 1) where
  free := physicalFree d v.free c
  weight := physicalFlow d v.free v.weight c
  mass_zero := by rw [physicalFlow_sum]; exact v.mass_zero
  supported := physicalFlow_support d v.free v.weight v.supported c
  energy_le_one := (physicalFlow_energy_le d v.free v.weight c).trans v.energy_le_one

def iterateState (d : ℕ) (v : CenteredState (d + 1)) :
    (t : ℕ) → History (d + 1) t → CenteredState (d + 1)
  | 0, _ => v
  | t + 1, ω => nextState d (iterateState d v t (fun i => ω i.castSucc)) (ω (Fin.last t))

def expectedEnergy (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ) : ℝ :=
  mean (fun ω : History (d + 1) t => ∑ x, (iterateState d v t ω).weight x ^ 2)

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_FiniteExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uΩ uι uΩ'

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

@[simp] theorem run_zero (d : ℕ) (ω : History d 0) : run d 0 ω = 1 := by
  simp [run]

theorem run_succ (d t : ℕ) (ω : History d (t + 1)) :
    run d (t + 1) ω = step d (ω (Fin.last t)) *
      run d t (fun i => ω i.castSucc) := by
  simp only [run, List.ofFn_succ']
  rw [List.concat_eq_append, List.reverse_concat', List.prod_cons]

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_WalshFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uΩ

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def oneFreeEnergy (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) : ℝ :=
  ∑ x : Position d,
    ((if B (Fin.cons true x) then 0 else w (Fin.cons false x) ^ 2) +
      (if B (Fin.cons false x) then 0 else w (Fin.cons true x) ^ 2))

end Conditional

namespace Conditional

def prefixZero {d : ℕ} (j : ℕ) (a : Position d) : Prop :=
  ∀ i : Fin d, i.val < j → a i = false

instance prefixZeroDecidable {d : ℕ} (j : ℕ) (a : Position d) :
    Decidable (prefixZero j a) := by
  unfold prefixZero
  infer_instance

@[simp] theorem prefixZero_zero {d : ℕ} (a : Position d) : prefixZero 0 a := by
  intro i hi
  omega

def bandEnergy (d : ℕ) (w : Position d → ℝ) (j : ℕ) : ℝ := by
  classical
  exact ∑ a : Position d, if prefixZero j a then coefficient w a ^ 2 else 0

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_FreshCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uΩ uι uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def expectedBand (d : ℕ) (v : CenteredState (d + 1)) (t j : ℕ) : ℝ :=
  mean (fun ω : History (d + 1) t =>
    bandEnergy (d + 1) (iterateState d v t ω).weight j / 2 ^ (d + 1))

def expectedNoise (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ) : ℝ :=
  mean (fun ω : History (d + 1) t =>
    oneFreeEnergy d (iterateState d v t ω).free (iterateState d v t ω).weight)

end Conditional

namespace Conditional

def pairFreeCount {α : Type uα} [Fintype α] (B : Bool × α → Bool) : ℕ :=
  ∑ i, ((B (false, i)).toNat + (B (true, i)).toNat)

def pairHalfCount {α : Type uα} [Fintype α] (B : Bool × α → Bool)
    (c : α → Bool) (h : Bool) : ℕ :=
  ∑ i, (B (h ^^ c i, i)).toNat

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_HalfHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

structure RawState (d : ℕ) where
  free : Position d → Bool
  weight : Position d → ℝ

def rawNext (d : ℕ) (v : RawState (d + 1)) (c : Coins (d + 1)) : RawState (d + 1) where
  free := physicalFree d v.free c
  weight := physicalFlow d v.free v.weight c

def rawIterate (d : ℕ) (v : RawState (d + 1)) :
    (t : ℕ) → History (d + 1) t → RawState (d + 1)
  | 0, _ => v
  | t + 1, ω => rawNext d (rawIterate d v t (fun i => ω i.castSucc)) (ω (Fin.last t))

def CenteredState.raw {d : ℕ} (v : CenteredState d) : RawState d := ⟨v.free, v.weight⟩

end Conditional

namespace Conditional

def firstMean (d : ℕ) (w : Position (d + 1) → ℝ) (x : Position d) : ℝ :=
  mean (fun b : Bool => w (Fin.cons b x))

def meanLayer : (d : ℕ) → (Position d → ℝ) → Position d → ℝ
  | 0, w => w
  | d + 1, w => fun x => firstMean d w (Fin.init x)

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_NoiseEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def insertBit (d : ℕ) (i : Fin (d + 1)) (b : Bool) (x : Position d) : Position (d + 1) :=
  Fin.insertNth i b x

def halfPositionEquiv (d : ℕ) (i : Fin (d + 1)) : Bool × Position d ≃ Position (d + 1) :=
  Fin.insertNthEquiv (fun _ => Bool) i

@[simp] theorem halfPositionEquiv_apply (d : ℕ) (i : Fin (d + 1)) (p : Bool × Position d) :
    halfPositionEquiv d i p = insertBit d i p.1 p.2 := rfl

@[simp] theorem insertBit_zero (d : ℕ) (b : Bool) (x : Position d) :
    insertBit d 0 b x = Fin.cons b x := Fin.insertNth_zero' _ _

@[simp] theorem insertBit_last (d : ℕ) (b : Bool) (x : Position d) :
    insertBit d (Fin.last d) b x = Fin.snoc x b := Fin.insertNth_last' _ _

@[ext] theorem RawState.ext {d : ℕ} {v u : RawState d}
    (hf : v.free = u.free) (hw : v.weight = u.weight) : v = u := by
  cases v; cases u; simp_all

def halfRaw (d : ℕ) (i : Fin (d + 1)) (h : Bool) (v : RawState (d + 1)) : RawState d where
  free x := v.free (insertBit d i h x)
  weight x := v.weight (insertBit d i h x)

end Conditional

namespace Conditional

def halfMarker (d t : ℕ) : Fin (d + 2) := ⟨d + 1 - t, by omega⟩
def coinHalfMarker (d t : ℕ) : Fin (d + 1) := ⟨d - t, by omega⟩

@[simp] theorem halfMarker_zero (d : ℕ) : halfMarker d 0 = Fin.last (d + 1) := rfl
@[simp] theorem halfMarker_end (d : ℕ) : halfMarker d (d + 1) = 0 := by
  apply Fin.ext; simp [halfMarker]

def halfHistory (d t : ℕ) (h : Bool) (ω : History (d + 2) t) : History (d + 1) t :=
  fun i x => ω i (insertBit d (coinHalfMarker d i.val) h x)

@[simp] theorem halfHistory_snoc (d t : ℕ) (h : Bool)
    (ω : History (d + 2) t) (c : Coins (d + 2)) :
    halfHistory d (t + 1) h (Fin.snoc ω c) =
      Fin.snoc (halfHistory d t h ω) (fun x => c (insertBit d (coinHalfMarker d t) h x)) := by
  funext i x
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change (Fin.snoc (α := fun _ => Coins (d + 2)) ω c (Fin.last t)) (insertBit d (coinHalfMarker d t) h x) =
      (Fin.snoc (α := fun _ => Coins (d + 1)) (halfHistory d t h ω)
        (fun z => c (insertBit d (coinHalfMarker d t) h z)) (Fin.last t)) x
    erw [Fin.snoc_last, Fin.snoc_last]
  · change (Fin.snoc (α := fun _ => Coins (d + 2)) ω c j.castSucc) (insertBit d (coinHalfMarker d j.val) h x) =
      (Fin.snoc (α := fun _ => Coins (d + 1)) (halfHistory d t h ω)
        (fun z => c (insertBit d (coinHalfMarker d t) h z)) j.castSucc) x
    erw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    rfl

def splitHalfHistory (d t : ℕ) :
    History (d + 2) t ≃ History (d + 1) t × History (d + 1) t where
  toFun ω := (halfHistory d t false ω, halfHistory d t true ω)
  invFun p := fun i y =>
    if y (coinHalfMarker d i.val) then
      p.2 i (Fin.removeNth (coinHalfMarker d i.val) y)
    else p.1 i (Fin.removeNth (coinHalfMarker d i.val) y)
  left_inv ω := by
    funext i y
    obtain ⟨⟨h, x⟩, rfl⟩ := (halfPositionEquiv d (coinHalfMarker d i.val)).surjective y
    simp only [halfPositionEquiv_apply, insertBit, Fin.insertNth_apply_same,
      halfHistory, Fin.removeNth_insertNth]
    cases h <;> rfl
  right_inv p := by
    apply Prod.ext <;> funext i x <;>
      simp [halfHistory, insertBit, Fin.insertNth_apply_same, Fin.removeNth_insertNth]

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_EnergyDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

 def rawEnergy {d : ℕ} (v : RawState d) : ℝ := ∑ x, v.weight x ^ 2
 def halfEnergy (d : ℕ) (v : RawState (d + 1)) (h : Bool) : ℝ :=
   ∑ x : Position d, v.weight (Fin.cons h x) ^ 2
 def partnerEnergy (d : ℕ) (v : RawState (d + 1)) (h : Bool) : ℝ :=
   ∑ x : Position d, v.weight (Fin.cons h x) ^ 2 *
     (if v.free (Fin.cons (!h) x) then 1 else 0)
 def startHalfDensity (d : ℕ) (v : RawState (d + 1)) (h : Bool) : ℝ :=
   (freeCount (halfRaw d (Fin.last d) h v).free : ℝ) / Fintype.card (Position d)

end Conditional

namespace Conditional

def splitHistory (d s t : ℕ) : History d (s + t) ≃ History d s × History d t where
  toFun ω := (fun i => ω (Fin.castAdd t i), fun i => ω (Fin.natAdd s i))
  invFun p := Fin.append p.1 p.2
  left_inv ω := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Fin.append_left _ _ _
    · exact Fin.append_right _ _ _
  right_inv p := by
    apply Prod.ext <;> funext i
    · exact Fin.append_left _ _ _
    · exact Fin.append_right _ _ _

@[simp] theorem rawIterate_snoc (d t : ℕ) (v : RawState (d + 1))
    (ω : History (d + 1) t) (c : Coins (d + 1)) :
    rawIterate d v (t + 1) (Fin.snoc ω c) = rawNext d (rawIterate d v t ω) c := by
  simp [rawIterate]

@[simp] theorem iterateState_snoc (d t : ℕ) (v : CenteredState (d + 1))
    (ω : History (d + 1) t) (c : Coins (d + 1)) :
    iterateState d v (t + 1) (Fin.snoc ω c) = nextState d (iterateState d v t ω) c := by
  simp [iterateState]

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_MarginalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def singleHistory (d : ℕ) : Coins d ≃ History d 1 where
  toFun c := fun _ => c
  invFun ω := ω 0
  left_inv _ := rfl
  right_inv ω := by
    funext i
    change ω 0 = ω i
    rw [Subsingleton.elim i 0]

@[simp] theorem iterateState_one (d : ℕ) (v : CenteredState (d + 1)) (c : Coins (d + 1)) :
    iterateState d v 1 (fun _ => c) = nextState d v c := rfl

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_MaskedResampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uι

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def maskedCoin {α : Type uα} (mask : α → Bool) (c r : α → Bool) : α → Bool :=
  fun x => if mask x then r x else c x

def maskSwap {α : Type uα} (mask : α → Bool) :
    Equiv.Perm ((α → Bool) × (α → Bool)) :=
  Function.Involutive.toPerm
    (fun p => (maskedCoin mask p.1 p.2, maskedCoin mask p.2 p.1)) (by
      intro p
      apply Prod.ext <;> funext x <;>
        cases hm : mask x <;> simp [maskedCoin, hm])

def freePairMask (d : ℕ) (B : Position (d + 1) → Bool) : Position d → Bool :=
  fun x => B (Fin.cons false x) && B (Fin.cons true x)

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_ConditionalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

@[simp] theorem run_snoc (d t : ℕ) (ω : History d t) (c : Coins d) :
    run d (t + 1) (Fin.snoc ω c) = step d c * run d t ω := by
  rw [run_succ]
  simp

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_TaggedCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def freeOf {α : Type uα} [DecidableEq α] {k : ℕ} (e : Fin k → α) : α → Bool :=
  fun y => decide (∀ i, e i ≠ y)

@[simp] theorem freeOf_exposed {α : Type uα} [DecidableEq α] {k : ℕ}
    (e : Fin k → α) (i : Fin k) : freeOf e (e i) = false := by
  simp [freeOf]

@[simp] theorem freeOf_true {α : Type uα} [DecidableEq α] {k : ℕ}
    (e : Fin k → α) (y : α) : freeOf e y = true ↔ ∀ i, e i ≠ y := by
  simp [freeOf]

def completeTest {α : Type uα} [Fintype α] [DecidableEq α] {k : ℕ}
    (f : (Fin (k + 1) → α) → ℝ) (e : Fin k → α) : ℝ :=
  (1 / (freeCount (freeOf e) : ℝ)) * ∑ y, if freeOf e y then f (Fin.snoc e y) else 0

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_MarginalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uΩ uα uΩ'

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def marginalRate (d : ℕ) : ℝ :=
  Real.sqrt (3136 * ((1 / 32 : ℝ) ^ d + (2 ^ d : ℝ) ^ 3 * (9 / 10 : ℝ) ^ (2 ^ d)))

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Reachability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Reachability
open Conditional

theorem run_append (d s t : ℕ) (a : History d s) (b : History d t) :
    run d (s + t) (Fin.append a b) = run d t b * run d s a := by
  induction t with
  | zero =>
    have hz : Fin.append a b = a := by funext i; exact Fin.append_left a b i
    rw [hz, run_zero, one_mul]
    rfl
  | succ t ih =>
    obtain ⟨⟨c, b⟩, rfl⟩ := (Fin.snocEquiv (fun _ : Fin (t + 1) => Coins d)).surjective b
    erw [Fin.append_snoc, run_snoc, run_snoc, ih, mul_assoc]

def zeroCoins (d : ℕ) : Coins (d + 1) := fun _ => false

def returnMonoid (d : ℕ) : Submonoid (State (d + 1)) where
  carrier := {g | ∃ t, orderOf (rotate (d + 1)) ∣ t ∧ ∃ ω : History (d + 1) t, run (d + 1) t ω = g}
  one_mem' := ⟨0, dvd_zero _, fun i => i.elim0, run_zero _ _⟩
  mul_mem' := by
    rintro g h ⟨s, hs, a, rfl⟩ ⟨t, ht, b, rfl⟩
    exact ⟨t + s, dvd_add ht hs, Fin.append b a, run_append _ _ _ _ _⟩

def returnGroup (d : ℕ) : Subgroup (State (d + 1)) :=
  Subgroup.closure (returnMonoid d : Set (State (d + 1)))

@[simp] theorem mem_returnGroup (d : ℕ) (g : State (d + 1)) :
    g ∈ returnGroup d ↔ g ∈ returnMonoid d := by
  change g ∈ (Subgroup.closure (returnMonoid d : Set (State (d + 1)))).toSubmonoid ↔ _
  rw [Subgroup.closure_toSubmonoid_of_finite, Submonoid.closure_eq]

end Reachability

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_FiniteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uΩ uΩ' uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace FiniteLaw
open Conditional

variable {G : Type uG} [Fintype G] [Group G]

def conv (μ ν : G → ℝ) (z : G) : ℝ := ∑ g, μ g * ν (g⁻¹ * z)

end FiniteLaw

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Parity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Parity
open Conditional

def sign (d : ℕ) (g : State d) : ℝ := ((Equiv.Perm.sign g : ℤˣ) : ℤ)

end Parity

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Cyclic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uE uX uH

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Specht

variable {G : Type uG} [Group G]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def cyclic (ρ : Representation ℂ G E) (e : E) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (Set.range fun g => ρ g e)
  apply_mem_toSubmodule g := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨h, rfl⟩ := hv
      exact Submodule.subset_span ⟨g * h, by simp⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
      simpa using (Submodule.span ℂ (Set.range fun h => ρ h e)).add_mem ihx ihy
    | smul a x hx ih =>
      simpa using (Submodule.span ℂ (Set.range fun h => ρ h e)).smul_mem a ih

lemma self_mem_cyclic (ρ : Representation ℂ G E) (e : E) : e ∈ cyclic ρ e := by
  exact Submodule.subset_span ⟨1, by simp⟩

theorem submodule_alternative (ρ : Representation ℂ G E) (e : E)
    (hunit : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (K : Module.End ℂ E) (hK : ∀ v, K v = ⟪e, v⟫_ℂ • e)
    (hstable : ∀ U : Subrepresentation ρ, ∀ v ∈ U, K v ∈ U)
    (U : Subrepresentation ρ) :
    cyclic ρ e ≤ U ∨ ∀ u ∈ U, ∀ v ∈ cyclic ρ e, ⟪v, u⟫_ℂ = 0 := by
  classical
  by_cases he : e ∈ U
  · left
    exact Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact U.apply_mem_toSubmodule g he)
  · right
    intro u hu v hv
    have horth (g : G) : ⟪ρ g e, u⟫_ℂ = 0 := by
      have hgu : ρ g⁻¹ u ∈ U := U.apply_mem_toSubmodule g⁻¹ hu
      have hk := hstable U _ hgu
      rw [hK] at hk
      have hz : ⟪e, ρ g⁻¹ u⟫_ℂ = 0 := by
        by_contra hne
        apply he
        have hh := U.toSubmodule.smul_mem (⟪e, ρ g⁻¹ u⟫_ℂ)⁻¹ hk
        change e ∈ U.toSubmodule
        simpa [smul_smul, hne] using hh
      have hi := hunit g e (ρ g⁻¹ u)
      simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply] using hi.trans hz
    induction hv using Submodule.span_induction with
    | mem v hv => obtain ⟨g, rfl⟩ := hv; exact horth g
    | zero => simp
    | add x y hx hy ihx ihy => simp [ihx, ihy]
    | smul a x hx ih => simp [ih]

theorem cyclic_irreducible (ρ : Representation ℂ G E) (e : E) (he : e ≠ 0)
    (hunit : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (K : Module.End ℂ E) (hK : ∀ v, K v = ⟪e, v⟫_ℂ • e)
    (hstable : ∀ U : Subrepresentation ρ, ∀ v ∈ U, K v ∈ U) :
    Representation.IsIrreducible (cyclic ρ e).toRepresentation := by
  let S := cyclic ρ e
  let eS : S.toSubmodule := ⟨e, self_mem_cyclic ρ e⟩
  have heS : eS ≠ 0 := by intro hh; apply he; exact congrArg Subtype.val hh
  have htb : (⊤ : Subrepresentation S.toRepresentation) ≠ ⊥ := by
    intro hh
    have hel : eS ∈ (⊤ : Subrepresentation S.toRepresentation) := by trivial
    rw [hh] at hel
    exact heS hel
  let : Nontrivial (Subrepresentation S.toRepresentation) := ⟨⟨⊤, ⊥, htb⟩⟩
  refine ⟨fun U => ?_⟩
  let U' : Subrepresentation ρ := {
    toSubmodule := U.toSubmodule.map S.toSubmodule.subtype
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact ⟨S.toRepresentation g u, U.apply_mem_toSubmodule g hu, rfl⟩ }
  rcases submodule_alternative ρ e hunit K hK hstable U' with h | h
  · right
    apply top_unique
    intro u _
    obtain ⟨v, hv, heq⟩ := h u.property
    have hvu : v = u := Subtype.ext heq
    exact hvu ▸ hv
  · left
    apply bot_unique
    intro u hu
    have hum : (u : E) ∈ U' := ⟨u, hu, rfl⟩
    have hh := h _ hum _ u.property
    have hz : (u : E) = 0 := inner_self_eq_zero.mp hh
    exact Subtype.ext hz

namespace PermutationSpace
open scoped Classical

variable {X : Type uX} [Fintype X] [MulAction G X]

def rep : Representation ℂ G (EuclideanSpace ℂ X) where
  toFun g := {
    toFun v := WithLp.toLp 2 (fun x => v (g⁻¹ • x))
    map_add' := by intro v w; rfl
    map_smul' := by intro a v; rfl }
  map_one' := by ext v x; simp
  map_mul' := by
    intro g h
    ext v x
    change v ((g * h)⁻¹ • x) = v (h⁻¹ • g⁻¹ • x)
    simp [mul_smul]

omit [Fintype X] in
@[simp] lemma rep_apply (g : G) (v : EuclideanSpace ℂ X) (x : X) :
    rep g v x = v (g⁻¹ • x) := rfl

lemma rep_unitary (g : G) (v w : EuclideanSpace ℂ X) :
    ⟪rep g v, rep g w⟫_ℂ = ⟪v, w⟫_ℂ := by
  simp only [PiLp.inner_apply, rep_apply]
  exact Equiv.sum_comp (MulAction.toPerm g⁻¹) (fun x => inner ℂ (v x) (w x))

omit [Fintype X] in
lemma rep_single (g : G) (x : X) :
    rep g (EuclideanSpace.single x (1 : ℂ)) = EuclideanSpace.single (g • x) (1 : ℂ) := by
  classical
  ext y
  simp only [rep_apply, PiLp.single_apply, inv_smul_eq_iff]

variable {H : Type uH} [Group H] [Fintype H]

def alternator (ι : H →* G) (χ : H →* ℂ) : Module.End ℂ (EuclideanSpace ℂ X) :=
  ∑ h, χ h • rep (ι h)

omit [Fintype X] in
lemma alternator_apply (ι : H →* G) (χ : H →* ℂ) (v : EuclideanSpace ℂ X) :
    alternator ι χ v = ∑ h, χ h • rep (ι h) v := by
  simp [alternator, LinearMap.sum_apply]

omit [Fintype X] in
lemma alternator_stable (ι : H →* G) (χ : H →* ℂ)
    (U : Subrepresentation (rep : Representation ℂ G (EuclideanSpace ℂ X)))
    (v : EuclideanSpace ℂ X) (hv : v ∈ U) : alternator ι χ v ∈ U := by
  rw [alternator_apply]
  exact U.toSubmodule.sum_mem fun h _ => U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule _ hv)

omit [Fintype X] in
lemma alternator_translate (ι : H →* G) (χ : H →* ℂ) (a : H)
    (v : EuclideanSpace ℂ X) :
    alternator ι χ (rep (ι a) v) = χ a⁻¹ • alternator ι χ v := by
  rw [alternator_apply, alternator_apply, Finset.smul_sum]
  have he := Equiv.sum_comp (Equiv.mulRight a)
    (fun h => χ a⁻¹ • (χ h • (rep (ι h) v : EuclideanSpace ℂ X)))
  rw [← he]
  apply Finset.sum_congr rfl
  intro h _
  simp only [Equiv.coe_mulRight, smul_smul, map_mul]
  rw [show χ a⁻¹ * (χ h * χ a) = χ h by
    calc
      _ = χ h * (χ a⁻¹ * χ a) := by ring
      _ = χ h := by rw [← map_mul, inv_mul_cancel, map_one, mul_one]]
  simp only [Module.End.mul_apply]

omit [Fintype X] in
lemma alternator_single_zero (ι : H →* G) (χ : H →* ℂ)
    (x : X) (a : H) (ha : ι a • x = x) (hs : χ a = -1) :
    alternator ι χ (EuclideanSpace.single x (1 : ℂ)) = 0 := by
  have hh := alternator_translate ι χ a (EuclideanSpace.single x (1 : ℂ))
  rw [rep_single, ha, map_inv, hs, inv_neg, inv_one, neg_smul, one_smul] at hh
  have hz := congrArg (fun z => z + alternator ι χ (EuclideanSpace.single x (1 : ℂ))) hh
  have ht : (2 : ℂ) • alternator ι χ (EuclideanSpace.single x (1 : ℂ)) = 0 := by
    simpa [two_smul] using hz
  exact (smul_eq_zero.mp ht).resolve_left (by norm_num)

omit [Fintype X] in
lemma alternator_coeff (ι : H →* G) (χ : H →* ℂ) (v : EuclideanSpace ℂ X) (x : X) :
    alternator ι χ v x = ∑ h, χ h * v ((ι h)⁻¹ • x) := by
  simp [alternator_apply, WithLp.ofLp_sum, Finset.sum_apply]

omit [Fintype X] in
lemma polytabloid_base (ι : H →* G) (χ : H →* ℂ) (b : X)
    (hfree : ∀ h : H, ι h • b = b → h = 1) :
    alternator ι χ (EuclideanSpace.single b (1 : ℂ)) b = 1 := by
  classical
  rw [alternator_coeff, Finset.sum_eq_single 1]
  · simp
  · intro h _ hh
    have hn : (ι h)⁻¹ • b ≠ b := by
      intro he
      have hi : h⁻¹ = 1 := hfree h⁻¹ (by simpa using he)
      exact hh (inv_eq_one.mp hi)
    simp [hn]
  · simp

lemma polytabloid_inner (ι : H →* G) (χ : H →* ℂ) (b : X)
    (hreal : ∀ h, conj (χ h) = χ h) (hinv : ∀ h, χ h⁻¹ = χ h)
    (v : EuclideanSpace ℂ X) :
    ⟪alternator ι χ (EuclideanSpace.single b (1 : ℂ)), v⟫_ℂ = alternator ι χ v b := by
  classical
  rw [alternator_apply, sum_inner, alternator_coeff]
  simp only [inner_smul_left, rep_single, EuclideanSpace.inner_single_left, map_one,
    one_mul, hreal]
  have hh := Equiv.sum_comp (Equiv.inv H) (fun h => χ h * v ((ι h)⁻¹ • b))
  simpa only [Equiv.inv_apply, map_inv, inv_inv, hinv] using hh

theorem alternator_rank_one (ι : H →* G) (χ : H →* ℂ) (b : X)
    (hreal : ∀ h, conj (χ h) = χ h) (hinv : ∀ h, χ h⁻¹ = χ h)
    (hfree : ∀ h : H, ι h • b = b → h = 1)
    (halt : ∀ x : X, (∃ a : H, ι a • x = x ∧ χ a = -1) ∨
      ∃ a : H, x = ι a • b) (v : EuclideanSpace ℂ X) :
    alternator ι χ v =
      ⟪alternator ι χ (EuclideanSpace.single b (1 : ℂ)), v⟫_ℂ •
        alternator ι χ (EuclideanSpace.single b (1 : ℂ)) := by
  classical
  let e := alternator ι χ (EuclideanSpace.single b (1 : ℂ))
  have hs (x : X) : alternator ι χ (EuclideanSpace.single x (1 : ℂ)) ∈ Submodule.span ℂ {e} := by
    rcases halt x with ⟨a, ha, hχ⟩ | ⟨a, rfl⟩
    · rw [alternator_single_zero ι χ x a ha hχ]
      exact Submodule.zero_mem _
    · rw [← rep_single, alternator_translate]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton e))
  have hv : alternator ι χ v ∈ Submodule.span ℂ {e} := by
    have hexp := (EuclideanSpace.basisFun X ℂ).sum_repr v
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at hexp
    rw [← hexp, map_sum]
    exact Submodule.sum_mem _ fun x _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (hs x)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
  have heb : e b = 1 := polytabloid_base ι χ b hfree
  have hab : a = alternator ι χ v b := by
    have hh := congrArg (fun z : EuclideanSpace ℂ X => z b) ha
    simpa only [PiLp.smul_apply, smul_eq_mul, heb, mul_one] using hh
  rw [← ha, hab, polytabloid_inner ι χ b hreal hinv]

end PermutationSpace

end Thorp.Specht

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Tableaux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young

abbrev Cells (D : YoungDiagram) := {p : ℕ × ℕ // p ∈ D.cells}

lemma fin_le_strictMono {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f) (i : Fin n) :
    i.val ≤ f i := by
  have aux : ∀ k (hk : k < n), k ≤ f ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have hl := hf (show (⟨k, hk'⟩ : Fin n) < ⟨k + 1, hk⟩ from by simp)
      have hi := ih hk'
      omega
  exact aux i.val i.isLt

lemma card_column (D : YoungDiagram) (j : ℕ) :
    (Finset.univ.filter fun x : Cells D => x.val.2 = j).card = D.colLen j := by
  classical
  let e : {x : Cells D // x.val.2 = j} ≃ Fin (D.colLen j) := {
    toFun := fun x => ⟨x.val.val.1, YoungDiagram.mem_iff_lt_colLen.mp (by
      have hx : (x.val.val.1, x.val.val.2) ∈ D := x.val.property
      simpa only [x.property] using hx)⟩
    invFun := fun i => ⟨⟨(i, j), YoungDiagram.mem_iff_lt_colLen.mpr i.isLt⟩, rfl⟩
    left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl x.property.symm
    right_inv := by intro i; rfl }
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

lemma card_row_subtype (D : YoungDiagram) (i : ℕ) :
    Fintype.card {x : Cells D // x.val.1 = i} = D.rowLen i := by
  let e : {x : Cells D // x.val.1 = i} ≃ Fin (D.rowLen i) := {
    toFun := fun x => ⟨x.val.val.2, YoungDiagram.mem_iff_lt_rowLen.mp (by
      have hx : (x.val.val.1, x.val.val.2) ∈ D := x.val.property
      simpa only [x.property] using hx)⟩
    invFun := fun j => ⟨⟨(i, j), YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩, rfl⟩
    left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.property.symm rfl
    right_inv := by intro j; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

lemma eq_of_rowPreserving (D E : YoungDiagram) (e : Cells D ≃ Cells E)
    (he : ∀ x, (e x).val.1 = x.val.1) : D = E := by
  have hr (i : ℕ) : D.rowLen i = E.rowLen i := by
    rw [← card_row_subtype D i, ← card_row_subtype E i]
    exact Fintype.card_congr (e.subtypeEquiv (fun x => by rw [he]))
  apply YoungDiagram.ext
  ext p
  obtain ⟨i, j⟩ := p
  change (i, j) ∈ D ↔ (i, j) ∈ E
  simp only [YoungDiagram.mem_iff_lt_rowLen, hr]

theorem column_sort_le (D : YoungDiagram) (r : Cells D → ℕ)
    (hinj : ∀ x y : Cells D, x.val.2 = y.val.2 → r x = r y → x = y)
    :
    ∃ σ : Equiv.Perm (Cells D), (∀ x, (σ x).val.2 = x.val.2) ∧
      ∀ x, x.val.1 ≤ r (σ x) := by
  classical
  let S (j : ℕ) : Finset ℕ := (Finset.univ.filter fun x : Cells D => x.val.2 = j).image r
  have hc (j : ℕ) : (S j).card = D.colLen j := by
    change ((Finset.univ.filter fun x : Cells D => x.val.2 = j).image r).card = _
    rw [Finset.card_image_iff.mpr (show Set.InjOn r ↑(Finset.univ.filter fun x : Cells D => x.val.2 = j) from by
      intro x hx y hy hxy
      exact hinj x y ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) hxy)]
    exact card_column D j
  let F (j : ℕ) := (S j).orderEmbOfFin (hc j)
  have hpre (x : Cells D) : ∃ y : Cells D, y.val.2 = x.val.2 ∧
      r y = F x.val.2 ⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp x.property⟩ := by
    have hm := (S x.val.2).orderEmbOfFin_mem (hc _) ⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp x.property⟩
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hm
    exact ⟨y, (Finset.mem_filter.mp hy).2, he⟩
  choose f hcol hr using hpre
  have hf : Function.Injective f := by
    intro x y he
    have hj : x.val.2 = y.val.2 := (hcol x).symm.trans ((congrArg (fun z : Cells D => z.val.2) he).trans (hcol y))
    have hi : x.val.1 = y.val.1 := by
      have hval : F x.val.2 ⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp x.property⟩ =
          F y.val.2 ⟨y.val.1, YoungDiagram.mem_iff_lt_colLen.mp y.property⟩ := by
        rw [← hr x, ← hr y, he]
      have hy : y.val.1 < D.colLen x.val.2 := by rw [hj]; exact YoungDiagram.mem_iff_lt_colLen.mp y.property
      have hid : F y.val.2 ⟨y.val.1, YoungDiagram.mem_iff_lt_colLen.mp y.property⟩ = F x.val.2 ⟨y.val.1, hy⟩ := by
        have aux (j k i : ℕ) (hk : j = k) (hi : i < D.colLen j) (hi' : i < D.colLen k) :
            F j ⟨i, hi⟩ = F k ⟨i, hi'⟩ := by subst k; rfl
        exact aux _ _ _ hj.symm _ _
      rw [hid] at hval
      exact congrArg Fin.val ((F x.val.2).injective hval)
    exact Subtype.ext (Prod.ext hi hj)
  let σ : Equiv.Perm (Cells D) := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  refine ⟨σ, hcol, ?_⟩
  have hle (x : Cells D) : x.val.1 ≤ r (σ x) := by
    change x.val.1 ≤ r (f x)
    rw [hr]
    exact fin_le_strictMono _ (F x.val.2).strictMono ⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp x.property⟩
  exact hle

lemma rowRankSum_le (D : YoungDiagram) (r : Cells D → ℕ)
    (hinj : ∀ x y : Cells D, x.val.2 = y.val.2 → r x = r y → x = y) :
    ∑ x : Cells D, x.val.1 ≤ ∑ x : Cells D, r x := by
  obtain ⟨σ, -, hσ⟩ := column_sort_le D r hinj
  rw [← Equiv.sum_comp σ r]
  exact Finset.sum_le_sum fun x _ => hσ x

theorem column_sort (D : YoungDiagram) (r : Cells D → ℕ)
    (hinj : ∀ x y : Cells D, x.val.2 = y.val.2 → r x = r y → x = y)
    (hsum : ∑ x : Cells D, r x = ∑ x : Cells D, x.val.1) :
    ∃ σ : Equiv.Perm (Cells D), (∀ x, (σ x).val.2 = x.val.2) ∧
      ∀ x, r (σ x) = x.val.1 := by
  obtain ⟨σ, hc, hle⟩ := column_sort_le D r hinj
  refine ⟨σ, hc, ?_⟩
  have heq : ∑ x : Cells D, x.val.1 = ∑ x : Cells D, r (σ x) := by
    rw [Equiv.sum_comp σ r, hsum]
  have hh := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun x _ => hle x)).mp heq
  intro x
  exact (hh x (Finset.mem_univ x)).symm

end Thorp.Young

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Specht
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Specht
open scoped Classical

variable {α : Type uα} [Fintype α]

omit [Fintype α] in
@[simp] lemma perm_apply_inv (g : Equiv.Perm α) (x : α) : g (g⁻¹ x) = x := g.apply_symm_apply x

omit [Fintype α] in
@[simp] lemma perm_inv_apply (g : Equiv.Perm α) (x : α) : g⁻¹ (g x) = x := g.symm_apply_apply x

def Tabloid (r : α → ℕ) := {f : α → ℕ // ∃ g : Equiv.Perm α, f = r ∘ g}

instance tabloidFinite (r : α → ℕ) : Finite (Tabloid r) := by
  apply Finite.of_surjective (fun g : Equiv.Perm α => (⟨r ∘ g, g, rfl⟩ : Tabloid r))
  rintro ⟨f, g, rfl⟩
  exact ⟨g, rfl⟩

instance tabloidFintype (r : α → ℕ) : Fintype (Tabloid r) := Fintype.ofFinite _

instance tabloidAction (r : α → ℕ) : MulAction (Equiv.Perm α) (Tabloid r) where
  smul g f := ⟨f.val ∘ ⇑(g⁻¹ : Equiv.Perm α), by
    obtain ⟨h, hh⟩ := f.property
    refine ⟨h * g⁻¹, ?_⟩
    funext x
    simp only [Function.comp_apply, hh, Equiv.Perm.mul_apply]⟩
  one_smul f := by apply Subtype.ext; funext x; rfl
  mul_smul g h f := by
    apply Subtype.ext
    funext x
    change f.val ((g * h)⁻¹ x) = f.val (h⁻¹ (g⁻¹ x))
    rw [mul_inv_rev, Equiv.Perm.mul_apply]

omit [Fintype α] in
@[simp] lemma tabloid_smul_apply (r : α → ℕ) (g : Equiv.Perm α) (f : Tabloid r) (x : α) :
    (g • f).val x = f.val (g⁻¹ x) := rfl

def baseTabloid (r : α → ℕ) : Tabloid r := ⟨r, 1, by funext x; rfl⟩

omit [Fintype α] in
@[simp] lemma baseTabloid_apply (r : α → ℕ) (x : α) : (baseTabloid r).val x = r x := rfl

def fiberGroup (c : α → ℕ) : Subgroup (Equiv.Perm α) where
  carrier := {g | ∀ x, c (g x) = c x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro g h hg hh x; exact (hg (h x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    have hh := hg (g⁻¹ x)
    change c (g (g.symm x)) = c (g.symm x) at hh
    rw [g.apply_symm_apply] at hh
    exact hh.symm

omit [Fintype α] in
lemma stabilizes_tabloid_iff (r : α → ℕ) (g : Equiv.Perm α) (f : Tabloid r) :
    g • f = f ↔ ∀ x, f.val (g x) = f.val x := by
  constructor
  · intro h x
    have hh := congrArg (fun t : Tabloid r => t.val (g x)) h
    simpa only [tabloid_smul_apply, perm_inv_apply] using hh.symm
  · intro h
    apply Subtype.ext
    funext x
    have hh := h (g⁻¹ x)
    simpa only [tabloid_smul_apply, perm_apply_inv] using hh.symm

omit [Fintype α] in
lemma swap_preserves {c : α → ℕ} {x y : α} (hc : c x = c y) :
    Equiv.swap x y ∈ fiberGroup c := by
  intro z
  by_cases hzx : z = x
  · subst z; simp [hc]
  by_cases hzy : z = y
  · subst z; simp [hc]
  rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]

def complexSign : Equiv.Perm α →* ℂ where
  toFun g := ((Equiv.Perm.sign g : ℤˣ) : ℤ)
  map_one' := by simp
  map_mul' := by intro g h; simp

@[simp] lemma complexSign_conj (g : Equiv.Perm α) : conj (complexSign g) = complexSign g := by
  simp [complexSign]

@[simp] lemma complexSign_inv (g : Equiv.Perm α) : complexSign g⁻¹ = complexSign g := by
  simp [complexSign]

@[simp] lemma complexSign_swap (x y : α) (h : x ≠ y) : complexSign (Equiv.swap x y) = -1 := by
  simp [complexSign, Equiv.Perm.sign_swap h]

variable (D : YoungDiagram) (t : α ≃ Thorp.Young.Cells D)

def tableauRow (x : α) : ℕ := (t x).val.1

def tableauCol (x : α) : ℕ := (t x).val.2

omit [Fintype α] in

lemma row_col_free (g : fiberGroup (tableauCol D t))
    (hg : (g : Equiv.Perm α) • baseTabloid (tableauRow D t) = baseTabloid (tableauRow D t)) : g = 1 := by
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro x
  apply t.injective
  apply Subtype.ext
  apply Prod.ext
  · exact (stabilizes_tabloid_iff _ _ _).mp hg x
  · exact g.property x

lemma collision_odd (f : Tabloid (tableauRow D t)) (x y : α) (hxy : x ≠ y)
    (hc : tableauCol D t x = tableauCol D t y) (hr : f.val x = f.val y) :
    ∃ g : fiberGroup (tableauCol D t), (g : Equiv.Perm α) • f = f ∧ complexSign (g : Equiv.Perm α) = -1 := by
  refine ⟨⟨Equiv.swap x y, swap_preserves hc⟩, ?_, complexSign_swap x y hxy⟩
  rw [stabilizes_tabloid_iff]
  exact swap_preserves hr

lemma collision_or_column (f : Tabloid (tableauRow D t)) :
    (∃ a : fiberGroup (tableauCol D t), (a : Equiv.Perm α) • f = f ∧
      complexSign (a : Equiv.Perm α) = -1) ∨
    ∃ a : fiberGroup (tableauCol D t), f = (a : Equiv.Perm α) • baseTabloid (tableauRow D t) := by
  classical
  by_cases hc : ∃ x y : α, x ≠ y ∧ tableauCol D t x = tableauCol D t y ∧ f.val x = f.val y
  · obtain ⟨x, y, hxy, hx, hy⟩ := hc
    exact Or.inl (collision_odd D t f x y hxy hx hy)
  right
  let r : Thorp.Young.Cells D → ℕ := fun z => f.val (t.symm z)
  have hi : ∀ x y : Thorp.Young.Cells D, x.val.2 = y.val.2 → r x = r y → x = y := by
    intro x y hcol hr
    by_contra hxy
    apply hc
    refine ⟨t.symm x, t.symm y, ?_, ?_, hr⟩
    · exact fun h => hxy (t.symm.injective h)
    · simpa only [tableauCol, Equiv.apply_symm_apply] using hcol
  have hs : ∑ z : Thorp.Young.Cells D, r z = ∑ z : Thorp.Young.Cells D, z.val.1 := by
    change ∑ z, f.val (t.symm z) = _
    rw [Equiv.sum_comp t.symm]
    obtain ⟨g, hg⟩ := f.property
    rw [hg]
    change ∑ x, tableauRow D t (g x) = _
    rw [Equiv.sum_comp g]
    exact Equiv.sum_comp t (fun z : Thorp.Young.Cells D => z.val.1)
  obtain ⟨σ, hσc, hσr⟩ := Thorp.Young.column_sort D r hi hs
  let a : Equiv.Perm α := (t.trans σ).trans t.symm
  have hac : a ∈ fiberGroup (tableauCol D t) := by
    intro x
    change (t (t.symm (σ (t x)))).val.2 = (t x).val.2
    simpa only [Equiv.apply_symm_apply] using hσc (t x)
  have har (x : α) : f.val (a x) = tableauRow D t x := hσr (t x)
  refine ⟨⟨a, hac⟩, ?_⟩
  apply Subtype.ext
  funext x
  have hh := har (a⁻¹ x)
  simpa only [tabloid_smul_apply, baseTabloid_apply, perm_apply_inv] using hh

def tabloidRep : Representation ℂ (Equiv.Perm α) (EuclideanSpace ℂ (Tabloid (tableauRow D t))) :=
  PermutationSpace.rep

def columnAlternator : Module.End ℂ (EuclideanSpace ℂ (Tabloid (tableauRow D t))) :=
  PermutationSpace.alternator (fiberGroup (tableauCol D t)).subtype
    (complexSign.comp (fiberGroup (tableauCol D t)).subtype)

def polytabloid : EuclideanSpace ℂ (Tabloid (tableauRow D t)) :=
  columnAlternator D t (EuclideanSpace.single (baseTabloid (tableauRow D t)) (1 : ℂ))

lemma polytabloid_support (f : Tabloid (tableauRow D t)) (hf : polytabloid D t f ≠ 0) :
    ∃ h : fiberGroup (tableauCol D t), f = h.val • baseTabloid (tableauRow D t) := by
  by_contra hn
  push Not at hn
  apply hf
  change PermutationSpace.alternator (fiberGroup (tableauCol D t)).subtype
    (complexSign.comp (fiberGroup (tableauCol D t)).subtype)
    (EuclideanSpace.single (baseTabloid (tableauRow D t)) (1 : ℂ)) f = 0
  rw [PermutationSpace.alternator_coeff]
  apply Finset.sum_eq_zero
  intro h _
  have hne : h.val⁻¹ • f ≠ baseTabloid (tableauRow D t) := by
    intro he
    exact hn h (inv_smul_eq_iff.mp he)
  rw [PiLp.single_apply]
  change complexSign h.val * (if h.val⁻¹ • f = baseTabloid (tableauRow D t) then 1 else 0) = 0
  rw [ite_eq_right hne, mul_zero]

lemma polytabloid_diag : polytabloid D t (baseTabloid (tableauRow D t)) = 1 := by
  exact PermutationSpace.polytabloid_base (fiberGroup (tableauCol D t)).subtype
    (complexSign.comp (fiberGroup (tableauCol D t)).subtype)
    (baseTabloid (tableauRow D t)) (row_col_free D t)

lemma polytabloid_ne_zero : polytabloid D t ≠ 0 := by
  have hh := PermutationSpace.polytabloid_base (fiberGroup (tableauCol D t)).subtype
    (complexSign.comp (fiberGroup (tableauCol D t)).subtype)
    (baseTabloid (tableauRow D t)) (row_col_free D t)
  intro hz
  change polytabloid D t (baseTabloid (tableauRow D t)) = 1 at hh
  rw [hz] at hh
  norm_num at hh

lemma columnAlternator_rank_one (v : EuclideanSpace ℂ (Tabloid (tableauRow D t))) :
    columnAlternator D t v = ⟪polytabloid D t, v⟫_ℂ • polytabloid D t := by
  exact PermutationSpace.alternator_rank_one (fiberGroup (tableauCol D t)).subtype
    (complexSign.comp (fiberGroup (tableauCol D t)).subtype)
    (baseTabloid (tableauRow D t)) (fun h => complexSign_conj h.val)
    (fun h => complexSign_inv h.val) (row_col_free D t) (collision_or_column D t) v

def module : Subrepresentation (tabloidRep D t) := cyclic (tabloidRep D t) (polytabloid D t)

theorem irreducible : Representation.IsIrreducible (module D t).toRepresentation := by
  exact cyclic_irreducible (tabloidRep D t) (polytabloid D t) (polytabloid_ne_zero D t)
    PermutationSpace.rep_unitary (columnAlternator D t) (columnAlternator_rank_one D t)
    (PermutationSpace.alternator_stable (fiberGroup (tableauCol D t)).subtype
      (complexSign.comp (fiberGroup (tableauCol D t)).subtype))

end Thorp.Specht

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Polytabloids
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Specht
open scoped Classical

variable {α : Type uα} [Fintype α]

lemma tabloid_sum (r : α → ℕ) (f : Tabloid r) : ∑ x, f.val x = ∑ x, r x := by
  obtain ⟨g, hg⟩ := f.property
  rw [hg]
  exact Equiv.sum_comp g r

lemma collision_zero (r c : α → ℕ) (f : Tabloid r)
    (x y : α) (hxy : x ≠ y) (hc : c x = c y) (hf : f.val x = f.val y) :
    PermutationSpace.alternator (fiberGroup c).subtype
      (complexSign.comp (fiberGroup c).subtype) (EuclideanSpace.single f 1) = 0 := by
  apply PermutationSpace.alternator_single_zero _ _ f (⟨Equiv.swap x y, swap_preserves hc⟩ : fiberGroup c)
  · rw [stabilizes_tabloid_iff]
    exact swap_preserves hf
  · exact complexSign_swap x y hxy

lemma alternator_nonzero_nocollision (r c : α → ℕ)
    (v : EuclideanSpace ℂ (Tabloid r))
    (hv : PermutationSpace.alternator (fiberGroup c).subtype
      (complexSign.comp (fiberGroup c).subtype) v ≠ 0) :
    ∃ f : Tabloid r, ∀ x y, c x = c y → f.val x = f.val y → x = y := by
  by_contra hn
  push Not at hn
  apply hv
  have hexp := (EuclideanSpace.basisFun (Tabloid r) ℂ).sum_repr v
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at hexp
  rw [← hexp, map_sum]
  apply Finset.sum_eq_zero
  intro f _
  obtain ⟨x, y, hcol, hrow, hne⟩ := hn f
  rw [map_smul, collision_zero r c f x y hne hcol hrow, smul_zero]

lemma rowRankSum_tableau (D : YoungDiagram) (t : α ≃ Thorp.Young.Cells D) :
    ∑ x : α, tableauRow D t x = ∑ z : Thorp.Young.Cells D, z.val.1 :=
  Equiv.sum_comp t (fun z => z.val.1)

lemma rankSum_le_of_nocollision (D E : YoungDiagram)
    (t : α ≃ Thorp.Young.Cells D) (u : α ≃ Thorp.Young.Cells E)
    (f : Tabloid (tableauRow E u))
    (hf : ∀ x y, tableauCol D t x = tableauCol D t y → f.val x = f.val y → x = y) :
    ∑ z : Thorp.Young.Cells D, z.val.1 ≤ ∑ z : Thorp.Young.Cells E, z.val.1 := by
  have hi : ∀ x y : Thorp.Young.Cells D, x.val.2 = y.val.2 →
      f.val (t.symm x) = f.val (t.symm y) → x = y := by
    intro x y hc hr
    apply t.symm.injective
    apply hf _ _ _ hr
    simpa only [tableauCol, Equiv.apply_symm_apply] using hc
  have hh := Thorp.Young.rowRankSum_le D (fun z => f.val (t.symm z)) hi
  rw [Equiv.sum_comp t.symm, tabloid_sum, rowRankSum_tableau] at hh
  exact hh

lemma shape_eq_of_nocollision_equal_sum (D E : YoungDiagram)
    (t : α ≃ Thorp.Young.Cells D) (u : α ≃ Thorp.Young.Cells E)
    (f : Tabloid (tableauRow E u))
    (hf : ∀ x y, tableauCol D t x = tableauCol D t y → f.val x = f.val y → x = y)
    (hs : ∑ z : Thorp.Young.Cells D, z.val.1 = ∑ z : Thorp.Young.Cells E, z.val.1) : D = E := by
  have hi : ∀ x y : Thorp.Young.Cells D, x.val.2 = y.val.2 →
      f.val (t.symm x) = f.val (t.symm y) → x = y := by
    intro x y hc hr
    apply t.symm.injective
    apply hf _ _ _ hr
    simpa only [tableauCol, Equiv.apply_symm_apply] using hc
  have hsum : ∑ z : Thorp.Young.Cells D, f.val (t.symm z) = ∑ z : Thorp.Young.Cells D, z.val.1 := by
    rw [Equiv.sum_comp t.symm, tabloid_sum, rowRankSum_tableau, hs]
  obtain ⟨σ, -, hσ⟩ := Thorp.Young.column_sort D (fun z => f.val (t.symm z)) hi hsum
  obtain ⟨g, hg⟩ := f.property
  apply Thorp.Young.eq_of_rowPreserving D E (((σ.trans t.symm).trans g).trans u)
  intro x
  have hh := hσ x
  rw [hg] at hh
  exact hh

lemma mapped_column_nonzero (D E : YoungDiagram)
    (t : α ≃ Thorp.Young.Cells D) (u : α ≃ Thorp.Young.Cells E)
    (F : Representation.IntertwiningMap (module D t).toRepresentation (module E u).toRepresentation)
    (hF : Function.Injective F) :
    ∃ v : EuclideanSpace ℂ (Tabloid (tableauRow E u)),
      PermutationSpace.alternator (fiberGroup (tableauCol D t)).subtype
        (complexSign.comp (fiberGroup (tableauCol D t)).subtype) v ≠ 0 := by
  let e : (module D t).toSubmodule := ⟨polytabloid D t, self_mem_cyclic _ _⟩
  have he : e ≠ 0 := by
    intro h
    exact polytabloid_ne_zero D t (congrArg Subtype.val h)
  have heig : ∑ h : fiberGroup (tableauCol D t), complexSign h.val •
      (module D t).toRepresentation h.val e = ⟪polytabloid D t, polytabloid D t⟫_ℂ • e := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    change (∑ h : fiberGroup (tableauCol D t), complexSign h.val •
      tabloidRep D t h.val (polytabloid D t)) = _
    exact (PermutationSpace.alternator_apply _ _ _).symm.trans (columnAlternator_rank_one D t _)
  have hh := congrArg (fun z => (F z : EuclideanSpace ℂ (Tabloid (tableauRow E u)))) heig
  simp only [map_sum, map_smul, F.isIntertwining, Submodule.coe_sum, Submodule.coe_smul] at hh
  refine ⟨F e, ?_⟩
  intro hz
  have heq : PermutationSpace.alternator (fiberGroup (tableauCol D t)).subtype
      (complexSign.comp (fiberGroup (tableauCol D t)).subtype) (F e : EuclideanSpace ℂ (Tabloid (tableauRow E u))) =
      ⟪polytabloid D t, polytabloid D t⟫_ℂ • (F e : EuclideanSpace ℂ (Tabloid (tableauRow E u))) := by
    rw [PermutationSpace.alternator_apply]
    exact hh
  rw [hz] at heq
  rcases smul_eq_zero.mp heq.symm with hs | hs
  · exact polytabloid_ne_zero D t (inner_self_eq_zero.mp hs)
  · have hh' : F e = 0 := Subtype.ext hs
    exact he (hF (by simpa using hh'))

lemma rankSum_le_of_injective_intertwiner (D E : YoungDiagram)
    (t : α ≃ Thorp.Young.Cells D) (u : α ≃ Thorp.Young.Cells E)
    (F : Representation.IntertwiningMap (module D t).toRepresentation (module E u).toRepresentation)
    (hF : Function.Injective F) :
    ∑ z : Thorp.Young.Cells D, z.val.1 ≤ ∑ z : Thorp.Young.Cells E, z.val.1 := by
  obtain ⟨v, hv⟩ := mapped_column_nonzero D E t u F hF
  obtain ⟨f, hf⟩ := alternator_nonzero_nocollision _ _ v hv
  exact rankSum_le_of_nocollision D E t u f hf

theorem shape_eq_of_equiv (D E : YoungDiagram)
    (t : α ≃ Thorp.Young.Cells D) (u : α ≃ Thorp.Young.Cells E)
    (F : Representation.Equiv (module D t).toRepresentation (module E u).toRepresentation) : D = E := by
  have hle := rankSum_le_of_injective_intertwiner D E t u F.toIntertwiningMap F.toLinearEquiv.injective
  have hge := rankSum_le_of_injective_intertwiner E D u t F.symm.toIntertwiningMap F.symm.toLinearEquiv.injective
  obtain ⟨v, hv⟩ := mapped_column_nonzero D E t u F.toIntertwiningMap F.toLinearEquiv.injective
  obtain ⟨f, hf⟩ := alternator_nonzero_nocollision _ _ v hv
  exact shape_eq_of_nocollision_equal_sum D E t u f hf (le_antisymm hle hge)

end Thorp.Specht

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Irreducibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uX uK

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

variable {n : ℕ} {D : YoungDiagram}

def Standard (t : Fin n ≃ Cells D) : Prop := StrictMono t.symm

lemma standard_row_lt_iff (t : Fin n ≃ Cells D) (ht : Standard t) (x y : Fin n)
    (hr : (t x).val.1 = (t y).val.1) : x < y ↔ (t x).val.2 < (t y).val.2 := by
  constructor
  · intro hxy
    by_contra hn
    have hc : (t y).val.2 ≤ (t x).val.2 := Nat.le_of_not_gt hn
    have hyx : t y ≤ t x := ⟨by omega, hc⟩
    have hh : y ≤ x := by simpa only [Equiv.symm_apply_apply] using ht.monotone hyx
    exact not_le_of_gt hxy hh
  · intro hc
    have hxy : t x < t y := by
      refine lt_iff_le_not_ge.mpr ⟨⟨by omega, hc.le⟩, ?_⟩
      intro hh
      exact not_le_of_gt hc hh.2
    simpa only [Equiv.symm_apply_apply] using ht hxy

lemma standard_col_lt_iff (t : Fin n ≃ Cells D) (ht : Standard t) (x y : Fin n)
    (hc : (t x).val.2 = (t y).val.2) : x < y ↔ (t x).val.1 < (t y).val.1 := by
  constructor
  · intro hxy
    by_contra hn
    have hr : (t y).val.1 ≤ (t x).val.1 := Nat.le_of_not_gt hn
    have hyx : t y ≤ t x := ⟨hr, by omega⟩
    have hh : y ≤ x := by simpa only [Equiv.symm_apply_apply] using ht.monotone hyx
    exact not_le_of_gt hxy hh
  · intro hr
    have hxy : t x < t y := by
      refine lt_iff_le_not_ge.mpr ⟨⟨hr.le, by omega⟩, ?_⟩
      intro hh
      exact not_le_of_gt hr hh.1
    simpa only [Equiv.symm_apply_apply] using ht hxy

lemma column_eq_rowRank (t : Fin n ≃ Cells D) (ht : Standard t) (x : Fin n) :
    Fintype.card {y : Fin n // y < x ∧ (t y).val.1 = (t x).val.1} = (t x).val.2 := by
  let e : {y : Fin n // y < x ∧ (t y).val.1 = (t x).val.1} ≃ Fin ((t x).val.2) := {
    toFun := fun y => ⟨(t y.val).val.2, (standard_row_lt_iff t ht y.val x y.property.2).mp y.property.1⟩
    invFun := fun j => ⟨t.symm ⟨((t x).val.1, j), D.up_left_mem le_rfl j.isLt.le (t x).property⟩, by
      constructor
      · apply (standard_row_lt_iff t ht _ x (by simp)).mpr
        simpa only [Equiv.apply_symm_apply] using j.isLt
      · simp⟩
    left_inv := by
      intro y
      apply Subtype.ext
      apply t.injective
      simp only [Equiv.apply_symm_apply]
      apply Subtype.ext
      exact Prod.ext y.property.2.symm rfl
    right_inv := by intro j; apply Fin.ext; simp }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

lemma standard_eq_of_rows (t u : Fin n ≃ Cells D) (ht : Standard t) (hu : Standard u)
    (hr : ∀ x, (t x).val.1 = (u x).val.1) : t = u := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  apply Prod.ext (hr x)
  rw [← column_eq_rowRank t ht x, ← column_eq_rowRank u hu x]
  exact Fintype.card_congr ((Equiv.refl (Fin n)).subtypeEquiv (fun y => by simp only [Equiv.refl_apply, hr]))

end Thorp.Young

namespace Thorp.Specht
open scoped Classical

theorem independent_of_leading {I : Type uI} {X : Type uX} {K : Type uK} [Fintype I] [Fintype X] [LinearOrder K]
    (e : I → EuclideanSpace ℂ X) (b : I → X) (key : X → K)
    (hinj : Function.Injective (key ∘ b)) (hdiag : ∀ i, e i (b i) ≠ 0)
    (htri : ∀ i x, e i x ≠ 0 → key (b i) ≤ key x) : LinearIndependent ℂ e := by
  let : LinearOrder I := LinearOrder.lift' (key ∘ b) hinj
  rw [linearIndependent_iff']
  intro s a ha i hi
  by_contra hai
  let S := s.filter fun j => a j ≠ 0
  have hs : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hai⟩⟩
  let j := S.min' hs
  have hj : j ∈ S := S.min'_mem hs
  have hj' : j ∈ s := (Finset.mem_filter.mp hj).1
  have haz : a j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hval := congrArg (fun v : EuclideanSpace ℂ X => v (b j)) ha
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at hval
  rw [Finset.sum_eq_single_of_mem j hj'] at hval
  · exact (mul_ne_zero haz (hdiag j)) hval
  · intro k hk hkj
    by_cases hak : a k = 0
    · simp [hak]
    have hks : k ∈ S := Finset.mem_filter.mpr ⟨hk, hak⟩
    have hjk : j ≤ k := S.min'_le k hks
    have hjk' : j < k := lt_of_le_of_ne hjk (Ne.symm hkj)
    have hzero : e k (b j) = 0 := by
      by_contra hn
      have hh := htri k (b j) hn
      exact not_le_of_gt hjk' hh
    simp [hzero]

end Thorp.Specht

namespace Thorp.Specht
open scoped Classical

variable {n : ℕ} (D : YoungDiagram) (t : Fin n ≃ Thorp.Young.Cells D)

lemma column_word_le (ht : Thorp.Young.Standard t) (c : fiberGroup (tableauCol D t)) :
    toLex (tableauRow D t) ≤ toLex (fun x => tableauRow D t (c.val⁻¹ x)) := by
  by_cases hc : c.val = 1
  · simp [hc]
  let S := Finset.univ.filter fun x : Fin n => c.val⁻¹ x ≠ x
  have hs : S.Nonempty := by
    by_contra hn
    apply hc
    have he : c.val⁻¹ = 1 := by
      apply Equiv.ext
      intro x
      by_contra hx
      exact hn ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
    exact inv_eq_one.mp he
  let x := S.min' hs
  have hx : c.val⁻¹ x ≠ x := (Finset.mem_filter.mp (S.min'_mem hs)).2
  have hbefore (y : Fin n) (hy : y < x) : c.val⁻¹ y = y := by
    by_contra hn
    have hm : y ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ y, hn⟩
    exact not_le_of_gt hy (S.min'_le y hm)
  have hlt : x < c.val⁻¹ x := by
    apply lt_of_le_of_ne
    · by_contra hn
      have hh := hbefore (c.val⁻¹ x) (lt_of_not_ge hn)
      exact hx (c.val.symm.injective hh)
    · exact Ne.symm hx
  have hcol : (t x).val.2 = (t (c.val⁻¹ x)).val.2 := by
    have hh := c.property (c.val⁻¹ x)
    simpa only [tableauCol, perm_apply_inv] using hh
  have hrow := (Thorp.Young.standard_col_lt_iff t ht x (c.val⁻¹ x) hcol).mp hlt
  apply le_of_lt
  change Pi.Lex (· < ·) (· < ·) (tableauRow D t) (fun y => tableauRow D t (c.val⁻¹ y))
  exact ⟨x, fun y hy => congrArg (tableauRow D t) (hbefore y hy).symm, hrow⟩

def movedTableau (g : Equiv.Perm (Fin n)) : Fin n ≃ Thorp.Young.Cells D := (g⁻¹).trans t

def StandardPerm := {g : Equiv.Perm (Fin n) // Thorp.Young.Standard (movedTableau D t g)}

instance instFintypeStandardPerm : Fintype (StandardPerm D t) := inferInstanceAs (Fintype {g : Equiv.Perm (Fin n) // Thorp.Young.Standard (movedTableau D t g)})

def movedWord (g : Equiv.Perm (Fin n)) : Tabloid (tableauRow D t) := g • baseTabloid (tableauRow D t)

lemma moved_diag (g : Equiv.Perm (Fin n)) :
    tabloidRep D t g (polytabloid D t) (movedWord D t g) = 1 := by
  change polytabloid D t (g⁻¹ • (g • baseTabloid (tableauRow D t))) = 1
  rw [inv_smul_smul]
  exact polytabloid_diag D t

lemma moved_leading (g : Equiv.Perm (Fin n)) (hg : Thorp.Young.Standard (movedTableau D t g))
    (f : Tabloid (tableauRow D t)) (hf : tabloidRep D t g (polytabloid D t) f ≠ 0) :
    toLex (movedWord D t g).val ≤ toLex f.val := by
  obtain ⟨h, hh⟩ := polytabloid_support D t (g⁻¹ • f) hf
  have he : f = (g * h.val) • baseTabloid (tableauRow D t) := by
    rw [mul_smul]
    exact inv_smul_eq_iff.mp hh
  let c : Equiv.Perm (Fin n) := g * h.val * g⁻¹
  have hc : c ∈ fiberGroup (tableauCol D (movedTableau D t g)) := by
    intro x
    change (t (g⁻¹ (g (h.val (g⁻¹ x))))).val.2 = (t (g⁻¹ x)).val.2
    rw [perm_inv_apply]
    exact h.property (g⁻¹ x)
  have hcword : c • movedWord D t g = f := by
    rw [he]
    change (g * h.val * g⁻¹) • (g • baseTabloid _) = (g * h.val) • baseTabloid _
    simp only [← mul_smul, inv_mul_cancel_right]
  have hw := column_word_le D (movedTableau D t g) hg ⟨c, hc⟩
  change toLex (movedWord D t g).val ≤ toLex (c • movedWord D t g).val at hw
  rw [hcword] at hw
  exact hw

lemma standardWord_injective : Function.Injective (fun g : StandardPerm D t => toLex (movedWord D t g.val).val) := by
  intro g h he
  have hr : ∀ x, (movedTableau D t g.val x).val.1 = (movedTableau D t h.val x).val.1 :=
    fun x => congrFun he x
  have ht := Thorp.Young.standard_eq_of_rows _ _ g.property h.property hr
  apply Subtype.ext
  apply inv_injective
  apply Equiv.ext
  intro x
  apply t.injective
  exact congrArg (fun z : Fin n ≃ Thorp.Young.Cells D => z x) ht

theorem standard_polytabloids_independent :
    LinearIndependent ℂ (fun g : StandardPerm D t => tabloidRep D t g.val (polytabloid D t)) := by
  apply independent_of_leading _ (fun g => movedWord D t g.val) (fun f => toLex f.val)
    (standardWord_injective D t)
  · intro i
    rw [moved_diag]
    exact one_ne_zero
  · intro i f hf
    exact moved_leading D t i.val i.property f hf

def orbitVector (g : Equiv.Perm (Fin n)) : (module D t).toSubmodule :=
  ⟨tabloidRep D t g (polytabloid D t),
    (module D t).apply_mem_toSubmodule g (self_mem_cyclic _ _)⟩

theorem standardPerm_card_le_degree :
    Fintype.card (StandardPerm D t) ≤ Module.finrank ℂ (module D t).toSubmodule := by
  have hi : LinearIndependent ℂ (fun g : StandardPerm D t => orbitVector D t g.val) :=
    LinearIndependent.of_comp (module D t).toSubmodule.subtype (standard_polytabloids_independent D t)
  exact hi.fintype_card_le_finrank

end Thorp.Specht

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Classification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uI uV uα

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

def rowCellsEquiv (D : YoungDiagram) : Cells D ≃ (i : Fin (D.colLen 0)) × Fin (D.rowLen i) where
  toFun x := ⟨⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp (D.up_left_mem le_rfl (Nat.zero_le _) x.property)⟩,
    ⟨x.val.2, YoungDiagram.mem_iff_lt_rowLen.mp x.property⟩⟩
  invFun x := ⟨(x.1, x.2), YoungDiagram.mem_iff_lt_rowLen.mpr x.2.isLt⟩
  left_inv x := rfl
  right_inv x := by cases x; rfl

lemma card_cells_eq_sum (D : YoungDiagram) : Fintype.card (Cells D) = D.rowLens.sum := by
  rw [Fintype.card_congr (rowCellsEquiv D), Fintype.card_sigma]
  simp only [Fintype.card_fin, YoungDiagram.rowLens]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Finset.sum_range]

def ofPartition {n : ℕ} (p : Nat.Partition n) : YoungDiagram :=
  YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) (Multiset.pairwise_sort _ _).sortedGE

lemma rowLens_ofPartition {n : ℕ} (p : Nat.Partition n) :
    (ofPartition p).rowLens = p.parts.sort (· ≥ ·) := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro x hx
  exact p.parts_pos ((Multiset.mem_sort _).mp hx)

lemma ofPartition_injective {n : ℕ} : Function.Injective (ofPartition (n := n)) := by
  intro p q hpq
  apply Nat.Partition.ext
  have hh := congrArg YoungDiagram.rowLens hpq
  rw [rowLens_ofPartition, rowLens_ofPartition] at hh
  simpa only [Multiset.sort_eq] using congrArg (fun x : List ℕ => (x : Multiset ℕ)) hh

def toPartition (D : YoungDiagram) (n : ℕ) (hn : Fintype.card (Cells D) = n) : Nat.Partition n where
  parts := D.rowLens
  parts_pos := fun hx => D.pos_of_mem_rowLens _ hx
  parts_sum := by simpa only [Multiset.sum_coe, ← card_cells_eq_sum] using hn

end Thorp.Young

namespace Thorp.Fourier
open scoped Classical

variable {G : Type uG} [Group G] [Fintype G]

def charPair (f h : G → ℂ) : ℂ := (Nat.card G : ℂ)⁻¹ * ∑ g, f g * h g⁻¹

lemma charPair_sum {I : Type uI} (s : Finset I) (a : I → ℂ) (f : I → G → ℂ) (h : G → ℂ) :
    charPair (∑ i ∈ s, a i • f i) h = ∑ i ∈ s, a i * charPair (f i) h := by
  simp only [charPair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_assoc (a i)]
  rw [← Finset.mul_sum]
  ring

lemma charPair_zero (h : G → ℂ) : charPair (0 : G → ℂ) h = 0 := by simp [charPair]

lemma irreducible_char_independent {I : Type uI} {V : I → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) [∀ i, Representation.IsIrreducible (ρ i)]
    (hne : ∀ i j, Nonempty (Representation.Equiv (ρ i) (ρ j)) → i = j) :
    LinearIndependent ℂ (fun i => (ρ i).character) := by
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne _)
  have ho (i j : I) : charPair (ρ i).character (ρ j).character = if i = j then 1 else 0 := by
    rw [charPair, Representation.char_orthonormal]
    congr 1
    apply propext
    constructor
    · exact fun h => (hne j i h).symm
    · intro h; subst j; exact ⟨Representation.Equiv.refl _⟩
  rw [linearIndependent_iff']
  intro s a ha i hi
  have hh := congrArg (fun f => charPair f (ρ i).character) ha
  rw [charPair_sum, charPair_zero] at hh
  simp only [ho] at hh
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', ite_eq_left hi] using hh

end Thorp.Fourier

namespace Thorp.Specht
open scoped Classical
variable {α : Type uα} [Fintype α]

abbrev Shape (α : Type uα) [Fintype α] := Nat.Partition (Fintype.card α)

def canonicalTableau (p : Shape α) : α ≃ Thorp.Young.Cells (Thorp.Young.ofPartition p) := by
  have card_cells_eq_sum (D : YoungDiagram) : Fintype.card (Thorp.Young.Cells D) = D.rowLens.sum := by
    rw [Fintype.card_congr (Thorp.Young.rowCellsEquiv D), Fintype.card_sigma]
    simp only [Fintype.card_fin, YoungDiagram.rowLens]
    rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Finset.sum_range]
  have rowLens_ofPartition {n : ℕ} (p : Nat.Partition n) :
      (Thorp.Young.ofPartition p).rowLens = p.parts.sort (· ≥ ·) := by
    apply YoungDiagram.rowLens_ofRowLens_eq_self
    intro x hx
    exact p.parts_pos ((Multiset.mem_sort _).mp hx)
  have card_ofPartition {n : ℕ} (p : Nat.Partition n) : Fintype.card (Thorp.Young.Cells (Thorp.Young.ofPartition p)) = n := by
    rw [card_cells_eq_sum, rowLens_ofPartition]
    simpa only [← Multiset.sum_coe, Multiset.sort_eq] using p.parts_sum
  exact Fintype.equivOfCardEq (card_ofPartition p).symm

abbrev Space (p : Shape α) := (module (Thorp.Young.ofPartition p) (canonicalTableau p)).toSubmodule

def family (p : Shape α) : Representation ℂ (Equiv.Perm α) (Space p) :=
  (module (Thorp.Young.ofPartition p) (canonicalTableau p)).toRepresentation

instance family_irreducible (p : Shape α) : Representation.IsIrreducible (family p) :=
  irreducible (Thorp.Young.ofPartition p) (canonicalTableau p)

lemma family_inequiv (p q : Shape α) (he : Nonempty (Representation.Equiv (family p) (family q))) : p = q := by
  obtain ⟨e⟩ := he
  apply Thorp.Young.ofPartition_injective
  exact shape_eq_of_equiv _ _ _ _ e

lemma characters_independent : LinearIndependent ℂ (fun p : Shape α => (family p).character) :=
  Thorp.Fourier.irreducible_char_independent family family_inequiv

def classLift (f : Equiv.Perm α → ℂ) (p : Shape α) : ℂ :=
  if h : ∃ g : Equiv.Perm α, g.partition = p then f h.choose else 0

lemma classLift_apply (f : Equiv.Perm α → ℂ)
    (hf : ∀ g h, IsConj g h → f g = f h) (g : Equiv.Perm α) :
    classLift f g.partition = f g := by
  unfold classLift
  have hh : ∃ a : Equiv.Perm α, a.partition = g.partition := ⟨g, rfl⟩
  rw [dite_eq_left hh]
  exact hf _ g (Equiv.Perm.partition_eq_of_isConj.mpr hh.choose_spec)

lemma character_isClass (p : Shape α) (g h : Equiv.Perm α) (hgh : IsConj g h) :
    (family p).character g = (family p).character h := by
  obtain ⟨x, hx⟩ := isConj_iff.mp hgh
  rw [← hx]
  exact (Representation.char_conj (family p) g x).symm

lemma liftedCharacters_independent :
    LinearIndependent ℂ (fun p : Shape α => classLift (family p).character) := by
  let E : (Shape α → ℂ) →ₗ[ℂ] (Equiv.Perm α → ℂ) := {
    toFun := fun f g => f g.partition
    map_add' := by intro f h; rfl
    map_smul' := by intro a f; rfl }
  apply LinearIndependent.of_comp E
  convert characters_independent (α := α) using 1
  funext p g
  exact classLift_apply _ (character_isClass p) g

def characterBasis : Module.Basis (Shape α) ℂ (Shape α → ℂ) :=
  basisOfPiSpaceOfLinearIndependent liftedCharacters_independent

lemma characterBasis_apply (p : Shape α) : characterBasis p = classLift (family p).character := by
  exact congrFun (coe_basisOfPiSpaceOfLinearIndependent liftedCharacters_independent) p

end Thorp.Specht

namespace Thorp.Specht
open scoped Classical
variable {α : Type uα} [Fintype α]

lemma class_expansion (f : Equiv.Perm α → ℂ)
    (hf : ∀ g h, IsConj g h → f g = f h) :
    (∑ p : Shape α, (characterBasis.repr (classLift f)) p • (family p).character) = f := by
  funext g
  have he := congrFun (characterBasis.sum_repr (classLift f)) g.partition
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, characterBasis_apply,
    classLift_apply _ (character_isClass _), classLift_apply _ hf] at he
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he

lemma char_orthogonal (p q : Shape α) :
    Thorp.Fourier.charPair (family p).character (family q).character = if p = q then 1 else 0 := by
  let : Invertible (Nat.card (Equiv.Perm α) : ℂ) := invertibleOfNonzero (NeZero.ne _)
  rw [Thorp.Fourier.charPair, Representation.char_orthonormal]
  congr 1
  apply propext
  exact ⟨fun h => (family_inequiv q p h).symm,
    fun h => by subst q; exact ⟨Representation.Equiv.refl _⟩⟩

lemma class_coeff (f : Equiv.Perm α → ℂ)
    (hf : ∀ g h, IsConj g h → f g = f h) (q : Shape α) :
    characterBasis.repr (classLift f) q = Thorp.Fourier.charPair f (family q).character := by
  have he := congrArg (fun x => Thorp.Fourier.charPair x (family q).character) (class_expansion f hf)
  rw [Thorp.Fourier.charPair_sum] at he
  simp only [char_orthogonal, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] at he
  exact he

def degree (p : Shape α) : ℕ := Module.finrank ℂ (Space p)

theorem regular_char (g : Equiv.Perm α) :
    ∑ p : Shape α, (degree p : ℂ) * (family p).character g =
      if g = 1 then (Nat.card (Equiv.Perm α) : ℂ) else 0 := by
  let δ : Equiv.Perm α → ℂ := fun h => if h = 1 then Nat.card (Equiv.Perm α) else 0
  have hδ : ∀ a b, IsConj a b → δ a = δ b := by
    intro a b hab
    have hh : a = 1 ↔ b = 1 := by
      obtain ⟨c, hc⟩ := isConj_iff.mp hab
      rw [← hc]
      constructor
      · intro ha; simp [ha]
      · intro hb
        have hh := congrArg (fun z => c⁻¹ * z * c) hb
        simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, one_mul, mul_one] using hh
    simp only [δ, hh]
  have hc (p : Shape α) : Thorp.Fourier.charPair δ (family p).character = degree p := by
    rw [Thorp.Fourier.charPair]
    simp only [δ, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, inv_one,
      Representation.char_one]
    rw [← mul_assoc, inv_mul_cancel₀ (NeZero.ne _), one_mul]
    rfl
  have he := congrFun (class_expansion δ hδ) g
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, class_coeff δ hδ, hc] using he

end Thorp.Specht

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_LinearExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uα uI uB

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

variable (A : Type uA) [Fintype A] [PartialOrder A]

def Extensions := {e : A ≃ Fin (Fintype.card A) // StrictMono e}

instance instFintypeExtensions : Fintype (Extensions A) := inferInstanceAs (Fintype {e : A ≃ Fin (Fintype.card A) // StrictMono e})

lemma extensions_nonempty : Nonempty (Extensions A) := by
  let h : A ≃ LinearExtension A := Equiv.refl A
  let : Fintype (LinearExtension A) := Fintype.ofEquiv A h
  let e := (Fintype.orderIsoFinOfCardEq (LinearExtension A) (Fintype.card_congr h.symm)).symm
  refine ⟨⟨h.trans e.toEquiv, ?_⟩⟩
  exact e.strictMono.comp
    (toLinearExtension.monotone.strictMono_of_injective fun _ _ hh => hh)

end Thorp.Young

namespace Thorp.Specht
open scoped Classical
variable {n : ℕ} (D : YoungDiagram) (t : Fin n ≃ Thorp.Young.Cells D)

lemma labels_card_le_degree {I : Type uI} [Fintype I]
    (l : I → Thorp.Young.Cells D ≃ Fin n) (hl : ∀ i, StrictMono (l i))
    (hi : Function.Injective l) : Fintype.card I ≤ Module.finrank ℂ (module D t).toSubmodule := by
  let F (i : I) : StandardPerm D t := ⟨t.trans (l i), by
    intro x y hxy
    change l i (t (t.symm x)) < l i (t (t.symm y))
    simpa only [Equiv.apply_symm_apply] using hl i hxy⟩
  have hF : Function.Injective F := by
    intro i j hij
    apply hi
    apply Equiv.ext
    intro x
    have hh := congrArg (fun g : StandardPerm D t => g.val (t.symm x)) hij
    simpa only [F, Equiv.trans_apply, Equiv.apply_symm_apply] using hh
  exact (Fintype.card_le_of_injective F hF).trans (standardPerm_card_le_degree D t)

lemma extensions_card_le_degree :
    Fintype.card (Thorp.Young.Extensions (Thorp.Young.Cells D)) ≤
      Module.finrank ℂ (module D t).toSubmodule := by
  have hc : Fintype.card (Thorp.Young.Cells D) = n := (Fintype.card_congr t.symm).trans (Fintype.card_fin n)
  let c := finCongr hc
  apply labels_card_le_degree D t (fun e => e.val.trans c)
  · intro e x y hxy
    exact e.property hxy
  · intro e f hef
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply c.injective
    exact congrArg (fun z : Thorp.Young.Cells D ≃ Fin n => z x) hef

end Thorp.Specht

namespace Thorp.Young
open scoped Classical

def transposeCells (D : YoungDiagram) : Cells D ≃o Cells D.transpose where
  toFun x := ⟨x.val.swap, by
    change x.val.swap ∈ D.transpose
    rw [YoungDiagram.mem_transpose, Prod.swap_swap]
    exact x.property⟩
  invFun x := ⟨x.val.swap, (YoungDiagram.mem_transpose.mp x.property)⟩
  left_inv x := by apply Subtype.ext; exact Prod.swap_swap x.val
  right_inv x := by apply Subtype.ext; exact Prod.swap_swap x.val
  map_rel_iff' := by intro x y; exact and_comm

def longest (D : YoungDiagram) : ℕ := max (D.rowLen 0) (D.colLen 0)

end Thorp.Young

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_ExtensionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

abbrev Lower (D : YoungDiagram) := {x : Cells D // x.val.1 ≠ 0}

def topPrefix (D : YoungDiagram) (u : ℕ) : Set (Cells D) :=
  {x | x.val.1 = 0 ∧ x.val.2 < u}

end Thorp.Young

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_PartitionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

def idealDiagram (D : YoungDiagram) (s : Set (Cells D)) (hs : IsLowerSet s) : YoungDiagram where
  cells := (Finset.univ.filter (· ∈ s)).image Subtype.val
  isLowerSet := by
    intro y x hxy hy
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
    have hyD : y ∈ D := by rw [← hzy]; exact z.property
    have hxD : x ∈ D := D.isLowerSet hxy hyD
    refine Finset.mem_image.mpr ⟨⟨x, hxD⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    apply hs (show (⟨x, hxD⟩ : Cells D) ≤ z from by change x ≤ z.val; rwa [hzy])
    exact (Finset.mem_filter.mp hz).2

lemma mem_idealDiagram (D : YoungDiagram) (s : Set (Cells D)) (hs : IsLowerSet s) (p : ℕ × ℕ) :
    p ∈ idealDiagram D s hs ↔ ∃ h : p ∈ D, (⟨p, h⟩ : Cells D) ∈ s := by
  constructor
  · intro hp
    obtain ⟨x, hx, hxp⟩ := Finset.mem_image.mp hp
    subst p
    exact ⟨x.property, (Finset.mem_filter.mp hx).2⟩
  · rintro ⟨h, hp⟩
    exact Finset.mem_image.mpr ⟨⟨p, h⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩

def idealCells (D : YoungDiagram) (s : Set (Cells D)) (hs : IsLowerSet s) :
    Cells (idealDiagram D s hs) ≃o s where
  toFun x := ⟨⟨x.val, (mem_idealDiagram D s hs x.val).mp x.property |>.choose⟩,
    (mem_idealDiagram D s hs x.val).mp x.property |>.choose_spec⟩
  invFun x := ⟨x.val.val, (mem_idealDiagram D s hs x.val.val).mpr ⟨x.val.property, x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

end Thorp.Young

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_DegreeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

def rowTail (D : YoungDiagram) : YoungDiagram where
  cells := (D.cells.filter (fun p => p.1 ≠ 0)).image (fun p => (p.1 - 1, p.2))
  isLowerSet := by
    intro y x hxy hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hpD, hp0⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_image.mpr
    refine ⟨(x.1 + 1, x.2), Finset.mem_filter.mpr ⟨?_, by omega⟩, ?_⟩
    · exact D.up_left_mem (by have := hxy.1; omega) hxy.2 hpD
    · simp

lemma mem_rowTail (D : YoungDiagram) (i j : ℕ) : (i, j) ∈ rowTail D ↔ (i + 1, j) ∈ D := by
  change (i, j) ∈ (D.cells.filter (fun p => p.1 ≠ 0)).image (fun p => (p.1 - 1, p.2)) ↔ _
  constructor
  · intro h
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp h
    obtain ⟨hpD, hp0⟩ := Finset.mem_filter.mp hp
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    have hp : p = (i + 1, j) := Prod.ext (by dsimp at h₁; omega) h₂
    simpa only [← hp, YoungDiagram.mem_cells] using hpD
  · intro h
    exact Finset.mem_image.mpr ⟨(i + 1, j), Finset.mem_filter.mpr ⟨h, by omega⟩, by simp⟩

def rowTailCells (D : YoungDiagram) : Cells (rowTail D) ≃ Lower D where
  toFun x := ⟨⟨(x.val.1 + 1, x.val.2), (mem_rowTail D _ _).mp x.property⟩, by simp⟩
  invFun x := ⟨(x.val.val.1 - 1, x.val.val.2), (mem_rowTail D _ _).mpr (by
    have h : x.val.val.1 - 1 + 1 = x.val.val.1 := by have := x.property; omega
    simpa only [h, YoungDiagram.mem_cells, Prod.mk.eta] using x.val.property)⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by
    apply Subtype.ext; apply Subtype.ext
    exact Prod.ext (by have := x.property; dsimp; omega) rfl

def orient (D : YoungDiagram) : YoungDiagram :=
  if D.colLen 0 ≤ D.rowLen 0 then D else D.transpose

def orientation (D : YoungDiagram) : Bool := decide (D.colLen 0 ≤ D.rowLen 0)

end Thorp.Young

namespace Thorp.Specht
open scoped Classical
open Thorp.Young

abbrev NShape (n : ℕ) := Shape (Fin n)

def defect {n : ℕ} (p : NShape n) : ℕ := n - longest (ofPartition p)

lemma extensions_le_degree {n : ℕ} (p : NShape n) :
    Fintype.card (Extensions (Cells (ofPartition p))) ≤ degree p :=
  extensions_card_le_degree (ofPartition p) (canonicalTableau p)

lemma degree_pos {n : ℕ} (p : NShape n) : 0 < degree p := by
  let := extensions_nonempty (Cells (ofPartition p))
  exact (Fintype.card_pos).trans_le (extensions_le_degree p)

end Thorp.Specht

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_ReciprocalDegrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

open Filter Topology

namespace Thorp.Specht
open scoped Classical
open Filter Topology Thorp.Young

variable {n : ℕ}

def inverseDegree (p : NShape n) : ℝ := ((degree p : ℝ)^2)⁻¹

def slice (n u : ℕ) : ℝ := ∑ p : {p : NShape n // defect p = u}, inverseDegree p.val

def smallSlice (n u : ℕ) : ℝ := if 0 < u ∧ 4 * u ≤ n then slice n u else 0

def exceptionalReciprocalSum (n : ℕ) : ℝ := ∑ p : NShape n, if 0 < defect p then inverseDegree p else 0

end Thorp.Specht

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Reynolds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uV uW uE uI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def integrated (ρ : Representation ℂ G V) (f : G → ℂ) : Module.End ℂ V :=
  ∑ g, f g • ρ g

def reynolds (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (A : V →ₗ[ℂ] W) : V →ₗ[ℂ] W :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, σ g ∘ₗ A ∘ₗ ρ g⁻¹

lemma reynolds_intertwines (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (A : V →ₗ[ℂ] W)
    (h : G) (v : V) : reynolds ρ σ A (ρ h v) = σ h (reynolds ρ σ A v) := by
  simp only [reynolds, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    map_smul, map_sum]
  congr 1
  have he := Equiv.sum_comp (Equiv.mulLeft h) (fun g : G => σ g (A (ρ g⁻¹ (ρ h v))))
  rw [← he]
  apply Finset.sum_congr rfl
  intro g _
  change σ (h * g) (A (ρ (h * g)⁻¹ (ρ h v))) = σ h (σ g (A (ρ g⁻¹ v)))
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply]
  congr 2
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

def reynoldsMap (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (A : V →ₗ[ℂ] W) :
    Representation.IntertwiningMap ρ σ :=
  (reynolds ρ σ A).intertwiningMap_of_isIntertwiningMap ρ σ (reynolds_intertwines ρ σ A)

end Thorp.Fourier

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

def convolution (f k : G → ℂ) (x : G) : ℂ := ∑ g, f g * k (g⁻¹ * x)

def delta : G → ℂ := fun g => if g = 1 then 1 else 0

end Thorp.Fourier

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_FourierFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uE uV

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical

structure Family (G : Type) [Group G] [Fintype G] where
  Index : Type
  [finiteIndex : Fintype Index]
  Space : Index → Type
  [normed : ∀ i, NormedAddCommGroup (Space i)]
  [innerSpace : ∀ i, InnerProductSpace ℂ (Space i)]
  [finiteDim : ∀ i, FiniteDimensional ℂ (Space i)]
  rep : ∀ i, Representation ℂ G (Space i)
  [irreducible : ∀ i, Representation.IsIrreducible (rep i)]
  positive : ∀ i, 0 < Module.finrank ℂ (Space i)
  unitary : ∀ i g x y, ⟪rep i g x, rep i g y⟫_ℂ = ⟪x, y⟫_ℂ
  distinct : ∀ i j, Nonempty (Representation.Equiv (rep i) (rep j)) → i = j
  regular : ∀ g, ∑ i, (Module.finrank ℂ (Space i) : ℂ) * (rep i).character g =
    if g = 1 then (Fintype.card G : ℂ) else 0

attribute [instance] Family.finiteIndex Family.normed Family.innerSpace Family.finiteDim Family.irreducible

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)

def degree (i : F.Index) : ℕ := Module.finrank ℂ (F.Space i)

def kernel (i : F.Index) (g : G) : ℂ :=
  (F.degree i : ℂ) * (Fintype.card G : ℂ)⁻¹ * (F.rep i).character g⁻¹

end Family
end Thorp.Fourier

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

def projector (ρ : Representation ℂ G V) (i : F.Index) : Module.End ℂ V := integrated ρ (F.kernel i)

end Family
end Thorp.Fourier

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_JointProjectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uE

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier.Family
open scoped Classical
variable {H : Type} [Group H] [Fintype H] (F : Family H)
variable {I : Type} [Fintype I]

def jointKernel (a : I → F.Index) (g : I → H) : ℂ := ∏ i, F.kernel (a i) (g i)

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

def jointProjector (ρ : Representation ℂ (I → H) E) (a : I → F.Index) : Module.End ℂ E :=
  integrated ρ (F.jointKernel a)

def tensorList (a : I → F.Index) : List I → FDRep ℂ (I → H)
  | [] => FDRep.of (Representation.trivial ℂ (I → H) ℂ)
  | i :: l => FDRep.of (Representation.tprod ((F.rep (a i)).comp (Pi.evalMonoidHom (fun _ : I => H) i)) (tensorList a l).ρ)

def tensorFamily (a : I → F.Index) : FDRep ℂ (I → H) := F.tensorList a Finset.univ.toList

end Thorp.Fourier.Family

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_ProductProjectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uH uI uE uJ

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical

namespace Family
variable {H I : Type} [Group H] [Fintype H] [Fintype I] [Nonempty I] (F : Family H)

noncomputable def leastFactor (a : I → F.Index) : I :=
  Classical.choose (Finset.exists_min_image Finset.univ (fun i => F.degree (a i)) Finset.univ_nonempty)

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

noncomputable def splitVector (ρ : Representation ℂ (I → H) E) (v : E) (i : I) : E :=
  ∑ a : I → F.Index, if F.leastFactor a = i then F.jointProjector ρ a v else 0

end Family
end Thorp.Fourier

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_FourierBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uE

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier.Family
open scoped Classical
variable {H : Type} [Group H] [Fintype H] (F : Family H)

def reciprocalSum : ℝ := ∑ b, ((F.degree b : ℝ) ^ 2)⁻¹

end Thorp.Fourier.Family

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

noncomputable def hsSq (A : Module.End ℂ E) : ℝ :=
  ∑ k, ‖A (stdOrthonormalBasis ℂ E k)‖ ^ 2

end Thorp.Fourier

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_SymmetricFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Specht
open scoped Classical
open Thorp.Young

lemma family_unitary {α : Type} [Fintype α] (p : Shape α) (g : Equiv.Perm α) (v w : Space (α:=α) p) :
    ⟪family p g v, family p g w⟫_ℂ = ⟪v, w⟫_ℂ := by
  change ⟪tabloidRep _ _ g v.val, tabloidRep _ _ g w.val⟫_ℂ = ⟪v.val, w.val⟫_ℂ
  exact PermutationSpace.rep_unitary g v.val w.val

lemma regular_char_fin (n : ℕ) (g : Equiv.Perm (Fin n)) :
    ∑ p : NShape n, (Module.finrank ℂ (Space (α:=Fin n) p) : ℂ) * (family (α:=Fin n) p).character g =
      if g = 1 then (Fintype.card (Equiv.Perm (Fin n)) : ℂ) else 0 := by
  have hc : Fintype.card (Equiv.Perm (Fin n)) = Nat.card (Equiv.Perm (Fin n)) := Fintype.card_eq_nat_card
  rw [hc]
  by_cases h : g = 1
  · simpa only [degree, ite_eq_left h] using regular_char g
  · simpa only [degree, ite_eq_right h] using regular_char g

def symmetricFamily (n : ℕ) : Thorp.Fourier.Family (Equiv.Perm (Fin n)) where
  Index := NShape n
  Space := fun p => Space (α:=Fin n) p
  rep := fun p => family (α:=Fin n) p
  positive := by
    intro p
    simpa only [degree] using degree_pos p
  unitary := fun p g v w => family_unitary (α:=Fin n) p g v w
  distinct := fun p q h => family_inequiv (α:=Fin n) p q h
  regular := by
    intro g
    by_cases h : g = 1
    · simpa only [ite_eq_left h] using regular_char_fin n g
    · simpa only [ite_eq_right h] using regular_char_fin n g

end Thorp.Specht

namespace Thorp.Fourier
open scoped Classical

variable {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def subrepPull (ρ : Representation ℂ G V) (e : H ≃* G) :
    Subrepresentation ρ ≃o Subrepresentation (ρ.comp e.toMonoidHom) where
  toFun U := { toSubmodule := U.toSubmodule
               apply_mem_toSubmodule := fun h => U.apply_mem_toSubmodule (e h) }
  invFun U := { toSubmodule := U.toSubmodule
                apply_mem_toSubmodule := by
                  intro g v hv
                  have hh := U.apply_mem_toSubmodule (e.symm g) hv
                  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using hh }
  left_inv U := by rfl
  right_inv U := by rfl
  map_rel_iff' := by rfl

def Family.pull (F : Family G) (e : H ≃* G) : Family H where
  Index := F.Index
  Space := F.Space
  rep i := (F.rep i).comp e.toMonoidHom
  irreducible i := (subrepPull (F.rep i) e).symm.isSimpleOrder
  positive := F.positive
  unitary := fun i h => F.unitary i (e h)
  distinct := by
    intro i j hh
    obtain ⟨A⟩ := hh
    apply F.distinct i j
    refine ⟨{ A.toLinearEquiv with isIntertwining' := ?_ }⟩
    intro g
    ext v
    have ha := DFunLike.congr_fun (A.isIntertwining' (e.symm g)) v
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using ha
  regular := by
    intro h
    have hh := F.regular (e h)
    have hc : Fintype.card G = Fintype.card H := (Fintype.card_congr e.toEquiv).symm
    change ∑ i, (Module.finrank ℂ (F.Space i) : ℂ) * (F.rep i).character (e h) = _
    simpa only [e.map_eq_one_iff, hc] using hh

end Thorp.Fourier

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_PermutationCharacters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Specht
open scoped Classical

variable {α : Type} [Fintype α]

def permutationFamily (α : Type) [Fintype α] [DecidableEq α] : Thorp.Fourier.Family (Equiv.Perm α) :=
  (symmetricFamily (Fintype.card α)).pull (Equiv.permCongrHom (Fintype.equivFin α))

end Thorp.Specht

namespace Thorp.Fourier
open scoped Classical
variable {G : Type} [Group G] [Fintype G]

def realConv (μ ν : G → ℝ) (g : G) : ℝ := ∑ h, μ h * ν (h⁻¹ * g)

def realPower (ν : G → ℝ) : ℕ → G → ℝ
  | 0 => fun g => if g = 1 then 1 else 0
  | k+1 => realConv ν (realPower ν k)

end Thorp.Fourier

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Trimming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY uΩ uI uG uH uA

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp

namespace Trim
open scoped Classical

variable {X : Type uX} {Y : Type uY} [Fintype X] [Fintype Y]

def push (μ : X → ℝ) (f : X → Y) (y : Y) : ℝ := ∑ x, if f x = y then μ x else 0

variable {I : Type uI} [Fintype I]
variable {G : Type uG} {H : Type uH} [Group G] [Fintype G] [Group H] [Fintype H]

def cosetMass (ψ : (I → H) →* G) (μ : G → ℝ) (i : I) (g : G) : ℝ :=
  ∑ h, μ (g * ψ (Pi.mulSingle i h))

def good (ψ : (I → H) →* G) (μ : G → ℝ) (g : G) : Prop :=
  ∀ i, cosetMass ψ μ i g ≤ 2 * ((Fintype.card H : ℝ) / Fintype.card G)

def discarded (ψ : (I → H) →* G) (μ : G → ℝ) : ℝ :=
  ∑ g, if good ψ μ g then 0 else μ g

def kept (ψ : (I → H) →* G) (μ : G → ℝ) (g : G) : ℝ :=
  if good ψ μ g then μ g else 0

def normalized (ψ : (I → H) →* G) (μ : G → ℝ) (g : G) : ℝ :=
  kept ψ μ g / (1 - discarded ψ μ)

end Trim

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_BlockEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uβ uα

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Block
open scoped Classical
variable {I : Type uI} {β : Type uβ} {α : Type uα}

attribute [-simp] Thorp.Specht.perm_apply_inv Thorp.Specht.perm_inv_apply in
def perm (p : I → Equiv.Perm β) : Equiv.Perm (I × β) where
  toFun x := (x.1, p x.1 x.2)
  invFun x := (x.1, (p x.1)⁻¹ x.2)
  left_inv x := by simp
  right_inv x := by simp

def hom : (I → Equiv.Perm β) →* Equiv.Perm (I × β) where
  toFun := perm
  map_one' := by ext ⟨i,b⟩ <;> rfl
  map_mul' p q := by ext ⟨i,b⟩ <;> rfl

def embedding (e : α ≃ I × β) : (I → Equiv.Perm β) →* Equiv.Perm α :=
  (e.symm.permCongrHom).toMonoidHom.comp hom

def complement (i : I) := {j : I // j ≠ i} × β

instance instFintypeComplement [Fintype I] [Fintype β] (i : I) : Fintype (complement (β:=β) i) :=
  inferInstanceAs (Fintype ({j : I // j ≠ i} × β))

lemma card_complement [Fintype I] [Fintype β] (i : I) :
    Fintype.card (complement (β:=β) i) = (Fintype.card I - 1) * Fintype.card β := by
  change Fintype.card ({j : I // j ≠ i} × β) = _
  rw [Fintype.card_prod, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

def complementIn (e : α ≃ I × β) (i : I) (x : complement (β:=β) i) : α :=
  e.symm (x.1.val, x.2)

def restriction (e : α ≃ I × β) (i : I) (g : Equiv.Perm α) : complement (β:=β) i → α :=
  g ∘ complementIn e i

lemma perm_single_apply (i j : I) (h : Equiv.Perm β) (b : β) :
    perm (Pi.mulSingle i h) (j,b) = if j = i then (j,h b) else (j,b) := by
  by_cases hj : j = i
  · subst j; simp [perm]
  · simp [perm, hj]

lemma embedding_apply (e : α ≃ I × β) (p : I → Equiv.Perm β) (x : α) :
    embedding e p x = e.symm (perm p (e x)) := rfl

lemma restriction_right (e : α ≃ I × β) (i : I) (g : Equiv.Perm α) (h : Equiv.Perm β) :
    restriction e i (g * embedding e (Pi.mulSingle i h)) = restriction e i g := by
  funext x
  simp only [restriction, Function.comp_apply, Equiv.Perm.coe_mul, embedding_apply,
    complementIn, e.apply_symm_apply, perm_single_apply, x.1.property, ↓reduceIte]

lemma fixes_inside (i : I) (r : Equiv.Perm (I × β))
    (hr : ∀ j b, j ≠ i → r (j,b) = (j,b)) (b : β) : (r (i,b)).1 = i := by
  by_contra h
  have hh := hr (r (i,b)).1 (r (i,b)).2 h
  have he : (i,b) = r (i,b) := r.injective (by simpa only [Prod.mk.eta] using hh.symm)
  exact h (congrArg Prod.fst he).symm

lemma fixes_outside_inv (i : I) (r : Equiv.Perm (I × β))
    (hr : ∀ j b, j ≠ i → r (j,b) = (j,b)) (j : I) (b : β) (hj : j ≠ i) :
    r⁻¹ (j,b) = (j,b) := by
  apply r.injective
  simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using (hr j b hj).symm

def extract (i : I) (r : Equiv.Perm (I × β))
    (hr : ∀ j b, j ≠ i → r (j,b) = (j,b)) : Equiv.Perm β where
  toFun b := (r (i,b)).2
  invFun b := (r⁻¹ (i,b)).2
  left_inv b := by
    have he : (i, (r (i,b)).2) = r (i,b) := Prod.ext (fixes_inside i r hr b).symm rfl
    change (r⁻¹ (i, (r (i,b)).2)).2 = b
    rw [he, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  right_inv b := by
    have he : (i, (r⁻¹ (i,b)).2) = r⁻¹ (i,b) :=
      Prod.ext (fixes_inside i r⁻¹ (fixes_outside_inv i r hr) b).symm rfl
    change (r (i, (r⁻¹ (i,b)).2)).2 = b
    rw [he, Equiv.Perm.inv_def, Equiv.apply_symm_apply]

lemma perm_extract (i : I) (r : Equiv.Perm (I × β))
    (hr : ∀ j b, j ≠ i → r (j,b) = (j,b)) : perm (Pi.mulSingle i (extract i r hr)) = r := by
  apply Equiv.ext
  rintro ⟨j,b⟩
  rw [perm_single_apply]
  by_cases hj : j = i
  · subst j
    simp only [↓reduceIte]
    exact Prod.ext (fixes_inside i r hr b).symm rfl
  · rw [ite_eq_right hj, hr j b hj]

lemma restriction_fiber (e : α ≃ I × β) (i : I) (g k : Equiv.Perm α)
    (hk : restriction e i k = restriction e i g) :
    ∃ h : Equiv.Perm β, g * embedding e (Pi.mulSingle i h) = k := by
  let r : Equiv.Perm (I × β) := e.permCongr (g⁻¹ * k)
  have hr (j : I) (b : β) (hj : j ≠ i) : r (j,b) = (j,b) := by
    have hh := congrFun hk (⟨j,hj⟩,b)
    change k (e.symm (j,b)) = g (e.symm (j,b)) at hh
    change e (g⁻¹ (k (e.symm (j,b)))) = (j,b)
    rw [hh, Equiv.Perm.inv_def, Equiv.symm_apply_apply, e.apply_symm_apply]
  refine ⟨extract i r hr, ?_⟩
  apply mul_left_cancel (a:=g⁻¹)
  rw [← mul_assoc, inv_mul_cancel, one_mul]
  have he := perm_extract i r hr
  apply (Equiv.permCongrHom e).injective
  change e.permCongr (e.symm.permCongr (perm (Pi.mulSingle i (extract i r hr)))) = r
  simpa only [← Equiv.permCongr_symm, Equiv.apply_symm_apply] using he

lemma single_embedding_injective (e : α ≃ I × β) (i : I) :
    Function.Injective (fun h : Equiv.Perm β => embedding e (Pi.mulSingle i h)) := by
  intro h k hh
  ext b
  have he := DFunLike.congr_fun hh (e.symm (i,b))
  simp only [embedding_apply, e.apply_symm_apply, perm_single_apply, ↓reduceIte] at he
  exact congrArg Prod.snd (e.symm.injective he)

end Thorp.Block

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_BlockFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uβ uα uK

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp

namespace Block
open scoped Classical
variable {I : Type uI} {β : Type uβ} {α : Type uα} [Fintype I] [Fintype β] [Fintype α] [DecidableEq α] [DecidableEq β]

def fiberEquiv (e : α ≃ I × β) (i : I) (g : Equiv.Perm α) :
    Equiv.Perm β ≃ {k : Equiv.Perm α // restriction e i k = restriction e i g} :=
  Equiv.ofBijective (fun h => ⟨g * embedding e (Pi.mulSingle i h), restriction_right e i g h⟩)
    ⟨fun h k hh => single_embedding_injective e i (mul_left_cancel (congrArg Subtype.val hh)),
      fun ⟨k,hk⟩ => by
        obtain ⟨h, hh⟩ := restriction_fiber e i g k hk
        exact ⟨h, Subtype.ext hh⟩⟩

variable {K : Type uK} [Fintype K]

def orderedRestriction (e : α ≃ I × β) (i : I) (o : K ≃ complement (β:=β) i) (g : Equiv.Perm α) : K → α :=
  restriction e i g ∘ o

end Block

namespace Block
open scoped Classical

def eightEquiv (d : ℕ) : Position (d+1+2) ≃ Fin 8 × Position d :=
  Fintype.equivOfCardEq (by simp only [card_position, Fintype.card_prod, Fintype.card_fin, pow_add]; norm_num; omega)

lemma complement_card (d : ℕ) (i : Fin 8) :
    Fintype.card (complement (β:=Position d) i) = 7 * 2^d := by
  rw [card_complement, Fintype.card_fin, card_position]

def ordering (d : ℕ) (i : Fin 8) : Fin (7 * 2^d) ≃ complement (β:=Position d) i :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, complement_card])

def domain (d : ℕ) (i : Fin 8) : Fin (7*2^d) → Position (d+1+2) :=
  complementIn (eightEquiv d) i ∘ ordering d i

def discarded (d : ℕ) : ℝ :=
  Trim.discarded (embedding (eightEquiv d)) (law (d+1+2) (200*(d+1+2)))

end Block

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_EightBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp
open scoped Classical

namespace Block
open Thorp.Fourier Thorp.Specht

def fullRate (d : ℕ) : ℝ :=
  8 * discarded d + (1/2 : ℝ) * Real.sqrt
    (2 * (2 * discarded d)^16 + (96 : ℝ)^8 * exceptionalReciprocalSum (2^(d+1+2)))

end Block
end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_FixedLists_Asymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped BigOperators
open Filter
namespace Thorp.FixedLists

def energyEnvelope (C d : ℕ) : ℝ :=
  (63 / 64 : ℝ) ^ (C * (d + 4)) + 64 * (9 / 10 : ℝ) ^ (2 ^ d)

def listRate (d : ℕ) : ℝ :=
  Real.sqrt (((2 : ℝ) ^ (d + 4)) ^ 3 * energyEnvelope 254 d)

end Thorp.FixedLists

end

end OAI
end


