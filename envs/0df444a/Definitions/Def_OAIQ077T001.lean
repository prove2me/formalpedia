-- Prove2me | Definitions.Def_OAIQ077T001
-- name    : OAIQ077T001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:50:41.706357+00:00
-- url     : https://prove2.me/theorems/8f1543bd-9212-46a2-933a-2be0d0876494
-- title:
--   Definitions bundle OAIQ077T001 of the split of OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ThorpNine.main`, carved from OpenAI's openai/math development (OpenAI, *Optimal logarithmic mixing of the Thorp shuffle (routing densities)*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1175 declarations of OpenAI's Lean: 729 definitions, 10 inductive types or structures, 41 instances and 395 theorems. The definitions and types are `OAI.ThorpNine.Casimir.Thorp.collectionWeight`, `OAI.ThorpNine.Casimir.Thorp.crowdedMass`, `OAI.ThorpNine.Casimir.Thorp.cycleCoefficient`, `OAI.ThorpNine.Casimir.Thorp.cycleTrace`, `OAI.ThorpNine.Casimir.Thorp.densityConstant`, `OAI.ThorpNine.Casimir.Thorp.densityCutoff`, `OAI.ThorpNine.Casimir.Thorp.densityTailConstant`, `OAI.ThorpNine.Casimir.Thorp.distance`, `OAI.ThorpNine.Casimir.Thorp.familyEnd`, `OAI.ThorpNine.Casimir.Thorp.heightDecay`, `OAI.ThorpNine.Casimir.Thorp.inclusionMoment`, `OAI.ThorpNine.Casimir.Thorp.modifiedAssembleEquiv`, `OAI.ThorpNine.Casimir.Thorp.modifiedOverhead`, `OAI.ThorpNine.Casimir.Thorp.momentBase`, `OAI.ThorpNine.Casimir.Thorp.pairAssembleEquiv`, `OAI.ThorpNine.Casimir.Thorp.pairFiber`, `OAI.ThorpNine.Casimir.Thorp.parallelPerm`, `OAI.ThorpNine.Casimir.Thorp.parallelUsers`, `OAI.ThorpNine.Casimir.Thorp.permDistance`, `OAI.ThorpNine.Casimir.Thorp.relabeledPerm`, `OAI.ThorpNine.Casimir.Thorp.rotationLower`, `OAI.ThorpNine.Casimir.Thorp.seedSandwichShuffle`, `OAI.ThorpNine.Casimir.Thorp.sparseCoefficient`, `OAI.ThorpNine.Casimir.Thorp.sparseMass`, `OAI.ThorpNine.Casimir.Thorp.switchUsers`, `OAI.ThorpNine.Casimir.Thorp.walkSet`, `OAI.ThorpNine.Contact.Thorp.CylinderBound`, `OAI.ThorpNine.Contact.Thorp.DensityTransfer.applyKernel`, `OAI.ThorpNine.Contact.Thorp.PermutationHilbert.act`, `OAI.ThorpNine.Contact.Thorp.QueryTree.flipCoin`, `OAI.ThorpNine.Contact.Thorp.SparseContact.ContactEvent`, `OAI.ThorpNine.Contact.Thorp.SparseContact.Harmonic`, `OAI.ThorpNine.Contact.Thorp.SparseContact.NoIsolated`, `OAI.ThorpNine.Contact.Thorp.SparseContact.contactConstant`, `OAI.ThorpNine.Contact.Thorp.SparseContact.endpointProb`, `OAI.ThorpNine.Contact.Thorp.SparseContact.fiber`, `OAI.ThorpNine.Contact.Thorp.SparseContact.labelsOf`, `OAI.ThorpNine.Contact.Thorp.SparseContact.mixedInitial`, `OAI.ThorpNine.Contact.Thorp.SparseContact.mixedReturn`, `OAI.ThorpNine.Contact.Thorp.SparseContact.mixedTuple` and 699 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `ThorpRouting_Casimir_CutoffMass`, `ThorpRouting_Casimir_Distance`, `ThorpRouting_Casimir_ExposedCoins`, `ThorpRouting_Casimir_InputTree`, `ThorpRouting_Casimir_ModifiedRoutingMoment`, `ThorpRouting_Casimir_PairAssembleEquiv`, `ThorpRouting_Casimir_PalindromeFamilyCost`, `ThorpRouting_Casimir_ParallelFollow`, `ThorpRouting_Casimir_PriorPaths`, `ThorpRouting_Casimir_RotationMeeting`, `ThorpRouting_Casimir_SandwichShuffle`, `ThorpRouting_Contact_Coins`, `ThorpRouting_Contact_ExposedCoins`, `ThorpRouting_Contact_Main`, `ThorpRouting_Contact_ModifiedReverseEquiv`, `ThorpRouting_Contact_ModifiedRoutingMoment`, `ThorpRouting_Contact_ModifiedStageEquiv`, `ThorpRouting_Contact_ParallelFollow`, `ThorpRouting_Contact_Representative`, `ThorpRouting_Contact_ShapePartitionEquiv`, `ThorpRouting_Dense_AssignmentSlots`, `ThorpRouting_Dense_Coins`, `ThorpRouting_Dense_ColoredEmbedding`, `ThorpRouting_Dense_CutoffMass`, `ThorpRouting_Dense_ExposedCoins`, `ThorpRouting_Dense_Main`, `ThorpRouting_Dense_PalindromeFamilyCost`, `ThorpRouting_Dense_ParallelFollow`, `ThorpRouting_Dense_PriorPaths`, `ThorpRouting_Dense_ProjectCycle`, `ThorpRouting_Dense_RotationCharge`, `ThorpRouting_Dense_SingleSlotsEquiv`, `ThorpRouting_Harmonic_AlternatingPerm`, `ThorpRouting_Harmonic_AssignmentSlots`, `ThorpRouting_Harmonic_AverageMap`, `ThorpRouting_Harmonic_BlockProduct`, `ThorpRouting_Harmonic_Coins`, `ThorpRouting_Harmonic_CutoffMass`, `ThorpRouting_Harmonic_ExposedCoins`, `ThorpRouting_Harmonic_InputTree`, `ThorpRouting_Harmonic_ModifiedReverseCoins`, `ThorpRouting_Harmonic_ModifiedRoutingMoment`, `ThorpRouting_Harmonic_PairAssembleEquiv`, `ThorpRouting_Harmonic_PalindromeFamilyCost`, `ThorpRouting_Harmonic_ParallelFollow`, `ThorpRouting_Harmonic_PriorPaths`, `ThorpRouting_Harmonic_RotationMeeting`, `ThorpRouting_Harmonic_SandwichShuffle`, `ThorpRouting_Harmonic_Shapes`, `ThorpRouting_Harmonic_Site`, `ThorpRouting_Harmonic_TailShapes`, `ThorpRouting_Harmonic_ZeroExtend`, `ThorpRouting_HighTail_AssignmentSlots`, `ThorpRouting_HighTail_Coins`, `ThorpRouting_HighTail_ColoredEmbedding`, `ThorpRouting_HighTail_CutoffMass`, `ThorpRouting_HighTail_ExposedCoins`, `ThorpRouting_HighTail_Main`, `ThorpRouting_HighTail_ParallelFollow`, `ThorpRouting_HighTail_PriorPaths`, `ThorpRouting_HighTail_ProjectCycle`, `ThorpRouting_HighTail_RotationMeeting`, `ThorpRouting_Smoothing_AlternatingPerm`, `ThorpRouting_Smoothing_AssignmentSlots`, `ThorpRouting_Smoothing_BenesCoins`, `ThorpRouting_Smoothing_Coins`, `ThorpRouting_Smoothing_ExposedCoins`, `ThorpRouting_Smoothing_Main`, `ThorpRouting_Smoothing_ParallelFollow`, `ThorpRouting_Smoothing_ParallelFreshPre`, `ThorpRouting_Smoothing_PriorPaths`, `ThorpRouting_Smoothing_RotationCharge`, `ThorpRouting_SparseSaving_Coins`, `ThorpRouting_SparseSaving_Main`, `ThorpRouting_SparseSaving_ModifiedReverseEquiv`, `ThorpRouting_SparseSaving_ModifiedRoutingMoment`, `ThorpRouting_SparseSaving_ModifiedStageEquiv`, `ThorpRouting_SparseSaving_ParallelFollow`, `ThorpRouting_SparseSaving_Representative`, `ThorpRouting_SparseSaving_ShapePartitionEquiv`, `ThorpRouting_Tail_BenesCoins`.
--
--   **Imports.** It imports the published bundle `Def_ThorpRouting`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ077T003`; the statements `OAI_ThorpNine_Casimir_Thorp_CasimirBounds_trace_bound`, `OAI.ThorpNine.Casimir.Thorp.CasimirBounds.trace_bound_q77`, `OAI_ThorpNine_Contact_Thorp_SparseContact_sample_sweep_bound`, `OAI.ThorpNine.Contact.Thorp.SparseContact.sample_sweep_bound_q77`, `OAI_ThorpNine_Harmonic_Thorp_Specht_near_row_amplification` and `OAI.ThorpNine.Harmonic.Thorp.Specht.near_row_amplification_q77`; the proofs of `OAI_ThorpNine_Contact_Thorp_SparseContact_sample_sweep_bound`, `OAI.ThorpNine.Contact.Thorp.SparseContact.sample_sweep_bound_q77`, `OAI_ThorpNine_Contact_Thorp_SparseContact_uniform_sparse_contact`, `OAI.ThorpNine.Contact.Thorp.SparseContact.uniform_sparse_contact_q77`, `OAI_ThorpNine_Harmonic_Thorp_Casimir_eventual_level_contraction`, `OAI.ThorpNine.Harmonic.Thorp.Casimir.eventual_level_contraction_q77`, `OAI_ThorpNine_Harmonic_Thorp_Specht_spectral_regimes` and `OAI.ThorpNine.Harmonic.Thorp.Specht.spectral_regimes_q77`.
-- source:
--   OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Routing-densities-and-representation-contraction-for-Thorp-sweeps-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_ThorpRouting

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_Distance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp

open scoped BigOperators
open Filter

instance instNonemptyCoins (d : ℕ) : Nonempty (Coins d) := by
  cases d <;> dsimp [Coins] <;> infer_instance

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

noncomputable def inclusionMoment {α Ω : Type*} [Fintype Ω]
    (F : Ω → Finset α) (s : Finset α) : ℝ := by
  classical
  exact finiteMean (fun ω => if s ⊆ F ω then 1 else 0)

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_ExposedCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp
open scoped BigOperators
open Filter

lemma xor_eq_iff (a b c : Bool) : Bool.xor a b = c ↔ b = Bool.xor a c := by
  cases a <;> cases b <;> cases c <;> decide

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

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_RotationMeeting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp
open scoped BigOperators
open Filter

section OrbitCore
variable {α : Type*} [Fintype α] [DecidableEq α]

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

section Collections
variable {d A : ℕ}

noncomputable def rotationLower (d : ℕ) {A : ℕ} (r : Fin A → ℕ) : ℝ :=
  Real.exp (-Real.log 2 * ((A:ℝ)*d/2 + ∑ i : Fin A, Real.log (r i+1) / (2 * Real.log 2)))

noncomputable def collectionWeight (d : ℕ) {A : ℕ} (r : Fin A → ℕ) : ℝ :=
  ((2:ℝ)^d)^A * (∏ i : Fin A, (r i+1 : ℝ)) * rotationLower d r

end Collections

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_PriorPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp
open scoped BigOperators
open Filter

variable {α B : Type*} [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] {d : ℕ}

def parallelPerm (ω : B × SwitchIndex d → Bool) : Equiv.Perm (B × Card d) where
  toFun x := (x.1,butterflyPerm d (decodeButterfly d (fun i => ω (x.1,i))) x.2)
  invFun y := (y.1,(butterflyPerm d (decodeButterfly d (fun i => ω (y.1,i)))).symm y.2)
  left_inv x := by simp
  right_inv y := by simp

def relabeledPerm (pre : α ≃ B × Card d) (post : B × Card d ≃ α)
    (ω : B × SwitchIndex d → Bool) : Equiv.Perm α :=
  (pre.trans (parallelPerm ω)).trans post

def parallelUsers (pre : α ≃ B × Card d) (ω : B × SwitchIndex d → Bool)
    (i : B × SwitchIndex d) : α × α :=
  let u := switchUsers d (decodeButterfly d (fun j => ω (i.1,j))) i.2
  (pre.symm (i.1,u.1),pre.symm (i.1,u.2))

omit [Fintype α] [DecidableEq α] [Fintype B] [DecidableEq B] in
lemma parallelUsers_ne (pre : α ≃ B × Card d) (ω : B × SwitchIndex d → Bool)
    (i : B × SwitchIndex d) : (parallelUsers pre ω i).1 ≠ (parallelUsers pre ω i).2 := by
  intro h
  exact switchUsers_ne d _ _ (congrArg Prod.snd (pre.symm.injective h))

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_ParallelFollow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp
open scoped BigOperators
open Filter

section ParallelFairLayer
variable {β : Type*} [Fintype β] [DecidableEq β]

noncomputable def pairFiber (S : Finset (Bool × β)) (b : β) : Finset Bool :=
  Finset.univ.filter (fun ε => (ε,b) ∈ S)

end ParallelFairLayer

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_SandwichShuffle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp


noncomputable def sparseCoefficient {α : Type*} (w : ℝ) (T : Finset α) : ℝ :=
  if T.card = 1 then 0 else w^T.card


noncomputable def sparseMass {α β : Type*} [DecidableEq α] [Fintype β]
    (D : β → Finset α) (A : Finset α) : ℕ :=
  ∑ b, if 2 ≤ (D b ∩ A).card then (D b ∩ A).card else 0


def crowdedMass (h : ℕ) : ℕ := if 2 ≤ h then h else 0

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_CutoffMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp

noncomputable def cycleCoefficient (r J : ℕ) (q : ℝ) : ℝ :=
  Real.log q / J + 2*q*Real.sqrt J/Real.sqrt ((2:ℝ)^r)

def familyEnd (L n : ℕ) : ℕ := if n = 0 then 0 else 2*(L*4^(n-1))

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_PalindromeFamilyCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp


noncomputable def heightDecay (H : ℕ) : ℝ :=
  68*Real.exp (-(H:ℝ)/64)/(1-Real.exp (-(1:ℝ)/64))

noncomputable def momentBase : ℝ := (2:ℝ)^(1/1000:ℝ)


noncomputable def densityCutoff (p : ℝ) : ℕ := ⌊-Real.log p/(4*Real.log 2)⌋₊

noncomputable def densityTailConstant : ℝ :=
  68*Real.exp (1/64)/(1-Real.exp (-(1:ℝ)/64))

noncomputable def densityConstant : ℝ :=
  256*(1+heightDecay 1)+1+densityTailConstant

variable {α : Type*} [Fintype α] [DecidableEq α]


noncomputable def permDistance (p q : Equiv.Perm α) : ℕ :=
  (Finset.univ.filter (fun x => p x ≠ q x)).card

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_InputTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp

def seedSandwichShuffle {A B C D E : Type*} :
    (A × B) × ((C × D) × E) ≃ ((A × C) × (B × D)) × E where
  toFun x := (((x.1.1,x.2.1.1),(x.1.2,x.2.1.2)),x.2.2)
  invFun x := ((x.1.1.1,x.1.2.1),((x.1.1.2,x.1.2.2),x.2))
  left_inv _ := rfl
  right_inv _ := rfl

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_ModifiedRoutingMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp

noncomputable def modifiedOverhead (L r : ℕ) : ℝ :=
  (((L+r:ℕ):ℝ)*Real.log 2+1)/((2:ℝ)^(L+r)*1000)

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Casimir_PairAssembleEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp
open scoped BigOperators Classical

def pairAssembleEquiv (B C H : Type*) :
    ((H × (B → C × C)) × H) ≃ (((B → C) × H) × ((B → C) × H)) where
  toFun w := (((fun b => (w.1.2 b).1),w.1.1),((fun b => (w.1.2 b).2),w.2))
  invFun w := ((w.1.2,fun b => (w.1.1 b,w.2.1 b)),w.2.2)
  left_inv _w := rfl
  right_inv _w := rfl

def modifiedAssembleEquiv (B C H U : Type*) :
    ((H × (B → U × (C × C))) × H) ≃ (B → U) × (((B → C) × H) × ((B → C) × H)) where
  toFun w := ((fun b => (w.1.2 b).1),
    (((fun b => (w.1.2 b).2.1),w.1.1),((fun b => (w.1.2 b).2.2),w.2)))
  invFun w := ((w.2.1.2,fun b => (w.1 b,(w.2.1.1 b,w.2.2.1 b))),w.2.2.2)
  left_inv _w := rfl
  right_inv _w := rfl

end Thorp

end ThorpNine.Casimir

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Contact_Coins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

namespace Thorp

open scoped BigOperators
open Filter

noncomputable def childMarks {d : ℕ} (s : Finset (Card (d + 1))) (ε : Bool) :
    Finset (Card d) := (s.filter (fun x => x 0 = ε)).image Fin.tail

def CylinderBound {α : Type*} (m : Finset α → ℝ) (p : α → ℝ) : Prop :=
  ∀ s, m s ≤ ∏ i ∈ s, p i

noncomputable def finiteMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

noncomputable def inclusionMoment {α Ω : Type*} [Fintype Ω]
    (F : Ω → Finset α) (s : Finset α) : ℝ := by
  classical
  exact finiteMean (fun ω => if s ⊆ F ω then 1 else 0)

namespace QueryTree

variable {ι : Type*} [DecidableEq ι]

def flipCoin (i : ι) : Equiv.Perm (ι → Bool) :=
  (show Function.Involutive (fun ω : ι → Bool => Function.update ω i (!(ω i))) from by
    intro ω
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [Function.update_of_ne h]).toPerm

end QueryTree

def encodeButterfly : (d : ℕ) → Butterfly d → SwitchIndex d → Bool
  | 0, _, i => nomatch i
  | _d + 1, b, Sum.inl y => b.1 y
  | d + 1, b, Sum.inr (ε,i) => encodeButterfly d (b.2 ε) i

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

end ThorpNine.Contact

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Contact_ExposedCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

namespace Thorp
open scoped BigOperators
open Filter

def switchUsers : (d : ℕ) → Butterfly d → SwitchIndex d → Card d × Card d
  | 0, _, i => nomatch i
  | d + 1, b, Sum.inl y =>
      (Fin.cons false ((butterflyPerm d (b.2 false)).symm y),
       Fin.cons true ((butterflyPerm d (b.2 true)).symm y))
  | d + 1, b, Sum.inr (ε,i) =>
      (Fin.cons ε (switchUsers d (b.2 ε) i).1,
       Fin.cons ε (switchUsers d (b.2 ε) i).2)

end Thorp

end ThorpNine.Contact

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Contact_ParallelFollow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

namespace Thorp
open scoped BigOperators
open Filter

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

noncomputable def fairSetLayer {Ω : Type*} (F : Ω → Finset (Bool × β)) :
    Ω × (β → Bool) → Finset (Bool × β) := fun ω => (F ω.1).image (pairLayer ω.2)

end ParallelFairLayer

section JoinChildren
variable {β : Type*} [DecidableEq β]

noncomputable def childJoin (A B : Finset β) : Finset (Bool × β) :=
  A.image (fun x => (false,x)) ∪ B.image (fun x => (true,x))

noncomputable def boolFiber (S : Finset (Bool × β)) (b : Bool) : Finset β :=
  (S.filter (fun x => x.1 = b)).image Prod.snd

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

noncomputable def butterflyMarks (d : ℕ) (A : Finset (Card d))
    (ω : SwitchIndex d → Bool) : Finset (Card d) :=
  A.image (butterflyPerm d (decodeButterfly d ω))

end Thorp

end ThorpNine.Contact

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Contact_ModifiedRoutingMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

namespace Thorp


namespace DensityTransfer
open scoped BigOperators

noncomputable def applyKernel {X : Type*} [Fintype X] (P : X → X → ℝ)
    (v : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => ∑ y, (P x y : ℂ)*v y)

end DensityTransfer

end Thorp

end ThorpNine.Contact

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Contact_ModifiedReverseEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

namespace Thorp.Specht
open scoped BigOperators Classical

@[simp] lemma card_cell (μ : YoungDiagram) : Fintype.card (Cell μ) = μ.card := by
  simp [Cell, YoungDiagram.card]

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

end Thorp.Specht

end ThorpNine.Contact

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Contact_ShapePartitionEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

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

noncomputable def colIndex {μ : YoungDiagram} (x : Cell μ) : Fin (μ.rowLen 0) :=
  ⟨col x, (YoungDiagram.mem_iff_lt_rowLen.mp x.2).trans_le (μ.rowLen_anti 0 (row x) (Nat.zero_le _))⟩

noncomputable instance tabloidMulAction (μ : YoungDiagram) : MulAction (Equiv.Perm (Cell μ)) (Tabloid μ) where
  smul p f := tabloidAct p f
  one_smul f := by change tabloidAct 1 f = f; rw [tabloidAct_one]; rfl
  mul_smul p q f := by change tabloidAct (p*q) f = tabloidAct p (tabloidAct q f); rw [tabloidAct_mul]; rfl

abbrev Tail (μ : YoungDiagram) := {x : Cell μ // row x ≠ 0}

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

end Thorp.UnitaryFinite

end ThorpNine.Contact

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Contact_Representative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G X : Type*} [Group G] [Fintype G] [Fintype X]
  (a : G →* Equiv.Perm X) (x₀ : X) (ha : ∀ x, ∃ g, a g x₀=x)

noncomputable def representative (x : X) : G := Classical.choose (ha x)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

def IsFixed (w : V) : Prop := ∀ g, a g x₀=x₀ → ρ g w=w

noncomputable def coefficient (w v : V) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => inner ℂ (ρ (representative a x₀ ha x) w) v)

noncomputable def normalizedCoefficient (w v : V) : EuclideanSpace ℂ X :=
  (Real.sqrt ((Module.finrank ℂ V:ℝ)/(Fintype.card X:ℝ)) : ℂ) • coefficient a x₀ ha ρ w v

end Thorp.UnitaryFinite

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

end
open scoped BigOperators Classical

end Thorp.UnitaryFinite
namespace Thorp
open scoped BigOperators Classical

variable {Ω G : Type*} [Fintype Ω] [Fintype G]

noncomputable def sampleLaw (P : Ω → G) (g : G) : ℝ :=
  finiteMean (fun ω => if P ω=g then 1 else 0)

end Thorp

end ThorpNine.Contact

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Contact_ModifiedStageEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

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
lemma tupleAction_transitive (e f : ι ↪ α) : ∃ p, tupleAction p e=f := by
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair e f e.injective f.injective
  exact ⟨p,Function.Embedding.ext hp⟩

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

noncomputable def neighborhood {V : Type*} [Fintype V] (G : SimpleGraph V)
    (R : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => ∃ v ∈ R, G.Adj v w)

def NoIsolated {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ v ∈ S, ∃ w ∈ S, G.Adj v w

noncomputable def typedSet {N X : Type*} [Fintype N] [Fintype X]
    (A : N → Finset X) : Finset (N × X) := by
  classical
  exact Finset.univ.filter (fun v => v.2 ∈ A v.1)

@[simp] lemma mem_typedSet {N X : Type*} [Fintype N] [Fintype X]
    (A : N → Finset X) (v : N × X) : v ∈ typedSet A ↔ v.2 ∈ A v.1 := by
  classical
  simp [typedSet]

noncomputable def fiber {N X : Type*} [Fintype X]
    (S : Finset (N × X)) (t : N) : Finset X := by
  classical
  exact Finset.univ.filter (fun x => (t,x) ∈ S)

@[simp] lemma mem_fiber {N X : Type*} [Fintype X]
    (S : Finset (N × X)) (t : N) (x : X) : x ∈ fiber S t ↔ (t,x) ∈ S := by
  classical
  simp [fiber]

end Thorp.SparseContact

end ThorpNine.Contact

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Contact_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Contact

namespace Thorp.SparseContact
open scoped BigOperators Classical

noncomputable def typedMarks {N : Type*} [Fintype N] (d : ℕ)
    (A : N → Finset (Card d)) (ω : N → (SwitchIndex d → Bool)) : Finset (N × Card d) :=
  typedSet (fun t => butterflyMarks d (A t) (ω t))

noncomputable def returnRoute {N : Type*} (d : ℕ) (b : N → Butterfly d)
    (v : N × Card d) : Finset (SwitchIndex d) :=
  routeDomain d ((butterflyPerm d (b v.1)).symm v.2) v.2

noncomputable def returnGraph {N : Type*} (d : ℕ) (b : N → Butterfly d) :
    SimpleGraph (N × Card d) where
  Adj v w := v ≠ w ∧ ¬Disjoint (returnRoute d b v) (returnRoute d b w)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hh => h.2 hh.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable def endpointProb {L : Type*} (d : ℕ) (A : Finset L)
    (x y : L → Card d) : ℝ := by
  classical
  exact finiteMean (fun ω : SwitchIndex d → Bool =>
    if ∀ i ∈ A, butterflyPerm d (decodeButterfly d ω) (x i) = y i then (1:ℝ) else 0)

noncomputable def partialKernel {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x y : L → Card d) : ℝ :=
  ((2:ℝ)^d)^A.card / ((2:ℝ)^d)^(Fintype.card L) * endpointProb d A x y

def ContactEvent {L : Type*} (d : ℕ) (x y : L → Card d) : Prop :=
  ∀ i, ∃ j, i ≠ j ∧ ¬Disjoint (routeDomain d (x i) (y i)) (routeDomain d (x j) (y j))


noncomputable def networkOf {L : Type*} (A : Finset L) (i : L) : Option L := by
  classical
  exact if i ∈ A then none else some i

noncomputable def mixedTuple {L : Type*} (d : ℕ) (A : Finset L)
    (ω : Option L → (SwitchIndex d → Bool)) (x : L → Card d) : L → Card d :=
  fun i => butterflyPerm d (decodeButterfly d (ω (networkOf A i))) (x i)

noncomputable def mixedReturn {L : Type*} (d : ℕ) (A : Finset L)
    (ω : Option L → (SwitchIndex d → Bool)) (y : L → Card d) : L → Card d :=
  fun i => (butterflyPerm d (decodeButterfly d (ω (networkOf A i)))).symm (y i)

noncomputable def labelsOf {L : Type*} (A : Finset L) : Option L → Finset L := by
  classical
  exact fun t => match t with
    | none => A
    | some i => if i ∈ A then ∅ else {i}

noncomputable def mixedInitial {L : Type*} (d : ℕ) (A : Finset L)
    (x : L → Card d) (t : Option L) : Finset (Card d) := by
  classical
  exact (labelsOf A t).image x

noncomputable def retainedKernel {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x : L ↪ Card d) (y : L → Card d) : ℝ := by
  classical
  exact if ContactEvent d x y then partialKernel d A x y else 0

noncomputable def rectOperator {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Y → ℝ) : EuclideanSpace ℂ Y →L[ℂ] EuclideanSpace ℂ X :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun x => ∑ y, (P x y : ℂ)*v y)
      map_add' := by
        intro v w
        ext x
        simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        ext x
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
        change (∑ y, (P x y : ℂ)*(c*v y)) = c*∑ y, (P x y : ℂ)*v y
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring }

@[simp] lemma rectOperator_apply {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Y → ℝ) (v : EuclideanSpace ℂ Y) (x : X) :
    rectOperator P v x = ∑ y, (P x y:ℂ)*v y := rfl


noncomputable def pointStabilizer {α : Type*} (A : Finset α) : Subgroup (Equiv.Perm α) where
  carrier := {p | ∀ x ∈ A, p x = x}
  one_mem' := by intro x _; rfl
  mul_mem' := by intro p q hp hq x hx; change p (q x) = x; rw [hq x hx, hp x hx]
  inv_mem' := by intro p hp x hx; exact (Equiv.Perm.inv_eq_iff_eq).mpr (hp x hx).symm


section Orbit
variable {G X V : Type*} [Group G] [Fintype G] [Fintype X]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (a : G →* Equiv.Perm X) (x₀ : X) (ha : ∀ x, ∃ g, a g x₀ = x)
    (ρ : Representation ℂ G V) (w : V) (hw : UnitaryFinite.IsFixed a x₀ ρ w)

noncomputable def orbitVector (x : X) : V := ρ (UnitaryFinite.representative a x₀ ha x) w

end Orbit

def Harmonic {L α : Type*} [Fintype L] [Fintype α] (f : EuclideanSpace ℂ (L ↪ α)) : Prop :=
  ∀ (A : Finset L), A ≠ Finset.univ → ∀ z : L → α,
    (∑ y : L ↪ α, if ∀ i ∈ A, y i = z i then f y else 0) = 0

noncomputable def zeroExtend {L α : Type*} [Fintype L] [Fintype α]
    (f : EuclideanSpace ℂ (L ↪ α)) : EuclideanSpace ℂ (L → α) := by
  classical
  exact WithLp.toLp 2 (fun y => if h : Function.Injective y then f ⟨y,h⟩ else 0)

end Thorp.SparseContact

namespace Thorp.SparseContact

noncomputable def contactConstant : ℝ := 32 * Real.exp (2 * Real.exp 1)

end Thorp.SparseContact

end ThorpNine.Contact

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Dense_Coins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Dense

namespace Thorp

open scoped BigOperators
open Filter

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

end Thorp

end ThorpNine.Dense

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Dense_ExposedCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Dense

namespace Thorp
open scoped BigOperators
open Filter

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

end QueryTree

end Thorp

end ThorpNine.Dense

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Dense_RotationCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Dense

namespace Thorp
open scoped BigOperators
open Filter

section OrbitCore
variable {α : Type*} [Fintype α] [DecidableEq α]

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

end ThorpNine.Dense

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Dense_AssignmentSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Dense

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

end ThorpNine.Dense

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Dense_PriorPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Dense

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

section GroupedCounting
variable {A : ℕ}

abbrev CyclesOfLength (p : Equiv.Perm (α)) (S : Finset (α)) (j : ℕ) :=
  {C : SelectedCycle p S // C.val.card = j}

noncomputable instance instFintypeCyclesOfLength (p : Equiv.Perm (α)) (S : Finset (α)) (j : ℕ) :
    Fintype (CyclesOfLength p S j) := Fintype.ofFinite _

end GroupedCounting

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

end ThorpNine.Dense

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Dense_ParallelFollow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Dense

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

section ParallelFairLayer
variable {β : Type*} [Fintype β] [DecidableEq β]

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

end Thorp

end ThorpNine.Dense

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Dense_ProjectCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Dense

namespace Thorp
open scoped BigOperators
open Filter
namespace CycleColoring
variable {α : Type*} [Fintype α] [DecidableEq α]

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

lemma selected_alternating_eq (p : Equiv.Perm α) (A B : Finset α)
    (C : RoutingNetwork.SelectedCycle (alternatingPerm p) (childJoin A B)) :
    C.val = childJoin (projectCycle p A B C).val (projectCycle p A B C).val := by
  change C.val = childJoin (boolFiber C.val false) (boolFiber C.val false)
  obtain ⟨x,hx⟩ := C.property.1
  rw [hx,orbit_alternating,boolFiber_childJoin]
  rfl

end CycleColoring

noncomputable def headAverage {d : ℕ} (p : Card (d+1) → ℝ) (y : Card d) : ℝ :=
  (p (Fin.cons false y)+p (Fin.cons true y))/2

noncomputable def inverseButterflyMarks (d : ℕ) (A : Finset (Card d))
    (ω : SwitchIndex d → Bool) : Finset (Card d) :=
  A.image (butterflyPerm d (decodeButterfly d ω)).symm

namespace PairRouting

section
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

noncomputable instance instDecidableCompatible (x : ι → Bool × α) (c : ι → Bool) : Decidable (Compatible x c) :=
  Classical.propDecidable _

end

end PairRouting
end Thorp

end ThorpNine.Dense

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Dense_ColoredEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Dense

namespace Thorp


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

end ThorpNine.Dense

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Dense_CutoffMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Dense

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

end ThorpNine.Dense

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Dense_PalindromeFamilyCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Dense

namespace Thorp

noncomputable def palindromeFamilyCost (L n d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : ℕ :=
  ∑ j ∈ Finset.range n, palindromeSlabCost (L*4^j) d e ω


noncomputable def heightDecay (H : ℕ) : ℝ :=
  68*Real.exp (-(H:ℝ)/64)/(1-Real.exp (-(1:ℝ)/64))

end Thorp

open scoped BigOperators


end ThorpNine.Dense

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Dense_SingleSlotsEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Dense

open scoped BigOperators
namespace Thorp.RoutingNetwork
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def singleSlotsEquiv (p : Equiv.Perm α) (S : Finset α) (r : ℕ) :
    CycleSlots p S (fun _ : Fin 1 => r) ≃
      {C : SelectedCycle p S // C.val.card = r+1} :=
  (cycleSlotsEquivAssignments p S (fun _ : Fin 1 => r)).trans
  { toFun := fun a => ⟨a.val 0, a.property.2 0⟩
    invFun := fun C => ⟨fun _ => C.val, Function.injective_of_subsingleton _, fun _ => C.property⟩
    left_inv := fun a => by
      apply Subtype.ext
      funext i
      have hi : i=0 := Subsingleton.elim _ _
      subst i
      rfl
    right_inv := fun C => rfl }

noncomputable def cycleCount (p : Equiv.Perm α) (S : Finset α) (r : ℕ) : ℝ :=
  Fintype.card {C : SelectedCycle p S // C.val.card = r+1}

end Thorp.RoutingNetwork

namespace Thorp
open scoped BigOperators

def unitCardEquiv (d : ℕ) : Card d ≃ Unit × Card d where
  toFun x := ((),x)
  invFun x := x.2
  left_inv _ := rfl
  right_inv x := by cases x with | mk u x => cases u; rfl

def unitBitsEquiv (d : ℕ) : (Unit × SwitchIndex d → Bool) ≃ (SwitchIndex d → Bool) where
  toFun ω i := ω ((),i)
  invFun ω i := ω i.2
  left_inv ω := by funext i; rcases i with ⟨u,i⟩; cases u; rfl
  right_inv _ := rfl

namespace CycleColoring
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def projectSharedCycle (p : Equiv.Perm α) (A B : Finset α)
    (C : RoutingNetwork.SelectedCycle (alternatingPerm p) (childJoin A B)) :
    RoutingNetwork.SelectedCycle p (A ∩ B) := by
  refine ⟨(projectCycle p A B C).val, (projectCycle p A B C).property.1, ?_⟩
  intro x hx
  apply Finset.mem_inter.mpr
  refine ⟨(projectCycle p A B C).property.2 hx, ?_⟩
  have he := selected_alternating_eq p A B C
  have hc : (true,x) ∈ C.val := by
    rw [he]
    exact (mem_childJoin _ _ true x).mpr hx
  exact (mem_childJoin A B true x).mp (C.property.2 hc)

end CycleColoring

namespace PairRouting
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

noncomputable def sharedPairs (e : ι ↪ Bool × α) : Finset α :=
  boolFiber (labelSet e) false ∩ boolFiber (labelSet e) true

end PairRouting
end Thorp

namespace Thorp

noncomputable def sharedLevel (t : ℕ) : (d : ℕ) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card d) → (SwitchIndex d → Bool) → ℕ
  | 0, _, _, _, _ => 0
  | d+1, _, _, e, X =>
      let χ := coinStepEquiv d X
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x χ.2
      let hc := PairRouting.colors_compatible x χ.2
      if t = d+1 then (PairRouting.sharedPairs x).card else
        sharedLevel t d (PairRouting.childEmbedding x c hc false) χ.1.1 +
          sharedLevel t d (PairRouting.childEmbedding x c hc true) χ.1.2

noncomputable def denseLevelCoefficient (j : ℕ) (t : ℝ) : ℝ :=
  DenseTruncation.h (j+1) * ((Real.exp (t*(2:ℝ)^j)-1)/(2:ℝ)^j)


def pairCoords (r s : ℕ) : Card ((s+1)+r) ≃ Bool × (Card r × Card s) :=
  (cardSplit r (s+1)).trans
    { toFun := fun x => ((x.2) 0,(x.1,Fin.tail x.2))
      invFun := fun x => (x.2.1,Fin.cons x.1 x.2.2)
      left_inv := by intro x; simp only [Fin.cons_self_tail]
      right_inv := by intro x; simp only [Fin.cons_zero,Fin.tail_cons] }

noncomputable def gridPairs (r s : ℕ) (A : Finset (Card ((s+1)+r))) : Finset (Card r × Card s) :=
  Finset.univ.filter (fun x => (pairCoords r s).symm (false,x) ∈ A ∧
    (pairCoords r s).symm (true,x) ∈ A)

noncomputable def gridShared (r s : ℕ) (A : Finset (Card ((s+1)+r))) : ℕ :=
  (gridPairs r s A).card


noncomputable def suffixMarks (r s : ℕ) (A : Finset (Card (s+r))) (y : Card s) : Finset (Card r) :=
  blockMarks ((cardSplit r s).trans (Equiv.prodComm _ _)) A y

noncomputable def sharedPartnerMean (r s : ℕ) (A : Finset (Card ((s+1)+r))) : ℝ :=
  (∑ y : Card s, ((suffixMarks r (s+1) A (Fin.cons false y)).card : ℝ) *
    (suffixMarks r (s+1) A (Fin.cons true y)).card) / (2:ℝ)^r

def pairReorder (r s : ℕ) : Card (s+1) × Card r ≃ Bool × (Card r × Card s) where
  toFun x := (x.1 0,(x.2,Fin.tail x.1))
  invFun x := (Fin.cons x.1 x.2.2,x.2.1)
  left_inv x := by simp only [Fin.cons_self_tail]
  right_inv x := by simp only [Fin.cons_zero,Fin.tail_cons]

end Thorp

end ThorpNine.Dense

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Dense_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Dense

open scoped BigOperators
namespace Thorp

def PairSeparated {d : ℕ} (i : Fin d) (x y : Card d) : Prop :=
  x i = false ∧ y i = true ∧ ∀ j : Fin d, i < j → x j = y j


abbrev SeparatedPair {d : ℕ} (A : Finset (Card d)) (i : Fin d) :=
  {p : A × A // PairSeparated i p.1.val p.2.val}

noncomputable def separatedCount {d : ℕ} (A : Finset (Card d)) (i : Fin d) : ℕ := by
  classical
  exact Fintype.card (SeparatedPair A i)


noncomputable def partnerMean (d : ℕ) (A : Finset (Card d)) (j : ℕ) : ℝ :=
  if hj : j < d then (separatedCount A ⟨d-j-1,by omega⟩ : ℝ) / (2:ℝ)^(d-j-1) else 0

noncomputable def partnerAllocation (d : ℕ) (A : Finset (Card d)) (j : ℕ) : ℝ :=
  2*partnerMean d A j/A.card


open Filter Topology

end Thorp

namespace Thorp.DenseTruncation

noncomputable def unusedTail (d : ℕ) : ℝ :=
  (1/2:ℝ)*∑' j : ℕ, h (d+j+1)

end Thorp.DenseTruncation

namespace Thorp

noncomputable def augmentedAllocation (d : ℕ) (A : Finset (Card d)) (j : ℕ) : ℝ :=
  if j < d then partnerAllocation d A j else 1

end Thorp

open scoped BigOperators
namespace Thorp.DenseTruncation

noncomputable def stirlingRemainder (n : ℕ) : ℝ :=
  Real.log (n.factorial:ℝ) - n*Real.log n+n

end Thorp.DenseTruncation

end ThorpNine.Dense

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_Coins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp

open scoped BigOperators
open Filter

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
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_ExposedCoins
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
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_RotationMeeting
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
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_AssignmentSlots
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
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_PriorPaths
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
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_ParallelFollow
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

end CycleColoring
end Thorp

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_AlternatingPerm
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
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_SandwichShuffle
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
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_CutoffMass
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
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_PalindromeFamilyCost
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
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_InputTree
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
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_ModifiedRoutingMoment
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
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_ModifiedReverseCoins
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

@[simp] lemma card_cell (μ : YoungDiagram) : Fintype.card (Cell μ) = μ.card := by
  simp [Cell, YoungDiagram.card]

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

end Thorp.Specht

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_Shapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

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

end Thorp.UnitaryFinite

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_AverageMap
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

end Thorp.UnitaryFinite
namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G X : Type*} [Group G] [Fintype G] [Fintype X]
  (a : G →* Equiv.Perm X) (x₀ : X) (ha : ∀ x, ∃ g, a g x₀=x)

noncomputable def representative (x : X) : G := Classical.choose (ha x)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

def IsFixed (w : V) : Prop := ∀ g, a g x₀=x₀ → ρ g w=w

noncomputable def coefficient (w v : V) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => inner ℂ (ρ (representative a x₀ ha x) w) v)

noncomputable def normalizedCoefficient (w v : V) : EuclideanSpace ℂ X :=
  (Real.sqrt ((Module.finrank ℂ V:ℝ)/(Fintype.card X:ℝ)) : ℂ) • coefficient a x₀ ha ρ w v

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
    0 < sampleLaw P g ↔ ∃ ω,P ω=g := by
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
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_BlockProduct
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
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_PairAssembleEquiv
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
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_ZeroExtend
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
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_TailShapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

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

namespace Thorp.StrongSmoothing


open scoped BigOperators

variable {X : Type*} [Fintype X] [Nonempty X]

noncomputable def act (K : Matrix X X ℝ) (f : X → ℝ) (y : X) : ℝ := ∑ x, K x y*f x

variable [DecidableEq X]

noncomputable def rowDensity (K : Matrix X X ℝ) (r : ℕ) (x y : X) : ℝ :=
  (Fintype.card X:ℝ)*(K^r) x y

end Thorp.StrongSmoothing

namespace Thorp.StrongSmoothing.PermLaw
open scoped BigOperators
variable {X Ω Ω' : Type*} [Fintype X] [DecidableEq X] [Fintype Ω] [Fintype Ω']

noncomputable def kernel (P : Ω → Equiv.Perm X) : Matrix X X ℝ :=
  fun x y => finiteMean (fun ω => if P ω x = y then (1:ℝ) else 0)

end Thorp.StrongSmoothing.PermLaw

namespace Thorp.StrongSmoothing
open scoped BigOperators

section TupleAction
variable {ι β Ω : Type*} [Fintype Ω]

def tuplePerm (P : Equiv.Perm β) : Equiv.Perm (ι ↪ β) where
  toFun x := x.trans P.toEmbedding
  invFun x := x.trans P.symm.toEmbedding
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp

@[simp] lemma tuplePerm_apply (P : Equiv.Perm β) (x : ι ↪ β) (i : ι) :
    tuplePerm P x i = P (x i) := rfl

end TupleAction

end Thorp.StrongSmoothing

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Harmonic_Site
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.ButterflyReverse
open scoped BigOperators

abbrev Site (d : ℕ) := {t : Fin d × Card d // t.2 t.1 = false}

def site : (d : ℕ) → SwitchIndex d → Site d
  | 0, t => nomatch t
  | _+1, Sum.inl y => ⟨(0, Fin.cons false y), rfl⟩
  | d+1, Sum.inr (b,t) =>
      ⟨((site d t).1.1.succ, Fin.cons b (site d t).1.2), (site d t).2⟩

lemma site_injective (d : ℕ) : Function.Injective (site d) := by
  induction d with
  | zero => intro t; exact Empty.elim t
  | succ d ih =>
    intro s t h
    cases s with
    | inl y =>
      cases t with
      | inl z =>
        have he := congrArg (fun a : Site (d+1) => Fin.tail a.1.2) h
        exact congrArg Sum.inl he
      | inr t =>
        have he := congrArg (fun a : Site (d+1) => a.1.1.val) h
        simp [site] at he
    | inr s =>
      cases t with
      | inl y =>
        have he := congrArg (fun a : Site (d+1) => a.1.1.val) h
        simp [site] at he
      | inr t =>
        obtain ⟨b,s⟩ := s
        obtain ⟨c,t⟩ := t
        have hbc := congrArg (fun a : Site (d+1) => a.1.2 0) h
        simp only [site, Fin.cons_zero] at hbc
        have hst : site d s = site d t := by
          apply Subtype.ext
          apply Prod.ext
          · exact Fin.succ_inj.mp (congrArg (fun a : Site (d+1) => a.1.1) h)
          · exact congrArg (fun a : Site (d+1) => Fin.tail a.1.2) h
        cases hbc
        cases ih hst
        rfl

lemma site_surjective (d : ℕ) : Function.Surjective (site d) := by
  induction d with
  | zero => intro t; exact Fin.elim0 t.1.1
  | succ d ih =>
    rintro ⟨⟨i,x⟩,hx⟩
    refine Fin.cases ?_ (fun j => ?_) i hx
    · intro hx0
      refine ⟨Sum.inl (Fin.tail x), ?_⟩
      apply Subtype.ext
      simp only [site, Prod.mk.injEq, true_and]
      rw [←hx0,Fin.cons_self_tail]
    · intro hxj
      obtain ⟨t,ht⟩ := ih ⟨(j,Fin.tail x),hxj⟩
      refine ⟨Sum.inr (x 0,t), ?_⟩
      apply Subtype.ext
      simp only [site,ht,Fin.cons_self_tail]

noncomputable def siteEquiv (d : ℕ) : SwitchIndex d ≃ Site d :=
  Equiv.ofBijective (site d) ⟨site_injective d,site_surjective d⟩

def reverseCard (d : ℕ) : Equiv.Perm (Card d) where
  toFun x := fun i => x i.rev
  invFun x := fun i => x i.rev
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

@[simp] lemma reverseCard_apply (d : ℕ) (x : Card d) (i : Fin d) :
    reverseCard d x i = x i.rev := rfl

@[simp] lemma reverseCard_involutive (d : ℕ) (x : Card d) :
    reverseCard d (reverseCard d x) = x := by funext i; simp

def mirrorSite (d : ℕ) : Equiv.Perm (Site d) where
  toFun s := ⟨(s.1.1.rev,reverseCard d s.1.2),by simpa using s.2⟩
  invFun s := ⟨(s.1.1.rev,reverseCard d s.1.2),by simpa using s.2⟩
  left_inv s := by apply Subtype.ext; simp
  right_inv s := by apply Subtype.ext; simp

noncomputable def mirrorSwitch (d : ℕ) : Equiv.Perm (SwitchIndex d) :=
  (siteEquiv d).trans ((mirrorSite d).trans (siteEquiv d).symm)

lemma site_mirrorSwitch (d : ℕ) (t : SwitchIndex d) :
    site d (mirrorSwitch d t) = mirrorSite d (site d t) := by
  exact (siteEquiv d).apply_symm_apply _

lemma mirrorSwitch_involutive (d : ℕ) (t : SwitchIndex d) :
    mirrorSwitch d (mirrorSwitch d t) = t := by
  apply site_injective d
  rw [site_mirrorSwitch,site_mirrorSwitch]
  apply Subtype.ext
  simp [mirrorSite]

noncomputable def mirrorCoins (d : ℕ) : Equiv.Perm (SwitchIndex d → Bool) where
  toFun ω := fun t => ω (mirrorSwitch d t)
  invFun ω := fun t => ω (mirrorSwitch d t)
  left_inv ω := by funext t; change ω (mirrorSwitch d (mirrorSwitch d t)) = ω t; rw [mirrorSwitch_involutive]
  right_inv ω := by funext t; change ω (mirrorSwitch d (mirrorSwitch d t)) = ω t; rw [mirrorSwitch_involutive]

def reverseOrder (d : ℕ) : Equiv.Perm (Fin d) where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev

end Thorp.ButterflyReverse

namespace Thorp.StrongTail
open scoped BigOperators Classical

section
open Specht

lemma mem_tailDiagram (μ : YoungDiagram) (i j : ℕ) :
    (i,j) ∈ tailDiagram μ ↔ (i+1,j) ∈ μ := by
  rw [tailDiagram, YoungDiagram.mem_ofRowLens]
  constructor
  · rintro ⟨hi,hj⟩
    rw [List.getElem_tail,YoungDiagram.get_rowLens] at hj
    exact YoungDiagram.mem_iff_lt_rowLen.mpr hj
  · intro h
    have hi : i+1 < μ.colLen 0 :=
      (YoungDiagram.mem_iff_lt_colLen.mp h).trans_le (μ.colLen_anti 0 j (Nat.zero_le _))
    have hi' : i < μ.rowLens.tail.length := by simp only [List.length_tail,YoungDiagram.length_rowLens]; omega
    refine ⟨hi', ?_⟩
    simpa only [List.getElem_tail,YoungDiagram.get_rowLens] using YoungDiagram.mem_iff_lt_rowLen.mp h

lemma tail_height (μ : YoungDiagram) : (tailDiagram μ).colLen 0 = μ.colLen 0 - 1 := by
  rw [←YoungDiagram.length_rowLens]
  exact (YoungDiagram.rowLens_length_ofRowLens (fun x hx => μ.pos_of_mem_rowLens x (List.mem_of_mem_tail hx))).trans
    (by simp only [List.length_tail,YoungDiagram.length_rowLens])

noncomputable def tailCellEquiv (μ : YoungDiagram) : Cell (tailDiagram μ) ≃ Tail μ where
  toFun x := ⟨⟨(x.1.1+1,x.1.2),(mem_tailDiagram μ _ _).mp x.2⟩,by simp [row]⟩
  invFun x := ⟨(row x.1-1,col x.1),(mem_tailDiagram μ _ _).mpr (by
    have he : row x.1-1+1 = row x.1 := by have := x.2; omega
    change (row x.1-1+1,col x.1) ∈ μ
    rw [he]
    exact x.1.2)⟩
  left_inv x := by apply Subtype.ext; simp [row,col]
  right_inv x := by
    apply Subtype.ext; apply Subtype.ext; apply Prod.ext
    · change row x.1-1+1 = row x.1
      have := x.2; omega
    · rfl

noncomputable abbrev upCell (μ : YoungDiagram) (x : Cell (tailDiagram μ)) : Cell μ := (tailCellEquiv μ x).1

@[simp] lemma upCell_row (μ : YoungDiagram) (x : Cell (tailDiagram μ)) : row (upCell μ x) = row x+1 := rfl
@[simp] lemma upCell_col (μ : YoungDiagram) (x : Cell (tailDiagram μ)) : col (upCell μ x) = col x := rfl

noncomputable def extendPerm (μ : YoungDiagram) (p : Equiv.Perm (Cell (tailDiagram μ))) :
    Equiv.Perm (Cell μ) := p.extendDomain (tailCellEquiv μ)

@[simp] lemma extendPerm_up (μ : YoungDiagram) (p : Equiv.Perm (Cell (tailDiagram μ)))
    (x : Cell (tailDiagram μ)) : extendPerm μ p (upCell μ x) = upCell μ (p x) :=
  Equiv.Perm.extendDomain_apply_image p (tailCellEquiv μ) x

lemma extendPerm_top (μ : YoungDiagram) (p : Equiv.Perm (Cell (tailDiagram μ)))
    (x : Cell μ) (hx : row x=0) : extendPerm μ p x = x :=
  Equiv.Perm.extendDomain_apply_not_subtype p (tailCellEquiv μ) (not_not.mpr hx)

@[simp] lemma extendPerm_inv (μ : YoungDiagram) (p : Equiv.Perm (Cell (tailDiagram μ))) :
    (extendPerm μ p)⁻¹ = extendPerm μ p⁻¹ := Equiv.Perm.extendDomain_symm _ _

@[simp] lemma extendPerm_sign (μ : YoungDiagram) (p : Equiv.Perm (Cell (tailDiagram μ))) :
    permSign (extendPerm μ p) = permSign p := by
  simp [extendPerm,permSign,Equiv.Perm.sign_extendDomain]

noncomputable def liftRows (μ : YoungDiagram) (f : Tabloid (tailDiagram μ)) (x : Cell μ) : Fin (μ.colLen 0) :=
  if hx : row x ≠ 0 then
    ⟨(f.1 ((tailCellEquiv μ).symm ⟨x,hx⟩)).val+1,by
      have h := (f.1 ((tailCellEquiv μ).symm ⟨x,hx⟩)).isLt
      have hh := tail_height μ
      omega⟩
  else rowIndex x

@[simp] lemma liftRows_up (μ : YoungDiagram) (f : Tabloid (tailDiagram μ))
    (x : Cell (tailDiagram μ)) : (liftRows μ f (upCell μ x)).val = (f.1 x).val+1 := by
  simp [liftRows,upCell]

lemma liftRows_top (μ : YoungDiagram) (f : Tabloid (tailDiagram μ)) (x : Cell μ) (hx : row x=0) :
    liftRows μ f x = rowIndex x := by simp [liftRows,hx]

lemma liftRows_perm (μ : YoungDiagram) (f : Tabloid (tailDiagram μ))
    (p : Equiv.Perm (Cell (tailDiagram μ))) (hf : f.1 = rowIndex ∘ p) :
    liftRows μ f = rowIndex ∘ extendPerm μ p := by
  funext x
  by_cases hx : row x = 0
  · simp [liftRows_top μ f x hx,extendPerm_top μ p x hx]
  · let y := (tailCellEquiv μ).symm ⟨x,hx⟩
    have he : upCell μ y = x := congrArg Subtype.val ((tailCellEquiv μ).apply_symm_apply ⟨x,hx⟩)
    rw [←he]
    apply Fin.ext
    simp [hf,Function.comp_apply,rowIndex]

noncomputable def liftTabloid (μ : YoungDiagram) (f : Tabloid (tailDiagram μ)) : Tabloid μ :=
  ⟨liftRows μ f, by obtain ⟨p,hp⟩ := f.2; exact ⟨extendPerm μ p,liftRows_perm μ f p hp⟩⟩

@[simp] lemma liftTabloid_base (μ : YoungDiagram) :
    liftTabloid μ (baseTabloid (tailDiagram μ)) = baseTabloid μ := by
  apply Subtype.ext
  funext x
  by_cases hx : row x=0
  · exact liftRows_top μ _ x hx
  · let y := (tailCellEquiv μ).symm ⟨x,hx⟩
    have he : upCell μ y = x := congrArg Subtype.val ((tailCellEquiv μ).apply_symm_apply ⟨x,hx⟩)
    rw [←he]
    apply Fin.ext
    exact liftRows_up μ _ y

noncomputable def restrictTabloids (μ : YoungDiagram) :
    (Tabloid μ → ℂ) →ₗ[ℂ] (Tabloid (tailDiagram μ) → ℂ) where
  toFun v := fun f => v (liftTabloid μ f)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

end
open StrongSmoothing

end Thorp.StrongTail

end ThorpNine.Harmonic

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_HighTail_Coins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.HighTail

namespace Thorp

open scoped BigOperators
open Filter

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

end ThorpNine.HighTail

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_HighTail_ExposedCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.HighTail

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

end QueryTree

end Thorp

end ThorpNine.HighTail

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_HighTail_RotationMeeting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.HighTail

namespace Thorp
open scoped BigOperators
open Filter

section OrbitCore
variable {α : Type*} [Fintype α] [DecidableEq α]

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

end ThorpNine.HighTail

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_HighTail_AssignmentSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.HighTail

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

end ThorpNine.HighTail

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_HighTail_PriorPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.HighTail

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

end ThorpNine.HighTail

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_HighTail_ParallelFollow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.HighTail

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

end ParallelButterfly

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

section ParallelFairLayer
variable {β : Type*} [Fintype β] [DecidableEq β]

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

end Thorp

end ThorpNine.HighTail

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_HighTail_ProjectCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.HighTail

namespace Thorp
open scoped BigOperators
open Filter
namespace CycleColoring
variable {α : Type*} [Fintype α] [DecidableEq α]

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

noncomputable def headAverage {d : ℕ} (p : Card (d+1) → ℝ) (y : Card d) : ℝ :=
  (p (Fin.cons false y)+p (Fin.cons true y))/2

noncomputable def inverseButterflyMarks (d : ℕ) (A : Finset (Card d))
    (ω : SwitchIndex d → Bool) : Finset (Card d) :=
  A.image (butterflyPerm d (decodeButterfly d ω)).symm

namespace PairRouting

section
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

noncomputable instance instDecidableCompatible (x : ι → Bool × α) (c : ι → Bool) : Decidable (Compatible x c) :=
  Classical.propDecidable _

end

end PairRouting
end Thorp

end ThorpNine.HighTail

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_HighTail_ColoredEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.HighTail

namespace Thorp


noncomputable def sparseCoefficient {α : Type*} (w : ℝ) (T : Finset α) : ℝ :=
  if T.card = 1 then 0 else w^T.card


noncomputable def sparseMass {α β : Type*} [DecidableEq α] [Fintype β]
    (D : β → Finset α) (A : Finset α) : ℕ :=
  ∑ b, if 2 ≤ (D b ∩ A).card then (D b ∩ A).card else 0


def crowdedMass (h : ℕ) : ℕ := if 2 ≤ h then h else 0

end Thorp

end ThorpNine.HighTail

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_HighTail_CutoffMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.HighTail

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

end Thorp

end ThorpNine.HighTail

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_HighTail_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.HighTail

namespace Thorp

def familyEnd (L n : ℕ) : ℕ := if n = 0 then 0 else 2*(L*4^(n-1))

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

end Thorp


namespace Thorp.HighHeight
open scoped BigOperators Classical

def lowCoins (r s : ℕ) (Y : SwitchIndex (s+r) → Bool) :
    Card r × SwitchIndex s → Bool :=
  fun j => Y ((splitSwitch r s).symm (Sum.inl j))

noncomputable def lowEvent (r s : ℕ) (lo : Card r × SwitchIndex s → Bool)
    (Y : SwitchIndex (s+r) → Bool) : ℝ := if lowCoins r s Y=lo then 1 else 0


noncomputable def tailConstant : ℝ :=
  68*Real.exp (1/64)/(1-Real.exp (-1/64))

noncomputable def constant : ℝ := (tailConstant+densityConstant)/Real.log 2

end Thorp.HighHeight

end ThorpNine.HighTail

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Smoothing_Coins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Smoothing

namespace Thorp

open scoped BigOperators
open Filter

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

end Thorp

end ThorpNine.Smoothing

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Smoothing_ExposedCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Smoothing

namespace Thorp
open scoped BigOperators
open Filter

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

end QueryTree

end Thorp

end ThorpNine.Smoothing

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Smoothing_RotationCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Smoothing

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

end ThorpNine.Smoothing

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Smoothing_AssignmentSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Smoothing

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

end ThorpNine.Smoothing

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Smoothing_PriorPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Smoothing

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

end ThorpNine.Smoothing

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Smoothing_ParallelFollow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Smoothing

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

end CycleColoring
end Thorp

end ThorpNine.Smoothing

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Smoothing_AlternatingPerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Smoothing

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

end ThorpNine.Smoothing

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Smoothing_BenesCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Smoothing

namespace Thorp
open scoped BigOperators
open Filter

abbrev BenesCoins (d : ℕ) := (SwitchIndex d → Bool) × (SwitchIndex d → Bool)

def palindromePerm (d : ℕ) (ω : BenesCoins d) : Equiv.Perm (Card d) :=
  butterflyPerm d (decodeButterfly d ω.1) * (butterflyPerm d (decodeButterfly d ω.2)).symm

def sandwichShuffle {A B C D E F : Type*} :
    ((A × B) × C) × ((D × E) × F) ≃ ((A × D) × (B × E)) × (F × C) where
  toFun x := (((x.1.1.1,x.2.1.1),(x.1.1.2,x.2.1.2)),(x.2.2,x.1.2))
  invFun x := (((x.1.1.1,x.1.2.1),x.2.2),((x.1.1.2,x.1.2.2),x.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

def benesStepEquiv (d : ℕ) : BenesCoins (d+1) ≃
    (BenesCoins d × BenesCoins d) × ((Card d → Bool) × (Card d → Bool)) :=
  (Equiv.prodCongr (coinStepEquiv d) (coinStepEquiv d)).trans sandwichShuffle

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

end Thorp

end ThorpNine.Smoothing

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Smoothing_ParallelFreshPre
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Smoothing

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

noncomputable def palindromeFamilyCost (L n d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : ℕ :=
  ∑ j ∈ Finset.range n, palindromeSlabCost (L*4^j) d e ω

end Thorp

end ThorpNine.Smoothing

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Smoothing_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Smoothing

namespace Thorp


noncomputable def heightDecay (H : ℕ) : ℝ :=
  68*Real.exp (-(H:ℝ)/64)/(1-Real.exp (-(1:ℝ)/64))

noncomputable def momentBase : ℝ := (2:ℝ)^(1/1000:ℝ)

end Thorp


namespace Thorp.StrongSmoothing
open scoped BigOperators

variable {X : Type*} [Fintype X] [Nonempty X]

noncomputable def act (K : Matrix X X ℝ) (f : X → ℝ) (y : X) : ℝ := ∑ x, K x y*f x

variable [DecidableEq X]

noncomputable def rowDensity (K : Matrix X X ℝ) (r : ℕ) (x y : X) : ℝ :=
  (Fintype.card X:ℝ)*(K^r) x y

end Thorp.StrongSmoothing

namespace Thorp.StrongSmoothing.PermLaw
open scoped BigOperators
variable {X Ω Ω' : Type*} [Fintype X] [DecidableEq X] [Fintype Ω] [Fintype Ω']

noncomputable def kernel (P : Ω → Equiv.Perm X) : Matrix X X ℝ :=
  fun x y => finiteMean (fun ω => if P ω x = y then (1:ℝ) else 0)

end Thorp.StrongSmoothing.PermLaw

namespace Thorp.StrongSmoothing
open scoped BigOperators

section TupleAction
variable {ι β Ω : Type*} [Fintype ι] [Fintype β] [DecidableEq β] [Fintype Ω]

def tuplePerm (P : Equiv.Perm β) : Equiv.Perm (ι ↪ β) where
  toFun x := x.trans P.toEmbedding
  invFun x := x.trans P.symm.toEmbedding
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp

omit [Fintype ι] [Fintype β] [DecidableEq β] in
@[simp] lemma tuplePerm_apply (P : Equiv.Perm β) (x : ι ↪ β) (i : ι) :
    tuplePerm P x i = P (x i) := rfl

end TupleAction

end Thorp.StrongSmoothing

end ThorpNine.Smoothing

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_SparseSaving_Coins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.SparseSaving

namespace Thorp

open scoped BigOperators
open Filter

def CylinderBound {α : Type*} (m : Finset α → ℝ) (p : α → ℝ) : Prop :=
  ∀ s, m s ≤ ∏ i ∈ s, p i

noncomputable def finiteMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

namespace QueryTree

variable {ι : Type*} [DecidableEq ι]

def flipCoin (i : ι) : Equiv.Perm (ι → Bool) :=
  (show Function.Involutive (fun ω : ι → Bool => Function.update ω i (!(ω i))) from by
    intro ω
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [Function.update_of_ne h]).toPerm

end QueryTree

noncomputable def routeDomain : (d : ℕ) → Card d → Card d → Finset (SwitchIndex d)
  | 0, _, _ => ∅
  | d + 1, x, y => by
      classical
      exact insert (Sum.inl (Fin.tail y))
        ((routeDomain d (Fin.tail x) (Fin.tail y)).image (fun i => Sum.inr (x 0,i)))

end Thorp

end ThorpNine.SparseSaving

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_SparseSaving_ParallelFollow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.SparseSaving

namespace Thorp
open scoped BigOperators
open Filter

section JoinChildren
variable {β : Type*} [DecidableEq β]

noncomputable def boolFiber (S : Finset (Bool × β)) (b : Bool) : Finset β :=
  (S.filter (fun x => x.1 = b)).image Prod.snd

end JoinChildren

noncomputable def butterflyMarks (d : ℕ) (A : Finset (Card d))
    (ω : SwitchIndex d → Bool) : Finset (Card d) :=
  A.image (butterflyPerm d (decodeButterfly d ω))

end Thorp

end ThorpNine.SparseSaving

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_SparseSaving_ModifiedRoutingMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.SparseSaving

namespace Thorp


namespace DensityTransfer
open scoped BigOperators

noncomputable def applyKernel {X : Type*} [Fintype X] (P : X → X → ℝ)
    (v : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => ∑ y, (P x y : ℂ)*v y)

end DensityTransfer

end Thorp

end ThorpNine.SparseSaving

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_SparseSaving_ModifiedReverseEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.SparseSaving

namespace Thorp.Specht
open scoped BigOperators Classical

@[simp] lemma card_cell (μ : YoungDiagram) : Fintype.card (Cell μ) = μ.card := by
  simp [Cell, YoungDiagram.card]

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

end Thorp.Specht

end ThorpNine.SparseSaving

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_SparseSaving_ShapePartitionEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.SparseSaving

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

noncomputable def colIndex {μ : YoungDiagram} (x : Cell μ) : Fin (μ.rowLen 0) :=
  ⟨col x, (YoungDiagram.mem_iff_lt_rowLen.mp x.2).trans_le (μ.rowLen_anti 0 (row x) (Nat.zero_le _))⟩

noncomputable instance tabloidMulAction (μ : YoungDiagram) : MulAction (Equiv.Perm (Cell μ)) (Tabloid μ) where
  smul p f := tabloidAct p f
  one_smul f := by change tabloidAct 1 f = f; rw [tabloidAct_one]; rfl
  mul_smul p q f := by change tabloidAct (p*q) f = tabloidAct p (tabloidAct q f); rw [tabloidAct_mul]; rfl

abbrev Tail (μ : YoungDiagram) := {x : Cell μ // row x ≠ 0}

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

end Thorp.UnitaryFinite

end ThorpNine.SparseSaving

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_SparseSaving_Representative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.SparseSaving

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G X : Type*} [Group G] [Fintype G] [Fintype X]
  (a : G →* Equiv.Perm X) (x₀ : X) (ha : ∀ x, ∃ g, a g x₀=x)

noncomputable def representative (x : X) : G := Classical.choose (ha x)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

def IsFixed (w : V) : Prop := ∀ g, a g x₀=x₀ → ρ g w=w

end Thorp.UnitaryFinite

end ThorpNine.SparseSaving

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_SparseSaving_ModifiedStageEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.SparseSaving

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G X Ω : Type*} [Group G] [Fintype G] [Fintype X] [Fintype Ω]

noncomputable def actionKernel (a : G →* Equiv.Perm X) (P : Ω → G) (x y : X) : ℝ :=
  finiteMean (fun ω => if a (P ω) x=y then 1 else 0)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

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

noncomputable def neighborhood {V : Type*} [Fintype V] (G : SimpleGraph V)
    (R : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => ∃ v ∈ R, G.Adj v w)

def NoIsolated {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ v ∈ S, ∃ w ∈ S, G.Adj v w

noncomputable def typedSet {N X : Type*} [Fintype N] [Fintype X]
    (A : N → Finset X) : Finset (N × X) := by
  classical
  exact Finset.univ.filter (fun v => v.2 ∈ A v.1)

@[simp] lemma mem_typedSet {N X : Type*} [Fintype N] [Fintype X]
    (A : N → Finset X) (v : N × X) : v ∈ typedSet A ↔ v.2 ∈ A v.1 := by
  classical
  simp [typedSet]

noncomputable def fiber {N X : Type*} [Fintype X]
    (S : Finset (N × X)) (t : N) : Finset X := by
  classical
  exact Finset.univ.filter (fun x => (t,x) ∈ S)

@[simp] lemma mem_fiber {N X : Type*} [Fintype X]
    (S : Finset (N × X)) (t : N) (x : X) : x ∈ fiber S t ↔ (t,x) ∈ S := by
  classical
  simp [fiber]

end Thorp.SparseContact

end ThorpNine.SparseSaving

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_SparseSaving_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.SparseSaving

namespace Thorp.SparseContact
open scoped BigOperators Classical

noncomputable def typedMarks {N : Type*} [Fintype N] (d : ℕ)
    (A : N → Finset (Card d)) (ω : N → (SwitchIndex d → Bool)) : Finset (N × Card d) :=
  typedSet (fun t => butterflyMarks d (A t) (ω t))

noncomputable def returnRoute {N : Type*} (d : ℕ) (b : N → Butterfly d)
    (v : N × Card d) : Finset (SwitchIndex d) :=
  routeDomain d ((butterflyPerm d (b v.1)).symm v.2) v.2

noncomputable def returnGraph {N : Type*} (d : ℕ) (b : N → Butterfly d) :
    SimpleGraph (N × Card d) where
  Adj v w := v ≠ w ∧ ¬Disjoint (returnRoute d b v) (returnRoute d b w)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hh => h.2 hh.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable def endpointProb {L : Type*} (d : ℕ) (A : Finset L)
    (x y : L → Card d) : ℝ := by
  classical
  exact finiteMean (fun ω : SwitchIndex d → Bool =>
    if ∀ i ∈ A, butterflyPerm d (decodeButterfly d ω) (x i) = y i then (1:ℝ) else 0)

noncomputable def partialKernel {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x y : L → Card d) : ℝ :=
  ((2:ℝ)^d)^A.card / ((2:ℝ)^d)^(Fintype.card L) * endpointProb d A x y

def ContactEvent {L : Type*} (d : ℕ) (x y : L → Card d) : Prop :=
  ∀ i, ∃ j, i ≠ j ∧ ¬Disjoint (routeDomain d (x i) (y i)) (routeDomain d (x j) (y j))


noncomputable def networkOf {L : Type*} (A : Finset L) (i : L) : Option L := by
  classical
  exact if i ∈ A then none else some i

noncomputable def mixedTuple {L : Type*} (d : ℕ) (A : Finset L)
    (ω : Option L → (SwitchIndex d → Bool)) (x : L → Card d) : L → Card d :=
  fun i => butterflyPerm d (decodeButterfly d (ω (networkOf A i))) (x i)

noncomputable def mixedReturn {L : Type*} (d : ℕ) (A : Finset L)
    (ω : Option L → (SwitchIndex d → Bool)) (y : L → Card d) : L → Card d :=
  fun i => (butterflyPerm d (decodeButterfly d (ω (networkOf A i)))).symm (y i)

noncomputable def labelsOf {L : Type*} (A : Finset L) : Option L → Finset L := by
  classical
  exact fun t => match t with
    | none => A
    | some i => if i ∈ A then ∅ else {i}

noncomputable def mixedInitial {L : Type*} (d : ℕ) (A : Finset L)
    (x : L → Card d) (t : Option L) : Finset (Card d) := by
  classical
  exact (labelsOf A t).image x

noncomputable def retainedKernel {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x : L ↪ Card d) (y : L → Card d) : ℝ := by
  classical
  exact if ContactEvent d x y then partialKernel d A x y else 0

noncomputable def rectOperator {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Y → ℝ) : EuclideanSpace ℂ Y →L[ℂ] EuclideanSpace ℂ X :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun x => ∑ y, (P x y : ℂ)*v y)
      map_add' := by
        intro v w
        ext x
        simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        ext x
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
        change (∑ y, (P x y : ℂ)*(c*v y)) = c*∑ y, (P x y : ℂ)*v y
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring }

@[simp] lemma rectOperator_apply {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Y → ℝ) (v : EuclideanSpace ℂ Y) (x : X) :
    rectOperator P v x = ∑ y, (P x y:ℂ)*v y := rfl


noncomputable def pointStabilizer {α : Type*} (A : Finset α) : Subgroup (Equiv.Perm α) where
  carrier := {p | ∀ x ∈ A, p x = x}
  one_mem' := by intro x _; rfl
  mul_mem' := by intro p q hp hq x hx; change p (q x) = x; rw [hq x hx, hp x hx]
  inv_mem' := by intro p hp x hx; exact (Equiv.Perm.inv_eq_iff_eq).mpr (hp x hx).symm


section Orbit
variable {G X V : Type*} [Group G] [Fintype G] [Fintype X]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (a : G →* Equiv.Perm X) (x₀ : X) (ha : ∀ x, ∃ g, a g x₀ = x)
    (ρ : Representation ℂ G V) (w : V) (hw : UnitaryFinite.IsFixed a x₀ ρ w)

noncomputable def orbitVector (x : X) : V := ρ (UnitaryFinite.representative a x₀ ha x) w

end Orbit

def Harmonic {L α : Type*} [Fintype L] [Fintype α] (f : EuclideanSpace ℂ (L ↪ α)) : Prop :=
  ∀ (A : Finset L), A ≠ Finset.univ → ∀ z : L → α,
    (∑ y : L ↪ α, if ∀ i ∈ A, y i = z i then f y else 0) = 0

end Thorp.SparseContact

namespace Thorp.SparseContact

section
open scoped BigOperators Classical

noncomputable def zeroExtend {L α : Type*} [Fintype L] [Fintype α]
    (f : EuclideanSpace ℂ (L ↪ α)) : EuclideanSpace ℂ (L → α) := by
  classical
  exact WithLp.toLp 2 (fun y => if h : Function.Injective y then f ⟨y,h⟩ else 0)

end
open scoped BigOperators

end Thorp.SparseContact

namespace Thorp.SparseContact

noncomputable def contactConstant : ℝ := 32 * Real.exp (2 * Real.exp 1)

end Thorp.SparseContact


end ThorpNine.SparseSaving

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Tail_BenesCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Tail

namespace Thorp


def crowdedMass (h : ℕ) : ℕ := if 2 ≤ h then h else 0

end Thorp

end ThorpNine.Tail

end OAI
end


