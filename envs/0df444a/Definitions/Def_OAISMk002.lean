-- Prove2me | Definitions.Def_OAISMk002
-- name    : OAISMk002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T10:40:45.17359+00:00
-- url     : https://prove2.me/theorems/c7783486-7f50-4084-8401-a4264a15668f
-- title:
--   Definitions bundle OAISMk002 of the split of OpenAI, Nontrivial Markov Type Forces Superreflexivity
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MarkovSuperreflexivity.hasNontrivialMarkovType_iff_hasEquivalentUCNorm`, carved from OpenAI's openai/math development (OpenAI, *Nontrivial Markov Type Forces Superreflexivity*, OpenAI Math Release, September 23, 2026, result family 327, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 61 declarations of OpenAI's Lean: 25 definitions and 36 theorems. The definitions and types are `OAI.MarkovSuperreflexivity.latticeLift`, `OAI.MarkovSuperreflexivity.liftPotential`, `OAI.MarkovSuperreflexivity.markedChartPath`, `OAI.MarkovSuperreflexivity.markedLaw`, `OAI.MarkovSuperreflexivity.markedLetters`, `OAI.MarkovSuperreflexivity.markedSumCost`, `OAI.MarkovSuperreflexivity.normalizedChartEdgeLabel`, `OAI.MarkovSuperreflexivity.openArc`, `OAI.MarkovSuperreflexivity.positiveWalkLabel`, `OAI.MarkovSuperreflexivity.rawChartEdgeLabel`, `OAI.MarkovSuperreflexivity.rawChartWalkSum`, `OAI.MarkovSuperreflexivity.rawWalkLabel`, `OAI.MarkovSuperreflexivity.sampledBackward`, `OAI.MarkovSuperreflexivity.sampledDifference`, `OAI.MarkovSuperreflexivity.sampledForward`, `OAI.MarkovSuperreflexivity.selectedConsecutiveBlocks`, `OAI.MarkovSuperreflexivity.stationaryEdgeCost`, `OAI.MarkovSuperreflexivity.unitSequenceBidual`, `OAI.MarkovSuperreflexivity.unitSequenceBidualLinear`, `OAI.MarkovSuperreflexivity.walkAlphaPoint`, `OAI.MarkovSuperreflexivity.walkBetaPoint`, `OAI.MarkovSuperreflexivity.walkFractionPoint`, `OAI.MarkovSuperreflexivity.walkIntegerPoint`, `OAI.MarkovSuperreflexivity.walkOrbitFloor`, `OAI.MarkovSuperreflexivity.walkOrbitFraction`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/MarkovType, in whole or in part: `MarkovType_CoefficientSelectedBlocks`, `MarkovType_FiniteWalk`, `MarkovType_LatticeLift`, `MarkovType_MarkedChains`, `MarkovType_MarkedLetters`, `MarkovType_MarkedPaths`, `MarkovType_PeriodicArcs`, `MarkovType_PeriodicOrderIso`, `MarkovType_ReversibleMartingales`, `MarkovType_ScalarUltralimit`, `MarkovType_TriangularNonreflexivity`, `MarkovType_WalkLabels`, `MarkovType_WalkLandmarks`, `MarkovType_WalkMarkedDisplacement`, `MarkovType_WalkParameters`, `MarkovType_WalkPrefixLevels`, `MarkovType_WalkTransport`, `MarkovType_WordAction`.
--
--   **Imports.** It imports the published bundle `Def_MarkovType`; the bundles `OAISMk000` and `OAISMk001` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MarkovSuperreflexivity.FiniteTriangularObstruction.sequenceL2`, `OAI.MarkovSuperreflexivity.MarkovTypeWith.not_coordinatesRepresentable`, `OAI.MarkovSuperreflexivity.exists_power_smooth_equivalentNorm`, `OAI.MarkovSuperreflexivity.finiteTriangularObstruction_of_hasEquivalentUCNorm`, `OAI.MarkovSuperreflexivity.hasEquivalentUCNorm_of_finiteTriangularObstruction` and `OAI.MarkovSuperreflexivity.hasNontrivialMarkovType_iff_hasEquivalentUCNorm`.
-- source:
--   OpenAI, Nontrivial Markov Type Forces Superreflexivity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 327; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nontrivial-Markov-Type-Forces-Superreflexivity-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/MarkovType at commit adc7f12

import Mathlib
import Init.Data.List.Count
import Lean.Elab.Tactic.Omega
import Definitions.Def_MarkovType
import Definitions.Def_OAISMk000
import Definitions.Def_OAISMk001

section
-- module Solutions.OAIS_Markov.MarkovType_CoefficientSelectedBlocks
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n m : ℕ}

def selectedConsecutiveBlocks (e : Fin m ↪o Fin n) (x : Fin n → E) : Fin m → E :=
  consecutiveBlocks x (selectedBlockCuts e)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_MarkedChains
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.instFintypeOrbitRep _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

def stationaryEdgeCost {S E V : Type*} [Fintype S] [Fintype E]
    [NormedAddCommGroup V] (C : FiniteMarkedChain S E) (g : E → V) (p : ℝ) : ℝ :=
  ∑ e, C.π (C.src e) * C.q e * Real.rpow (‖g e‖) p

def markedSumCost {S E V : Type*} [Fintype S] [Fintype E]
    [NormedAddCommGroup V] (C : FiniteMarkedChain S E) (g : E → V) (p : ℝ)
    (n : ℕ) : ℝ :=
  markedExpect C n (fun ω => Real.rpow (‖edgeSum g ω‖) p)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_MarkedPaths
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.instFintypeOrbitRep _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {S E : Type*} [sectionFintypeS : Fintype S] [sectionFintypeE : Fintype E]

theorem markedPathWeight_nonneg (C : FiniteMarkedChain S E) (n : ℕ)
    (ω : MarkedPath S E n) : 0 ≤ markedPathWeight C n ω := by
  classical
  unfold markedPathWeight
  split_ifs
  · exact mul_nonneg (C.π_nonneg _) (Finset.prod_nonneg fun i _ => C.q_nonneg _)
  · exact le_rfl

def markedLaw (C : FiniteMarkedChain S E) (n : ℕ) : FiniteLaw (MarkedPath S E n) where
  mass := markedPathWeight C n
  mass_nonneg := markedPathWeight_nonneg C n
  sum_mass := sum_markedPathWeight C n

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_MarkedLetters
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {S E A : Type*} [sectionFintypeS : Fintype S] [sectionFintypeE : Fintype E] [sectionFintypeA : Fintype A]

def markedLetters (mark : E → A) {n : ℕ} (ω : MarkedPath S E n) : Fin n → A :=
  fun i => mark (ω.2 i)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_PeriodicOrderIso
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

theorem periodicLiftFun_add_int (e : ℝ ≃o ℝ) (x : ℝ) (j : ℤ) :
    periodicLiftFun e (x + j) = periodicLiftFun e x + j := by
  simp only [periodicLiftFun, Int.floor_add_intCast, Int.fract_add_intCast, Int.cast_add]
  ring

theorem periodicBend_add_int (x : ℝ) (j : ℤ) :
    periodicBend (x + j) = periodicBend x + j :=
  periodicLiftFun_add_int twoSlopeOrderIso x j

theorem periodicBend_symm_add_int (x : ℝ) (j : ℤ) :
    periodicBend.symm (x + j) = periodicBend.symm x + j :=
  periodicLiftFun_add_int twoSlopeOrderIso.symm x j

theorem periodicBend_displacement (x : ℝ) :
    0 ≤ periodicBend x - x ∧ periodicBend x - x ≤ 7 / 9 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  have he : periodicBend x - x = twoSlope (Int.fract x) - Int.fract x := by
    rw [periodicBend_apply]
    have hf := Int.floor_add_fract x
    linarith
  rw [he]
  unfold twoSlope
  split_ifs <;> constructor <;> linarith

theorem translatedPeriodicOrderIso_add_int (a c x : ℝ) (j : ℤ) :
    translatedPeriodicOrderIso a c (x + j) = translatedPeriodicOrderIso a c x + j := by
  change c + periodicBend (x + j - a) = c + periodicBend (x - a) + j
  rw [show x + (j : ℝ) - a = x - a + j by ring, periodicBend_add_int]
  ring

theorem translatedPeriodicOrderIso_symm_add_int (a c x : ℝ) (j : ℤ) :
    (translatedPeriodicOrderIso a c).symm (x + j) =
      (translatedPeriodicOrderIso a c).symm x + j := by
  change a + periodicBend.symm (x + j - c) = a + periodicBend.symm (x - c) + j
  rw [show x + (j : ℝ) - c = x - c + j by ring, periodicBend_symm_add_int]
  ring

theorem translatedPeriodicOrderIso_displacement (a c x : ℝ) :
    c - a ≤ translatedPeriodicOrderIso a c x - x ∧
      translatedPeriodicOrderIso a c x - x ≤ c - a + 7 / 9 := by
  have h := periodicBend_displacement (x - a)
  rw [translatedPeriodicOrderIso_apply]
  constructor <;> linarith

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_PeriodicArcs
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

def openArc (s : Letter) : Set ℝ := periodicIoo (alpha s) (beta s)

theorem letterOrderIso_inv (s : Letter) : letterOrderIso s.inv = (letterOrderIso s).symm := by
  rcases s with ⟨g, b⟩
  cases b <;> rfl

theorem letterOrderIso_add_int (s : Letter) (x : ℝ) (j : ℤ) :
    letterOrderIso s (x + j) = letterOrderIso s x + j := by
  rcases s with ⟨g, b⟩
  cases b
  · exact translatedPeriodicOrderIso_symm_add_int _ _ x j
  · exact translatedPeriodicOrderIso_add_int _ _ x j

theorem positiveOrderIso_displacement (g : Fin 2) (x : ℝ) :
    -(4 / 3 : ℝ) ≤ positiveOrderIso g x - x ∧
      positiveOrderIso g x - x ≤ -(5 / 9 : ℝ) := by
  have h := translatedPeriodicOrderIso_displacement (alpha (g, false))
    (beta (g, true) - 1) x
  change beta (g, true) - 1 - alpha (g, false) ≤ positiveOrderIso g x - x ∧
    positiveOrderIso g x - x ≤ beta (g, true) - 1 - alpha (g, false) + 7 / 9 at h
  have hc : beta (g, true) - 1 - alpha (g, false) = -(4 / 3 : ℝ) := by
    fin_cases g <;> norm_num [beta, alpha, arcRank]
  rw [hc] at h
  change -(4 / 3 : ℝ) ≤ positiveOrderIso g x - x ∧
    positiveOrderIso g x - x ≤ -(5 / 9 : ℝ)
  constructor <;> linarith

theorem letterOrderIso_abs_move_le (s : Letter) (x : ℝ) :
    |letterOrderIso s x - x| ≤ (4 / 3 : ℝ) := by
  rcases s with ⟨g, b⟩
  cases b
  · change |(positiveOrderIso g).symm x - x| ≤ (4 / 3 : ℝ)
    have h := positiveOrderIso_displacement g ((positiveOrderIso g).symm x)
    rw [(positiveOrderIso g).apply_symm_apply] at h
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · change |positiveOrderIso g x - x| ≤ (4 / 3 : ℝ)
    have h := positiveOrderIso_displacement g x
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem letterOrderIso_displacement_lt (s : Letter) (x : ℝ) :
    |letterOrderIso s x - x| < 2 :=
  lt_of_le_of_lt (letterOrderIso_abs_move_le s x) (by norm_num)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkParameters
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

theorem walk_shift_bounds {n : ℕ} {j m : ℤ}
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ))
    (hmlo : -(2 * (n : ℤ)) ≤ m) (hmhi : m ≤ 2 * (n : ℤ) - 1) :
    3 ≤ j - m ∧ j - m ≤ (walkWindowLength n : ℤ) - 2 := by
  simp only [walkWindowLeft, walkWindowRight, walkWindowLength,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at *
  omega

theorem walk_integer_shift_mem_range {n : ℕ} {j : ℤ}
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ)) :
    -(2 * (n : ℤ)) ≤ j ∧ j ≤ (walkWindowLength n : ℤ) + 2 * (n : ℤ) := by
  simp only [walkWindowLeft, walkWindowRight, walkWindowLength,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at *
  omega

theorem walk_translated_shift_mem_range {n : ℕ} {j m : ℤ}
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ))
    (hmlo : -(2 * (n : ℤ)) ≤ m) (hmhi : m ≤ 2 * (n : ℤ) - 1) :
    -(2 * (n : ℤ)) ≤ j - m ∧
      j - m ≤ (walkWindowLength n : ℤ) + 2 * (n : ℤ) := by
  obtain ⟨hlo, hhi⟩ := walk_shift_bounds hjlo hjhi hmlo hmhi
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  omega

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WordAction
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

theorem wordMap_append (u v : List Letter) (x : ℝ) :
    wordMap (u ++ v) x = wordMap u (wordMap v x) := by
  induction u with
  | nil => rfl
  | cons s u ih => simp only [List.cons_append, wordMap_cons, ih]

theorem wordMap_inverseWord (w : List Letter) :
    wordMap (inverseWord w) = (wordMap w).symm := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      apply OrderIso.ext
      funext x
      simp only [inverseWord_cons, wordMap_append, wordMap_singleton, ih,
        letterOrderIso_inv, wordMap_cons_symm]

theorem wordMap_add_int (w : List Letter) (x : ℝ) (j : ℤ) :
    wordMap w (x + (j : ℝ)) = wordMap w x + (j : ℝ) := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      simp only [wordMap_cons, ih, letterOrderIso_add_int]

theorem wordMap_symm_add_int (w : List Letter) (x : ℝ) (j : ℤ) :
    (wordMap w).symm (x + (j : ℝ)) = (wordMap w).symm x + (j : ℝ) := by
  rw [← wordMap_inverseWord]
  exact wordMap_add_int (inverseWord w) x j

theorem prefixState_wordMap (w : List Letter) (k : ℕ) (x : ℝ) :
    (wordMap (w.take k)).symm (wordMap w x) = wordMap (w.drop k) x := by
  have h : wordMap w x = wordMap (w.take k) (wordMap (w.drop k) x) := by
    rw [← wordMap_append, List.take_append_drop]
  rw [h, OrderIso.symm_apply_apply]

theorem prefixState_wordMap_add_int (w : List Letter) (k : ℕ) (x : ℝ) (j : ℤ) :
    (wordMap (w.take k)).symm (wordMap w x + (j : ℝ)) =
      wordMap (w.drop k) x + (j : ℝ) := by
  rw [wordMap_symm_add_int, prefixState_wordMap]

theorem wordMap_displacement_le (w : List Letter) (x : ℝ) :
    abs (wordMap w x - x) ≤ 2 * (w.length : ℝ) := by
  induction w with
  | nil => simp only [wordMap_nil_apply, sub_self, abs_zero, List.length_nil,
      Nat.cast_zero, mul_zero, le_refl]
  | cons s w ih =>
      have hs := letterOrderIso_displacement_lt s (wordMap w x)
      have ht := abs_sub_le (letterOrderIso s (wordMap w x)) (wordMap w x) x
      simp only [wordMap_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

theorem wordMap_displacement_lt {w : List Letter} (hw : w ≠ []) (x : ℝ) :
    abs (wordMap w x - x) < 2 * (w.length : ℝ) := by
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons s w =>
      have hs := letterOrderIso_displacement_lt s (wordMap w x)
      have ht := abs_sub_le (letterOrderIso s (wordMap w x)) (wordMap w x) x
      have ih := wordMap_displacement_le w x
      simp only [wordMap_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkLandmarks
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

theorem sampled_integer_mem_walkLandmarks {n : ℕ} (j : ℤ)
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ)) :
    (j : ℝ) ∈ walkLandmarks n := by
  obtain ⟨hlo, hhi⟩ := walk_integer_shift_mem_range hjlo hjhi
  exact integer_mem_walkLandmarks j hlo hhi

theorem translated_orbit_mem_walkLandmarks {n : ℕ} (w : List Letter)
    (hw : w.length ≤ n) (j m : ℤ)
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ))
    (hmlo : -(2 * (n : ℤ)) ≤ m) (hmhi : m ≤ 2 * (n : ℤ) - 1) :
    wordMap w 0 + ((j - m : ℤ) : ℝ) ∈ walkLandmarks n := by
  obtain ⟨hlo, hhi⟩ := walk_translated_shift_mem_range hjlo hjhi hmlo hmhi
  exact orbit_shift_mem_walkLandmarks w hw (j - m) hlo hhi

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkLabels
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

def walkAlphaPoint (n : ℕ) (s : Letter) (j : Fin (walkWindowLength n)) :
    ↥(walkLandmarks n) :=
  ⟨alpha s + (j.val : ℝ), alpha_shift_mem_walkLandmarks n s j⟩

def walkBetaPoint (n : ℕ) (s : Letter) (j : Fin (walkWindowLength n)) :
    ↥(walkLandmarks n) :=
  ⟨beta s + (j.val : ℝ), beta_shift_mem_walkLandmarks n s j⟩

def positiveWalkLabel {n B : ℕ} (C : Chart (walkLandmarks n) B) (s : Letter) : C00 :=
  ∑ j : Fin (walkWindowLength n),
    (C00.basis (C (walkAlphaPoint n s j)).val -
      C00.basis (C (walkBetaPoint n s j)).val)

def rawWalkLabel {n B : ℕ} (C : Chart (walkLandmarks n) B) (s : Letter)
    (C' : Chart (walkLandmarks n) B) : C00 :=
  if s.2 then positiveWalkLabel C s else -positiveWalkLabel C' s.inv

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkTransport
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

noncomputable def walkOrbitFloor (w : List Letter) : ℤ := Int.floor (wordMap w 0)

noncomputable def walkOrbitFraction (w : List Letter) : ℝ :=
  wordMap w 0 - (walkOrbitFloor w : ℝ)

theorem wordMap_displacement_lt_of_length_le {n : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n) (y : ℝ) :
    abs (wordMap w y - y) < 2 * (n : ℝ) := by
  by_cases hnil : w = []
  · subst w
    simp only [wordMap_nil_apply, sub_self, abs_zero]
    positivity
  · have hd := wordMap_displacement_lt hnil y
    have hcast : (w.length : ℝ) ≤ (n : ℝ) := by exact_mod_cast hw
    linarith

theorem walkOrbitFloor_bounds {n : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n) :
    -(2 * (n : ℤ)) ≤ walkOrbitFloor w ∧
      walkOrbitFloor w ≤ 2 * (n : ℤ) - 1 := by
  apply walk_floor_bounds
  simpa only [sub_zero] using wordMap_displacement_lt_of_length_le hn w hw 0

theorem walkOrbitFraction_add_int (w : List Letter) (j : ℤ) :
    walkOrbitFraction w + (j : ℝ) =
      wordMap w 0 + ((j - walkOrbitFloor w : ℤ) : ℝ) := by
  simp only [walkOrbitFraction, Int.cast_sub]
  ring

theorem pullbackPoint_fraction_mem {n : ℕ} (hn : 0 < n)
    (w : List Letter) (hw : w.length ≤ n) (k : ℕ) (j : ℤ)
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ)) :
    pullbackPoint w k (walkOrbitFraction w + (j : ℝ)) ∈ walkLandmarks n := by
  rw [walkOrbitFraction_add_int]
  change (wordMap (w.take k)).symm
    (wordMap w 0 + ((j - walkOrbitFloor w : ℤ) : ℝ)) ∈ walkLandmarks n
  rw [prefixState_wordMap_add_int]
  obtain ⟨hmlo, hmhi⟩ := walkOrbitFloor_bounds hn w hw
  apply translated_orbit_mem_walkLandmarks _ _ j (walkOrbitFloor w)
    hjlo hjhi hmlo hmhi
  simp only [List.length_drop]
  omega

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkPrefixLevels
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

def rawChartWalkSum {n B : ℕ} (w : List Letter)
    (C : Fin (w.length + 1) → Chart (walkLandmarks n) B) : C00 :=
  ∑ i : Fin w.length, rawWalkLabel (C i.castSucc) (w.get i) (C i.succ)

def walkIntegerPoint {n : ℕ} (j : ℤ)
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ)) : ↥(walkLandmarks n) :=
  ⟨(j : ℝ), sampled_integer_mem_walkLandmarks j hjlo hjhi⟩

def walkFractionPoint {n : ℕ} (hn : 0 < n) (w : List Letter)
    (hw : w.length ≤ n) (j : ℤ)
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ)) : ↥(walkLandmarks n) :=
  ⟨walkOrbitFraction w + (j : ℝ), by
    simpa only [pullbackPoint_zero] using
      pullbackPoint_fraction_mem hn w hw 0 j hjlo hjhi⟩

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_WalkMarkedDisplacement
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

open FiniteWalkDrift

def rawChartEdgeLabel {n B : ℕ} (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (e : UniformCouplingEdge (PositiveMassSupport ν) Letter) : C00 :=
  rawWalkLabel e.1.val e.2.1 e.2.2.val

def markedChartPath {n B : ℕ} (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) n)
    (i : Fin (n + 1)) : Chart (walkLandmarks n) B :=
  (markedState (concreteChartChain ν) ω i).val

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteWalk
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instFiniteDimensionalReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instModuleReal _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNorm _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.CoordinateSpace.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instModuleReal _root_.OAI.MarkovSuperreflexivity.NormedC00.instNorm _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.NormedC00.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

open FiniteWalkDrift

def normalizedChartEdgeLabel (N : OrderedNorm) {n B : ℕ}
    (ν : FiniteLaw (Chart (walkLandmarks n) B)) (e : ConcreteChartEdge ν) : C00 :=
  (N.alternatingNorm (walkWindowLength n))⁻¹ • rawChartEdgeLabel ν e

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_LatticeLift
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {S E : Type*} [Fintype S] [Fintype E]

def latticeLift (C : FiniteMarkedChain S E) (R : ℕ) :
    FiniteMarkedChain (S × LiftCube C R) (E × LiftCube C R) where
  π := liftMass C R
  π_nonneg := liftMass_nonneg C R
  sum_π := sum_liftMass C R
  src := liftSource C R
  tgt := liftTarget C R
  rev := liftReverse C R
  rev_rev := liftReverse_involutive C R
  src_rev := liftSource_reverse C R
  tgt_rev := liftTarget_reverse C R
  q := fun e => C.q e.1
  q_nonneg := fun e => C.q_nonneg e.1
  sum_q := fun s => by
    rw [← sum_liftOutgoing C R s]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : liftSource C R e = s <;> simp only [he, ite_true, ite_false]
  balance := lift_edge_balance C R

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def liftPotential (C : FiniteMarkedChain S E) (g : E → V) (R : ℕ)
    (x : S × LiftCube C R) : V := labelLinear C g (latticeCubeVal x.2)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_ReversibleMartingales
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {S X : Type*} [Fintype S]
variable [NormedAddCommGroup X] [sectionNormedSpaceℝX : NormedSpace ℝ X]

def sampledDifference (C : FiniteReversibleChain S) (f : S → X)
    {m : ℕ} (j : Fin m) (ω : StatePath S (2 * m)) : X :=
  f (ω (sampledEvenIndex j.succ)) - chainAverage C f (ω (sampledOddIndex j))

def sampledForward (C : FiniteReversibleChain S) (f : S → X)
    (m k : ℕ) (ω : StatePath S (2 * m)) : X :=
  ∑ j : Fin m, if j.val < k then sampledDifference C f j ω else 0

def sampledBackward (C : FiniteReversibleChain S) (f : S → X)
    (m k : ℕ) (ω : StatePath S (2 * m)) : X :=
  sampledForward C f m k (pathReverse ω)

@[simp] theorem sampledForward_zero (C : FiniteReversibleChain S)
    (f : S → X) (m : ℕ) (ω : StatePath S (2 * m)) :
    sampledForward C f m 0 ω = 0 := by
  simp [sampledForward]

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_ScalarUltralimit
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace MarkovSuperreflexivity

variable {f g : ℕ → ℝ}

theorem realULim_abs (U : Ultrafilter ℕ) (hf : RealSeqBounded f) :
    realULim U (fun n => |f n|) = |realULim U f| :=
  realULim_eq_of_tendsto U (tendsto_realULim U hf).abs

theorem realULim_le_of_eventually_le (U : Ultrafilter ℕ) (hf : RealSeqBounded f)
    {c : ℝ} (h : ∀ᶠ n in (U : Filter ℕ), f n ≤ c) : realULim U f ≤ c :=
  le_of_tendsto (tendsto_realULim U hf) h

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularNonreflexivity
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace MarkovSuperreflexivity

universe u

variable {Z : Type u} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem unit_eval_bounded (e : ℕ → Z) (he : ∀ i, ‖e i‖ ≤ 1)
    (g : StrongDual ℝ Z) : RealSeqBounded (fun i => g (e i)) :=
  ⟨‖g‖, unit_eval_abs_le e he g⟩

theorem unit_eval_ulim_bound (e : ℕ → Z) (he : ∀ i, ‖e i‖ ≤ 1)
    (g : StrongDual ℝ Z) :
    |realULim freeUltrafilter (fun i => g (e i))| ≤ ‖g‖ := by
  rw [← realULim_abs freeUltrafilter (unit_eval_bounded e he g)]
  exact realULim_le_of_eventually_le freeUltrafilter (unit_eval_bounded e he g).abs
    (Filter.Eventually.of_forall (unit_eval_abs_le e he g))

def unitSequenceBidualLinear (e : ℕ → Z) (he : ∀ i, ‖e i‖ ≤ 1) :
    StrongDual ℝ Z →ₗ[ℝ] ℝ where
  toFun g := realULim freeUltrafilter (fun i => g (e i))
  map_add' g h := by
    simpa only [add_apply] using
      realULim_add freeUltrafilter (unit_eval_bounded e he g) (unit_eval_bounded e he h)
  map_smul' c g := by
    simpa only [smul_apply, RingHom.id_apply, smul_eq_mul] using
      realULim_const_mul freeUltrafilter c (unit_eval_bounded e he g)

def unitSequenceBidual (e : ℕ → Z) (he : ∀ i, ‖e i‖ ≤ 1) :
    StrongDual ℝ (StrongDual ℝ Z) :=
  (unitSequenceBidualLinear e he).mkContinuous 1 (fun g => by
    change ‖realULim freeUltrafilter (fun i => g (e i))‖ ≤ 1 * ‖g‖
    simpa only [Real.norm_eq_abs, one_mul] using unit_eval_ulim_bound e he g)

@[simp]
theorem unitSequenceBidual_apply (e : ℕ → Z) (he : ∀ i, ‖e i‖ ≤ 1)
    (g : StrongDual ℝ Z) :
    unitSequenceBidual e he g = realULim freeUltrafilter (fun i => g (e i)) := rfl

end MarkovSuperreflexivity

end

end OAI
end


