-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
-- name    : LeanPool_DeciSigma1_Holes_Tail_Levels
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:53:14.901528+00:00
-- url     : https://prove2.me/theorems/a05fbb97-cb37-4d32-a014-96449d791813
-- title:
--   Levels
-- statement:
--   Definitions and structural lemmas for Levels, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Levels.lean

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.GroupWithZero.Nat
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_le_suffixLengthEnvelope
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_cons
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_cons
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
structure LevelBounds (σ k N : ℕ) where
  /-- Uniform bound on designated periodic pieces. -/
  pieceCountBase : ℕ
  /-- Period bound at each level. -/
  periodBound : ℕ → ℕ
  /-- Suffix-chain bound at each level. -/
  chainLengthBound : ℕ → ℕ
  /-- Terminal periodic-suffix bound at each level. -/
  terminalLengthBound : ℕ → ℕ
  /-- Bound on uncovered positions at each level. -/
  uncoveredBound : ℕ → ℕ
  /-- Length needed to escape the preceding level. -/
  escapeLengthBound : ℕ → ℕ
  /-- Suffix window needed to compare states at each level. -/
  comparisonWindow : ℕ → ℕ
  /-- Initial suffix window at each level. -/
  startWindow : ℕ → ℕ
  /-- Suffix-chain budget at each level. -/
  fixedChainBudget : ℕ → ℕ
  pieceCountBase_eq : pieceCountBase = 4 + 2 * (k - 1) * (N - 1)
  periodBound_mono : Monotone periodBound
  terminalLengthBound_mono : Monotone terminalLengthBound
  uncoveredBound_mono : Monotone uncoveredBound
  escapeLengthBound_mono : Monotone escapeLengthBound
  stateCount_le_fixedChainBudget : ∀ l, N ≤ fixedChainBudget l
  fixedChainBudget_ge_chainLength : ∀ l, chainLengthBound l + N ≤ fixedChainBudget (l + 2)
  chainLengthBound_ge_cover : ∀ l, (pieceCountBase + 1) * (2 * periodBound l) + uncoveredBound l +
      terminalLengthBound l ≤ chainLengthBound l
  startWindow_gt : ∀ l, (N + 1) * periodBound l < startWindow (l + 1)
  chainWindow_le_startWindow : ∀ l, (pieceCountBase + 2) * (chainLengthBound l + 1) ≤
      startWindow (l + 2)
  escapeLengthBound_eq : ∀ l, escapeLengthBound l =
      suffixLengthBound k N (List.replicate k (pieceCountBase + N)) (startWindow l)
  comparisonWindow_eq : ∀ l, comparisonWindow l =
      suffixLengthEnvelope k N (List.replicate k (pieceCountBase + N)) (startWindow l)
  factorLengthBound_le_periodBound : ∀ l, factorLengthBound k N (comparisonWindow l) ≤ periodBound l
  periodBound_lt_escapeLengthBound : 1 ≤ N → ∀ l, periodBound l < escapeLengthBound l
  uncoveredBound_ge_candidateBound : ∀ l, (pieceCountBase + 2) * (3 * escapeLengthBound l + 3) ≤
      uncoveredBound l
  terminalLengthBound_gt_cover : ∀ l, N * periodBound (l + 1) + uncoveredBound l +
      (pieceCountBase + 1) * (2 * periodBound (l + 1)) < terminalLengthBound (l + 1)
  terminalLengthBound_ge_periodBudget : ∀ l, 1 + fixedChainBudget (l + 1) *
      (periodBound l * N.factorial) + 2 * (periodBound l * N.factorial) + N * periodBound l ≤
          terminalLengthBound l
def levelCount (k : ℕ) : ℕ := 3 * (2 * k + 1)
structure LevelState where
  /-- Period bound passed to the next level. -/
  periodBound : ℕ
  /-- Current suffix-chain bound. -/
  chainLengthBound : ℕ
  /-- Suffix-chain bound from the preceding level. -/
  previousChainLengthBound : ℕ
  /-- Bound on terminal periodic suffixes. -/
  terminalLengthBound : ℕ
  /-- Bound on positions outside the periodic cover. -/
  uncoveredBound : ℕ
def levelStartWindow (N Q : ℕ) (st : LevelState) : ℕ :=
  (N + 1) * st.periodBound + (Q + 2) * (st.previousChainLengthBound + 1)
def levelStep (k N Q : ℕ) (st : LevelState) : LevelState :=
  let bs := levelStartWindow N Q st
  let Tp := suffixLengthBound k N (List.replicate k (Q + N)) bs
  let Bw := suffixLengthEnvelope k N (List.replicate k (Q + N)) bs
  let e := max (factorLengthBound k N Bw) st.periodBound
  let Tt := (Q + 2) * (3 * Tp + 3)
  let h := e * N.factorial
  let Y := (1 + (st.chainLengthBound + N) * h) + 2 * h + N * e + (Q + 3) * (3 * e) +
      st.uncoveredBound + st.terminalLengthBound
  { periodBound := e, chainLengthBound := (Q + 2) * (1 + 2 * e) + Tt + Y + N,
    previousChainLengthBound := st.chainLengthBound, terminalLengthBound := Y,
    uncoveredBound := Tt }
def initialLevelState : LevelState :=
  { periodBound := 1, chainLengthBound := 0, previousChainLengthBound := 0,
    terminalLengthBound := 0, uncoveredBound := 0 }
def levelMultiplicity (k N : ℕ) : ℕ := 4 + 2 * (k - 1) * (N - 1)
def levelState (k N l : ℕ) :
    LevelState := (levelStep k N (levelMultiplicity k N))^[l] initialLevelState
section Explicit
variable {N : ℕ}
theorem levelState_succ (l : ℕ) :
    levelState k N (l + 1) = levelStep k N (levelMultiplicity k N) (levelState k N l) :=
  Function.iterate_succ_apply' _ _ _
theorem levelState_periodBound_pos (l : ℕ) : 1 ≤ (levelState k N l).periodBound := by
  induction l with
  | zero => simp [levelState, initialLevelState]
  | succ l ih => rw [levelState_succ]; simp only [levelStep]; omega
theorem levelStep_chainLengthBound_ge (Q : ℕ) (st : LevelState) (he : 1 ≤ st.periodBound) :
    st.chainLengthBound ≤ (levelStep k N Q st).chainLengthBound := by
  simp only [levelStep]
  set e := max (factorLengthBound k N (suffixLengthEnvelope k N (List.replicate k (Q + N))
    (levelStartWindow N Q st))) st.periodBound
  have h1 : 1 ≤ e := le_trans he (le_max_right _ _)
  have h2 : 1 ≤ e * N.factorial :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (Nat.factorial_ne_zero N))
  have h3 := Nat.le_mul_of_pos_right (st.chainLengthBound + N) h2
  omega
theorem levelState_previousChainLengthBound_le (l : ℕ) :
    (levelState k N l).previousChainLengthBound ≤ (levelState k N l).chainLengthBound := by
  cases l with
  | zero => simp [levelState, initialLevelState]
  | succ l =>
    rw [levelState_succ]
    exact levelStep_chainLengthBound_ge _ _ (levelState_periodBound_pos l)
theorem lt_factorLengthBound (m N b : ℕ) (hN : 1 ≤ N) : b < factorLengthBound m N b := by
  unfold factorLengthBound suffixNodeBound
  have h1 : 1 ≤ N * (m * (b * (b + 1) / 2) + 1) := Nat.mul_pos hN (Nat.succ_pos _)
  have h2 := Nat.mul_le_mul_left (b + 1) h1
  omega
theorem factorLengthBound_suffixLengthEnvelope_lt (m N : ℕ) :
    ∀ (Ss : List ℕ) (b : ℕ), factorLengthBound m N (suffixLengthEnvelope m N Ss b) <
        suffixLengthBound m N Ss b
  | [], b => by simp
  | S :: Ss, b => by
    rw [suffixLengthBound_cons, suffixLengthEnvelope_cons]
    have :=
        factorLengthBound_suffixLengthEnvelope_lt m N Ss
            ((fun b => b + suffixLengthBound m N Ss b)^[S] b +
      suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b))
    omega
def levelWindow (k N l : ℕ) : ℕ := levelStartWindow N (levelMultiplicity k N) (levelState k N l)
def levelEscapeLength (k N l : ℕ) : ℕ :=
  suffixLengthBound k N (List.replicate k (levelMultiplicity k N + N)) (levelWindow k N l)
theorem levelWindow_le_succ (l : ℕ) : levelWindow k N l ≤ levelWindow k N (l + 1) := by
  unfold levelWindow levelStartWindow
  rw [levelState_succ l]
  simp only [levelStep]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (le_max_right _ _))
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (levelState_previousChainLengthBound_le l) 1))
theorem levelEscapeLength_le_succ (l : ℕ) :
    levelEscapeLength k N l ≤ levelEscapeLength k N (l + 1) :=
  suffixLengthBound_mono k N _ (levelWindow_le_succ l)
theorem levelState_succ_uncoveredBound (l : ℕ) : (levelState k N (l + 1)).uncoveredBound =
    (levelMultiplicity k N + 2) * (3 * levelEscapeLength k N l + 3) := by
  rw [levelState_succ]; rfl
end Explicit
def levelBounds (σ k N : ℕ) : LevelBounds σ k N where
  pieceCountBase := levelMultiplicity k N
  periodBound l := (levelState k N (l + 1)).periodBound
  chainLengthBound l := (levelState k N (l + 1)).chainLengthBound
  terminalLengthBound l := (levelState k N (l + 1)).terminalLengthBound
  uncoveredBound l := (levelState k N (l + 1)).uncoveredBound
  escapeLengthBound l := levelEscapeLength k N l
  comparisonWindow l :=
      suffixLengthEnvelope k N (List.replicate k (levelMultiplicity k N + N)) (levelWindow k N l)
  startWindow l := levelWindow k N l
  fixedChainBudget l := (levelState k N l).previousChainLengthBound + N
  pieceCountBase_eq := rfl
  periodBound_mono := by
    apply monotone_nat_of_le_succ
    intro l
    change (levelState k N (l + 1)).periodBound ≤ (levelState k N (l + 1 + 1)).periodBound
    rw [levelState_succ (l + 1)]; simp only [levelStep]; exact le_max_right _ _
  terminalLengthBound_mono := by
    apply monotone_nat_of_le_succ
    intro l
    change (levelState k N (l + 1)).terminalLengthBound ≤
        (levelState k N (l + 1 + 1)).terminalLengthBound
    rw [levelState_succ (l + 1)]; simp only [levelStep]; omega
  uncoveredBound_mono := monotone_nat_of_le_succ fun l => by
    change (levelState k N (l + 1)).uncoveredBound ≤ (levelState k N (l + 1 + 1)).uncoveredBound
    rw [levelState_succ_uncoveredBound, levelState_succ_uncoveredBound]
    have := levelEscapeLength_le_succ (k := k) (N := N) l
    exact Nat.mul_le_mul_left _ (by omega)
  escapeLengthBound_mono := monotone_nat_of_le_succ levelEscapeLength_le_succ
  stateCount_le_fixedChainBudget l := Nat.le_add_left _ _
  fixedChainBudget_ge_chainLength l := by
    show (levelState k N (l + 1)).chainLengthBound + N ≤
        (levelState k N (l + 2)).previousChainLengthBound + N
    rw [show l + 2 = (l + 1) + 1 by rfl, levelState_succ (l + 1)]
    simp [levelStep]
  chainLengthBound_ge_cover l := by
    show (levelMultiplicity k N + 1) * (2 * (levelState k N (l + 1)).periodBound) +
        (levelState k N (l + 1)).uncoveredBound +
      (levelState k N (l + 1)).terminalLengthBound ≤ (levelState k N (l + 1)).chainLengthBound
    rw [levelState_succ l]
    simp only [levelStep]
    set e :=
        max (factorLengthBound k N (suffixLengthEnvelope k N
          (List.replicate k (levelMultiplicity k N + N))
          (levelStartWindow N (levelMultiplicity k N) (levelState k N l))))
          (levelState k N l).periodBound
    have : (levelMultiplicity k N + 1) * (2 * e) ≤ (levelMultiplicity k N + 2) * (1 + 2 * e) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  startWindow_gt l := by
    show (N + 1) * (levelState k N (l + 1)).periodBound < levelWindow k N (l + 1)
    unfold levelWindow levelStartWindow
    have : 0 < (levelMultiplicity k N + 2) *
        ((levelState k N (l + 1)).previousChainLengthBound + 1) :=
      Nat.mul_pos (by omega) (by omega)
    omega
  chainWindow_le_startWindow l := by
    show (levelMultiplicity k N + 2) * ((levelState k N (l + 1)).chainLengthBound + 1) ≤
      levelWindow k N (l + 2)
    unfold levelWindow levelStartWindow
    rw [levelState_succ (l + 1)]
    exact Nat.le_add_left _ _
  escapeLengthBound_eq l := rfl
  comparisonWindow_eq l := rfl
  factorLengthBound_le_periodBound l := by
    show _ ≤ (levelState k N (l + 1)).periodBound
    rw [levelState_succ l]; simp only [levelStep]; exact le_max_left _ _
  periodBound_lt_escapeLengthBound hN l := by
    show (levelState k N (l + 1)).periodBound < levelEscapeLength k N l
    rw [levelState_succ l]
    simp only [levelStep, levelEscapeLength, levelWindow]
    apply max_lt (factorLengthBound_suffixLengthEnvelope_lt k N _ _)
    set Ss := List.replicate k (levelMultiplicity k N + N)
    set bs := levelStartWindow N (levelMultiplicity k N) (levelState k N l)
    have h1 := factorLengthBound_suffixLengthEnvelope_lt k N Ss bs
    have h2 := le_suffixLengthEnvelope k N Ss bs
    have h3 := lt_factorLengthBound k N (suffixLengthEnvelope k N Ss bs) hN
    have h4 : (levelState k N l).periodBound ≤ bs := by
      have : (levelState k N l).periodBound ≤ (N + 1) * (levelState k N l).periodBound :=
        Nat.le_mul_of_pos_left _ (by omega)
      exact this.trans (Nat.le_add_right _ _)
    omega
  uncoveredBound_ge_candidateBound l := (levelState_succ_uncoveredBound l).ge
  terminalLengthBound_gt_cover l := by
    show N * (levelState k N (l + 1 + 1)).periodBound +
        (levelState k N (l + 1)).uncoveredBound +
      (levelMultiplicity k N + 1) * (2 * (levelState k N (l + 1 + 1)).periodBound) <
          (levelState k N (l + 1 + 1)).terminalLengthBound
    rw [levelState_succ (l + 1)]
    simp only [levelStep]
    set e :=
        max (factorLengthBound k N (suffixLengthEnvelope k N
          (List.replicate k (levelMultiplicity k N + N))
          (levelStartWindow N (levelMultiplicity k N) (levelState k N (l + 1)))))
          (levelState k N (l + 1)).periodBound
    have : (levelMultiplicity k N + 1) * (2 * e) ≤ (levelMultiplicity k N + 3) * (3 * e) :=
        Nat.mul_le_mul (by omega) (by omega)
    omega
  terminalLengthBound_ge_periodBudget l := by
    show 1 + ((levelState k N (l + 1)).previousChainLengthBound + N) *
        ((levelState k N (l + 1)).periodBound * N.factorial) +
      2 * ((levelState k N (l + 1)).periodBound * N.factorial) + N *
          (levelState k N (l + 1)).periodBound ≤
      (levelState k N (l + 1)).terminalLengthBound
    rw [levelState_succ l]
    simp only [levelStep]
    omega
structure PeriodicFactor where
  /-- First position of the factor. -/
  start : ℕ
  /-- Position immediately after the factor. -/
  stop : ℕ
  /-- Period assigned to the factor. -/
  period : ℕ
  deriving DecidableEq
def PeriodicFactor.Valid (w : List α) (E : ℕ) (f : PeriodicFactor) : Prop :=
  0 < f.period ∧ f.period ≤ E ∧ f.stop ≤ w.length ∧ PeriodicOn w f.period f.start f.stop
def Covers (fs : List PeriodicFactor) (x : ℕ) : Prop := ∃ f ∈ fs, f.start ≤ x ∧ x < f.stop
instance (fs : List PeriodicFactor) (x : ℕ) : Decidable (Covers fs x) :=
  inferInstanceAs (Decidable (∃ f ∈ fs, _))
def uncoveredPositions (fs : List PeriodicFactor) (J n : ℕ) : Finset ℕ :=
  (Finset.Ico J n).filter (fun x => ¬ Covers fs x)
def PeriodicCover (w : List α) (J P E T : ℕ) : Prop :=
  ∃ fs : List PeriodicFactor, fs.length ≤ P ∧ (∀ f ∈ fs, f.Valid w E) ∧
      (uncoveredPositions fs J w.length).card ≤ T
def HasTerminalPeriod (E : ℕ) (w : List α) (s : ℕ) : Prop :=
  ∃ p ∈ Finset.Icc 1 E, (w.drop s).HasPeriod p
instance [DecidableEq α] (E : ℕ) (w : List α) : DecidablePred (HasTerminalPeriod E w) :=
  fun _ => inferInstanceAs (Decidable (∃ p ∈ _, _))
def longestPeriodicSuffixLength [DecidableEq α] (E : ℕ) (w : List α) : ℕ :=
  ((Finset.range (w.length + 1)).filter (HasTerminalPeriod E w)).sup (fun s => w.length - s)
section LevelProperties
variable {σ N : ℕ}
def CoordinateCover (C : LevelBounds σ k N) (l : ℕ) (M : StructuralReader α S k)
    (W : Fin k → List α)
    (i : Fin k) : Prop :=
  PeriodicCover (W i) (M.firstRejection W i) (C.pieceCountBase + 1) (C.periodBound l)
      (C.uncoveredBound l)
def LevelCoverProperty [DecidableEq α] (C : LevelBounds σ k N) (l : ℕ) (M : StructuralReader α S k)
    (W : Fin k → List α) (i : Fin k) : Prop :=
  CoordinateCover C l M W i ∧ longestPeriodicSuffixLength (C.periodBound l) (W i) <
      C.terminalLengthBound l
end LevelProperties
section FirstRejection
variable {M : StructuralReader α S k} {W : Fin k → List α} {i : Fin k}
end FirstRejection
section Monotonicity
variable {σ : ℕ} [DecidableEq α] [Fintype S]
end Monotonicity
section Stable
variable {σ : ℕ} [DecidableEq α] [Fintype S]
end Stable
section Chains
variable {σ : ℕ} [DecidableEq α] [Fintype S] [DecidableEq S]
end Chains
end DeciSigma1.Holes.Tail


