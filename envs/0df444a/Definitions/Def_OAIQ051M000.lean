-- Prove2me | Definitions.Def_OAIQ051M000
-- name    : OAIQ051M000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T17:12:51.589347+00:00
-- url     : https://prove2.me/theorems/1caf8bc1-b5f0-47db-881e-b7cadd446a40
-- title:
--   Definitions bundle OAIQ051M000 of the split of OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 833 declarations of OpenAI's Lean: 390 definitions, 22 inductive types or structures, 13 instances and 408 theorems. The definitions and types are `OAI.MatchingFPRAS.Adaptive.Law`, `OAI.MatchingFPRAS.Adaptive.Law.event`, `OAI.MatchingFPRAS.Adaptive.Law.iid`, `OAI.MatchingFPRAS.Adaptive.Law.sigma`, `OAI.MatchingFPRAS.AlphabetCost.supportedWrites`, `OAI.MatchingFPRAS.AlphabetCost.writesCount`, `OAI.MatchingFPRAS.Amplification.halfRepetitions`, `OAI.MatchingFPRAS.Amplification.median`, `OAI.MatchingFPRAS.Amplification.sortedList`, `OAI.MatchingFPRAS.Amplification.sortedValue`, `OAI.MatchingFPRAS.BinaryArithmeticProc.add`, `OAI.MatchingFPRAS.BinaryArithmeticProc.addEntry`, `OAI.MatchingFPRAS.BinaryArithmeticProc.compare`, `OAI.MatchingFPRAS.BinaryArithmeticProc.compareEntry`, `OAI.MatchingFPRAS.BinaryArithmeticProc.less`, `OAI.MatchingFPRAS.BinaryArithmeticProc.pickLt`, `OAI.MatchingFPRAS.BinaryArithmeticProc.sub`, `OAI.MatchingFPRAS.BinaryArithmeticProc.subEntry`, `OAI.MatchingFPRAS.BinaryNormalize.normalize`, `OAI.MatchingFPRAS.BinaryNormalize.program`, `OAI.MatchingFPRAS.BinaryNormalize.stripProgram`, `OAI.MatchingFPRAS.BinaryNormalize.stripRaw`, `OAI.MatchingFPRAS.BinaryNormalize.swap01`, `OAI.MatchingFPRAS.BitArithmetic.FractionBound`, `OAI.MatchingFPRAS.BitArithmetic.GridFraction`, `OAI.MatchingFPRAS.BitArithmetic.matrixBound`, `OAI.MatchingFPRAS.BitComplexity.PolynomiallyBounded`, `OAI.MatchingFPRAS.BitComplexity.boundD`, `OAI.MatchingFPRAS.BitComplexity.boundK`, `OAI.MatchingFPRAS.BitComplexity.boundN`, `OAI.MatchingFPRAS.BitComplexity.boundS`, `OAI.MatchingFPRAS.BoolPostCompiler.down`, `OAI.MatchingFPRAS.BoolPostCompiler.up`, `OAI.MatchingFPRAS.BottleneckAlgorithm.advance`, `OAI.MatchingFPRAS.BottleneckAlgorithm.close`, `OAI.MatchingFPRAS.BottleneckAlgorithm.edge`, `OAI.MatchingFPRAS.BottleneckAlgorithm.seed`, `OAI.MatchingFPRAS.Cells.ArcData`, `OAI.MatchingFPRAS.Cells.ArcData.Admissible`, `OAI.MatchingFPRAS.Cells.ArcData.Good` and 372 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/MatchingCount, in whole or in part: `MatchingCount_Algorithm_EmpiricalDenom`, `MatchingCount_Algorithm_Guard`, `MatchingCount_Algorithm_OutputLengthBound`, `MatchingCount_Algorithm_RationalScale`, `MatchingCount_Algorithm_RelabelWeights`, `MatchingCount_Algorithm_SortedList`, `MatchingCount_Algorithm_TreeScaling`, `MatchingCount_Algorithm_TreeStageActivity`, `MatchingCount_Arithmetic_ArithmeticSize`, `MatchingCount_Arithmetic_BinaryAddition`, `MatchingCount_Arithmetic_BinaryCompare`, `MatchingCount_Arithmetic_BinaryNormalize`, `MatchingCount_Arithmetic_BinarySubtract`, `MatchingCount_Arithmetic_SubtractProc`, `MatchingCount_Arithmetic_TreeAdaptiveArithmetic`, `MatchingCount_Arithmetic_TreeCompare`, `MatchingCount_Arithmetic_TreeFraction`, `MatchingCount_Arithmetic_TreeFractionExtra`, `MatchingCount_Arithmetic_TreeNumberOps`, `MatchingCount_Complexity_AlphabetCompilerCost`, `MatchingCount_Complexity_GuardMachineBase`, `MatchingCount_Graphs_ArcData`, `MatchingCount_Graphs_ColoredEdge`, `MatchingCount_Graphs_CompleteGraph`, `MatchingCount_Graphs_Edge`, `MatchingCount_Graphs_EdgeLow`, `MatchingCount_Graphs_FillHoles`, `MatchingCount_Graphs_FirstHoleSortedCons`, `MatchingCount_Graphs_Height`, `MatchingCount_Graphs_HoleBlocks`, `MatchingCount_Graphs_HoleStrength`, `MatchingCount_Graphs_Incident`, `MatchingCount_Graphs_Marked`, `MatchingCount_Graphs_MatchingMap`, `MatchingCount_Graphs_Mate`, `MatchingCount_Graphs_PM`, `MatchingCount_Graphs_PathActivity`, `MatchingCount_Graphs_PathStrength`, `MatchingCount_Graphs_Profile`, `MatchingCount_Graphs_RatWeight`, `MatchingCount_Graphs_Related`, `MatchingCount_Graphs_RemainingBags`, `MatchingCount_Graphs_RowPeak`, `MatchingCount_Graphs_Sets`, `MatchingCount_Graphs_SumLiftMate`, `MatchingCount_Graphs_ThresholdGraph`, `MatchingCount_Graphs_TreeGeometry`, `MatchingCount_Graphs_Vertex`, `MatchingCount_Machines_BoolPostCompiler`, `MatchingCount_Machines_CoinTM1`, `MatchingCount_Machines_CoinTM1Finite`, `MatchingCount_Machines_FiniteStore`, `MatchingCount_Machines_PhysicalPost`, `MatchingCount_Machines_PhysicalRestriction`, `MatchingCount_Machines_RegisterControl`, `MatchingCount_Machines_RegisterProc`, `MatchingCount_Machines_RegisterStructured`, `MatchingCount_Machines_RegisterTree`, `MatchingCount_Machines_SupportedCompiler`, `MatchingCount_Machines_TableLookup`, `MatchingCount_Machines_TreeChoice`, `MatchingCount_Machines_TreeFold`, `MatchingCount_Machines_TreeFunction`, `MatchingCount_Machines_TreeList`, `MatchingCount_Machines_TreeLookup`, `MatchingCount_Machines_TreeMachine`, `MatchingCount_Machines_TreeSlotWeight`, `MatchingCount_Machines_TreeTransfer`, `MatchingCount_Machines_TreeTyped`, `MatchingCount_Probability_AdaptiveLaw`, `MatchingCount_Probability_FinitePMF`, `MatchingCount_Probability_Tv`, `MatchingCount_Sampling_Certify`, `MatchingCount_Sampling_ChosenChord`, `MatchingCount_Sampling_DiscreteLadderSteps`, `MatchingCount_Sampling_Endpoints`, `MatchingCount_Sampling_Sym2Order`, `MatchingCount_Tapes_CoinAlphabet`, `MatchingCount_Tapes_CoinStack`, `MatchingCount_Tapes_CoinSupport`, `MatchingCount_Tapes_RunBits`, `MatchingCount_Tapes_StackEmbedding`, `MatchingCount_Tapes_StackLens`, `MatchingCount_Tapes_TreeBits`, `MatchingCount_Tapes_WordOps`.
--
--   **Imports.** It imports the published bundle `Def_MatchingFPRAS`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ051M002` and `OAIQ051M003`.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/MatchingCount at commit adc7f12

import Mathlib
import Definitions.Def_MatchingFPRAS

section
-- module Solutions.OAIQ051_MC.Compat
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
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_ColoredEdge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

variable {V L : Type*}

abbrev ColoredEdge (V L : Type*) := {e : Sym2 V × L // ¬ e.1.IsDiag}

namespace ColoredEdge

variable (e : ColoredEdge V L)

def Incident (v : V) : Prop := v ∈ e.val.1

def color : L := e.val.2

end ColoredEdge

def Allowed (bags : V → Finset L) (e : ColoredEdge V L) : Prop :=
  ∀ v, e.Incident v → e.color ∈ bags v

abbrev BagEdge (bags : V → Finset L) := {e : ColoredEdge V L // Allowed bags e}

namespace BagEdge

variable {bags : V → Finset L}

def Incident (e : BagEdge bags) (v : V) : Prop := e.val.Incident v

end BagEdge

variable {E : Type*} [DecidableEq V] [DecidableEq E] (inc : E → V → Prop)

def MatchingOn (M : Finset E) (U : Finset V) : Prop :=
  (∀ e ∈ M, ∀ v, inc e v → v ∈ U) ∧
  (∀ v ∈ U, ∃! e, e ∈ M ∧ inc e v)

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Mate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Switching

open Finset
open scoped Classical symmDiff

abbrev Mate (V : Type*) := {m : V → V // Function.Involutive m}

variable {V : Type*}

@[simp] theorem mate_mate (m : Mate V) (v : V) : m.1 (m.1 v) = v := m.2 v

def overlay (m n : Mate V) : SimpleGraph V where
  Adj v w := (m.1 v = w ∧ v ≠ w) ∨ (n.1 v = w ∧ v ≠ w)
  symm := ⟨by
    intro v w h
    rcases h with ⟨h, hne⟩ | ⟨h, hne⟩
    · exact Or.inl ⟨by rw [← h, mate_mate], Ne.symm hne⟩
    · exact Or.inr ⟨by rw [← h, mate_mate], Ne.symm hne⟩⟩
  loopless := ⟨by intro v; simp⟩

@[simp] theorem overlay_adj (m n : Mate V) (v w : V) :
    (overlay m n).Adj v w ↔ (m.1 v = w ∧ v ≠ w) ∨ (n.1 v = w ∧ v ≠ w) := Iff.rfl

theorem overlay_comm (m n : Mate V) : overlay m n = overlay n m := by
  ext v w
  exact or_comm

theorem reachable_mate_left (m n : Mate V) (v : V) :
    (overlay m n).Reachable v (m.1 v) := by
  by_cases hv : m.1 v = v
  · rw [hv]
  · exact (show (overlay m n).Adj v (m.1 v) from Or.inl ⟨rfl, Ne.symm hv⟩).reachable

theorem reachable_mate_left_iff (m n : Mate V) (a v : V) :
    (overlay m n).Reachable a (m.1 v) ↔ (overlay m n).Reachable a v := by
  constructor
  · intro h
    exact h.trans (reachable_mate_left m n v).symm
  · intro h
    exact h.trans (reachable_mate_left m n v)

theorem reachable_mate_right_iff (m n : Mate V) (a v : V) :
    (overlay m n).Reachable a (n.1 v) ↔ (overlay m n).Reachable a v := by
  rw [overlay_comm]
  exact reachable_mate_left_iff n m a v

noncomputable def switched (m n : Mate V) (a : V) : Mate V := by
  classical
  refine ⟨fun v => if (overlay m n).Reachable a v then n.1 v else m.1 v, ?_⟩
  intro v
  by_cases h : (overlay m n).Reachable a v
  · simp [h, reachable_mate_right_iff]
  · simp [h, reachable_mate_left_iff]

@[simp] theorem switched_apply (m n : Mate V) (a v : V) :
    (switched m n a).1 v =
      if (overlay m n).Reachable a v then n.1 v else m.1 v := by
  classical
  rfl

def restrictMate (m : Mate V) (S : Set V)
    (hS : ∀ v, m.1 v ∈ S ↔ v ∈ S) : Mate S :=
  ⟨fun v => ⟨m.1 v.1, (hS v.1).mpr v.2⟩,
   by intro v; apply Subtype.ext; exact m.2 v.1⟩

@[simp] theorem restrictMate_apply (m : Mate V) (S : Set V)
    (hS : ∀ v, m.1 v ∈ S ↔ v ∈ S) (v : S) :
    ((restrictMate m S hS).1 v).1 = m.1 v.1 := rfl

@[simp] theorem component_mem_iff (m n : Mate V) (a v : V) :
    v ∈ ((overlay m n).connectedComponentMk a).supp ↔ (overlay m n).Reachable a v := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq,
    SimpleGraph.reachable_comm]

noncomputable def weight [Fintype V] [LinearOrder V] (w : V → V → ℝ)
    (m : Mate V) : ℝ := ∏ v, if v < m.1 v then w v (m.1 v) else 1

def HasHoles (m : Mate V) (U : Finset V) : Prop := ∀ v, m.1 v = v ↔ v ∈ U

noncomputable def matchings [Fintype V] (U : Finset V) : Finset (Mate V) :=
  Finset.univ.filter (fun m => HasHoles m U)

@[simp] theorem mem_matchings [Fintype V] (m : Mate V) (U : Finset V) :
    m ∈ matchings U ↔ HasHoles m U := by simp [matchings]

noncomputable def partition [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (U : Finset V) : ℝ := ∑ m ∈ matchings U, weight w m

end MatchingFPRAS.Switching

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Edge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Switching
open Finset
open scoped Classical symmDiff

variable {V : Type*}

noncomputable def withEdge (m : Mate V) (a b : V) : Mate V := by
  classical
  by_cases h : m.1 a = a ∧ m.1 b = b
  · refine ⟨fun v => if v = a then b else if v = b then a else m.1 v, ?_⟩
    intro v
    by_cases hva : v = a
    · subst v
      by_cases hab : a = b <;> simp [hab]
    by_cases hvb : v = b
    · subst v
      by_cases hab : a = b <;> simp [hab, hva]
    have hma : m.1 v ≠ a := by
      intro hv
      have he := congrArg m.1 hv
      rw [mate_mate, h.1] at he
      exact hva he
    have hmb : m.1 v ≠ b := by
      intro hv
      have he := congrArg m.1 hv
      rw [mate_mate, h.2] at he
      exact hvb he
    simp [hva, hvb, hma, hmb]
  · exact m

@[simp] theorem withEdge_apply (m : Mate V) (a b v : V)
    (ha : m.1 a = a) (hb : m.1 b = b) :
    (withEdge m a b).1 v = if v = a then b else if v = b then a else m.1 v := by
  classical
  simp [withEdge, ha, hb]

def edgeActivity [LinearOrder V] (w : V → V → ℝ) (a b : V) : ℝ :=
  if a < b then w a b else w b a

theorem edgeActivity_comm [LinearOrder V] (w : V → V → ℝ) (a b : V) :
    edgeActivity w a b = edgeActivity w b a := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp [edgeActivity, h, h.not_gt]
  · rfl
  · simp [edgeActivity, h, h.not_gt]

noncomputable def holeRatio [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (U : Finset V) : ℝ := partition w U / partition w ∅

noncomputable def rowMax [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ) (a : V) : ℝ :=
  ((Finset.univ.erase a).sup' (by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
    omega) fun b => holeRatio w {a,b})

end MatchingFPRAS.Switching

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_PathStrength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Switching
open Finset
open scoped Classical symmDiff

variable {V : Type*}

noncomputable def pathStrength [LinearOrder V] (w : V → V → ℝ) {a b : V}
    (hab : a ≠ b) (p : (⊤ : SimpleGraph V).Path a b) : ℝ :=
  p.val.darts.toFinset.inf' (by
    obtain ⟨d,hd⟩ := List.exists_mem_of_ne_nil p.val.darts
      (fun h => hab ((SimpleGraph.Walk.darts_eq_nil.mp h).eq))
    exact ⟨d,List.mem_toFinset.mpr hd⟩)
    (fun d => edgeActivity w d.fst d.snd)

noncomputable def bottleneck [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a b : V) : ℝ :=
  if hab : a = b then 1 else
    max 1 ((Finset.univ : Finset ((⊤ : SimpleGraph V).Path a b)).sup'
      (by exact ⟨SimpleGraph.Path.singleton (by simpa using hab), Finset.mem_univ _⟩)
      (pathStrength w hab))

theorem one_le_bottleneck [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a b : V) : 1 ≤ bottleneck w a b := by
  unfold bottleneck
  split_ifs
  · rfl
  · exact le_max_left _ _

theorem walk_isChain_of_darts [LinearOrder V] {G : SimpleGraph V}
    (w : V → V → ℝ) (B : ℝ) {a b : V} (p : G.Walk a b)
    (h : ∀ d ∈ p.darts, B ≤ edgeActivity w d.fst d.snd) :
    List.IsChain (fun x y => B ≤ edgeActivity w x y) p.support := by
  induction p with
  | nil => simp
  | @cons a c b hadj p ih =>
    rw [SimpleGraph.Walk.support_cons, ← p.cons_tail_support]
    apply List.isChain_cons_cons.mpr
    constructor
    · exact h ⟨(a,c),hadj⟩ (by simp)
    · rw [p.cons_tail_support]
      apply ih
      intro d hd
      exact h d (by simp [hd])

theorem bottleneck_path [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a b : V) (hab : a ≠ b) (hB : 1 < bottleneck w a b) :
    ∃ L : List V,
      List.IsChain (fun x y => bottleneck w a b ≤ edgeActivity w x y) (a :: L) ∧
      (a :: L).Nodup ∧ b ∈ L := by
  obtain ⟨p,hp,hmax⟩ := Finset.exists_mem_eq_sup'
    (show (Finset.univ : Finset ((⊤ : SimpleGraph V).Path a b)).Nonempty from
      ⟨SimpleGraph.Path.singleton (by simpa using hab), Finset.mem_univ _⟩)
    (pathStrength w hab)
  have he : bottleneck w a b = pathStrength w hab p := by
    unfold bottleneck at hB ⊢
    rw [dite_eq_right hab, hmax] at hB ⊢
    exact max_eq_right ((lt_max_iff.mp hB).resolve_left (lt_irrefl 1)).le
  have hd : ∀ d ∈ p.val.darts, bottleneck w a b ≤ edgeActivity w d.fst d.snd := by
    intro d hd
    rw [he]
    exact Finset.inf'_le _ (List.mem_toFinset.mpr hd)
  refine ⟨p.val.support.tail, ?_, ?_, ?_⟩
  · rw [p.val.cons_tail_support]
    exact walk_isChain_of_darts w _ p.val hd
  · rw [p.val.cons_tail_support]
    exact p.property.support_nodup
  · exact p.val.end_mem_tail_support_of_ne hab

noncomputable def erasePair (m : Mate V) (a b : V) : Mate V := by
  classical
  by_cases h : m.1 a = b
  · refine ⟨fun v => if v = a ∨ v = b then v else m.1 v, ?_⟩
    intro v
    have hba : m.1 b = a := by rw [← h, mate_mate]
    by_cases hv : v = a ∨ v = b
    · simp [hv]
    · have hma : m.1 v ≠ a := by
        intro he
        have hh := congrArg m.1 he
        rw [mate_mate, h] at hh
        exact hv (Or.inr hh)
      have hmb : m.1 v ≠ b := by
        intro he
        have hh := congrArg m.1 he
        rw [mate_mate, hba] at hh
        exact hv (Or.inl hh)
      simp [hv, hma, hmb, mate_mate]
  · exact m

@[simp] theorem erasePair_apply (m : Mate V) (a b v : V) (h : m.1 a = b) :
    (erasePair m a b).1 v = if v = a ∨ v = b then v else m.1 v := by
  classical
  simp [erasePair, h]

end MatchingFPRAS.Switching

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_FillHoles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Switching
open Finset
open scoped Classical symmDiff

variable {V : Type*}
theorem mate_mem_holes_iff [DecidableEq V] (m : Mate V) (S : Finset V)
    (hm : HasHoles m S) (v : V) : m.1 v ∈ S ↔ v ∈ S := by
  rw [← hm (m.1 v), ← hm v, mate_mate]
  exact eq_comm

noncomputable def fillHoles [Fintype V] [DecidableEq V] (m q : Mate V) (S : Finset V)
    (hm : HasHoles m S) (hq : HasHoles q Sᶜ) : Mate V := by
  classical
  refine ⟨fun v => if v ∈ S then q.1 v else m.1 v, ?_⟩
  intro v
  by_cases hv : v ∈ S
  · have hqv : q.1 v ∈ S := by
      have h := mate_mem_holes_iff q Sᶜ hq v
      have he : q.1 v ∈ S ↔ v ∈ S := by
        simpa only [Finset.mem_compl, not_iff_not] using h
      exact he.mpr hv
    simp [hv,hqv,mate_mate]
  · have hmv : m.1 v ∉ S := fun h => hv ((mate_mem_holes_iff m S hm v).mp h)
    simp [hv,hmv,mate_mate]

@[simp] theorem fillHoles_apply [Fintype V] [DecidableEq V] (m q : Mate V) (S : Finset V)
    (hm : HasHoles m S) (hq : HasHoles q Sᶜ) (v : V) :
    (fillHoles m q S hm hq).1 v = if v ∈ S then q.1 v else m.1 v := rfl

end MatchingFPRAS.Switching

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_ThresholdGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Switching

open Finset

variable {V : Type*}

lemma edgeActivity_of_symmetric [LinearOrder V] (B : V → V → ℝ)
    (hB : ∀ a b, B a b = B b a) (a b : V) : edgeActivity B a b = B a b := by
  unfold edgeActivity
  split_ifs
  · rfl
  · exact hB b a

def thresholdGraph [LinearOrder V] (w : V → V → ℝ) (t : ℝ) : SimpleGraph V where
  Adj a b := a ≠ b ∧ t ≤ edgeActivity w a b
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm,by simpa only [edgeActivity_comm w b a] using h.2⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

lemma strong_walk_reachable [LinearOrder V] (w : V → V → ℝ) (t : ℝ)
    {a b : V} (p : (⊤ : SimpleGraph V).Walk a b)
    (hp : ∀ d ∈ p.darts, t ≤ edgeActivity w d.fst d.snd) :
    (thresholdGraph w t).Reachable a b := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a c b hac p ih =>
    have he : t ≤ edgeActivity w a c := hp ⟨(a,c),hac⟩ (by simp)
    have htail : ∀ d ∈ p.darts, t ≤ edgeActivity w d.fst d.snd := by
      intro d hd
      exact hp d (by simp [hd])
    exact (SimpleGraph.Adj.reachable (G := thresholdGraph w t)
      ⟨by simpa using hac,he⟩).trans (ih htail)

lemma threshold_map_strong [LinearOrder V] (w : V → V → ℝ) (t : ℝ)
    {a b : V} (p : (thresholdGraph w t).Walk a b) :
    ∀ d ∈ (p.map (SimpleGraph.Hom.ofLE le_top)).darts,
      t ≤ edgeActivity w d.fst d.snd := by
  intro d hd
  rw [SimpleGraph.Walk.darts_map] at hd
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
  exact e.adj.2

theorem bottleneck_threshold [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a b : V) (hab : a ≠ b) (t : ℝ) (ht : 1 < t) :
    t ≤ bottleneck w a b ↔ (thresholdGraph w t).Reachable a b := by
  classical
  constructor
  · intro h
    obtain ⟨p,hp,hmax⟩ := Finset.exists_mem_eq_sup'
      (show (Finset.univ : Finset ((⊤ : SimpleGraph V).Path a b)).Nonempty from
        ⟨SimpleGraph.Path.singleton (by simpa using hab), Finset.mem_univ _⟩)
      (pathStrength w hab)
    have he : t ≤ pathStrength w hab p := by
      unfold bottleneck at h
      rw [dite_eq_right hab,hmax] at h
      exact (le_max_iff.mp h).resolve_left (not_le_of_gt ht)
    apply strong_walk_reachable w t p.val
    intro d hd
    exact he.trans (Finset.inf'_le _ (List.mem_toFinset.mpr hd))
  · intro h
    obtain ⟨p,hp⟩ := h.exists_isPath
    let q : (⊤ : SimpleGraph V).Path a b :=
      ⟨p.map (SimpleGraph.Hom.ofLE le_top),hp.map Function.injective_id⟩
    have hstr : t ≤ pathStrength w hab q := by
      apply Finset.le_inf'
      intro d hd
      exact threshold_map_strong w t p d (List.mem_toFinset.mp hd)
    unfold bottleneck
    rw [dite_eq_right hab]
    exact hstr.trans ((Finset.le_sup' _ (Finset.mem_univ q)).trans (le_max_right _ _))

theorem bottleneck_comm [Fintype V] [LinearOrder V] (w : V → V → ℝ) (a b : V) :
    bottleneck w a b = bottleneck w b a := by
  by_cases hab : a = b
  · subst b; rfl
  apply le_antisymm
  · by_cases h : 1 < bottleneck w a b
    · exact (bottleneck_threshold w b a (Ne.symm hab) _ h).mpr
        (((bottleneck_threshold w a b hab _ h).mp le_rfl).symm)
    · exact (le_of_not_gt h).trans (one_le_bottleneck w b a)
  · by_cases h : 1 < bottleneck w b a
    · exact (bottleneck_threshold w a b hab _ h).mpr
        (((bottleneck_threshold w b a (Ne.symm hab) _ h).mp le_rfl).symm)
    · exact (le_of_not_gt h).trans (one_le_bottleneck w a b)

theorem bottleneck_ultrametric [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    min (bottleneck w a c) (bottleneck w c b) ≤ bottleneck w a b := by
  let t := min (bottleneck w a c) (bottleneck w c b)
  by_cases ht : 1 < t
  · apply (bottleneck_threshold w a b hab t ht).mpr
    exact ((bottleneck_threshold w a c hac t ht).mp (min_le_left _ _)).trans
      ((bottleneck_threshold w c b hbc.symm t ht).mp (min_le_right _ _))
  · exact (le_of_not_gt ht).trans (one_le_bottleneck w a b)

theorem edgeActivity_le_bottleneck [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a b : V) (hab : a ≠ b) :
    edgeActivity w a b ≤ bottleneck w a b := by
  by_cases h : 1 < edgeActivity w a b
  · exact (bottleneck_threshold w a b hab _ h).mpr
      (SimpleGraph.Adj.reachable (G := thresholdGraph w _) ⟨hab,le_rfl⟩)
  · exact (le_of_not_gt h).trans (one_le_bottleneck w a b)

theorem bottleneck_le_row_bound [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a : V) (T : ℝ) (hT : 1 ≤ T)
    (hrow : ∀ b, a ≠ b → edgeActivity w a b ≤ T) (b : V) :
    bottleneck w a b ≤ T := by
  by_cases hab : a = b
  · subst b; simpa [bottleneck] using hT
  by_cases hB : 1 < bottleneck w a b
  · obtain ⟨L,hL,hnd,hb⟩ := bottleneck_path w a b hab hB
    cases L with
    | nil => simp at hb
    | cons c L =>
      have hne : a ≠ c := by
        have h := (List.nodup_cons.mp hnd).1
        simp only [List.mem_cons,not_or] at h
        exact h.1
      have he := (List.isChain_cons_cons.mp hL).1
      exact he.trans (hrow c hne)
  · exact (le_of_not_gt hB).trans hT

theorem bottleneck_eq_of_threshold_iff
    {W : Type*} [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (w : V → V → ℝ) (w' : W → W → ℝ) (a b : V) (a' b' : W)
    (hab : a ≠ b) (hab' : a' ≠ b')
    (h : ∀ t : ℝ, 1 < t →
      ((thresholdGraph w t).Reachable a b ↔ (thresholdGraph w' t).Reachable a' b')) :
    bottleneck w a b = bottleneck w' a' b' := by
  apply le_antisymm
  · by_cases ht : 1 < bottleneck w a b
    · exact (bottleneck_threshold w' a' b' hab' _ ht).mpr
        ((h _ ht).mp ((bottleneck_threshold w a b hab _ ht).mp le_rfl))
    · exact (le_of_not_gt ht).trans (one_le_bottleneck w' a' b')
  · by_cases ht : 1 < bottleneck w' a' b'
    · exact (bottleneck_threshold w a b hab _ ht).mpr
        ((h _ ht).mpr ((bottleneck_threshold w' a' b' hab' _ ht).mp le_rfl))
    · exact (le_of_not_gt ht).trans (one_le_bottleneck w a b)

end MatchingFPRAS.Switching

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_SumLiftMate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Switching

section

open Finset

variable {V W : Type*}

def sumLiftMate (m : Mate V) : Mate (V ⊕ W) :=
  ⟨Sum.map m.val id,by intro x; cases x <;> simp⟩

@[simp] lemma sumLiftMate_inl (m : Mate V) (a : V) :
    (sumLiftMate (W := W) m).val (Sum.inl a)=Sum.inl (m.val a) := rfl

@[simp] lemma sumLiftMate_inr (m : Mate V) (a : W) :
    (sumLiftMate m).val (Sum.inr a)=(Sum.inr a : V ⊕ W) := rfl

end

end MatchingFPRAS.Switching

namespace MatchingFPRAS.Subdivision

open Finset

abbrev Selection (m : ℕ) := Fin (m+1) → Bool

def Valid {m : ℕ} (holes : Finset (Fin m)) (b : Selection m) : Prop :=
  ∀ i : Fin m, if i ∈ holes then b i.castSucc = false ∧ b i.succ = false
    else b i.castSucc ≠ b i.succ

def alternating (a : Bool) (i : ℕ) : Bool := if i % 2 = 0 then a else !a

@[simp] theorem alternating_zero (a : Bool) : alternating a 0 = a := by
  simp [alternating]

@[simp] theorem alternating_succ (a : Bool) (i : ℕ) :
    alternating a (i+1) = !(alternating a i) := by
  by_cases h : i % 2 = 0
  · have hs : (i+1)%2 = 1 := by omega
    simp [alternating,h,hs]
  · have hs : i%2=1 := by omega
    have ht : (i+1)%2=0 := by omega
    simp [alternating,hs,ht]

@[simp] theorem alternating_add_two (a : Bool) (i : ℕ) :
    alternating a (i+2) = alternating a i := by
  rw [show i+2=(i+1)+1 by omega, alternating_succ, alternating_succ]
  simp

lemma bool_ne_iff_eq_not (a b : Bool) : a ≠ b ↔ b = !a := by
  cases a <;> cases b <;> simp

theorem intact_iff {m : ℕ} (b : Selection m) :
    Valid ∅ b ↔ ∀ i : Fin (m+1), b i = alternating (b 0) i.val := by
  constructor
  · intro h i
    have hstep (j : Fin m) : b j.succ = !(b j.castSucc) := by
      apply (bool_ne_iff_eq_not _ _).mp
      simpa [Valid] using h j
    have aux (k : ℕ) (hk : k < m+1) : b ⟨k,hk⟩ = alternating (b 0) k := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [alternating_succ]
        have hk' : k < m := by omega
        have he := hstep ⟨k,hk'⟩
        simpa only [Fin.succ_mk, Fin.castSucc_mk, ih (by omega)] using he
    exact aux i.val i.isLt
  · intro h i
    simp only [Finset.notMem_empty, ↓reduceIte]
    rw [h i.castSucc, h i.succ]
    simp only [Fin.val_castSucc, Fin.val_succ, alternating_succ]
    cases alternating (b 0) i.val <;> decide

theorem intact_terminals {m : ℕ} (hm : Even m) (b : Selection m)
    (h : Valid ∅ b) : b (Fin.last m) = b 0 := by
  rw [(intact_iff b).mp h]
  simp [alternating, Nat.even_iff.mp hm]

theorem alternating_valid (m : ℕ) (a : Bool) :
    Valid ∅ (fun i : Fin (m+1) => alternating a i.val) := by
  apply (intact_iff _).mpr
  intro i
  simp

@[simp] theorem alternating_not (a : Bool) (i : ℕ) :
    alternating (!a) i = !(alternating a i) := by
  unfold alternating
  split_ifs <;> simp

def duplicate (xs : List ℝ) : List ℝ := xs.flatMap (fun x => [x,x])

@[simp] theorem duplicate_nil : duplicate [] = [] := rfl

@[simp] theorem duplicate_cons (x : ℝ) (xs : List ℝ) :
    duplicate (x::xs) = x::x::duplicate xs := by simp [duplicate]

@[simp] theorem duplicate_length (xs : List ℝ) :
    (duplicate xs).length = 2*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

end MatchingFPRAS.Subdivision

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Profile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Subdivision

open Finset

noncomputable def profile (p : ℕ) (B Hu Hv lam : ℝ) : List ℝ :=
  duplicate (List.ofFn fun r : Fin p => max B (Hu / 2^r.val)) ++ [lam] ++
    duplicate ((List.ofFn fun r : Fin p => max B (Hv / 2^r.val)).reverse)

@[simp] theorem profile_length (p : ℕ) (B Hu Hv lam : ℝ) :
    (profile p B Hu Hv lam).length = 4*p+1 := by simp [profile]; omega

noncomputable def profileActivity (p : ℕ) (B Hu Hv lam : ℝ) (i : Fin (4*p+1)) : ℝ :=
  (profile p B Hu Hv lam).get (i.cast (profile_length p B Hu Hv lam).symm)

section Deletion

variable {V E : Type*} [Fintype V] [Fintype E]

def Uses {m : ℕ} (u v : E → V) (b : E → Selection m) (e : E) (x : V) : Prop :=
  (b e 0 = true ∧ u e = x) ∨ (b e (Fin.last m) = true ∧ v e = x)

def FamilyHoles (u v : E → V) (m : ℕ) (R₀ : Finset V) (U : E → Finset (Fin m))
    (b : E → Selection m) : Prop :=
  (∀ e, Valid (U e) (b e)) ∧
  (∀ x ∈ R₀, ∀ e, ¬ Uses u v b e x) ∧
  (∀ x ∉ R₀, ∃! e, Uses u v b e x)

noncomputable def broken {m : ℕ} (U : E → Finset (Fin m)) : Finset E := by
  classical
  exact Finset.univ.filter fun e => (U e).Nonempty

@[simp] lemma mem_broken {m : ℕ} (U : E → Finset (Fin m)) (e : E) :
    e ∈ broken U ↔ (U e).Nonempty := by
  classical
  simp [broken]

noncomputable def residualHoles {m : ℕ} (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (b : E → Selection m) : Finset V := by
  classical
  exact R₀ ∪ Finset.univ.filter (fun x => ∃ e ∈ broken U, Uses u v b e x)

@[simp] lemma mem_residualHoles {m : ℕ} (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (b : E → Selection m) (x : V) :
    x ∈ residualHoles u v R₀ U b ↔ x ∈ R₀ ∨ ∃ e ∈ broken U, Uses u v b e x := by
  classical
  simp [residualHoles]

def LogicalHoles (u v : E → V) (R : Finset V) (forbidden : Finset E)
    (s : E → Bool) : Prop :=
  (∀ e ∈ forbidden, s e = false) ∧
  (∀ x ∈ R, ∀ e, ¬ (s e = true ∧ (u e = x ∨ v e = x))) ∧
  (∀ x ∉ R, ∃! e, s e = true ∧ (u e = x ∨ v e = x))

omit [Fintype V] [Fintype E] in
lemma intact_uses {m : ℕ} (hm : Even m) (u v : E → V) (b : E → Selection m)
    (e : E) (x : V) (hb : Valid ∅ (b e)) :
    Uses u v b e x ↔ b e 0 = true ∧ (u e = x ∨ v e = x) := by
  rw [Uses,intact_terminals hm _ hb]
  exact and_or_left.symm

end Deletion

end MatchingFPRAS.Subdivision

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_HoleBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Subdivision
open Finset

structure HoleBlocks (m : ℕ) where
  left : Option (Fin m)
  neutral : List (Fin m × Fin m)
  right : Option (Fin m)

lemma duplicate_getElem (xs : List ℝ) (i : ℕ) (hi : i < (duplicate xs).length) :
    (duplicate xs)[i] = xs[i/2]'(by simp only [duplicate_length] at hi; omega) := by
  induction xs generalizing i with
  | nil => simp [duplicate] at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [duplicate]
    | succ i =>
      cases i with
      | zero => simp [duplicate]
      | succ i =>
        have hi' : i < (duplicate xs).length := by simp only [duplicate_cons,List.length_cons] at hi; omega
        have hh := ih i hi'
        simpa only [duplicate_cons,List.getElem_cons_succ,Nat.succ_eq_add_one,
          show (i+1+1)/2=i/2+1 by omega] using hh

lemma profile_left (p : ℕ) (B Hu Hv lam : ℝ) (i : Fin (4*p+1))
    (hi : i.val < 2*p) :
    profileActivity p B Hu Hv lam i = max B (Hu/2^(i.val/2)) := by
  unfold profileActivity profile
  simp only [List.get_eq_getElem,Fin.cast]
  have hl : i.val < (duplicate (List.ofFn fun r : Fin p => max B (Hu/2^r.val))).length := by
    simpa using hi
  rw [List.getElem_append_left (by simpa only [List.length_append,List.length_singleton] using
    (show i.val < (duplicate (List.ofFn fun r : Fin p => max B (Hu/2^r.val))).length+1 by omega))]
  rw [List.getElem_append_left hl,duplicate_getElem]
  simp

@[simp] lemma profile_center (p : ℕ) (B Hu Hv lam : ℝ) :
    profileActivity p B Hu Hv lam ⟨2*p,by omega⟩ = lam := by
  unfold profileActivity profile
  simp only [List.get_eq_getElem,Fin.cast]
  rw [List.getElem_append_left (by simp)]
  rw [List.getElem_append_right (by simp)]
  simp

lemma profile_right (p : ℕ) (B Hu Hv lam : ℝ) (i : Fin (4*p+1))
    (hi : 2*p < i.val) :
    profileActivity p B Hu Hv lam i = max B (Hv/2^((4*p-i.val)/2)) := by
  unfold profileActivity profile
  simp only [List.get_eq_getElem,Fin.cast]
  rw [List.getElem_append_right (by simp; omega),duplicate_getElem]
  simp only [duplicate_length,List.length_ofFn,List.length_append,List.length_singleton,
    List.getElem_reverse,List.getElem_ofFn]
  congr 3
  omega

theorem profile_lower (p : ℕ) (B Hu Hv lam : ℝ) (hlam : lam ≤ B)
    (i : Fin (4*p+1)) : lam ≤ profileActivity p B Hu Hv lam i := by
  rcases lt_trichotomy i.val (2*p) with hi | hi | hi
  · rw [profile_left _ _ _ _ _ _ hi]; exact hlam.trans (le_max_left _ _)
  · have he : i=⟨2*p,by omega⟩ := Fin.ext hi
    rw [he]; simp
  · rw [profile_right _ _ _ _ _ _ hi]; exact hlam.trans (le_max_left _ _)

lemma legValue_antitone (B H : ℝ) (hH : 0 ≤ H) :
    Antitone (fun r : ℕ => max B (H/(2:ℝ)^r)) := by
  intro i j hij
  apply max_le_max_left
  exact div_le_div_of_nonneg_left hH (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hij)

lemma legValue_step (B H : ℝ) (hB : 0 ≤ B) (r : ℕ) :
    max B (H/(2:ℝ)^r) ≤ 2*max B (H/(2:ℝ)^(r+1)) := by
  apply max_le
  · exact (le_max_left B (H/2^(r+1))).trans
      (by have hh := (le_max_left B (H/2^(r+1))); nlinarith)
  · have he : H/(2:ℝ)^r = 2*(H/(2:ℝ)^(r+1)) := by rw [pow_succ]; field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)

lemma profile_innermost (K : ℕ) (B H : ℝ) (hB : 1 ≤ B) (hH : H ≤ 4^K) :
    max B (H/(2:ℝ)^(2*K+1)) = B := by
  apply max_eq_left
  have hp : (2:ℝ)^(2*K+1) = 2*4^K := by
    rw [pow_succ,pow_mul]; norm_num; ring
  rw [hp]
  apply (div_le_iff₀ (by positivity)).mpr
  have h4 : (0:ℝ) ≤ 4^K := by positivity
  nlinarith

noncomputable def internalStrength (p : ℕ) (B Hu Hv : ℝ) (j : Fin (4*p)) : ℝ :=
  if j.val < 2*p then max B (Hu/2^(j.val/2))
    else max B (Hv/2^((4*p-(j.val+1))/2))

lemma le_internalStrength (p : ℕ) (B Hu Hv : ℝ) (j : Fin (4*p)) :
    B ≤ internalStrength p B Hu Hv j := by
  unfold internalStrength; split_ifs <;> exact le_max_left _ _

theorem internalStrength_incident (p : ℕ) (B Hu Hv lam : ℝ)
    (hHu : 0 ≤ Hu) (hHv : 0 ≤ Hv) (hlam : lam ≤ B) (j : Fin (4*p)) :
    profileActivity p B Hu Hv lam j.castSucc ≤ internalStrength p B Hu Hv j ∧
    profileActivity p B Hu Hv lam j.succ ≤ internalStrength p B Hu Hv j := by
  by_cases hj : j.val < 2*p
  · have hs : internalStrength p B Hu Hv j=max B (Hu/2^(j.val/2)) := by simp [internalStrength,hj]
    rw [hs]
    constructor
    · rw [profile_left _ _ _ _ _ _ hj]
      exact le_rfl
    · by_cases hj' : j.val+1 < 2*p
      · rw [profile_left _ _ _ _ _ _ hj']
        exact legValue_antitone B Hu hHu (by simp only [Fin.val_succ]; omega)
      · have hc : j.succ=⟨2*p,by omega⟩ := Fin.ext (by simp only [Fin.val_succ]; omega)
        rw [hc,profile_center]
        exact hlam.trans (le_max_left _ _)
  · have hs : internalStrength p B Hu Hv j=max B (Hv/2^((4*p-(j.val+1))/2)) := by
      simp [internalStrength,hj]
    rw [hs]
    constructor
    · by_cases hj' : 2*p < j.val
      · rw [profile_right _ _ _ _ _ _ hj']
        exact legValue_antitone B Hv hHv (by simp only [Fin.val_castSucc]; omega)
      · have hc : j.castSucc=⟨2*p,by omega⟩ := Fin.ext (by simp only [Fin.val_castSucc]; omega)
        rw [hc,profile_center]
        exact hlam.trans (le_max_left _ _)
    · rw [profile_right _ _ _ _ _ _ (by simp only [Fin.val_succ]; omega)]
      exact le_rfl

theorem internalStrength_left_leg (p : ℕ) (B Hu Hv lam : ℝ) (hHu : 0 ≤ Hu)
    (j : Fin (4*p)) (hj : j.val < 2*p) (i : Fin (4*p+1)) (hi : i.val ≤ j.val) :
    internalStrength p B Hu Hv j ≤ profileActivity p B Hu Hv lam i := by
  rw [profile_left _ _ _ _ _ _ (by omega)]
  simp only [internalStrength,ite_eq_left hj]
  exact legValue_antitone B Hu hHu (by omega)

theorem internalStrength_right_leg (p : ℕ) (B Hu Hv lam : ℝ) (hHv : 0 ≤ Hv)
    (j : Fin (4*p)) (hj : ¬ j.val < 2*p) (i : Fin (4*p+1)) (hi : j.val+1 ≤ i.val) :
    internalStrength p B Hu Hv j ≤ profileActivity p B Hu Hv lam i := by
  rw [profile_right _ _ _ _ _ _ (by omega)]
  simp only [internalStrength,ite_eq_right hj]
  exact legValue_antitone B Hv hHv (by omega)

end MatchingFPRAS.Subdivision

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_FirstHoleSortedCons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Subdivision

variable {V E : Type*} [Fintype V] [Fintype E]

lemma internalStrength_le_twice_incident (p : ℕ) (hp : 1≤p) (B Hu Hv : ℝ)
    (hB : 0≤B) (hHu : 0≤Hu) (hHv : 0≤Hv)
    (hinnerL : max B (Hu/2^(p-1))=B) (hinnerR : max B (Hv/2^(p-1))=B)
    (j : Fin (4*p)) :
    internalStrength p B Hu Hv j ≤ 2*profileActivity p B Hu Hv B j.castSucc ∧
    internalStrength p B Hu Hv j ≤ 2*profileActivity p B Hu Hv B j.succ := by
  have two_self (x : ℝ) (hx : B≤x) : x≤2*x := by linarith
  by_cases hj : j.val<2*p
  · rw [internalStrength,ite_eq_left hj]
    constructor
    · rw [profile_left _ _ _ _ _ _ hj]
      exact two_self _ (le_max_left _ _)
    · by_cases hk : j.val+1<2*p
      · rw [profile_left _ _ _ _ _ _ hk]
        calc
          _ ≤ 2*max B (Hu/2^(j.val/2+1)) := legValue_step B Hu hB _
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (legValue_antitone B Hu hHu (by simp only [Fin.val_succ]; omega)) (by norm_num)
      · have he : j.succ=⟨2*p,by omega⟩ := Fin.ext (by simp only [Fin.val_succ]; omega)
        rw [he,profile_center,show j.val/2=p-1 by omega,hinnerL]
        exact two_self _ le_rfl
  · rw [internalStrength,ite_eq_right hj]
    constructor
    · by_cases hk : 2*p<j.val
      · rw [profile_right _ _ _ _ _ _ hk]
        calc
          _ ≤ 2*max B (Hv/2^((4*p-(j.val+1))/2+1)) := legValue_step B Hv hB _
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (legValue_antitone B Hv hHv (by simp only [Fin.val_castSucc]; omega)) (by norm_num)
      · have he : j.castSucc=⟨2*p,by omega⟩ := Fin.ext (by simp only [Fin.val_castSucc]; omega)
        rw [he,profile_center,show (4*p-(j.val+1))/2=p-1 by omega,hinnerR]
        exact two_self _ le_rfl
    · rw [profile_right _ _ _ _ _ _ (by simp only [Fin.val_succ]; omega)]
      exact two_self _ (le_max_left _ _)

lemma profile_adjacent_near (p : ℕ) (hp : 1≤p) (B Hu Hv : ℝ)
    (hB : 0≤B) (hHu : 0≤Hu) (hHv : 0≤Hv)
    (hinnerL : max B (Hu/2^(p-1))=B) (hinnerR : max B (Hv/2^(p-1))=B)
    (j : Fin (4*p)) :
    profileActivity p B Hu Hv B j.castSucc ≤ 2*profileActivity p B Hu Hv B j.succ ∧
    profileActivity p B Hu Hv B j.succ ≤ 2*profileActivity p B Hu Hv B j.castSucc := by
  have h₁ := internalStrength_incident p B Hu Hv B hHu hHv le_rfl j
  have h₂ := internalStrength_le_twice_incident p hp B Hu Hv hB hHu hHv hinnerL hinnerR j
  exact ⟨h₁.1.trans h₂.2,h₁.2.trans h₂.1⟩

end MatchingFPRAS.Subdivision

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RealGeometry

variable {V E : Type*}

abbrev Vertex (V E : Type*) (m : ℕ) := V ⊕ (E × Fin m)

def atVertex (u v : E → V) (m : ℕ) (e : E) (i : Fin (m+2)) : Vertex V E m :=
  if h0 : i.val=0 then Sum.inl (u e)
  else if h1 : i.val=m+1 then Sum.inl (v e)
  else Sum.inr (e,⟨i.val-1,by omega⟩)

@[simp] lemma atVertex_zero (u v : E → V) (m : ℕ) (e : E) :
    atVertex u v m e 0 = Sum.inl (u e) := by simp [atVertex]

@[simp] lemma atVertex_last (u v : E → V) (m : ℕ) (e : E) :
    atVertex u v m e (Fin.last (m+1)) = Sum.inl (v e) := by simp [atVertex]

@[simp] lemma atVertex_internal (u v : E → V) (m : ℕ) (e : E) (i : Fin m) :
    atVertex u v m e i.succ.castSucc = Sum.inr (e,i) := by
  simp only [atVertex,Fin.val_castSucc,Fin.val_succ,Nat.add_eq_zero_iff,one_ne_zero,
    and_false,↓reduceDIte]
  rw [dite_eq_right (by have := i.isLt; omega)]
  rfl

lemma atVertex_eq_inr_iff (u v : E → V) (m : ℕ) (e f : E)
    (i : Fin (m+2)) (j : Fin m) :
    atVertex u v m e i = Sum.inr (f,j) ↔ e=f ∧ i.val=j.val+1 := by
  unfold atVertex
  split_ifs with h0 h1
  · simp only [false_iff,not_and]
    intro h
    have := j.isLt
    omega
  · simp only [false_iff,not_and]
    intro h
    have := j.isLt
    omega
  · simp only [Sum.inr.injEq,Prod.mk.injEq,Fin.ext_iff]
    constructor
    · rintro ⟨rfl,h⟩; exact ⟨rfl,by omega⟩
    · rintro ⟨rfl,h⟩; exact ⟨rfl,by omega⟩

lemma atVertex_eq_inl_iff (u v : E → V) (m : ℕ) (e : E)
    (i : Fin (m+2)) (x : V) :
    atVertex u v m e i = Sum.inl x ↔
      (i.val=0 ∧ u e=x) ∨ (i.val=m+1 ∧ v e=x) := by
  unfold atVertex
  split_ifs with h0 h1
  · simp [h0]
  · simp [h1]
  · simp [h0,h1]

theorem atVertex_injective (u v : E → V) (m : ℕ) (e : E) (huv : u e ≠ v e) :
    Function.Injective (atVertex u v m e) := by
  intro i j h
  by_cases hi0 : i.val=0
  · have he : atVertex u v m e i = Sum.inl (u e) := by simp [atVertex,hi0]
    have hj := (atVertex_eq_inl_iff u v m e j (u e)).mp (h.symm.trans he)
    rcases hj with hj | hj
    · apply Fin.ext; omega
    · exact False.elim (huv hj.2.symm)
  · by_cases hi1 : i.val=m+1
    · have he : atVertex u v m e i = Sum.inl (v e) := by simp [atVertex,hi1]
      have hj := (atVertex_eq_inl_iff u v m e j (v e)).mp (h.symm.trans he)
      rcases hj with hj | hj
      · exact False.elim (huv hj.2)
      · apply Fin.ext; omega
    · let k : Fin m := ⟨i.val-1,by omega⟩
      have he : atVertex u v m e i = Sum.inr (e,k) := by simp [atVertex,hi0,hi1,k]
      have hj := (atVertex_eq_inr_iff u v m e e j k).mp (h.symm.trans he)
      apply Fin.ext
      dsimp [k] at hj
      omega

theorem internal_private (u v : E → V) (m : ℕ) (e f : E) (i : Fin m)
    (j : Fin (m+2)) :
    atVertex u v m e i.succ.castSucc = atVertex u v m f j ↔
      e=f ∧ i.val+1=j.val := by
  rw [atVertex_internal,eq_comm,atVertex_eq_inr_iff]
  exact and_congr eq_comm eq_comm

def edge (u v : E → V) (m : ℕ) (e : E) (i : Fin (m+1)) : Sym2 (Vertex V E m) :=
  s(atVertex u v m e i.castSucc,atVertex u v m e i.succ)

lemma first_vertex_terminal (u v : E → V) (m : ℕ) (e : E)
    (i : Fin (m+1)) (x : V) :
    atVertex u v m e i.castSucc = Sum.inl x ↔ i.val=0 ∧ u e=x := by
  rw [atVertex_eq_inl_iff]
  have h : i.val ≠ m+1 := by omega
  simp [h]

lemma second_vertex_terminal (u v : E → V) (m : ℕ) (e : E)
    (i : Fin (m+1)) (x : V) :
    atVertex u v m e i.succ = Sum.inl x ↔ i.val=m ∧ v e=x := by
  rw [atVertex_eq_inl_iff]
  simp only [Fin.val_succ,Nat.add_eq_zero_iff,one_ne_zero,and_false,false_and,false_or,
    Nat.add_right_cancel_iff]

lemma edge_ordered_injective (u v : E → V) (m : ℕ) (hm : 1 ≤ m)
    (e f : E) (i j : Fin (m+1))
    (h0 : atVertex u v m e i.castSucc = atVertex u v m f j.castSucc)
    (h1 : atVertex u v m e i.succ = atVertex u v m f j.succ) : e=f ∧ i=j := by
  by_cases hi : i.val=0
  · have hz : atVertex u v m e i.castSucc = Sum.inl (u e) := by
      apply (first_vertex_terminal _ _ _ _ _ _).mpr; exact ⟨hi,rfl⟩
    have hj : j.val=0 := ((first_vertex_terminal _ _ _ _ _ _).mp (h0.symm.trans hz)).1
    let k : Fin m := ⟨0,by omega⟩
    have hki : i.succ = k.succ.castSucc := by apply Fin.ext; simp only [Fin.val_succ,Fin.val_castSucc]; dsimp only [k]; omega
    have hkj : j.succ = k.succ.castSucc := by apply Fin.ext; simp only [Fin.val_succ,Fin.val_castSucc]; dsimp only [k]; omega
    rw [hki,hkj,atVertex_internal,atVertex_internal] at h1
    have hef : e=f := congrArg Prod.fst (Sum.inr.inj h1)
    exact ⟨hef,Fin.ext (by omega)⟩
  · let k : Fin m := ⟨i.val-1,by omega⟩
    have hki : i.castSucc = k.succ.castSucc := by apply Fin.ext; simp only [Fin.val_succ,Fin.val_castSucc]; dsimp only [k]; omega
    rw [hki] at h0
    have hh := (internal_private u v m e f k j.castSucc).mp h0
    refine ⟨hh.1,Fin.ext ?_⟩
    dsimp [k] at hh
    omega

lemma edge_ordered_not_reverse (u v : E → V) (m : ℕ) (hm : 2 ≤ m)
    (e f : E) (i j : Fin (m+1)) :
    ¬ (atVertex u v m e i.castSucc = atVertex u v m f j.succ ∧
      atVertex u v m e i.succ = atVertex u v m f j.castSucc) := by
  rintro ⟨h0,h1⟩
  by_cases hi : i.val=0
  · have hz : atVertex u v m e i.castSucc = Sum.inl (u e) := by
      apply (first_vertex_terminal _ _ _ _ _ _).mpr; exact ⟨hi,rfl⟩
    have hj : j.val=m := ((second_vertex_terminal _ _ _ _ _ _).mp (h0.symm.trans hz)).1
    let k : Fin m := ⟨0,by omega⟩
    have hki : i.succ = k.succ.castSucc := by apply Fin.ext; simp only [Fin.val_succ,Fin.val_castSucc]; dsimp only [k]; omega
    rw [hki] at h1
    have hh := (internal_private u v m e f k j.castSucc).mp h1
    dsimp [k] at hh
    omega
  · let k : Fin m := ⟨i.val-1,by omega⟩
    have hki : i.castSucc = k.succ.castSucc := by apply Fin.ext; simp only [Fin.val_succ,Fin.val_castSucc]; dsimp only [k]; omega
    rw [hki] at h0
    have hh := (internal_private u v m e f k j.succ).mp h0
    have hij : i.val=j.val+1 := by dsimp [k] at hh; omega
    by_cases him : i.val=m
    · have hz : atVertex u v m e i.succ = Sum.inl (v e) := by
        apply (second_vertex_terminal _ _ _ _ _ _).mpr; exact ⟨him,rfl⟩
      have hj : j.val=0 := ((first_vertex_terminal _ _ _ _ _ _).mp (h1.symm.trans hz)).1
      omega
    · let l : Fin m := ⟨i.val,by omega⟩
      have hli : i.succ = l.succ.castSucc := rfl
      rw [hli] at h1
      have hh' := (internal_private u v m e f l j.castSucc).mp h1
      dsimp [l] at hh'
      omega

theorem edge_injective (u v : E → V) (m : ℕ) (hm : 2 ≤ m) :
    Function.Injective (fun q : E × Fin (m+1) => edge u v m q.1 q.2) := by
  rintro ⟨e,i⟩ ⟨f,j⟩ h
  have he := Sym2.eq_iff.mp h
  rcases he with h | h
  · have hh := edge_ordered_injective u v m (by omega) e f i j h.1 h.2
    exact Prod.ext hh.1 hh.2
  · exact False.elim (edge_ordered_not_reverse u v m hm e f i j h)

noncomputable def activity [Fintype E] (u v : E → V) (m : ℕ)
    (t : E → Fin (m+1) → ℝ) (x y : Vertex V E m) : ℝ := by
  classical
  exact ∑ q : E × Fin (m+1), if edge u v m q.1 q.2 = s(x,y) then t q.1 q.2 else 0

lemma activity_symm [Fintype E] (u v : E → V) (m : ℕ)
    (t : E → Fin (m+1) → ℝ) (x y : Vertex V E m) :
    activity u v m t x y = activity u v m t y x := by
  classical
  simp only [activity,Sym2.eq_swap]

theorem activity_on_edge [Fintype E] (u v : E → V) (m : ℕ) (hm : 2 ≤ m)
    (t : E → Fin (m+1) → ℝ) (e : E) (i : Fin (m+1)) :
    activity u v m t (atVertex u v m e i.castSucc) (atVertex u v m e i.succ) = t e i := by
  classical
  unfold activity
  rw [Finset.sum_eq_single (e,i)]
  · simp [edge]
  · intro q hq hne
    have hnot : edge u v m q.1 q.2 ≠ edge u v m e i := by
      intro he
      exact hne (edge_injective u v m hm he)
    exact ite_eq_right hnot
  · simp

lemma activity_eq_zero_of_not_edge [Fintype E] (u v : E → V) (m : ℕ)
    (t : E → Fin (m+1) → ℝ) (x y : Vertex V E m)
    (h : ∀ e i, edge u v m e i ≠ s(x,y)) : activity u v m t x y = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro q hq
  exact ite_eq_right (h q.1 q.2)

theorem activity_eq_edge_or_zero [Fintype E] (u v : E → V) (m : ℕ) (hm : 2 ≤ m)
    (t : E → Fin (m+1) → ℝ) (x y : Vertex V E m) :
    activity u v m t x y = 0 ∨
      ∃ e i, edge u v m e i = s(x,y) ∧ activity u v m t x y = t e i := by
  classical
  by_cases hex : ∃ e i, edge u v m e i = s(x,y)
  · obtain ⟨e,i,he⟩ := hex
    refine Or.inr ⟨e,i,he,?_⟩
    rcases Sym2.eq_iff.mp he with he | he
    · rw [← he.1,← he.2]
      exact activity_on_edge u v m hm t e i
    · rw [← he.2,← he.1,activity_symm]
      exact activity_on_edge u v m hm t e i
  · left
    exact activity_eq_zero_of_not_edge u v m t x y (by simpa only [not_exists] using hex)

theorem internal_incident_iff (u v : E → V) (m : ℕ) (e f : E)
    (i : Fin (m+1)) (j : Fin m) :
    Sum.inr (f,j) ∈ edge u v m e i ↔
      e=f ∧ (i.val=j.val ∨ i.val=j.val+1) := by
  rw [edge,Sym2.mem_iff]
  simp only [eq_comm (a := Sum.inr (f,j)),atVertex_eq_inr_iff,Fin.val_castSucc,Fin.val_succ]
  constructor
  · rintro (⟨he,hi⟩ | ⟨he,hi⟩)
    · exact ⟨he,Or.inr hi⟩
    · exact ⟨he,Or.inl (by omega)⟩
  · rintro ⟨he,hi | hi⟩
    · exact Or.inr ⟨he,by omega⟩
    · exact Or.inl ⟨he,hi⟩

theorem internal_activity_le [Fintype E] (u v : E → V) (m : ℕ) (hm : 2 ≤ m)
    (t : E → Fin (m+1) → ℝ) (e : E) (j : Fin m) (T : ℝ) (hT : 0 ≤ T)
    (hleft : t e j.castSucc ≤ T) (hright : t e j.succ ≤ T) (y : Vertex V E m) :
    activity u v m t (Sum.inr (e,j)) y ≤ T := by
  rcases activity_eq_edge_or_zero u v m hm t (Sum.inr (e,j)) y with hzero | ⟨f,i,he,hw⟩
  · simpa [hzero] using hT
  · have hin : Sum.inr (e,j) ∈ edge u v m f i := by rw [he]; exact Sym2.mem_mk_left _ _
    obtain ⟨rfl,hi | hi⟩ := (internal_incident_iff u v m f e i j).mp hin
    · have hij : i=j.castSucc := Fin.ext hi
      simpa [hw,hij] using hleft
    · have hij : i=j.succ := Fin.ext hi
      simpa [hw,hij] using hright

def realThreshold (u v : E → V) (m : ℕ) (t : E → Fin (m+1) → ℝ)
    (τ : ℝ) : SimpleGraph (Vertex V E m) where
  Adj a b := a ≠ b ∧ ∃ e i, edge u v m e i = s(a,b) ∧ τ ≤ t e i
  symm := ⟨by rintro a b ⟨hne,e,i,he,ht⟩; exact ⟨hne.symm,e,i,by simpa only [Sym2.eq_swap] using he,ht⟩⟩
  loopless := ⟨by rintro a ⟨hne,_⟩; exact hne rfl⟩

def logicalThreshold (u v : E → V) (lam : E → ℝ) (τ : ℝ) : SimpleGraph V where
  Adj a b := a ≠ b ∧ ∃ e, s(u e,v e)=s(a,b) ∧ τ ≤ lam e
  symm := ⟨by rintro a b ⟨hne,e,he,ht⟩; exact ⟨hne.symm,e,by simpa only [Sym2.eq_swap] using he,ht⟩⟩
  loopless := ⟨by rintro a ⟨hne,_⟩; exact hne rfl⟩

def contract (u v : E → V) (m : ℕ) (c : Fin (m+1)) : Vertex V E m → V
  | Sum.inl a => a
  | Sum.inr (e,j) => if j.val < c.val then u e else v e

@[simp] lemma contract_terminal (u v : E → V) (m : ℕ) (c : Fin (m+1)) (a : V) :
    contract u v m c (Sum.inl a) = a := rfl

lemma contract_atVertex (u v : E → V) (m : ℕ) (c : Fin (m+1)) (e : E)
    (i : Fin (m+2)) : contract u v m c (atVertex u v m e i) =
      if i.val ≤ c.val then u e else v e := by
  by_cases h0 : i.val=0
  · simp [atVertex,h0,contract]
  by_cases hlast : i.val=m+1
  · have hn : ¬ i.val ≤ c.val := by omega
    simp only [atVertex,dite_eq_right h0,dite_eq_left hlast,contract,ite_eq_right hn]
  · have he : i.val-1 < c.val ↔ i.val ≤ c.val := by omega
    simp [atVertex,h0,hlast,contract,he]

lemma contracted_edge (u v : E → V) (m : ℕ) (c : Fin (m+1)) (e : E)
    (i : Fin (m+1)) :
    contract u v m c (atVertex u v m e i.castSucc) =
      contract u v m c (atVertex u v m e i.succ) ∨
    (i=c ∧ contract u v m c (atVertex u v m e i.castSucc)=u e ∧
      contract u v m c (atVertex u v m e i.succ)=v e) := by
  rw [contract_atVertex,contract_atVertex]
  simp only [Fin.val_castSucc,Fin.val_succ]
  by_cases hi : i.val < c.val
  · left; simp [show i.val ≤ c.val by omega,show i.val+1 ≤ c.val by omega]
  by_cases hi' : c.val < i.val
  · left; simp [show ¬ i.val ≤ c.val by omega,show ¬ i.val+1 ≤ c.val by omega]
  · have hic : i=c := Fin.ext (by omega)
    right; subst i; simp

lemma reachable_of_edge_reachable {W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V → W) (hf : ∀ a b, G.Adj a b → H.Reachable (f a) (f b))
    {a b : V} (h : G.Reachable a b) : H.Reachable (f a) (f b) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h he ih =>
    exact ih.trans ((SimpleGraph.reachable_iff_reflTransGen _ _).mp (hf _ _ he))

theorem threshold_contract (u v : E → V) (m : ℕ) (c : Fin (m+1))
    (lam : E → ℝ) (t : E → Fin (m+1) → ℝ) (hc : ∀ e, t e c=lam e)
    (τ : ℝ) {a b : Vertex V E m} (h : (realThreshold u v m t τ).Reachable a b) :
    (logicalThreshold u v lam τ).Reachable (contract u v m c a) (contract u v m c b) := by
  apply reachable_of_edge_reachable (realThreshold u v m t τ)
    (logicalThreshold u v lam τ) (contract u v m c) _ h
  rintro a b ⟨hab,e,i,he,ht⟩
  rcases Sym2.eq_iff.mp he with he | he
  · rw [← he.1,← he.2]
    rcases contracted_edge u v m c e i with heq | ⟨rfl,hleft,hright⟩
    · rw [heq]
    · rw [hleft,hright]
      by_cases huv : u e=v e
      · rw [huv]
      · exact SimpleGraph.Adj.reachable ⟨huv,e,rfl,by simpa [hc e] using ht⟩
  · rw [← he.2,← he.1]
    apply SimpleGraph.Reachable.symm
    rcases contracted_edge u v m c e i with heq | ⟨rfl,hleft,hright⟩
    · rw [heq]
    · rw [hleft,hright]
      by_cases huv : u e=v e
      · rw [huv]
      · exact SimpleGraph.Adj.reachable ⟨huv,e,rfl,by simpa [hc e] using ht⟩

lemma positions_reachable (G : SimpleGraph V) (m : ℕ) (f : Fin (m+2) → V)
    (hf : ∀ i : Fin (m+1), G.Reachable (f i.castSucc) (f i.succ))
    (i : Fin (m+2)) : G.Reachable (f 0) (f i) := by
  obtain ⟨i,hi⟩ := i
  induction i with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ i ih =>
    have hi' : i < m+2 := by omega
    have hi'' : i < m+1 := by omega
    exact (ih hi').trans (hf ⟨i,hi''⟩)

theorem threshold_lift_edge (u v : E → V) (m : ℕ) (lam : E → ℝ)
    (t : E → Fin (m+1) → ℝ) (hm : ∀ e i, lam e ≤ t e i)
    (τ : ℝ) (e : E) (he : τ ≤ lam e) :
    (realThreshold u v m t τ).Reachable (Sum.inl (u e)) (Sum.inl (v e)) := by
  have h := positions_reachable (realThreshold u v m t τ) m (atVertex u v m e)
    (fun i => ?_) (Fin.last (m+1))
  · simpa using h
  by_cases hn : atVertex u v m e i.castSucc = atVertex u v m e i.succ
  · rw [hn]
  · exact SimpleGraph.Adj.reachable ⟨hn,e,i,rfl,he.trans (hm e i)⟩

theorem terminal_threshold_iff (u v : E → V) (m : ℕ) (c : Fin (m+1))
    (lam : E → ℝ) (t : E → Fin (m+1) → ℝ) (hc : ∀ e, t e c=lam e)
    (hm : ∀ e i, lam e ≤ t e i) (τ : ℝ) (a b : V) :
    (realThreshold u v m t τ).Reachable (Sum.inl a) (Sum.inl b) ↔
      (logicalThreshold u v lam τ).Reachable a b := by
  constructor
  · exact threshold_contract u v m c lam t hc τ
  · apply reachable_of_edge_reachable (logicalThreshold u v lam τ)
      (realThreshold u v m t τ) Sum.inl
    rintro a b ⟨hne,e,he,ht⟩
    rcases Sym2.eq_iff.mp he with he | he
    · rw [← he.1,← he.2]; exact threshold_lift_edge u v m lam t hm τ e ht
    · rw [← he.2,← he.1]; exact (threshold_lift_edge u v m lam t hm τ e ht).symm

lemma activity_on_eq [Fintype E] (u v : E → V) (m : ℕ) (hm : 2 ≤ m)
    (t : E → Fin (m+1) → ℝ) (e : E) (i : Fin (m+1)) (a b : Vertex V E m)
    (he : edge u v m e i=s(a,b)) : activity u v m t a b=t e i := by
  rcases Sym2.eq_iff.mp he with he | he
  · rw [← he.1,← he.2]; exact activity_on_edge u v m hm t e i
  · rw [← he.2,← he.1,activity_symm]; exact activity_on_edge u v m hm t e i

theorem realThreshold_adj_iff [Fintype E] (u v : E → V) (m : ℕ) (hm : 2 ≤ m)
    (t : E → Fin (m+1) → ℝ) (τ : ℝ) (hτ : 0 < τ) (a b : Vertex V E m) :
    (realThreshold u v m t τ).Adj a b ↔ a ≠ b ∧ τ ≤ activity u v m t a b := by
  constructor
  · rintro ⟨hne,e,i,he,ht⟩
    exact ⟨hne,by rwa [activity_on_eq u v m hm t e i a b he]⟩
  · rintro ⟨hne,ht⟩
    rcases activity_eq_edge_or_zero u v m hm t a b with hzero | ⟨e,i,he,hw⟩
    · rw [hzero] at ht; exact False.elim (not_le_of_gt hτ ht)
    · exact ⟨hne,e,i,he,by rwa [hw] at ht⟩

theorem path_interval_reachable (u v : E → V) (m : ℕ)
    (t : E → Fin (m+1) → ℝ) (τ : ℝ) (e : E)
    (i j : Fin (m+2)) (hij : i.val ≤ j.val)
    (ht : ∀ k : Fin (m+1), i.val ≤ k.val → k.val < j.val → τ ≤ t e k) :
    (realThreshold u v m t τ).Reachable (atVertex u v m e i) (atVertex u v m e j) := by
  have aux : ∀ (k : ℕ) (hk : k < m+2), i.val ≤ k →
      (∀ q : Fin (m+1), i.val ≤ q.val → q.val < k → τ ≤ t e q) →
      (realThreshold u v m t τ).Reachable (atVertex u v m e i)
        (atVertex u v m e ⟨k,hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk hik hq
      have he : i=⟨0,hk⟩ := Fin.ext (by change i.val = 0; omega)
      rw [he]
    | succ k ih =>
      intro hk hik hq
      by_cases he : i.val=k+1
      · have hei : i=⟨k+1,hk⟩ := Fin.ext he
        rw [hei]
      have hki : i.val ≤ k := by omega
      have hk' : k < m+2 := by omega
      have hk'' : k < m+1 := by omega
      have hprior := ih hk' hki (fun q hiq hqk => hq q hiq (by omega))
      apply hprior.trans
      by_cases hn : atVertex u v m e ⟨k,hk'⟩ = atVertex u v m e ⟨k+1,hk⟩
      · rw [hn]
      · exact SimpleGraph.Adj.reachable ⟨hn,e,⟨k,hk''⟩,rfl,hq ⟨k,hk''⟩ hki (Nat.lt_succ_self k)⟩
  exact aux j.val j.isLt hij ht

end MatchingFPRAS.RealGeometry

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_PathActivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open Finset

variable {V E : Type*} [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E]

instance vertexLinearOrder (m : ℕ) : LinearOrder (Vertex V E m) := by
  letI : LinearOrder (E × Fin m) := LinearOrder.lift' (toLex : E × Fin m → E ×ₗ Fin m) (fun _ _ h => h)
  exact LinearOrder.lift' (toLex : V ⊕ (E × Fin m) → V ⊕ₗ (E × Fin m)) (fun _ _ h => h)

omit [Fintype V] [Fintype E] in
@[simp] lemma terminal_lt_iff (m : ℕ) (a b : V) :
    @LT.lt (Vertex V E m) (vertexLinearOrder (V := V) (E := E) m).toLT (Sum.inl a) (Sum.inl b) ↔ a < b := by
  change Sum.Lex (· < · : V → V → Prop) _ (Sum.inl a) (Sum.inl b) ↔ a < b
  exact Sum.lex_inl_inl

omit [Fintype V] in
lemma real_threshold_eq [Fintype V] (u v : E → V) (m : ℕ) (hm : 2 ≤ m)
    (t : E → Fin (m+1) → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    thresholdGraph (activity u v m t) τ=realThreshold u v m t τ := by
  ext a b
  rw [realThreshold_adj_iff u v m hm t τ hτ]
  change (a ≠ b ∧ τ ≤ edgeActivity (activity u v m t) a b) ↔ _
  rw [edgeActivity_of_symmetric _ (activity_symm u v m t)]

theorem interval_le_bottleneck (u v : E → V) (m : ℕ) (hm : 2 ≤ m)
    (huv : ∀ e, u e ≠ v e) (t : E → Fin (m+1) → ℝ) (e : E)
    (i j : Fin (m+2)) (hij : i.val < j.val) (T : ℝ)
    (ht : ∀ k : Fin (m+1), i.val ≤ k.val → k.val < j.val → T ≤ t e k) :
    T ≤ bottleneck (activity u v m t) (atVertex u v m e i) (atVertex u v m e j) := by
  by_cases hT : 1 < T
  · apply (bottleneck_threshold _ _ _ ?_ T hT).mpr
    · rw [real_threshold_eq u v m hm t T (by linarith)]
      exact path_interval_reachable u v m t T e i j hij.le ht
    · intro he
      have := congrArg Fin.val (atVertex_injective u v m e (huv e) he)
      omega
  · exact (le_of_not_gt hT).trans (one_le_bottleneck _ _ _)

noncomputable def pathActivity (p : ℕ) (B Hu Hv lam : E → ℝ) : E → Fin (4*p+1) → ℝ :=
  fun e => profileActivity p (B e) (Hu e) (Hv e) (lam e)

noncomputable def realBottleneck (u v : E → V) (p : ℕ) (B Hu Hv lam : E → ℝ) :
    Vertex V E (4*p) → Vertex V E (4*p) → ℝ :=
  bottleneck (activity u v (4*p) (pathActivity p B Hu Hv lam))

theorem realBottleneck_internal_cap (u v : E → V) (p : ℕ) (hp : 1 ≤ p)
    (B Hu Hv lam : E → ℝ) (hB : ∀ e, 1 ≤ B e) (hHu : ∀ e, 0 ≤ Hu e)
    (hHv : ∀ e, 0 ≤ Hv e) (hlam : ∀ e, lam e ≤ B e) (e : E) (j : Fin (4*p))
    (a : Vertex V E (4*p)) :
    realBottleneck u v p B Hu Hv lam (Sum.inr (e,j)) a ≤
      internalStrength p (B e) (Hu e) (Hv e) j := by
  apply bottleneck_le_row_bound
  · exact (hB e).trans (le_internalStrength _ _ _ _ _)
  · intro b hb
    rw [edgeActivity_of_symmetric _ (activity_symm _ _ _ _)]
    apply internal_activity_le u v (4*p) (by omega)
    · exact (zero_le_one.trans (hB e)).trans (le_internalStrength _ _ _ _ _)
    · exact (internalStrength_incident p (B e) (Hu e) (Hv e) (lam e)
        (hHu e) (hHv e) (hlam e) j).1
    · exact (internalStrength_incident p (B e) (Hu e) (Hv e) (lam e)
        (hHu e) (hHv e) (hlam e) j).2

theorem realBottleneck_left_home (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (hp : 1 ≤ p) (B Hu Hv lam : E → ℝ) (hHu : ∀ e, 0 ≤ Hu e)
    (e : E) (j : Fin (4*p)) (hj : j.val < 2*p) :
    internalStrength p (B e) (Hu e) (Hv e) j ≤
      realBottleneck u v p B Hu Hv lam (Sum.inr (e,j)) (Sum.inl (u e)) := by
  rw [realBottleneck,bottleneck_comm]
  have h := interval_le_bottleneck u v (4*p) (by omega) huv
    (pathActivity p B Hu Hv lam) e 0 j.succ.castSucc (by simp) _
    (fun k _ hk => internalStrength_left_leg p (B e) (Hu e) (Hv e) (lam e)
      (hHu e) j hj k (by simp only [Fin.val_castSucc,Fin.val_succ] at hk; omega))
  simpa only [atVertex_zero,atVertex_internal,atVertex_last,realBottleneck] using h

 theorem realBottleneck_right_home (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (hp : 1 ≤ p) (B Hu Hv lam : E → ℝ) (hHv : ∀ e, 0 ≤ Hv e)
    (e : E) (j : Fin (4*p)) (hj : ¬ j.val < 2*p) :
    internalStrength p (B e) (Hu e) (Hv e) j ≤
      realBottleneck u v p B Hu Hv lam (Sum.inr (e,j)) (Sum.inl (v e)) := by
  have h := interval_le_bottleneck u v (4*p) (by omega) huv
    (pathActivity p B Hu Hv lam) e j.succ.castSucc (Fin.last (4*p+1))
    (by simp only [Fin.val_castSucc,Fin.val_succ,Fin.val_last]; omega) _
    (fun k hk _ => internalStrength_right_leg p (B e) (Hu e) (Hv e) (lam e)
      (hHv e) j hj k (by simpa only [Fin.val_castSucc,Fin.val_succ] using hk))
  simpa only [atVertex_zero,atVertex_internal,atVertex_last,realBottleneck] using h

noncomputable def leftFactor (p : ℕ) (B Hu Hv lam : ℝ) (j : Fin (4*p)) : ℝ :=
  if j.val < 2*p then 1 else lam / internalStrength p B Hu Hv j

noncomputable def rightFactor (p : ℕ) (B Hu Hv lam : ℝ) (j : Fin (4*p)) : ℝ :=
  if j.val < 2*p then lam / internalStrength p B Hu Hv j else 1

noncomputable def neutralFactor (p : ℕ) (B Hu Hv lam : ℝ) (j k : Fin (4*p)) : ℝ :=
  if k.val < 2*p then (internalStrength p B Hu Hv j)⁻¹
  else if j.val < 2*p then lam / (internalStrength p B Hu Hv j * internalStrength p B Hu Hv k)
  else (internalStrength p B Hu Hv k)⁻¹

abbrev LogicalEdge (V : Type*) [LinearOrder V] := {q : V × V // q.1 < q.2}

instance logicalEdgeLinearOrder : LinearOrder (LogicalEdge V) :=
  LinearOrder.lift' (fun e => toLex e.val) (fun _ _ h => Subtype.ext h)

def source (e : LogicalEdge V) : V := e.val.1

def target (e : LogicalEdge V) : V := e.val.2

omit [Fintype V] in
lemma source_ne_target [Fintype V] (e : LogicalEdge V) : source e ≠ target e := e.property.ne

def logicalActivity (w : V → V → ℝ) (e : LogicalEdge V) : ℝ :=
  edgeActivity w (source e) (target e)

omit [Fintype V] in
lemma logical_threshold_eq [Fintype V] (w : V → V → ℝ) (τ : ℝ) :
    logicalThreshold source target (logicalActivity w) τ=thresholdGraph w τ := by
  ext a b
  change (a ≠ b ∧ ∃ e : LogicalEdge V, s(source e,target e)=s(a,b) ∧ τ ≤ logicalActivity w e) ↔
    (a ≠ b ∧ τ ≤ edgeActivity w a b)
  constructor
  · rintro ⟨hne,e,he,ht⟩
    refine ⟨hne,?_⟩
    rcases Sym2.eq_iff.mp he with he | he
    · simpa only [logicalActivity,he.1,he.2] using ht
    · simpa only [logicalActivity,he.1,he.2,edgeActivity_comm w b a] using ht
  · rintro ⟨hne,ht⟩
    refine ⟨hne,?_⟩
    rcases lt_or_gt_of_ne hne with hab | hab
    · exact ⟨⟨(a,b),hab⟩,rfl,ht⟩
    · exact ⟨⟨(b,a),hab⟩,Sym2.eq_swap,by simpa [logicalActivity,source,target,edgeActivity_comm w b a] using ht⟩

theorem terminal_bottleneck (w : V → V → ℝ) (p : ℕ) (hp : 1 ≤ p)
    (Hu Hv : LogicalEdge V → ℝ) (a b : V) :
    realBottleneck source target p (fun e => bottleneck w (source e) (target e))
      Hu Hv (logicalActivity w) (Sum.inl a) (Sum.inl b) = bottleneck w a b := by
  by_cases hab : a=b
  · subst b; simp [realBottleneck,bottleneck]
  apply bottleneck_eq_of_threshold_iff _ w _ _ a b (Sum.inl_injective.ne hab) hab
  intro τ hτ
  rw [real_threshold_eq source target (4*p) (by omega) _ τ (by linarith)]
  rw [terminal_threshold_iff source target (4*p) ⟨2*p,by omega⟩
    (logicalActivity w) (pathActivity p (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w))
    (fun e => profile_center p _ _ _ _) ?_ τ a b]
  · rw [logical_threshold_eq]
  · intro e i
    exact profile_lower p _ _ _ _ (edgeActivity_le_bottleneck w (source e) (target e)
      (source_ne_target e)) i

noncomputable def enlargedHoles (m : ℕ) (R₀ : Finset V) (U : E → Finset (Fin m)) :
    Finset (Vertex V E m) :=
  R₀.map ⟨Sum.inl,Sum.inl_injective⟩ ∪
    Finset.univ.biUnion (fun e => (U e).map ⟨fun j => Sum.inr (e,j),fun _ _ h => congrArg Prod.snd (Sum.inr_injective h)⟩)

omit [Fintype V] in
@[simp] lemma mem_enlargedHoles_left [Fintype V] (m : ℕ) (R₀ : Finset V) (U : E → Finset (Fin m)) (x : V) :
    Sum.inl x ∈ enlargedHoles m R₀ U ↔ x ∈ R₀ := by
  classical
  simp [enlargedHoles]

omit [Fintype V] in
@[simp] lemma mem_enlargedHoles_right [Fintype V] (m : ℕ) (R₀ : Finset V) (U : E → Finset (Fin m))
    (e : E) (j : Fin m) : Sum.inr (e,j) ∈ enlargedHoles m R₀ U ↔ j ∈ U e := by
  classical
  simp only [enlargedHoles,Finset.mem_union,Finset.mem_map,Finset.mem_biUnion,
    Finset.mem_univ,true_and]
  constructor
  · rintro (⟨x,hx,hxx⟩ | ⟨e',j',hj,hjj⟩)
    · change (Sum.inl x : Vertex V E m)=Sum.inr (e,j) at hxx
      cases hxx
    · have hh := Prod.mk.inj (Sum.inr_injective hjj)
      rcases hh with ⟨hee,hjj⟩
      subst e'; subst j'; exact hj
  · intro hj; exact Or.inr ⟨e,j,hj,rfl⟩

noncomputable def neutralPairs (m : ℕ) (d : E → HoleBlocks m) :
    List (Vertex V E m × Vertex V E m) :=
  Finset.univ.toList.flatMap (fun e => (d e).neutral.map
    (fun q => (Sum.inr (e,q.1),Sum.inr (e,q.2))))

noncomputable def consumedPairs (u v : E → V) (m : ℕ) (d : E → HoleBlocks m) :
    List (Vertex V E m × Vertex V E m) :=
  Finset.univ.toList.flatMap (fun e =>
    (d e).left.toList.map (fun j => (Sum.inr (e,j),Sum.inl (u e))) ++
    (d e).right.toList.map (fun j => (Sum.inr (e,j),Sum.inl (v e))))

omit [Fintype V] [LinearOrder V] [LinearOrder E] in
@[simp] lemma mem_neutralPairs [Fintype V] [LinearOrder V] [LinearOrder E]
    {m : ℕ} (d : E → HoleBlocks m) (q : Vertex V E m × Vertex V E m) :
    q ∈ neutralPairs m d ↔ ∃ e r, r ∈ (d e).neutral ∧ q=(Sum.inr (e,r.1),Sum.inr (e,r.2)) := by
  classical
  simp only [neutralPairs,List.mem_flatMap,Finset.mem_toList,Finset.mem_univ,true_and,List.mem_map]
  constructor
  · rintro ⟨e,r,hr,he⟩; exact ⟨e,r,hr,he.symm⟩
  · rintro ⟨e,r,hr,rfl⟩; exact ⟨e,r,hr,rfl⟩

omit [Fintype V] [LinearOrder V] [LinearOrder E] in
@[simp] lemma mem_consumedPairs [Fintype V] [LinearOrder V] [LinearOrder E]
    {m : ℕ} (u v : E → V) (d : E → HoleBlocks m)
    (q : Vertex V E m × Vertex V E m) :
    q ∈ consumedPairs u v m d ↔ ∃ e j,
      (j ∈ (d e).left ∧ q=(Sum.inr (e,j),Sum.inl (u e))) ∨
      (j ∈ (d e).right ∧ q=(Sum.inr (e,j),Sum.inl (v e))) := by
  classical
  simp only [consumedPairs,List.mem_flatMap,Finset.mem_toList,Finset.mem_univ,true_and,
    List.mem_append,List.mem_map,Option.mem_toList]
  constructor
  · rintro ⟨e,h | h⟩
    · obtain ⟨j,hj,he⟩ := h; exact ⟨e,j,Or.inl ⟨hj,he.symm⟩⟩
    · obtain ⟨j,hj,he⟩ := h; exact ⟨e,j,Or.inr ⟨hj,he.symm⟩⟩
  · rintro ⟨e,j,h | h⟩
    · exact ⟨e,Or.inl ⟨j,h.1,h.2.symm⟩⟩
    · exact ⟨e,Or.inr ⟨j,h.1,h.2.symm⟩⟩

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Related
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open Finset

variable {V E : Type*} [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E]

lemma edge_activity_le_realBottleneck (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (hp : 1 ≤ p) (B Hu Hv lam : E → ℝ) (e : E) (i : Fin (4*p+1)) :
    pathActivity p B Hu Hv lam e i ≤ realBottleneck u v p B Hu Hv lam
      (atVertex u v (4*p) e i.castSucc) (atVertex u v (4*p) e i.succ) := by
  apply interval_le_bottleneck u v (4*p) (by omega) huv (pathActivity p B Hu Hv lam) e
    i.castSucc i.succ (by simp)
  intro k hk hk'
  have he : k=i := Fin.ext (by simp only [Fin.val_castSucc,Fin.val_succ] at hk hk'; omega)
  subst k
  exact le_rfl

theorem realBottleneck_noncentral_edge (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (hp : 1 ≤ p) (B Hu Hv lam : E → ℝ) (hB : ∀ e, 1 ≤ B e)
    (hHu : ∀ e, 0 ≤ Hu e) (hHv : ∀ e, 0 ≤ Hv e) (hlam : ∀ e, lam e ≤ B e)
    (e : E) (i : Fin (4*p+1)) (hi : i.val ≠ 2*p) :
    realBottleneck u v p B Hu Hv lam (atVertex u v (4*p) e i.castSucc)
      (atVertex u v (4*p) e i.succ) = pathActivity p B Hu Hv lam e i := by
  apply le_antisymm _ (edge_activity_le_realBottleneck u v huv p hp B Hu Hv lam e i)
  rcases lt_or_gt_of_ne hi with hi | hi
  · let j : Fin (4*p) := ⟨i.val,by omega⟩
    have hv : atVertex u v (4*p) e i.succ=Sum.inr (e,j) :=
      (atVertex_eq_inr_iff u v (4*p) e e i.succ j).mpr ⟨rfl,rfl⟩
    rw [hv,realBottleneck,bottleneck_comm]
    have hc := realBottleneck_internal_cap u v p hp B Hu Hv lam hB hHu hHv hlam e j
      (atVertex u v (4*p) e i.castSucc)
    simpa [realBottleneck,pathActivity,internalStrength,show j.val<2*p from hi,
      profile_left p (B e) (Hu e) (Hv e) (lam e) i hi,j] using hc
  · let j : Fin (4*p) := ⟨i.val-1,by have := i.isLt; omega⟩
    have hv : atVertex u v (4*p) e i.castSucc=Sum.inr (e,j) :=
      (atVertex_eq_inr_iff u v (4*p) e e i.castSucc j).mpr ⟨rfl,by dsimp [j]; omega⟩
    rw [hv]
    have hc := realBottleneck_internal_cap u v p hp B Hu Hv lam hB hHu hHv hlam e j
      (atVertex u v (4*p) e i.succ)
    have hj : ¬ j.val < 2*p := by dsimp [j]; omega
    have he : j.val+1=i.val := by dsimp [j]; omega
    simpa only [pathActivity,profile_right p (B e) (Hu e) (Hv e) (lam e) i hi,
      internalStrength,ite_eq_right hj,he] using hc

variable {V : Type*} [Fintype V] [LinearOrder V]

theorem realBottleneck_central_edge (w : V → V → ℝ) (p : ℕ) (hp : 1 ≤ p)
    (Hu Hv : LogicalEdge V → ℝ) (hHu : ∀ e, 0 ≤ Hu e) (hHv : ∀ e, 0 ≤ Hv e)
    (hinner : ∀ e, max (bottleneck w (source e) (target e)) (Hu e/2^(p-1)) =
      bottleneck w (source e) (target e)) (e : LogicalEdge V) :
    realBottleneck source target p (fun e => bottleneck w (source e) (target e))
      Hu Hv (logicalActivity w)
      (atVertex source target (4*p) e ⟨2*p,by omega⟩)
      (atVertex source target (4*p) e ⟨2*p+1,by omega⟩) =
      bottleneck w (source e) (target e) := by
  let B := fun e : LogicalEdge V => bottleneck w (source e) (target e)
  let j : Fin (4*p) := ⟨2*p-1,by omega⟩
  let k : Fin (4*p) := ⟨2*p,by omega⟩
  have hj : j.val < 2*p := by dsimp [j]; omega
  have hk : ¬ k.val < 2*p := by simp [k]
  have hjk : j≠k := by intro h; have := congrArg Fin.val h; dsimp [j,k] at this; omega
  have hjv : atVertex source target (4*p) e ⟨2*p,by omega⟩ = Sum.inr (e,j) :=
    (atVertex_eq_inr_iff _ _ _ _ _ _ _).mpr ⟨rfl,by dsimp [j]; omega⟩
  have hkv : atVertex source target (4*p) e ⟨2*p+1,by omega⟩ = Sum.inr (e,k) :=
    (atVertex_eq_inr_iff _ _ _ _ _ _ _).mpr ⟨rfl,rfl⟩
  rw [hjv,hkv]
  have hsj : internalStrength p (B e) (Hu e) (Hv e) j=B e := by
    rw [internalStrength,ite_eq_left hj]
    have hdiv : j.val/2=p-1 := by dsimp [j]; omega
    rw [hdiv]
    exact hinner e
  apply le_antisymm
  · have hc := realBottleneck_internal_cap source target p hp B Hu Hv (logicalActivity w)
        (fun e => one_le_bottleneck w _ _) hHu hHv
        (fun e => edgeActivity_le_bottleneck w _ _ (source_ne_target e)) e j (Sum.inr (e,k))
    exact (hc.trans_eq hsj)
  · let t := activity source target (4*p) (pathActivity p B Hu Hv (logicalActivity w))
    have hleft : B e ≤ bottleneck t (Sum.inr (e,j)) (Sum.inl (source e)) :=
      (le_internalStrength p (B e) (Hu e) (Hv e) j).trans
        (realBottleneck_left_home source target source_ne_target p hp B Hu Hv (logicalActivity w) hHu e j hj)
    have hright : B e ≤ bottleneck t (Sum.inr (e,k)) (Sum.inl (target e)) :=
      (le_internalStrength p (B e) (Hu e) (Hv e) k).trans
        (realBottleneck_right_home source target source_ne_target p hp B Hu Hv (logicalActivity w) hHv e k hk)
    have hterm : bottleneck t (Sum.inl (source e)) (Sum.inl (target e))=B e :=
      terminal_bottleneck w p hp Hu Hv _ _
    have hx : B e ≤ bottleneck t (Sum.inr (e,j)) (Sum.inl (target e)) := by
      have ht := bottleneck_ultrametric t (Sum.inr (e,j)) (Sum.inl (target e)) (Sum.inl (source e))
        (by simp) (by simp) (by simpa using (source_ne_target e).symm)
      exact ((le_min hleft hterm.ge).trans ht)
    have htri := bottleneck_ultrametric t (Sum.inr (e,j)) (Sum.inr (e,k)) (Sum.inl (target e))
      (by simpa using hjk) (by simp) (by simp)
    rw [bottleneck_comm t (Sum.inl (target e)) (Sum.inr (e,k))] at htri
    exact (le_min hx hright).trans htri

theorem source_effective_profile (w : V → V → ℝ) (p : ℕ) (hp : 1≤p)
    (Hu Hv : LogicalEdge V → ℝ) (hHu : ∀ e, 0≤Hu e) (hHv : ∀ e, 0≤Hv e)
    (hinner : ∀ e, max (bottleneck w (source e) (target e)) (Hu e/2^(p-1)) =
      bottleneck w (source e) (target e)) (e : LogicalEdge V) (i : Fin (4*p+1)) :
    realBottleneck source target p (fun e => bottleneck w (source e) (target e)) Hu Hv
      (logicalActivity w) (atVertex source target (4*p) e i.castSucc)
      (atVertex source target (4*p) e i.succ) =
      profileActivity p (bottleneck w (source e) (target e)) (Hu e) (Hv e)
        (bottleneck w (source e) (target e)) i := by
  by_cases hi : i.val=2*p
  · have he : i=⟨2*p,by omega⟩ := Fin.ext hi
    rw [he,profile_center]
    exact realBottleneck_central_edge w p hp Hu Hv hHu hHv hinner e
  · rw [realBottleneck_noncentral_edge source target source_ne_target p hp _ Hu Hv
      (logicalActivity w) (fun _ => one_le_bottleneck _ _ _) hHu hHv
      (fun e => edgeActivity_le_bottleneck w _ _ (source_ne_target e)) e i hi]
    rcases lt_or_gt_of_ne hi with hi | hi
    · simp only [pathActivity,profile_left _ _ _ _ _ _ hi]
    · simp only [pathActivity,profile_right _ _ _ _ _ _ hi]

omit [Fintype V] [LinearOrder V] in
theorem effective_profile_incident_near {E : Type*} (u v : E → V)
    (p : ℕ) (hp : 1≤p) (B : E → ℝ) (H : V → ℝ)
    (hB : ∀ e, 0≤B e) (hH : ∀ x, 0≤H x)
    (hdom : ∀ e, B e≤H (u e) ∧ B e≤H (v e))
    (hinnerL : ∀ e, max (B e) (H (u e)/2^(p-1))=B e)
    (hinnerR : ∀ e, max (B e) (H (v e)/2^(p-1))=B e)
    (x : Vertex V E (4*p)) (e f : E) (i j : Fin (4*p+1))
    (he : x=atVertex u v (4*p) e i.castSucc ∨ x=atVertex u v (4*p) e i.succ)
    (hf : x=atVertex u v (4*p) f j.castSucc ∨ x=atVertex u v (4*p) f j.succ) :
    profileActivity p (B e) (H (u e)) (H (v e)) (B e) i ≤
      2*profileActivity p (B f) (H (u f)) (H (v f)) (B f) j := by
  cases x with
  | inl x =>
    have ht (g : E) (k : Fin (4*p+1))
        (hg : Sum.inl x=atVertex u v (4*p) g k.castSucc ∨ Sum.inl x=atVertex u v (4*p) g k.succ) :
        profileActivity p (B g) (H (u g)) (H (v g)) (B g) k=H x := by
      rcases hg with hg | hg
      · obtain ⟨hk,hx⟩ := (first_vertex_terminal u v (4*p) g k x).mp hg.symm
        rw [profile_left _ _ _ _ _ _ (by omega),hk]
        simp only [Nat.zero_div,pow_zero,div_one,max_eq_right (hdom g).1]
        exact congrArg H hx
      · obtain ⟨hk,hx⟩ := (second_vertex_terminal u v (4*p) g k x).mp hg.symm
        rw [profile_right _ _ _ _ _ _ (by omega),hk]
        simp only [Nat.sub_self,Nat.zero_div,pow_zero,div_one,max_eq_right (hdom g).2]
        exact congrArg H hx
    rw [ht e i he,ht f j hf]
    linarith [hH x]
  | inr z =>
    rcases z with ⟨g,k⟩
    have hi : e=g ∧ (i.val=k.val ∨ i.val=k.val+1) := by
      rcases he with he | he
      · have hh := (atVertex_eq_inr_iff u v (4*p) e g i.castSucc k).mp he.symm
        exact ⟨hh.1,Or.inr hh.2⟩
      · have hh := (atVertex_eq_inr_iff u v (4*p) e g i.succ k).mp he.symm
        exact ⟨hh.1,Or.inl (by simpa using hh.2)⟩
    have hj : f=g ∧ (j.val=k.val ∨ j.val=k.val+1) := by
      rcases hf with hf | hf
      · have hh := (atVertex_eq_inr_iff u v (4*p) f g j.castSucc k).mp hf.symm
        exact ⟨hh.1,Or.inr hh.2⟩
      · have hh := (atVertex_eq_inr_iff u v (4*p) f g j.succ k).mp hf.symm
        exact ⟨hh.1,Or.inl (by simpa using hh.2)⟩
    obtain ⟨rfl,hi⟩ := hi
    obtain ⟨rfl,hj⟩ := hj
    have hnear := profile_adjacent_near p hp (B f) (H (u f)) (H (v f))
      (hB f) (hH _) (hH _) (hinnerL f) (hinnerR f) k
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · have heq : i=j := Fin.ext (hi.trans hj.symm)
      rw [heq]
      have hn := (hB f).trans (profile_lower p (B f) (H (u f)) (H (v f)) (B f) le_rfl j)
      linarith
    · have hi' : i=k.castSucc := Fin.ext hi
      have hj' : j=k.succ := Fin.ext hj
      simpa [hi',hj'] using hnear.1
    · have hi' : i=k.succ := Fin.ext hi
      have hj' : j=k.castSucc := Fin.ext hj
      simpa [hi',hj'] using hnear.2
    · have heq : i=j := Fin.ext (hi.trans hj.symm)
      rw [heq]
      have hn := (hB f).trans (profile_lower p (B f) (H (u f)) (H (v f)) (B f) le_rfl j)
      linarith

end MatchingFPRAS.Enlargement

namespace MatchingFPRAS.Hierarchy

variable {V : Type*} [Fintype V]

variable (B : V → V → ℝ)

variable (hsym : ∀ a b, B a b = B b a)

variable (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)

def Related (t : ℝ) (a b : V) : Prop := a=b ∨ t ≤ B a b

omit [Fintype V] in
include hsym in
lemma related_symm (t : ℝ) {a b : V} (h : Related B t a b) : Related B t b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rwa [hsym])

omit [Fintype V] in
include htri in
lemma related_trans (t : ℝ) {a b c : V} (hab : Related B t a b) (hbc : Related B t b c) :
    Related B t a c := by
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  by_cases hac : a=c
  · exact Or.inl hac
  by_cases hab' : a=b
  · subst b; exact Or.inr hbc
  by_cases hbc' : c=b
  · subst c; exact Or.inr hab
  exact Or.inr ((le_min hab hbc).trans (htri a c b hac hab' hbc'))

def thresholdSetoid (t : ℝ) : Setoid V where
  r := Related B t
  iseqv := ⟨fun _ => Or.inl rfl,related_symm B hsym t,related_trans B htri t⟩

abbrev Component (t : ℝ) := Quotient (thresholdSetoid B hsym htri t)

abbrev Label (H : ℕ) := (k : Fin (H+1)) × Component B hsym htri (2^k.val)

def labelAt {H : ℕ} (k : Fin (H+1)) (x : V) : Label B hsym htri H :=
  ⟨k,Quotient.mk _ x⟩

variable (hfloor : ∀ a b, 1 ≤ B a b)

noncomputable def dyadicLevel (H : ℕ) (x : ℝ) : Fin (H+1) := by
  classical
  exact ⟨Nat.findGreatest (fun k => (2:ℝ)^k ≤ x) H,
    Nat.lt_succ_of_le (Nat.findGreatest_le H)⟩

lemma dyadic_upper (H : ℕ) (x : ℝ) (hx : x ≤ (2:ℝ)^H) :
    x < (2:ℝ)^((dyadicLevel H x).val+1) := by
  classical
  by_cases he : (dyadicLevel H x).val=H
  · rw [he,pow_succ]
    have : 0 < (2:ℝ)^H := by positivity
    linarith
  · by_contra hn
    have hle : (dyadicLevel H x).val+1 ≤ H := by have := (dyadicLevel H x).isLt; omega
    have hg := Nat.le_findGreatest (P := fun k => (2:ℝ)^k ≤ x) hle (le_of_not_gt hn)
    change (dyadicLevel H x).val+1 ≤ (dyadicLevel H x).val at hg
    omega

variable {E : Type*} [Fintype E] (left right : E → V) (H : ℕ)

def Incident (e : E) (x : V) : Prop := x=left e ∨ x=right e

noncomputable def edgeLabel (e : E) : Label B hsym htri H :=
  labelAt B hsym htri (dyadicLevel H (B (left e) (right e))) (left e)

noncomputable def memberships (x : V) : Finset (Label B hsym htri H) := by
  classical
  exact (Finset.univ.filter (fun e => Incident left right e x)).image
    (edgeLabel B hsym htri left right H)

omit [Fintype V] in
lemma mem_memberships (x : V) (l : Label B hsym htri H) :
    l ∈ memberships B hsym htri left right H x ↔
      ∃ e, Incident left right e x ∧ edgeLabel B hsym htri left right H e=l := by
  classical
  simp [memberships]

end MatchingFPRAS.Hierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Height
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

lemma row_nonempty (x : V) : (Finset.univ.erase x : Finset V).Nonempty := by
  obtain ⟨y,hy⟩ := exists_ne x
  exact ⟨y,by simp [hy]⟩

noncomputable def sourceHeight (w : V → V → ℝ) (x : V) : ℝ :=
  (Finset.univ.erase x).sup' (row_nonempty x) (bottleneck w x)

lemma bottleneck_le_sourceHeight (w : V → V → ℝ) {x y : V} (hxy : x ≠ y) :
    bottleneck w x y ≤ sourceHeight w x :=
  Finset.le_sup' (bottleneck w x) (by simp [hxy.symm])

lemma one_le_sourceHeight (w : V → V → ℝ) (x : V) : 1 ≤ sourceHeight w x := by
  obtain ⟨y,hy⟩ := exists_ne x
  exact (one_le_bottleneck w x y).trans (bottleneck_le_sourceHeight w hy.symm)

lemma sourceHeight_nonneg (w : V → V → ℝ) (x : V) : 0 ≤ sourceHeight w x :=
  zero_le_one.trans (one_le_sourceHeight w x)

lemma sourceHeight_bound (w : V → V → ℝ) (K : ℕ)
    (hw : ∀ x y, x ≠ y → edgeActivity w x y ≤ (4:ℝ)^K) (x : V) : sourceHeight w x ≤ 4^K := by
  apply Finset.sup'_le
  intro y hy
  exact bottleneck_le_row_bound w x (4^K) (one_le_pow₀ (by norm_num)) (hw x) y

noncomputable def maxSourceHeight (w : V → V → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (sourceHeight w)

lemma sourceHeight_le_max (w : V → V → ℝ) (x : V) : sourceHeight w x ≤ maxSourceHeight w :=
  Finset.le_sup' (sourceHeight w) (Finset.mem_univ x)

lemma maxSourceHeight_bound (w : V → V → ℝ) (K : ℕ)
    (hw : ∀ x y, x ≠ y → edgeActivity w x y ≤ (4:ℝ)^K) : maxSourceHeight w ≤ 4^K := by
  exact Finset.sup'_le _ _ (fun x _ => sourceHeight_bound w K hw x)

noncomputable def sourceLevels (w : V → V → ℝ) (K : ℕ) : ℕ :=
  (dyadicLevel (2*K) (maxSourceHeight w)).val

lemma sourceLevels_le (w : V → V → ℝ) (K : ℕ) : sourceLevels w K ≤ 2*K := by
  have := (dyadicLevel (2*K) (maxSourceHeight w)).isLt
  dsimp [sourceLevels]; omega

lemma maxSourceHeight_lt (w : V → V → ℝ) (K : ℕ)
    (hw : ∀ x y, x ≠ y → edgeActivity w x y ≤ (4:ℝ)^K) :
    maxSourceHeight w < (2:ℝ)^(sourceLevels w K+1) := by
  apply dyadic_upper
  convert maxSourceHeight_bound w K hw using 1
  all_goals try with_reducible_and_instances rfl
  rw [pow_mul]; norm_num

abbrev SourceVertex (V : Type*) [LinearOrder V] (K : ℕ) := Vertex V (LogicalEdge V) (4*(2*K+2))

abbrev SourceRealEdge (V : Type*) [LinearOrder V] (K : ℕ) := LogicalEdge V × Fin (4*(2*K+2)+1)

def realLeft (K : ℕ) (e : SourceRealEdge V K) : SourceVertex V K :=
  atVertex source target (4*(2*K+2)) e.1 e.2.castSucc

def realRight (K : ℕ) (e : SourceRealEdge V K) : SourceVertex V K :=
  atVertex source target (4*(2*K+2)) e.1 e.2.succ

noncomputable def sourceRealB (w : V → V → ℝ) (K : ℕ) : SourceVertex V K → SourceVertex V K → ℝ :=
  realBottleneck source target (2*K+2) (fun e => bottleneck w (source e) (target e))
    (fun e => sourceHeight w (source e)) (fun e => sourceHeight w (target e)) (logicalActivity w)

lemma source_profile_strength (w : V → V → ℝ) (K : ℕ)
    (hw : ∀ x y, x ≠ y → edgeActivity w x y ≤ (4:ℝ)^K) (e : SourceRealEdge V K) :
    sourceRealB w K (realLeft K e) (realRight K e) =
      profileActivity (2*K+2) (bottleneck w (source e.1) (target e.1))
        (sourceHeight w (source e.1)) (sourceHeight w (target e.1))
        (bottleneck w (source e.1) (target e.1)) e.2 := by
  apply source_effective_profile
  · omega
  · intro e; exact sourceHeight_nonneg w _
  · intro e; exact sourceHeight_nonneg w _
  · intro f
    rw [show 2*K+2-1=2*K+1 by omega]
    exact profile_innermost K _ _ (one_le_bottleneck _ _ _) (sourceHeight_bound w K hw _)

lemma source_strength_incident_near (w : V → V → ℝ) (K : ℕ)
    (hw : ∀ x y, x ≠ y → edgeActivity w x y ≤ (4:ℝ)^K)
    (x : SourceVertex V K) (e f : SourceRealEdge V K)
    (he : Incident (realLeft K) (realRight K) e x)
    (hf : Incident (realLeft K) (realRight K) f x) :
    sourceRealB w K (realLeft K e) (realRight K e) ≤ 2*sourceRealB w K (realLeft K f) (realRight K f) := by
  simp only [source_profile_strength w K hw]
  apply effective_profile_incident_near source target (2*K+2) (by omega)
    (fun e => bottleneck w (source e) (target e)) (sourceHeight w)
  · intro e; exact zero_le_one.trans (one_le_bottleneck _ _ _)
  · exact sourceHeight_nonneg w
  · intro e
    exact ⟨bottleneck_le_sourceHeight w (source_ne_target e),by
      rw [bottleneck_comm]; exact bottleneck_le_sourceHeight w (source_ne_target e).symm⟩
  · intro e
    rw [show 2*K+2-1=2*K+1 by omega]
    exact profile_innermost K _ _ (one_le_bottleneck _ _ _) (sourceHeight_bound w K hw _)
  · intro e
    rw [show 2*K+2-1=2*K+1 by omega]
    exact profile_innermost K _ _ (one_le_bottleneck _ _ _) (sourceHeight_bound w K hw _)
  · exact he
  · exact hf

lemma profile_upper (p : ℕ) (B HU HV lam T : ℝ) (hB : B ≤ T) (hU : HU ≤ T) (hV : HV ≤ T)
    (hU0 : 0 ≤ HU) (hV0 : 0 ≤ HV) (hlam : lam ≤ T) (i : Fin (4*p+1)) :
    profileActivity p B HU HV lam i ≤ T := by
  rcases lt_trichotomy i.val (2*p) with h | h | h
  · rw [profile_left _ _ _ _ _ _ h]
    exact max_le hB ((div_le_self hU0 (one_le_pow₀ (by norm_num))).trans hU)
  · have hi : i=⟨2*p,by omega⟩ := Fin.ext h
    rw [hi,profile_center]; exact hlam
  · rw [profile_right _ _ _ _ _ _ h]
    exact max_le hB ((div_le_self hV0 (one_le_pow₀ (by norm_num))).trans hV)

lemma source_strength_le_max (w : V → V → ℝ) (K : ℕ)
    (hw : ∀ x y, x ≠ y → edgeActivity w x y ≤ (4:ℝ)^K) (e : SourceRealEdge V K) :
    sourceRealB w K (realLeft K e) (realRight K e) ≤ maxSourceHeight w := by
  rw [source_profile_strength w K hw]
  have hb := (bottleneck_le_sourceHeight w (source_ne_target e.1)).trans (sourceHeight_le_max w _)
  exact profile_upper _ _ _ _ _ _ hb (sourceHeight_le_max w _) (sourceHeight_le_max w _)
    (sourceHeight_nonneg w _) (sourceHeight_nonneg w _) hb _

lemma sourceRealB_comm (w : V → V → ℝ) (K : ℕ) (x y : SourceVertex V K) :
    sourceRealB w K x y = sourceRealB w K y x := bottleneck_comm _ _ _

lemma sourceRealB_tri (w : V → V → ℝ) (K : ℕ) (x y z : SourceVertex V K)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    min (sourceRealB w K x z) (sourceRealB w K z y) ≤ sourceRealB w K x y :=
  bottleneck_ultrametric _ _ _ _ hxy hxz hyz

lemma sourceRealB_floor (w : V → V → ℝ) (K : ℕ) (x y : SourceVertex V K) :
    1 ≤ sourceRealB w K x y := one_le_bottleneck _ _ _

abbrev SourceLabel (w : V → V → ℝ) (K : ℕ) :=
  Label (sourceRealB w K) (sourceRealB_comm w K) (sourceRealB_tri w K) (sourceLevels w K)

noncomputable def sourceBags (w : V → V → ℝ) (K : ℕ) (x : SourceVertex V K) :
    Finset (SourceLabel w K) :=
  memberships (sourceRealB w K) (sourceRealB_comm w K) (sourceRealB_tri w K)
    (realLeft K) (realRight K) (sourceLevels w K) x

end MatchingFPRAS.Enlargement

namespace MatchingFPRAS.Transport

section

open Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (inc : E → V → Prop)

noncomputable def support (Q : Finset E) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ∃ e ∈ Q, inc e v

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma mem_support (Q : Finset E) (v : V) : v ∈ support inc Q ↔ ∃ e ∈ Q, inc e v := by
  classical
  simp [support]

abbrev Partial := {Q : Finset E // MatchingOn inc Q (support inc Q)}

abbrev Matchings (U : Finset V) := {M : Finset E // MatchingOn inc M U}

noncomputable instance matchingsFintype (U : Finset V) : Fintype (Matchings inc U) := Fintype.ofFinite _

noncomputable def partitionWeight {R : Type*} [CommSemiring R] (w : E → R) (U : Finset V) : R :=
  ∑ M : Matchings inc U, ∏ e ∈ M.val, w e

end

open Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (inc : E → V → Prop)

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
@[simp] lemma support_empty : support inc ∅=∅ := by
  ext x; simp [support]

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_HoleStrength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open Finset

variable {V E : Type*} [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E]

omit [Fintype V] [LinearOrder V] [LinearOrder E] in
@[simp] lemma mem_consumed_destination_right [Fintype V] [LinearOrder V] [LinearOrder E]
    (u v : E → V) (m : ℕ) (d : E → HoleBlocks m)
    (e : E) (j : Fin m) : Sum.inr (e,j) ∉ (consumedPairs u v m d).map Prod.snd := by
  simp [consumedPairs,List.map_flatMap,List.map_append,List.map_map,Function.comp_def]




noncomputable def holeStrength (p : ℕ) (B Hu Hv : E → ℝ) : Vertex V E (4*p) → ℝ
  | Sum.inl _ => 1
  | Sum.inr (e,j) => internalStrength p (B e) (Hu e) (Hv e) j

noncomputable def neutralCharge (p : ℕ) (B Hu Hv lam : E → ℝ) :
    Vertex V E (4*p) × Vertex V E (4*p) → ℝ
  | (Sum.inr (e,j),Sum.inr (_,k)) => neutralFactor p (B e) (Hu e) (Hv e) (lam e) j k
  | _ => 0

noncomputable def consumedCharge (u : E → V) (p : ℕ) (B Hu Hv lam : E → ℝ) :
    Vertex V E (4*p) × Vertex V E (4*p) → ℝ
  | (Sum.inr (e,j),Sum.inl x) => if x=u e then leftFactor p (B e) (Hu e) (Hv e) (lam e) j
      else rightFactor p (B e) (Hu e) (Hv e) (lam e) j
  | _ => 0

noncomputable def totalDeletionCharge (u v : E → V) (p : ℕ) (B Hu Hv lam : E → ℝ)
    (d : E → HoleBlocks (4*p)) : ℝ :=
  ((neutralPairs (V := V) (4*p) d).map (neutralCharge p B Hu Hv lam)).prod *
    ((consumedPairs u v (4*p) d).map (consumedCharge u p B Hu Hv lam)).prod

noncomputable def blockCharge (p : ℕ) (B Hu Hv lam : ℝ) (d : HoleBlocks (4*p)) : ℝ :=
  (d.left.toList.map (leftFactor p B Hu Hv lam)).prod *
    (d.neutral.map (fun q => neutralFactor p B Hu Hv lam q.1 q.2)).prod *
    (d.right.toList.map (rightFactor p B Hu Hv lam)).prod

noncomputable def pathConstant (p : ℕ) (B Hu Hv : ℝ) : ℝ :=
  (∏ r : Fin p, max B (Hu/2^r.val)) * (∏ r : Fin p, max B (Hv/2^r.val))

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Incident
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Representation

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.Enlargement
open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

abbrev Incident (e : LogicalEdge V) (x : V) := source e=x ∨ target e=x

noncomputable def other (e : LogicalEdge V) (x : V) : V :=
  if source e=x then target e else source e

omit [Fintype V] in
@[simp] lemma other_source (e : LogicalEdge V) : other e (source e)=target e := by simp [other]
@[simp] lemma other_target (e : LogicalEdge V) : other e (target e)=source e := by
  simp [other,source_ne_target e]

lemma other_incident (e : LogicalEdge V) (x : V) (hx : Incident e x) :
    Incident e (other e x) := by
  rcases hx with rfl | rfl <;> simp only [other_source,other_target] <;> tauto

lemma other_ne (e : LogicalEdge V) (x : V) (hx : Incident e x) : other e x ≠ x := by
  rcases hx with rfl | rfl <;> simp [source_ne_target e,(source_ne_target e).symm]

lemma other_other (e : LogicalEdge V) (x : V) (hx : Incident e x) :
    other e (other e x)=x := by rcases hx with rfl | rfl <;> simp

lemma edge_eq_of_inc_other {e f : LogicalEdge V} (h : Incident f (source e))
    (ho : other f (source e)=target e) : f=e := by
  rcases h with h | h
  · have ht : target f=target e := by simpa only [← h,other_source] using ho
    exact Subtype.ext (Prod.ext h ht)
  · have hs : source f=target e := by simpa only [← h,other_target] using ho
    have hf := f.property
    have he := e.property
    change source f < target f at hf
    change source e < target e at he
    rw [hs,h] at hf
    exact False.elim ((lt_asymm he hf))

variable (R : Finset V) (s : LogicalEdge V → Bool)
    (hs : LogicalHoles source target R ∅ s)

include hs in
omit [Fintype V] in
lemma selected_not_hole [Fintype V] (e : LogicalEdge V) (he : s e=true) (x : V) (hx : Incident e x) :
    x ∉ R := by
  intro hxR
  exact hs.2.1 x hxR e ⟨he,hx⟩

noncomputable def chosen (x : V) (hx : x ∉ R) : LogicalEdge V :=
  (hs.2.2 x hx).exists.choose

omit [Fintype V] in
lemma chosen_spec [Fintype V] (x : V) (hx : x ∉ R) :
    s (chosen R s hs x hx)=true ∧ Incident (chosen R s hs x hx) x :=
  (hs.2.2 x hx).exists.choose_spec

lemma chosen_eq (x : V) (hx : x ∉ R) (e : LogicalEdge V)
    (he : s e=true) (hi : Incident e x) : chosen R s hs x hx=e := by
  exact (hs.2.2 x hx).unique (chosen_spec R s hs x hx) ⟨he,hi⟩

noncomputable def mateFun (x : V) : V :=
  if h : x ∈ R then x else other (chosen R s hs x h) x

omit [Fintype V] in
lemma mateFun_hole [Fintype V] (x : V) (hx : x ∈ R) : mateFun R s hs x=x := by simp [mateFun,hx]

lemma mateFun_selected (e : LogicalEdge V) (he : s e=true) (x : V) (hx : Incident e x) :
    mateFun R s hs x=other e x := by
  have hn := selected_not_hole R s hs e he x hx
  simp only [mateFun,dite_eq_right hn]
  rw [chosen_eq R s hs x hn e he hx]

lemma mateFun_involutive : Function.Involutive (mateFun R s hs) := by
  intro x
  by_cases hx : x ∈ R
  · rw [mateFun_hole R s hs x hx,mateFun_hole R s hs x hx]
  · let e := chosen R s hs x hx
    have he := chosen_spec R s hs x hx
    have hx' : mateFun R s hs x=other e x := mateFun_selected R s hs e he.1 x he.2
    rw [hx',mateFun_selected R s hs e he.1 _ (other_incident e x he.2),other_other e x he.2]

noncomputable def asMate : Mate V := ⟨mateFun R s hs,mateFun_involutive R s hs⟩

lemma asMate_selected (e : LogicalEdge V) :
    (asMate R s hs).val (source e)=target e ↔ s e=true := by
  constructor
  · intro hm
    have hx : source e ∉ R := by
      intro hx
      have hh := mateFun_hole R s hs _ hx
      change mateFun R s hs (source e)=target e at hm
      exact source_ne_target e (hh.symm.trans hm)
    let f := chosen R s hs (source e) hx
    have hf := chosen_spec R s hs (source e) hx
    have ho : other f (source e)=target e := by
      rw [← mateFun_selected R s hs f hf.1 _ hf.2]
      exact hm
    have hfe : f=e := edge_eq_of_inc_other hf.2 ho
    exact hfe ▸ hf.1
  · intro he
    exact (mateFun_selected R s hs e he (source e) (Or.inl rfl)).trans (other_source e)

variable {R s hs}

noncomputable def select (m : Mate V) (e : LogicalEdge V) : Bool :=
  decide (m.val (source e)=target e)

omit [Fintype V] in
@[simp] lemma select_eq_true [Fintype V] (m : Mate V) (e : LogicalEdge V) :
    select m e=true ↔ m.val (source e)=target e := by simp [select]

lemma select_mate_other (m : Mate V) (e : LogicalEdge V)
    (he : select m e=true) (x : V) (hx : Incident e x) : m.val x=other e x := by
  have ht := (select_eq_true m e).mp he
  rcases hx with rfl | rfl
  · simpa only [other_source] using ht
  · simp only [other_target]
    rw [← ht,mate_mate]

lemma edge_eq_of_selected_inc (m : Mate V) {e f : LogicalEdge V}
    (he : select m e=true) (hf : select m f=true)
    (x : V) (hex : Incident e x) (hfx : Incident f x) : e=f := by
  have hh : other e x=other f x := (select_mate_other m e he x hex).symm.trans
    (select_mate_other m f hf x hfx)
  rcases hex with rfl | rfl
  · exact (edge_eq_of_inc_other hfx (hh.symm.trans (other_source e))).symm
  · have hy : Incident f (source e) := by
      rw [other_target] at hh
      rw [hh]
      exact other_incident f _ hfx
    apply (edge_eq_of_inc_other hy ?_).symm
    rw [other_target] at hh
    rw [hh,other_other f _ hfx]

lemma select_holes (m : Mate V) (hm : HasHoles m R) :
    LogicalHoles source target R ∅ (select m) := by
  classical
  refine ⟨by simp,?_,?_⟩
  · intro x hx e he
    have hh := select_mate_other m e he.1 x he.2
    rw [(hm x).mpr hx] at hh
    exact other_ne e x he.2 hh.symm
  · intro x hx
    have hmx : m.val x ≠ x := fun h => hx ((hm x).mp h)
    have hex : ∃ e : LogicalEdge V, select m e=true ∧ Incident e x := by
      rcases lt_or_gt_of_ne hmx.symm with h | h
      · exact ⟨⟨(x,m.val x),h⟩,by simp [select,source,target],Or.inl rfl⟩
      · exact ⟨⟨(m.val x,x),h⟩,by simp [select,source,target],Or.inr rfl⟩
    obtain ⟨e,he⟩ := hex
    refine ⟨e,he,?_⟩
    intro f hf
    exact edge_eq_of_selected_inc m hf.1 he.1 x hf.2 he.2

@[simp] lemma select_asMate : select (asMate R s hs)=s := by
  funext e
  apply Bool.eq_iff_iff.mpr
  exact (select_eq_true _ e).trans (asMate_selected R s hs e)

end MatchingFPRAS.Representation

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Representation
open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

lemma intact_family (p : ℕ) (m : Mate V) (hm : HasHoles m ∅) :
    FamilyHoles source target (4*p) ∅ (fun _ => ∅)
      (fun e i => alternating (select m e) i.val) := by
  have hs := select_holes m hm
  refine ⟨fun e => alternating_valid _ _,by simp,?_⟩
  intro x hx
  have hi (e : LogicalEdge V) :
      Uses source target (fun (e : LogicalEdge V) (i : Fin (4*p+1)) => alternating (select m e) i.val) e x ↔
        select m e=true ∧ Incident e x := by
    rw [intact_uses (show Even (4*p) from ⟨2*p,by omega⟩) source target _ e x
      (alternating_valid _ _)]
    simp only [Fin.val_zero,alternating,Nat.zero_mod,ite_true]
  simpa only [hi] using hs.2.2 x hx

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_EdgeLow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RealGeometry

open Finset MatchingFPRAS.Subdivision MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (u v : E → V) (m : ℕ)

noncomputable def survivors (R : Finset V) (U : E → Finset (Fin m)) : Finset (Vertex V E m) := by
  classical
  exact univ.filter fun x => match x with
    | Sum.inl x => x∉R
    | Sum.inr (e,i) => i∉U e

omit [DecidableEq V] [DecidableEq E] in
@[simp] lemma mem_survivors_terminal (R : Finset V) (U : E → Finset (Fin m)) (x : V) :
    Sum.inl x ∈ survivors m R U ↔ x∉R := by simp [survivors]

omit [DecidableEq V] [DecidableEq E] in
@[simp] lemma mem_survivors_internal (R : Finset V) (U : E → Finset (Fin m)) (e : E) (i : Fin m) :
    Sum.inr (e,i) ∈ survivors m R U ↔ i∉U e := by simp [survivors]

end MatchingFPRAS.RealGeometry

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_ArcData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Cells

open SimpleGraph

variable {L : Type*} {G : SimpleGraph L}

lemma exists_walk_on_trace (a : ℕ → L) (n : ℕ)
    (ha : ∀ i < n, a i = a (i + 1) ∨ G.Adj (a i) (a (i + 1))) :
    ∃ w : G.Walk (a 0) (a n), ∀ v ∈ w.support, ∃ i ≤ n, a i = v := by
  induction n with
  | zero =>
    refine ⟨.nil, ?_⟩
    intro v hv
    have hv' : v = a 0 := by simpa using hv
    exact ⟨0, le_rfl, hv'.symm⟩
  | succ n ih =>
    obtain ⟨w, hw⟩ := ih (fun i hi => ha i (by omega))
    rcases ha n (by omega) with heq | hadj
    · refine ⟨w.copy rfl heq, ?_⟩
      intro v hv
      obtain ⟨i, hi, hiv⟩ := hw v (by simpa using hv)
      exact ⟨i, by omega, hiv⟩
    · refine ⟨w.concat hadj, ?_⟩
      intro v hv
      have hv' : v ∈ w.support ∨ v = a (n + 1) := by simpa using hv
      rcases hv' with hv' | hv'
      · obtain ⟨i, hi, hiv⟩ := hw v hv'
        exact ⟨i, by omega, hiv⟩
      · exact ⟨n + 1, le_rfl, hv'.symm⟩

lemma neighbor_return (hG : G.IsAcyclic) (a : ℕ → L) (n : ℕ) (P : L)
    (ha : ∀ i < n, a i = a (i + 1) ∨ G.Adj (a i) (a (i + 1)))
    (havoid : ∀ i ≤ n, a i ≠ P) (hfirst : G.Adj P (a 0))
    (hlast : G.Adj P (a n)) : a 0 = a n := by
  classical
  obtain ⟨w, hw⟩ := exists_walk_on_trace a n ha
  have hnot : P ∉ w.toPath.val.support := by
    intro hP
    obtain ⟨i, hi, hiP⟩ := hw P (w.support_toPath_subset_support hP)
    exact havoid i hi hiP
  have hp : (Walk.cons hfirst w.toPath.val).IsPath := w.toPath.isPath.cons hnot
  have hv := hG.eq_snd_of_adj_start hp hlast (Walk.cons hfirst w.toPath.val).end_mem_support
  simpa using hv.symm

structure ArcData (G : SimpleGraph L) (s : ℕ) where
  labels : ℕ → L
  sets : ℕ → Finset L
  left_mem : ∀ i < s, labels i ∈ sets i
  right_mem : ∀ i < s, labels i ∈ sets (i + 1)
  clique : ∀ i ≤ s, ∀ u ∈ sets i, ∀ v ∈ sets i, u = v ∨ G.Adj u v

namespace ArcData

variable {s : ℕ} (A : ArcData G s)

def Admissible (x y : ℕ) : Prop := ∃ l, l ∈ A.sets x ∧ l ∈ A.sets y

def Good (x y : ℕ) : Prop := y = x + 1 ∨ A.Admissible (x + 1) (y - 1)

structure Split (exteriorGood : Prop) where
  p₁ : ℕ
  p₂ : ℕ
  positive : 0 < p₁
  ordered : p₁ < p₂
  inside : p₂ < s
  odd₁ : p₁ % 2 = 1
  even₂ : p₂ % 2 = 0
  first : A.Admissible 0 p₁
  middle : A.Admissible p₁ p₂
  third : A.Admissible p₂ s
  some_good : (A.Good 0 p₁ ∧ A.Good p₂ s) ∨ (A.Good p₁ p₂ ∧ exteriorGood)
  outer_long : 1 < p₁ → 1 < s - p₂ → A.Good p₁ p₂ ∧ exteriorGood
  middle_long : 1 < p₂ - p₁ → A.Good 0 p₁ ∧ A.Good p₂ s

lemma trace (i : ℕ) (hi : i + 1 < s) :
    A.labels i = A.labels (i + 1) ∨ G.Adj (A.labels i) (A.labels (i + 1)) :=
  A.clique (i + 1) (by omega) _ (A.right_mem i (by omega)) _ (A.left_mem (i + 1) hi)

lemma edge_admissible (i : ℕ) (hi : i < s) : A.Admissible i (i + 1) :=
  ⟨A.labels i, A.left_mem i hi, A.right_mem i hi⟩

lemma last_mem (hs : 0 < s) : A.labels (s - 1) ∈ A.sets s := by
  convert A.right_mem (s - 1) (by omega) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  omega

lemma good_of_same_boundary (x y : ℕ) (hxy : x < y) (hy : y ≤ s)
    (heq : A.labels x = A.labels (y - 1)) : A.Good x y := by
  right
  refine ⟨A.labels x, A.right_mem x (by omega), ?_⟩
  rw [heq]
  exact A.left_mem (y - 1) (by omega)

lemma neighbor_return_between (hG : G.IsAcyclic) (P : L)
    (lo hi : ℕ) (hlo : lo ≤ hi) (hhi : hi < s)
    (havoid : ∀ i, lo ≤ i → i ≤ hi → A.labels i ≠ P)
    (hfirst : G.Adj P (A.labels lo)) (hlast : G.Adj P (A.labels hi)) :
    A.labels lo = A.labels hi := by
  have hf : G.Adj P ((fun i => A.labels (lo + i)) 0) := by simpa using hfirst
  have hl : G.Adj P ((fun i => A.labels (lo + i)) (hi - lo)) := by
    simpa only [Nat.add_sub_of_le hlo] using hlast
  have h := neighbor_return hG (fun i => A.labels (lo + i)) (hi - lo) P
    (fun i hi' => by
      have := A.trace (lo + i) (by omega)
      simpa only [Nat.add_assoc] using this)
    (fun i hi' => havoid (lo + i) (by omega) (by omega)) hf hl
  simpa only [Nat.add_zero, Nat.add_sub_of_le hlo] using h

lemma split_short_middle {exteriorGood : Prop} (hext : exteriorGood)
    (p : ℕ) (hp : 0 < p) (hps : p + 1 < s) (hodd : p % 2 = 1)
    (hfirst : A.Admissible 0 p) (hthird : A.Admissible (p + 1) s) :
    Nonempty (A.Split exteriorGood) := by
  refine ⟨⟨p, p + 1, hp, by omega, hps, hodd, by omega,
    hfirst, A.edge_admissible p (by omega), hthird, ?_, ?_, ?_⟩⟩
  · exact Or.inr ⟨Or.inl rfl, hext⟩
  · exact fun _ _ => ⟨Or.inl rfl, hext⟩
  · intro h
    omega

lemma split_short_outer (exteriorGood : Prop) (hs : 3 ≤ s) (hsodd : s % 2 = 1)
    (heq : A.labels 0 = A.labels (s - 1)) : Nonempty (A.Split exteriorGood) := by
  have hg₁ : A.Good 0 1 := Or.inl rfl
  have hg₃ : A.Good (s - 1) s := Or.inl (by omega)
  have ha₃ : A.Admissible (s - 1) s :=
    ⟨A.labels (s - 1), A.left_mem (s - 1) (by omega), A.last_mem (by omega)⟩
  have ha₂ : A.Admissible 1 (s - 1) := by
    refine ⟨A.labels 0, A.right_mem 0 (by omega), ?_⟩
    rw [heq]
    exact A.left_mem (s - 1) (by omega)
  refine ⟨⟨1, s - 1, by omega, by omega, by omega, by omega, by omega,
    A.edge_admissible 0 (by omega), ha₂, ha₃, Or.inl ⟨hg₁, hg₃⟩,
    ?_, fun _ => ⟨hg₁, hg₃⟩⟩⟩
  intro h
  omega

lemma split_good_exterior (hG : G.IsAcyclic) {exteriorGood : Prop} (hext : exteriorGood)
    (hs : 3 ≤ s) (hsodd : s % 2 = 1) (P : L)
    (hP₀ : P ∈ A.sets 0) (hPₛ : P ∈ A.sets s) : Nonempty (A.Split exteriorGood) := by
  classical
  by_cases hboundary : A.labels 0 = A.labels (s - 1)
  · exact A.split_short_outer exteriorGood hs hsodd hboundary
  by_cases hodd : ∃ i, i < s ∧ i % 2 = 1 ∧ A.labels i = P
  · obtain ⟨i, his, hi, hiP⟩ := hodd
    refine A.split_short_middle hext i (by omega) (by omega) hi ?_ ?_
    · exact ⟨P, hP₀, by simpa only [hiP] using A.left_mem i his⟩
    · exact ⟨P, by simpa only [hiP] using A.right_mem i his, hPₛ⟩
  have heven : ∀ i < s, A.labels i = P → i % 2 = 0 := by
    intro i his hiP
    have hm := Nat.mod_lt i (by omega : 0 < 2)
    by_contra hn
    exact hodd ⟨i, his, by omega, hiP⟩
  have hex : ∃ i, i < s ∧ A.labels i = P := by
    by_contra hnone
    push Not at hnone
    have hav : ∀ i, 0 ≤ i → i ≤ s - 1 → A.labels i ≠ P :=
      fun i _ hi => hnone i (by omega)
    have hadj₀ : G.Adj P (A.labels 0) :=
      (A.clique 0 (by omega) P hP₀ _ (A.left_mem 0 (by omega))).resolve_left
        (fun h => hnone 0 (by omega) h.symm)
    have hadjₛ : G.Adj P (A.labels (s - 1)) :=
      (A.clique s le_rfl P hPₛ _ (A.last_mem (by omega))).resolve_left
        (fun h => hnone (s - 1) (by omega) h.symm)
    exact hboundary (A.neighbor_return_between hG P 0 (s - 1) (by omega) (by omega)
      hav hadj₀ hadjₛ)
  by_cases hzero : A.labels 0 = P
  · let j := Nat.findGreatest (fun i => A.labels i = P) (s - 1)
    have hjle : j ≤ s - 1 := Nat.findGreatest_le _
    have hjP : A.labels j = P := Nat.findGreatest_spec (P := fun i => A.labels i = P) (by omega : 0 ≤ s - 1) hzero
    have hlast : A.labels (s - 1) ≠ P := fun h => hboundary (hzero.trans h.symm)
    have hjlt : j < s - 1 := by
      by_contra h
      have : j = s - 1 := by omega
      exact hlast (this ▸ hjP)
    have hjEven : j % 2 = 0 := heven j (by omega) hjP
    have hav : ∀ i, j + 1 ≤ i → i ≤ s - 1 → A.labels i ≠ P := by
      intro i hi his
      exact Nat.findGreatest_is_greatest (P := fun k => A.labels k = P) (by omega : j < i) his
    have hPa : P ∈ A.sets (j + 1) := by
      simpa only [hjP] using A.right_mem j (by omega)
    have hadjFirst : G.Adj P (A.labels (j + 1)) :=
      (A.clique (j + 1) (by omega) P hPa _ (A.left_mem (j + 1) (by omega))).resolve_left
        (fun h => hav (j + 1) le_rfl (by omega) h.symm)
    have hadjLast : G.Adj P (A.labels (s - 1)) :=
      (A.clique s le_rfl P hPₛ _ (A.last_mem (by omega))).resolve_left
        (fun h => hlast h.symm)
    have hQ := A.neighbor_return_between hG P (j + 1) (s - 1)
      (by omega) (by omega) hav hadjFirst hadjLast
    refine A.split_short_middle hext (j + 1) (by omega) (by omega) (by omega)
      ⟨P, hP₀, hPa⟩ ?_
    refine ⟨A.labels (j + 1), A.right_mem (j + 1) (by omega), ?_⟩
    rw [hQ]
    exact A.last_mem (by omega)
  · let i := Nat.find hex
    have hi : i < s := (Nat.find_spec hex).1
    have hiP : A.labels i = P := (Nat.find_spec hex).2
    have hiPos : 0 < i := by
      by_contra h
      have hi0 : i = 0 := by omega
      exact hzero (hi0 ▸ hiP)
    have hiEven : i % 2 = 0 := heven i hi hiP
    have hia : i - 1 + 1 = i := by omega
    have hav : ∀ k, 0 ≤ k → k ≤ i - 1 → A.labels k ≠ P := by
      intro k _ hk hkP
      have hkmin := Nat.find_min' hex (show k < s ∧ A.labels k = P from ⟨by omega, hkP⟩)
      change i ≤ k at hkmin
      omega
    have hPi : P ∈ A.sets i := by simpa only [hiP] using A.left_mem i hi
    have hprev : A.labels (i - 1) ∈ A.sets i := by
      simpa only [hia] using A.right_mem (i - 1) (by omega)
    have hadjFirst : G.Adj P (A.labels 0) :=
      (A.clique 0 (by omega) P hP₀ _ (A.left_mem 0 (by omega))).resolve_left
        (fun h => hzero h.symm)
    have hadjLast : G.Adj P (A.labels (i - 1)) :=
      (A.clique i (by omega) P hPi _ hprev).resolve_left
        (fun h => hav (i - 1) (by omega) le_rfl h.symm)
    have hQ := A.neighbor_return_between hG P 0 (i - 1) (by omega) (by omega)
      hav hadjFirst hadjLast
    refine A.split_short_middle hext (i - 1) (by omega) (by omega) (by omega) ?_ ?_
    · refine ⟨A.labels 0, A.left_mem 0 (by omega), ?_⟩
      rw [hQ]
      exact A.left_mem (i - 1) (by omega)
    · rw [hia]
      exact ⟨P, hPi, hPₛ⟩

lemma split_left_boundary (hG : G.IsAcyclic) (exteriorGood : Prop)
    (hs : 3 ≤ s) (hsodd : s % 2 = 1) (P : L)
    (hP₀ : P ∈ A.sets 0) (hPₛ : P ∈ A.sets s) (hzero : A.labels 0 = P) :
    Nonempty (A.Split exteriorGood) := by
  classical
  by_cases hlast : A.labels (s - 1) = P
  · exact A.split_short_outer exteriorGood hs hsodd (hzero.trans hlast.symm)
  let j := Nat.findGreatest (fun i => A.labels i = P) (s - 1)
  have hjle : j ≤ s - 1 := Nat.findGreatest_le _
  have hjP : A.labels j = P :=
    Nat.findGreatest_spec (P := fun i => A.labels i = P) (by omega : 0 ≤ s - 1) hzero
  have hjlt : j < s - 1 := by
    by_contra h
    have : j = s - 1 := by omega
    exact hlast (this ▸ hjP)
  have hav : ∀ i, j + 1 ≤ i → i ≤ s - 1 → A.labels i ≠ P := by
    intro i hi his
    exact Nat.findGreatest_is_greatest (P := fun k => A.labels k = P) (by omega : j < i) his
  have hPt : P ∈ A.sets (j + 1) := by
    simpa only [hjP] using A.right_mem j (by omega)
  have hadjFirst : G.Adj P (A.labels (j + 1)) :=
    (A.clique (j + 1) (by omega) P hPt _ (A.left_mem (j + 1) (by omega))).resolve_left
      (fun h => hav (j + 1) le_rfl (by omega) h.symm)
  have hadjLast : G.Adj P (A.labels (s - 1)) :=
    (A.clique s le_rfl P hPₛ _ (A.last_mem (by omega))).resolve_left
      (fun h => hlast h.symm)
  have hQ := A.neighbor_return_between hG P (j + 1) (s - 1)
    (by omega) (by omega) hav hadjFirst hadjLast
  by_cases htEven : (j + 1) % 2 = 0
  · have hg₁ : A.Good 0 1 := Or.inl rfl
    have hg₃ : A.Good (j + 1) s := A.good_of_same_boundary _ _ (by omega) le_rfl hQ
    have ha₂ : A.Admissible 1 (j + 1) :=
      ⟨P, by simpa only [hzero] using A.right_mem 0 (by omega), hPt⟩
    have ha₃ : A.Admissible (j + 1) s := by
      refine ⟨A.labels (j + 1), A.left_mem (j + 1) (by omega), ?_⟩
      rw [hQ]
      exact A.last_mem (by omega)
    refine ⟨⟨1, j + 1, by omega, by omega, by omega, by omega, htEven,
      A.edge_admissible 0 (by omega), ha₂, ha₃, Or.inl ⟨hg₁, hg₃⟩,
      ?_, fun _ => ⟨hg₁, hg₃⟩⟩⟩
    intro h
    omega
  · have htOdd : (j + 1) % 2 = 1 := by omega
    have hg₁ : A.Good 0 (j + 1) := by
      apply A.good_of_same_boundary _ _ (by omega) (by omega)
      simpa only [Nat.add_sub_cancel, hzero] using hjP.symm
    have hg₃ : A.Good (s - 1) s := Or.inl (by omega)
    have ha₁ : A.Admissible 0 (j + 1) := ⟨P, hP₀, hPt⟩
    have ha₂ : A.Admissible (j + 1) (s - 1) := by
      refine ⟨A.labels (j + 1), A.left_mem (j + 1) (by omega), ?_⟩
      rw [hQ]
      exact A.left_mem (s - 1) (by omega)
    have ha₃ : A.Admissible (s - 1) s :=
      ⟨A.labels (s - 1), A.left_mem (s - 1) (by omega), A.last_mem (by omega)⟩
    refine ⟨⟨j + 1, s - 1, by omega, by omega, by omega, htOdd, by omega,
      ha₁, ha₂, ha₃, Or.inl ⟨hg₁, hg₃⟩, ?_, fun _ => ⟨hg₁, hg₃⟩⟩⟩
    intro _ h
    omega

def reverse : ArcData G s where
  labels i := A.labels (s - 1 - i)
  sets i := A.sets (s - i)
  left_mem i hi := by
    have hj : s - 1 - i < s := by omega
    have heq : s - 1 - i + 1 = s - i := by omega
    simpa only [heq] using A.right_mem (s - 1 - i) hj
  right_mem i hi := by
    have hj : s - 1 - i < s := by omega
    have heq : s - 1 - i = s - (i + 1) := by omega
    simpa only [← heq] using A.left_mem (s - 1 - i) hj
  clique i hi := A.clique (s - i) (by omega)

lemma admissible_symm {x y : ℕ} (h : A.Admissible x y) : A.Admissible y x := by
  obtain ⟨l, hl₁, hl₂⟩ := h
  exact ⟨l, hl₂, hl₁⟩

lemma good_reverse {x y : ℕ} (hxy : x < y) (hy : y ≤ s)
    (h : A.reverse.Good x y) : A.Good (s - y) (s - x) := by
  rcases h with hshort | ⟨l, hl₁, hl₂⟩
  · left
    omega
  · right
    change l ∈ A.sets (s - (x + 1)) at hl₁
    change l ∈ A.sets (s - (y - 1)) at hl₂
    have h₁ : s - (x + 1) = s - x - 1 := by omega
    have h₂ : s - (y - 1) = s - y + 1 := by omega
    exact ⟨l, by simpa only [h₂] using hl₂, by simpa only [h₁] using hl₁⟩

def Split.unreverse {exteriorGood : Prop} (hsodd : s % 2 = 1)
    (T : A.reverse.Split exteriorGood) : A.Split exteriorGood := by
  have h₁ := T.positive
  have h₂ := T.ordered
  have h₃ := T.inside
  have ho := T.odd₁
  have he := T.even₂
  have ha₁ : A.Admissible 0 (s - T.p₂) := by
    have h := A.admissible_symm T.third
    simpa only [reverse, Nat.sub_self] using h
  have ha₂ : A.Admissible (s - T.p₂) (s - T.p₁) := A.admissible_symm T.middle
  have ha₃ : A.Admissible (s - T.p₁) s := by
    have h := A.admissible_symm T.first
    simpa only [reverse, Nat.sub_zero] using h
  have g₁ : A.reverse.Good T.p₂ s → A.Good 0 (s - T.p₂) := by
    intro h
    simpa only [Nat.sub_self] using A.good_reverse h₃ le_rfl h
  have g₂ : A.reverse.Good T.p₁ T.p₂ → A.Good (s - T.p₂) (s - T.p₁) :=
    A.good_reverse h₂ (by omega)
  have g₃ : A.reverse.Good 0 T.p₁ → A.Good (s - T.p₁) s := by
    intro h
    simpa only [Nat.sub_zero] using A.good_reverse h₁ (by omega) h
  refine ⟨s - T.p₂, s - T.p₁, by omega, by omega, by omega, by omega, by omega,
    ha₁, ha₂, ha₃, ?_, ?_, ?_⟩
  · rcases T.some_good with ⟨hf, ht⟩ | ⟨hm, hg⟩
    · exact Or.inl ⟨g₁ ht, g₃ hf⟩
    · exact Or.inr ⟨g₂ hm, hg⟩
  · intro hf ht
    obtain ⟨hm, hg⟩ := T.outer_long (by omega) (by omega)
    exact ⟨g₂ hm, hg⟩
  · intro hm
    obtain ⟨hf, ht⟩ := T.middle_long (by omega)
    exact ⟨g₁ ht, g₃ hf⟩

theorem split (hG : G.IsAcyclic) (exteriorGood : Prop)
    (hs : 3 ≤ s) (hsodd : s % 2 = 1) (P : L)
    (hP₀ : P ∈ A.sets 0) (hPₛ : P ∈ A.sets s)
    (hbad : ¬exteriorGood → A.labels 0 = P ∨ A.labels (s - 1) = P) :
    Nonempty (A.Split exteriorGood) := by
  classical
  by_cases hext : exteriorGood
  · exact A.split_good_exterior hG hext hs hsodd P hP₀ hPₛ
  rcases hbad hext with hleft | hright
  · exact A.split_left_boundary hG exteriorGood hs hsodd P hP₀ hPₛ hleft
  · have hP₀' : P ∈ A.reverse.sets 0 := by simpa only [reverse, Nat.sub_zero] using hPₛ
    have hPₛ' : P ∈ A.reverse.sets s := by simpa only [reverse, Nat.sub_self] using hP₀
    have hzero : A.reverse.labels 0 = P := by simpa only [reverse, Nat.sub_zero] using hright
    obtain ⟨T⟩ := A.reverse.split_left_boundary hG exteriorGood hs hsodd P hP₀' hPₛ' hzero
    exact ⟨T.unreverse A hsodd⟩

end ArcData

structure CycleData (G : SimpleGraph L) (m : ℕ) where
  labels : ℤ → L
  periodic : ∀ i, labels (i + m) = labels i
  adjacent : ∀ i, labels (i - 1) = labels i ∨ G.Adj (labels (i - 1)) (labels i)

end MatchingFPRAS.Cells

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Sets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Cells
open SimpleGraph

variable {L : Type*} {G : SimpleGraph L}
namespace CycleData

variable [DecidableEq L] {m : ℕ} (C : CycleData G m)

def sets (i : ℤ) : Finset L := {C.labels (i - 1), C.labels i}

def Admissible (x y : ℕ) : Prop := ∃ l, l ∈ C.sets x ∧ l ∈ C.sets y

def Good (x y : ℕ) : Prop := y = x + 1 ∨ C.Admissible (x + 1) (y - 1)

def ExteriorGood (x y : ℕ) : Prop :=
  y + 1 = x + m ∨ ∃ l, l ∈ C.sets ((y : ℤ) + 1) ∧ l ∈ C.sets ((x : ℤ) - 1)

lemma sets_clique (i : ℤ) : ∀ u ∈ C.sets i, ∀ v ∈ C.sets i, u = v ∨ G.Adj u v := by
  intro u hu v hv
  simp only [sets, Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact Or.inl rfl
  · exact C.adjacent i
  · exact (C.adjacent i).imp Eq.symm (fun h => h.symm)
  · exact Or.inl rfl

def arc (x s : ℕ) : ArcData G s where
  labels i := C.labels ((x : ℤ) + i)
  sets i := C.sets ((x : ℤ) + i)
  left_mem i _ := by simp [sets]
  right_mem i _ := by
    simp only [sets, Finset.mem_insert, Finset.mem_singleton]
    left
    congr 1
    push_cast
    omega
  clique i _ := C.sets_clique ((x : ℤ) + i)

lemma arc_admissible (x s u v : ℕ) :
    (C.arc x s).Admissible u v ↔ C.Admissible (x + u) (x + v) := by
  simp only [ArcData.Admissible, Admissible, arc, Nat.cast_add]

lemma arc_good (x s u v : ℕ) (huv : u < v) :
    (C.arc x s).Good u v ↔ C.Good (x + u) (x + v) := by
  have hv : 1 ≤ v := by omega
  have h₁ : x + u + 1 = x + (u + 1) := by omega
  have h₂ : x + v - 1 = x + (v - 1) := by omega
  simp only [ArcData.Good, Good, h₁, h₂, ← C.arc_admissible x s]
  constructor
  · rintro (h | h)
    · exact Or.inl (by omega)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (by omega)
    · exact Or.inr h

lemma bad_exterior_boundary (x s : ℕ) (hs : 0 < s) (P : L)
    (hP₀ : P ∈ (C.arc x s).sets 0) (hPₛ : P ∈ (C.arc x s).sets s)
    (hbad : ¬ C.ExteriorGood x (x + s)) :
    (C.arc x s).labels 0 = P ∨ (C.arc x s).labels (s - 1) = P := by
  by_contra h
  push Not at h
  rcases h with ⟨hleft, hright⟩
  have hcast : (↑(s - 1) : ℤ) = (s : ℤ) - 1 := by omega
  simp only [arc, Nat.cast_zero, add_zero] at hleft hP₀
  simp only [arc, hcast] at hright
  have h₀ : P = C.labels ((x : ℤ) - 1) := by
    simpa only [sets, Finset.mem_insert, Finset.mem_singleton, or_iff_left hleft.symm] using hP₀
  have hₛ : P = C.labels ((x : ℤ) + s) := by
    have hne : P ≠ C.labels ((x : ℤ) + s - 1) := by
      intro hh
      apply hright
      convert hh.symm using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      omega
    simpa only [arc, sets, Finset.mem_insert, Finset.mem_singleton, or_iff_right hne] using hPₛ
  apply hbad
  right
  refine ⟨P, ?_, ?_⟩
  · simp only [sets, Finset.mem_insert, Finset.mem_singleton]
    left
    convert hₛ using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    push_cast
    omega
  · simp only [sets, Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr h₀

structure Cell (x p q y : ℕ) : Prop where
  first_pos : x < p
  middle_pos : p < q
  third_pos : q < y
  odd_first : (p - x) % 2 = 1
  odd_middle : (q - p) % 2 = 1
  odd_third : (y - q) % 2 = 1
  odd_exterior : (m - (y - x)) % 2 = 1
  first : C.Admissible x p
  middle : C.Admissible p q
  third : C.Admissible q y
  exterior : C.Admissible y x
  some_good : (C.Good x p ∧ C.Good q y) ∨ (C.Good p q ∧ C.ExteriorGood x y)
  outer_long : 1 < p - x → 1 < y - q → C.Good p q ∧ C.ExteriorGood x y
  middle_exterior_long : 1 < q - p → 1 < m - (y - x) → C.Good x p ∧ C.Good q y

inductive Subdivision (C : CycleData G m) : ℕ → ℕ → Type _ where
  | edge {x y} (short : y = x + 1) : Subdivision C x y
  | node {x p q y} (cell : C.Cell x p q y)
      (first : Subdivision C x p) (middle : Subdivision C p q)
      (third : Subdivision C q y) : Subdivision C x y

lemma cell_of_split (x s : ℕ) (hm : m % 2 = 0) (hs : s % 2 = 1)
    (hbound : x + s < m) (hadm : C.Admissible x (x + s))
    (T : (C.arc x s).Split (C.ExteriorGood x (x + s))) :
    C.Cell x (x + T.p₁) (x + T.p₂) (x + s) := by
  have h₁ := T.positive
  have h₂ := T.ordered
  have h₃ := T.inside
  have ho := T.odd₁
  have he := T.even₂
  have ha₁ : C.Admissible x (x + T.p₁) := by
    simpa only [Nat.add_zero] using (C.arc_admissible x s 0 T.p₁).mp T.first
  have ha₂ := (C.arc_admissible x s T.p₁ T.p₂).mp T.middle
  have ha₃ := (C.arc_admissible x s T.p₂ s).mp T.third
  have hae : C.Admissible (x + s) x := by
    obtain ⟨l, hl₁, hl₂⟩ := hadm
    exact ⟨l, hl₂, hl₁⟩
  have g₁ : (C.arc x s).Good 0 T.p₁ → C.Good x (x + T.p₁) := by
    intro h
    simpa only [Nat.add_zero] using (C.arc_good x s 0 T.p₁ h₁).mp h
  have g₂ := (C.arc_good x s T.p₁ T.p₂ h₂).mp
  have g₃ := (C.arc_good x s T.p₂ s h₃).mp
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      ha₁, ha₂, ha₃, hae, ?_, ?_, ?_⟩
  · rcases T.some_good with ⟨hf, ht⟩ | ⟨hm, hg⟩
    · exact Or.inl ⟨g₁ hf, g₃ ht⟩
    · exact Or.inr ⟨g₂ hm, hg⟩
  · intro hf ht
    obtain ⟨hm, hg⟩ := T.outer_long (by omega) (by omega)
    exact ⟨g₂ hm, hg⟩
  · intro hmiddle _
    obtain ⟨hf, ht⟩ := T.middle_long (by omega)
    exact ⟨g₁ hf, g₃ ht⟩

theorem quadrangulate_arc (hG : G.IsAcyclic) (heven : m % 2 = 0)
    (s : ℕ) : ∀ x, 0 < s → s % 2 = 1 → x + s < m →
      C.Admissible x (x + s) → Nonempty (Subdivision C x (x + s)) := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro x hs hsodd hbound hadm
    by_cases hshort : s = 1
    · exact ⟨.edge (by omega)⟩
    have hslarge : 3 ≤ s := by omega
    obtain ⟨P, hP₀, hPₛ⟩ := hadm
    have hP₀' : P ∈ (C.arc x s).sets 0 := by simpa only [arc, Nat.cast_zero, add_zero] using hP₀
    have hPₛ' : P ∈ (C.arc x s).sets s := by simpa only [arc, Nat.cast_add] using hPₛ
    obtain ⟨T⟩ := (C.arc x s).split hG (C.ExteriorGood x (x + s)) hslarge hsodd P
      hP₀' hPₛ' (C.bad_exterior_boundary x s hs P hP₀' hPₛ')
    have h₁ := T.positive
    have h₂ := T.ordered
    have h₃ := T.inside
    have ho := T.odd₁
    have he := T.even₂
    have cell := C.cell_of_split x s heven hsodd hbound ⟨P, hP₀, hPₛ⟩ T
    obtain ⟨Q₁⟩ := ih T.p₁ (by omega) x h₁ ho (by omega) cell.first
    have eq₂ : x + T.p₁ + (T.p₂ - T.p₁) = x + T.p₂ := by omega
    have eq₃ : x + T.p₂ + (s - T.p₂) = x + s := by omega
    obtain ⟨Q₂⟩ := ih (T.p₂ - T.p₁) (by omega) (x + T.p₁) (by omega) (by omega)
      (by omega) (by simpa only [eq₂] using cell.middle)
    obtain ⟨Q₃⟩ := ih (s - T.p₂) (by omega) (x + T.p₂) (by omega) (by omega)
      (by omega) (by simpa only [eq₃] using cell.third)
    rw [eq₂] at Q₂
    rw [eq₃] at Q₃
    exact ⟨.node cell Q₁ Q₂ Q₃⟩

theorem quadrangulate (hG : G.IsAcyclic) (hm : 4 ≤ m) (heven : m % 2 = 0) :
    Nonempty (Subdivision C 0 (m - 1)) := by
  have hclose : C.labels ((m : ℤ) - 1) = C.labels (-1) := by
    calc
      C.labels ((m : ℤ) - 1) = C.labels (-1 + (m : ℤ)) := congrArg C.labels (by omega)
      _ = C.labels (-1) := C.periodic (-1)
  have hadm : C.Admissible 0 (0 + (m - 1)) := by
    refine ⟨C.labels (-1), ?_, ?_⟩
    · simp [sets]
    · simp only [Nat.zero_add, sets, Finset.mem_insert, Finset.mem_singleton]
      right
      rw [← hclose]
      congr 1
      omega
  simpa only [Nat.zero_add] using
    C.quadrangulate_arc hG heven (m - 1) 0 (by omega) (by omega) (by omega) hadm

namespace Subdivision

variable {C} {x y : ℕ}

def cells : {x y : ℕ} → Subdivision C x y → ℕ
  | _, _, .edge _ => 0
  | _, _, .node _ Q₁ Q₂ Q₃ => 1 + Q₁.cells + Q₂.cells + Q₃.cells

def sumCells : {x y : ℕ} → Subdivision C x y → (ℕ → ℕ → ℕ → ℕ → ℝ) → ℝ
  | _, _, .edge _, _ => 0
  | x, y, .node (p := p) (q := q) _ Q₁ Q₂ Q₃, localTerm =>
      localTerm x p q y + Q₁.sumCells localTerm + Q₂.sumCells localTerm + Q₃.sumCells localTerm

end Subdivision

end CycleData

end MatchingFPRAS.Cells

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_ChosenChord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Cells.CycleData

variable {L : Type*} [DecidableEq L] {G : SimpleGraph L} {m : ℕ} {C : CycleData G m}

@[ext] structure CellIndex where
  x : ℕ
  p : ℕ
  q : ℕ
  y : ℕ
  deriving DecidableEq

namespace Subdivision

variable {x y : ℕ}

def cellList : {x y : ℕ} → Subdivision C x y → List CellIndex
  | _, _, .edge _ => []
  | x, y, .node (p := p) (q := q) _ Q₁ Q₂ Q₃ =>
      ⟨x,p,q,y⟩ :: (Q₁.cellList ++ Q₂.cellList ++ Q₃.cellList)

lemma mem_cellList {Q : Subdivision C x y} {a : CellIndex} (ha : a ∈ Q.cellList) :
    x ≤ a.x ∧ a.y ≤ y ∧ C.Cell a.x a.p a.q a.y := by
  induction Q with
  | edge h => simp [cellList] at ha
  | @node x p q y h Q₁ Q₂ Q₃ ih₁ ih₂ ih₃ =>
    simp only [cellList, List.mem_cons, List.mem_append] at ha
    rcases ha with rfl | (ha | ha) | ha
    · exact ⟨le_rfl, le_rfl, h⟩
    · obtain ⟨hx,hy,hc⟩ := ih₁ ha
      exact ⟨hx, by have := h.middle_pos; have := h.third_pos; omega, hc⟩
    · obtain ⟨hx,hy,hc⟩ := ih₂ ha
      exact ⟨by have := h.first_pos; omega, by have := h.third_pos; omega, hc⟩
    · obtain ⟨hx,hy,hc⟩ := ih₃ ha
      exact ⟨by have := h.first_pos; have := h.middle_pos; omega, hy, hc⟩

def cellSet (Q : Subdivision C x y) : Finset CellIndex := Q.cellList.toFinset

end Subdivision

end MatchingFPRAS.Cells.CycleData

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_MatchingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

open Finset

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]

variable [DecidableEq V] [DecidableEq E] [DecidableEq F]

variable (inc : E → V → Prop) (inc' : F → V → Prop) (f : E ↪ F)

variable (hinc : ∀ e x,inc' (f e) x ↔ inc e x)

noncomputable def edgeExtension (w : E → ℝ) (q : F) : ℝ := by
  classical
  exact if h : ∃ e,f e=q then w h.choose else 0

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance instDecidableEqSourceLabel (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance instFintypeBagEdgeSourceVertexSourceLabelSourceBags (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

noncomputable def sourceRealLabel (w : V → V → ℝ) (K : ℕ) (e : SourceRealEdge V K) : SourceLabel w K :=
  edgeLabel (sourceRealB w K) (sourceRealB_comm w K) (sourceRealB_tri w K)
    (realLeft K) (realRight K) (sourceLevels w K) e

omit [Nontrivial V] in
lemma real_edge_not_diag [Nontrivial V] (K : ℕ) (e : SourceRealEdge V K) :
    ¬(edge source target (4*(2*K+2)) e.1 e.2).IsDiag := by
  rw [edge,Sym2.mk_isDiag_iff]
  intro he
  have hi := atVertex_injective source target (4*(2*K+2)) e.1 (source_ne_target e.1) he
  have := congrArg Fin.val hi
  simp at this

noncomputable def sourceColoredReal (w : V → V → ℝ) (K : ℕ) (e : SourceRealEdge V K) :
    BagEdge (sourceBags w K) :=
  ⟨⟨(edge source target (4*(2*K+2)) e.1 e.2,sourceRealLabel w K e),real_edge_not_diag K e⟩,by
    intro x hx
    apply (mem_memberships _ _ _ (realLeft K) (realRight K) (sourceLevels w K) x _).mpr
    refine ⟨e,?_,rfl⟩
    simpa [ColoredEdge.Incident,Incident,realLeft,realRight,edge] using hx⟩

lemma sourceColoredReal_injective (w : V → V → ℝ) (K : ℕ) :
    Function.Injective (sourceColoredReal w K) := by
  intro e f h
  apply edge_injective source target (4*(2*K+2)) (by omega)
  exact congrArg (fun q : BagEdge (sourceBags w K) => q.val.val.1) h

noncomputable def sourceRealEmbedding (w : V → V → ℝ) (K : ℕ) :
    SourceRealEdge V K ↪ BagEdge (sourceBags w K) :=
  ⟨sourceColoredReal w K,sourceColoredReal_injective w K⟩

noncomputable def sourceRealActivity (w : V → V → ℝ) (K : ℕ) (e : SourceRealEdge V K) : ℝ :=
  pathActivity (2*K+2) (fun e => bottleneck w (source e) (target e))
    (fun e => sourceHeight w (source e)) (fun e => sourceHeight w (target e)) (logicalActivity w) e.1 e.2

noncomputable def sourceRealPortion (w : V → V → ℝ) (K : ℕ) : BagEdge (sourceBags w K) → ℝ :=
  by classical exact edgeExtension (sourceRealEmbedding w K) (sourceRealActivity w K)

noncomputable def holeTerminals (K : ℕ) (H : Finset (SourceVertex V K)) : Finset V :=
  by classical exact univ.filter fun x => Sum.inl x∈H

noncomputable def holeInternals (K : ℕ) (H : Finset (SourceVertex V K)) (e : LogicalEdge V) :
    Finset (Fin (4*(2*K+2))) := by classical exact univ.filter fun i => Sum.inr (e,i)∈H

omit [Nontrivial V] in
lemma survivors_empty [Nontrivial V] (K : ℕ) : survivors (V := V) (E := LogicalEdge V) (4*(2*K+2)) ∅ (fun _ => ∅)=univ := by
  ext x
  cases x with
  | inl x => simp
  | inr ei => rcases ei with ⟨e,i⟩; simp



open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance instDecidableEqSourceLabel_1_rb8346f_1 (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _
noncomputable def bagHeight (w : V → V → ℝ) (K : ℕ) (l : SourceLabel w K) : ℝ := (2:ℝ)^l.1.val

noncomputable def sourceBagWeight (w : V → V → ℝ) (K D : ℕ)
    (e : BagEdge (sourceBags w K)) : ℝ :=
  sourceRealPortion w K e+bagHeight w K e.val.val.2/D

noncomputable def sourceD (K : ℕ) : ℕ :=
  100*Fintype.card (SourceVertex V K)^2*(100000000*(Fintype.card V+1)^4)

lemma sourceD_one (K : ℕ) : 1 ≤ sourceD (V:=V) K := by
  have hn : 0 < Fintype.card (SourceVertex V K) := Fintype.card_pos
  have hp : 0 < sourceD (V:=V) K := by
    dsimp [sourceD]
    positivity
  omega

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_PM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance instDecidableEqSourceLabel_2_rb8346f_1 (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _
omit [Nontrivial V] in
lemma sourceVertex_card_ge (K : ℕ) : Fintype.card V ≤ Fintype.card (SourceVertex V K) := by
  exact Fintype.card_le_of_injective (Sum.inl : V → SourceVertex V K) Sum.inl_injective

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Marked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Marking

open Finset MatchingFPRAS.Transport

variable {V E I : Type*} [Fintype V] [Fintype E] [Fintype I]

variable [DecidableEq V] [DecidableEq E] [DecidableEq I]

variable (inc : E → V → Prop)

abbrev Marked := Σ M : Matchings inc univ, (↥M.val → I)

noncomputable def mass (part : E → I → ℝ) (a : Marked (I:=I) inc) : ℝ :=
  ∏ e : a.1.val, part e.val (a.2 e)

def collapse (part : E → I → ℝ) (e : E) : ℝ := ∑ i,part e i

noncomputable def law (part : E → I → ℝ) (a : Marked (I:=I) inc) : ℝ :=
  mass inc part a/partitionWeight inc (collapse part) univ

end MatchingFPRAS.Marking

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.Representation Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance instDecidableEqSourceLabel_3 (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance instFintypeBagEdgeSourceVertexSourceLabelSourceBags_4 (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

noncomputable def frozenActivity (w w₁ : V → V → ℝ) (K : ℕ)
    (e : SourceRealEdge V K) : ℝ :=
  pathActivity (2*K+2) (fun e => bottleneck w (source e) (target e))
    (fun e => sourceHeight w (source e)) (fun e => sourceHeight w (target e))
    (logicalActivity w₁) e.1 e.2

noncomputable def frozenPortion (w w₁ : V → V → ℝ) (K : ℕ) : BagEdge (sourceBags w K) → ℝ :=
  by classical exact edgeExtension (sourceRealEmbedding w K) (frozenActivity w w₁ K)

noncomputable def sourceC (w : V → V → ℝ) (K : ℕ) : ℝ :=
  ∏ e : LogicalEdge V,pathConstant (2*K+2) (bottleneck w (source e) (target e))
    (sourceHeight w (source e)) (sourceHeight w (target e))

noncomputable def rawReweight (w w₁ : V → V → ℝ) (K : ℕ) (e : SourceRealEdge V K) : ℝ :=
  if e.2.val=2*(2*K+2) then logicalActivity w₁ e.1/logicalActivity w e.1 else 1

noncomputable def bagReweight (w w₁ : V → V → ℝ) (K : ℕ) (q : BagEdge (sourceBags w K)) : ℝ := by
  classical
  exact if h : ∃ e,sourceRealEmbedding w K e=q then rawReweight w w₁ K h.choose else 1

lemma bagReweight_on (w w₁ : V → V → ℝ) (K : ℕ) (e : SourceRealEdge V K) :
    bagReweight w w₁ K (sourceRealEmbedding w K e)=rawReweight w w₁ K e := by
  classical
  unfold bagReweight
  rw [dite_eq_left ⟨e,rfl⟩]
  exact congrArg (rawReweight w w₁ K) ((sourceRealEmbedding w K).injective
    (Exists.choose_spec (show ∃ e',sourceRealEmbedding w K e'=sourceRealEmbedding w K e from ⟨e,rfl⟩)))

noncomputable def centralEdge (w : V → V → ℝ) (K : ℕ) (e : LogicalEdge V) : BagEdge (sourceBags w K) :=
  sourceRealEmbedding w K (e,⟨2*(2*K+2),by omega⟩)

noncomputable def probePortion (w : V → V → ℝ) (K D : ℕ) (q : BagEdge (sourceBags w K)) : ℝ := by
  classical
  exact if ∃ e,centralEdge w K e=q then 1/(D:ℝ) else 0

noncomputable def sourcePortions (w : V → V → ℝ) (K D : ℕ)
    (e : BagEdge (sourceBags w K)) : Fin 3 → ℝ :=
  ![sourceRealPortion w K e,bagHeight w K e.val.val.2/D-probePortion w K D e,probePortion w K D e]

noncomputable def probePartial (w : V → V → ℝ) (K : ℕ) (e₀ : LogicalEdge V) :
    Partial (BagEdge.Incident (bags:=sourceBags w K)) := by
  classical
  refine ⟨{centralEdge w K e₀},?_,?_⟩
  · intro e he x hx
    exact (mem_support _ _ _).mpr ⟨e,he,hx⟩
  · intro x hx
    obtain ⟨e,he,hex⟩ := (mem_support _ _ _).mp hx
    refine ⟨e,⟨he,hex⟩,?_⟩
    intro f hf
    exact (mem_singleton.mp hf.1).trans (mem_singleton.mp he).symm

open scoped Classical

abbrev SourceMarked (w : V → V → ℝ) (K : ℕ) :=
  Marking.Marked (I:=Fin 3) (BagEdge.Incident (bags:=sourceBags w K))

noncomputable def sourceLaw (w : V → V → ℝ) (K D : ℕ) : SourceMarked w K → ℝ :=
  Marking.law BagEdge.Incident (sourcePortions w K D)

noncomputable def observableA (w : V → V → ℝ) (K : ℕ) (a : SourceMarked w K) : ℝ := by
  classical exact if a.2=(fun _ => 0) then 1 else 0

noncomputable def observableD (w w₁ : V → V → ℝ) (K : ℕ) (a : SourceMarked w K) : ℝ := by
  classical exact if a.2=(fun _ => 0) then ∏ e ∈ a.1.val,bagReweight w w₁ K e else 0

noncomputable def observableProbe (w w₁ : V → V → ℝ) (K : ℕ) (e₀ : LogicalEdge V)
    (a : SourceMarked w K) : ℝ := by
  classical exact if {centralEdge w K e₀}⊆a.1.val ∧
      a.2=(fun e => if e.val∈({centralEdge w K e₀} : Finset _) then 2 else 0)
    then ∏ e ∈ a.1.val \ {centralEdge w K e₀},bagReweight w w₁ K e else 0

noncomputable def sourceBagZ (w : V → V → ℝ) (K D : ℕ) : ℝ :=
  partitionWeight BagEdge.Incident (sourceBagWeight w K D) univ

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_Tv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Variation

open Finset
open scoped Classical

variable {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]

noncomputable def iid (p : Ω → ℝ) (n : ℕ) (x : Fin n → Ω) : ℝ := ∏ i,p (x i)

omit [Fintype Ω] in
lemma iid_nonneg (p : Ω → ℝ) (hp : ∀ x,0 ≤ p x) (n : ℕ) (x : Fin n → Ω) : 0 ≤ iid p n x :=
  prod_nonneg fun _ _ => hp _

lemma iid_sum (p : Ω → ℝ) (hs : ∑ x,p x=1) (n : ℕ) : ∑ x,iid p n x=1 := by
  unfold iid
  rw [←Fintype.prod_sum]
  simp [hs]


end MatchingFPRAS.Variation

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_RunBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Counting

open Finset

abbrev alpha : ℚ := 1/100000

lemma others_nonempty {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : (univ.erase i).Nonempty := by
  let j : Fin n := ⟨if i.val=0 then 1 else 0, by split_ifs <;> omega⟩
  refine ⟨j,mem_erase.mpr ⟨?_,mem_univ _⟩⟩
  apply Fin.ne_of_val_ne
  dsimp [j]; split_ifs <;> omega

def rowMaximum {n : ℕ} (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ) (i : Fin n) : ℚ :=
  (univ.erase i).sup' (others_nonempty hn i) (fun j => G i j / v j)

def scaleUpdate {n : ℕ} (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ) (i : Fin n) : Fin n → ℚ :=
  Function.update v i (rowMaximum hn G v i)

def scalingTrace {n : ℕ} (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ) : ℕ → Fin n → ℚ
  | 0 => fun _ => 2
  | k+1 => if hk : k<n then scaleUpdate hn G (scalingTrace hn G k) ⟨k,hk⟩ else scalingTrace hn G k



open Finset

variable {n : ℕ}

structure ScaleInvariant (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ) : Prop where
  lower : ∀ i, alpha/2 ≤ v i
  upper : ∀ i, v i ≤ 2
  feasible : ∀ i j, i≠j → G i j ≤ v i*v j

lemma ScaleInvariant.pos {G : Fin n → Fin n → ℚ} {v : Fin n → ℚ}
    (hv : ScaleInvariant G v) (i) : 0 < v i := lt_of_lt_of_le (by norm_num [alpha]) (hv.lower i)

lemma rowMaximum_le (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ)
    (hv : ScaleInvariant G v) (i) : rowMaximum hn G v i ≤ v i := by
  apply Finset.sup'_le
  intro j hj
  exact (div_le_iff₀ (hv.pos j)).mpr (hv.feasible i j (mem_erase.mp hj).1.symm)

lemma ratio_le_rowMaximum (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ)
    (i j) (hji : j≠i) : G i j/v j ≤ rowMaximum hn G v i :=
  Finset.le_sup' (fun j => G i j/v j) (mem_erase.mpr ⟨hji,mem_univ _⟩)

lemma rowMaximum_lower (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ)
    (hG : ∀ i j, i≠j → alpha ≤ G i j) (hv : ScaleInvariant G v) (i) :
    alpha/2 ≤ rowMaximum hn G v i := by
  obtain ⟨j,hj⟩ := others_nonempty hn i
  have hji := (mem_erase.mp hj).1
  apply le_trans _ (ratio_le_rowMaximum hn G v i j hji)
  apply (le_div_iff₀ (hv.pos j)).mpr
  have hGi := hG i j hji.symm
  have hvi := hv.upper j
  norm_num [alpha] at *
  linarith

lemma scaleUpdate_le (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ)
    (hv : ScaleInvariant G v) (i j) : scaleUpdate hn G v i j ≤ v j := by
  by_cases hji : j=i
  · subst j; simpa [scaleUpdate] using rowMaximum_le hn G v hv i
  · simp [scaleUpdate,Function.update_of_ne hji]

lemma scaleUpdate_invariant (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ)
    (hsym : ∀ i j, G i j=G j i) (hG : ∀ i j, i≠j → alpha ≤ G i j)
    (hv : ScaleInvariant G v) (i) : ScaleInvariant G (scaleUpdate hn G v i) := by
  constructor
  · intro j
    by_cases hji : j=i
    · subst j; simpa [scaleUpdate] using rowMaximum_lower hn G v hG hv i
    · simpa [scaleUpdate,Function.update_of_ne hji] using hv.lower j
  · intro j; exact (scaleUpdate_le hn G v hv i j).trans (hv.upper j)
  · intro a b hab
    by_cases hai : a=i
    · subst a
      have hb := (div_le_iff₀ (hv.pos b)).mp (ratio_le_rowMaximum hn G v i b hab.symm)
      simpa [scaleUpdate,Function.update_of_ne hab.symm] using hb
    · by_cases hbi : b=i
      · subst b
        have ha := (div_le_iff₀ (hv.pos a)).mp (ratio_le_rowMaximum hn G v i a hai)
        simpa [scaleUpdate,Function.update_of_ne hai,hsym i a,mul_comm] using ha
      · simpa [scaleUpdate,Function.update_of_ne hai,Function.update_of_ne hbi] using hv.feasible a b hab

lemma scaleUpdate_tight (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ)
    (hv : ScaleInvariant G v) (i) :
    ∃ j, j≠i ∧ scaleUpdate hn G v i i*scaleUpdate hn G v i j=G i j := by
  obtain ⟨j,hj,heq⟩ := Finset.exists_mem_eq_sup' (others_nonempty hn i) (fun j => G i j/v j)
  have hji := (mem_erase.mp hj).1
  refine ⟨j,hji,?_⟩
  change rowMaximum hn G v i = G i j/v j at heq
  simp only [scaleUpdate,Function.update_self,Function.update_of_ne hji]
  rw [heq]
  exact div_mul_cancel₀ _ (hv.pos j).ne'

lemma tight_persists (G : Fin n → Fin n → ℚ) (v v' : Fin n → ℚ)
    (hv : ScaleInvariant G v) (hv' : ScaleInvariant G v') (hdown : ∀ i, v' i ≤ v i)
    (i j) (hji : j≠i) (hij : v i*v j=G i j) : v' i*v' j=G i j := by
  apply le_antisymm
  · calc
      _ ≤ v i*v j := mul_le_mul (hdown i) (hdown j) (hv'.pos j).le (hv.pos i).le
      _ = _ := hij
  · exact hv'.feasible i j hji.symm




lemma scalingTrace_invariant (hn : 2 ≤ n) (G : Fin n → Fin n → ℚ)
    (hsym : ∀ i j, G i j=G j i) (hG : ∀ i j, i≠j → alpha ≤ G i j ∧ G i j ≤ 3)
    (k : ℕ) : ScaleInvariant G (scalingTrace hn G k) ∧
      ∀ i, i.val<k → ∃ j, j≠i ∧ scalingTrace hn G k i*scalingTrace hn G k j=G i j := by
  induction k with
  | zero =>
    constructor
    · constructor
      · intro i; norm_num [scalingTrace,alpha]
      · intro i; simp [scalingTrace]
      · intro i j h; have := (hG i j h).2; simp only [scalingTrace]; linarith
    · intro i hi; omega
  | succ k ih =>
    by_cases hk : k<n
    · let i : Fin n := ⟨k,hk⟩
      have hinv := scaleUpdate_invariant hn G (scalingTrace hn G k) hsym (fun i j h => (hG i j h).1) ih.1 i
      have htrace : scalingTrace hn G (k+1)=scaleUpdate hn G (scalingTrace hn G k) i := by
        simp [scalingTrace,hk,i]
      rw [htrace]
      refine ⟨hinv,?_⟩
      intro a ha
      by_cases hak : a.val<k
      · obtain ⟨j,hj,he⟩ := ih.2 a hak
        refine ⟨j,hj,?_⟩
        exact tight_persists G _ _ ih.1 hinv (scaleUpdate_le hn G _ ih.1 i) a j hj he
      · have hai : a=i := Fin.ext (by dsimp [i]; omega)
        subst a
        exact scaleUpdate_tight hn G _ ih.1 i
    · have htrace : scalingTrace hn G (k+1)=scalingTrace hn G k := by simp [scalingTrace,hk]
      rw [htrace]
      refine ⟨ih.1,?_⟩
      intro i _
      exact ih.2 i (by have := i.isLt; omega)



open Finset



def sigma (D K : ℕ) (epsilon : ℚ) : ℚ := min (alpha/(100*D)) (epsilon/(1000*K))

def ratioEstimate (abar dbar : ℚ) : ℚ := if 0<abar then dbar/abar else 1

def upperEstimate (D : ℕ) (dbar zbar : ℚ) : ℚ :=
  if 0<dbar then max alpha (min 3 ((D:ℚ)*zbar/dbar+alpha)) else 1

end MatchingFPRAS.Counting

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Certify
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ComputableReach

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

variable (G : SimpleGraph α) [DecidableRel G.Adj]

def grow (s : Finset α) : Finset α := s ∪ univ.filter (fun b => ∃ a ∈ s, G.Adj a b)

def reached (s : Finset α) (n : ℕ) : Finset α := (grow G)^[n] s

def closure (a : α) : Finset α := reached G {a} (Fintype.card α)

lemma mem_grow (s : Finset α) (b : α) :
    b ∈ grow G s ↔ b ∈ s ∨ ∃ a ∈ s, G.Adj a b := by simp [grow]

lemma subset_grow (s : Finset α) : s ⊆ grow G s := subset_union_left

lemma reached_step (s : Finset α) (n : ℕ) : reached G s (n+1) = grow G (reached G s n) :=
  Function.iterate_succ_apply' _ _ _

lemma reached_step' (s : Finset α) (n : ℕ) : reached G s (n+1) = reached G (grow G s) n :=
  Function.iterate_succ_apply _ _ _

lemma reached_succ (s : Finset α) (n : ℕ) : reached G s n ⊆ reached G s (n+1) := by
  rw [reached_step]
  exact subset_grow G _

lemma reached_mono_time (s : Finset α) : Monotone (reached G s) :=
  monotone_nat_of_le_succ (reached_succ G s)

lemma reached_reachable (a b : α) (n : ℕ) (h : b ∈ reached G {a} n) : G.Reachable a b := by
  induction n generalizing b with
  | zero =>
    have hb : b=a := by simpa [reached] using h
    subst b
    exact SimpleGraph.Reachable.refl a
  | succ n ih =>
    rw [reached_step,mem_grow] at h
    rcases h with h | ⟨c,hc,hcb⟩
    · exact ih b h
    · exact (ih c hc).trans hcb.reachable

lemma walk_reached {s : Finset α} {a b : α} (p : G.Walk a b) (ha : a ∈ s) :
    b ∈ reached G s p.length := by
  induction p generalizing s with
  | nil => exact ha
  | @cons a b c hab p ih =>
    rw [SimpleGraph.Walk.length_cons,reached_step']
    exact ih ((mem_grow G s b).mpr (Or.inr ⟨a,ha,hab⟩))

@[simp] theorem mem_closure (a b : α) : b ∈ closure G a ↔ G.Reachable a b := by
  constructor
  · exact reached_reachable G a b _
  · rintro ⟨p⟩
    exact reached_mono_time G {a} p.toPath.isPath.length_lt.le
      (walk_reached G p.toPath.val (mem_singleton_self a))

end MatchingFPRAS.ComputableReach

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RemainingBags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh.Computable

open Finset MatchingFPRAS.Transport

variable {V L : Type*} [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L]

variable {bags : V → Finset L}

instance allowedDec (e : ColoredEdge V L) : Decidable (Allowed bags e) :=
  inferInstanceAs (Decidable (∀ x,x∈e.val.1 → e.val.2∈bags x))

end MatchingFPRAS.UnitRefresh.Computable

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Sym2Order
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

open Finset Variation

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

@[instance_reducible] def sym2Order : LinearOrder (Sym2 V) :=
  LinearOrder.lift' (fun e=>toLex (Sym2.sortEquiv e).val)
    (fun _ _ h=>Sym2.sortEquiv.injective (Subtype.ext (toLex.injective h)))

attribute [local instance] sym2Order

@[instance_reducible] def bagEdgeOrder {bags : V → Finset L} : LinearOrder (BagEdge bags) :=
  LinearOrder.lift' (fun e : BagEdge bags=>toLex e.val.val)
    (fun _ _ h=>Subtype.ext (Subtype.ext (toLex.injective h)))

attribute [local instance] bagEdgeOrder

variable {bags : V → Finset L} {G : SimpleGraph L}

variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)

attribute [local instance] UnitRefresh.Computable.allowedDec

@[instance_reducible] def bagEdgeFintype : Fintype (BagEdge bags) := Subtype.fintype (Allowed bags)

attribute [local instance] bagEdgeFintype

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_DiscreteLadderSteps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.BottleneckAlgorithm

open Finset MatchingFPRAS.Switching

variable {V : Type*} [Fintype V] [LinearOrder V]

variable {α : Type*} [LinearOrder α] [OfNat α 1]

def edge (w : V → V → α) (a b : V) : α := if a<b then w a b else w b a

def seed (w : V → V → α) (a b : V) : α := if a=b then 1 else max 1 (edge w a b)

def advance (w : V → V → α) (a b : V) : α :=
  if a=b then 1 else max (w a b)
    (univ.sup' ⟨a,mem_univ a⟩ fun c => min (w a c) (w c b))

def close (w : V → V → α) : ℕ → V → V → α
  | 0 => seed w
  | k+1 => advance (close w k)

@[simp] lemma close_diag (w : V → V → α) (k : ℕ) (a : V) : close w k a a=1 := by
  cases k <;> simp [close,seed,advance]

lemma close_one (w : V → V → α) (k : ℕ) (a b : V) : 1 ≤ close w k a b := by
  induction k with
  | zero =>
    by_cases hab : a=b
    · simp [close,seed,hab]
    · simp [close,seed,hab]
  | succ k ih =>
    by_cases h : a=b
    · subst b; simp
    · exact ih.trans (by simp [close,advance,h])

lemma close_mono_step (w : V → V → α) (k : ℕ) (a b : V) :
    close w k a b ≤ close w (k+1) a b := by
  by_cases h : a=b
  · subst b; simp
  · simp [close,advance,h]

lemma close_mono (w : V → V → α) (a b : V) : Monotone (fun k=>close w k a b) :=
  monotone_nat_of_le_succ (fun k=>close_mono_step w k a b)

lemma edge_le_close (w : V → V → α) (k : ℕ) (a b : V) (hab : a≠b) :
    edge w a b ≤ close w k a b := by
  have h : edge w a b ≤ close w 0 a b := by
    simp [close,seed,hab]
  exact h.trans (close_mono w a b (Nat.zero_le k))

lemma via_le_close (w : V → V → α) (k : ℕ) (a b c : V) (hab : a≠b) :
    min (close w k a c) (close w k c b) ≤ close w (k+1) a b := by
  exact (le_sup' (fun c=>min (close w k a c) (close w k c b)) (mem_univ c)).trans
    (by simp [close,advance,hab])

lemma chain_le_close (w : V → V → α) (t : α) (a b : V) (L : List V)
    (hab : a≠b) (hc : List.IsChain (fun x y=>t≤edge w x y) (a::L))
    (hn : (a::L).Nodup) (hb : b∈L) : t ≤ close w L.length a b := by
  induction L generalizing a with
  | nil => simp at hb
  | cons c cs ih =>
    rcases List.isChain_cons_cons.mp hc with ⟨hac,hc⟩
    have han := List.nodup_cons.mp hn
    have hne : a≠c := by intro h; apply han.1; simp [h]
    rcases List.mem_cons.mp hb with rfl|hb
    · exact hac.trans (edge_le_close w _ _ _ hne)
    · have hcb : c≠b := by
        intro he
        exact (List.nodup_cons.mp han.2).1 (he ▸ hb)
      have hh := ih c hcb hc han.2 hb
      change t ≤ close w (cs.length+1) a b
      exact (le_min (hac.trans (edge_le_close w cs.length a c hne)) hh).trans
        (via_le_close w cs.length a b c hab)

lemma close_le (w B : V → V → α) (_hdiag : ∀ a,B a a=1) (hone : ∀ a b,1≤B a b)
    (hedge : ∀ a b,a≠b → edge w a b≤B a b)
    (htri : ∀ a b c,a≠b → a≠c → b≠c → min (B a c) (B c b)≤B a b)
    (k : ℕ) (a b : V) : close w k a b≤B a b := by
  induction k generalizing a b with
  | zero =>
    by_cases hab : a=b
    · subst b; simpa [close,seed] using hone a a
    · simpa [close,seed,hab] using max_le (hone a b) (hedge a b hab)
  | succ k ih =>
    by_cases hab : a=b
    · subst b; simpa using hone a a
    · change (if a=b then 1 else _)≤_
      rw [ite_eq_right hab]
      apply max_le (ih a b)
      apply sup'_le
      intro c _
      by_cases hac : a=c
      · subst c
        rw [close_diag]
        exact (min_le_left _ _).trans (hone a b)
      by_cases hbc : b=c
      · subst c
        rw [close_diag]
        exact (min_le_right _ _).trans (hone a b)
      exact (min_le_min (ih a c) (ih c b)).trans (htri a b c hab hac hbc)

theorem real_close_eq (w : V → V → ℝ) (a b : V) :
    close w (Fintype.card V) a b=bottleneck w a b := by
  apply le_antisymm
  · exact close_le w (bottleneck w) (by intro a; simp [bottleneck])
      (one_le_bottleneck w) (edgeActivity_le_bottleneck w) (bottleneck_ultrametric w) _ _ _
  · by_cases hab : a=b
    · subst b; simp [bottleneck]
    by_cases ht : 1<bottleneck w a b
    · obtain ⟨L,hL,hnd,hb⟩ := bottleneck_path w a b hab ht
      have hlen := hnd.length_le_card
      have h := chain_le_close w (bottleneck w a b) a b L hab hL hnd hb
      exact h.trans (close_mono w a b (by simpa using (show L.length≤Fintype.card V from by simpa using (Nat.le_of_succ_le hlen))))
    · exact (le_of_not_gt ht).trans (close_one w _ _ _)

lemma cast_close (w : V → V → ℚ) (k : ℕ) (a b : V) :
    ((close w k a b : ℚ) : ℝ)=close (fun x y => (w x y : ℝ)) k a b := by
  induction k generalizing a b with
  | zero =>
    unfold close seed edge
    split_ifs <;> simp [Rat.cast_max]
  | succ k ih =>
    simp only [close,advance]
    split_ifs with hab
    · simp
    · have hh := Finset.apply_sup'_eq_sup'_comp (s:=(univ:Finset V))
        (f:=fun c=>min (close w k a c) (close w k c b)) ⟨a,mem_univ a⟩
        (fun x : ℚ => (x : ℝ)) (by intro x y; exact Rat.cast_max x y)
      rw [Rat.cast_max]
      apply congrArg₂ max (ih a b)
      calc
        _ = _ := hh
        _ = _ := by
          apply Finset.sup'_congr _ rfl
          intro c _
          simp [Rat.cast_min,ih]

theorem rational_close_eq (w : V → V → ℚ) (a b : V) :
    ((close w (Fintype.card V) a b : ℚ) : ℝ)=bottleneck (fun x y=>(w x y:ℝ)) a b := by
  rw [cast_close,real_close_eq]

end MatchingFPRAS.BottleneckAlgorithm

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RelabelWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Enlargement
open Transport

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
noncomputable local instance relabelWeightsSourceLabelDecidableEq (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _
noncomputable local instance relabelWeightsSourceBagEdgeFintype (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _
end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_CompleteGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Counting

def scheduleAdmissible (n : ℕ) (epsilon : ℚ) (k : ℕ) : Prop :=
  1 ≤ k ∧ (n:ℚ)^(n/2)/(1+1/(n:ℚ))^k ≤ epsilon/32



theorem counting_schedule_exists (n : ℕ) (hn : 2 ≤ n) (epsilon : ℚ)
    (he : 0 < epsilon) (he1 : epsilon < 1) :
    ∃ K : ℕ, scheduleAdmissible n epsilon K ∧
      (∀ k, scheduleAdmissible n epsilon k → K ≤ k) ∧
      (K:ℝ) ≤ 1+2*n*((n/2:ℕ)*Real.log n+Real.log (32/(epsilon:ℝ))) := by
  classical
  have hnr : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have her : (0:ℝ) < epsilon := by exact_mod_cast he
  have he1r : (epsilon:ℝ) < 1 := by exact_mod_cast he1
  let b : ℝ := 1+1/(n:ℝ)
  have hb : 1 < b := by
    dsimp [b]
    have ht : 0 < 1/(n:ℝ) := by positivity
    linarith
  have hb0 : 0 < b := by linarith
  have hlog : 1/(2*(n:ℝ)) ≤ Real.log b := by
    have h := Real.one_sub_inv_le_log_of_pos hb0
    have hcalc : 1/(2*(n:ℝ)) ≤ 1-b⁻¹ := by
      dsimp [b]
      field_simp
      nlinarith
    exact hcalc.trans h
  let L : ℝ := (n/2:ℕ)*Real.log n+Real.log (32/(epsilon:ℝ))
  have hratio : 1 < 32/(epsilon:ℝ) := (lt_div_iff₀ her).mpr (by linarith)
  have hL : 0 < L := by
    have ha : 0 ≤ (n/2:ℕ)*Real.log (n:ℝ) := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
    have hb := Real.log_pos hratio
    dsimp [L]
    linarith
  let C : ℝ := 2*n*L
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let k : ℕ := ⌊C⌋₊+1
  have hk1 : 1 ≤ k := by dsimp [k]; omega
  have hkt : C < (k:ℝ) := by
    dsimp [k]
    exact_mod_cast Nat.lt_floor_add_one C
  have hku : (k:ℝ) ≤ C+1 := by
    dsimp [k]
    push_cast
    linarith [Nat.floor_le hC]
  have hkl : L ≤ (k:ℝ)*Real.log b := by
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_left hlog hk0
    have hsmall : L ≤ (k:ℝ)*(1/(2*(n:ℝ))) := by
      rw [mul_one_div]
      apply (le_div_iff₀ (by positivity : 0 < 2*(n:ℝ))).mpr
      dsimp [C] at hkt
      nlinarith
    exact hsmall.trans hm
  have ha0 : (0:ℝ) < (n:ℝ)^(n/2)/b^k := by positivity
  have ht0 : (0:ℝ) < (epsilon:ℝ)/32 := by positivity
  have hlogratio : Real.log ((n:ℝ)^(n/2)/b^k) ≤ Real.log ((epsilon:ℝ)/32) := by
    rw [Real.log_div (by positivity) (by positivity),Real.log_pow,Real.log_pow]
    have hcancel : Real.log ((epsilon:ℝ)/32) = -Real.log (32/(epsilon:ℝ)) := by
      rw [Real.log_div (by positivity) (by norm_num),Real.log_div (by norm_num) (by positivity)]
      ring
    rw [hcancel]
    dsimp [L] at hkl
    linarith
  have hreal : (n:ℝ)^(n/2)/(1+1/(n:ℝ))^k ≤ (epsilon:ℝ)/32 :=
    (Real.log_le_log_iff ha0 ht0).mp hlogratio
  have hrat : (n:ℚ)^(n/2)/(1+1/(n:ℚ))^k ≤ epsilon/32 := by
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact hreal
  have hex : ∃ k, scheduleAdmissible n epsilon k := ⟨k,hk1,hrat⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_, ?_⟩
  · intro j hj
    exact Nat.find_min' hex hj
  · have hleast : Nat.find hex ≤ k := Nat.find_min' hex ⟨hk1,hrat⟩
    have hlr : (Nat.find hex:ℝ) ≤ k := by exact_mod_cast hleast
    change (Nat.find hex:ℝ) ≤ 1+C
    linarith

end MatchingFPRAS.Counting

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RatWeight
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance instDecidableEqSourceLabel_6 (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance instFintypeBagEdgeSourceVertexSourceLabelSourceBags_7 (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

open scoped Classical

end MatchingFPRAS.Enlargement

noncomputable section

namespace MatchingFPRAS.RealStage

open Finset

abbrev alpha : ℝ := 1/100000



open Finset

end MatchingFPRAS.RealStage

end

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RowPeak
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MatchingFPRAS.RealStage

open Finset

variable {n : ℕ}



open Finset



def sigma (D K : ℕ) (epsilon : ℝ) : ℝ := min (alpha/(100*D)) (epsilon/(1000*K))

def ratioEstimate (abar dbar : ℝ) : ℝ := if 0<abar then dbar/abar else 1

def upperEstimate (D : ℕ) (dbar zbar : ℝ) : ℝ :=
  if 0<dbar then max alpha (min 3 ((D:ℝ)*zbar/dbar+alpha)) else 1



end MatchingFPRAS.RealStage

end

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset
open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V]

def pairEdge (i j : V) (hij : i≠j) : LogicalEdge V :=
  ⟨(min i j,max i j),min_lt_max.mpr hij⟩

omit [Fintype V] in
lemma pairEdge_swap (i j : V) (hij : i≠j) : pairEdge i j hij=pairEdge j i hij.symm := by
  apply Subtype.ext
  simp [pairEdge,min_comm,max_comm]

noncomputable def probeMatrix (z : LogicalEdge V → ℝ) (i j : V) : ℝ :=
  if hij : i=j then 0 else z (pairEdge i j hij)

omit [Fintype V] in
lemma probeMatrix_off (z : LogicalEdge V → ℝ) (i j : V) (hij : i≠j) :
    probeMatrix z i j=z (pairEdge i j hij) := dite_eq_right hij

omit [Fintype V] in
lemma probeMatrix_symm (z : LogicalEdge V → ℝ) (i j : V) : probeMatrix z i j=probeMatrix z j i := by
  by_cases hij : i=j
  · subst j; rfl
  · rw [probeMatrix_off _ _ _ hij,probeMatrix_off _ _ _ (Ne.symm hij),pairEdge_swap]

noncomputable def estimateMatrix (D : ℕ) (dbar : ℝ) (zbar : LogicalEdge V → ℝ) (i j : V) : ℝ :=
  RealStage.upperEstimate D dbar (probeMatrix zbar i j)

variable [Nontrivial V]

noncomputable local instance instDecidableEqSourceLabel_7 (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance instFintypeBagEdgeSourceVertexSourceLabelSourceBags_8 (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

noncomputable def meanA (w : V → V → ℝ) (K : ℕ) : ℝ :=
  ∑ q : SourceMarked w K,sourceLaw w K (sourceD (V:=V) K) q*observableA w K q

noncomputable def meanD (w w₁ : V → V → ℝ) (K : ℕ) : ℝ :=
  ∑ q : SourceMarked w K,sourceLaw w K (sourceD (V:=V) K) q*observableD w w₁ K q

noncomputable def meanProbe (w w₁ : V → V → ℝ) (K : ℕ) (e : LogicalEdge (V)) : ℝ :=
  ∑ q : SourceMarked w K,sourceLaw w K (sourceD (V:=V) K) q*observableProbe w w₁ K e q

variable {n : ℕ} [Nontrivial (Fin n)]

noncomputable local instance instDecidableEqSourceLabelFin_rb8346f_1 (w : Fin n → Fin n → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _
structure StageData (n K T : ℕ) where
  hn : 2 ≤ n
  w : Fin n → Fin n → ℝ
  next : Fin n → Fin n → ℝ
  positive : ∀ i j,0 < w i j
  next_positive : ∀ i j,0 < next i j
  partition_positive : 0 < partition w ∅
  lower : ∀ i,(1:ℝ)/4 ≤ rowMax (by simpa using hn) w i
  upper : ∀ i,rowMax (by simpa using hn) w i ≤ 1
  cool_lower : ∀ i j,i≠j → (1+1/(n:ℝ))⁻¹*w i j ≤ next i j
  cool_upper : ∀ i j,i≠j → next i j ≤ w i j
  cap : ∀ i j,i≠j → edgeActivity w i j ≤ (4:ℝ)^K
  stages : 1 ≤ T
  epsilon : ℝ
  epsilon_positive : 0 < epsilon
  epsilon_lt_one : epsilon < 1

variable {K T : ℕ}

structure EmpiricalData (c : StageData n K T) where
  abar : ℝ
  dbar : ℝ
  zbar : LogicalEdge (Fin n) → ℝ
  errorA : |abar-meanA c.w K| ≤ RealStage.sigma (sourceD (V:=Fin n) K) T c.epsilon
  errorD : |dbar-meanD c.w c.next K| ≤ RealStage.sigma (sourceD (V:=Fin n) K) T c.epsilon
  errorProbe : ∀ e,|zbar e-meanProbe c.w c.next K e| ≤ RealStage.sigma (sourceD (V:=Fin n) K) T c.epsilon

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_FinitePMF
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Concentration

open MeasureTheory ProbabilityTheory Finset

variable {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I]

variable {μ : Measure Ω} [IsProbabilityMeasure μ]



open MeasureTheory ProbabilityTheory Finset
open scoped Classical

variable {Ω I J : Type*} [Fintype Ω] [Fintype I] [Fintype J]

noncomputable def finitePMF (p : Ω → ℝ) (hp : ∀ x,0 ≤ p x) (hs : ∑ x,p x=1) : PMF Ω :=
  PMF.ofFintype (fun x => ENNReal.ofReal (p x)) (by
    rw [←ENNReal.ofReal_sum_of_nonneg (fun x _ => hp x),hs]
    simp)

end MatchingFPRAS.Concentration

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset
open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance instDecidableEqSourceLabel_8 (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance instFintypeBagEdgeSourceVertexSourceLabelSourceBags_9 (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

omit [Fintype V] [Nontrivial V] in
lemma logicalActivity_le_off (w w₁ : V → V → ℝ)
    (h : ∀ i j,i≠j → w₁ i j ≤ w i j) (e : LogicalEdge V) :
    logicalActivity w₁ e ≤ logicalActivity w e := by
  unfold logicalActivity edgeActivity
  split_ifs
  · exact h _ _ e.property.ne
  · exact h _ _ e.property.ne.symm

lemma bagReweight_range_off (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hw₁ : ∀ x y,0 ≤ w₁ x y) (hle : ∀ x y,x≠y → w₁ x y ≤ w x y)
    (K : ℕ) (e : BagEdge (sourceBags w K)) :
    0 ≤ bagReweight w w₁ K e ∧ bagReweight w w₁ K e ≤ 1 := by
  unfold bagReweight
  split_ifs with he
  · unfold rawReweight
    split_ifs
    · have h₀ : 0 < logicalActivity w he.choose.1 := by
        unfold logicalActivity edgeActivity; split_ifs <;> exact hw _ _
      have h₁ : 0 ≤ logicalActivity w₁ he.choose.1 := by
        unfold logicalActivity edgeActivity; split_ifs <;> exact hw₁ _ _
      exact ⟨div_nonneg h₁ h₀.le,(div_le_one h₀).mpr (logicalActivity_le_off w w₁ hle _)⟩
    · norm_num
  · norm_num

lemma observableD_range_off (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hw₁ : ∀ x y,0 ≤ w₁ x y) (hle : ∀ x y,x≠y → w₁ x y ≤ w x y)
    (K : ℕ) (a : SourceMarked w K) :
    0 ≤ observableD w w₁ K a ∧ observableD w w₁ K a ≤ 1 := by
  unfold observableD
  split_ifs
  · exact ⟨Finset.prod_nonneg (fun e _ => (bagReweight_range_off w w₁ hw hw₁ hle K e).1),
      Finset.prod_le_one (fun e _ => (bagReweight_range_off w w₁ hw hw₁ hle K e).1)
        (fun e _ => (bagReweight_range_off w w₁ hw hw₁ hle K e).2)⟩
  · norm_num

abbrev ObservableIndex (V : Type*) [LinearOrder V] := Fin 2 ⊕ LogicalEdge V

noncomputable def sourceObservable (w w₁ : V → V → ℝ) (K : ℕ) :
    ObservableIndex V → SourceMarked w K → ℝ
  | Sum.inl i => if i=0 then observableA w K else observableD w w₁ K
  | Sum.inr e => observableProbe w w₁ K e

noncomputable def sampleAverage {Ω : Type*} {S : ℕ} (f : Ω → ℝ) (x : Fin S → Ω) : ℝ :=
  (∑ i,f (x i))/(S:ℝ)

noncomputable def sourceMean (w w₁ : V → V → ℝ) (K : ℕ) (j : ObservableIndex V) : ℝ :=
  ∑ x : SourceMarked w K,sourceLaw w K (sourceD (V:=V) K) x*sourceObservable w w₁ K j x

def StageGood {S : ℕ} (w w₁ : V → V → ℝ) (K : ℕ) (σ : ℝ) (x : Fin S → SourceMarked w K) : Prop :=
  ∀ j : ObservableIndex V, |sampleAverage (sourceObservable w w₁ K j) x-sourceMean w w₁ K j| ≤ σ

variable {n K T S : ℕ} [Nontrivial (Fin n)]

noncomputable def empiricalData (c : StageData n K T) (x : Fin S → SourceMarked c.w K)
    (h : StageGood c.w c.next K (RealStage.sigma (sourceD (V:=Fin n) K) T c.epsilon) x) : EmpiricalData c where
  abar := sampleAverage (observableA c.w K) x
  dbar := sampleAverage (observableD c.w c.next K) x
  zbar e := sampleAverage (observableProbe c.w c.next K e) x
  errorA := by simpa only [sourceObservable,ite_true,sourceMean,meanA] using h (Sum.inl 0)
  errorD := by simpa only [sourceObservable,show (1:Fin 2)≠0 by decide,ite_false,sourceMean,meanD] using h (Sum.inl 1)
  errorProbe e := by simpa only [sourceObservable,sourceMean,meanProbe] using h (Sum.inr e)

noncomputable def stageSampleCount (n D T : ℕ) (ε : ℝ) : ℕ :=
  ⌈10*((RealStage.sigma D T ε)⁻¹)^2*((n:ℝ)+T+1)⌉₊



open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset
open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance instDecidableEqSourceLabel_9 (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance instFintypeBagEdgeSourceVertexSourceLabelSourceBags_10 (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Endpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.GraphBridge

open Finset MatchingFPRAS.Enlargement MatchingFPRAS.Subdivision MatchingFPRAS.Representation MatchingFPRAS.Switching

variable {n : ℕ}

def endpoints : LogicalEdge (Fin n) ↪ (Fin n × Fin n) := ⟨Subtype.val,Subtype.val_injective⟩

def selectedEdges (s : LogicalEdge (Fin n) → Bool) : Finset (Fin n × Fin n) :=
  (univ.filter fun e => s e=true).map endpoints

lemma mem_selected (s : LogicalEdge (Fin n) → Bool) (e : LogicalEdge (Fin n)) :
    e.val ∈ selectedEdges s ↔ s e=true := by simp [selectedEdges,endpoints]

def edgeSelection (M : Finset (Fin n × Fin n)) (e : LogicalEdge (Fin n)) : Bool := decide (e.val∈M)

@[simp] lemma edgeSelection_selected (s : LogicalEdge (Fin n) → Bool) :
    edgeSelection (selectedEdges s)=s := by
  funext e
  apply Bool.eq_iff_iff.mpr
  simp [edgeSelection,mem_selected]

end MatchingFPRAS.GraphBridge

namespace MatchingFPRAS.Counting



def productEstimate {K : ℕ} (initial : ℝ) (estimates : Fin K → ℝ) : ℝ :=
  initial * ∏ j, estimates j



end MatchingFPRAS.Counting

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_AdaptiveLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Adaptive

open Finset

variable {Ω : Type*} [Fintype Ω]

structure Law (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ x,0 ≤ mass x
  total : ∑ x,mass x=1

instance instCoeFunLawForallReal : CoeFun (Law Ω) (fun _ => Ω → ℝ) := ⟨Law.mass⟩

noncomputable def Law.event (μ : Law Ω) (P : Ω → Prop) : ℝ := by
  classical
  exact ∑ x,if P x then μ x else 0



open Finset
open scoped Classical

variable {Ω : Type*} [Fintype Ω] {Ψ : Ω → Type*} [∀ x,Fintype (Ψ x)]

noncomputable def Law.sigma (μ : Law Ω) (ν : ∀ x,Law (Ψ x)) : Law (Sigma Ψ) where
  mass z := μ z.1*ν z.1 z.2
  nonneg z := mul_nonneg (μ.nonneg z.1) ((ν z.1).nonneg z.2)
  total := by
    rw [Fintype.sum_sigma]
    change (∑ x,∑ y,μ x*(ν x) y)=1
    simp_rw [←mul_sum,Law.total,mul_one]
    exact μ.total



open Finset
open MatchingFPRAS.Enlargement MatchingFPRAS.Transport
open scoped Classical

variable {Ω : Type*} [Fintype Ω]

noncomputable def Law.iid (μ : Law Ω) (S : ℕ) : Law (Fin S → Ω) where
  mass := Variation.iid μ.mass S
  nonneg := Variation.iid_nonneg μ.mass μ.nonneg S
  total := Variation.iid_sum μ.mass μ.total S

end MatchingFPRAS.Adaptive

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Counting
open Finset

variable {n : ℕ}
lemma ratioEstimate_cast (a d : ℚ) :
    (ratioEstimate a d:ℝ)=RealStage.ratioEstimate a d := by
  simp only [ratioEstimate,RealStage.ratioEstimate]
  have hp : (0:ℝ)<a ↔ (0:ℚ)<a := by exact_mod_cast Iff.rfl
  simp only [hp]
  split_ifs <;> push_cast <;> rfl
end MatchingFPRAS.Counting

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_SortedList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Amplification
open Finset

variable {k : ℕ}

def sortedList (x : Fin (2*k+1) → ℚ) : List ℚ :=
  (List.ofFn x).mergeSort (· ≤ ·)

lemma sortedList_length (x : Fin (2*k+1) → ℚ) : (sortedList x).length=2*k+1 := by
  simp [sortedList]

def sortedValue (x : Fin (2*k+1) → ℚ) (i : Fin (2*k+1)) : ℚ :=
  (sortedList x)[i.val]'(by rw [sortedList_length]; exact i.isLt)

def median (x : Fin (2*k+1) → ℚ) : ℚ := sortedValue x ⟨k,by omega⟩

open Finset MatchingFPRAS.Adaptive MatchingFPRAS.Transport
open scoped Classical

variable {Ω : Type*} [Fintype Ω]

open Finset MatchingFPRAS.Adaptive
open scoped Classical

def halfRepetitions (δ : ℚ) : ℕ := 5*(Nat.clog 2 ⌈δ⁻¹⌉₊+1)
end MatchingFPRAS.Amplification

namespace MatchingFPRAS.Counting
instance scheduleDecidable (n : ℕ) (epsilon : ℚ) (k : ℕ) : Decidable (scheduleAdmissible n epsilon k) :=
  inferInstanceAs (Decidable (1≤k ∧ (n:ℚ)^(n/2)/(1+1/(n:ℚ))^k≤epsilon/32))
lemma schedule_exists (n : ℕ) (hn : 2≤n) (e : ℚ) (he : 0<e) (he1 : e<1) :
    ∃ k,scheduleAdmissible n e k := by
  obtain ⟨k,hk,_⟩:=counting_schedule_exists n hn e he he1
  exact ⟨k,hk⟩
def leastSchedule (n : ℕ) (hn : 2≤n) (e : ℚ) (he : 0<e) (he1 : e<1) : ℕ :=
  Nat.find (schedule_exists n hn e he he1)
lemma leastSchedule_spec (n : ℕ) (hn : 2≤n) (e : ℚ) (he : 0<e) (he1 : e<1) :
    scheduleAdmissible n e (leastSchedule n hn e he he1) := Nat.find_spec _
end MatchingFPRAS.Counting

namespace MatchingFPRAS.BitArithmetic
open Finset

def FractionBound (B : ℕ) (x : ℝ) : Prop :=
  ∃ a b : ℕ,0<b ∧ a≤B ∧ b≤B ∧ x=(a:ℝ)/b
end MatchingFPRAS.BitArithmetic

namespace MatchingFPRAS.BitArithmetic
open Finset

def GridFraction (Q : ℕ) (x : ℝ) : Prop := ∃ a : ℕ,a≤Q ∧ x=(a:ℝ)/Q
end MatchingFPRAS.BitArithmetic

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_EmpiricalDenom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.BitArithmetic
open Finset

def matrixBound (D B : ℕ) : ℕ := 200000*(D+1)*B^2
end MatchingFPRAS.BitArithmetic

namespace MatchingFPRAS.Counting

def schedulePolynomial (n : ℕ) (e : ℚ) : ℕ := n*(n*n+32*⌈e⁻¹⌉₊)
end MatchingFPRAS.Counting

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OutputLengthBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.BitComplexity

def PolynomiallyBounded (f : ℕ → ℕ) : Prop := ∃ C d : ℕ, ∀ x,1≤x → f x≤C*x^d
def boundK (x : ℕ) : ℕ := (2*x)*((2*x)*(2*x)+32*x)
def boundN (x : ℕ) : ℕ := 2*x+(2*x)^2*(4*(2*boundK x+2))
def boundD (x : ℕ) : ℕ := 100*(boundN x)^2*(100000000*(2*x+1)^4)
def boundS (x : ℕ) : ℕ := 10*(10000000*boundD x+1000*boundK x*x)^2*(2*x+boundK x+1)
open Transport

end MatchingFPRAS.BitComplexity

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_Guard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Enlargement
open Finset Switching Subdivision RealGeometry MatchingFPRAS.Representation

open Transport
open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
noncomputable local instance instDecidableEqSourceLabel_11 (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _
noncomputable local instance instFintypeBagEdgeSourceVertexSourceLabelSourceBags_12 (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_GuardMachineBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.MachineCost
open Turing

def advance {α : Type*} (f : α → Option α) (x : α) : α := (f x).getD x
def run {α : Type*} (f : α → Option α) : ℕ → α → α
  | 0,x => x
  | n+1,x => run f n (advance f x)

lemma run_add {α : Type*} (f : α → Option α) (n m : ℕ) (x : α) :
    run f (n+m) x=run f m (run f n x) := by
  induction n generalizing x with
  | zero => simp only [Nat.zero_add,run]
  | succ n ih => simpa only [Nat.succ_add,run] using ih (advance f x)

end MatchingFPRAS.MachineCost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_BinaryAddition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackAddition
open Turing MachineCost

abbrev Stacks := Fin 3 → List Bool
abbrev Store := Option Bool × Option Bool
def value : List Bool → ℕ
  | [] => 0
  | b::bs => b.toNat+2*value bs
def digit (c a b : Bool) : Bool := xor (xor c a) b
def carry (c a b : Bool) : Bool := (c && a) || (c && b) || (a && b)
lemma digit_identity (c a b : Bool) :
    (digit c a b).toNat+2*(carry c a b).toNat=c.toNat+a.toNat+b.toNat := by
  cases c <;> cases a <;> cases b <;> rfl

def addDigits (c : Bool) (A B : List Bool) : List Bool :=
  match A,B with
  | [],[] => if c then [true] else []
  | a::A,[] => digit c a false::addDigits (carry c a false) A []
  | [],b::B => digit c false b::addDigits (carry c false b) [] B
  | a::A,b::B => digit c a b::addDigits (carry c a b) A B
termination_by A.length+B.length

lemma addDigits_value (A B : List Bool) (c : Bool) :
    value (addDigits c A B)=value A+value B+c.toNat := by
  induction A generalizing B c with
  | nil =>
    induction B generalizing c with
    | nil => cases c <;> simp [addDigits,value]
    | cons b B ih =>
      rw [addDigits]
      simp only [value]
      rw [ih]
      have h:=digit_identity c false b
      simp only [Bool.toNat_false,Nat.add_zero] at h
      simp only [value]
      omega
  | cons a A ih =>
    cases B with
    | nil =>
      rw [addDigits]
      simp only [value]
      rw [ih]
      have h:=digit_identity c a false
      simp only [Bool.toNat_false,Nat.add_zero] at h
      simp only [value]
      omega
    | cons b B =>
      rw [addDigits]
      simp only [value]
      rw [ih]
      have h:=digit_identity c a b
      omega
lemma addDigits_length (A B : List Bool) (c : Bool) :
    (addDigits c A B).length ≤ max A.length B.length+1 := by
  induction A generalizing B c with
  | nil =>
    induction B generalizing c with
    | nil => cases c <;> simp [addDigits]
    | cons b B ih =>
      rw [addDigits,List.length_cons]
      have h:=ih (carry c false b)
      simp only [List.length_nil,Nat.zero_max,List.length_cons] at h ⊢
      omega
  | cons a A ih =>
    cases B with
    | nil =>
      rw [addDigits,List.length_cons]
      have h:=ih [] (carry c a false)
      simp only [List.length_nil,Nat.max_zero,List.length_cons] at h ⊢
      omega
    | cons b B =>
      rw [addDigits,List.length_cons]
      have h:=ih B (carry c a b)
      simp only [List.length_cons]
      omega

def program (c : Bool) : TM2.Stmt (fun _ : Fin 3=>Bool) Bool Store :=
  .pop 0 (fun v a=>(a,v.2)) (.pop 1 (fun v b=>(v.1,b))
    (.branch (fun v=>v.1.isNone && v.2.isNone)
      (.branch (fun _=>c) (.push 2 (fun _=>true) (.load (fun _=>default) .halt))
        (.load (fun _=>default) .halt))
      (.push 2 (fun v=>digit c (v.1.getD false) (v.2.getD false))
        (.goto (fun v=>carry c (v.1.getD false) (v.2.getD false))))))
def stackData (A B L : List Bool) : Stacks := ![A,B,L]
@[simp] lemma stackData_zero (A B L : List Bool) : stackData A B L 0=A := rfl
@[simp] lemma stackData_one (A B L : List Bool) : stackData A B L 1=B := rfl
@[simp] lemma stackData_two (A B L : List Bool) : stackData A B L 2=L := rfl
def cfg (c : Option Bool) (A B L : List Bool) (v : Store) :
    TM2.Cfg (fun _ : Fin 3=>Bool) Bool Store := ⟨c,v,stackData A B L⟩
lemma update_zero (A B L X : List Bool) :
    Function.update (stackData A B L) 0 X=stackData X B L := by
  funext i
  fin_cases i <;> simp [stackData]
lemma update_one (A B L X : List Bool) :
    Function.update (stackData A B L) 1 X=stackData A X L := by
  funext i
  fin_cases i <;> simp [stackData]
lemma update_two (A B L X : List Bool) :
    Function.update (stackData A B L) 2 X=stackData A B X := by
  funext i
  fin_cases i <;> simp [stackData]
lemma step_empty (c : Bool) (L : List Bool) (v : Store) :
    advance (TM2.step program) (cfg (some c) [] [] L v)=
      cfg none [] [] ((addDigits c [] []).reverse++L) default := by
  cases c <;> simp [advance,TM2.step,program,TM2.stepAux,cfg,
    update_zero,update_one,update_two,addDigits]
lemma step_digits (c : Bool) (A B L : List Bool) (v : Store)
    (h : A≠[] ∨ B≠[]) :
    advance (TM2.step program) (cfg (some c) A B L v)=
      cfg (some (carry c (A.headD false) (B.headD false))) A.tail B.tail
        (digit c (A.headD false) (B.headD false)::L) (A.head?,B.head?) := by
  cases A <;> cases B <;> simp_all [advance,TM2.step,program,TM2.stepAux,cfg,
    update_zero,update_one,update_two]
lemma addDigits_step (c : Bool) (A B : List Bool) (h : A ≠ [] ∨ B ≠ []) :
    addDigits c A B=digit c (A.headD false) (B.headD false)::
      addDigits (carry c (A.headD false) (B.headD false)) A.tail B.tail := by
  cases A <;> cases B <;> simp_all [addDigits]

theorem run_addition (A B L : List Bool) (c : Bool) (v : Store) :
    ∃ t ≤ A.length+B.length+1,
      MachineCost.run (TM2.step program) t (cfg (some c) A B L v)=
        cfg none [] [] ((addDigits c A B).reverse++L) default := by
  have aux : ∀ n (A B : List Bool), A.length+B.length=n →
      ∀ (c : Bool) (L : List Bool) (v : Store),
      ∃ t ≤ A.length+B.length+1,
        MachineCost.run (TM2.step program) t (cfg (some c) A B L v)=
          cfg none [] [] ((addDigits c A B).reverse++L) default := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A B hn c L v
      by_cases he : A=[] ∧ B=[]
      · rcases he with ⟨rfl,rfl⟩
        exact ⟨1,by simp,step_empty c L v⟩
      · have hne : A≠[] ∨ B≠[] := by tauto
        have hlt : A.tail.length+B.tail.length<n := by
          cases A <;> cases B <;> simp_all
          all_goals omega
        obtain ⟨t,ht,hr⟩:=ih _ hlt A.tail B.tail rfl
          (carry c (A.headD false) (B.headD false))
          (digit c (A.headD false) (B.headD false)::L) (A.head?,B.head?)
        refine ⟨t+1,by omega,?_⟩
        rw [MachineCost.run,step_digits c A B L v hne,hr,addDigits_step c A B hne]
        simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
  exact aux _ A B rfl c L v
lemma value_bits (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    simp only [value,ih]
    cases b <;> simp [Nat.bit,Bool.toNat]
    omega

lemma addition_numerals (m n : ℕ) : value (addDigits false m.bits n.bits)=m+n := by
  simp only [addDigits_value,value_bits,Bool.toNat_false,Nat.add_zero]
end MatchingFPRAS.StackAddition

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_BoolPostCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.BoolPostCompiler
open Turing MachineCost
open scoped Classical

def up : PointedMap Bool Symbol := ⟨fun b=>if b then 1 else 0,rfl⟩
def down : PointedMap Symbol Bool := ⟨fun a=>decide (a=1),rfl⟩
end MatchingFPRAS.BoolPostCompiler

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_AlphabetCompilerCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.AlphabetCost
open Turing Turing.TM1 Turing.TM1to1 MachineCost

variable {Γ Λ σ : Type*} [Inhabited Γ]

def writesCount : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q => writesCount q
  | .write _ q => writesCount q+1
  | .load _ q => writesCount q
  | .branch _ q r => max (writesCount q) (writesCount r)
  | .goto _ => 0
  | .halt => 0
end MatchingFPRAS.AlphabetCost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_SupportedCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.AlphabetCost
open Turing MachineCost
open scoped Classical

variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable {n : ℕ} (enc : Γ → List.Vector Bool n) (dec : List.Vector Bool n → Γ)
  (enc0 : enc default = List.Vector.replicate n false)
  (encdec : ∀ a,dec (enc a)=a) (M : Λ → TM1.Stmt Γ Λ σ)
  (S : Finset Λ) (hS : TM1.Supports M S)
include encdec hS
noncomputable def supportedWrites : ℕ := S.sup (fun l=>writesCount (M l))
end MatchingFPRAS.AlphabetCost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_BinaryCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackCompare
open Turing MachineCost StackAddition

def updateOrder (c : Ordering) (a b : Bool) : Ordering :=
  if a=b then c else if a then .gt else .lt

def compareDigits (c : Ordering) (A B : List Bool) : Ordering :=
  match A,B with
  | [],[] => c
  | a::A,[] => compareDigits (updateOrder c a false) A []
  | [],b::B => compareDigits (updateOrder c false b) [] B
  | a::A,b::B => compareDigits (updateOrder c a b) A B
termination_by A.length+B.length

def result (c : Ordering) (m n : ℕ) : Ordering := if m=n then c else compare m n
lemma result_digits (c : Ordering) (a b : Bool) (m n : ℕ) :
    result (updateOrder c a b) m n=result c (a.toNat+2*m) (b.toNat+2*n) := by
  rcases lt_trichotomy m n with h|h|h
  · have hb : a.toNat+2*m < b.toNat+2*n := by
      cases a <;> cases b <;> simp only [Bool.toNat_true,Bool.toNat_false] <;> omega
    simp [result,ne_of_lt h,ne_of_lt hb,compare_lt_iff_lt.mpr h,compare_lt_iff_lt.mpr hb]
  · subst n
    cases a <;> cases b <;> cases c <;>
      simp [result,updateOrder,eq_comm]
    all_goals first
    | exact (compare_lt_iff_lt.mpr (by omega)).symm
    | exact (compare_gt_iff_gt.mpr (by omega)).symm
  · have hb : b.toNat+2*n < a.toNat+2*m := by
      cases a <;> cases b <;> simp only [Bool.toNat_true,Bool.toNat_false] <;> omega
    simp [result,ne_of_gt h,ne_of_gt hb,compare_gt_iff_gt.mpr h,compare_gt_iff_gt.mpr hb]
lemma compareDigits_result (A B : List Bool) (c : Ordering) :
    compareDigits c A B=result c (value A) (value B) := by
  induction A generalizing B c with
  | nil =>
    induction B generalizing c with
    | nil => simp [compareDigits,result,value]
    | cons b B ih =>
      rw [compareDigits,ih]
      simpa only [value,Bool.toNat_false,Nat.zero_add,Nat.mul_zero] using result_digits c false b 0 (value B)
  | cons a A ih =>
    cases B with
    | nil =>
      rw [compareDigits,ih]
      simpa only [value,Bool.toNat_false,Nat.zero_add,Nat.mul_zero,Nat.add_zero] using result_digits c a false (value A) 0
    | cons b B =>
      rw [compareDigits,ih]
      exact result_digits c a b (value A) (value B)
lemma compares_values (A B : List Bool) :
    compareDigits .eq A B=compare (value A) (value B) := by
  rw [compareDigits_result]
  unfold result
  split_ifs with h
  · simp [h]
  · rfl
def flags (c : Ordering) : List Bool := [decide (c=.lt),decide (c=.gt)]
def program (c : Ordering) : TM2.Stmt (fun _ : Fin 3=>Bool) Ordering Store :=
  .pop 0 (fun v a=>(a,v.2)) (.pop 1 (fun v b=>(v.1,b))
    (.branch (fun v=>v.1.isNone && v.2.isNone)
      (.push 2 (fun _=>decide (c=.gt)) (.push 2 (fun _=>decide (c=.lt))
         (.load (fun _=>default) .halt)))
      (.goto (fun v=>updateOrder c (v.1.getD false) (v.2.getD false)))))
def cfg (c : Option Ordering) (A B L : List Bool) (v : Store) :
    TM2.Cfg (fun _ : Fin 3=>Bool) Ordering Store := ⟨c,v,stackData A B L⟩
lemma step_empty (c : Ordering) (L : List Bool) (v : Store) :
    advance (TM2.step program) (cfg (some c) [] [] L v)=
      cfg none [] [] (flags c++L) default := by
  cases c <;> simp [advance,TM2.step,program,TM2.stepAux,cfg,flags,
    update_zero,update_one,update_two]
lemma step_digits (c : Ordering) (A B L : List Bool) (v : Store)
    (h : A≠[] ∨ B≠[]) :
    advance (TM2.step program) (cfg (some c) A B L v)=
      cfg (some (updateOrder c (A.headD false) (B.headD false))) A.tail B.tail L (A.head?,B.head?) := by
  cases A <;> cases B <;> simp_all [advance,TM2.step,program,TM2.stepAux,cfg,
    update_zero,update_one,update_two,List.headD]
lemma compareDigits_step (c : Ordering) (A B : List Bool) (h : A ≠ [] ∨ B ≠ []) :
    compareDigits c A B=
      compareDigits (updateOrder c (A.headD false) (B.headD false)) A.tail B.tail := by
  cases A <;> cases B <;> simp_all [compareDigits,List.headD]
theorem run_comparison (A B L : List Bool) (c : Ordering) (v : Store) :
    ∃ t ≤ A.length+B.length+1,
      MachineCost.run (TM2.step program) t (cfg (some c) A B L v)=
        cfg none [] [] (flags (compareDigits c A B)++L) default := by
  have aux : ∀ n (A B : List Bool), A.length+B.length=n →
      ∀ (c : Ordering) (L : List Bool) (v : Store),
      ∃ t ≤ A.length+B.length+1,
        MachineCost.run (TM2.step program) t (cfg (some c) A B L v)=
          cfg none [] [] (flags (compareDigits c A B)++L) default := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A B hn c L v
      by_cases he : A=[] ∧ B=[]
      · rcases he with ⟨rfl,rfl⟩
        refine ⟨1,by simp,?_⟩
        simpa only [MachineCost.run,compareDigits] using step_empty c L v
      · have hne : A≠[] ∨ B≠[] := by tauto
        have hlt : A.tail.length+B.tail.length<n := by
          cases A <;> cases B <;> simp_all
          all_goals omega
        obtain ⟨t,ht,hr⟩:=ih _ hlt A.tail B.tail rfl
          (updateOrder c (A.headD false) (B.headD false)) L (A.head?,B.head?)
        refine ⟨t+1,by omega,?_⟩
        rw [MachineCost.run,step_digits c A B L v hne,hr,compareDigits_step c A B hne]
  exact aux _ A B rfl c L v
end MatchingFPRAS.StackCompare

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_ArithmeticSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackComposition
open Turing MachineCost

variable {K Λ P σ : Type*} {Γ : K → Type*} [DecidableEq K]
def relabel (f : Λ → P) (h : Option P) : TM2.Stmt Γ Λ σ → TM2.Stmt Γ P σ
  | .push k a q => .push k a (relabel f h q)
  | .peek k a q => .peek k a (relabel f h q)
  | .pop k a q => .pop k a (relabel f h q)
  | .load a q => .load a (relabel f h q)
  | .branch p q r => .branch p (relabel f h q) (relabel f h r)
  | .goto l => .goto (fun a=>f (l a))
  | .halt => match h with | none=>.halt | some k=>.goto (fun _=>k)
def mapCfg (f : Λ → P) (h : Option P) (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ P σ :=
  ⟨c.l.bind (fun l=>some (f l)) |>.or h,c.var,c.stk⟩
omit [DecidableEq K] in
lemma mapCfg_some (f : Λ → P) (h : Option P) (l : Λ) (v : σ) (S : ∀ k,List (Γ k)) :
    mapCfg f h ⟨some l,v,S⟩=⟨some (f l),v,S⟩ := rfl
lemma relabel_eval (f : Λ → P) (h : Option P) (q : TM2.Stmt Γ Λ σ)
    (v : σ) (S : ∀ k,List (Γ k)) :
    TM2.stepAux (relabel f h q) v S=mapCfg f h (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k a q ih => exact ih v _
  | peek k a q ih => exact ih _ S
  | pop k a q ih => exact ih _ _
  | load a q ih => exact ih (a v) S
  | branch p q r ihq ihr =>
    cases hp:p v <;> simp only [relabel,TM2.stepAux,hp,Bool.cond_false,Bool.cond_true] <;>
      first | apply ihr | apply ihq
  | goto l => rfl
  | halt => cases h <;> rfl
lemma run_halted (M : Λ → TM2.Stmt Γ Λ σ) (n : ℕ)
    (v : σ) (S : ∀ k,List (Γ k)) :
    MachineCost.run (TM2.step M) n ⟨none,v,S⟩=⟨none,v,S⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [MachineCost.run,advance,TM2.step,Option.getD_none] using ih
lemma run_relabel_to_halt (M : Λ → TM2.Stmt Γ Λ σ) (N : P → TM2.Stmt Γ P σ)
    (f : Λ → P) (h : Option P) (hN : ∀ l,N (f l)=relabel f h (M l))
    (n : ℕ) (c : TM2.Cfg Γ Λ σ) (v : σ) (S : ∀ k,List (Γ k))
    (he : MachineCost.run (TM2.step M) n c=⟨none,v,S⟩) :
    ∃ k≤n,MachineCost.run (TM2.step N) k (mapCfg f h c)=⟨h,v,S⟩ := by
  induction n generalizing c with
  | zero =>
    have hc : c=⟨none,v,S⟩:=he
    subst c
    exact ⟨0,le_rfl,rfl⟩
  | succ n ih =>
    rcases c with ⟨l,v',S'⟩
    cases l with
    | none =>
      rw [run_halted] at he
      cases he
      exact ⟨0,Nat.zero_le _,rfl⟩
    | some l =>
      have he' : MachineCost.run (TM2.step M) n (TM2.stepAux (M l) v' S')=⟨none,v,S⟩ := he
      obtain ⟨k,hk,hh⟩:=ih _ he'
      refine ⟨k+1,by omega,?_⟩
      rw [MachineCost.run,mapCfg_some]
      have hs : advance (TM2.step N) ⟨some (f l),v',S'⟩=
          mapCfg f h (TM2.stepAux (M l) v' S') := by
        simp only [advance,TM2.step,Option.getD_some,hN,relabel_eval]
      rw [hs,hh]
variable [Inhabited Λ] [Inhabited P]
def sequence (M : Λ → TM2.Stmt Γ Λ σ) (N : P → TM2.Stmt Γ P σ) :
    Λ⊕P → TM2.Stmt Γ (Λ⊕P) σ
  | .inl l => relabel Sum.inl (some (Sum.inr default)) (M l)
  | .inr k => relabel Sum.inr none (N k)
omit [Inhabited Λ] in
lemma sequence_run (M : Λ → TM2.Stmt Γ Λ σ) (N : P → TM2.Stmt Γ P σ)
    (c : TM2.Cfg Γ Λ σ) (m n : ℕ) (v v' : σ) (S S' : ∀ k,List (Γ k))
    (hM : MachineCost.run (TM2.step M) m c=⟨none,v,S⟩)
    (hN : MachineCost.run (TM2.step N) n ⟨some default,v,S⟩=⟨none,v',S'⟩) :
    ∃ k ≤ m+n,MachineCost.run (TM2.step (sequence M N)) k
      (mapCfg Sum.inl (some (Sum.inr default)) c)=⟨none,v',S'⟩ := by
  obtain ⟨i,hi,hei⟩:=run_relabel_to_halt M (sequence M N) Sum.inl
    (some (Sum.inr default)) (fun _=>rfl) m c v S hM
  obtain ⟨j,hj,hej⟩:=run_relabel_to_halt N (sequence M N) Sum.inr
    none (fun _=>rfl) n ⟨some default,v,S⟩ v' S' hN
  refine ⟨i+j,by omega,?_⟩
  rw [run_add,hei]
  exact hej

open Turing MachineCost

end MatchingFPRAS.StackComposition

namespace MatchingFPRAS.StackReverse
open Turing MachineCost StackAddition

abbrev S := Option Bool
abbrev Γ := fun _ : Fin 3 => Bool
def program : Unit → TM2.Stmt Γ Unit S := fun _ =>
  .pop 0 (fun _ a=>a)
    (.branch Option.isNone (.load (fun _=>none) .halt)
      (.push 1 (fun v=>v.getD false) (.goto (fun _=>()))))
def cfg (l : Option Unit) (A B C : List Bool) (v : S) : TM2.Cfg Γ Unit S :=
  ⟨l,v,stackData A B C⟩
lemma next_empty (B C : List Bool) (v : S) :
    advance (TM2.step program) (cfg (some ()) [] B C v)=cfg none [] B C none := by
  simp [advance,TM2.step,program,TM2.stepAux,cfg,update_zero]
lemma next_cons (a : Bool) (A B C : List Bool) (v : S) :
    advance (TM2.step program) (cfg (some ()) (a::A) B C v)=
      cfg (some ()) A (a::B) C (some a) := by
  simp [advance,TM2.step,program,TM2.stepAux,cfg,update_zero,update_one]
theorem run_reverse (A B C : List Bool) (v : S) :
    MachineCost.run (TM2.step program) (A.length+1) (cfg (some ()) A B C v)=
      cfg none [] (A.reverse++B) C none := by
  induction A generalizing B v with
  | nil => simpa only [List.length_nil,List.reverse_nil,List.nil_append,MachineCost.run] using next_empty B C v
  | cons a A ih =>
    rw [List.length_cons,show A.length+1+1=(A.length+1)+1 by rfl,MachineCost.run,next_cons,ih]
    simp [List.reverse_cons,List.append_assoc]
end MatchingFPRAS.StackReverse

namespace MatchingFPRAS.ForwardAddition
open Turing MachineCost StackAddition

local instance initialControl : Inhabited (Bool⊕Unit) := ⟨.inl false⟩
abbrev Γ := fun _ : Fin 3 => Bool
def reverseProgram : Unit → TM2.Stmt Γ Unit Store := fun _ =>
  .pop 2 (fun v a=>(a,v.2))
    (.branch (fun v=>v.1.isNone) (.load (fun _=>default) .halt)
      (.push 0 (fun v=>v.1.getD false) (.goto (fun _=>()))))
def rcfg (l : Option Unit) (A B C : List Bool) (v : Store) : TM2.Cfg Γ Unit Store :=
  ⟨l,v,stackData A B C⟩
lemma next_empty (A B : List Bool) (v : Store) :
    advance (TM2.step reverseProgram) (rcfg (some ()) A B [] v)=rcfg none A B [] default := by
  simp [advance,TM2.step,reverseProgram,TM2.stepAux,rcfg,update_two]
lemma next_cons (a : Bool) (A B C : List Bool) (v : Store) :
    advance (TM2.step reverseProgram) (rcfg (some ()) A B (a::C) v)=
      rcfg (some ()) (a::A) B C (some a,v.2) := by
  simp [advance,TM2.step,reverseProgram,TM2.stepAux,rcfg,update_zero,update_two]
lemma run_reverse (A B C : List Bool) (v : Store) :
    MachineCost.run (TM2.step reverseProgram) (C.length+1) (rcfg (some ()) A B C v)=
      rcfg none (C.reverse++A) B [] default := by
  induction C generalizing A v with
  | nil => simpa only [List.length_nil,List.reverse_nil,List.nil_append,MachineCost.run] using next_empty A B v
  | cons c C ih =>
    rw [List.length_cons,MachineCost.run,next_cons,ih]
    simp [List.reverse_cons,List.append_assoc]
def program : Bool⊕Unit → TM2.Stmt Γ (Bool⊕Unit) Store :=
  StackComposition.sequence StackAddition.program reverseProgram
lemma run_add (A B : List Bool) :
    ∃ k≤2*(A.length+B.length)+3,
      MachineCost.run (TM2.step program) k ⟨some default,default,stackData A B []⟩=
        ⟨none,default,stackData (addDigits false A B) [] []⟩ := by
  obtain ⟨n,hn,he⟩:=run_addition A B [] false default
  have he' : MachineCost.run (TM2.step StackAddition.program) n
      (cfg (some false) A B [] default)=cfg none [] [] (addDigits false A B).reverse default := by
    simpa only [List.append_nil] using he
  have hr := run_reverse [] [] (addDigits false A B).reverse default
  have hr' : MachineCost.run (TM2.step reverseProgram) ((addDigits false A B).length+1)
      ⟨some default,default,stackData [] [] (addDigits false A B).reverse⟩=
      ⟨none,default,stackData (addDigits false A B) [] []⟩ := by
    simpa only [rcfg,List.length_reverse,List.reverse_reverse,List.append_nil] using hr
  obtain ⟨k,hk,hkrun⟩:=StackComposition.sequence_run StackAddition.program reverseProgram
    (cfg (some false) A B [] default) n ((addDigits false A B).length+1)
    (default : Store) (default : Store) (stackData [] [] (addDigits false A B).reverse)
      (stackData (addDigits false A B) [] []) he' hr'
  refine ⟨k,?_,?_⟩
  · have hl:=addDigits_length A B false
    omega
  · exact hkrun
end MatchingFPRAS.ForwardAddition

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_StackEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackEmbedding
open Turing MachineCost

variable {K J α Λ σ τ : Type*} [DecidableEq K] [DecidableEq J]
open scoped Classical

noncomputable def extend (e : K ↪ J) (S : K → List α) (R : J → List α) (j : J) : List α :=
  if h : ∃ k,e k=j then S (Classical.choose h) else R j
omit [DecidableEq K] [DecidableEq J] in
@[simp] lemma extend_on (e : K ↪ J) (S : K → List α) (R : J → List α) (k : K) :
    extend e S R (e k)=S k := by
  have h : ∃ l,e l=e k := ⟨k,rfl⟩
  rw [extend,dite_eq_left h,e.injective (Classical.choose_spec h)]
omit [DecidableEq K] [DecidableEq J] in
lemma extend_off (e : K ↪ J) (S : K → List α) (R : J → List α) (j : J)
    (h : ¬∃ k,e k=j) : extend e S R j=R j := by rw [extend,dite_eq_right h]
lemma extend_update (e : K ↪ J) (S : K → List α) (R : J → List α) (k : K) (w : List α) :
    Function.update (extend e S R) (e k) w=extend e (Function.update S k w) R := by
  funext j
  by_cases h : ∃ l,e l=j
  · obtain ⟨l,rfl⟩:=h
    by_cases hl : l=k
    · subst l; simp
    · have hne : e l≠e k := fun h=>hl (e.injective h)
      simp [Function.update_of_ne hne,Function.update_of_ne hl]
  · have hne : j≠e k := fun h'=>h ⟨k,h'.symm⟩
    rw [Function.update_of_ne hne,extend_off e _ _ j h,extend_off e _ _ j h]

end MatchingFPRAS.StackEmbedding

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_StackLens
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackLens
open Turing MachineCost StackEmbedding

structure Lens (σ τ : Type*) where
  get : τ → σ
  put : τ → σ → τ
  get_put : ∀ v s,get (put v s)=s
  put_get : ∀ v,put v (get v)=v
  put_put : ∀ v s t,put (put v s) t=put v t

def Lens.identity (σ : Type*) : Lens σ σ :=
  ⟨id,fun _ s=>s,fun _ _=>rfl,fun _=>rfl,fun _ _ _=>rfl⟩
variable {K J α Λ σ τ : Type*} [DecidableEq K] [DecidableEq J]

def stmt (e : K ↪ J) (L : Lens σ τ) :
    TM2.Stmt (fun _ : K=>α) Λ σ → TM2.Stmt (fun _ : J=>α) Λ τ
  | .push k a q => .push (e k) (fun v=>a (L.get v)) (stmt e L q)
  | .peek k a q => .peek (e k) (fun v x=>L.put v (a (L.get v) x)) (stmt e L q)
  | .pop k a q => .pop (e k) (fun v x=>L.put v (a (L.get v) x)) (stmt e L q)
  | .load a q => .load (fun v=>L.put v (a (L.get v))) (stmt e L q)
  | .branch p q r => .branch (fun v=>p (L.get v)) (stmt e L q) (stmt e L r)
  | .goto l => .goto (fun v=>l (L.get v))
  | .halt => .halt
noncomputable def cfg (e : K ↪ J) (L : Lens σ τ) (R : J → List α) (u : τ)
    (c : TM2.Cfg (fun _ : K=>α) Λ σ) : TM2.Cfg (fun _ : J=>α) Λ τ :=
  ⟨c.l,L.put u c.var,extend e c.stk R⟩
lemma stmt_eval (e : K ↪ J) (L : Lens σ τ) (R : J → List α) (u : τ)
    (q : TM2.Stmt (fun _ : K=>α) Λ σ) (v : σ) (S : K → List α) :
    TM2.stepAux (stmt e L q) (L.put u v) (extend e S R)=
      cfg e L R u (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k a q ih =>
    simpa only [stmt,TM2.stepAux,L.get_put,extend_on,extend_update] using ih v (Function.update S k (a v::S k))
  | peek k a q ih =>
    simpa only [stmt,TM2.stepAux,L.get_put,L.put_put,extend_on] using ih (a v (S k).head?) S
  | pop k a q ih =>
    simpa only [stmt,TM2.stepAux,L.get_put,L.put_put,extend_on,extend_update] using ih (a v (S k).head?) (Function.update S k (S k).tail)
  | load a q ih => simpa only [stmt,TM2.stepAux,L.get_put,L.put_put] using ih (a v) S
  | branch p q r ihq ihr =>
    cases h : p v <;> simp only [stmt,TM2.stepAux,L.get_put,h,Bool.cond_false,Bool.cond_true] <;>
      first | apply ihr | apply ihq
  | goto l => simp only [stmt,TM2.stepAux,cfg,L.get_put]
  | halt => rfl
def program (e : K ↪ J) (L : Lens σ τ) (M : Λ → TM2.Stmt (fun _ : K=>α) Λ σ) :=
  fun l=>stmt e L (M l)
lemma advance_cfg (e : K ↪ J) (L : Lens σ τ) (M : Λ → TM2.Stmt (fun _ : K=>α) Λ σ)
    (R : J → List α) (u : τ) (c : TM2.Cfg (fun _ : K=>α) Λ σ) :
    advance (TM2.step (program e L M)) (cfg e L R u c)=cfg e L R u (advance (TM2.step M) c) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => rfl
  | some l => exact stmt_eval e L R u (M l) v S

theorem run_cfg (e : K ↪ J) (L : Lens σ τ) (M : Λ → TM2.Stmt (fun _ : K=>α) Λ σ)
    (R : J → List α) (u : τ) (n : ℕ) (c : TM2.Cfg (fun _ : K=>α) Λ σ) :
    MachineCost.run (TM2.step (program e L M)) n (cfg e L R u c)=
      cfg e L R u (MachineCost.run (TM2.step M) n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => rw [MachineCost.run,advance_cfg,ih,MachineCost.run]
end MatchingFPRAS.StackLens

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeData
inductive Data where
  | nil
  | cons (head tail : Data)
  deriving DecidableEq, Inhabited
open Data

def encode : Data → List Bool
  | .nil => [false]
  | .cons a b => true::(encode a++encode b)
end MatchingFPRAS.TreeData

namespace MatchingFPRAS.TreeTransfer
open Turing MachineCost TreeData

abbrev Store := Option Bool
abbrev Stacks := Fin 3 → List Bool
def program : Unit → TM2.Stmt (fun _ : Fin 3=>Bool) Unit Store := fun _=>
  .peek 2 (fun _ b=>b) (.branch Option.isNone (.load (fun _=>none) .halt)
    (.pop 2 (fun v _=>v) (.pop 0 (fun _ b=>b)
      (.push 1 (fun v=>v.getD false) (.branch (fun v=>v.getD false)
        (.push 2 (fun _=>false) (.push 2 (fun _=>false) (.goto (fun _=>()))))
        (.goto (fun _=>())))))))
def stackData (A B D : List Bool) : Stacks := ![A,B,D]
def cfg (l : Option Unit) (A B D : List Bool) (v : Store) :
    TM2.Cfg (fun _ : Fin 3=>Bool) Unit Store := ⟨l,v,stackData A B D⟩
@[simp] lemma stacks_zero (A B D : List Bool) : stackData A B D 0=A := rfl
@[simp] lemma stacks_one (A B D : List Bool) : stackData A B D 1=B := rfl
@[simp] lemma stacks_two (A B D : List Bool) : stackData A B D 2=D := rfl
lemma update_zero (A B D X : List Bool) : Function.update (stackData A B D) 0 X=stackData X B D := by
  funext i; fin_cases i <;> simp [stackData]
lemma update_one (A B D X : List Bool) : Function.update (stackData A B D) 1 X=stackData A X D := by
  funext i; fin_cases i <;> simp [stackData]
lemma update_two (A B D X : List Bool) : Function.update (stackData A B D) 2 X=stackData A B X := by
  funext i; fin_cases i <;> simp [stackData]
lemma step_nil (A B D : List Bool) (v : Store) :
    advance (TM2.step program) (cfg (some ()) (false::A) B (false::D) v)=
      cfg (some ()) A (false::B) D (some false) := by
  simp [advance,TM2.step,program,TM2.stepAux,cfg,update_zero,update_one,update_two]
lemma step_cons (A B D : List Bool) (v : Store) :
    advance (TM2.step program) (cfg (some ()) (true::A) B (false::D) v)=
      cfg (some ()) A (true::B) (false::false::D) (some true) := by
  simp [advance,TM2.step,program,TM2.stepAux,cfg,update_zero,update_one,update_two]
lemma step_stop (A B : List Bool) (v : Store) :
    advance (TM2.step program) (cfg (some ()) A B [] v)=cfg none A B [] none := by
  simp [advance,TM2.step,program,TM2.stepAux,cfg]

theorem run_tree (x : Data) (A B D : List Bool) (v : Store) :
    MachineCost.run (TM2.step program) (encode x).length
      (cfg (some ()) (encode x++A) B (false::D) v)=
      cfg (some ()) A ((encode x).reverse++B) D (some false) := by
  induction x generalizing A B D v with
  | nil => simpa [encode,MachineCost.run] using step_nil A B D v
  | cons x y ihx ihy =>
    simp only [encode,List.length_cons,List.length_append,List.cons_append]
    rw [MachineCost.run,step_cons]
    rw [show (encode x++encode y)++A=encode x++(encode y++A) by simp only [List.append_assoc]]
    rw [run_add,ihx,ihy]
    simp only [List.reverse_cons,List.reverse_append,List.append_assoc,List.singleton_append]

theorem run_transfer (x : Data) (A B : List Bool) (v : Store) :
    MachineCost.run (TM2.step program) ((encode x).length+1)
      (cfg (some ()) (encode x++A) B [false] v)=
      cfg none A ((encode x).reverse++B) [] none := by
  rw [run_add,run_tree]
  exact step_stop A ((encode x).reverse++B) (some false)
end MatchingFPRAS.TreeTransfer

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_WordOps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.WordOps
open Turing MachineCost TreeTransfer

def duplicate : Unit → TM2.Stmt (fun _ : Fin 3=>Bool) Unit Store := fun _=>
  .pop 0 (fun _ b=>b) (.branch Option.isNone (.load (fun _=>none) .halt)
    (.push 1 (fun v=>v.getD false) (.push 2 (fun v=>v.getD false) (.goto (fun _=>())))))
lemma duplicate_nil (B D : List Bool) (v : Store) :
    advance (TM2.step duplicate) (cfg (some ()) [] B D v)=cfg none [] B D none := by
  simp [advance,TM2.step,duplicate,TM2.stepAux,cfg,update_zero]
lemma duplicate_cons (b : Bool) (A B D : List Bool) (v : Store) :
    advance (TM2.step duplicate) (cfg (some ()) (b::A) B D v)=
      cfg (some ()) A (b::B) (b::D) (some b) := by
  simp [advance,TM2.step,duplicate,TM2.stepAux,cfg,update_zero,update_one,update_two]
theorem run_duplicate (A B D : List Bool) (v : Store) :
    MachineCost.run (TM2.step duplicate) (A.length+1) (cfg (some ()) A B D v)=
      cfg none [] (A.reverse++B) (A.reverse++D) none := by
  induction A generalizing B D v with
  | nil => simpa only [List.length_nil,Nat.zero_add,List.reverse_nil,List.nil_append,MachineCost.run] using duplicate_nil B D v
  | cons b A ih =>
    rw [List.length_cons,Nat.add_right_comm,MachineCost.run,duplicate_cons,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

def clear : Unit → TM2.Stmt (fun _ : Fin 3=>Bool) Unit Store := fun _=>
  .pop 0 (fun _ b=>b) (.branch Option.isNone (.load (fun _=>none) .halt) (.goto (fun _=>())))
lemma clear_nil (B D : List Bool) (v : Store) :
    advance (TM2.step clear) (cfg (some ()) [] B D v)=cfg none [] B D none := by
  simp [advance,TM2.step,clear,TM2.stepAux,cfg,update_zero]
lemma clear_cons (b : Bool) (A B D : List Bool) (v : Store) :
    advance (TM2.step clear) (cfg (some ()) (b::A) B D v)=cfg (some ()) A B D (some b) := by
  simp [advance,TM2.step,clear,TM2.stepAux,cfg,update_zero]
theorem run_clear (A B D : List Bool) (v : Store) :
    MachineCost.run (TM2.step clear) (A.length+1) (cfg (some ()) A B D v)=cfg none [] B D none := by
  induction A generalizing v with
  | nil => exact clear_nil B D v
  | cons b A ih => rw [List.length_cons,Nat.add_right_comm,MachineCost.run,clear_cons,ih]
end MatchingFPRAS.WordOps

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_RegisterProc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RegisterProc
open Turing MachineCost

abbrev Store := Option Bool
abbrev Stack (K : Type) := K → List Bool
structure Proc (K : Type) where
  Label : Type
  [labels : Fintype Label]
  [entry : Inhabited Label]
  code : Label → TM2.Stmt (fun _ : K=>Bool) Label Store
attribute [instance] Proc.labels Proc.entry
variable {K : Type} [DecidableEq K]

def Exec (P : Proc K) (S T : Stack K) (bound : ℕ) : Prop :=
  ∃ n≤bound,MachineCost.run (TM2.step P.code) n ⟨some default,none,S⟩=⟨none,none,T⟩
lemma Exec.mono {P : Proc K} {S T : Stack K} {n m : ℕ}
    (h : Exec P S T n) (hn : n ≤ m) : Exec P S T m := by
  obtain ⟨k,hk,he⟩:=h; exact ⟨k,hk.trans hn,he⟩

def seq (P Q : Proc K) : Proc K :=
  { Label := P.Label ⊕ Q.Label
    entry := ⟨Sum.inl default⟩
    code := StackComposition.sequence P.code Q.code }
lemma Exec.seq {P Q : Proc K} {S T U : Stack K} {n m : ℕ}
    (hP : Exec P S T n) (hQ : Exec Q T U m) : Exec (seq P Q) S U (n+m) := by
  obtain ⟨i,hi,he⟩:=hP
  obtain ⟨j,hj,hf⟩:=hQ
  obtain ⟨k,hk,hg⟩:=StackComposition.sequence_run P.code Q.code
    ⟨some default,none,S⟩ i j none none T U he hf
  exact ⟨k,hk.trans (Nat.add_le_add hi hj),hg⟩

def atom (s : TM2.Stmt (fun _ : K=>Bool) Unit Store) : Proc K := ⟨Unit,fun _=>s⟩
lemma exec_atom (s : TM2.Stmt (fun _ : K=>Bool) Unit Store) (S T : Stack K)
    (h : TM2.stepAux s none S=⟨none,none,T⟩) : Exec (atom s) S T 1 := ⟨1,le_rfl,h⟩

def reindex (P : Proc (Fin 3)) (e : Fin 3 ↪ K) : Proc K :=
  ⟨P.Label,StackLens.program e (StackLens.Lens.identity Store) P.code⟩
noncomputable def frame (e : Fin 3 ↪ K) (A B C : List Bool) (S : Stack K) : Stack K :=
  StackEmbedding.extend e ![A,B,C] S
lemma exec_reindex (P : Proc (Fin 3)) (e : Fin 3 ↪ K) (S : Stack K)
    (A B C A' B' C' : List Bool) (n : ℕ)
    (h : Exec P ![A,B,C] ![A',B',C'] n) :
    Exec (reindex P e) (frame e A B C S) (frame e A' B' C' S) n := by
  obtain ⟨k,hk,he⟩:=h
  refine ⟨k,hk,?_⟩
  have hh := StackLens.run_cfg e (StackLens.Lens.identity Store) P.code S none k
    ⟨some default,none,![A,B,C]⟩
  rw [he] at hh
  exact hh

def triple (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c) : Fin 3 ↪ K :=
  ⟨![a,b,c],by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
omit [DecidableEq K] in
@[simp] lemma triple_zero (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    triple a b c hab hac hbc 0=a := rfl
omit [DecidableEq K] in
@[simp] lemma triple_one (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    triple a b c hab hac hbc 1=b := rfl
omit [DecidableEq K] in
@[simp] lemma triple_two (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    triple a b c hab hac hbc 2=c := rfl

def put3 (S : Stack K) (a b c : K) (A B C : List Bool) : Stack K :=
  Function.update (Function.update (Function.update S a A) b B) c C
lemma frame_triple (S : Stack K) (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (A B C : List Bool) : frame (triple a b c hab hac hbc) A B C S=put3 S a b c A B C := by
  funext j
  by_cases hja : j=a
  · subst j
    have hh:=StackEmbedding.extend_on (triple a b c hab hac hbc) ![A,B,C] S 0
    simpa [frame,put3,hab,hac,hbc,hab.symm,hac.symm,hbc.symm] using hh
  by_cases hjb : j=b
  · subst j
    have hh:=StackEmbedding.extend_on (triple a b c hab hac hbc) ![A,B,C] S 1
    simpa [frame,put3,hab,hac,hbc,hab.symm,hac.symm,hbc.symm] using hh
  by_cases hjc : j=c
  · subst j
    have hh:=StackEmbedding.extend_on (triple a b c hab hac hbc) ![A,B,C] S 2
    simpa [frame,put3] using hh
  have he : ¬∃ k,triple a b c hab hac hbc k=j := by
    rintro ⟨k,hk⟩; fin_cases k <;> simp_all
  rw [frame,StackEmbedding.extend_off _ _ _ j he]
  simp [put3,hja,hjb,hjc]
lemma put3_same (S : Stack K) (a b c : K) (_ : a≠b) (hac : a≠c) (hbc : b≠c) :
    put3 S a b c (S a) (S b) (S c)=S := by
  funext j
  by_cases hja : j=a <;> by_cases hjb : j=b <;> by_cases hjc : j=c <;> simp_all [put3]

def clearRaw : Proc (Fin 3) := ⟨Unit,WordOps.clear⟩
def reverseRaw : Proc (Fin 3) := ⟨Unit,StackReverse.program⟩
def duplicateRaw : Proc (Fin 3) := ⟨Unit,WordOps.duplicate⟩
def transferRaw : Proc (Fin 3) := ⟨Unit,TreeTransfer.program⟩
lemma clearRaw_exec (A B C : List Bool) :
    Exec clearRaw ![A,B,C] ![[],B,C] (A.length+1) :=
  ⟨_,le_rfl,WordOps.run_clear A B C none⟩
lemma reverseRaw_exec (A B C : List Bool) :
    Exec reverseRaw ![A,B,C] ![[],A.reverse++B,C] (A.length+1) :=
  ⟨_,le_rfl,StackReverse.run_reverse A B C none⟩
lemma duplicateRaw_exec (A B C : List Bool) :
    Exec duplicateRaw ![A,B,C] ![[],A.reverse++B,A.reverse++C] (A.length+1) :=
  ⟨_,le_rfl,WordOps.run_duplicate A B C none⟩
lemma transferRaw_exec (x : TreeData.Data) (A B : List Bool) :
    Exec transferRaw ![TreeData.encode x++A,B,[false]] ![A,(TreeData.encode x).reverse++B,[]]
      ((TreeData.encode x).length+1) :=
  ⟨_,le_rfl,TreeTransfer.run_transfer x A B none⟩
end MatchingFPRAS.RegisterProc

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_RegisterTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RegisterProc
open Turing MachineCost TreeData

lemma exec_perm (P : Proc (Fin 3)) (e : Fin 3 ≃ Fin 3) (S T : Stack (Fin 3))
    (n : ℕ) (h : Exec P (S ∘ e) (T ∘ e) n) : Exec (reindex P e.toEmbedding) S T n := by
  have hf (S : Stack (Fin 3)) : frame e.toEmbedding (S (e 0)) (S (e 1)) (S (e 2)) S=S := by
    funext j
    obtain ⟨i,rfl⟩:=e.surjective j
    have hh:=StackEmbedding.extend_on e.toEmbedding ![S (e 0),S (e 1),S (e 2)] S i
    fin_cases i <;> exact hh
  have hs : S ∘ e=![S (e 0),S (e 1),S (e 2)] := by funext i; fin_cases i <;> rfl
  have ht : T ∘ e=![T (e 0),T (e 1),T (e 2)] := by funext i; fin_cases i <;> rfl
  rw [hs,ht] at h
  have hh:=exec_reindex P e.toEmbedding S _ _ _ _ _ _ n h
  rw [hf] at hh
  have hf' : frame e.toEmbedding (T (e 0)) (T (e 1)) (T (e 2)) S=T := by
    funext j
    obtain ⟨i,rfl⟩:=e.surjective j
    have he:=StackEmbedding.extend_on e.toEmbedding ![T (e 0),T (e 1),T (e 2)] S i
    fin_cases i <;> exact he
  rwa [hf'] at hh

def p02 : Fin 3 ≃ Fin 3 := Equiv.swap 0 2
def p01 : Fin 3 ≃ Fin 3 := Equiv.swap 0 1
def p12 : Fin 3 ≃ Fin 3 := Equiv.swap 1 2
def p201 : Fin 3 ≃ Fin 3 := p02.trans p01

def p120 : Fin 3 ≃ Fin 3 := p201.symm
@[simp] lemma vector_p01 (A B C : List Bool) : ![A,B,C] ∘ p01=![B,A,C] := by
  funext i; fin_cases i <;> rfl
@[simp] lemma vector_p02 (A B C : List Bool) : ![A,B,C] ∘ p02=![C,B,A] := by
  funext i; fin_cases i <;> rfl
@[simp] lemma vector_p12 (A B C : List Bool) : ![A,B,C] ∘ p12=![A,C,B] := by
  funext i; fin_cases i <;> rfl
@[simp] lemma vector_p201 (A B C : List Bool) : ![A,B,C] ∘ p201=![C,A,B] := by
  funext i; fin_cases i <;> rfl
@[simp] lemma vector_p120 (A B C : List Bool) : ![A,B,C] ∘ p120=![B,C,A] := by
  funext i; fin_cases i <;> rfl

def reverse02 : Proc (Fin 3) := reindex reverseRaw p12.toEmbedding
def reverse10 : Proc (Fin 3) := reindex reverseRaw p01.toEmbedding
def reverse20 : Proc (Fin 3) := reindex reverseRaw p201.toEmbedding
def reverse21 : Proc (Fin 3) := reindex reverseRaw p02.toEmbedding
lemma reverse02_exec (A B C : List Bool) :
    Exec reverse02 ![A,B,C] ![[],B,A.reverse++C] (A.length+1) := by
  apply exec_perm
  simpa only [vector_p12] using reverseRaw_exec A C B
lemma reverse10_exec (A B C : List Bool) :
    Exec reverse10 ![A,B,C] ![B.reverse++A,[],C] (B.length+1) := by
  apply exec_perm
  simpa only [vector_p01] using reverseRaw_exec B A C
lemma reverse20_exec (A B C : List Bool) :
    Exec reverse20 ![A,B,C] ![C.reverse++A,B,[]] (C.length+1) := by
  apply exec_perm
  simpa only [vector_p201] using reverseRaw_exec C A B
lemma reverse21_exec (A B C : List Bool) :
    Exec reverse21 ![A,B,C] ![A,C.reverse++B,[]] (C.length+1) := by
  apply exec_perm
  simpa only [vector_p02] using reverseRaw_exec C B A

def finishCons : Proc (Fin 3) := atom (.push 0 (fun _=>false) (.push 1 (fun _=>true) .halt))
lemma finishCons_exec (A : List Bool) : Exec finishCons ![[],A,[]] ![[false],true::A,[]] 1 := by
  apply exec_atom
  simp only [TM2.stepAux]
  congr 1
  funext i; fin_cases i <;> simp

def cons : Proc (Fin 3) := seq reverse02 (seq reverse21 finishCons)
lemma cons_exec (x y : Data) :
    Exec cons ![encode x,encode y,[]] ![encode .nil,encode (.cons x y),[]]
      (2*(encode x).length+3) := by
  have h₁:=reverse02_exec (encode x) (encode y) []
  have h₂:=reverse21_exec [] (encode y) (encode x).reverse
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h₁ h₂
  have hh:=h₁.seq (h₂.seq (finishCons_exec (encode x++encode y)))
  exact hh.mono (by omega)

def clear1 : Proc (Fin 3) := reindex clearRaw p01.toEmbedding
lemma clear1_exec (A B C : List Bool) : Exec clear1 ![A,B,C] ![A,[],C] (B.length+1) := by
  apply exec_perm
  simpa only [vector_p01] using clearRaw_exec B A C

def copy : Proc (Fin 3) := seq clear1 (seq duplicateRaw (seq reverse10 reverse21))
lemma copy_exec (A B : List Bool) : Exec copy ![A,B,[]] ![A,A,[]]
    (B.length+3*A.length+4) := by
  have h₁:=clear1_exec A B []
  have h₂:=duplicateRaw_exec A [] []
  have h₃:=reverse10_exec [] A.reverse A.reverse
  have h₄:=reverse21_exec A [] A.reverse
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at h₂ h₃ h₄
  have hh:=h₁.seq (h₂.seq (h₃.seq h₄))
  exact hh.mono (by omega)

def startSplit : Proc (Fin 3) := atom (.pop 1 (fun v _=>v) (.push 0 (fun _=>false) .halt))
lemma startSplit_exec (A : List Bool) : Exec startSplit ![[],true::A,[]] ![[false],A,[]] 1 := by
  apply exec_atom
  simp only [TM2.stepAux]
  congr 1
  funext i; fin_cases i <;> simp
def transfer12 : Proc (Fin 3) := reindex transferRaw p120.toEmbedding
lemma transfer12_exec (x : Data) (A B : List Bool) :
    Exec transfer12 ![[false],encode x++A,B] ![[],A,(encode x).reverse++B]
      ((encode x).length+1) := by
  apply exec_perm
  simpa only [vector_p120] using transferRaw_exec x A B

def split : Proc (Fin 3) := seq clearRaw (seq startSplit (seq transfer12 reverse20))
lemma split_exec (A : List Bool) (x y : Data) :
    Exec split ![A,encode (.cons x y),[]] ![encode x,encode y,[]]
      (A.length+2*(encode x).length+4) := by
  have h₁:=clearRaw_exec A (encode (.cons x y)) []
  have h₂:=startSplit_exec (encode x++encode y)
  have h₃:=transfer12_exec x (encode y) []
  have h₄:=reverse20_exec [] (encode y) (encode x).reverse
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at h₃ h₄
  have hh:=h₁.seq (h₂.seq (h₃.seq h₄))
  exact hh.mono (by omega)
end MatchingFPRAS.RegisterProc

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RegisterProc
open Turing TreeData

def makeNil : Proc (Fin 3) := seq clearRaw (atom (.push 0 (fun _=>false) .halt))
lemma makeNil_exec (A B C : List Bool) : Exec makeNil ![A,B,C] ![[false],B,C] (A.length+2) := by
  have h₁:=clearRaw_exec A B C
  have h₂ : Exec (atom (.push 0 (fun _=>false) .halt)) ![[],B,C] ![[false],B,C] 1 := by
    apply exec_atom
    simp only [TM2.stepAux]
    congr 1
    funext i; fin_cases i <;> simp
  exact (h₁.seq h₂).mono (by omega)

variable {K : Type} [DecidableEq K]
lemma exec_on (P : Proc (Fin 3)) (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (S : Stack K) (A B C : List Bool) (n : ℕ)
    (h : Exec P ![S a,S b,S c] ![A,B,C] n) :
    Exec (reindex P (triple a b c hab hac hbc)) S (put3 S a b c A B C) n := by
  have hh:=exec_reindex P (triple a b c hab hac hbc) S _ _ _ _ _ _ n h
  simpa only [frame_triple,put3_same S a b c hab hac hbc] using hh
end MatchingFPRAS.RegisterProc

namespace MatchingFPRAS.TreeMachine
open TreeData RegisterProc Turing MachineCost

variable {R Λ : Type} [DecidableEq R]
abbrev K (R : Type) := R⊕Fin 2
abbrev Env (R : Type) := R→Data

def encodeEnv (E : Env R) : Stack (K R)
  | .inl r => encode (E r)
  | .inr _ => []
def pairEmbedding (i j : R) (hij : i≠j) : Fin 3 ↪ K R :=
  triple (.inl i) (.inl j) (.inr 0) (by simpa) (by simp) (by simp)
def singleEmbedding (i : R) : Fin 3 ↪ K R :=
  triple (.inl i) (.inr 0) (.inr 1) (by simp) (by simp) (by simp)

def putPair (E : Env R) (i j : R) (x y : Data) : Env R :=
  Function.update (Function.update E i x) j y
lemma encode_putPair (E : Env R) (i j : R) (hij : i≠j) (x y : Data) :
    put3 (encodeEnv E) (.inl i) (.inl j) (.inr 0) (encode x) (encode y) []=
      encodeEnv (putPair E i j x y) := by
  funext k
  cases k with
  | inr k => fin_cases k <;> simp [put3,encodeEnv]
  | inl k =>
    by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [put3,encodeEnv,putPair]
lemma encode_putSingle (E : Env R) (i : R) (x : Data) :
    put3 (encodeEnv E) (.inl i) (.inr 0) (.inr 1) (encode x) [] []=
      encodeEnv (Function.update E i x) := by
  funext k
  cases k with
  | inr k => fin_cases k <;> simp [put3,encodeEnv]
  | inl k => by_cases hi : k=i <;> simp_all [put3,encodeEnv]

inductive Instr (R Λ : Type) where
  | halt
  | go (next : Λ)
  | branch (i : R) (nil cons : Λ)
  | nil (i : R) (next : Λ)
  | copy (i j : R) (distinct : i≠j) (next : Λ)
  | cons (i j : R) (distinct : i≠j) (next : Λ)
  | split (i j : R) (distinct : i≠j) (next : Λ)

def procedure : Instr R Λ → Proc (K R)
  | .nil i _ => reindex makeNil (singleEmbedding i)
  | .copy i j h _ => reindex RegisterProc.copy (pairEmbedding i j h)
  | .cons i j h _ => reindex RegisterProc.cons (pairEmbedding i j h)
  | .split i j h _ => reindex RegisterProc.split (pairEmbedding i j h)
  | _ => atom .halt

lemma nil_exec (E : Env R) (i : R) (l : Λ) :
    Exec (procedure (.nil i l)) (encodeEnv E) (encodeEnv (Function.update E i .nil))
      ((encode (E i)).length+2) := by
  have hh:=exec_on (K:=K R) makeNil (.inl i) (.inr 0) (.inr 1) (by simp) (by simp) (by simp)
    (encodeEnv E) [false] [] [] _ (makeNil_exec (encode (E i)) [] [])
  have he:=encode_putSingle E i .nil
  simp only [encode] at he
  rwa [he] at hh
lemma copy_exec (E : Env R) (i j : R) (hij : i≠j) (l : Λ) :
    Exec (procedure (.copy i j hij l)) (encodeEnv E) (encodeEnv (putPair E i j (E i) (E i)))
      ((encode (E j)).length+3*(encode (E i)).length+4) := by
  have hh:=exec_on (K:=K R) RegisterProc.copy (.inl i) (.inl j) (.inr 0) (by simpa) (by simp) (by simp)
    (encodeEnv E) (encode (E i)) (encode (E i)) [] _ (RegisterProc.copy_exec (encode (E i)) (encode (E j)))
  rwa [encode_putPair E i j hij] at hh
lemma cons_exec (E : Env R) (i j : R) (hij : i≠j) (l : Λ) :
    Exec (procedure (.cons i j hij l)) (encodeEnv E) (encodeEnv (putPair E i j .nil (.cons (E i) (E j))))
      (2*(encode (E i)).length+3) := by
  have hh:=exec_on (K:=K R) RegisterProc.cons (.inl i) (.inl j) (.inr 0) (by simpa) (by simp) (by simp)
    (encodeEnv E) (encode .nil) (encode (.cons (E i) (E j))) [] _ (RegisterProc.cons_exec (E i) (E j))
  rwa [encode_putPair E i j hij] at hh
lemma split_exec (E : Env R) (i j : R) (hij : i≠j) (l : Λ) (x y : Data) (he : E j=.cons x y) :
    Exec (procedure (.split i j hij l)) (encodeEnv E) (encodeEnv (putPair E i j x y))
      ((encode (E i)).length+2*(encode x).length+4) := by
  have h:=RegisterProc.split_exec (encode (E i)) x y
  rw [←he] at h
  have hh:=exec_on (K:=K R) RegisterProc.split (.inl i) (.inl j) (.inr 0) (by simpa) (by simp) (by simp)
    (encodeEnv E) (encode x) (encode y) [] _ h
  rwa [encode_putPair E i j hij] at hh
end MatchingFPRAS.TreeMachine

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_BinaryNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.BinaryNormalize
open Turing MachineCost RegisterProc TreeTransfer
open StackAddition (value value_bits)

def normalize (A : List Bool) : List Bool := (A.reverse.dropWhile Bool.not).reverse
lemma normalize_cons (b : Bool) (A : List Bool) :
    normalize (b::A)=if normalize A=[] ∧ b=false then [] else b::normalize A := by
  simp only [normalize,List.reverse_cons,List.dropWhile_append]
  have hh (B : List Bool) :
      (if B.isEmpty then [b].dropWhile Bool.not else B++[b]).reverse=
        if B.reverse=[] ∧ b=false then [] else b::B.reverse := by
    cases B <;> cases b <;> simp
  exact hh _
lemma normalize_bits (A : List Bool) : normalize A=(value A).bits := by
  induction A with
  | nil => rfl
  | cons b A ih =>
    rw [normalize_cons,ih]
    cases b with
    | false =>
      by_cases hz : value A=0
      · simp [hz,value]
      · have hne : (value A).bits≠[] := by
          intro emptyBits
          exact hz ((value_bits (value A)).symm.trans (congrArg value emptyBits))
        simp only [value,Bool.toNat_false,Nat.zero_add, Nat.bit0_bits _ hz,hne,false_and,↓reduceIte]
    | true =>
      simp only [Bool.true_eq_false,and_false,↓reduceIte,value,Bool.toNat_true]
      rw [Nat.add_comm 1 (2*value A),Nat.bit1_bits]
lemma normalize_length (A : List Bool) : (normalize A).length≤A.length := by
  simpa only [normalize,List.length_reverse] using List.length_dropWhile_le Bool.not A.reverse

def stripProgram : Unit→TM2.Stmt (fun _ : Fin 3=>Bool) Unit (Option Bool) := fun _=>
  .peek 0 (fun _ x=>x) (.branch (fun x=>x.isNone || x.getD false)
    (.load (fun _=>none) .halt)
    (.pop 0 (fun v _=>v) (.goto (fun _=>()))))
lemma strip_nil (B C : List Bool) (v : Option Bool) :
    advance (TM2.step stripProgram) (cfg (some ()) [] B C v)=cfg none [] B C none := by
  simp [advance,TM2.step,stripProgram,TM2.stepAux,cfg]
lemma strip_true (A B C : List Bool) (v : Option Bool) :
    advance (TM2.step stripProgram) (cfg (some ()) (true::A) B C v)=cfg none (true::A) B C none := by
  simp [advance,TM2.step,stripProgram,TM2.stepAux,cfg]
lemma strip_false (A B C : List Bool) (v : Option Bool) :
    advance (TM2.step stripProgram) (cfg (some ()) (false::A) B C v)=cfg (some ()) A B C (some false) := by
  simp [advance,TM2.step,stripProgram,TM2.stepAux,cfg,update_zero]
lemma run_strip (A B C : List Bool) (v : Option Bool) :
    ∃ n≤A.length+1,MachineCost.run (TM2.step stripProgram) n (cfg (some ()) A B C v)=
      cfg none (A.dropWhile Bool.not) B C none := by
  induction A generalizing v with
  | nil => exact ⟨1,le_rfl,strip_nil B C v⟩
  | cons a A ih => cases a with
    | false =>
      obtain ⟨n,hn,he⟩:=ih (some false)
      refine ⟨n+1,by simp only [List.length_cons]; omega,?_⟩
      rw [MachineCost.run,strip_false,he]
      rfl
    | true => exact ⟨1,by simp,strip_true A B C v⟩
def stripRaw : Proc (Fin 3) := ⟨Unit,stripProgram⟩
lemma stripRaw_exec (A B C : List Bool) :
    Exec stripRaw ![A,B,C] ![A.dropWhile Bool.not,B,C] (A.length+1) := run_strip A B C none

def swap01 : Fin 3 ↪ Fin 3 := triple 1 0 2 (by decide) (by decide) (by decide)
lemma reindex_swap (P : Proc (Fin 3)) (A B C A' B' C' : List Bool) (n : ℕ)
    (h : Exec P ![A,B,C] ![A',B',C'] n) :
    Exec (reindex P swap01) ![B,A,C] ![B',A',C'] n := by
  have hh:=exec_on P (1 : Fin 3) 0 2 (by decide) (by decide) (by decide) ![B,A,C] A' B' C' n h
  have hout : put3 ![B,A,C] (1 : Fin 3) 0 2 A' B' C'=![B',A',C'] := by
    funext i; fin_cases i <;> simp [put3]
  rw [hout] at hh
  exact hh

def program : Proc (Fin 3) := seq reverseRaw (seq (reindex stripRaw swap01) (reindex reverseRaw swap01))
theorem exec (A C : List Bool) : Exec program ![A,[],C] ![normalize A,[],C] (3*A.length+3) := by
  have h₁:=reverseRaw_exec A [] C
  simp only [List.append_nil] at h₁
  have h₂:=reindex_swap stripRaw A.reverse [] C _ [] C _ (stripRaw_exec A.reverse [] C)
  have h₃:=reindex_swap reverseRaw (A.reverse.dropWhile Bool.not) [] C [] _ C _
    (reverseRaw_exec (A.reverse.dropWhile Bool.not) [] C)
  simp only [List.append_nil] at h₃
  have hh:=h₁.seq (h₂.seq h₃)
  apply hh.mono
  have hl:=List.length_dropWhile_le Bool.not A.reverse
  simp only [List.length_reverse] at hl ⊢
  omega
end MatchingFPRAS.BinaryNormalize

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_FiniteStore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteStore
open Turing MachineCost RegisterProc

variable {K Λ σ : Type} [DecidableEq K]

def stmt : TM2.Stmt (fun _ : K=>Bool) Λ σ → σ →
    TM2.Stmt (fun _ : K=>Bool) (Λ×σ) (Option Bool)
  | .push k f q,v => .push k (fun _=>f v) (stmt q v)
  | .peek k f q,v => .peek k (fun _ x=>x)
      (.branch Option.isNone (stmt q (f v none))
        (.branch (fun x=>x.getD false) (stmt q (f v (some true))) (stmt q (f v (some false)))))
  | .pop k f q,v => .pop k (fun _ x=>x)
      (.branch Option.isNone (stmt q (f v none))
        (.branch (fun x=>x.getD false) (stmt q (f v (some true))) (stmt q (f v (some false)))))
  | .load f q,v => stmt q (f v)
  | .branch f q r,v => if f v then stmt q v else stmt r v
  | .goto f,v => .load (fun _=>none) (.goto (fun _=>(f v,v)))
  | .halt,_ => .load (fun _=>none) .halt

def cfg (c : TM2.Cfg (fun _ : K=>Bool) Λ σ) :
    TM2.Cfg (fun _ : K=>Bool) (Λ×σ) (Option Bool) :=
  ⟨c.l.map (fun l=>(l,c.var)),none,c.stk⟩

theorem stmt_eval (q : TM2.Stmt (fun _ : K=>Bool) Λ σ) (v : σ) (u : Option Bool)
    (S : K→List Bool) : TM2.stepAux (stmt q v) u S=cfg (TM2.stepAux q v S) := by
  induction q generalizing v u S with
  | push k f q ih => simpa only [stmt,TM2.stepAux] using ih v u (Function.update S k (f v::S k))
  | peek k f q ih =>
    cases hh : (S k).head? with
    | none => simpa only [stmt,TM2.stepAux,hh,Option.isNone_none,Bool.cond_true] using ih (f v none) none S
    | some b => cases b <;> simpa only [stmt,TM2.stepAux,hh,Option.isNone_some,Bool.cond_false,
      Option.getD_some,Bool.cond_true] using ih (f v (S k).head?) (S k).head? S
  | pop k f q ih =>
    cases hh : (S k).head? with
    | none => simpa only [stmt,TM2.stepAux,hh,Option.isNone_none,Bool.cond_true] using ih (f v none) none (Function.update S k (S k).tail)
    | some b => cases b <;> simpa only [stmt,TM2.stepAux,hh,Option.isNone_some,Bool.cond_false,
      Option.getD_some,Bool.cond_true] using ih (f v (S k).head?) (S k).head? (Function.update S k (S k).tail)
  | load f q ih => exact ih (f v) u S
  | branch f q r ihq ihr =>
    cases hh : f v with
    | false => simpa only [stmt,TM2.stepAux,hh,Bool.false_eq_true,↓reduceIte,Bool.cond_false] using ihr v u S
    | true => simpa only [stmt,TM2.stepAux,hh,↓reduceIte,Bool.cond_true] using ihq v u S
  | goto f => rfl
  | halt => rfl

def program (M : Λ→TM2.Stmt (fun _ : K=>Bool) Λ σ) :
    Λ×σ→TM2.Stmt (fun _ : K=>Bool) (Λ×σ) (Option Bool) := fun p=>stmt (M p.1) p.2
lemma advance_cfg (M : Λ→TM2.Stmt (fun _ : K=>Bool) Λ σ)
    (c : TM2.Cfg (fun _ : K=>Bool) Λ σ) :
    advance (TM2.step (program M)) (cfg c)=cfg (advance (TM2.step M) c) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => rfl
  | some l => exact stmt_eval (M l) v none S
lemma run_cfg (M : Λ→TM2.Stmt (fun _ : K=>Bool) Λ σ) (n : ℕ)
    (c : TM2.Cfg (fun _ : K=>Bool) Λ σ) :
    MachineCost.run (TM2.step (program M)) n (cfg c)=cfg (MachineCost.run (TM2.step M) n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => rw [MachineCost.run,advance_cfg,ih,MachineCost.run]

def procedure [Fintype Λ] [DecidableEq Λ] [Inhabited Λ] [Fintype σ] [DecidableEq σ]
    (M : Λ→TM2.Stmt (fun _ : K=>Bool) Λ σ) (v : σ) : Proc K :=
  { Label := Λ×σ
    labels := inferInstance
    entry := ⟨(default,v)⟩
    code := program M }

theorem exec [Fintype Λ] [DecidableEq Λ] [Inhabited Λ] [Fintype σ] [DecidableEq σ]
    (M : Λ→TM2.Stmt (fun _ : K=>Bool) Λ σ) (v w : σ) (A B : Stack K) (n : ℕ)
    (h : MachineCost.run (TM2.step M) n ⟨some default,v,A⟩=⟨none,w,B⟩) :
    Exec (procedure M v) A B n := by
  refine ⟨n,le_rfl,?_⟩
  exact (run_cfg M n ⟨some default,v,A⟩).trans (congrArg cfg h)
end MatchingFPRAS.FiniteStore

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeData
open Data

def ofList : List Data → Data
  | [] => .nil
  | x::xs => .cons x (ofList xs)
end MatchingFPRAS.TreeData

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TableLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeData
open Data

def bit (b : Bool) : Data := if b then .cons .nil .nil else .nil
def nat (n : ℕ) : Data := ofList (n.bits.map bit)
@[simp] lemma nat_zero : nat 0=.nil := by simp [nat,Nat.bits,ofList]
end MatchingFPRAS.TreeData

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeData

def bits (A : List Bool) : Data := ofList (A.map bit)
@[simp] lemma bits_nil : bits []=.nil := rfl
@[simp] lemma bits_cons (b : Bool) (A : List Bool) : bits (b::A)=.cons (bit b) (bits A) := rfl
end MatchingFPRAS.TreeData

namespace MatchingFPRAS.TreeBits
open Turing MachineCost RegisterProc TreeData TreeTransfer

def decodeProgram : Unit→TM2.Stmt (fun _ : Fin 3=>Bool) Unit (Option Bool) := fun _=>
  .pop 0 (fun _ x=>x) (.branch (fun x=>x.getD false)
    (.pop 0 (fun _ x=>x) (.branch (fun x=>x.getD false)
      (.pop 0 (fun v _=>v) (.pop 0 (fun v _=>v) (.push 1 (fun _=>true) (.goto (fun _=>())))))
      (.push 1 (fun _=>false) (.goto (fun _=>())))))
    (.load (fun _=>none) .halt))
lemma decode_nil (A B C : List Bool) (v : Option Bool) :
    advance (TM2.step decodeProgram) (cfg (some ()) (false::A) B C v)=cfg none A B C none := by
  simp [advance,TM2.step,decodeProgram,TM2.stepAux,cfg,update_zero]
lemma decode_cons (b : Bool) (bs A B C : List Bool) (v : Option Bool) :
    advance (TM2.step decodeProgram) (cfg (some ()) (encode (bits (b::bs))++A) B C v)=
      cfg (some ()) (encode (bits bs)++A) (b::B) C (some b) := by
  cases b <;> simp [advance,TM2.step,decodeProgram,TM2.stepAux,cfg,update_zero,update_one,encode,bit]
lemma run_decode (bs A B C : List Bool) (v : Option Bool) :
    MachineCost.run (TM2.step decodeProgram) (bs.length+1)
      (cfg (some ()) (encode (bits bs)++A) B C v)=cfg none A (bs.reverse++B) C none := by
  induction bs generalizing B v with
  | nil => simpa only [bits_nil,encode,List.singleton_append,List.length_nil,List.reverse_nil,List.nil_append,Nat.zero_add,MachineCost.run] using decode_nil A B C v
  | cons b bs ih =>
    rw [List.length_cons,Nat.add_right_comm,MachineCost.run,decode_cons,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
def decodeRaw : Proc (Fin 3) := ⟨Unit,decodeProgram⟩
lemma decodeRaw_exec (bs A B C : List Bool) :
    Exec decodeRaw ![encode (bits bs)++A,B,C] ![A,bs.reverse++B,C] (bs.length+1) :=
  ⟨_,le_rfl,run_decode bs A B C none⟩

def encodeProgram : Unit→TM2.Stmt (fun _ : Fin 3=>Bool) Unit (Option Bool) := fun _=>
  .pop 0 (fun _ x=>x) (.branch Option.isNone (.load (fun _=>none) .halt)
    (.branch (fun x=>x.getD false)
      (.push 1 (fun _=>false) (.push 1 (fun _=>false) (.push 1 (fun _=>true) (.push 1 (fun _=>true) (.goto (fun _=>()))))))
      (.push 1 (fun _=>false) (.push 1 (fun _=>true) (.goto (fun _=>()))))))
lemma encode_nil (B C : List Bool) (v : Option Bool) :
    advance (TM2.step encodeProgram) (cfg (some ()) [] B C v)=cfg none [] B C none := by
  simp [advance,TM2.step,encodeProgram,TM2.stepAux,cfg,update_zero]
lemma encode_cons (b : Bool) (bs C : List Bool) (x : Data) (v : Option Bool) :
    advance (TM2.step encodeProgram) (cfg (some ()) (b::bs) (encode x) C v)=
      cfg (some ()) bs (encode (.cons (bit b) x)) C (some b) := by
  cases b <;> simp [advance,TM2.step,encodeProgram,TM2.stepAux,cfg,update_zero,update_one,encode,bit]
def prepend (bs : List Bool) (x : Data) : Data := bs.foldr (fun b x=>.cons (bit b) x) x
lemma prepend_append (A B : List Bool) (x : Data) : prepend (A++B) x=prepend A (prepend B x) := by
  simp [prepend,List.foldr_append]
lemma run_encode (bs C : List Bool) (x : Data) (v : Option Bool) :
    MachineCost.run (TM2.step encodeProgram) (bs.length+1)
      (cfg (some ()) bs (encode x) C v)=cfg none [] (encode (prepend bs.reverse x)) C none := by
  induction bs generalizing x v with
  | nil => exact encode_nil (encode x) C v
  | cons b bs ih =>
    rw [List.length_cons,Nat.add_right_comm,MachineCost.run,encode_cons,ih,List.reverse_cons,prepend_append]
    rfl
lemma prepend_bits (bs : List Bool) : prepend bs .nil=bits bs := by
  induction bs <;> simp_all [prepend,bits,ofList]
def encodeRaw : Proc (Fin 3) := ⟨Unit,encodeProgram⟩
lemma encodeRaw_exec (bs C : List Bool) :
    Exec encodeRaw ![bs.reverse,[false],C] ![[],encode (bits bs),C] (bs.length+1) := by
  refine ⟨_,le_rfl,?_⟩
  have h:=run_encode bs.reverse C .nil none
  simpa only [List.length_reverse,List.reverse_reverse,prepend_bits,encode,encodeRaw,cfg,stackData] using h
end MatchingFPRAS.TreeBits

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeNumberOps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeBits
open Turing MachineCost RegisterProc BinaryNormalize TreeData

def decodeForward : Proc (Fin 3) := seq decodeRaw (reindex reverseRaw swap01)
lemma decodeForward_exec (A C : List Bool) :
    Exec decodeForward ![encode (bits A),[],C] ![A,[],C] (2*A.length+2) := by
  have h₁:=decodeRaw_exec A [] [] C
  simp only [List.append_nil] at h₁
  have h₂:=reindex_swap reverseRaw A.reverse [] C [] _ C _ (reverseRaw_exec A.reverse [] C)
  simp only [List.reverse_reverse,List.append_nil] at h₂
  apply (h₁.seq h₂).mono
  simp only [List.length_reverse]; omega

def encodeForward : Proc (Fin 3) := seq reverseRaw
  (seq (atom (.push 0 (fun _=>false) .halt)) (reindex encodeRaw swap01))
end MatchingFPRAS.TreeBits

namespace MatchingFPRAS.BinaryArithmeticProc
open RegisterProc Turing MachineCost

local instance addEntry : Inhabited (Bool⊕Unit) := ⟨.inl false⟩
def add : Proc (Fin 3) := FiniteStore.procedure ForwardAddition.program (default : StackAddition.Store)
lemma add_exec (A B : List Bool) :
    Exec add ![A,B,[]] ![StackAddition.addDigits false A B,[],[]] (2*(A.length+B.length)+3) := by
  obtain ⟨n,hn,he⟩:=ForwardAddition.run_add A B
  exact (FiniteStore.exec ForwardAddition.program default default _ _ n he).mono hn

local instance compareEntry : Inhabited Ordering := ⟨.eq⟩
def compare : Proc (Fin 3) := FiniteStore.procedure StackCompare.program (default : StackAddition.Store)
lemma compare_exec (A B : List Bool) :
    Exec compare ![A,B,[]] ![[],[],StackCompare.flags (Ord.compare (StackAddition.value A) (StackAddition.value B))]
      (A.length+B.length+1) := by
  obtain ⟨n,hn,he⟩:=StackCompare.run_comparison A B [] .eq default
  have h:=FiniteStore.exec StackCompare.program default default _ _ n he
  simp only [StackCompare.compares_values,List.append_nil] at h
  exact h.mono hn
end MatchingFPRAS.BinaryArithmeticProc

namespace MatchingFPRAS.TreeArithmetic
open RegisterProc TreeData TreeMachine Turing

variable {R : Type} [DecidableEq R]

def decode (i : R) : Proc (K R) := reindex TreeBits.decodeForward (singleEmbedding i)
def encode (i : R) : Proc (K R) := reindex TreeBits.encodeForward (singleEmbedding i)
def normalize (i : R) : Proc (K R) := reindex BinaryNormalize.program (singleEmbedding i)
def add (i j : R) (hij : i≠j) : Proc (K R) :=
  seq (decode i) (seq (decode j)
    (seq (reindex BinaryArithmeticProc.add (pairEmbedding i j hij))
      (seq (normalize i) (seq (encode i) (atom (.push (.inl j) (fun _=>false) .halt))))))

def rawPair (E : Env R) (i j : R) (A B : List Bool) : Stack (K R) :=
  Function.update (Function.update (encodeEnv E) (.inl i) A) (.inl j) B
lemma rawPair_scratch (E : Env R) (i j : R) (A B : List Bool) (k : Fin 2) :
    rawPair E i j A B (.inr k)=[] := by simp [rawPair,encodeEnv]
lemma rawPair_left (E : Env R) (i j : R) (hij : i≠j) (A B : List Bool) :
    rawPair E i j A B (.inl i)=A := by simp [rawPair,hij]
lemma rawPair_right (E : Env R) (i j : R) (A B : List Bool) :
    rawPair E i j A B (.inl j)=B := by simp [rawPair]
lemma rawPair_encode (E : Env R) (i j : R) (x y : Data) :
    rawPair E i j (TreeData.encode x) (TreeData.encode y)=encodeEnv (putPair E i j x y) := by
  funext k
  cases k with
  | inr k => simp [rawPair,encodeEnv]
  | inl k => by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [rawPair,encodeEnv,putPair]
lemma rawPair_same (E : Env R) (i j : R) :
    rawPair E i j (TreeData.encode (E i)) (TreeData.encode (E j))=encodeEnv E := by
  funext k
  cases k with
  | inr k => simp [rawPair,encodeEnv]
  | inl k => by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [rawPair,encodeEnv]
lemma put3_raw_left (E : Env R) (i j : R) (hij : i≠j) (A B F : List Bool) :
    put3 (rawPair E i j A B) (.inl i) (.inr 0) (.inr 1) F [] []=rawPair E i j F B := by
  funext k
  cases k with
  | inr k => fin_cases k <;> simp [put3,rawPair,encodeEnv]
  | inl k => by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [put3,rawPair]
lemma put3_raw_right (E : Env R) (i j : R) (hij : i≠j) (A B F : List Bool) :
    put3 (rawPair E i j A B) (.inl j) (.inr 0) (.inr 1) F [] []=rawPair E i j A F := by
  funext k
  cases k with
  | inr k => fin_cases k <;> simp [put3,rawPair,encodeEnv]
  | inl k => by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [put3,rawPair]
lemma on_left (P : Proc (Fin 3)) (E : Env R) (i j : R) (hij : i≠j) (A B F : List Bool) (n : ℕ)
    (h : Exec P ![A,[],[]] ![F,[],[]] n) :
    Exec (reindex P (singleEmbedding i)) (rawPair E i j A B) (rawPair E i j F B) n := by
  have hh:=exec_on P (.inl i : K R) (.inr 0) (.inr 1) (by simp) (by simp) (by simp)
    (rawPair E i j A B) F [] [] n
  rw [rawPair_left E i j hij,rawPair_scratch,rawPair_scratch] at hh
  simpa only [singleEmbedding,put3_raw_left E i j hij] using hh h
lemma on_right (P : Proc (Fin 3)) (E : Env R) (i j : R) (hij : i≠j) (A B F : List Bool) (n : ℕ)
    (h : Exec P ![B,[],[]] ![F,[],[]] n) :
    Exec (reindex P (singleEmbedding j)) (rawPair E i j A B) (rawPair E i j A F) n := by
  have hh:=exec_on P (.inl j : K R) (.inr 0) (.inr 1) (by simp) (by simp) (by simp)
    (rawPair E i j A B) F [] [] n
  rw [rawPair_right,rawPair_scratch,rawPair_scratch] at hh
  simpa only [singleEmbedding,put3_raw_right E i j hij] using hh h
lemma on_pair (P : Proc (Fin 3)) (E : Env R) (i j : R) (hij : i≠j) (A B F G : List Bool) (n : ℕ)
    (h : Exec P ![A,B,[]] ![F,G,[]] n) :
    Exec (reindex P (pairEmbedding i j hij)) (rawPair E i j A B) (rawPair E i j F G) n := by
  have hh:=exec_on P (.inl i : K R) (.inl j) (.inr 0) (by simpa) (by simp) (by simp)
    (rawPair E i j A B) F G [] n
  rw [rawPair_left E i j hij,rawPair_right,rawPair_scratch] at hh
  have he : put3 (rawPair E i j A B) (.inl i) (.inl j) (.inr 0) F G []=rawPair E i j F G := by
    funext k
    cases k with
    | inr k => fin_cases k <;> simp [put3,rawPair,encodeEnv]
    | inl k => by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [put3,rawPair]
  exact he ▸ hh h

end MatchingFPRAS.TreeArithmetic

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.BinaryArithmeticProc
open RegisterProc TreeData Turing

def pickLt : Proc (Fin 3) := atom
  (.pop 2 (fun _ x=>x) (.pop 2 (fun x _=>x)
    (.branch (fun x=>x.getD false)
      (.push 0 (fun _=>false) (.push 0 (fun _=>false) (.push 0 (fun _=>true)
        (.load (fun _=>none) .halt))))
      (.push 0 (fun _=>false) (.load (fun _=>none) .halt)))))
lemma pickLt_exec (c : Ordering) :
    Exec pickLt ![[],[],StackCompare.flags c] ![encode (bit (decide (c=.lt))),[],[]] 1 := by
  apply exec_atom
  cases c <;> simp [TM2.stepAux,StackCompare.flags,encode,bit]
  all_goals funext k; fin_cases k <;> simp

def less : Proc (Fin 3) := seq compare pickLt
lemma less_exec (A B : List Bool) :
    Exec less ![A,B,[]] ![encode (bit (decide (StackAddition.value A<StackAddition.value B))),[],[]]
      (A.length+B.length+2) := by
  have hh:=(compare_exec A B).seq (pickLt_exec (Ord.compare (StackAddition.value A) (StackAddition.value B)))
  simp only [compare_lt_iff_lt] at hh
  exact hh.mono (by omega)
end MatchingFPRAS.BinaryArithmeticProc

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_RegisterControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RegisterControl
open TreeData TreeMachine RegisterProc Turing MachineCost

variable {R Λ : Type} [DecidableEq R]
inductive Instr (R Λ : Type) where
  | halt
  | go (next : Λ)
  | branch (i : R) (nil cons : Λ)
  | call (P : Proc (K R)) (next : Λ)

def procedure : Instr R Λ → Proc (K R)
  | .call P _ => P
  | _ => atom .halt
def successor : Instr R Λ → Option Λ
  | .call _ l => some l
  | _ => none
abbrev Label (M : Λ → Instr R Λ) := Λ ⊕ ((l : Λ) × (procedure (M l)).Label)
instance instFintypeLabel (M : Λ → Instr R Λ) [Fintype Λ] : Fintype (Label M) := by unfold Label; infer_instance

def code (M : Λ → Instr R Λ) : Label M → TM2.Stmt (fun _ : K R=>Bool) (Label M) Store
  | .inl l => match M l with
    | .halt => .halt
    | .go k => .goto (fun _=>.inl k)
    | .branch i a b => .peek (.inl i) (fun _ x=>x) (.branch (fun x=>x.getD false)
        (.load (fun _=>none) (.goto (fun _=>.inl b)))
        (.load (fun _=>none) (.goto (fun _=>.inl a))))
    | .call _ _ => .goto (fun _=>.inr ⟨l,default⟩)
  | .inr ⟨l,u⟩ => StackComposition.relabel (fun u=>.inr ⟨l,u⟩)
      ((successor (M l)).map Sum.inl) ((procedure (M l)).code u)
def compile [Fintype Λ] [Inhabited Λ] (M : Λ → Instr R Λ) : Proc (K R) :=
  { Label := Label M
    entry := ⟨.inl default⟩
    code := code M }
def cfg (M : Λ → Instr R Λ) (l : Option Λ) (E : Env R) : TM2.Cfg (fun _ : K R=>Bool) (Label M) Store :=
  ⟨l.map Sum.inl,none,encodeEnv E⟩

inductive Effect : Instr R Λ → Env R → Option Λ → Env R → ℕ → Prop
  | halt (E) : Effect .halt E none E 1
  | go (E l) : Effect (.go l) E (some l) E 1
  | nilBranch (E i l r) (h : E i=.nil) : Effect (.branch i l r) E (some l) E 1
  | consBranch (E i l r x y) (h : E i=.cons x y) : Effect (.branch i l r) E (some r) E 1
  | call (P E F l n) (h : Exec P (encodeEnv E) (encodeEnv F) n) : Effect (.call P l) E (some l) F (n+1)

lemma effect_compiles (M : Λ → Instr R Λ) (l : Λ) (I : Instr R Λ) (hI : M l=I)
    (E F : Env R) (next : Option Λ) (n : ℕ) (h : Effect I E next F n) :
    ∃ k≤n,MachineCost.run (TM2.step (code M)) k (cfg M (some l) E)=cfg M next F := by
  cases h with
  | halt E =>
    refine ⟨1,le_rfl,?_⟩
    simp only [MachineCost.run,advance,TM2.step,cfg,Option.map_some,code,hI,TM2.stepAux,
      Option.getD_some,Option.map_none]
  | go E a =>
    refine ⟨1,le_rfl,?_⟩
    simp only [MachineCost.run,advance,TM2.step,cfg,Option.map_some,code,hI,TM2.stepAux,Option.getD_some]
  | nilBranch E i a b hi =>
    refine ⟨1,le_rfl,?_⟩
    simp only [MachineCost.run,advance,TM2.step,cfg,Option.map_some,code,hI,TM2.stepAux,
      encodeEnv,hi,encode,List.head?_cons,Option.getD_some,Bool.cond_false]
  | consBranch E i a b x y hi =>
    refine ⟨1,le_rfl,?_⟩
    simp only [MachineCost.run,advance,TM2.step,cfg,Option.map_some,code,hI,TM2.stepAux,
      encodeEnv,hi,encode,List.head?_cons,Option.getD_some,Bool.cond_true]
  | call P E F a n hp =>
    have hp' : Exec (procedure (M l)) (encodeEnv E) (encodeEnv F) n := by simpa only [hI,procedure] using hp
    obtain ⟨j,hj,he⟩:=hp'
    obtain ⟨k,hk,hs⟩:=StackComposition.run_relabel_to_halt (procedure (M l)).code (code M)
      (fun u=>Sum.inr ⟨l,u⟩) ((successor (M l)).map Sum.inl) (fun _=>rfl)
      j ⟨some default,none,encodeEnv E⟩ none (encodeEnv F) he
    refine ⟨k+1,by omega,?_⟩
    rw [MachineCost.run]
    have ha : advance (TM2.step (code M)) (cfg M (some l) E)=
        StackComposition.mapCfg (fun u=>Sum.inr ⟨l,u⟩) ((successor (M l)).map Sum.inl)
          ⟨some default,none,encodeEnv E⟩ := by
      simp only [advance,TM2.step,cfg,Option.map_some,code,hI,TM2.stepAux,Option.getD_some,
        StackComposition.mapCfg_some]
    rw [ha,hs]
    simp only [cfg,hI,successor,Option.map_some]

inductive Runs (M : Λ → Instr R Λ) : Option Λ → Env R → Env R → ℕ → Prop
  | done (E) : Runs M none E E 0
  | step (l E next F G n k) (h : Effect (M l) E next F k)
      (rest : Runs M next F G n) : Runs M (some l) E G (k+n)
  | weaken (l : Option Λ) (E F : Env R) (n b : ℕ) (h : Runs M l E F n) (hn : n ≤ b) : Runs M l E F b
lemma runs_compiles (M : Λ → Instr R Λ) (n : ℕ) (l : Option Λ) (E F : Env R)
    (h : Runs M l E F n) :
    ∃ k≤n,MachineCost.run (TM2.step (code M)) k (cfg M l E)=cfg M none F := by
  induction h with
  | done E => exact ⟨0,le_rfl,rfl⟩
  | step l E next F G n k h rest ih =>
    obtain ⟨i,hi,he⟩:=effect_compiles M l (M l) rfl E F next k h
    obtain ⟨j,hj,hf⟩:=ih
    exact ⟨i+j,Nat.add_le_add hi hj,by rw [run_add,he,hf]⟩
  | weaken l E F n m h hnm ih => obtain ⟨k,hk,he⟩:=ih; exact ⟨k,hk.trans hnm,he⟩
lemma compile_exec [Fintype Λ] [Inhabited Λ] (M : Λ → Instr R Λ) (n : ℕ) (E F : Env R)
    (h : Runs M (some default) E F n) : Exec (compile M) (encodeEnv E) (encodeEnv F) n :=
  runs_compiles M n (some default) E F h
end MatchingFPRAS.RegisterControl

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_RegisterStructured
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RegisterStructured
open RegisterProc TreeData TreeMachine RegisterControl

variable {R : Type} [DecidableEq R]

inductive Select where | test | left | right | halt deriving DecidableEq, Inhabited
instance instFintypeSelect : Fintype Select := ⟨{.test,.left,.right,.halt},by intro s; cases s <;> simp⟩
def selectCode (i : R) (P Q : Proc (K R)) : Select → RegisterControl.Instr R Select
  | .test => .branch i .left .right
  | .left => .call P .halt
  | .right => .call Q .halt
  | .halt => .halt
def select (i : R) (P Q : Proc (K R)) : Proc (K R) := compile (selectCode i P Q)
lemma select_nil (i : R) (P Q : Proc (K R)) (E F : Env R) (n : ℕ)
    (hi : E i=.nil) (h : Exec P (encodeEnv E) (encodeEnv F) n) :
    Exec (select i P Q) (encodeEnv E) (encodeEnv F) (n+3) := by
  have hh : RegisterControl.Runs (selectCode i P Q) (some Select.halt) F F 1 :=
    Runs.step _ _ _ _ _ 0 1 (Effect.halt _) (Runs.done _)
  have hl : RegisterControl.Runs (selectCode i P Q) (some Select.left) E F ((n+1)+1) :=
    Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ n h) hh
  have ht : RegisterControl.Runs (selectCode i P Q) (some Select.test) E F (1+((n+1)+1)) :=
    Runs.step _ _ _ _ _ _ _ (Effect.nilBranch E i _ _ hi) hl
  exact (compile_exec _ _ _ _ ht).mono (by omega)
lemma select_cons (i : R) (P Q : Proc (K R)) (E F : Env R) (n : ℕ) (x y : Data)
    (hi : E i=.cons x y) (h : Exec Q (encodeEnv E) (encodeEnv F) n) :
    Exec (select i P Q) (encodeEnv E) (encodeEnv F) (n+3) := by
  have hh : RegisterControl.Runs (selectCode i P Q) (some Select.halt) F F 1 :=
    Runs.step _ _ _ _ _ 0 1 (Effect.halt _) (Runs.done _)
  have hr : RegisterControl.Runs (selectCode i P Q) (some Select.right) E F ((n+1)+1) :=
    Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ n h) hh
  have ht : RegisterControl.Runs (selectCode i P Q) (some Select.test) E F (1+((n+1)+1)) :=
    Runs.step _ _ _ _ _ _ _ (Effect.consBranch E i _ _ x y hi) hr
  exact (compile_exec _ _ _ _ ht).mono (by omega)

end MatchingFPRAS.RegisterStructured

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFunction
open TreeData TreeMachine RegisterProc

abbrev Reg := Fin 10
def env (x y s : Data) : Env Reg := fun i=>if i=0 then x else if i=1 then y else if i=2 then s else .nil
@[simp] lemma env0 (x y s : Data) : env x y s 0=x := rfl
@[simp] lemma env1 (x y s : Data) : env x y s 1=y := rfl
@[simp] lemma env2 (x y s : Data) : env x y s 2=s := rfl
def size (x : Data) : ℕ := (TreeData.encode x).length
@[simp] lemma size_nil : size .nil=1 := rfl
@[simp] lemma size_cons (x y : Data) : size (.cons x y)=size x+size y+1 := by
  simp [size,TreeData.encode]

lemma env_update0 (x y s a : Data) : Function.update (env x y s) 0 a=env a y s := by
  funext i; fin_cases i <;> simp [env]
lemma env_update1 (x y s a : Data) : Function.update (env x y s) 1 a=env x a s := by
  funext i; fin_cases i <;> simp [env]
lemma env_update2 (x y s a : Data) : Function.update (env x y s) 2 a=env x y a := by
  funext i; fin_cases i <;> simp [env]
attribute [simp] env_update0 env_update1 env_update2

def clear (i : Reg) : Proc (K Reg) := procedure (.nil i ())
def copy (i j : Reg) (h : i≠j) : Proc (K Reg) := procedure (.copy i j h ())
def cons (i j : Reg) (h : i≠j) : Proc (K Reg) := procedure (.cons i j h ())
def split (i j : Reg) (h : i≠j) : Proc (K Reg) := procedure (.split i j h ())

lemma copy01 (x y s : Data) :
    Exec (copy 0 1 (by decide)) (encodeEnv (env x y s)) (encodeEnv (env x x s)) (size y+3*size x+4) := by
  simpa only [putPair,env_update0,env_update1,env0,env1,size,copy] using copy_exec (env x y s) 0 1 (by decide) ()
lemma copy10 (x y s : Data) :
    Exec (copy 1 0 (by decide)) (encodeEnv (env x y s)) (encodeEnv (env y y s)) (size x+3*size y+4) := by
  simpa only [putPair,env_update0,env_update1,env0,env1,size,copy] using copy_exec (env x y s) 1 0 (by decide) ()
lemma cons12 (x y s : Data) :
    Exec (cons 1 2 (by decide)) (encodeEnv (env x y s)) (encodeEnv (env x .nil (.cons y s))) (2*size y+3) := by
  simpa only [putPair,env_update1,env_update2,env1,env2,size,cons] using cons_exec (env x y s) 1 2 (by decide) ()
lemma cons02 (x y s : Data) :
    Exec (cons 0 2 (by decide)) (encodeEnv (env x y s)) (encodeEnv (env .nil y (.cons x s))) (2*size x+3) := by
  simpa only [putPair,env_update0,env_update2,env0,env2,size,cons] using cons_exec (env x y s) 0 2 (by decide) ()
lemma cons10 (x y s : Data) :
    Exec (cons 1 0 (by decide)) (encodeEnv (env x y s)) (encodeEnv (env (.cons y x) .nil s)) (2*size y+3) := by
  simpa only [putPair,env_update0,env_update1,env0,env1,size,cons] using cons_exec (env x y s) 1 0 (by decide) ()
lemma split12 (x y a s : Data) :
    Exec (split 1 2 (by decide)) (encodeEnv (env x y (.cons a s))) (encodeEnv (env x a s)) (size y+2*size a+4) := by
  simpa only [putPair,env_update1,env_update2,env1,env2,size,split] using split_exec (env x y (.cons a s)) 1 2 (by decide) () a s rfl
lemma split10 (x y z s : Data) :
    Exec (split 1 0 (by decide)) (encodeEnv (env (.cons x y) z s)) (encodeEnv (env y x s)) (size z+2*size x+4) := by
  simpa only [putPair,env_update0,env_update1,env0,env1,size,split] using split_exec (env (.cons x y) z s) 1 0 (by decide) () x y rfl
lemma clear0 (x y s : Data) :
    Exec (clear 0) (encodeEnv (env x y s)) (encodeEnv (env .nil y s)) (size x+2) := by
  simpa only [env_update0,env0,size,clear] using nil_exec (env x y s) 0 ()
lemma clear1 (x y s : Data) :
    Exec (clear 1) (encodeEnv (env x y s)) (encodeEnv (env x .nil s)) (size y+2) := by
  simpa only [env_update1,env1,size,clear] using nil_exec (env x y s) 1 ()

def pair (P Q : Proc (K Reg)) : Proc (K Reg) :=
  seq (copy 0 1 (by decide)) (seq (cons 1 2 (by decide)) (seq P
    (seq (split 1 2 (by decide)) (seq (cons 0 2 (by decide))
      (seq (copy 1 0 (by decide)) (seq (clear 1) (seq Q
        (seq (split 1 2 (by decide)) (cons 1 0 (by decide))))))))))

end MatchingFPRAS.TreeFunction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeTyped
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

class Codec (A : Type) where
  encode : A → Data
export Codec (encode)
instance instCodecData : Codec Data := ⟨id⟩
instance instCodecNat : Codec ℕ := ⟨nat⟩
instance instCodecBool : Codec Bool := ⟨bit⟩
instance instCodecProd {A B : Type} [Codec A] [Codec B] : Codec (A×B) := ⟨fun x=>.cons (encode x.1) (encode x.2)⟩
instance instCodecList {A : Type} [Codec A] : Codec (List A) := ⟨fun x=>ofList (x.map encode)⟩
@[simp] lemma encode_prod {A B : Type} [Codec A] [Codec B] (a : A) (b : B) :
    encode (a,b)=.cons (encode a) (encode b) := rfl
@[simp] lemma encode_list_nil {A : Type} [Codec A] : encode ([] : List A)=.nil := rfl
@[simp] lemma encode_list_cons {A : Type} [Codec A] (a : A) (as : List A) :
    encode (a::as)=.cons (encode a) (encode as) := rfl

def Realizes {A B : Type} [Codec A] [Codec B] (P : Proc (K Reg)) (f : A → B) (t : A → ℕ) : Prop :=
  ∀ a s,Exec P (encodeEnv (env (encode a) .nil s)) (encodeEnv (env (encode (f a)) .nil s)) (t a)
structure Realizer {A B : Type} [Codec A] [Codec B] (f : A → B) where
  program : Proc (K Reg)
  cost : A → ℕ
  correct : Realizes program f cost

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def composition {f : A → B} {g : B → C} (F : Realizer f) (G : Realizer g) : Realizer (g ∘ f) :=
  ⟨seq F.program G.program,fun a=>F.cost a+G.cost (f a),fun a s=>(F.correct a s).seq (G.correct (f a) s)⟩

def pair {f : A → B} {g : A → C} (F : Realizer f) (G : Realizer g) : Realizer (fun a=>(f a,g a)) where
  program := TreeFunction.pair F.program G.program
  cost := fun a=>F.cost a+G.cost a+11*TreeFunction.size (encode a)+6*TreeFunction.size (encode (f a))+31
  correct := by
    intro a s
    have h1:=copy01 (encode a) .nil s
    have h2:=cons12 (encode a) (encode a) s
    have h3:=F.correct a (.cons (encode a) s)
    have h4:=split12 (encode (f a)) .nil (encode a) s
    have h5:=cons02 (encode (f a)) (encode a) s
    have h6:=copy10 .nil (encode a) (.cons (encode (f a)) s)
    have h7:=clear1 (encode a) (encode a) (.cons (encode (f a)) s)
    have h8:=G.correct a (.cons (encode (f a)) s)
    have h9:=split12 (encode (g a)) .nil (encode (f a)) s
    have h10:=cons10 (encode (g a)) (encode (f a)) s
    apply (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq h10))))))))).mono
    simp only [size_nil]
    omega

def identity : Realizer (id : A → A) :=
  ⟨atom .halt,fun _=>1,fun _ _=>exec_atom .halt _ _ rfl⟩

def first : Realizer (Prod.fst : A×B → A) where
  program := seq (TreeFunction.split 1 0 (by decide))
    (seq (TreeFunction.copy 1 0 (by decide)) (TreeFunction.clear 1))
  cost := fun ab=>6*TreeFunction.size (encode ab.1)+TreeFunction.size (encode ab.2)+11
  correct := by
    intro ⟨a,b⟩ s
    have h1:=split10 (encode a) (encode b) .nil s
    have h2:=copy10 (encode b) (encode a) s
    have h3:=clear1 (encode a) (encode a) s
    apply (h1.seq (h2.seq h3)).mono
    simp only [size_nil]; omega

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFunction
open TreeData TreeMachine RegisterProc

lemma split02 (x y a s : Data) :
    Exec (split 0 2 (by decide)) (encodeEnv (env x y (.cons a s)))
      (encodeEnv (env a y s)) (size x+2*size a+4) := by
  simpa only [putPair,env_update0,env_update2,env0,env2,size,split] using
    split_exec (env x y (.cons a s)) 0 2 (by decide) () a s rfl
end MatchingFPRAS.TreeFunction

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def choose {f : A → Bool} {g h : A → B} (F : Realizer f) (G : Realizer g) (H : Realizer h) :
    Realizer (fun a=>if f a then g a else h a) where
  program := seq (TreeFunction.copy 0 1 (by decide)) (seq (TreeFunction.cons 1 2 (by decide))
    (seq F.program (RegisterStructured.select 0
      (seq (TreeFunction.split 0 2 (by decide)) H.program)
      (seq (TreeFunction.split 0 2 (by decide)) G.program))))
  cost := fun a=>F.cost a+(if f a then G.cost a else H.cost a)+7*TreeFunction.size (encode a)+18
  correct := by
    intro a s
    have h1:=copy01 (encode a) .nil s
    have h2:=cons12 (encode a) (encode a) s
    have h3:=F.correct a (.cons (encode a) s)
    have h4:=split02 (encode (f a)) .nil (encode a) s
    have hs : TreeFunction.size (encode (f a)) ≤ 3 := by
      cases f a <;> simp [Codec.encode,bit]
    cases hf : f a
    · have h5:=H.correct a s
      have hh:=RegisterStructured.select_nil 0 _ (seq (TreeFunction.split 0 2 (by decide)) G.program) (env (encode (f a)) .nil (.cons (encode a) s))
        (env (encode (h a)) .nil s) _ (by simp [hf,Codec.encode,bit]) (h4.seq h5)
      simp only [hf,Bool.false_eq_true,↓reduceIte]
      apply (h1.seq (h2.seq (h3.seq hh))).mono
      simp only [hf]
      simp only [size_nil]
      rw [hf] at hs
      omega
    · have h5:=G.correct a s
      have hh:=RegisterStructured.select_cons 0 (seq (TreeFunction.split 0 2 (by decide)) H.program) _ (env (encode (f a)) .nil (.cons (encode a) s))
        (env (encode (g a)) .nil s) _ .nil .nil (by simp [hf,Codec.encode,bit]) (h4.seq h5)
      simp only [hf,↓reduceIte]
      apply (h1.seq (h2.seq (h3.seq hh))).mono
      simp only [hf]
      simp only [size_nil]
      rw [hf] at hs
      omega

def constantData (x : Data) : Realizer (fun _ : A => x) :=
  match x with
  | .nil => ⟨TreeFunction.clear 0,fun a=>TreeFunction.size (encode a)+2,fun a s=>clear0 (encode a) .nil s⟩
  | .cons x y =>
    let P : Realizer (fun _ : A => (x,y)) := pair (constantData x) (constantData y)
    ⟨P.program,P.cost,P.correct⟩

def constant (b : B) : Realizer (fun _ : A=>b) :=
  let P : Realizer (fun _ : A=>encode b) := constantData (encode b)
  ⟨P.program,P.cost,P.correct⟩
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B : Type} [Codec A] [Codec B]
namespace Fold
open RegisterControl (Instr Runs Effect)

def heads (a b r s : Data) : Env Reg := Function.update (env b r s) 3 a
end Fold

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B C : Type} [Codec A] [Codec B] [Codec C]
def Realizer.congr {f g : A → B} (F : Realizer f) (h : ∀ a,f a=g a) : Realizer g :=
  ⟨F.program,F.cost,fun a s=>by simpa only [h a] using F.correct a s⟩

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_BinarySubtract
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackSubtract
open Turing MachineCost StackAddition

def borrow (c a b : Bool) : Bool := decide (a.toNat < b.toNat+c.toNat)

def subDigits (c : Bool) (A B : List Bool) : Bool × List Bool :=
  match A,B with
  | [],[] => (c,[])
  | a::A,[] => let r:=subDigits (borrow c a false) A []; (r.1,digit c a false::r.2)
  | [],b::B => let r:=subDigits (borrow c false b) [] B; (r.1,digit c false b::r.2)
  | a::A,b::B => let r:=subDigits (borrow c a b) A B; (r.1,digit c a b::r.2)
termination_by A.length+B.length

lemma subDigits_length (A B : List Bool) (c : Bool) :
    (subDigits c A B).2.length=max A.length B.length := by
  induction A generalizing B c with
  | nil =>
    induction B generalizing c with
    | nil => simp [subDigits]
    | cons b B ih => simp [subDigits,ih]
  | cons a A ih =>
    cases B with
    | nil => simp [subDigits,ih]
    | cons b B => simp [subDigits,ih,max_add_add_right]

def program (c : Bool) : TM2.Stmt (fun _ : Fin 3=>Bool) Bool Store :=
  .pop 0 (fun v a=>(a,v.2)) (.pop 1 (fun v b=>(v.1,b))
    (.branch (fun v=>v.1.isNone && v.2.isNone)
      (.load (fun _=>default) .halt)
      (.push 2 (fun v=>digit c (v.1.getD false) (v.2.getD false))
        (.goto (fun v=>borrow c (v.1.getD false) (v.2.getD false))))))
def cfg (c : Option Bool) (A B L : List Bool) (v : Store) :
    TM2.Cfg (fun _ : Fin 3=>Bool) Bool Store := ⟨c,v,stackData A B L⟩
lemma step_empty (c : Bool) (L : List Bool) (v : Store) :
    advance (TM2.step program) (cfg (some c) [] [] L v)=cfg none [] [] L default := by
  simp [advance,TM2.step,program,TM2.stepAux,cfg,update_zero,update_one]
lemma step_digits (c : Bool) (A B L : List Bool) (v : Store) (h : A ≠ [] ∨ B ≠ []) :
    advance (TM2.step program) (cfg (some c) A B L v)=
      cfg (some (borrow c (A.headD false) (B.headD false))) A.tail B.tail
        (digit c (A.headD false) (B.headD false)::L) (A.head?,B.head?) := by
  cases A <;> cases B <;> simp_all [advance,TM2.step,program,TM2.stepAux,cfg,
    update_zero,update_one,update_two]
lemma subDigits_step (c : Bool) (A B : List Bool) (h : A ≠ [] ∨ B ≠ []) :
    (subDigits c A B).2 = digit c (A.headD false) (B.headD false)::
      (subDigits (borrow c (A.headD false) (B.headD false)) A.tail B.tail).2 := by
  cases A <;> cases B <;> simp_all [subDigits]

theorem run_subtraction (A B L : List Bool) (c : Bool) (v : Store) :
    ∃ t≤A.length+B.length+1,MachineCost.run (TM2.step program) t (cfg (some c) A B L v)=
      cfg none [] [] ((subDigits c A B).2.reverse++L) default := by
  have aux : ∀ n (A B : List Bool),A.length+B.length=n → ∀ (c : Bool) (L : List Bool) (v : Store),
      ∃ t≤A.length+B.length+1,MachineCost.run (TM2.step program) t (cfg (some c) A B L v)=
        cfg none [] [] ((subDigits c A B).2.reverse++L) default := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A B hn c L v
      by_cases he : A=[] ∧ B=[]
      · rcases he with ⟨rfl,rfl⟩
        refine ⟨1,by simp,?_⟩
        simpa only [MachineCost.run,subDigits,List.reverse_nil,List.nil_append] using step_empty c L v
      · have hne : A≠[] ∨ B≠[] := by tauto
        have hlt : A.tail.length+B.tail.length<n := by
          cases A <;> cases B <;> simp_all
          all_goals omega
        obtain ⟨t,ht,hr⟩:=ih _ hlt A.tail B.tail rfl
          (borrow c (A.headD false) (B.headD false))
          (digit c (A.headD false) (B.headD false)::L) (A.head?,B.head?)
        refine ⟨t+1,by omega,?_⟩
        rw [MachineCost.run,step_digits c A B L v hne,hr,subDigits_step c A B hne]
        simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
  exact aux _ A B rfl c L v
end MatchingFPRAS.StackSubtract

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_SubtractProc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ForwardSubtract
open Turing MachineCost StackAddition StackSubtract

local instance initialControl : Inhabited (Bool⊕Unit) := ⟨.inl false⟩
abbrev Γ := fun _ : Fin 3 => Bool
def program : Bool⊕Unit → TM2.Stmt Γ (Bool⊕Unit) Store :=
  StackComposition.sequence StackSubtract.program ForwardAddition.reverseProgram
lemma run_sub (A B : List Bool) :
    ∃ k≤2*(A.length+B.length)+2,
      MachineCost.run (TM2.step program) k ⟨some default,default,stackData A B []⟩=
        ⟨none,default,stackData ((subDigits false A B).2) [] []⟩ := by
  obtain ⟨n,hn,he⟩:=run_subtraction A B [] false default
  have he' : MachineCost.run (TM2.step StackSubtract.program) n
      (StackSubtract.cfg (some false) A B [] default)=StackSubtract.cfg none [] [] ((subDigits false A B).2).reverse default := by
    simpa only [List.append_nil] using he
  have hr := ForwardAddition.run_reverse [] [] ((subDigits false A B).2).reverse default
  have hr' : MachineCost.run (TM2.step ForwardAddition.reverseProgram) (((subDigits false A B).2).length+1)
      ⟨some default,default,stackData [] [] ((subDigits false A B).2).reverse⟩=
      ⟨none,default,stackData ((subDigits false A B).2) [] []⟩ := by
    simpa only [ForwardAddition.rcfg,List.length_reverse,List.reverse_reverse,List.append_nil] using hr
  obtain ⟨k,hk,hkrun⟩:=StackComposition.sequence_run StackSubtract.program ForwardAddition.reverseProgram
    (StackSubtract.cfg (some false) A B [] default) n (((subDigits false A B).2).length+1)
    (default : Store) (default : Store) (stackData [] [] ((subDigits false A B).2).reverse)
      (stackData ((subDigits false A B).2) [] []) he' hr'
  refine ⟨k,?_,?_⟩
  · have hl:=subDigits_length A B false
    omega
  · exact hkrun
end MatchingFPRAS.ForwardSubtract

namespace MatchingFPRAS.BinaryArithmeticProc
open RegisterProc Turing

local instance subEntry : Inhabited (Bool⊕Unit) := ⟨.inl false⟩
def sub : Proc (Fin 3) := FiniteStore.procedure ForwardSubtract.program (default : StackAddition.Store)
lemma sub_exec (A B : List Bool) :
    Exec sub ![A,B,[]] ![(StackSubtract.subDigits false A B).2,[],[]] (2*(A.length+B.length)+2) := by
  obtain ⟨n,hn,he⟩:=ForwardSubtract.run_sub A B
  exact (FiniteStore.exec ForwardSubtract.program default default _ _ n he).mono hn
end MatchingFPRAS.BinaryArithmeticProc

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeFraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

abbrev Fraction := ℕ×ℕ

def normalize (x : Fraction) : Fraction :=
  if x.2=0 then (0,1) else (x.1/(x.1.gcd x.2),x.2/(x.1.gcd x.2))

def mul (x : Fraction×Fraction) : Fraction := normalize (x.1.1*x.2.1,x.1.2*x.2.2)

def add (x : Fraction×Fraction) : Fraction :=
  normalize (x.1.1*x.2.2+x.2.1*x.1.2,x.1.2*x.2.2)

def div (x : Fraction×Fraction) : Fraction := normalize (x.1.1*x.2.2,x.1.2*x.2.1)

end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableScaling
open TreeTyped TreeFraction Polynomial

abbrev Vector := List (ℕ×Fraction)
end MatchingFPRAS.ExecutableScaling

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeFractionExtra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped Polynomial

def product (xs : List Fraction) : Fraction := xs.foldl (fun a b=>mul (b,a)) (1,1)
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeSlotWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

def fuelPower (x : Fraction×List Bool) : Fraction := product (x.2.map (fun _=>x.1))
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped Polynomial Enlargement RealGeometry

abbrev RawLogical := ℕ×ℕ
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeAdaptiveArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableAdaptive
open TreeTyped TreeFraction ExecutableScaling

abbrev ProbeTable := List ((ℕ×ℕ)×Fraction)
abbrev MatrixData := (ℕ×Fraction)×ProbeTable

def orderedPair (x : ℕ×ℕ) : ℕ×ℕ := if x.1<x.2 then x else (x.2,x.1)
end MatchingFPRAS.ExecutableAdaptive

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeStageActivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableAdaptive
open TreeTyped TreeFraction ExecutableScaling ExecutableSource

abbrev GraphData := List ℕ×List RawLogical
abbrev ActivityData := (GraphData×List Bool)×Vector
abbrev CellData := (List RawLogical×Fraction)×Vector

def cooling (n : ℕ) : Fraction := div ((1,1),add ((1,1),div ((1,1),(n,1))))

def cellData (x : ActivityData) : CellData :=
  ((x.1.1.2,fuelPower (cooling x.1.1.1.length,x.1.2)),x.2)
end MatchingFPRAS.ExecutableAdaptive

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_PhysicalPost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing

variable {Γ Q R : Type} [Inhabited Γ]

structure Cfg (Γ Q : Type) [Inhabited Γ] where
  state : Option Q
  tape : Tape Γ

abbrev Table (Γ Q : Type) := Q → Γ → Bool → Option (Q × TM0.Stmt Γ)

end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_CoinTM1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.CoinTM1
open Turing MachineCost

variable {Γ Λ σ : Type} [Inhabited Γ]

abbrev Node (Γ Λ σ : Type) := Λ ⊕ TM1.Stmt Γ Λ σ
abbrev State (Γ Λ σ : Type) := Node Γ Λ σ × σ
abbrev Coins (Λ : Type) := Λ → Option (Bool → Λ)

def aux (a : Γ) : TM1.Stmt Γ Λ σ → σ → Option (State Γ Λ σ × TM0.Stmt Γ)
  | .move d q,v => some ((.inr q,v),.move d)
  | .write f q,v => some ((.inr q,v),.write (f a v))
  | .load f q,v => aux a q (f a v)
  | .branch f q r,v => if f a v then aux a q v else aux a r v
  | .goto f,v => some ((.inl (f a v),v),.write a)
  | .halt,_ => none

def table (M : Λ → TM1.Stmt Γ Λ σ) (coin : Coins Λ) : PhysicalPost.Table Γ (State Γ Λ σ)
  | (.inl l,v),a,b => match coin l with
    | none => aux a (M l) v
    | some f => some ((.inl (f b),v),.write a)
  | (.inr q,v),a,_ => aux a q v

def pending (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) : PhysicalPost.Cfg Γ (State Γ Λ σ) :=
  ⟨some (.inr q,v),T⟩

def trCfg (c : TM1.Cfg Γ Λ σ) : PhysicalPost.Cfg Γ (State Γ Λ σ) :=
  ⟨c.l.map (fun l=>(Sum.inl l,c.var)),c.Tape⟩

end MatchingFPRAS.CoinTM1

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_PhysicalRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing

variable {Γ Q : Type} [Inhabited Γ]

def Supported (M : Table Γ Q) (S : Finset Q) : Prop :=
  ∀ q ∈ S, ∀ a b q' act,M q a b=some (q',act) → q'∈S

end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_CoinTM1Finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.CoinTM1
open Turing
open scoped Classical

variable {Γ Λ σ : Type} [Inhabited Λ] [Fintype σ]

noncomputable def nodes (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) : Finset (Node Γ Λ σ) :=
  S.disjSum (S.biUnion (fun l=>TM1.stmts₁ (M l)))
noncomputable def states (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) : Finset (State Γ Λ σ) :=
  (nodes M S) ×ˢ Finset.univ

omit [Inhabited Λ] [Fintype σ] in
lemma node_entry {M : Λ → TM1.Stmt Γ Λ σ} {S : Finset Λ} {l : Λ} (h : l∈S) :
    Sum.inl l∈nodes M S := by simp only [nodes,Finset.inl_mem_disjSum]; exact h
omit [Inhabited Λ] [Fintype σ] in
lemma node_pending {M : Λ → TM1.Stmt Γ Λ σ} {S : Finset Λ} {q : TM1.Stmt Γ Λ σ}
    (h : some q∈TM1.stmts M S) : Sum.inr q∈nodes M S := by
  simpa only [nodes,Finset.inr_mem_disjSum,TM1.stmts,Finset.some_mem_insertNone] using h
omit [Inhabited Λ] in
lemma state_mem {M : Λ → TM1.Stmt Γ Λ σ} {S : Finset Λ} {q : Node Γ Λ σ} {v : σ}
    (h : q∈nodes M S) : (q,v)∈states M S := by
  simp only [states,Finset.mem_product,Finset.mem_univ,and_true]; exact h

lemma aux_supported {M : Λ → TM1.Stmt Γ Λ σ} {S : Finset Λ}
    (hs : TM1.Supports M S) (a : Γ) (q : TM1.Stmt Γ Λ σ)
    (hq : some q∈TM1.stmts M S) (v : σ) (q' : State Γ Λ σ) (act : TM0.Stmt Γ)
    (he : aux a q v=some (q',act)) : q'∈states M S := by
  classical
  induction q generalizing v q' act with
  | move d q ih =>
    simp only [aux,Option.some.injEq,Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    apply state_mem
    apply node_pending
    exact TM1.stmts_trans (by simp only [TM1.stmts₁,Finset.mem_insert]; exact Or.inr TM1.stmts₁_self) hq
  | write f q ih =>
    simp only [aux,Option.some.injEq,Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    apply state_mem
    apply node_pending
    exact TM1.stmts_trans (by simp only [TM1.stmts₁,Finset.mem_insert]; exact Or.inr TM1.stmts₁_self) hq
  | load f q ih =>
    exact ih (TM1.stmts_trans (by simp only [TM1.stmts₁,Finset.mem_insert]; exact Or.inr TM1.stmts₁_self) hq) _ _ _ he
  | branch f q r ihq ihr =>
    simp only [aux] at he
    split_ifs at he with hf
    · exact ihq (TM1.stmts_trans (by simp only [TM1.stmts₁,Finset.mem_insert,Finset.mem_union]; exact Or.inr (Or.inl TM1.stmts₁_self)) hq) _ _ _ he
    · exact ihr (TM1.stmts_trans (by simp only [TM1.stmts₁,Finset.mem_insert,Finset.mem_union]; exact Or.inr (Or.inr TM1.stmts₁_self)) hq) _ _ _ he
  | goto f =>
    simp only [aux,Option.some.injEq,Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    exact state_mem (node_entry (TM1.stmts_supportsStmt hs hq a v))
  | halt => simp [aux] at he

theorem table_supported (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hs : TM1.Supports M S)
    (coin : Coins Λ) (hc : ∀ l∈S,∀ f,coin l=some f→∀ b,f b∈S) :
    PhysicalPost.Supported (table M coin) (states M S) := by
  intro q hq a b q' act he
  have hn : q.1∈nodes M S := (Finset.mem_product.mp hq).1
  rcases q with ⟨l,v⟩
  cases l with
  | inl l =>
    have hl : l∈S := by simpa only [nodes,Finset.inl_mem_disjSum] using hn
    simp only [table] at he
    split at he
    · apply aux_supported hs a (M l) _ v q' act he
      simp only [TM1.stmts,Finset.some_mem_insertNone,Finset.mem_biUnion]
      exact ⟨l,hl,TM1.stmts₁_self⟩
    · rename_i f hf
      simp only [Option.some.injEq,Prod.mk.injEq] at he
      rcases he with ⟨rfl,rfl⟩
      exact state_mem (node_entry (hc l hl f hf b))
  | inr q =>
    apply aux_supported hs a q _ v q' act he
    simpa only [nodes,Finset.inr_mem_disjSum,TM1.stmts,Finset.some_mem_insertNone] using hn

end MatchingFPRAS.CoinTM1

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_CoinAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.CoinAlphabet
open Turing TM1 TM1to1 MachineCost

variable {Γ Λ σ : Type} [Inhabited Γ]
def safe (p : Λ → Prop) : Λ' Γ Λ σ → Prop
  | .normal l => p l
  | .write _ _ => True

def coins (c : CoinTM1.Coins Λ) : CoinTM1.Coins (Λ' Γ Λ σ)
  | .normal l => (c l).map (fun f b=>.normal (f b))
  | .write _ _ => none

end MatchingFPRAS.CoinAlphabet

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_CoinStack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.CoinStack
open Turing TM2to1 TM2to1.Λ' MachineCost

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]

def safe (p : Λ → Prop) : Λ' K Γ Λ σ → Prop
  | .normal l => p l
  | .go _ _ _ | .ret _ => True

def coins (c : CoinTM1.Coins Λ) : CoinTM1.Coins (Λ' K Γ Λ σ)
  | .normal l => (c l).map (fun f b=>.normal (f b))
  | .go _ _ _ | .ret _ => none

end MatchingFPRAS.CoinStack

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_CoinSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.CoinAlphabet
open Turing
open scoped Classical

variable {Γ Λ σ : Type} [Inhabited Γ] [Fintype Γ]
omit [Inhabited Γ] in
lemma normal_not_writes (l : Λ) (q : TM1.Stmt Γ Λ σ) : TM1to1.Λ'.normal l∉TM1to1.writes q := by
  induction q <;> simp_all [TM1to1.writes]
omit [Inhabited Γ] in
lemma normal_mem (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (l : Λ) :
    TM1to1.Λ'.normal l∈TM1to1.trSupp M S ↔ l∈S := by
  simp only [TM1to1.trSupp,Finset.mem_biUnion,Finset.mem_insert,TM1to1.Λ'.normal.injEq,
    normal_not_writes,or_false]
  constructor
  · rintro ⟨l',hl',rfl⟩; exact hl'
  · intro hl; exact ⟨l,hl,rfl⟩
omit [Inhabited Γ] in
lemma coins_supported (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (c : CoinTM1.Coins Λ)
    (hc : ∀ l∈S,∀ f,c l=some f→∀ b,f b∈S) :
    ∀ l∈TM1to1.trSupp M S,∀ f,coins c l=some f→∀ b,f b∈TM1to1.trSupp M S := by
  intro l hl f hf b
  cases l with
  | normal l =>
    have hl':= (normal_mem M S l).mp hl
    simp only [coins,Option.map_eq_some_iff] at hf
    obtain ⟨g,hg,rfl⟩:=hf
    exact (normal_mem M S (g b)).mpr (hc l hl' g hg b)
  | write a q => simp [coins] at hf
end MatchingFPRAS.CoinAlphabet

namespace MatchingFPRAS.CoinStack
open Turing TM2to1
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]
omit [DecidableEq K] in
lemma normal_not_internal (l : Λ) (q : TM2.Stmt Γ Λ σ) : Λ'.normal l∉trStmts₁ q := by
  induction q using stmtStRec with
  | run k o q ih => simp_all [trStmts₁_run]
  | load f q ih => exact ih
  | branch f q r ihq ihr => simp_all [trStmts₁]
  | goto f => simp [trStmts₁]
  | halt => simp [trStmts₁]
omit [DecidableEq K] in
lemma normal_mem (M : Λ → TM2.Stmt Γ Λ σ) (S : Finset Λ) (l : Λ) :
    Λ'.normal l∈trSupp M S ↔ l∈S := by
  simp only [trSupp,Finset.mem_biUnion,Finset.mem_insert,Λ'.normal.injEq,
    normal_not_internal,or_false]
  constructor
  · rintro ⟨l',hl',rfl⟩; exact hl'
  · intro hl; exact ⟨l,hl,rfl⟩
omit [DecidableEq K] in
lemma coins_supported (M : Λ → TM2.Stmt Γ Λ σ) (S : Finset Λ) (c : CoinTM1.Coins Λ)
    (hc : ∀ l∈S,∀ f,c l=some f→∀ b,f b∈S) :
    ∀ l∈trSupp M S,∀ f,coins c l=some f→∀ b,f b∈trSupp M S := by
  intro l hl f hf b
  cases l with
  | normal l =>
    have hl':= (normal_mem M S l).mp hl
    simp only [coins,Option.map_eq_some_iff] at hf
    obtain ⟨g,hg,rfl⟩:=hf
    exact (normal_mem M S (g b)).mpr (hc l hl' g hg b)
  | go k o q => simp [coins] at hf
  | ret q => simp [coins] at hf
end MatchingFPRAS.CoinStack

end OAI
end


