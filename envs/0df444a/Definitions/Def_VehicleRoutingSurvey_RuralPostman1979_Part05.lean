-- Prove2me | Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part05
-- name    : VehicleRoutingSurvey_RuralPostman1979_Part05
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T14:03:39.987324+00:00
-- url     : https://prove2.me/theorems/2f7b52a3-291e-4e07-a6b1-67817599e130
-- title:
--   Rural postman algorithm — Connector-tree construction and Euler adjacency lists
-- statement:
--   This module supplies the Lean definitions and checked auxiliary results for connector-tree construction and Euler adjacency lists in the Table 3 proof. It uses the mission’s rural-run and arithmetic-RAM model.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.Forall2
import Mathlib.Tactic.Ring
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part01
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part02
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part03
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part04

/-! runtime/PrimRound.lean -/
section RppSource_PrimRound
namespace VehicleRoutingSurvey.Routing

structure PrimLayout (n : ℕ) where
  rows : ℕ
  matrix : ℕ
  labels : ℕ
  support : ℕ
  visits : ℕ
  mask : ℕ
  output : ℕ
  rowsBelowLabels : rows + n ≤ labels
  labelsBelowSupport : labels + n ≤ support
  supportBelowVisits : support + n ≤ visits
  visitsBelowMask : visits + n ≤ mask
  maskBelowOutput : mask + n ^ 2 ≤ output

structure PrimRoundFrame (I : Service) (layout : PrimLayout I.graph.n)
    (required seen : Fin I.graph.n → Bool) (cut : Finset (RequiredComponent I))
    (pairs : List (PrimPair I)) (s : ArithmeticState) : Prop where
  mask : PrimMaskFrame I.graph.n layout.rows layout.matrix layout.support layout.visits
    layout.mask required seen s
  labelBase : s.nr 24 = layout.labels
  zero : s.nr 33 = 0
  labels : ∀ u v : Fin I.graph.n, s.nm (layout.labels + u.val) = s.nm (layout.labels + v.val) ↔
    sameComponent I u v
  supported : ∀ v, required v = true ↔ v ∈ requiredVertices I
  selected : ∀ v, seen v = true ↔ v ∈ requiredVertices I ∧ requiredComponent I v ∈ cut
  output : PrimPairOutputFrame I layout.output pairs s
  distances : ∀ p : PrimPair I, s.rm (layout.matrix + primPairOffset p) = distance I.graph p.1 p.2
  sentinel : ∀ p : PrimPair I, distance I.graph p.1 p.2 < s.rm (layout.matrix + I.graph.n ^ 2)

def primRoundBlock : List ArithmeticInstruction :=
  appendBlock primSelectAcrossCutBlock (branchOnUnequal 12 44 commitPrimOffsetBlock)

private theorem PrimMaskFrame.controlOnly {n rows matrix support visits mask : ℕ}
    {required seen : Fin n → Bool} {s t : ArithmeticState}
    (frame : PrimMaskFrame n rows matrix support visits mask required seen s)
    (registers : t.nr = s.nr) (memory : t.nm = s.nm) :
    PrimMaskFrame n rows matrix support visits mask required seen t :=
  ⟨frame.floyd.preserved (fun r _ _ => congrFun registers r) memory,
    (congrFun registers 40).trans frame.supportBase, (congrFun registers 41).trans frame.visitedBase,
    (congrFun registers 42).trans frame.maskBase, frame.supportBeforeMask, frame.visitsBeforeMask,
    frame.rowsBeforeMask, fun v => (congrFun memory _).trans (frame.supportBit v),
    fun v => (congrFun memory _).trans (frame.visitedBit v)⟩

private theorem PrimRoundFrame.controlOnly {I : Service} {layout : PrimLayout I.graph.n}
    {required seen : Fin I.graph.n → Bool} {cut : Finset (RequiredComponent I)} {pairs : List (PrimPair I)}
    {s t : ArithmeticState} (frame : PrimRoundFrame I layout required seen cut pairs s)
    (registers : t.nr = s.nr) (natural : t.nm = s.nm) (real : t.rm = s.rm) :
    PrimRoundFrame I layout required seen cut pairs t :=
  ⟨frame.mask.controlOnly registers natural, (congrFun registers 24).trans frame.labelBase,
    (congrFun registers 33).trans frame.zero, by rw [natural]; exact frame.labels,
    frame.supported, frame.selected,
    ⟨(congrFun registers 43).trans frame.output.baseAt, (congrFun registers 38).trans frame.output.cursor,
      (congrFun registers 39).trans frame.output.length, by rw [natural]; exact frame.output.words⟩,
    by rw [real]; exact frame.distances, by rw [real]; exact frame.sentinel⟩

structure PrimRoundResult (I : Service) (layout : PrimLayout I.graph.n) (root : Fin I.graph.n)
    (required : Fin I.graph.n → Bool) (cut : Finset (RequiredComponent I)) (initial : ArithmeticState)
    (nextCut : Finset (RequiredComponent I)) (nextPairs : List (PrimPair I)) (nextSeen : Fin I.graph.n → Bool)
    (steps : ℕ) (s : ArithmeticState) : Prop where
  run : BlockRuns primRoundBlock steps initial s
  bound : steps ≤ 28 * I.graph.n ^ 2 + 22 * I.graph.n + 34
  running : s.halted = false
  frame : PrimRoundFrame I layout required nextSeen nextCut nextPairs s
  prefixValid : PrimPrefix I root nextCut nextPairs
  progress : nextCut = activeRequiredComponents I ∨ nextCut.card = cut.card + 1
  loopIndex : s.nr 32 = initial.nr 32
  pathsBase : s.nr 26 = initial.nr 26
  realMemory : s.rm = initial.rm
  previousNatural : ∀ k < layout.labels, s.nm k = initial.nm k

/-- One round selects the cheapest crossing pair, appends it, and marks
the new component. Once all components are reached it only tests the cut. -/
theorem primRoundBlock_correct {I : Service} {layout : PrimLayout I.graph.n} {root : Fin I.graph.n}
    {required seen : Fin I.graph.n → Bool} {cut : Finset (RequiredComponent I)} {pairs : List (PrimPair I)}
    {s : ArithmeticState} (state : PrimRoundFrame I layout required seen cut pairs s)
    (current : PrimPrefix I root cut pairs) (undirected : Undirected I.graph)
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ (nextCut : Finset (RequiredComponent I)) (nextPairs : List (PrimPair I))
      (nextSeen : Fin I.graph.n → Bool) (steps : ℕ) (t : ArithmeticState),
      PrimRoundResult I layout root required cut s nextCut nextPairs nextSeen steps t := by
  classical
  let n := I.graph.n
  have labelsBeforeVisits : layout.labels + n ≤ layout.visits :=
    layout.labelsBelowSupport.trans ((Nat.le_add_right _ _).trans layout.supportBelowVisits)
  have visitsBeforeOutput : layout.visits + n ≤ layout.output :=
    layout.visitsBelowMask.trans ((Nat.le_add_right _ _).trans layout.maskBelowOutput)
  have labelsBeforeMask : layout.labels + n ≤ layout.mask :=
    labelsBeforeVisits.trans ((Nat.le_add_right _ _).trans layout.visitsBelowMask)
  obtain ⟨selected, selectRun, selectReady, foundMask, zero, limit, real, fixed, natural, choice⟩ :=
    primSelectAcrossCutBlock_correct current state.mask entry running state.supported state.selected
      state.distances state.sentinel
  let ready := {selected with pc := 0}
  have beforeMask (k : ℕ) (below : k < layout.mask) : selected.nm k = s.nm k :=
    natural k (fun within => (not_le.mpr below) within.1)
  have afterMask (k : ℕ) (above : layout.output ≤ k) : selected.nm k = s.nm k :=
    natural k (fun within => (not_lt.mpr (layout.maskBelowOutput.trans above)) within.2)
  have safeLabels (u : Fin n) : layout.labels + u.val < layout.mask :=
    (Nat.add_lt_add_left u.isLt _).trans_le labelsBeforeMask
  have selectedLabels (u v : Fin n) :
      selected.nm (layout.labels + u.val) = selected.nm (layout.labels + v.val) ↔ sameComponent I u v := by
    rw [beforeMask _ (safeLabels u), beforeMask _ (safeLabels v)]
    exact state.labels u v
  have selectedOutput : PrimPairOutputFrame I layout.output pairs selected :=
    ⟨(fixed 43 (by decide) (by decide)).trans state.output.baseAt,
      (fixed 38 (by decide) (by decide)).trans state.output.cursor,
      (fixed 39 (by decide) (by decide)).trans state.output.length, fun i =>
        ⟨(afterMask _ (by omega)).trans (state.output.words i).1,
          (afterMask _ (by omega)).trans (state.output.words i).2⟩⟩
  have selectedFrame : PrimRoundFrame I layout required seen cut pairs selected :=
    ⟨foundMask, (fixed 24 (by decide) (by decide)).trans state.labelBase, zero, selectedLabels,
      state.supported, state.selected, selectedOutput,
      by rw [real]; exact state.distances, by rw [real]; exact state.sentinel⟩
  have readyFrame : PrimRoundFrame I layout required seen cut pairs ready :=
    selectedFrame.controlOnly rfl rfl rfl
  rcases choice with ⟨missing, finished⟩ | ⟨p, chosen, eligible, least⟩
  · have skip : ready.nr 12 = ready.nr 44 := missing.trans limit.symm
    have stopped := branchOnUnequal_skip 12 44 commitPrimOffsetBlock ready rfl selectReady skip
    let t := relocateState primSelectAcrossCutBlock.length
      {ready with pc := (branchOnUnequal 12 44 commitPrimOffsetBlock).length}
    have obtains : PrimRoundFrame I layout required seen cut pairs t :=
      readyFrame.controlOnly rfl rfl rfl
    refine ⟨cut, pairs, seen, _, t, ⟨by simpa only [primRoundBlock] using selectRun.append stopped,
      by omega, selectReady, obtains,
      current, Or.inl finished, fixed 32 (by decide) (by decide), fixed 26 (by decide) (by decide), real,
      fun k below => beforeMask k (below.trans_le ((Nat.le_add_right _ _).trans labelsBeforeMask))⟩⟩
  · have available : ready.nr 12 ≠ ready.nr 44 := by
      change selected.nr 12 ≠ selected.nr 44
      rw [chosen, limit]
      exact Nat.ne_of_lt (primPairOffset_lt p)
    obtain ⟨commit, commitRun, commitReady, appended, commitReal, _, stable, outsideVisits, mark⟩ :=
      commitPrimOffsetBlock_correct readyFrame.output rfl selectReady readyFrame.mask.floyd.dimension
        readyFrame.mask.floyd.one readyFrame.zero readyFrame.labelBase readyFrame.mask.visitedBase
        labelsBeforeVisits visitsBeforeOutput p chosen
    have commits := branchOnUnequal_take 12 44 commitPrimOffsetBlock (s := ready) (t := commit)
      rfl selectReady available commitRun
    let t := relocateState primSelectAcrossCutBlock.length (relocateState 3 commit)
    let nextCut := insert (requiredComponent I p.2) cut
    let nextSeen (v : Fin n) : Bool := decide (v ∈ requiredVertices I ∧ requiredComponent I v ∈ nextCut)
    have nextModel : PrimPrefix I root nextCut (pairs ++ [p]) :=
      current.append undirected p eligible least
    have notVisited : requiredComponent I p.2 ∉ cut := eligible.2.2.2
    have outsideLow (k : ℕ) (hk : k < layout.visits) : t.nm k = selected.nm k :=
      outsideVisits k (hk.trans_le ((Nat.le_add_right _ _).trans visitsBeforeOutput))
        (fun inside => (not_le.mpr hk) inside.1)
    have unchangedLabels (w : Fin n) : t.nm (layout.labels + w.val) = selected.nm (layout.labels + w.val) :=
      outsideLow _ ((Nat.add_lt_add_left w.isLt _).trans_le labelsBeforeVisits)
    have seenAsFlag (v : Fin n) : seen v = true ↔
        v ∈ requiredVertices I ∧ requiredComponent I v ∈ cut := state.selected v
    have oldFlags (v : Fin n) : selected.nm (layout.visits + v.val) =
        if v ∈ requiredVertices I ∧ requiredComponent I v ∈ cut then 1 else 0 := by
      rw [foundMask.visitedBit]
      change (if seen v = true then 1 else 0) = _
      simp only [seenAsFlag]
    have marked (w : Fin n) : t.nm (layout.visits + w.val) = if nextSeen w then 1 else 0 := by
      have bit := markPrimComponent_flag cut (fun u => selected.nm (layout.labels + u.val))
        (fun u => selected.nm (layout.visits + u.val)) selectedLabels oldFlags p.2 eligible.2.1 w
      change commit.nm _ = _
      rw [mark]
      simpa [nextSeen, nextCut] using bit
    have withinFrame : FloydFrame n layout.rows layout.matrix t :=
      ⟨(stable 3 (by decide) (by decide) (by decide) (by decide)).trans foundMask.floyd.tableBase,
        (stable 4 (by decide) (by decide) (by decide) (by decide)).trans foundMask.floyd.matrixBase,
        (stable 5 (by decide) (by decide) (by decide) (by decide)).trans foundMask.floyd.dimension,
        (stable 6 (by decide) (by decide) (by decide) (by decide)).trans foundMask.floyd.one,
        fun i hi => (outsideLow _ ((Nat.add_lt_add_left hi _).trans_le
          (layout.rowsBelowLabels.trans ((Nat.le_add_right _ _).trans labelsBeforeVisits)))).trans
          (foundMask.floyd.rows i hi)⟩
    have nextMask : PrimMaskFrame n layout.rows layout.matrix layout.support layout.visits layout.mask
        required nextSeen t :=
      ⟨withinFrame, (stable 40 (by decide) (by decide) (by decide) (by decide)).trans foundMask.supportBase,
        (stable 41 (by decide) (by decide) (by decide) (by decide)).trans foundMask.visitedBase,
        (stable 42 (by decide) (by decide) (by decide) (by decide)).trans foundMask.maskBase,
        foundMask.supportBeforeMask, foundMask.visitsBeforeMask, foundMask.rowsBeforeMask, fun v =>
          (outsideLow _ ((Nat.add_lt_add_left v.isLt _).trans_le layout.supportBelowVisits)).trans
            (foundMask.supportBit v), marked⟩
    have totalReal : t.rm = s.rm := commitReal.trans real
    have actualOutput : PrimPairOutputFrame I layout.output (pairs ++ [p]) t :=
      ⟨appended.baseAt, appended.cursor, appended.length, appended.words⟩
    have nextFrame : PrimRoundFrame I layout required nextSeen nextCut (pairs ++ [p]) t :=
      ⟨nextMask, (stable 24 (by decide) (by decide) (by decide) (by decide)).trans selectedFrame.labelBase,
        (stable 33 (by decide) (by decide) (by decide) (by decide)).trans zero,
        fun u v => by rw [unchangedLabels u, unchangedLabels v]; exact selectedLabels u v,
        state.supported, fun v => by simp [nextSeen], actualOutput,
        by rw [totalReal]; exact state.distances, by rw [totalReal]; exact state.sentinel⟩
    refine ⟨nextCut, pairs ++ [p], nextSeen, _, t,
      ⟨by simpa only [primRoundBlock] using selectRun.append commits, by omega, commitReady,
      nextFrame, nextModel, Or.inr (Finset.card_insert_of_notMem notVisited),
      (stable 32 (by decide) (by decide) (by decide) (by decide)).trans (fixed 32 (by decide) (by decide)),
      (stable 26 (by decide) (by decide) (by decide) (by decide)).trans (fixed 26 (by decide) (by decide)),
      totalReal, ?_⟩⟩
    intro k below
    exact (outsideLow _ (below.trans_le ((Nat.le_add_right _ _).trans labelsBeforeVisits))).trans
      (beforeMask k (below.trans_le ((Nat.le_add_right _ _).trans labelsBeforeMask)))

end VehicleRoutingSurvey.Routing
end RppSource_PrimRound

/-! runtime/PrimInitialization.lean -/
section RppSource_PrimInitialization
namespace VehicleRoutingSurvey.Routing

def adjacentPrimLayout (n rows matrix labels : ℕ) (fits : rows + n ≤ labels) : PrimLayout n :=
  let support := labels + n
  let visits := support + n
  let mask := visits + n
  ⟨rows, matrix, labels, support, visits, mask, mask + n ^ 2, fits, le_rfl, le_rfl, le_rfl, le_rfl⟩

private def configurePrimArrays : List ArithmeticInstruction :=
  [.natAdd 40 24 5, .natAdd 41 40 5, .natAdd 42 41 5,
    .natSub 44 5 6, .natAdd 44 3 44, .natLoad 44 44, .natAdd 44 44 5, .natAdd 43 42 44,
    .natLoad 8 6, .natConst 9 2, .natAdd 45 5 33, .realConst 0 1, .natAdd 51 4 44,
    .natSub 26 37 44, .natAdd 37 40 33, .natAdd 23 5 5]

private def configurePrimState (s : ArithmeticState) : ArithmeticState :=
  let n := s.nr 5
  let support := s.nr 24 + n
  let visits := support + n
  let mask := visits + n
  let cells := s.nm (s.nr 3 + (n - s.nr 6)) + n
  let nr := Function.update (Function.update (Function.update s.nr 40 support) 41 visits) 42 mask
  let nr := Function.update (Function.update nr 44 cells) 43 (mask + cells)
  let nr := Function.update (Function.update (Function.update nr 8 (s.nm (s.nr 6))) 9 2) 45 (n + s.nr 33)
  let nr := Function.update (Function.update nr 51 (s.nr 4 + cells)) 26 (s.nr 37 - cells)
  let nr := Function.update (Function.update nr 37 (support + s.nr 33)) 23 (n + n)
  {s with pc := 16, nr := nr, rr := Function.update s.rr 0 1}

private theorem configurePrimArrays_runs {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) : BlockRuns configurePrimArrays 16 s (configurePrimState s) := by
  refine ⟨?_, ?_, rfl⟩
  · have position (i : ℕ) (hi : i ≤ 16) :
        ((arithmeticStep configurePrimArrays)^[i] s).pc = i ∧
          ((arithmeticStep configurePrimArrays)^[i] s).halted = false := by
      induction i with
      | zero => exact ⟨entry, running⟩
      | succ i ih =>
        have below : i < 16 := by omega
        have previous := ih below.le
        rw [Function.iterate_succ_apply']
        simp only [arithmeticStep, previous.1, previous.2, Bool.false_eq_true, ↓reduceIte]
        interval_cases i <;> exact ⟨rfl, rfl⟩
    intro i hi
    change ((arithmeticStep configurePrimArrays)^[i] s).pc < 16
    rwa [(position i (by omega)).1]
  · simp [configurePrimState, configurePrimArrays, arithmeticStep, entry, running,
      Function.iterate_succ_apply', Function.update_idem]

private def retainPrimSentinel : List ArithmeticInstruction :=
  [.realStore 51 0, .natAdd 38 43 33, .natConst 39 0]

def initializePrimArraysBlock : List ArithmeticInstruction :=
  appendBlock configurePrimArrays
    (appendBlock clearRequiredBitsBlock (appendBlock apspWeightBlock retainPrimSentinel))

structure PrimArraySeed (I : Service) (layout : PrimLayout I.graph.n) (next : ℕ)
    (initial final : ArithmeticState) : Prop where
  frame : PrimSupportFrame I layout.rows layout.matrix layout.support final
  running : final.halted = false
  nextBase : final.nr 26 = next
  labelBase : final.nr 24 = layout.labels
  visitedBase : final.nr 41 = layout.visits
  maskBase : final.nr 42 = layout.mask
  cursor : final.nr 9 = 2
  noRoot : final.nr 45 = I.graph.n
  output : PrimPairOutputFrame I layout.output [] final
  supportZeros : ∀ u : Fin I.graph.n, final.nm (layout.support + u.val) = 0
  visitedZeros : ∀ u : Fin I.graph.n, final.nm (layout.visits + u.val) = 0
  beforeSupport : ∀ k < layout.support, final.nm k = initial.nm k
  real : final.rm = Function.update initial.rm (layout.matrix + I.graph.n ^ 2)
    (1 + (ruralRealInput I).sum)

/-- Lay out Prim's arrays, clear support and visited flags, and reserve a
real sentinel obtained from a single raw-weight scan. -/
theorem initializePrimArraysBlock_correct {I : Service} {rows matrix labels next : ℕ}
    {s : ArithmeticState} (frame : FloydFrame I.graph.n rows matrix s)
    (positive : 0 < I.graph.n) (entry : s.pc = 0) (running : s.halted = false)
    (labelBase : s.nr 24 = labels) (oldBits : s.nr 37 = next + I.graph.n ^ 2) (zero : s.nr 33 = 0)
    (rowsFit : rows + I.graph.n ≤ labels) (inputFit : 2 + 3 * I.graph.q ≤ labels)
    (naturalInput : ∀ k < 2 + 3 * I.graph.q, s.nm k = (ruralNatInput I)[k]?.getD 0)
    (weightInput : ∀ e : Fin I.graph.q, s.rm e.val = I.graph.weight e) :
    let layout := adjacentPrimLayout I.graph.n rows matrix labels rowsFit
    ∃ t, BlockRuns initializePrimArraysBlock (10 * I.graph.n + 5 * I.graph.q + 23) s t ∧
      PrimArraySeed I layout next s t := by
  intro layout
  let n := I.graph.n
  let configured := configurePrimState s
  let clearing := {configured with pc := 0}
  have last : n - 1 < n := by omega
  have successor : (n - 1).succ = n := by omega
  have cells : s.nm (s.nr 3 + (n - 1)) + n = n ^ 2 := by
    rw [frame.tableBase, frame.rows _ last, pow_two, ← Nat.mul_succ, successor]
  have qAt : s.nm 1 = I.graph.q := by
    rw [naturalInput _ (by omega)]
    simp [ruralNatInput]
  have one : clearing.nr 6 = 1 := frame.one
  have reserve : clearing.nr 37 = layout.support := by
    simp [clearing, configured, configurePrimState, frame.dimension, labelBase, zero, layout, adjacentPrimLayout]
  have count : clearing.nr 23 = 2 * n := by
    simp [clearing, configured, configurePrimState, frame.dimension, n, two_mul]
  obtain ⟨cleared, clear, ready, fixed, clearRm, clearRr, clearNm⟩ :=
    clearRequiredBitsBlock_correct (s := clearing) rfl running one zero reserve count
  let summing := {cleared with pc := 0}
  have clearedOne : summing.nr 6 = 1 := (fixed 6 (by decide) (by decide)).trans one
  have totalEdges : summing.nr 8 = I.graph.q := by
    change cleared.nr 8 = _
    rw [fixed 8 (by decide) (by decide)]
    simp [clearing, configured, configurePrimState, frame.one, qAt]
  have initialSum : summing.rr 0 = 1 := by
    change cleared.rr 0 = 1
    rw [clearRr]
    simp [clearing, configured, configurePrimState]
  obtain ⟨weighted, weightRun, summed, weightsNm, weightsRm, total, weightFixed⟩ :=
    apspWeightBlock_correct I summing rfl ready clearedOne totalEdges initialSum
      (fun e => (congrFun clearRm e.val).trans (weightInput e))
  let retaining := {weighted with pc := 0}
  let kept := {weighted with
    pc := 3
    nr := Function.update (Function.update weighted.nr 38 (layout.output)) 39 0
    rm := Function.update weighted.rm (weighted.nr 51) (weighted.rr 0)}
  have unchanged (r : ℕ) (notIndex : r ≠ 7) (notScratch : r ≠ 38) : weighted.nr r = configured.nr r :=
    (weightFixed r notIndex).trans (fixed r notIndex notScratch)
  have savedZero : weighted.nr 33 = 0 := (unchanged 33 (by decide) (by decide)).trans zero
  have outputBase : weighted.nr 43 = layout.output := by
    rw [unchanged 43 (by decide) (by decide)]
    simp [configured, configurePrimState, frame.dimension, frame.one, labelBase, cells, n, layout, adjacentPrimLayout]
  have reserveReal : weighted.nr 51 = layout.matrix + n ^ 2 := by
    rw [unchanged 51 (by decide) (by decide)]
    simp [configured, configurePrimState, frame.matrixBase, frame.dimension, frame.one, cells, n,
      layout, adjacentPrimLayout]
  have keepRun : BlockRuns retainPrimSentinel 3 retaining kept := by
    refine ⟨?_, ?_, rfl⟩
    · intro i hi
      interval_cases i <;> simp [retaining, retainPrimSentinel, arithmeticStep, summed, Function.iterate_succ_apply']
    · simp [retaining, kept, retainPrimSentinel, arithmeticStep, summed, Function.iterate_succ_apply',
        outputBase, savedZero]
  let finish := relocateState configurePrimArrays.length (relocateState clearRequiredBitsBlock.length
    (relocateState apspWeightBlock.length kept))
  have stable (r : ℕ) (notIndex : r ≠ 7) (notCursor : r ≠ 38) (notSize : r ≠ 39) :
      finish.nr r = configured.nr r := by
    change Function.update (Function.update weighted.nr 38 layout.output) 39 0 r = _
    rw [Function.update_of_ne notSize, Function.update_of_ne notCursor]
    exact unchanged r notIndex notCursor
  have mem (k : ℕ) : finish.nm k =
      if layout.support ≤ k ∧ k < layout.support + 2 * n then 0 else s.nm k := by
    change weighted.nm k = _
    rw [weightsNm, show summing.nm = cleared.nm from rfl, clearNm] <;> rfl
  have lower (k : ℕ) (early : k < layout.support) : finish.nm k = s.nm k := by
    rw [mem, if_neg (fun writes => (not_le.mpr early) writes.1)]
  have floyd : FloydFrame n rows matrix finish := by
    refine ⟨?_, ?_, ?_, ?_, fun i hi => ?_⟩
    · rw [stable 3 (by decide) (by decide) (by decide)]
      exact frame.tableBase
    · rw [stable 4 (by decide) (by decide) (by decide)]
      exact frame.matrixBase
    · rw [stable 5 (by decide) (by decide) (by decide)]
      exact frame.dimension
    · rw [stable 6 (by decide) (by decide) (by decide)]
      exact frame.one
    · have bounds : rows + n ≤ layout.support := rowsFit.trans (Nat.le_add_right _ _)
      exact (lower _ ((Nat.add_lt_add_left hi _).trans_le bounds)).trans (frame.rows i hi)
  have rewrites (r : ℕ) (i : ℕ) (r7 : r ≠ 7) (r38 : r ≠ 38) (r39 : r ≠ 39)
      (value : configured.nr r = i) : finish.nr r = i :=
    (stable r r7 r38 r39).trans value
  have supportAt : finish.nr 40 = layout.support := rewrites 40 _ (by decide) (by decide) (by decide)
    (by simp [configured, configurePrimState, frame.dimension, labelBase, layout, adjacentPrimLayout])
  have bits : PrimSupportFrame I rows matrix layout.support finish :=
    ⟨floyd, rewrites 8 _ (by decide) (by decide) (by decide)
      (by simp [configured, configurePrimState, frame.one, qAt]), supportAt,
      rewrites 33 _ (by decide) (by decide) (by decide) zero,
      fun a ha => (lower a (ha.trans_le (inputFit.trans (Nat.le_add_right _ _)))).trans (naturalInput a ha),
      inputFit.trans (Nat.le_add_right _ _), rowsFit.trans (Nat.le_add_right _ _)⟩
  have empty : PrimPairOutputFrame I layout.output [] finish := by
    refine ⟨?_, ?_, ?_, fun i => Fin.elim0 i⟩
    · exact (stable 43 (by decide) (by decide) (by decide)).trans ((unchanged 43 (by decide) (by decide)).symm.trans outputBase)
    · change Function.update (Function.update weighted.nr 38 layout.output) 39 0 38 = _
      simp
    · change Function.update (Function.update weighted.nr 38 layout.output) 39 0 39 = _
      simp
  have steps : 16 + ((5 * (2 * n) + 2) + ((5 * I.graph.q + 2) + 3)) =
      10 * n + 5 * I.graph.q + 23 := by ring
  refine ⟨finish, by simpa only [initializePrimArraysBlock, steps] using
    (configurePrimArrays_runs entry running).append (clear.append (weightRun.append keepRun)), ?_⟩
  refine ⟨bits, summed, rewrites 26 _ (by decide) (by decide) (by decide) ?_,
    rewrites 24 _ (by decide) (by decide) (by decide) labelBase,
    rewrites 41 _ (by decide) (by decide) (by decide) ?_, rewrites 42 _ (by decide) (by decide) (by decide) ?_,
    rewrites 9 _ (by decide) (by decide) (by decide) rfl, rewrites 45 _ (by decide) (by decide) (by decide) ?_,
    empty, ?_, ?_, lower, ?_⟩
  · simp [configured, configurePrimState, oldBits, frame.dimension, frame.one, cells, n]
  · simp [configured, configurePrimState, frame.dimension, labelBase, layout, adjacentPrimLayout]
  · simp [configured, configurePrimState, frame.dimension, labelBase, layout, adjacentPrimLayout]
  · simp [configured, configurePrimState, frame.dimension, zero]
  · intro u
    rw [mem, if_pos]
    have bound := u.isLt
    omega
  · intro u
    rw [mem, if_pos]
    have bound := u.isLt
    change layout.support ≤ layout.support + n + u.val ∧ layout.support + n + u.val < layout.support + 2 * n
    omega
  · change Function.update weighted.rm (weighted.nr 51) (weighted.rr 0) = _
    rw [weightsRm, clearRm, reserveReal, total] <;> rfl

end VehicleRoutingSurvey.Routing
end RppSource_PrimInitialization

/-! runtime/PrimSweep.lean -/
section RppSource_PrimSweep
namespace VehicleRoutingSurvey.Routing

private theorem PrimRoundFrame.keepCounter {I : Service} {layout : PrimLayout I.graph.n}
    {required seen : Fin I.graph.n → Bool} {cut : Finset (RequiredComponent I)} {pairs : List (PrimPair I)}
    {s t : ArithmeticState} (frame : PrimRoundFrame I layout required seen cut pairs s)
    (register : ∀ r, r ≠ 32 → t.nr r = s.nr r) (natural : t.nm = s.nm) (real : t.rm = s.rm) :
    PrimRoundFrame I layout required seen cut pairs t := by
  have old := frame.mask
  have mask : PrimMaskFrame I.graph.n layout.rows layout.matrix layout.support layout.visits
      layout.mask required seen t :=
    ⟨old.floyd.preserved (fun r _ upper => register r (by omega)) natural,
      (register 40 (by decide)).trans old.supportBase, (register 41 (by decide)).trans old.visitedBase,
      (register 42 (by decide)).trans old.maskBase, old.supportBeforeMask, old.visitsBeforeMask,
      old.rowsBeforeMask, fun v => (congrFun natural _).trans (old.supportBit v),
      fun v => (congrFun natural _).trans (old.visitedBit v)⟩
  exact ⟨mask, (register 24 (by decide)).trans frame.labelBase,
    (register 33 (by decide)).trans frame.zero, by rw [natural]; exact frame.labels,
    frame.supported, frame.selected,
    ⟨(register 43 (by decide)).trans frame.output.baseAt, (register 38 (by decide)).trans frame.output.cursor,
      (register 39 (by decide)).trans frame.output.length, by rw [natural]; exact frame.output.words⟩,
    by rw [real]; exact frame.distances, by rw [real]; exact frame.sentinel⟩

private def primRoundLoop : List ArithmeticInstruction :=
  countedLoopFromZero 6 32 5 primRoundBlock

def primComponentTreeBlock : List ArithmeticInstruction :=
  appendBlock primRoundLoop primPairOutputInterface

/-- Starting from a valid Prim prefix, at most n rounds produce a minimum
component tree. The result supplies the contiguous pair-array interface for
shortest-path expansion. -/
theorem primComponentTreeBlock_correct {I : Service} {layout : PrimLayout I.graph.n} {root : Fin I.graph.n}
    {required seen : Fin I.graph.n → Bool} {cut : Finset (RequiredComponent I)} {pairs : List (PrimPair I)}
    {s : ArithmeticState} (frame : PrimRoundFrame I layout required seen cut pairs s)
    (current : PrimPrefix I root cut pairs) (undirected : Undirected I.graph)
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ (t : ArithmeticState) (tree : List (PrimPair I)) (steps : ℕ),
      BlockRuns primComponentTreeBlock steps s t ∧ t.halted = false ∧
      steps ≤ 28 * I.graph.n ^ 3 + 22 * I.graph.n ^ 2 + 37 * I.graph.n + 4 ∧
      MinimumComponentTree I tree ∧ FloydFrame I.graph.n layout.rows layout.matrix t ∧
      t.nr 34 = layout.output ∧ t.nr 35 = tree.length ∧ t.nr 26 = s.nr 26 ∧
      t.rm = s.rm ∧ (∀ k < layout.labels, t.nm k = s.nm k) ∧
      ∀ i : Fin tree.length,
        t.nm (layout.output + 2 * i.val) = (tree.get i).1.val ∧
        t.nm (layout.output + 2 * i.val + 1) = (tree.get i).2.val := by
  classical
  let n := I.graph.n
  let componentCount := (activeRequiredComponents I).card
  let budget := 28 * n ^ 2 + 22 * n + 34
  let inv (i : ℕ) (m : ArithmeticState) : Prop :=
    m.pc = 0 ∧ m.halted = false ∧ m.nr 32 = i ∧ m.nr 26 = s.nr 26 ∧ m.rm = s.rm ∧
    (∀ k < layout.labels, m.nm k = s.nm k) ∧
    ∃ (cut : Finset (RequiredComponent I)) (pairs : List (PrimPair I)) (seen : Fin n → Bool),
      PrimRoundFrame I layout required seen cut pairs m ∧
      PrimPrefix I root cut pairs ∧ min i componentCount ≤ cut.card
  let first := {s with pc := 0, nr := Function.update s.nr 32 0}
  have firstFrame : PrimRoundFrame I layout required seen cut pairs first :=
    frame.keepCounter (fun _ different => Function.update_of_ne different _ _) rfl rfl
  have initial : inv 0 first :=
    ⟨rfl, running, by simp [first], rfl, rfl, fun _ _ => rfl,
      cut, pairs, seen, firstFrame, current, by simp⟩
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 32 = i ∧ m.nr 5 = n := by
    obtain ⟨pc, ready, index, _, _, _, _, _, _, f, _, _⟩ := h
    exact ⟨pc, ready, index, f.mask.floyd.dimension⟩
  have substep (i : ℕ) (_ : i < n) (m : ArithmeticState) (h : inv i m) :
      ∃ t ticks, ticks ≤ budget ∧ BlockRuns primRoundBlock ticks m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 32 (t.nr 32 + t.nr 6)} := by
    obtain ⟨pc, ready, index, oldPaths, oldReal, oldMemory, oldCut, oldPairs, oldSeen, f, prior, progress⟩ := h
    obtain ⟨nextCut, nextPairs, nextSeen, ticks, t, round⟩ :=
      primRoundBlock_correct f prior undirected pc ready
    let next := {t with pc := 0, nr := Function.update t.nr 32 (t.nr 32 + t.nr 6)}
    have nextFrame : PrimRoundFrame I layout required nextSeen nextCut nextPairs next :=
      round.frame.keepCounter (fun _ different => Function.update_of_ne different _ _) rfl rfl
    have nextProgress : min (i + 1) componentCount ≤ nextCut.card := by
      rcases round.progress with complete | advance
      · rw [complete]
        exact Nat.min_le_right _ _
      · rw [advance]
        have stepBound : min (i + 1) componentCount ≤ min i componentCount + 1 := by
          by_cases before : i ≤ componentCount
          · rw [Nat.min_eq_left before]
            exact Nat.min_le_left _ _
          · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge before))]
            exact (Nat.min_le_right _ _).trans (Nat.le_succ _)
        exact stepBound.trans (Nat.add_le_add_right progress 1)
    refine ⟨t, ticks, round.bound, round.run, round.running, rfl, round.running, ?_, ?_,
      round.realMemory.trans oldReal, fun k below => (round.previousNatural k below).trans (oldMemory k below),
      nextCut, nextPairs, nextSeen, nextFrame, round.prefixValid, nextProgress⟩
    · simp [next, round.loopIndex, index, round.frame.mask.floyd.one]
    · exact round.pathsBase.trans oldPaths
  obtain ⟨last, actual, done, bound, loop⟩ :=
    countedLoopFromZero_bounded 6 32 5 n budget primRoundBlock inv entry running initial control substep
  obtain ⟨_, lastReady, _, lastPaths, lastReal, lastMemory, completed, tree, lastSeen, lastFrame, prefixValid,
    full⟩ := done
  have countFits : componentCount ≤ n := requiredComponentCount_le_vertices I
  have all : completed = activeRequiredComponents I := by
    apply Finset.eq_of_subset_of_card_le prefixValid.activeOnly
    simpa only [Nat.min_eq_right countFits] using full
  have minimum := prefixValid.finish all
  let startOutput := {last with pc := 0}
  have layoutRun : BlockRuns primRoundLoop actual s
      (relocateState 1 {last with pc := (countedLoop 6 32 5 primRoundBlock).length}) := loop
  obtain ⟨out, expose, doneReady, base, count, outNm, outRm, _, stable⟩ :=
    primPairOutputInterface_correct (s := startOutput) rfl lastReady lastFrame.zero
  let finish := relocateState primRoundLoop.length out
  have steps : 1 + (n * (budget + 3) + 1) + 2 =
      28 * n ^ 3 + 22 * n ^ 2 + 37 * n + 4 := by
    dsimp only [budget]
    ring
  have finalBound : actual + 2 ≤ 28 * n ^ 3 + 22 * n ^ 2 + 37 * n + 4 :=
    (Nat.add_le_add_right bound 2).trans_eq steps
  have fixed (r : ℕ) (lo : 3 ≤ r) (hi : r < 7) : out.nr r = last.nr r :=
    stable r (by omega) (by omega)
  have floyd : FloydFrame n layout.rows layout.matrix finish :=
    lastFrame.mask.floyd.preserved fixed outNm
  refine ⟨finish, tree, actual + 2, by simpa only [primComponentTreeBlock] using layoutRun.append expose,
    doneReady, finalBound, minimum, floyd, base.trans lastFrame.output.baseAt,
    count.trans lastFrame.output.length, (stable 26 (by decide) (by decide)).trans lastPaths,
    outRm.trans lastReal, fun k before => (congrFun outNm k).trans (lastMemory k before), ?_⟩
  intro i
  exact ⟨(congrFun outNm _).trans (lastFrame.output.words i).1,
    (congrFun outNm _).trans (lastFrame.output.words i).2⟩

end VehicleRoutingSurvey.Routing
end RppSource_PrimSweep

/-! runtime/PrimFromLabels.lean -/
section RppSource_PrimFromLabels
namespace VehicleRoutingSurvey.Routing

def primFromLabelsBlock : List ArithmeticInstruction :=
  appendBlock initializePrimArraysBlock
    (appendBlock primSupportScanBlock (appendBlock markPrimTargetBlock primComponentTreeBlock))

/-- Starting from the verified component labels and shortest distances,
produce a minimum component tree and the path expander's pair array. -/
theorem primFromLabelsBlock_correct {I : Service} {rows matrix labels next : ℕ} {s : ArithmeticState}
    (rural : Rural I) (requiredLinks : I.links.Nonempty) (frame : FloydFrame I.graph.n rows matrix s)
    (entry : s.pc = 0) (running : s.halted = false)
    (labelBase : s.nr 24 = labels) (oldBits : s.nr 37 = next + I.graph.n ^ 2) (zero : s.nr 33 = 0)
    (rowsFit : rows + I.graph.n ≤ labels) (inputFit : 2 + 3 * I.graph.q ≤ labels)
    (weightsFit : I.graph.q ≤ matrix)
    (naturalInput : ∀ k < 2 + 3 * I.graph.q, s.nm k = (ruralNatInput I)[k]?.getD 0)
    (weightInput : ∀ e : Fin I.graph.q, s.rm e.val = I.graph.weight e)
    (distances : ∀ p : PrimPair I, s.rm (matrix + primPairOffset p) = distance I.graph p.1 p.2)
    (classes : ∀ u v : Fin I.graph.n, s.nm (labels + u.val) = s.nm (labels + v.val) ↔
      sameComponent I u v) :
    let layout := adjacentPrimLayout I.graph.n rows matrix labels rowsFit
    ∃ (t : ArithmeticState) (tree : List (PrimPair I)) (steps : ℕ),
      BlockRuns primFromLabelsBlock steps s t ∧ t.halted = false ∧
      steps ≤ 28 * I.graph.n ^ 3 + 22 * I.graph.n ^ 2 + 58 * I.graph.n + 20 * I.graph.q + 33 ∧
      MinimumComponentTree I tree ∧ FloydFrame I.graph.n rows matrix t ∧
      t.nr 34 = layout.output ∧ t.nr 35 = tree.length ∧ t.nr 26 = next ∧
      (∀ k < labels, t.nm k = s.nm k) ∧
      (∀ p : PrimPair I, t.rm (matrix + primPairOffset p) = distance I.graph p.1 p.2) ∧
      (∀ e : Fin I.graph.q, t.rm e.val = I.graph.weight e) ∧
      ∀ i : Fin tree.length,
        t.nm (layout.output + 2 * i.val) = (tree.get i).1.val ∧
        t.nm (layout.output + 2 * i.val + 1) = (tree.get i).2.val := by
  classical
  intro layout
  let n := I.graph.n
  obtain ⟨seeded, seedRun, seed⟩ := initializePrimArraysBlock_correct frame rural.1.1 entry running
    labelBase oldBits zero rowsFit inputFit naturalInput weightInput
  let scanning := {seeded with pc := 0}
  let f := seed.frame
  have scanFrame : PrimSupportFrame I rows matrix layout.support scanning :=
    ⟨⟨f.floyd.tableBase, f.floyd.matrixBase, f.floyd.dimension, f.floyd.one, f.floyd.rows⟩,
      f.count, f.base, f.zero, f.input, f.inputBelow, f.rowsBelow⟩
  obtain ⟨found, root, supportRun, supportReady, supportFrame, supportFixed, rootAt, neededRoot,
    supportReal, _, supportMemory, supportFlags⟩ :=
    primSupportScanBlock_correct scanFrame rfl seed.running seed.cursor seed.noRoot seed.supportZeros requiredLinks
  have beforeSupport (k : ℕ) (before : k < layout.support) : found.nm k = s.nm k :=
    (supportMemory k (fun h => (not_le.mpr before) h.1)).trans (seed.beforeSupport k before)
  have labelRead (u : Fin n) : found.nm (labels + u.val) = s.nm (labels + u.val) :=
    beforeSupport _ ((Nat.add_lt_add_left u.isLt _).trans_le layout.labelsBelowSupport)
  have foundComponents (u v : Fin n) :
      found.nm (labels + u.val) = found.nm (labels + v.val) ↔ sameComponent I u v := by
    rw [labelRead u, labelRead v]
    exact classes u v
  have notYet (u : Fin n) : found.nm (layout.visits + u.val) = 0 := by
    have leAddress : layout.support + n ≤ layout.visits + u.val :=
      layout.supportBelowVisits.trans (Nat.le_add_right _ _)
    exact (supportMemory _ (fun inSupport => (not_lt.mpr leAddress) inSupport.2)).trans
      (seed.visitedZeros u)
  let marking := {found with pc := 0}
  have labelsBeforeVisits : labels + n ≤ layout.visits :=
    layout.labelsBelowSupport.trans ((Nat.le_add_right _ _).trans layout.supportBelowVisits)
  obtain ⟨marked, markRun, markReady, markFixed, markReal, _, markKeeps, markedFlag⟩ :=
    markPrimTargetBlock_correct (s := marking) rfl supportReady supportFrame.floyd.dimension
      supportFrame.floyd.one supportFrame.zero ((supportFixed 24 (by decide)).trans seed.labelBase)
      ((supportFixed 41 (by decide)).trans seed.visitedBase) root rootAt labelsBeforeVisits
  let start := {marked with pc := 0}
  let required (v : Fin n) : Bool := decide (v ∈ requiredVertices I)
  let cut : Finset (RequiredComponent I) := {requiredComponent I root}
  let seen (v : Fin n) : Bool := decide (v ∈ requiredVertices I ∧ requiredComponent I v ∈ cut)
  have belowVisits (k : ℕ) (below : k < layout.visits) : marked.nm k = found.nm k :=
    markKeeps k (fun possible => (not_le.mpr below) possible.1)
  have readMarked (u : Fin n) : marked.nm (labels + u.val) = s.nm (labels + u.val) :=
    (belowVisits _ ((Nat.add_lt_add_left u.isLt _).trans_le labelsBeforeVisits)).trans (labelRead u)
  have currentFloyd : FloydFrame n rows matrix start := by
    refine ⟨(markFixed 3 (by decide) (by decide) (by decide)).trans supportFrame.floyd.tableBase,
      (markFixed 4 (by decide) (by decide) (by decide)).trans supportFrame.floyd.matrixBase,
      (markFixed 5 (by decide) (by decide) (by decide)).trans supportFrame.floyd.dimension,
      (markFixed 6 (by decide) (by decide) (by decide)).trans supportFrame.floyd.one, ?_⟩
    intro i hi
    exact (belowVisits _ ((Nat.add_lt_add_left hi _).trans_le (rowsFit.trans
      ((Nat.le_add_right _ _).trans labelsBeforeVisits)))).trans (supportFrame.floyd.rows i hi)
  have supportBits (u : Fin n) : start.nm (layout.support + u.val) = if required u then 1 else 0 := by
    change marked.nm _ = _
    rw [belowVisits _ ((Nat.add_lt_add_left u.isLt _).trans_le layout.supportBelowVisits), supportFlags]
    simp [required]
  have markedBits (u : Fin n) : start.nm (layout.visits + u.val) = if seen u then 1 else 0 := by
    have flag := markPrimComponent_flag (∅ : Finset (RequiredComponent I))
      (fun v => found.nm (labels + v.val)) (fun v => found.nm (layout.visits + v.val))
      foundComponents (fun v => by simp [notYet]) root neededRoot u
    change marked.nm _ = _
    rw [markedFlag]
    change (if found.nm (labels + u.val) = found.nm (labels + root.val) then 1
      else found.nm (layout.visits + u.val)) = if seen u then 1 else 0
    simpa [seen, cut] using flag
  have initMask : PrimMaskFrame n rows matrix layout.support layout.visits layout.mask required seen start :=
    ⟨currentFloyd,
      (markFixed 40 (by decide) (by decide) (by decide)).trans supportFrame.base,
      (markFixed 41 (by decide) (by decide) (by decide)).trans ((supportFixed 41 (by decide)).trans seed.visitedBase),
      (markFixed 42 (by decide) (by decide) (by decide)).trans ((supportFixed 42 (by decide)).trans seed.maskBase),
      layout.supportBelowVisits.trans ((Nat.le_add_right _ _).trans layout.visitsBelowMask),
      layout.visitsBelowMask, rowsFit.trans ((Nat.le_add_right _ _).trans
        (labelsBeforeVisits.trans ((Nat.le_add_right _ _).trans layout.visitsBelowMask))),
      supportBits, markedBits⟩
  have storedReal : start.rm = Function.update s.rm (matrix + n ^ 2) (1 + (ruralRealInput I).sum) :=
    (markReal.trans supportReal).trans seed.real
  have stillDistances (p : PrimPair I) : start.rm (matrix + primPairOffset p) = distance I.graph p.1 p.2 := by
    rw [storedReal, Function.update_of_ne (Nat.ne_of_lt (Nat.add_lt_add_left (primPairOffset_lt p) _))]
    exact distances p
  have high (p : PrimPair I) : distance I.graph p.1 p.2 < start.rm (matrix + n ^ 2) := by
    rw [storedReal, Function.update_self]
    simpa [ruralRealInput, ← List.ofFn_eq_map, List.sum_ofFn] using
      distance_lt_weight_sentinel rural.1 rural.2.1 p.1 p.2
  have initOutput : PrimPairOutputFrame I layout.output [] start :=
    ⟨(markFixed 43 (by decide) (by decide) (by decide)).trans ((supportFixed 43 (by decide)).trans seed.output.baseAt),
      (markFixed 38 (by decide) (by decide) (by decide)).trans ((supportFixed 38 (by decide)).trans seed.output.cursor),
      (markFixed 39 (by decide) (by decide) (by decide)).trans ((supportFixed 39 (by decide)).trans seed.output.length),
      fun i => Fin.elim0 i⟩
  have initFrame : PrimRoundFrame I layout required seen cut [] start :=
    ⟨initMask, (markFixed 24 (by decide) (by decide) (by decide)).trans ((supportFixed 24 (by decide)).trans seed.labelBase),
      (markFixed 33 (by decide) (by decide) (by decide)).trans supportFrame.zero,
      fun u v => by
        change start.nm (labels + u.val) = start.nm (labels + v.val) ↔ sameComponent I u v
        rw [show start.nm _ = _ from readMarked u, show start.nm _ = _ from readMarked v]
        exact classes u v,
      fun v => by simp [required], fun v => by simp [seen], initOutput, stillDistances, high⟩
  obtain ⟨t, tree, actual, treeRun, finalReady, treeBound, minimum, floyd, base, count, pathsBase,
    resultReal, resultNatural, words⟩ :=
    primComponentTreeBlock_correct initFrame (primPrefix_initial root neededRoot) rural.2.2.1 rfl markReady
  let finish := relocateState initializePrimArraysBlock.length (relocateState primSupportScanBlock.length
    (relocateState markPrimTargetBlock.length t))
  have run := seedRun.append (supportRun.append (markRun.append treeRun))
  have ticks : (10 * n + 5 * I.graph.q + 23) + ((15 * I.graph.q + 2) + ((11 * n + 4) +
      (28 * n ^ 3 + 22 * n ^ 2 + 37 * n + 4))) =
      28 * n ^ 3 + 22 * n ^ 2 + 58 * n + 20 * I.graph.q + 33 := by ring
  have budget := (Nat.add_le_add_left (Nat.add_le_add_left
    (Nat.add_le_add_left treeBound (11 * n + 4)) (15 * I.graph.q + 2)) (10 * n + 5 * I.graph.q + 23)).trans_eq ticks
  have finalFloyd : FloydFrame n rows matrix finish := floyd.preserved (fun _ _ _ => rfl) rfl
  refine ⟨finish, tree, _, by simpa only [primFromLabelsBlock] using run, finalReady, budget,
    minimum, finalFloyd, base, count,
    pathsBase.trans ((markFixed 26 (by decide) (by decide) (by decide)).trans
      ((supportFixed 26 (by decide)).trans seed.nextBase)), ?_, ?_, ?_, words⟩
  · intro k earlier
    exact (resultNatural k earlier).trans
      ((belowVisits k (earlier.trans_le ((Nat.le_add_right _ _).trans labelsBeforeVisits))).trans
        (beforeSupport k (earlier.trans_le (Nat.le_add_right _ _))))
  · intro p
    exact (congrFun resultReal _).trans (stillDistances p)
  · intro e
    change t.rm e.val = I.graph.weight e
    rw [resultReal, storedReal, Function.update_of_ne (Nat.ne_of_lt
      (e.isLt.trans_le (weightsFit.trans (Nat.le_add_right _ _))))]
    exact weightInput e

end VehicleRoutingSurvey.Routing
end RppSource_PrimFromLabels

/-! runtime/PrimAfterPaths.lean -/
section RppSource_PrimAfterPaths
namespace VehicleRoutingSurvey.Routing

def minimumTreeAfterPathsBlock : List ArithmeticInstruction :=
  appendBlock requiredComponentsAfterPathsBlock primFromLabelsBlock

/-- Classify the required components and select their minimum-cost connecting
tree. The shortest-path pointers and the input records remain available for
expanding the output pairs into traversals. -/
theorem minimumTreeAfterPathsBlock_correct {I : Service} {rows matrix next : ℕ}
    {s : ArithmeticState} (rural : Rural I) (requiredLinks : I.links.Nonempty)
    (frame : FloydFrame I.graph.n rows matrix s) (nextAt : s.nr 26 = next)
    (input : ∀ k < 2 + 3 * I.graph.q, s.nm k = (ruralNatInput I)[k]?.getD 0)
    (inputBefore : 2 + 3 * I.graph.q ≤ next) (rowsBefore : rows + I.graph.n ≤ next)
    (weightsBefore : I.graph.q ≤ matrix)
    (weights : ∀ e : Fin I.graph.q, s.rm e.val = I.graph.weight e)
    (distances : ∀ p : PrimPair I, s.rm (matrix + primPairOffset p) = distance I.graph p.1 p.2)
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ (t : ArithmeticState) (tree : List (PrimPair I)) (steps output : ℕ),
      BlockRuns minimumTreeAfterPathsBlock steps s t ∧ t.halted = false ∧
      steps ≤ 40 * I.graph.n ^ 3 + 41 * I.graph.n ^ 2 + 68 * I.graph.n + 35 * I.graph.q + 50 ∧
      MinimumComponentTree I tree ∧ FloydFrame I.graph.n rows matrix t ∧
      t.nr 34 = output ∧ t.nr 35 = tree.length ∧ t.nr 26 = next ∧
      next + I.graph.n ^ 2 ≤ output ∧
      (∀ k < next + I.graph.n ^ 2, t.nm k = s.nm k) ∧
      (∀ p : PrimPair I, t.rm (matrix + primPairOffset p) = distance I.graph p.1 p.2) ∧
      (∀ e : Fin I.graph.q, t.rm e.val = I.graph.weight e) ∧
      ∀ i : Fin tree.length,
        t.nm (output + 2 * i.val) = (tree.get i).1.val ∧
        t.nm (output + 2 * i.val + 1) = (tree.get i).2.val := by
  let n := I.graph.n
  let bits := next + n ^ 2
  let labels := bits + n ^ 2
  obtain ⟨labeled, labelRun, labelReady, labelFrame, labelReal, _, labelKeeps, classes⟩ :=
    requiredComponentsAfterPathsBlock_correct frame rural.1.1 nextAt input inputBefore rowsBefore entry running
  let primStart := {labeled with pc := 0}
  have rowsFit : rows + n ≤ labels :=
    (rowsBefore.trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
  have inputFit : 2 + 3 * I.graph.q ≤ labels :=
    (inputBefore.trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
  have primInput (k : ℕ) (hk : k < 2 + 3 * I.graph.q) :
      primStart.nm k = (ruralNatInput I)[k]?.getD 0 :=
    (labelKeeps k (hk.trans_le (inputBefore.trans (Nat.le_add_right _ _)))).trans (input k hk)
  have primWeights (e : Fin I.graph.q) : primStart.rm e.val = I.graph.weight e :=
    (congrFun labelReal e.val).trans (weights e)
  have primDistances (p : PrimPair I) :
      primStart.rm (matrix + primPairOffset p) = distance I.graph p.1 p.2 :=
    (congrFun labelReal _).trans (distances p)
  have primFloyd : FloydFrame n rows matrix primStart := labelFrame.floyd.preserved (fun _ _ _ => rfl) rfl
  obtain ⟨marked, tree, steps, primRun, primReady, stepBound, minimum, primFrame, outputAt,
    countAt, pathsAt, primKeeps, shortest, finalWeights, pairWords⟩ :=
    primFromLabelsBlock_correct (s := primStart) rural requiredLinks primFloyd rfl labelReady
      labelFrame.labelBase labelFrame.bitBase labelFrame.zero rowsFit inputFit weightsBefore
      primInput primWeights primDistances classes
  let layout := adjacentPrimLayout n rows matrix labels rowsFit
  let finish := relocateState requiredComponentsAfterPathsBlock.length marked
  have run := labelRun.append primRun
  have budget : (12 * n ^ 3 + 19 * n ^ 2 + 10 * n + 15 * I.graph.q + 17) + steps ≤
      40 * n ^ 3 + 41 * n ^ 2 + 68 * n + 35 * I.graph.q + 50 := by
    calc
      _ ≤ (12 * n ^ 3 + 19 * n ^ 2 + 10 * n + 15 * I.graph.q + 17) +
          (28 * n ^ 3 + 22 * n ^ 2 + 58 * n + 20 * I.graph.q + 33) :=
        Nat.add_le_add_left stepBound _
      _ = _ := by ring
  have finalFrame : FloydFrame n rows matrix finish := primFrame.preserved (fun _ _ _ => rfl) rfl
  have outputAfterBits : bits ≤ layout.output := by
    change bits ≤ bits + n ^ 2 + n + n + n + n ^ 2
    omega
  refine ⟨finish, tree, _, layout.output, by simpa only [minimumTreeAfterPathsBlock] using run,
    primReady, budget, minimum, finalFrame, outputAt, countAt, pathsAt, outputAfterBits, ?_,
    shortest, finalWeights, pairWords⟩
  intro k hk
  exact (primKeeps k (hk.trans_le (Nat.le_add_right _ _))).trans (labelKeeps k hk)

end VehicleRoutingSurvey.Routing
end RppSource_PrimAfterPaths

/-! runtime/OccurrenceArray.lean -/
section RppSource_OccurrenceArray
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

/-- Consecutive natural cells contain the original link IDs of a list
of edge occurrences. Parallel links and repeated IDs remain distinct
occurrences. -/
def OccurrenceArray {q : ℕ} (memory : ℕ → ℕ) (base : ℕ) (edges : List (Fin q)) : Prop :=
  ∀ i (valid : i < edges.length), memory (base + i) = edges[i].val

theorem OccurrenceArray.append {memory : ℕ → ℕ} {base q : ℕ}
    {first second : List (Fin q)} (left : OccurrenceArray memory base first)
    (right : OccurrenceArray memory (base + first.length) second) :
    OccurrenceArray memory base (first ++ second) := by
  intro i valid
  by_cases old : i < first.length
  · exact (left i old).trans (congrArg Fin.val (List.getElem_append_left' old second))
  · have past : first.length ≤ i := Nat.le_of_not_gt old
    have inside : i - first.length < second.length := by
      simp only [List.length_append] at valid
      omega
    calc
      memory (base + i) = memory (base + first.length + (i - first.length)) := by
        congr 1
        omega
      _ = second[i - first.length].val := right (i - first.length) inside
      _ = ((first ++ second)[i]).val :=
        congrArg Fin.val ((List.getElem_append_right past (h₂ := valid)).symm)

theorem OccurrenceArray.preservedBelow {memory other : ℕ → ℕ} {base bound q : ℕ}
    {edges : List (Fin q)} (array : OccurrenceArray memory base edges)
    (fits : base + edges.length ≤ bound) (below : ∀ a < bound, other a = memory a) :
    OccurrenceArray other base edges := by
  intro i valid
  exact (below _ ((Nat.add_lt_add_left valid _).trans_le fits)).trans (array i valid)

theorem OccurrenceArray.appendStore {memory : ℕ → ℕ} {base q : ℕ}
    {edges : List (Fin q)} (array : OccurrenceArray memory base edges) (edge : Fin q) :
    OccurrenceArray (Function.update memory (base + edges.length) edge.val) base (edges ++ [edge]) := by
  have old : OccurrenceArray (Function.update memory (base + edges.length) edge.val) base edges :=
    array.preservedBelow le_rfl (fun _ valid => Function.update_of_ne (Nat.ne_of_lt valid) _ _)
  apply old.append
  intro i valid
  have zero : i = 0 := by simp at valid; omega
  subst i
  simp

theorem occurrenceArray_ofTraversals {memory : ℕ → ℕ} {base : ℕ} {walk : List (Traversal G)}
    (stored : ∀ i (valid : i < walk.length), memory (base + i) = walk[i].1.val) :
    OccurrenceArray memory base (walk.map Prod.fst) := by
  intro i valid
  have inside : i < walk.length := by simpa using valid
  simpa using stored i inside

end VehicleRoutingSurvey.Routing
end RppSource_OccurrenceArray

/-! runtime/RequiredOccurrences.lean -/
section RppSource_RequiredOccurrences
namespace VehicleRoutingSurvey.Routing

private def readRequiredFlagBlock : List ArithmeticInstruction :=
  [.natLoad 40 39, .natAdd 39 39 6, .natAdd 39 39 6, .natAdd 39 39 6]

private def readRequiredFlagResult (s : ArithmeticState) : ArithmeticState :=
  {s with
    pc := 4
    nr := Function.update (Function.update s.nr 40 (s.nm (s.nr 39))) 39
      (s.nr 39 + s.nr 6 + s.nr 6 + s.nr 6)}

private theorem readRequiredFlag_runs (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) :
    BlockRuns readRequiredFlagBlock 4 s (readRequiredFlagResult s) := by
  refine ⟨?_, ?_, rfl⟩
  · intro i less
    interval_cases i <;> simp [readRequiredFlagBlock, arithmeticStep, entry, running,
      Function.iterate_succ_apply']
  · simp [readRequiredFlagBlock, readRequiredFlagResult, arithmeticStep, entry, running,
      Function.iterate_succ_apply', Function.update_idem]

private def appendRequiredId : List ArithmeticInstruction :=
  [.natStore 29 38, .natAdd 29 29 6]

private def appendRequiredIdResult (s : ArithmeticState) : ArithmeticState :=
  {s with
    pc := 2
    nr := Function.update s.nr 29 (s.nr 29 + s.nr 6)
    nm := Function.update s.nm (s.nr 29) (s.nr 38)}

private theorem appendRequiredId_runs (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) :
    BlockRuns appendRequiredId 2 s (appendRequiredIdResult s) := by
  refine ⟨?_, ?_, rfl⟩
  · intro i less
    interval_cases i <;> simp [appendRequiredId, arithmeticStep, entry, running,
      Function.iterate_succ_apply']
  · simp [appendRequiredId, appendRequiredIdResult, arithmeticStep, entry, running,
      Function.iterate_succ_apply']

def scanRequiredOccurrenceBlock : List ArithmeticInstruction :=
  appendBlock readRequiredFlagBlock (branchOnUnequal 40 28 appendRequiredId)

private theorem scanRequiredOccurrenceBlock_correct (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1) (zero : s.nr 28 = 0) :
    ∃ t steps, steps ≤ 8 ∧ BlockRuns scanRequiredOccurrenceBlock steps s t ∧
      t.halted = false ∧ t.rm = s.rm ∧
      (∀ r ∉ ([29, 39, 40] : List ℕ), t.nr r = s.nr r) ∧ t.nr 39 = s.nr 39 + 3 ∧
      t.nr 29 = (if s.nm (s.nr 39) = 0 then s.nr 29 else s.nr 29 + 1) ∧
      t.nm = (if s.nm (s.nr 39) = 0 then s.nm else Function.update s.nm (s.nr 29) (s.nr 38)) := by
  let read := {readRequiredFlagResult s with pc := 0}
  have first := readRequiredFlag_runs s entry running
  have fixed (r : ℕ) (notFlag : r ≠ 40) (notCursor : r ≠ 39) : read.nr r = s.nr r := by
    simp [read, readRequiredFlagResult, Function.update_of_ne notFlag, Function.update_of_ne notCursor]
  have flag : read.nr 40 = s.nm (s.nr 39) := by simp [read, readRequiredFlagResult]
  have nextFlag : read.nr 39 = s.nr 39 + 3 := by
    simp [read, readRequiredFlagResult, one, Nat.add_assoc]
  have readZero : read.nr 28 = 0 := (fixed 28 (by decide) (by decide)).trans zero
  by_cases required : s.nm (s.nr 39) = 0
  · let skip := {read with pc := (branchOnUnequal 40 28 appendRequiredId).length}
    have skips : BlockRuns (branchOnUnequal 40 28 appendRequiredId) 2 read skip :=
      branchOnUnequal_skip 40 28 appendRequiredId read rfl running (flag.trans (required.trans readZero.symm))
    refine ⟨relocateState readRequiredFlagBlock.length skip, 6, by decide, first.append skips,
      running, rfl, ?_, nextFlag, ?_, ?_⟩
    · intro r untouched
      exact fixed r (fun eq => untouched (by simp [eq])) (fun eq => untouched (by simp [eq]))
    · change read.nr 29 = (if s.nm (s.nr 39) = 0 then s.nr 29 else s.nr 29 + 1)
      rw [if_pos required]
      exact fixed 29 (by decide) (by decide)
    · simp [required, skip, read, readRequiredFlagResult, relocateState]
  · let push := appendRequiredIdResult read
    have different : read.nr 40 ≠ read.nr 28 := by
      rw [flag, readZero]
      exact required
    have takes : BlockRuns (branchOnUnequal 40 28 appendRequiredId) 4 read (relocateState 3 push) :=
      branchOnUnequal_take 40 28 appendRequiredId (s := read) rfl running different
        (appendRequiredId_runs read rfl running)
    refine ⟨relocateState readRequiredFlagBlock.length (relocateState 3 push), 8, le_rfl,
      first.append takes, running, rfl, ?_, ?_, ?_, ?_⟩
    · intro r untouched
      have not29 : r ≠ 29 := fun eq => untouched (by simp [eq])
      have not39 : r ≠ 39 := fun eq => untouched (by simp [eq])
      have not40 : r ≠ 40 := fun eq => untouched (by simp [eq])
      change Function.update read.nr 29 (read.nr 29 + read.nr 6) r = _
      rw [Function.update_of_ne not29]
      exact fixed r not40 not39
    · simpa [push, appendRequiredIdResult, relocateState] using nextFlag
    · simp [push, appendRequiredIdResult, relocateState, required,
        fixed 29 (by decide) (by decide), fixed 6 (by decide) (by decide), one]
    · simp [push, appendRequiredIdResult, relocateState, read, readRequiredFlagResult, required]

private def initializeOccurrencesBlock : List ArithmeticInstruction :=
  [.natConst 28 0, .natLoad 10 6, .natConst 39 4, .natAdd 29 33 28]

private def initializeOccurrencesResult (s : ArithmeticState) : ArithmeticState :=
  {s with
    pc := 4
    nr := Function.update (Function.update (Function.update (Function.update s.nr 28 0)
      10 (s.nm (s.nr 6))) 39 4) 29 (s.nr 33)}

private theorem initializeOccurrences_runs (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) :
    BlockRuns initializeOccurrencesBlock 4 s (initializeOccurrencesResult s) := by
  refine ⟨?_, ?_, rfl⟩
  · intro i less
    interval_cases i <;> simp [initializeOccurrencesBlock, arithmeticStep, entry, running,
      Function.iterate_succ_apply']
  · simp [initializeOccurrencesBlock, initializeOccurrencesResult, arithmeticStep, entry, running,
      Function.iterate_succ_apply']

def requiredOccurrenceBlock : List ArithmeticInstruction :=
  appendBlock initializeOccurrencesBlock (countedLoopFromZero 6 38 10 scanRequiredOccurrenceBlock)

def requiredLinkList (I : Service) : List (Fin I.graph.q) :=
  (List.finRange I.graph.q).filter (fun e => decide (e ∈ I.links))

theorem requiredLinkList_spec (I : Service) :
    (requiredLinkList I).Nodup ∧ (requiredLinkList I).toFinset = I.links := by
  constructor
  · exact (List.nodup_finRange _).filter _
  · ext e
    simp [requiredLinkList, List.mem_finRange]

private def requiredThrough (I : Service) (i : ℕ) : List (Fin I.graph.q) :=
  ((List.finRange I.graph.q).take i).filter (fun e => decide (e ∈ I.links))

private theorem requiredThrough_succ (I : Service) {i : ℕ} (more : i < I.graph.q) :
    requiredThrough I (i + 1) =
      if (⟨i, more⟩ : Fin I.graph.q) ∈ I.links then requiredThrough I i ++ [⟨i, more⟩]
      else requiredThrough I i := by
  have inside : i < (List.finRange I.graph.q).length := by simpa using more
  rw [requiredThrough, List.take_succ_eq_append_getElem inside]
  by_cases chosen : (⟨i, more⟩ : Fin I.graph.q) ∈ I.links <;> simp [requiredThrough, chosen]

def requiredOccurrencePreserved : List ℕ := [3, 4, 5, 6, 26, 33, 34, 35]

private structure RequiredOccurrenceScan (I : Service) (input : ArithmeticState) (i : ℕ)
    (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 38 = i
  count : s.nr 10 = I.graph.q
  zero : s.nr 28 = 0
  flagCursor : s.nr 39 = 4 + 3 * i
  outputCursor : s.nr 29 = input.nr 33 + (requiredThrough I i).length
  fixed : ∀ r ∈ requiredOccurrencePreserved, s.nr r = input.nr r
  real : s.rm = input.rm
  low : ∀ a < input.nr 33, s.nm a = input.nm a
  array : OccurrenceArray s.nm (input.nr 33) (requiredThrough I i)

/-- The machine enumerates the required input links once each, in their
input order. The resulting buffer is the base of the Euler occurrence list. -/
theorem requiredOccurrenceBlock_correct {I : Service} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1)
    (afterInput : 2 + 3 * I.graph.q ≤ s.nr 33)
    (encoded : ∀ a < 2 + 3 * I.graph.q, s.nm a = (ruralNatInput I)[a]?.getD 0) :
    ∃ t steps, BlockRuns requiredOccurrenceBlock steps s t ∧ steps ≤ 11 * I.graph.q + 6 ∧
      t.halted = false ∧ t.nr 28 = 0 ∧ t.nr 29 = s.nr 33 + (requiredLinkList I).length ∧
      (∀ r ∈ requiredOccurrencePreserved, t.nr r = s.nr r) ∧ t.rm = s.rm ∧
      (∀ a < s.nr 33, t.nm a = s.nm a) ∧
      OccurrenceArray t.nm (s.nr 33) (requiredLinkList I) := by
  let setup := initializeOccurrencesResult s
  let start := {setup with pc := 0}
  let inv := RequiredOccurrenceScan I s
  have startCount : s.nm 1 = I.graph.q := by
    rw [encoded 1 (by omega)]
    simp [ruralNatInput]
  have initial : inv 0 {start with pc := 0, nr := Function.update start.nr 38 0} := by
    refine ⟨rfl, running, by simp, ?_, ?_, ?_, ?_, ?_, rfl, fun _ _ => rfl, ?_⟩
    · simp [start, setup, initializeOccurrencesResult, one, startCount]
    · simp [start, setup, initializeOccurrencesResult]
    · simp [start, setup, initializeOccurrencesResult]
    · simp [start, setup, initializeOccurrencesResult, requiredThrough]
    · intro r member
      have distinct (k : ℕ) (changed : k ∈ ([10, 28, 29, 38, 39] : List ℕ)) : r ≠ k := by
        rintro rfl
        simp [requiredOccurrencePreserved] at member
        simp at changed
        omega
      simp [start, setup, initializeOccurrencesResult, Function.update_of_ne (distinct 10 (by decide)),
        Function.update_of_ne (distinct 28 (by decide)), Function.update_of_ne (distinct 29 (by decide)),
        Function.update_of_ne (distinct 38 (by decide)), Function.update_of_ne (distinct 39 (by decide))]
    · intro j possible
      simp [requiredThrough] at possible
  have control (i : ℕ) (m : ArithmeticState) (ok : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 38 = i ∧ m.nr 10 = I.graph.q :=
    ⟨ok.entry, ok.running, ok.index, ok.count⟩
  have step (i : ℕ) (more : i < I.graph.q) (m : ArithmeticState) (ok : inv i m) :
      ∃ t steps, steps ≤ 8 ∧ BlockRuns scanRequiredOccurrenceBlock steps m t ∧
        t.halted = false ∧ inv (i + 1)
          {t with pc := 0, nr := Function.update t.nr 38 (t.nr 38 + t.nr 6)} := by
    let edge : Fin I.graph.q := ⟨i, more⟩
    have mOne : m.nr 6 = 1 := (ok.fixed 6 (by decide)).trans one
    have flagAddr : m.nr 39 = 2 + 3 * edge.val + 2 := by rw [ok.flagCursor]; dsimp [edge]; omega
    have lowFlag : m.nr 39 < 2 + 3 * I.graph.q := by rw [flagAddr]; dsimp [edge]; omega
    have flag : m.nm (m.nr 39) = if edge ∈ I.links then 1 else 0 := by
      rw [ok.low _ (lowFlag.trans_le afterInput), encoded _ lowFlag, flagAddr]
      exact congrArg (fun cell => cell.getD 0)
        (ruralNatInput_link_record I edge (j := 2) (by decide))
    obtain ⟨t, steps, budget, runs, ready, real, unchanged, nextFlag, cursor, memory⟩ :=
      scanRequiredOccurrenceBlock_correct m ok.entry ok.running mOne ok.zero
    have tIndex : t.nr 38 = i := (unchanged 38 (by decide)).trans ok.index
    have tOne : t.nr 6 = 1 := (unchanged 6 (by decide)).trans mOne
    have model : requiredThrough I (i + 1) =
        if edge ∈ I.links then requiredThrough I i ++ [edge] else requiredThrough I i :=
      requiredThrough_succ I more
    refine ⟨t, steps, budget, runs, ready, ?_⟩
    refine ⟨rfl, ready, by simp [tIndex, tOne], ?_, ?_, ?_, ?_, ?_, real.trans ok.real, ?_, ?_⟩
    · simpa using (unchanged 10 (by decide)).trans ok.count
    · simpa using (unchanged 28 (by decide)).trans ok.zero
    · have position : t.nr 39 = 4 + 3 * (i + 1) := by rw [nextFlag, ok.flagCursor]; omega
      simpa using position
    · change t.nr 29 = _
      rw [cursor, flag, model, ok.outputCursor]
      by_cases chosen : edge ∈ I.links <;> simp [chosen, Nat.add_assoc]
    · intro r member
      have notIndex : r ≠ 38 := by rintro rfl; simp [requiredOccurrencePreserved] at member
      have notTouched : r ∉ ([29, 39, 40] : List ℕ) := by
        intro bad
        simp [requiredOccurrencePreserved] at member
        simp at bad
        omega
      exact (Function.update_of_ne notIndex _ _).trans ((unchanged r notTouched).trans (ok.fixed r member))
    · intro a below
      change t.nm a = s.nm a
      rw [memory, flag]
      by_cases chosen : edge ∈ I.links
      · have distinct : a ≠ m.nr 29 := by rw [ok.outputCursor]; omega
        simpa [chosen, Function.update_of_ne distinct] using ok.low a below
      · simpa [chosen] using ok.low a below
    · change OccurrenceArray t.nm (s.nr 33) (requiredThrough I (i + 1))
      rw [memory, flag, model]
      by_cases chosen : edge ∈ I.links
      · simpa [chosen, ok.outputCursor, ok.index, edge] using ok.array.appendStore edge
      · simpa [chosen] using ok.array
  obtain ⟨last, elapsed, done, cap, loop⟩ :=
    countedLoopFromZero_bounded 6 38 10 I.graph.q 8 scanRequiredOccurrenceBlock inv
      (s := start) rfl running initial control step
  have whole : requiredThrough I I.graph.q = requiredLinkList I := by
    simp [requiredThrough, requiredLinkList, List.take_of_length_le]
  have bound : 4 + elapsed ≤ 11 * I.graph.q + 6 := by omega
  obtain ⟨mEntry, mRunning, mIndex, mCount, mZero, mFlag, mCursor, mFixed, mReal, mLow, mArray⟩ := done
  rw [whole] at mCursor mArray
  exact ⟨_, 4 + elapsed, (initializeOccurrences_runs s entry running).append loop, bound, mRunning,
    mZero, mCursor, mFixed, mReal, mLow, mArray⟩

end VehicleRoutingSurvey.Routing
end RppSource_RequiredOccurrences

/-! runtime/FollowLink.lean -/
section RppSource_FollowLink
namespace VehicleRoutingSurvey.Routing

/-- Load the next-edge ID for destination register 7 and source register
9. The next-edge table begins at register 26. The raw link endpoints
are still in the natural input array. -/
def loadNextLinkBlock : List ArithmeticInstruction :=
  [.natAdd 22 3 7, .natLoad 22 22, .natAdd 22 26 22, .natAdd 22 22 9,
    .natLoad 14 22, .natAdd 23 14 14, .natAdd 23 23 14,
    .natAdd 23 23 6, .natAdd 23 23 6, .natLoad 24 23,
    .natAdd 23 23 6, .natLoad 25 23]

private def loadNextLinkResult (s : ArithmeticState) : ArithmeticState :=
  let cell := s.nr 26 + s.nm (s.nr 3 + s.nr 7) + s.nr 9
  let edge := s.nm cell
  let inputCell := edge + edge + edge + s.nr 6 + s.nr 6
  let registers := Function.update (Function.update (Function.update s.nr 22 cell) 14 edge)
    23 inputCell
  {s with
    pc := 12
    nr := Function.update (Function.update (Function.update registers 24 (s.nm inputCell))
      23 (inputCell + s.nr 6))
      25 (s.nm (inputCell + s.nr 6))}

private theorem loadNextLinkBlock_runs (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    BlockRuns loadNextLinkBlock 12 s (loadNextLinkResult s) := by
  refine ⟨?_, ?_, rfl⟩
  · intro i inside
    interval_cases i <;> simp [loadNextLinkBlock, arithmeticStep, entry, running,
      Function.iterate_succ_apply']
  · simp [loadNextLinkBlock, loadNextLinkResult, arithmeticStep, entry, running,
      Function.iterate_succ_apply', Function.update_idem]

/-- Orient the loaded undirected link by comparing its tail with the
current vertex. Register 15 gets the direction bit and register 16 gets
the opposite endpoint. Register 28 contains zero. -/
def orientNextLinkBlock : List ArithmeticInstruction :=
  [.natBranch 9 24 1 2, .natBranch 24 9 3 6, .jump 6,
    .natConst 15 1, .natAdd 16 25 28, .jump 9,
    .natConst 15 0, .natAdd 16 24 28, .jump 9]

private def orientNextLinkResult (s : ArithmeticState) : ArithmeticState :=
  {s with
    pc := 9
    nr := Function.update
      (Function.update s.nr 15 (if s.nr 9 = s.nr 24 then 1 else 0))
      16 ((if s.nr 9 = s.nr 24 then s.nr 25 else s.nr 24) + s.nr 28)}

private theorem orientNextLinkBlock_runs (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    BlockRuns orientNextLinkBlock 5 s (orientNextLinkResult s) := by
  refine ⟨?_, ?_, rfl⟩
  · intro i inside
    by_cases lower : s.nr 9 ≤ s.nr 24
    · by_cases upper : s.nr 24 ≤ s.nr 9
      · interval_cases i <;> simp [orientNextLinkBlock, arithmeticStep, entry, running,
          Function.iterate_succ_apply', lower, upper]
      · interval_cases i <;> simp [orientNextLinkBlock, arithmeticStep, entry, running,
          Function.iterate_succ_apply', lower, upper]
    · interval_cases i <;> simp [orientNextLinkBlock, arithmeticStep, entry, running,
        Function.iterate_succ_apply', lower]
  · by_cases lower : s.nr 9 ≤ s.nr 24
    · by_cases upper : s.nr 24 ≤ s.nr 9
      · have same := Nat.le_antisymm lower upper
        simp [orientNextLinkBlock, orientNextLinkResult, arithmeticStep, entry, running,
          Function.iterate_succ_apply', lower, upper, same]
      · have different : s.nr 9 ≠ s.nr 24 := fun same => upper same.ge
        simp [orientNextLinkBlock, orientNextLinkResult, arithmeticStep, entry, running,
          Function.iterate_succ_apply', lower, upper, different]
    · have different : s.nr 9 ≠ s.nr 24 := fun same => lower same.le
      simp [orientNextLinkBlock, orientNextLinkResult, arithmeticStep, entry, running,
        Function.iterate_succ_apply', lower, different]

def followNextLinkBlock : List ArithmeticInstruction :=
  appendBlock loadNextLinkBlock orientNextLinkBlock

/-- A shortest-path pointer is decoded in seventeen arithmetic steps.
The nonloop premise ensures the direction is determined by the source. -/
theorem followNextLinkBlock_correct {G : Network} {rowOffsets distanceBase : ℕ}
    {source target : Fin G.n} {step : Traversal G} {s : ArithmeticState}
    (floyd : FloydFrame G.n rowOffsets distanceBase s)
    (sourceReg : s.nr 9 = source.val) (targetReg : s.nr 7 = target.val)
    (zero : s.nr 28 = 0) (entry : s.pc = 0) (running : s.halted = false)
    (parent : s.nm (s.nr 26 + G.n * target.val + source.val) = step.1.val)
    (starts : start G step = source) (nonloop : start G step ≠ finish G step)
    (tailCell : s.nm (2 + 3 * step.1.val) = (G.tail step.1).val)
    (headCell : s.nm (3 + 3 * step.1.val) = (G.head step.1).val) :
    ∃ t, BlockRuns followNextLinkBlock 17 s t ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      t.nr 14 = step.1.val ∧ t.nr 15 = (if step.2 then 1 else 0) ∧
      t.nr 16 = (finish G step).val := by
  let read := loadNextLinkResult s
  let oriented := orientNextLinkResult {read with pc := 0}
  have run := (loadNextLinkBlock_runs s entry running).append
    (orientNextLinkBlock_runs {read with pc := 0} rfl running)
  have offset : s.nm (s.nr 3 + s.nr 7) = G.n * target.val := by
    rw [floyd.tableBase, targetReg, floyd.rows _ target.isLt]
  have idReg : read.nr 14 = step.1.val := by
    simp [read, loadNextLinkResult, sourceReg, offset, parent]
  have constTail : step.1.val + step.1.val + step.1.val + 1 + 1 = 2 + 3 * step.1.val := by omega
  have constHead : step.1.val + step.1.val + step.1.val + 1 + 1 + 1 =
      3 + 3 * step.1.val := by omega
  have tailReg : read.nr 24 = (G.tail step.1).val := by
    simp [read, loadNextLinkResult, sourceReg, offset, parent, floyd.one, constTail, tailCell]
  have headReg : read.nr 25 = (G.head step.1).val := by
    simp [read, loadNextLinkResult, sourceReg, offset, parent, floyd.one, constHead, headCell]
  have readSource : read.nr 9 = source.val := by simp [read, loadNextLinkResult, sourceReg]
  have readZero : read.nr 28 = 0 := by simp [read, loadNextLinkResult, zero]
  have output : oriented.nr 15 = (if step.2 then 1 else 0) ∧
      oriented.nr 16 = (finish G step).val := by
    cases dir : step.2 with
    | false =>
      have different : source.val ≠ (G.tail step.1).val := by
        intro same
        apply nonloop
        have headIsSource : G.head step.1 = source := by simpa [start, dir] using starts
        simpa [start, finish, dir, headIsSource] using (Fin.ext same : source = G.tail step.1)
      simp [oriented, orientNextLinkResult, readSource, tailReg, different, readZero, finish, dir]
    | true =>
      have equal : source.val = (G.tail step.1).val := congrArg Fin.val
        (by simpa [start, dir] using starts.symm)
      simp [oriented, orientNextLinkResult, readSource, tailReg, headReg, equal, readZero, finish, dir]
  refine ⟨relocateState loadNextLinkBlock.length oriented, run, running, rfl, rfl, ?_, output.1, output.2⟩
  simpa [oriented, orientNextLinkResult, relocateState] using idReg

theorem followNextLinkBlock_fixed {s t : ArithmeticState}
    (run : BlockRuns followNextLinkBlock 17 s t) (entry : s.pc = 0)
    (running : s.halted = false) (r : ℕ)
    (untouched : r ∉ ([14, 15, 16, 22, 23, 24, 25] : List ℕ)) :
    t.nr r = s.nr r := by
  let read := loadNextLinkResult s
  let out := orientNextLinkResult {read with pc := 0}
  have executes := (loadNextLinkBlock_runs s entry running).append
    (orientNextLinkBlock_runs {read with pc := 0} rfl running)
  have same : t = relocateState loadNextLinkBlock.length out := run.run.symm.trans executes.run
  have different (k : ℕ) (changed : k ∈ ([14, 15, 16, 22, 23, 24, 25] : List ℕ)) :
      r ≠ k := fun eq => untouched (eq.symm ▸ changed)
  rw [same]
  simp [out, read, orientNextLinkResult, loadNextLinkResult, relocateState,
    Function.update_of_ne (different 14 (by decide)), Function.update_of_ne (different 15 (by decide)),
    Function.update_of_ne (different 16 (by decide)), Function.update_of_ne (different 22 (by decide)),
    Function.update_of_ne (different 23 (by decide)), Function.update_of_ne (different 24 (by decide)),
    Function.update_of_ne (different 25 (by decide))]

/-- Append the original link ID to the occurrence array for Euler
traversal, advance its cursor, and advance the current path vertex. -/
def appendNextOccurrenceBlock : List ArithmeticInstruction :=
  [.natStore 29 14, .natAdd 29 29 6, .natAdd 9 16 28]

private def appendNextOccurrenceResult (s : ArithmeticState) : ArithmeticState :=
  {s with
    pc := 3
    nr := Function.update (Function.update s.nr 29 (s.nr 29 + s.nr 6)) 9 (s.nr 16 + s.nr 28)
    nm := Function.update s.nm (s.nr 29) (s.nr 14)}

private theorem appendNextOccurrence_runs (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) :
    BlockRuns appendNextOccurrenceBlock 3 s (appendNextOccurrenceResult s) := by
  refine ⟨?_, ?_, rfl⟩
  · intro i less
    interval_cases i <;> simp [appendNextOccurrenceBlock, arithmeticStep, entry, running,
      Function.iterate_succ_apply']
  · simp [appendNextOccurrenceBlock, appendNextOccurrenceResult, arithmeticStep, entry, running,
      Function.iterate_succ_apply']

def followAndAppendOccurrenceBlock : List ArithmeticInstruction :=
  appendBlock followNextLinkBlock appendNextOccurrenceBlock

theorem followAndAppendOccurrenceBlock_correct {s decoded : ArithmeticState}
    (decodes : BlockRuns followNextLinkBlock 17 s decoded)
    (entry : s.pc = 0) (running : s.halted = false) (decodeReady : decoded.halted = false)
    (one : s.nr 6 = 1) (zero : s.nr 28 = 0)
    (decodedMemory : decoded.nm = s.nm) (decodedReal : decoded.rm = s.rm) :
    ∃ t, BlockRuns followAndAppendOccurrenceBlock 20 s t ∧ t.halted = false ∧
      t.nr 9 = decoded.nr 16 ∧ t.nr 29 = s.nr 29 + 1 ∧
      t.nm = Function.update s.nm (s.nr 29) (decoded.nr 14) ∧ t.rm = s.rm ∧
      ∀ r ∈ ([3, 4, 5, 6, 7, 26, 27, 28, 33, 34, 35, 36, 37] : List ℕ), t.nr r = s.nr r := by
  let ready := {decoded with pc := 0}
  let output := appendNextOccurrenceResult ready
  have runs := decodes.append (appendNextOccurrence_runs ready rfl decodeReady)
  have fixed (r : ℕ) (untouched : r ∉ ([14, 15, 16, 22, 23, 24, 25] : List ℕ)) :
      decoded.nr r = s.nr r := followNextLinkBlock_fixed decodes entry running r untouched
  have keepOne : decoded.nr 6 = 1 := (fixed 6 (by decide)).trans one
  have keepZero : decoded.nr 28 = 0 := (fixed 28 (by decide)).trans zero
  have keepCursor : decoded.nr 29 = s.nr 29 := fixed 29 (by decide)
  refine ⟨relocateState followNextLinkBlock.length output, runs, decodeReady, ?_, ?_, ?_, decodedReal, ?_⟩
  · simp [output, ready, appendNextOccurrenceResult, relocateState, keepZero]
  · simp [output, ready, appendNextOccurrenceResult, relocateState, keepOne, keepCursor]
  · simp [output, ready, appendNextOccurrenceResult, relocateState, decodedMemory, keepCursor]
  · intro r present
    have decoderUntouched : r ∉ ([14, 15, 16, 22, 23, 24, 25] : List ℕ) := by
      intro changes
      simp at present changes
      omega
    have noCurrentWrite : r ≠ 9 := by simp at present; omega
    have noCursorWrite : r ≠ 29 := by simp at present; omega
    simp [output, ready, appendNextOccurrenceResult, relocateState,
      Function.update_of_ne noCurrentWrite, Function.update_of_ne noCursorWrite, fixed r decoderUntouched]

end VehicleRoutingSurvey.Routing
end RppSource_FollowLink

/-! runtime/TightWalk.lean -/
section RppSource_TightWalk
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

/-- Read next edges until the destination is reached or the requested
number of pointer steps is exhausted. -/
def followTightPointers (target : Fin G.n) (next : ∀ u, u ≠ target → Traversal G) :
    ℕ → Fin G.n → List (Traversal G)
  | 0, _ => []
  | fuel + 1, u =>
    if done : u = target then [] else
      let edge := next u done
      edge :: followTightPointers target next fuel (finish G edge)

/-- A fuel bound at least the discovery rank is enough to follow the
stored pointers to the destination. The emitted traversals are shortest
and have no repeated vertex. -/
theorem followTightPointers_correct (nonnegative : Nonnegative G)
    (target : Fin G.n) (rank : Fin G.n → ℕ) (next : ∀ u, u ≠ target → Traversal G)
    (starts : ∀ u different, start G (next u different) = u)
    (allowed : ∀ u different, G.directed (next u different).1 = false ∨
      (next u different).2 = true)
    (tight : ∀ u different, tightTraversal G target (next u different))
    (decreases : ∀ u different, rank (finish G (next u different)) < rank u)
    (fuel : ℕ) (u : Fin G.n) (enough : rank u ≤ fuel) :
    let ts := followTightPointers target next fuel u
    ShortestPath G u target ts ∧ ts.length ≤ rank u ∧
      (u :: ts.map (finish G)).Nodup ∧
      (∀ x ∈ u :: ts.map (finish G), rank x ≤ rank u) := by
  have emptyResult : ShortestPath G target target [] ∧
      ([] : List (Traversal G)).length ≤ rank target ∧
      [target].Nodup ∧ (∀ x ∈ [target], rank x ≤ rank target) := by
    exact ⟨⟨rfl, fun ss _ => pathCost_nonnegative nonnegative ss⟩, Nat.zero_le _, by simp, by simp⟩
  induction fuel generalizing u with
  | zero =>
    have atTarget : u = target := by
      by_contra different
      exact (Nat.not_lt_zero _) ((decreases u different).trans_le enough)
    subst u
    exact emptyResult
  | succ fuel ih =>
    by_cases done : u = target
    · subst u
      simpa [followTightPointers] using emptyResult
    · let edge := next u done
      let after := finish G edge
      let tail := followTightPointers target next fuel after
      have lower : rank after < rank u := decreases u done
      have tailFuel : rank after ≤ fuel :=
        Nat.le_of_lt_succ (lower.trans_le enough)
      obtain ⟨shortestTail, tailLength, tailUnique, tailRanks⟩ := ih after tailFuel
      have valid : IsPath G u (edge :: tail) target :=
        ⟨(starts u done).symm, allowed u done, shortestTail.1⟩
      have cost : pathCost G (edge :: tail) = distance G u target := by
        have exactEdge := tight u done
        rw [tightTraversal, starts u done] at exactEdge
        change G.weight edge.1 + pathCost G tail = distance G u target
        exact (congrArg (G.weight edge.1 + ·) (distance_eq_of_shortestPath shortestTail)).symm.trans
          exactEdge.symm
      have shortest : ShortestPath G u target (edge :: tail) :=
        ⟨valid, fun other path => cost.symm ▸ distance_le_pathCost nonnegative path⟩
      have length : (edge :: tail).length ≤ rank u :=
        (Nat.succ_le_succ tailLength).trans lower
      have avoids : u ∉ after :: tail.map (finish G) :=
        fun seen => (Nat.not_le_of_gt lower) (tailRanks u seen)
      simp only [followTightPointers, dif_neg done]
      refine ⟨shortest, length, List.nodup_cons.mpr ⟨avoids, tailUnique⟩, ?_⟩
      intro x seen
      rcases List.mem_cons.mp seen with rfl | inTail
      · exact le_rfl
      · exact (tailRanks x inTail).trans lower.le

/-- Every emitted edge is one looked up by the pointer follower. -/
theorem followTightPointers_uses {target : Fin G.n}
    (next : ∀ u, u ≠ target → Traversal G) (fuel : ℕ) (source : Fin G.n)
    {step : Traversal G} (seen : step ∈ followTightPointers target next fuel source) :
    ∃ u, ∃ different : u ≠ target, step = next u different := by
  induction fuel generalizing source with
  | zero => simp [followTightPointers] at seen
  | succ fuel ih =>
    by_cases done : source = target
    · simp [followTightPointers, done] at seen
    · simp only [followTightPointers, dif_neg done, List.mem_cons] at seen
      rcases seen with rfl | more
      · exact ⟨source, done, rfl⟩
      · exact ih _ more

end VehicleRoutingSurvey.Routing
end RppSource_TightWalk

/-! runtime/PathEmission.lean -/
section RppSource_PathEmission
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

theorem TightStoredRow.shortestPath {target : Fin G.n} {table : DirectLinkTable G}
    {base : ℕ} {memory : ℕ → ℕ} (row : TightStoredRow target table base memory)
    (connected : Connected G) (nonnegative : Nonnegative G) (sound : DirectLinkTableSound table)
    (representative : DirectLinkRepresentatives G (tableChooses table)) (source : Fin G.n) :
    ∃ ts, ShortestPath G source target ts ∧ ts.length < G.n ∧
      ∀ edge ∈ ts, start G edge ≠ target ∧ start G edge ≠ finish G edge ∧
        memory (base + G.n * target.val + (start G edge).val) = edge.1.val := by
  obtain ⟨valid, everySource⟩ := tightSearchAfter_complete connected nonnegative target table sound representative
  let out := tightSearchAfter target table G.n
  let next (u : Fin G.n) (away : u ≠ target) : Traversal G := (row u away).choose
  have specification (u : Fin G.n) (away : u ≠ target) :
      start G (next u away) = u ∧
        (G.directed (next u away).1 = false ∨ (next u away).2 = true) ∧
        tightTraversal G target (next u away) ∧
        memory (base + G.n * target.val + u.val) = (next u away).1.val ∧
        out.rank (finish G (next u away)) < out.rank u :=
    (row u away).choose_spec
  have lengthLE : out.queue.length ≤ G.n := by simpa using valid.unique.length_le_card
  have rankBound : out.rank source < G.n :=
    (valid.ranks source (everySource source)).trans_le lengthLE
  obtain ⟨shortest, length, _, _⟩ := followTightPointers_correct nonnegative target out.rank next
    (fun u h => (specification u h).1) (fun u h => (specification u h).2.1)
    (fun u h => (specification u h).2.2.1) (fun u h => (specification u h).2.2.2.2)
    G.n source rankBound.le
  refine ⟨_, shortest, length.trans_lt rankBound, fun edge used => ?_⟩
  obtain ⟨u, away, rfl⟩ := followTightPointers_uses next G.n source used
  obtain ⟨startAt, _, _, stored, decreases⟩ := specification u away
  refine ⟨startAt.symm ▸ away, ?_, by rwa [startAt]⟩
  intro loop
  have same : finish G (next u away) = u := loop.symm.trans startAt
  rw [same] at decreases
  exact (Nat.lt_irrefl _) decreases

def emitShortestPathBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 27 5 (branchOnUnequal 9 7 followAndAppendOccurrenceBlock)

def pathEmitFixed : List ℕ := [3, 4, 5, 6, 7, 26, 28, 33, 34, 35, 36, 37]

private structure PathEmitInvariant (before : ArithmeticState) (destination : Fin G.n)
    (chosen : List (Traversal G)) (i : ℕ) (current : ArithmeticState) : Prop where
  entry : current.pc = 0
  running : current.halted = false
  index : current.nr 27 = i
  fixed : ∀ r ∈ pathEmitFixed, current.nr r = before.nr r
  real : current.rm = before.rm
  low : ∀ a < before.nr 29, current.nm a = before.nm a
  path : ∃ (emitted remaining : List (Traversal G)) (vertex : Fin G.n),
    chosen = emitted ++ remaining ∧ IsPath G vertex remaining destination ∧
    current.nr 9 = vertex.val ∧ remaining.length ≤ G.n - i ∧
    current.nr 29 = before.nr 29 + emitted.length ∧
    ∀ j (valid : j < emitted.length), current.nm (before.nr 29 + j) = emitted[j].1.val

private theorem pathEmit_indexPreserves (s : ArithmeticState) (index : ℕ)
    {r : ℕ} (member : r ∈ pathEmitFixed) :
    (Function.update s.nr 27 index) r = s.nr r := by
  have different : r ≠ 27 := by
    rintro rfl
    exact (by decide : 27 ∉ pathEmitFixed) member
  exact Function.update_of_ne different _ _

private theorem encodedOccurrence_append {memory : ℕ → ℕ} {base : ℕ}
    {emitted : List (Traversal G)} (edge : Traversal G)
    (encoded : ∀ j (valid : j < emitted.length), memory (base + j) = emitted[j].1.val) :
    ∀ j (valid : j < (emitted ++ [edge]).length),
      Function.update memory (base + emitted.length) edge.1.val (base + j) =
        ((emitted ++ [edge])[j]).1.val := by
  intro j valid
  by_cases before : j < emitted.length
  · have different : base + j ≠ base + emitted.length :=
      fun eq => (Nat.ne_of_lt before) (Nat.add_left_cancel eq)
    rw [Function.update_of_ne different, encoded j before]
    exact congrArg (fun step : Traversal G => step.1.val) (List.getElem_append_left' before [edge])
  · have final : j = emitted.length := by simp at valid; omega
    subst j
    rw [Function.update_self]
    have last : edge = (emitted ++ [edge])[emitted.length]'(by simp) := by
      simpa using (List.getElem_append_right' emitted (l₂ := [edge]) (i := 0) (by simp))
    exact congrArg (fun step : Traversal G => step.1.val) last

/-- Emit the original link IDs of a shortest path into the occurrence
buffer. The row pointers and original encoded links are kept intact. -/
theorem emitShortestPathBlock_correct {rowOffsets distances : ℕ} {s : ArithmeticState}
    {source target : Fin G.n} {table : DirectLinkTable G}
    (connected : Connected G) (nonnegative : Nonnegative G)
    (sound : DirectLinkTableSound table)
    (representative : DirectLinkRepresentatives G (tableChooses table))
    (row : TightStoredRow target table (s.nr 26) s.nm)
    (frame : FloydFrame G.n rowOffsets distances s)
    (startReg : s.nr 9 = source.val) (targetReg : s.nr 7 = target.val) (zero : s.nr 28 = 0)
    (rowOffsetsBelow : rowOffsets + G.n ≤ s.nr 29)
    (pointerTableBelow : s.nr 26 + G.n * G.n ≤ s.nr 29)
    (inputBelow : 2 + 3 * G.q ≤ s.nr 29)
    (tailCell : ∀ e : Fin G.q, s.nm (2 + 3 * e.val) = (G.tail e).val)
    (headCell : ∀ e : Fin G.q, s.nm (3 + 3 * e.val) = (G.head e).val)
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t ts steps, BlockRuns emitShortestPathBlock steps s t ∧
      steps ≤ 1 + (G.n * (22 + 3) + 1) ∧ t.halted = false ∧
      ShortestPath G source target ts ∧ ts.length < G.n ∧ t.nr 9 = target.val ∧
      t.nr 29 = s.nr 29 + ts.length ∧
      (∀ j (valid : j < ts.length), t.nm (s.nr 29 + j) = ts[j].1.val) ∧
      (∀ a < s.nr 29, t.nm a = s.nm a) ∧ t.rm = s.rm ∧
      ∀ r ∈ pathEmitFixed, t.nr r = s.nr r := by
  obtain ⟨ts, shortest, bounded, usedEdges⟩ :=
    row.shortestPath connected nonnegative sound representative source
  let inv := PathEmitInvariant s target ts
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 27 0} := by
    refine ⟨rfl, running, by simp, fun r hr => pathEmit_indexPreserves s 0 hr, rfl, fun _ _ => rfl, ?_⟩
    refine ⟨[], ts, source, rfl, shortest.1, ?_, ?_, ?_, ?_⟩
    · simpa using startReg
    · simpa using bounded.le
    · simp
    · intro j impossible
      simp at impossible
  have control (i : ℕ) (m : ArithmeticState) (ok : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 27 = i ∧ m.nr 5 = G.n :=
    ⟨ok.entry, ok.running, ok.index, (ok.fixed 5 (by decide)).trans frame.dimension⟩
  have step (i : ℕ) (more : i < G.n) (m : ArithmeticState) (ok : inv i m) :
      ∃ t steps, steps ≤ 22 ∧
        BlockRuns (branchOnUnequal 9 7 followAndAppendOccurrenceBlock) steps m t ∧
        t.halted = false ∧ inv (i + 1)
          {t with pc := 0, nr := Function.update t.nr 27 (t.nr 27 + t.nr 6)} := by
    obtain ⟨emitted, remaining, vertex, split, walks, atVertex, count, cursor, encoded⟩ := ok.path
    have mOne := (ok.fixed 6 (by decide)).trans frame.one
    have mZero := (ok.fixed 28 (by decide)).trans zero
    have targetAt := (ok.fixed 7 (by decide)).trans targetReg
    cases remaining with
    | nil =>
      have arrived : vertex = target := walks
      have equal : m.nr 9 = m.nr 7 := (atVertex.trans (congrArg Fin.val arrived)).trans targetAt.symm
      let t := {m with pc := (branchOnUnequal 9 7 followAndAppendOccurrenceBlock).length}
      refine ⟨t, 2, by decide, branchOnUnequal_skip 9 7 _ m ok.entry ok.running equal,
        ok.running, ?_⟩
      refine ⟨rfl, ok.running, ?_, ?_, ok.real, ok.low, ?_⟩
      · simp [t, ok.index, mOne]
      · intro r hr
        exact (pathEmit_indexPreserves t _ hr).trans (ok.fixed r hr)
      · refine ⟨emitted, [], vertex, split, walks, ?_, by simp, ?_, encoded⟩
        · simpa [t] using atVertex
        · simpa [t] using cursor
    | cons edge remaining =>
      have used : edge ∈ ts := split.symm ▸ List.mem_append.mpr (.inr List.mem_cons_self)
      obtain ⟨away, nonloop, pointer⟩ := usedEdges edge used
      have starts : start G edge = vertex := walks.1.symm
      have different : m.nr 9 ≠ m.nr 7 := by
        rw [atVertex, targetAt]
        exact fun same => away (starts.trans (Fin.ext same))
      have mFrame : FloydFrame G.n rowOffsets distances m := by
        refine ⟨(ok.fixed 3 (by decide)).trans frame.tableBase,
          (ok.fixed 4 (by decide)).trans frame.matrixBase, (ok.fixed 5 (by decide)).trans frame.dimension,
          mOne, ?_⟩
        intro j hj
        exact (ok.low _ ((Nat.add_lt_add_left hj _).trans_le rowOffsetsBelow)).trans (frame.rows j hj)
      have pointerAddress : s.nr 26 + G.n * target.val + vertex.val < s.nr 29 := by
        have within : G.n * target.val + vertex.val < G.n * G.n := by
          have rowBound : G.n * (target.val + 1) ≤ G.n * G.n :=
            Nat.mul_le_mul_left _ (Nat.succ_le_of_lt target.isLt)
          rw [Nat.mul_succ] at rowBound
          exact (Nat.add_lt_add_left vertex.isLt _).trans_le rowBound
        omega
      have mPointer : m.nm (m.nr 26 + G.n * target.val + vertex.val) = edge.1.val := by
        rw [ok.fixed 26 (by decide), ok.low _ pointerAddress, ← starts]
        exact pointer
      have edgeBelow := edge.1.isLt
      have mTail : m.nm (2 + 3 * edge.1.val) = (G.tail edge.1).val :=
        (ok.low _ (by omega)).trans (tailCell edge.1)
      have mHead : m.nm (3 + 3 * edge.1.val) = (G.head edge.1).val :=
        (ok.low _ (by omega)).trans (headCell edge.1)
      obtain ⟨d, reads, dReady, dNatural, dReal, id, _, vertexNext⟩ :=
        followNextLinkBlock_correct mFrame atVertex targetAt mZero ok.entry ok.running
          mPointer starts nonloop mTail mHead
      obtain ⟨after, appends, ready, nextVertex, nextCursor, writes, real, fixed⟩ :=
        followAndAppendOccurrenceBlock_correct reads ok.entry ok.running dReady
          mOne mZero dNatural dReal
      let t := relocateState 3 after
      have tIndex : t.nr 27 = i := (fixed 27 (by decide)).trans ok.index
      have tOne : t.nr 6 = 1 := (fixed 6 (by decide)).trans mOne
      refine ⟨t, 22, le_rfl, branchOnUnequal_take 9 7 _ ok.entry ok.running different appends,
        ready, ?_⟩
      refine ⟨rfl, ready, ?_, ?_, real.trans ok.real, ?_, ?_⟩
      · simp [t, tIndex, tOne]
      · intro r hr
        exact (pathEmit_indexPreserves t _ hr).trans ((fixed r (by
          simp [pathEmitFixed] at hr
          simp
          omega)).trans (ok.fixed r hr))
      · intro a below
        change after.nm a = s.nm a
        rw [writes, Function.update_of_ne (show a ≠ m.nr 29 by omega)]
        exact ok.low a below
      · refine ⟨emitted ++ [edge], remaining, finish G edge, ?_, walks.2.2, ?_, ?_, ?_, ?_⟩
        · simpa [List.append_assoc] using split
        · simpa [t, relocateState] using nextVertex.trans vertexNext
        · simp at count
          omega
        · simpa [t, relocateState, cursor, Nat.add_assoc] using nextCursor
        · intro j hj
          change after.nm (s.nr 29 + j) = _
          rw [writes, cursor, id]
          exact encodedOccurrence_append edge encoded j hj
  obtain ⟨last, actual, complete, budget, executes⟩ :=
    countedLoopFromZero_bounded 6 27 5 G.n 22
      (branchOnUnequal 9 7 followAndAppendOccurrenceBlock) inv entry running initial control step
  obtain ⟨emitted, remaining, vertex, split, walks, here, count, cursor, encoded⟩ := complete.path
  have empty : remaining = [] :=
    List.length_eq_zero_iff.mp (by simpa using count)
  subst remaining
  have finished : vertex = target := walks
  subst vertex
  have exactEdges : ts = emitted := by simpa using split
  subst emitted
  exact ⟨_, ts, actual, executes, budget, complete.running, shortest, bounded, here, cursor,
    encoded, complete.low, complete.real, complete.fixed⟩

end VehicleRoutingSurvey.Routing
end RppSource_PathEmission

/-! runtime/PairExpansion.lean -/
section RppSource_PairExpansion
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

def ExpansionPairArray (memory : ℕ → ℕ) (base : ℕ)
    (pairs : List (Fin G.n × Fin G.n)) : Prop :=
  ∀ i (valid : i < pairs.length),
    memory (base + 2 * i) = pairs[i].1.val ∧ memory (base + 2 * i + 1) = pairs[i].2.val

private def beginPairCursor : List ArithmeticInstruction := [.natAdd 36 34 28]

private theorem beginPairCursor_runs (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 28 = 0) :
    BlockRuns beginPairCursor 1 s {s with pc := 1, nr := Function.update s.nr 36 (s.nr 34)} := by
  refine ⟨?_, ?_, rfl⟩
  · intro i less
    have isZero : i = 0 := by omega
    simp [isZero, entry, beginPairCursor]
  · simp [beginPairCursor, arithmeticStep, entry, running, zero]

private def readExpansionPair : List ArithmeticInstruction :=
  [.natLoad 9 36, .natAdd 36 36 6, .natLoad 7 36, .natAdd 36 36 6]

private theorem readExpansionPair_correct (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1) :
    ∃ t, BlockRuns readExpansionPair 4 s t ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      t.nr 9 = s.nm (s.nr 36) ∧ t.nr 7 = s.nm (s.nr 36 + 1) ∧ t.nr 36 = s.nr 36 + 2 ∧
      ∀ r, r ≠ 9 → r ≠ 7 → r ≠ 36 → t.nr r = s.nr r := by
  let t := (arithmeticStep readExpansionPair)^[4] s
  have ready : t.halted = false := by
    simp [t, readExpansionPair, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = readExpansionPair.length := by
    simp [t, readExpansionPair, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [t, readExpansionPair, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [t, readExpansionPair, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [t, readExpansionPair, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [t, readExpansionPair, arithmeticStep, entry, running, one, Function.iterate_succ_apply']
  · simp [t, readExpansionPair, arithmeticStep, entry, running, one, Function.iterate_succ_apply', Nat.add_assoc]
  · intro r fromReg toReg cursorReg
    simp [t, readExpansionPair, arithmeticStep, entry, running, Function.iterate_succ_apply',
      Function.update_of_ne fromReg, Function.update_of_ne toReg, Function.update_of_ne cursorReg]

def expandOnePairBlock : List ArithmeticInstruction :=
  appendBlock readExpansionPair emitShortestPathBlock

def expandPairListBlock : List ArithmeticInstruction :=
  appendBlock beginPairCursor (countedLoopFromZero 6 37 35 expandOnePairBlock)

def pairExpansionPreserved : List ℕ := [3, 4, 5, 6, 26, 28, 33, 34, 35]

private structure PairExpansionProgress (input : ArithmeticState) (pairs : List (Fin G.n × Fin G.n))
    (prior : List (Fin G.q)) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 37 = i
  pairCursor : s.nr 36 = input.nr 34 + 2 * i
  fixed : ∀ r ∈ pairExpansionPreserved, s.nr r = input.nr r
  real : s.rm = input.rm
  low : ∀ address < input.nr 29, s.nm address = input.nm address
  paths : ∃ walks : List (List (Traversal G)),
    Expands G (pairs.take i) walks ∧ (∀ walk ∈ walks, walk.length < G.n) ∧
    s.nr 29 = input.nr 33 + (prior ++ walks.flatten.map Prod.fst).length ∧
    OccurrenceArray s.nm (input.nr 33) (prior ++ walks.flatten.map Prod.fst)

private theorem occurrencePointerAddressBound (target source : Fin G.n) :
    G.n * target.val + source.val < G.n * G.n := by
  have row : G.n * (target.val + 1) ≤ G.n * G.n :=
    Nat.mul_le_mul_left _ (Nat.succ_le_of_lt target.isLt)
  rw [Nat.mul_succ] at row
  exact (Nat.add_lt_add_left source.isLt _).trans_le row

theorem TightStoredRow.preservedBelow {table : DirectLinkTable G} {target : Fin G.n}
    {old fresh : ℕ → ℕ} {nextBase bound : ℕ} (row : TightStoredRow target table nextBase old)
    (fits : nextBase + G.n * G.n ≤ bound) (copies : ∀ a < bound, fresh a = old a) :
    TightStoredRow target table nextBase fresh := by
  intro source away
  obtain ⟨edge, starts, legal, tight, stored, decreases⟩ := row source away
  have below : nextBase + G.n * target.val + source.val < bound := by
    have within := occurrencePointerAddressBound target source
    omega
  exact ⟨edge, starts, legal, tight, (copies _ below).trans stored, decreases⟩

/-- Expand every encoded pair to a simple shortest path, appending its
link occurrences to the existing array. All source pair cells, raw link
records, and shortest-path pointers remain available below the cursor. -/
theorem expandPairListBlock_correct {rowOffsets distances : ℕ} {s : ArithmeticState}
    {table : DirectLinkTable G} (pairs : List (Fin G.n × Fin G.n)) (prior : List (Fin G.q))
    (connected : Connected G) (nonnegative : Nonnegative G) (frame : FloydFrame G.n rowOffsets distances s)
    (sound : DirectLinkTableSound table)
    (representative : DirectLinkRepresentatives G (tableChooses table))
    (rows : ∀ target, TightStoredRow target table (s.nr 26) s.nm)
    (count : s.nr 35 = pairs.length) (zero : s.nr 28 = 0)
    (initialCursor : s.nr 29 = s.nr 33 + prior.length)
    (encodedPairs : ExpansionPairArray s.nm (s.nr 34) pairs)
    (encodedPrior : OccurrenceArray s.nm (s.nr 33) prior)
    (pairsBelow : s.nr 34 + 2 * pairs.length ≤ s.nr 29)
    (rowsBelow : rowOffsets + G.n ≤ s.nr 29) (pointersBelow : s.nr 26 + G.n * G.n ≤ s.nr 29)
    (inputBelow : 2 + 3 * G.q ≤ s.nr 29)
    (tailCell : ∀ e : Fin G.q, s.nm (2 + 3 * e.val) = (G.tail e).val)
    (headCell : ∀ e : Fin G.q, s.nm (3 + 3 * e.val) = (G.head e).val)
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t steps paths, BlockRuns expandPairListBlock steps s t ∧
      steps ≤ pairs.length * (25 * G.n + 9) + 3 ∧ t.halted = false ∧
      Expands G pairs paths ∧ (∀ path ∈ paths, path.length < G.n) ∧
      t.nr 29 = s.nr 33 + (prior ++ paths.flatten.map Prod.fst).length ∧
      OccurrenceArray t.nm (s.nr 33) (prior ++ paths.flatten.map Prod.fst) ∧
      (∀ r ∈ pairExpansionPreserved, t.nr r = s.nr r) ∧ t.rm = s.rm ∧
      ∀ a < s.nr 29, t.nm a = s.nm a := by
  let staged := {s with pc := 0, nr := Function.update s.nr 36 (s.nr 34)}
  let inv := PairExpansionProgress s pairs prior
  have initial : inv 0 {staged with pc := 0, nr := Function.update staged.nr 37 0} := by
    refine ⟨rfl, running, by simp, by simp [staged], ?_, rfl, fun _ _ => rfl, ?_⟩
    · intro r selected
      have notRead : r ≠ 36 := by rintro rfl; simp [pairExpansionPreserved] at selected
      have notCount : r ≠ 37 := by rintro rfl; simp [pairExpansionPreserved] at selected
      simp [staged, Function.update_of_ne notRead, Function.update_of_ne notCount]
    · exact ⟨[], List.Forall₂.nil, by simp, by simpa [staged] using initialCursor,
        by simpa using encodedPrior⟩
  have control (i : ℕ) (m : ArithmeticState) (ok : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 37 = i ∧ m.nr 35 = pairs.length :=
    ⟨ok.entry, ok.running, ok.index, (ok.fixed 35 (by decide)).trans count⟩
  have step (i : ℕ) (more : i < pairs.length) (m : ArithmeticState) (ok : inv i m) :
      ∃ t steps, steps ≤ 25 * G.n + 6 ∧ BlockRuns expandOnePairBlock steps m t ∧
        t.halted = false ∧ inv (i + 1)
          {t with pc := 0, nr := Function.update t.nr 37 (t.nr 37 + t.nr 6)} := by
    obtain ⟨walks, priorPaths, lengthBounds, priorCursor, priorArray⟩ := ok.paths
    let pair := pairs[i]
    have protectedEnd : s.nr 29 ≤ m.nr 29 := by
      rw [initialCursor, priorCursor]
      simp
    have mOne := (ok.fixed 6 (by decide)).trans frame.one
    obtain ⟨read, reads, readReady, readNat, readReal, readSource, readTarget, readCursor, readFixed⟩ :=
      readExpansionPair_correct m ok.entry ok.running mOne
    let routeEntry := {read with pc := 0}
    have readKeeps (r : ℕ) (preserved : r ∈ pairExpansionPreserved) : read.nr r = m.nr r := by
      apply readFixed <;> intro eq <;> simp [pairExpansionPreserved, eq] at preserved
    have readOne := (readKeeps 6 (by decide)).trans mOne
    have readZero := ((readKeeps 28 (by decide)).trans (ok.fixed 28 (by decide))).trans zero
    have currentCursor : read.nr 29 = m.nr 29 := readFixed 29 (by decide) (by decide) (by decide)
    have readBase : read.nr 26 = s.nr 26 := (readKeeps 26 (by decide)).trans (ok.fixed 26 (by decide))
    have sourceBelow : s.nr 34 + 2 * i < s.nr 29 := by omega
    have targetBelow : s.nr 34 + 2 * i + 1 < s.nr 29 := by omega
    have observedSource : read.nr 9 = pair.1.val := by
      rw [readSource, ok.pairCursor, ok.low _ sourceBelow]
      exact (encodedPairs i more).1
    have observedTarget : read.nr 7 = pair.2.val := by
      rw [readTarget, ok.pairCursor, ok.low _ targetBelow]
      exact (encodedPairs i more).2
    have liveFrame : FloydFrame G.n rowOffsets distances routeEntry := by
      refine ⟨((readKeeps 3 (by decide)).trans (ok.fixed 3 (by decide))).trans frame.tableBase,
        ((readKeeps 4 (by decide)).trans (ok.fixed 4 (by decide))).trans frame.matrixBase,
        ((readKeeps 5 (by decide)).trans (ok.fixed 5 (by decide))).trans frame.dimension,
        readOne, ?_⟩
      intro j hj
      change read.nm (rowOffsets + j) = _
      rw [readNat, ok.low _ ((Nat.add_lt_add_left hj _).trans_le rowsBelow)]
      exact frame.rows j hj
    have liveRow : TightStoredRow pair.2 table (routeEntry.nr 26) routeEntry.nm := by
      change TightStoredRow pair.2 table (read.nr 26) read.nm
      rw [readBase, readNat]
      exact (rows pair.2).preservedBelow pointersBelow ok.low
    have liveRowsBelow : rowOffsets + G.n ≤ routeEntry.nr 29 := by
      change _ ≤ read.nr 29
      rw [currentCursor]
      exact rowsBelow.trans protectedEnd
    have livePointersBelow : routeEntry.nr 26 + G.n * G.n ≤ routeEntry.nr 29 := by
      change read.nr 26 + _ ≤ read.nr 29
      rw [readBase, currentCursor]
      exact pointersBelow.trans protectedEnd
    have liveInputBelow : 2 + 3 * G.q ≤ routeEntry.nr 29 := by
      change _ ≤ read.nr 29
      rw [currentCursor]
      exact inputBelow.trans protectedEnd
    have liveTail (e : Fin G.q) : routeEntry.nm (2 + 3 * e.val) = (G.tail e).val := by
      change read.nm _ = _
      have eBelow := e.isLt
      rw [readNat, ok.low _ (by omega)]
      exact tailCell e
    have liveHead (e : Fin G.q) : routeEntry.nm (3 + 3 * e.val) = (G.head e).val := by
      change read.nm _ = _
      have eBelow := e.isLt
      rw [readNat, ok.low _ (by omega)]
      exact headCell e
    obtain ⟨wrote, path, used, expands, usedBound, wroteReady, shortest, pathBound, _, endCursor,
      pathCells, stableInput, wroteReal, preserved⟩ :=
      emitShortestPathBlock_correct connected nonnegative sound representative liveRow liveFrame
        observedSource observedTarget readZero liveRowsBelow livePointersBelow liveInputBelow
        liveTail liveHead rfl readReady
    let t := relocateState readExpansionPair.length wrote
    have keepPairReg (r : ℕ) (present : r ∈ pairExpansionPreserved) : t.nr r = m.nr r := by
      exact (preserved r (by simp [pairExpansionPreserved, pathEmitFixed] at present ⊢; omega)).trans
        (readKeeps r present)
    have oneOut : t.nr 6 = 1 := (keepPairReg 6 (by decide)).trans mOne
    have indexOut : t.nr 37 = i := (preserved 37 (by decide)).trans
      ((readFixed 37 (by decide) (by decide) (by decide)).trans ok.index)
    have sourceMem (address : ℕ) (earlier : address < m.nr 29) : t.nm address = m.nm address := by
      have beforeWrite : address < routeEntry.nr 29 := by
        change address < read.nr 29
        rwa [currentCursor]
      exact (stableInput address beforeWrite).trans (congrFun readNat address)
    have past : OccurrenceArray t.nm (s.nr 33) (prior ++ walks.flatten.map Prod.fst) :=
      priorArray.preservedBelow (by rw [priorCursor]) sourceMem
    have new : OccurrenceArray t.nm (s.nr 33 + (prior ++ walks.flatten.map Prod.fst).length)
        (path.map Prod.fst) := by
      have atCursor : routeEntry.nr 29 = s.nr 33 + (prior ++ walks.flatten.map Prod.fst).length :=
        currentCursor.trans priorCursor
      change OccurrenceArray wrote.nm _ _
      have stored := occurrenceArray_ofTraversals pathCells
      rwa [atCursor] at stored
    have combined := past.append new
    have nextPaths : Expands G (pairs.take (i + 1)) (walks ++ [path]) := by
      rw [List.take_succ_eq_append_getElem more]
      exact List.rel_append priorPaths (List.Forall₂.cons shortest List.Forall₂.nil)
    have bound : 4 + used ≤ 25 * G.n + 6 := by omega
    refine ⟨t, 4 + used, bound, reads.append expands, wroteReady, ?_⟩
    refine ⟨rfl, wroteReady, by simp [t, indexOut, oneOut], ?_, ?_,
      wroteReal.trans (readReal.trans ok.real), ?_, ?_⟩
    · have pairAdvance : t.nr 36 = s.nr 34 + 2 * (i + 1) := by
        have observed : t.nr 36 = read.nr 36 := preserved 36 (by decide)
        rw [observed, readCursor, ok.pairCursor]
        omega
      simpa [t] using pairAdvance
    · intro r present
      have noReset : r ≠ 37 := by rintro rfl; simp [pairExpansionPreserved] at present
      exact (Function.update_of_ne noReset _ _).trans ((keepPairReg r present).trans (ok.fixed r present))
    · intro address below
      exact (sourceMem address (below.trans_le protectedEnd)).trans (ok.low address below)
    · refine ⟨walks ++ [path], nextPaths, ?_, ?_, ?_⟩
      · intro previous included
        rcases List.mem_append.mp included with earlier | last
        · exact lengthBounds previous earlier
        · exact (List.mem_singleton.mp last).symm ▸ pathBound
      · change wrote.nr 29 = _
        simpa [routeEntry, currentCursor, priorCursor, List.flatten_append,
          List.map_append, List.append_assoc, Nat.add_assoc] using endCursor
      · simpa [List.flatten_append, List.map_append, List.append_assoc] using combined
  obtain ⟨last, elapsed, done, cap, executes⟩ :=
    countedLoopFromZero_bounded 6 37 35 pairs.length (25 * G.n + 6) expandOnePairBlock inv
      (s := staged) rfl running initial control step
  obtain ⟨walks, pathProof, pathBounds, cursor, array⟩ := done.paths
  have setup := beginPairCursor_runs s entry running zero
  have totalBound : 1 + elapsed ≤ pairs.length * (25 * G.n + 9) + 3 := by
    rw [show 25 * G.n + 6 + 3 = 25 * G.n + 9 by omega] at cap
    omega
  exact ⟨_, 1 + elapsed, walks, setup.append executes, totalBound, done.running,
    by simpa using pathProof, pathBounds, cursor, array, done.fixed, done.real, done.low⟩

end VehicleRoutingSurvey.Routing
end RppSource_PairExpansion

/-! runtime/ConnectorOccurrences.lean -/
section RppSource_ConnectorOccurrences
namespace VehicleRoutingSurvey.Routing

def connectorOccurrencesBlock : List ArithmeticInstruction :=
  appendBlock requiredOccurrenceBlock expandPairListBlock

/-- Produce the base and expanded connector occurrences before parity
is computed. The tree pair list is supplied by the preceding stage. -/
theorem connectorOccurrencesBlock_correct {I : Service} {rowOffsets distances : ℕ}
    {table : DirectLinkTable I.graph} {s : ArithmeticState}
    (pairs : List (Fin I.graph.n × Fin I.graph.n)) (rural : Rural I)
    (frame : FloydFrame I.graph.n rowOffsets distances s)
    (sound : DirectLinkTableSound table)
    (representative : DirectLinkRepresentatives I.graph (tableChooses table))
    (rows : ∀ target, TightStoredRow target table (s.nr 26) s.nm)
    (count : s.nr 35 = pairs.length)
    (encodedPairs : ExpansionPairArray s.nm (s.nr 34) pairs)
    (rawInput : ∀ a < 2 + 3 * I.graph.q, s.nm a = (ruralNatInput I)[a]?.getD 0)
    (pairBound : s.nr 34 + 2 * pairs.length ≤ s.nr 33)
    (rowBound : rowOffsets + I.graph.n ≤ s.nr 33)
    (pointerBound : s.nr 26 + I.graph.n * I.graph.n ≤ s.nr 33)
    (rawBound : 2 + 3 * I.graph.q ≤ s.nr 33)
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t steps paths, BlockRuns connectorOccurrencesBlock steps s t ∧
      steps ≤ 11 * I.graph.q + pairs.length * (25 * I.graph.n + 9) + 9 ∧
      t.halted = false ∧ Expands I.graph pairs paths ∧
      (∀ path ∈ paths, path.length < I.graph.n) ∧
      t.nr 28 = 0 ∧ t.nr 29 = s.nr 33 + (requiredLinkList I ++ paths.flatten.map Prod.fst).length ∧
      OccurrenceArray t.nm (s.nr 33) (requiredLinkList I ++ paths.flatten.map Prod.fst) ∧
      (∀ r ∈ pairExpansionPreserved, r ≠ 28 → t.nr r = s.nr r) ∧
      t.rm = s.rm ∧ ∀ a < s.nr 33, t.nm a = s.nm a := by
  obtain ⟨b, scans, baseRun, baseBound, baseReady, zero, cursor, fixed, real, early, baseArray⟩ :=
    requiredOccurrenceBlock_correct entry running frame.one rawBound rawInput
  let expandEntry := {b with pc := 0}
  have liveFrame : FloydFrame I.graph.n rowOffsets distances expandEntry := by
    refine ⟨(fixed 3 (by decide)).trans frame.tableBase, (fixed 4 (by decide)).trans frame.matrixBase,
      (fixed 5 (by decide)).trans frame.dimension, (fixed 6 (by decide)).trans frame.one, ?_⟩
    intro j hj
    exact (early _ ((Nat.add_lt_add_left hj _).trans_le rowBound)).trans (frame.rows j hj)
  have liveRows (target : Fin I.graph.n) :
      TightStoredRow target table (expandEntry.nr 26) expandEntry.nm := by
    change TightStoredRow target table (b.nr 26) b.nm
    rw [fixed 26 (by decide)]
    exact (rows target).preservedBelow pointerBound early
  have cursorStart : expandEntry.nr 29 = expandEntry.nr 33 + (requiredLinkList I).length := by
    change b.nr 29 = b.nr 33 + _
    rwa [fixed 33 (by decide)]
  have pairInput : ExpansionPairArray expandEntry.nm (expandEntry.nr 34) pairs := by
    change ExpansionPairArray b.nm (b.nr 34) pairs
    rw [fixed 34 (by decide)]
    intro i hi
    exact ⟨(early _ (by omega)).trans (encodedPairs i hi).1,
      (early _ (by omega)).trans (encodedPairs i hi).2⟩
  have prior : OccurrenceArray expandEntry.nm (expandEntry.nr 33) (requiredLinkList I) := by
    change OccurrenceArray b.nm (b.nr 33) _
    rwa [fixed 33 (by decide)]
  have startAfter : s.nr 33 ≤ expandEntry.nr 29 := by change _ ≤ b.nr 29; rw [cursor]; omega
  have pairsBelow : expandEntry.nr 34 + 2 * pairs.length ≤ expandEntry.nr 29 := by
    change b.nr 34 + _ ≤ b.nr 29
    rw [fixed 34 (by decide)]
    exact pairBound.trans startAfter
  have pointersBelow : expandEntry.nr 26 + I.graph.n * I.graph.n ≤ expandEntry.nr 29 := by
    change b.nr 26 + _ ≤ b.nr 29
    rw [fixed 26 (by decide)]
    exact pointerBound.trans startAfter
  have keptRaw : ∀ a < 2 + 3 * I.graph.q, expandEntry.nm a = (ruralNatInput I)[a]?.getD 0 :=
    fun a ha => (early a (ha.trans_le rawBound)).trans (rawInput a ha)
  obtain ⟨p, expands, paths, pathRun, pathCost, ready, valid, pathLen, finalCursor,
      finalArray, finalFixed, finalReal, finalEarly⟩ :=
    expandPairListBlock_correct pairs (requiredLinkList I) rural.1 rural.2.1 liveFrame sound
      representative liveRows ((fixed 35 (by decide)).trans count) zero cursorStart pairInput prior
      pairsBelow (rowBound.trans startAfter) pointersBelow (rawBound.trans startAfter)
      (fun edge => (ruralInputs_preserveLinkEndpoints keptRaw edge).1)
      (fun edge => (ruralInputs_preserveLinkEndpoints keptRaw edge).2) rfl baseReady
  let final := relocateState requiredOccurrenceBlock.length p
  have completed := baseRun.append pathRun
  refine ⟨final, scans + expands, paths, completed, by omega, ready, valid, pathLen,
    (finalFixed 28 (by decide)).trans zero, ?_, ?_, ?_, finalReal.trans real, ?_⟩
  · change p.nr 29 = _
    have original := finalCursor
    change p.nr 29 = b.nr 33 + _ at original
    rwa [fixed 33 (by decide)] at original
  · change OccurrenceArray p.nm (s.nr 33) _
    have original := finalArray
    change OccurrenceArray p.nm (b.nr 33) _ at original
    rwa [fixed 33 (by decide)] at original
  · intro r hr notZero
    have original : r ∈ requiredOccurrencePreserved := by
      simp [pairExpansionPreserved] at hr
      simp [requiredOccurrencePreserved]
      omega
    exact (finalFixed r hr).trans (fixed r original)
  · exact fun a ha => (finalEarly a (ha.trans_le startAfter)).trans (early a ha)

end VehicleRoutingSurvey.Routing
end RppSource_ConnectorOccurrences

/-! matching/WeightedCacheRAM.lean -/
section RppSource_WeightedCacheRAM
namespace VehicleRoutingSurvey.Routing

/-- Merge one least-slack candidate into a cache cell. Natural register 0 is the new edge
identifier, and register 1 is the current one. Zero means empty. Real registers 0 and 1
carry their slacks. An equal-slack edge keeps the earlier representative. -/
def mergeSlackEntryBlock : List ArithmeticInstruction :=
  [.natConst 2 0, .natBranch 0 2 7 2, .natBranch 1 2 4 3, .realBranch 1 0 7 4,
    .natAdd 1 0 2, .realConst 2 0, .realAdd 1 0 2]

def mergeSlackEntryTakesCandidate (s : ArithmeticState) : Prop :=
  s.nr 0 ≠ 0 ∧ (s.nr 1 = 0 ∨ s.rr 0 < s.rr 1)

private theorem mergeSlackEntryBlock_absent (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (absent : s.nr 0 = 0) :
    (arithmeticStep mergeSlackEntryBlock)^[2] s = {s with pc := 7, nr := Function.update s.nr 2 0} := by
  simp [mergeSlackEntryBlock, arithmeticStep, Function.iterate_succ_apply', entry, running, absent]

private theorem mergeSlackEntryBlock_empty (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (available : s.nr 0 ≠ 0) (empty : s.nr 1 = 0) :
    (arithmeticStep mergeSlackEntryBlock)^[6] s =
      {s with
        pc := 7
        nr := Function.update (Function.update s.nr 2 0) 1 (s.nr 0)
        rr := Function.update (Function.update s.rr 2 0) 1 (s.rr 0)} := by
  simp [mergeSlackEntryBlock, arithmeticStep, Function.iterate_succ_apply', entry, running, available, empty]

private theorem mergeSlackEntryBlock_keep (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (available : s.nr 0 ≠ 0) (occupied : s.nr 1 ≠ 0)
    (noBetter : s.rr 1 ≤ s.rr 0) :
    (arithmeticStep mergeSlackEntryBlock)^[4] s = {s with pc := 7, nr := Function.update s.nr 2 0} := by
  simp [mergeSlackEntryBlock, arithmeticStep, Function.iterate_succ_apply', entry, running, available, occupied,
    noBetter]

private theorem mergeSlackEntryBlock_replace (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (available : s.nr 0 ≠ 0) (occupied : s.nr 1 ≠ 0)
    (better : s.rr 0 < s.rr 1) :
    (arithmeticStep mergeSlackEntryBlock)^[7] s =
      {s with
        pc := 7
        nr := Function.update (Function.update s.nr 2 0) 1 (s.nr 0)
        rr := Function.update (Function.update s.rr 2 0) 1 (s.rr 0)} := by
  simp [mergeSlackEntryBlock, arithmeticStep, Function.iterate_succ_apply', entry, running, available, occupied,
    not_le.mpr better]

/-- One cache comparison uses at most seven instructions, with the remaining memory intact. -/
theorem mergeSlackEntryBlock_spec (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ steps ≤ 7, let result := (arithmeticStep mergeSlackEntryBlock)^[steps] s
      BlockRuns mergeSlackEntryBlock steps s result ∧
      (mergeSlackEntryTakesCandidate s → result.nr 1 = s.nr 0 ∧ result.rr 1 = s.rr 0) ∧
      (¬ mergeSlackEntryTakesCandidate s → result.nr 1 = s.nr 1 ∧ result.rr 1 = s.rr 1) ∧
      result.nm = s.nm ∧ result.rm = s.rm := by
  classical
  by_cases absent : s.nr 0 = 0
  · refine ⟨2, by decide, ?_⟩
    rw [mergeSlackEntryBlock_absent s entry running absent]
    exact ⟨BlockRuns.of_running_exit (mergeSlackEntryBlock_absent s entry running absent) running rfl,
      by simp [mergeSlackEntryTakesCandidate, absent]⟩
  by_cases empty : s.nr 1 = 0
  · refine ⟨6, by decide, ?_⟩
    rw [mergeSlackEntryBlock_empty s entry running absent empty]
    exact ⟨BlockRuns.of_running_exit (mergeSlackEntryBlock_empty s entry running absent empty) running rfl,
      by simp [mergeSlackEntryTakesCandidate, absent, empty]⟩
  by_cases better : s.rr 0 < s.rr 1
  · refine ⟨7, by decide, ?_⟩
    rw [mergeSlackEntryBlock_replace s entry running absent empty better]
    exact ⟨BlockRuns.of_running_exit (mergeSlackEntryBlock_replace s entry running absent empty better) running rfl,
      by simp [mergeSlackEntryTakesCandidate, absent, empty, better]⟩
  · refine ⟨4, by decide, ?_⟩
    rw [mergeSlackEntryBlock_keep s entry running absent empty (le_of_not_gt better)]
    exact ⟨BlockRuns.of_running_exit (mergeSlackEntryBlock_keep s entry running absent empty (le_of_not_gt better)) running rfl,
      by simp [mergeSlackEntryTakesCandidate, absent, empty, better]⟩

end VehicleRoutingSurvey.Routing
end RppSource_WeightedCacheRAM

/-! matching/WeightedDeltaRAM.lean -/
section RppSource_WeightedDeltaRAM
namespace VehicleRoutingSurvey.Routing

/-- Real registers 0 and 3 contain slack and rate. Divide for a rising constraint, or
clear the candidate edge identifier for a constraint that imposes no upper bound. -/
def prepareDualBoundBlock : List ArithmeticInstruction :=
  [.realConst 4 0, .realBranch 3 4 2 4, .natConst 0 0, .jump 6, .realDiv 0 0 3, .jump 6]

private noncomputable def preparedDualBound (s : ArithmeticState) : ArithmeticState :=
  let initial := {s with pc := 6, rr := Function.update s.rr 4 0}
  if s.rr 3 ≤ 0 then {initial with nr := Function.update initial.nr 0 0}
  else {initial with rr := Function.update initial.rr 0 (s.rr 0 / s.rr 3)}

private theorem prepareDualBoundBlock_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) : BlockRuns prepareDualBoundBlock 4 s (preparedDualBound s) := by
  classical
  have instructionResult : (arithmeticStep prepareDualBoundBlock)^[4] s = preparedDualBound s := by
    by_cases nonpositive : s.rr 3 ≤ 0 <;>
      simp [prepareDualBoundBlock, arithmeticStep, Function.iterate_succ_apply', entry, running,
        preparedDualBound, nonpositive]
  apply BlockRuns.of_running_exit instructionResult
  · by_cases nonpositive : s.rr 3 ≤ 0 <;> simp [preparedDualBound, nonpositive, running]
  · by_cases nonpositive : s.rr 3 ≤ 0 <;> simp [preparedDualBound, nonpositive, prepareDualBoundBlock]

def mergeDualBoundBlock : List ArithmeticInstruction := appendBlock prepareDualBoundBlock mergeSlackEntryBlock

def mergeDualBoundTakesCandidate (s : ArithmeticState) : Prop :=
  s.nr 0 ≠ 0 ∧ 0 < s.rr 3 ∧ (s.nr 1 = 0 ∨ s.rr 0 / s.rr 3 < s.rr 1)

/-- A candidate is normalized to its slack divided by its positive rate and compared to
the previous minimum in at most eleven instructions. -/
theorem mergeDualBoundBlock_spec (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ steps ≤ 11, let result := (arithmeticStep mergeDualBoundBlock)^[steps] s
      BlockRuns mergeDualBoundBlock steps s result ∧
      (mergeDualBoundTakesCandidate s → result.nr 1 = s.nr 0 ∧ result.rr 1 = s.rr 0 / s.rr 3) ∧
      (¬mergeDualBoundTakesCandidate s → result.nr 1 = s.nr 1 ∧ result.rr 1 = s.rr 1) ∧
      result.nm = s.nm ∧ result.rm = s.rm := by
  classical
  let middle := {preparedDualBound s with pc := 0}
  have middleLive : middle.halted = false := by
    by_cases nonpositive : s.rr 3 ≤ 0 <;> simp [middle, preparedDualBound, nonpositive, running]
  have unchanged : middle.nr 1 = s.nr 1 ∧ middle.rr 1 = s.rr 1 ∧ middle.nm = s.nm ∧ middle.rm = s.rm := by
    by_cases nonpositive : s.rr 3 ≤ 0 <;> simp [middle, preparedDualBound, nonpositive]
  have equivalent : mergeSlackEntryTakesCandidate middle ↔ mergeDualBoundTakesCandidate s := by
    by_cases nonpositive : s.rr 3 ≤ 0
    · simp [middle, preparedDualBound, mergeSlackEntryTakesCandidate, mergeDualBoundTakesCandidate,
        nonpositive, not_lt_of_ge nonpositive]
    · simp [middle, preparedDualBound, mergeSlackEntryTakesCandidate, mergeDualBoundTakesCandidate,
        nonpositive, lt_of_not_ge nonpositive]
  obtain ⟨steps, short, compared, chosen, kept, natMem, realMem⟩ := mergeSlackEntryBlock_spec middle rfl middleLive
  have joined := BlockRuns.append (prepareDualBoundBlock_spec s entry running) compared
  refine ⟨4 + steps, by omega, ?_⟩
  dsimp only
  rw [mergeDualBoundBlock, joined.run]
  refine ⟨joined, ?_, ?_, natMem.trans unchanged.2.2.1, realMem.trans unchanged.2.2.2⟩
  · intro take
    have found := chosen (equivalent.mpr take)
    have positive : 0 < s.rr 3 := take.2.1
    have registers : middle.nr 0 = s.nr 0 ∧ middle.rr 0 = s.rr 0 / s.rr 3 := by
      simp [middle, preparedDualBound, not_le.mpr positive]
    exact ⟨found.1.trans registers.1, found.2.trans registers.2⟩
  · intro skip
    have found := kept (fun take => skip (equivalent.mp take))
    exact ⟨found.1.trans unchanged.1, found.2.trans unchanged.2.1⟩

end VehicleRoutingSurvey.Routing
end RppSource_WeightedDeltaRAM

/-! matching/WeightedReadDeltaRAM.lean -/
section RppSource_WeightedReadDeltaRAM
namespace VehicleRoutingSurvey.Routing

def naturalDestination : ArithmeticInstruction → ℕ
  | .natAdd dst _ _ | .natSub dst _ _ | .natConst dst _ | .natLoad dst _ => dst
  | _ => 0

private theorem arithmeticStep_keeps_register {p : List ArithmeticInstruction}
    {s : ArithmeticState} {r : ℕ} (otherWrites : ∀ ins ∈ p, naturalDestination ins ≠ r) :
    (arithmeticStep p s).nr r = s.nr r := by
  by_cases halted : s.halted = true
  · simp [arithmeticStep, halted]
  cases fetch : p[s.pc]? with
  | none => simp [arithmeticStep, halted, fetch]
  | some ins =>
    have writes := otherWrites ins (List.mem_of_getElem? fetch)
    cases ins <;> simp (disch := omega) [arithmeticStep, halted, fetch, naturalDestination] at writes ⊢

theorem arithmeticRun_keeps_register {p : List ArithmeticInstruction}
    {r : ℕ} (otherWrites : ∀ ins ∈ p, naturalDestination ins ≠ r) (s : ArithmeticState) (steps : ℕ) :
    ((arithmeticStep p)^[steps] s).nr r = s.nr r := by
  induction steps with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', arithmeticStep_keeps_register otherWrites, ih]

theorem arithmeticRun_keeps_high_register {p : List ArithmeticInstruction}
    {r : ℕ} (lowWrites : ∀ ins ∈ p, naturalDestination ins < r) (s : ArithmeticState) (steps : ℕ) :
    ((arithmeticStep p)^[steps] s).nr r = s.nr r := by
  exact arithmeticRun_keeps_register (fun ins h => (lowWrites ins h).ne) s steps

theorem naturalDestination_ne_of_list {p : List ArithmeticInstruction} {r : ℕ}
    (written : List ℕ) (checked : p.all (fun ins => decide (naturalDestination ins ∈ written)) = true)
    (away : r ∉ written) : ∀ ins ∈ p, naturalDestination ins ≠ r := by
  intro ins present same
  apply away
  exact same ▸ of_decide_eq_true (List.all_eq_true.mp checked ins present)

theorem arithmeticRun_keeps_from_destination_list {p : List ArithmeticInstruction} {r : ℕ}
    (written : List ℕ) (checked : p.all (fun ins => decide (naturalDestination ins ∈ written)) = true)
    (away : r ∉ written) (s : ArithmeticState) (steps : ℕ) :
    ((arithmeticStep p)^[steps] s).nr r = s.nr r :=
  arithmeticRun_keeps_register (naturalDestination_ne_of_list written checked away) s steps

def realDestination : ArithmeticInstruction → ℕ
  | .realConst dst _ | .realAdd dst _ _ | .realSub dst _ _ | .realMul dst _ _
  | .realDiv dst _ _ | .realLoad dst _ => dst
  | _ => 0

private theorem arithmeticStep_keeps_real_register {p : List ArithmeticInstruction}
    {s : ArithmeticState} {r : ℕ} (otherWrites : ∀ ins ∈ p, realDestination ins ≠ r) :
    (arithmeticStep p s).rr r = s.rr r := by
  by_cases halted : s.halted = true
  · simp [arithmeticStep, halted]
  cases fetch : p[s.pc]? with
  | none => simp [arithmeticStep, halted, fetch]
  | some ins =>
    have writes := otherWrites ins (List.mem_of_getElem? fetch)
    cases ins <;> simp (disch := omega) [arithmeticStep, halted, fetch, realDestination] at writes ⊢

theorem arithmeticRun_keeps_real_from_destination_list {p : List ArithmeticInstruction} {r : ℕ}
    (written : List ℕ) (checked : p.all (fun ins => decide (realDestination ins ∈ written)) = true)
    (away : r ∉ written) (s : ArithmeticState) (steps : ℕ) :
    ((arithmeticStep p)^[steps] s).rr r = s.rr r := by
  have avoids : ∀ ins ∈ p, realDestination ins ≠ r := by
    intro ins present same
    apply away
    exact same ▸ of_decide_eq_true (List.all_eq_true.mp checked ins present)
  induction steps with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', arithmeticStep_keeps_real_register avoids, ih]

@[simp] theorem naturalDestination_relocate (offset : ℕ) (ins : ArithmeticInstruction) :
    naturalDestination (relocateInstruction offset ins) = naturalDestination ins := by
  cases ins <;> rfl

theorem forall_naturalDestination_append (p : ℕ → Prop) (a b : List ArithmeticInstruction) :
    (∀ ins ∈ appendBlock a b, p (naturalDestination ins)) ↔
      (∀ ins ∈ a, p (naturalDestination ins)) ∧ ∀ ins ∈ b, p (naturalDestination ins) := by
  simp only [appendBlock, List.forall_mem_append, List.forall_mem_map, naturalDestination_relocate]

theorem forall_naturalDestination_counted (p : ℕ → Prop) (one index limit : ℕ)
    (body : List ArithmeticInstruction) :
    (∀ ins ∈ countedLoop one index limit body, p (naturalDestination ins)) ↔
      p 0 ∧ p index ∧ ∀ ins ∈ body, p (naturalDestination ins) := by
  simp only [countedLoop, List.forall_mem_append, List.forall_mem_map, naturalDestination_relocate]
  simp [naturalDestination, and_assoc, and_left_comm, and_comm]

theorem forall_naturalDestination_countedFromZero (p : ℕ → Prop) (one index limit : ℕ)
    (body : List ArithmeticInstruction) :
    (∀ ins ∈ countedLoopFromZero one index limit body, p (naturalDestination ins)) ↔
      p 0 ∧ p index ∧ ∀ ins ∈ body, p (naturalDestination ins) := by
  simp only [countedLoopFromZero, forall_naturalDestination_append, forall_naturalDestination_counted]
  simp [naturalDestination, and_assoc, and_left_comm, and_comm]

theorem forall_naturalDestination_unlessEqual (p : ℕ → Prop) (x y : ℕ)
    (body : List ArithmeticInstruction) :
    (∀ ins ∈ branchOnUnequal x y body, p (naturalDestination ins)) ↔
      p 0 ∧ ∀ ins ∈ body, p (naturalDestination ins) := by
  change (∀ ins ∈ [.natBranch x y 1 2, .natBranch y x (3 + body.length) 3, .jump 3] ++
      body.map (relocateInstruction 3), p (naturalDestination ins)) ↔ _
  simp only [List.forall_mem_append, List.forall_mem_map, naturalDestination_relocate]
  simp [naturalDestination]

theorem no_halt_from_running {p : List ArithmeticInstruction} {s : ArithmeticState} {steps : ℕ}
    (running : s.halted = false) (safe : ∀ k < steps, ((arithmeticStep p)^[k] s).pc < p.length)
    (notHalt : ArithmeticInstruction.halt ∉ p) : ((arithmeticStep p)^[steps] s).halted = false := by
  induction steps with
  | zero => exact running
  | succ k ih =>
    let before := (arithmeticStep p)^[k] s
    have entry : before.pc < p.length := safe k (Nat.lt_succ_self k)
    have live : before.halted = false := ih (fun j earlier => safe j (earlier.trans (Nat.lt_succ_self k)))
    have fetch : p[before.pc]? = some p[before.pc] := List.getElem?_eq_getElem entry
    have selected : p[before.pc] ∈ p := List.getElem_mem entry
    rw [Function.iterate_succ_apply']
    change (arithmeticStep p before).halted = false
    generalize eq : p[before.pc] = instr at fetch selected
    cases instr <;> simp [arithmeticStep, live, fetch, notHalt] at selected ⊢

private theorem mergeDualBoundBlock_low_writes (r : ℕ) (high : 3 ≤ r) :
    ∀ ins ∈ mergeDualBoundBlock, naturalDestination ins < r := by
  simp [mergeDualBoundBlock, appendBlock, prepareDualBoundBlock, mergeSlackEntryBlock,
    relocateInstruction, naturalDestination] <;> omega

private theorem mergeDualBoundBlock_no_halt : ArithmeticInstruction.halt ∉ mergeDualBoundBlock := by
  simp [mergeDualBoundBlock, appendBlock, prepareDualBoundBlock, mergeSlackEntryBlock, relocateInstruction]

/-- Read one cached event. Natural registers 3, 4, and 5 address the identifier, slack, and
rate arrays. Register 7 is the current index. The identifier is zero for an empty slot. -/
def readDualBoundBlock : List ArithmeticInstruction :=
  [.natAdd 6 3 7, .natLoad 0 6, .natAdd 6 4 7, .realLoad 0 6, .natAdd 6 5 7, .realLoad 3 6]

private def dualBoundReadState (s : ArithmeticState) : ArithmeticState :=
  let idAddress := s.nr 3 + s.nr 7
  let slackAddress := s.nr 4 + s.nr 7
  let rateAddress := s.nr 5 + s.nr 7
  {s with
    pc := 6
    nr := Function.update (Function.update (Function.update (Function.update s.nr 6 idAddress)
      0 (s.nm idAddress)) 6 slackAddress) 6 rateAddress
    rr := Function.update (Function.update s.rr 0 (s.rm slackAddress)) 3 (s.rm rateAddress)}

private theorem readDualBoundBlock_spec (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) :
    BlockRuns readDualBoundBlock 6 s (dualBoundReadState s) := by
  apply BlockRuns.of_running_exit
  · simp [dualBoundReadState, arithmeticStep, readDualBoundBlock, Function.iterate_succ_apply', entry, running]
  · exact running
  · rfl

def considerDualBoundBlock : List ArithmeticInstruction := appendBlock readDualBoundBlock mergeDualBoundBlock

def considerDualBoundTakesCandidate (s : ArithmeticState) : Prop :=
  s.nm (s.nr 3 + s.nr 7) ≠ 0 ∧ 0 < s.rm (s.nr 5 + s.nr 7) ∧
    (s.nr 1 = 0 ∨ s.rm (s.nr 4 + s.nr 7) / s.rm (s.nr 5 + s.nr 7) < s.rr 1)

/-- Read and consider one cached event in at most seventeen instructions. -/
theorem considerDualBoundBlock_spec (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ steps ≤ 17, let result := (arithmeticStep considerDualBoundBlock)^[steps] s
      BlockRuns considerDualBoundBlock steps s result ∧ result.halted = false ∧
      (considerDualBoundTakesCandidate s → result.nr 1 = s.nm (s.nr 3 + s.nr 7) ∧
        result.rr 1 = s.rm (s.nr 4 + s.nr 7) / s.rm (s.nr 5 + s.nr 7)) ∧
      (¬considerDualBoundTakesCandidate s → result.nr 1 = s.nr 1 ∧ result.rr 1 = s.rr 1) ∧
      result.nm = s.nm ∧ result.rm = s.rm ∧ ∀ r, 3 ≤ r → r ≠ 6 → result.nr r = s.nr r := by
  let middle := {dualBoundReadState s with pc := 0}
  have takes : mergeDualBoundTakesCandidate middle ↔ considerDualBoundTakesCandidate s := by
    simp [middle, dualBoundReadState, mergeDualBoundTakesCandidate, considerDualBoundTakesCandidate]
  obtain ⟨steps, bounded, merged, chosen, kept, natMem, realMem⟩ := mergeDualBoundBlock_spec middle rfl running
  have joined := BlockRuns.append (readDualBoundBlock_spec s entry running) merged
  have staysLive := no_halt_from_running (s := middle) running merged.inside mergeDualBoundBlock_no_halt
  refine ⟨6 + steps, by omega, ?_⟩
  dsimp only
  rw [considerDualBoundBlock, joined.run]
  refine ⟨joined, staysLive, ?_, ?_, natMem, realMem, ?_⟩
  · intro h
    simpa [middle, dualBoundReadState, relocateState] using chosen (takes.mpr h)
  · intro h
    simpa [middle, dualBoundReadState, relocateState] using kept (fun yes => h (takes.mp yes))
  · intro r high away
    have nonzero : r ≠ 0 := by omega
    have fixed := arithmeticRun_keeps_high_register (mergeDualBoundBlock_low_writes r high) middle steps
    simpa [middle, dualBoundReadState, relocateState, away, nonzero] using fixed

end VehicleRoutingSurvey.Routing
end RppSource_WeightedReadDeltaRAM

/-! runtime/PrimToOccurrences.lean -/
section RppSource_PrimToOccurrences
namespace VehicleRoutingSurvey.Routing

/-- Reserve the matching pair array immediately after the tree pairs.
The occurrence buffer begins after its capacity of two cells per vertex. -/
def allocateOccurrenceBufferBlock : List ArithmeticInstruction :=
  [.natAdd 0 35 35, .natAdd 106 34 0, .natAdd 0 5 5, .natAdd 33 106 0]

theorem allocateOccurrenceBufferBlock_correct (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns allocateOccurrenceBufferBlock 4 s t ∧ t.halted = false ∧
      t.nr 106 = s.nr 34 + 2 * s.nr 35 ∧ t.nr 33 = t.nr 106 + 2 * s.nr 5 ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧
      ∀ r, r ≠ 0 → r ≠ 33 → r ≠ 106 → t.nr r = s.nr r := by
  let t := (arithmeticStep allocateOccurrenceBufferBlock)^[4] s
  have ready : t.halted = false := by
    simp [t, allocateOccurrenceBufferBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = allocateOccurrenceBufferBlock.length := by
    simp [t, allocateOccurrenceBufferBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_, ?_⟩
  · simp [t, allocateOccurrenceBufferBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
    omega
  · simp [t, allocateOccurrenceBufferBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
    omega
  · simp [t, allocateOccurrenceBufferBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [t, allocateOccurrenceBufferBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · intro r scratch base reserve
    simp [t, allocateOccurrenceBufferBlock, arithmeticStep, entry, running, Function.iterate_succ_apply',
      Function.update_of_ne scratch, Function.update_of_ne base, Function.update_of_ne reserve]

private theorem connectorOccurrenceDestinationsBelowReservation :
    ∀ ins ∈ connectorOccurrencesBlock, naturalDestination ins < 106 := by
  have checked :
      connectorOccurrencesBlock.all (fun ins => decide (naturalDestination ins < 106)) = true := by
    decide
  exact fun ins found => of_decide_eq_true (List.all_eq_true.mp checked ins found)

def minimumTreeOccurrencesBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock minimumTreeAfterPathsBlock allocateOccurrenceBufferBlock)
    connectorOccurrencesBlock

/-- From the stored all-pairs paths, compute the minimum component tree
and the exact base-plus-connector occurrence array. The result is ready
for degree parity and retains space for the later matching pairs. -/
theorem minimumTreeOccurrencesBlock_correct {I : Service} {rows matrix next : ℕ}
    {table : DirectLinkTable I.graph} {s : ArithmeticState}
    (rural : Rural I) (requiredLinks : I.links.Nonempty)
    (frame : FloydFrame I.graph.n rows matrix s) (nextAt : s.nr 26 = next)
    (sound : DirectLinkTableSound table)
    (representative : DirectLinkRepresentatives I.graph (tableChooses table))
    (pathRows : ∀ target, TightStoredRow target table next s.nm)
    (raw : ∀ k < 2 + 3 * I.graph.q, s.nm k = (ruralNatInput I)[k]?.getD 0)
    (inputBefore : 2 + 3 * I.graph.q ≤ next) (rowsBefore : rows + I.graph.n ≤ next)
    (weightsBefore : I.graph.q ≤ matrix)
    (weights : ∀ e : Fin I.graph.q, s.rm e.val = I.graph.weight e)
    (distances : ∀ p : PrimPair I, s.rm (matrix + primPairOffset p) = distance I.graph p.1 p.2)
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ (t : ArithmeticState) (tree : List (PrimPair I))
      (paths : List (List (Traversal I.graph))) (steps : ℕ),
      BlockRuns minimumTreeOccurrencesBlock steps s t ∧ t.halted = false ∧
      steps ≤ 300 * (I.graph.n ^ 3 + I.graph.q) ∧
      MinimumComponentTree I tree ∧ Expands I.graph tree paths ∧
      (∀ path ∈ paths, path.length < I.graph.n) ∧
      FloydFrame I.graph.n rows matrix t ∧ t.nr 26 = next ∧ t.nr 28 = 0 ∧
      next + I.graph.n ^ 2 ≤ t.nr 106 ∧ t.nr 33 = t.nr 106 + 2 * I.graph.n ∧
      t.nr 29 = t.nr 33 + (requiredLinkList I ++ paths.flatten.map Prod.fst).length ∧
      OccurrenceArray t.nm (t.nr 33) (requiredLinkList I ++ paths.flatten.map Prod.fst) ∧
      (∀ k < next + I.graph.n ^ 2, t.nm k = s.nm k) ∧
      (∀ p : PrimPair I, t.rm (matrix + primPairOffset p) = distance I.graph p.1 p.2) ∧
      ∀ e : Fin I.graph.q, t.rm e.val = I.graph.weight e := by
  obtain ⟨m, tree, primSteps, output, prim, mReady, primBound, minimum, mFrame,
      outputAt, countAt, pathsAt, outputAfterPaths, mNatural, mDistances, mWeights, pairWords⟩ :=
    minimumTreeAfterPathsBlock_correct rural requiredLinks frame nextAt raw inputBefore rowsBefore
      weightsBefore weights distances entry running
  obtain ⟨a, alloc, aReady, reserved, occurrenceBase, aNat, aReal, aFixed⟩ :=
    allocateOccurrenceBufferBlock_correct {m with pc := 0} rfl mReady
  let allocated := relocateState minimumTreeAfterPathsBlock.length a
  let expansionEntry := {allocated with pc := 0}
  have fixed (r : ℕ) (nonScratch : r ≠ 0) (nonBase : r ≠ 33) (nonReserved : r ≠ 106) :
      expansionEntry.nr r = m.nr r := aFixed r nonScratch nonBase nonReserved
  have copied (address : ℕ) (below : address < next + I.graph.n ^ 2) :
      expansionEntry.nm address = s.nm address :=
    (congrFun aNat address).trans (mNatural address below)
  have aFrame : FloydFrame I.graph.n rows matrix expansionEntry :=
    mFrame.preserved (fun r hlo hhi => fixed r (by omega) (by omega) (by omega)) aNat
  have livePaths (target : Fin I.graph.n) :
      TightStoredRow target table (expansionEntry.nr 26) expansionEntry.nm := by
    have atPaths := (fixed 26 (by decide) (by decide) (by decide)).trans pathsAt
    rw [atPaths]
    refine (pathRows target).preservedBelow le_rfl fun address below => ?_
    exact copied address (by simpa [pow_two] using below)
  have pairAt := (fixed 34 (by decide) (by decide) (by decide)).trans outputAt
  have pairCount := (fixed 35 (by decide) (by decide) (by decide)).trans countAt
  have pairArray : ExpansionPairArray expansionEntry.nm (expansionEntry.nr 34) tree := by
    rw [pairAt]
    intro j hj
    change a.nm _ = _ ∧ a.nm _ = _
    rw [aNat]
    exact pairWords ⟨j, hj⟩
  have liveRaw (address : ℕ) (below : address < 2 + 3 * I.graph.q) :
      expansionEntry.nm address = (ruralNatInput I)[address]?.getD 0 :=
    (copied address (below.trans_le (inputBefore.trans (Nat.le_add_right _ _)))).trans (raw address below)
  have afterPaths : next + I.graph.n ^ 2 ≤ expansionEntry.nr 33 := by
    change next + I.graph.n ^ 2 ≤ a.nr 33
    rw [occurrenceBase, reserved, outputAt]
    omega
  have pairBound : expansionEntry.nr 34 + 2 * tree.length ≤ expansionEntry.nr 33 := by
    change expansionEntry.nr 34 + _ ≤ a.nr 33
    rw [pairAt, occurrenceBase, reserved, outputAt, countAt]
    omega
  have pointerBound : expansionEntry.nr 26 + I.graph.n * I.graph.n ≤ expansionEntry.nr 33 := by
    rw [(fixed 26 (by decide) (by decide) (by decide)).trans pathsAt]
    simpa [pow_two] using afterPaths
  obtain ⟨p, pathSteps, paths, expand, expandBound, ready, expands, pathLengths, zero, cursor,
      array, pFixed, pReal, pNat⟩ :=
    connectorOccurrencesBlock_correct tree rural aFrame sound representative livePaths pairCount
      pairArray liveRaw pairBound (rowsBefore.trans ((Nat.le_add_right _ _).trans afterPaths)) pointerBound
      (inputBefore.trans ((Nat.le_add_right _ _).trans afterPaths)) rfl aReady
  let final := relocateState
    (appendBlock minimumTreeAfterPathsBlock allocateOccurrenceBufferBlock).length p
  have sameReservation : p.nr 106 = a.nr 106 := by
    rw [← expand.run]
    exact arithmeticRun_keeps_high_register connectorOccurrenceDestinationsBelowReservation
      expansionEntry pathSteps
  have finalBase : p.nr 33 = a.nr 33 := pFixed 33 (by decide) (by decide)
  have finalRows : FloydFrame I.graph.n rows matrix final := by
    refine ⟨(pFixed 3 (by decide) (by decide)).trans aFrame.tableBase,
      (pFixed 4 (by decide) (by decide)).trans aFrame.matrixBase,
      (pFixed 5 (by decide) (by decide)).trans aFrame.dimension,
      (pFixed 6 (by decide) (by decide)).trans aFrame.one, ?_⟩
    intro j hj
    exact (pNat _ ((Nat.add_lt_add_left hj _).trans_le
      (rowsBefore.trans ((Nat.le_add_right _ _).trans afterPaths)))).trans (aFrame.rows j hj)
  have countBound : tree.length ≤ I.graph.n := (componentTree_length_lt minimum.1).le
  have product : tree.length * (25 * I.graph.n + 9) ≤ 25 * I.graph.n ^ 2 + 9 * I.graph.n := by
    calc
      _ ≤ I.graph.n * (25 * I.graph.n + 9) := Nat.mul_le_mul_right _ countBound
      _ = _ := by ring
  have square : I.graph.n ^ 2 ≤ I.graph.n ^ 3 := by
    calc
      _ = I.graph.n ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ I.graph.n ^ 2 * I.graph.n := Nat.mul_le_mul_left _ rural.1.1
      _ = _ := (pow_succ _ 2).symm
  have vertexBound : I.graph.n ≤ I.graph.n ^ 3 :=
    (by simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left I.graph.n rural.1.1 :
      I.graph.n ≤ I.graph.n ^ 2).trans square
  have cube : 0 < I.graph.n ^ 3 := pow_pos rural.1.1 _
  have bound : primSteps + 4 + pathSteps ≤ 300 * (I.graph.n ^ 3 + I.graph.q) := by omega
  refine ⟨final, tree, paths, _, (prim.append alloc).append expand, ready, bound, minimum, expands,
    pathLengths, finalRows, (pFixed 26 (by decide) (by decide)).trans
      ((fixed 26 (by decide) (by decide) (by decide)).trans pathsAt), zero, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change _ ≤ p.nr 106
    rw [sameReservation, reserved, outputAt]
    omega
  · change p.nr 33 = p.nr 106 + _
    rw [finalBase, sameReservation, occurrenceBase]
    exact congrArg (fun n => a.nr 106 + 2 * n) mFrame.dimension
  · change p.nr 29 = p.nr 33 + _
    rwa [finalBase]
  · change OccurrenceArray p.nm (p.nr 33) _
    rwa [finalBase]
  · intro address below
    exact (pNat address (below.trans_le afterPaths)).trans (copied address below)
  · intro pair
    exact (congrFun (pReal.trans aReal) _).trans (mDistances pair)
  · intro edge
    exact (congrFun (pReal.trans aReal) edge.val).trans (mWeights edge)

end VehicleRoutingSurvey.Routing
end RppSource_PrimToOccurrences

/-! runtime/RawToOccurrences.lean -/
section RppSource_RawToOccurrences
namespace VehicleRoutingSurvey.Routing

def rawToConnectorOccurrencesBlock : List ArithmeticInstruction :=
  appendBlock apspFromRawInputBlock minimumTreeOccurrencesBlock

/-- Compute the required and connector occurrences from the exact
encoded nonempty rural-postman input. This is the checkpoint at which
the odd degrees are computed. -/
theorem rawToConnectorOccurrencesBlock_correct {I : Service}
    (rural : Rural I) (required : I.links.Nonempty) :
    let n := I.graph.n
    let q := I.graph.q
    let rowOffsets := 2 + 3 * q
    let next := rowOffsets + n + n * n + n + n
    let start := arithmeticInput (ruralNatInput I) (ruralRealInput I)
    ∃ (t : ArithmeticState) (table : DirectLinkTable I.graph)
      (tree : List (PrimPair I)) (paths : List (List (Traversal I.graph))) (steps : ℕ),
      BlockRuns rawToConnectorOccurrencesBlock steps start t ∧ t.halted = false ∧
      steps ≤ 500 * (n ^ 3 + q) ∧
      MinimumComponentTree I tree ∧ Expands I.graph tree paths ∧
      (∀ path ∈ paths, path.length < n) ∧ FloydFrame n rowOffsets q t ∧
      t.nr 26 = next ∧ t.nr 28 = 0 ∧ next + n ^ 2 ≤ t.nr 106 ∧
      t.nr 33 = t.nr 106 + 2 * n ∧
      t.nr 29 = t.nr 33 + (requiredLinkList I ++ paths.flatten.map Prod.fst).length ∧
      OccurrenceArray t.nm (t.nr 33) (requiredLinkList I ++ paths.flatten.map Prod.fst) ∧
      DirectLinkTableSound table ∧ DirectLinkRepresentatives I.graph (tableChooses table) ∧
      (∀ target, TightStoredRow target table next t.nm) ∧
      (∀ a < 2 + 3 * q, t.nm a = (ruralNatInput I)[a]?.getD 0) ∧
      (∀ p : PrimPair I, t.rm (q + primPairOffset p) = distance I.graph p.1 p.2) ∧
      ∀ edge : Fin q, t.rm edge.val = I.graph.weight edge := by
  let n := I.graph.n
  let q := I.graph.q
  let rowOffsets := 2 + 3 * q
  let next := rowOffsets + n + n * n + n + n
  obtain ⟨a, table, pathsRun, aReady, aFrame, aNext, input, sound, representative, distanceData,
      weights, rows⟩ := apspFromRawInputBlock_correct rural
  let entry := {a with pc := 0}
  have inputFrame : FloydFrame n rowOffsets q entry :=
    aFrame.preserved (fun _ _ _ => rfl) rfl
  have inputBefore : 2 + 3 * q ≤ next := by dsimp [next, rowOffsets]; omega
  have rowsBefore : rowOffsets + n ≤ next := by dsimp [next]; omega
  have distancePairs (pair : PrimPair I) :
      entry.rm (q + primPairOffset pair) = distance I.graph pair.1 pair.2 := by
    change a.rm _ = _
    simpa [primPairOffset, Nat.add_assoc] using distanceData pair.1 pair.2
  obtain ⟨b, tree, paths, steps, occurrencesRun, bReady, occurrenceBound, minimum, expands,
      short, bFrame, bNext, zero, reserved, occurrenceBase, cursor, occurrences, retained,
      distances, linkWeights⟩ := minimumTreeOccurrencesBlock_correct rural required inputFrame aNext
        sound representative rows input inputBefore rowsBefore le_rfl weights distancePairs rfl aReady
  let final := relocateState apspFromRawInputBlock.length b
  have finalFrame : FloydFrame n rowOffsets q final :=
    bFrame.preserved (fun _ _ _ => rfl) rfl
  have allRows (target : Fin n) : TightStoredRow target table next final.nm := by
    change TightStoredRow target table next b.nm
    exact (rows target).preservedBelow le_rfl
      (fun address below => retained address (by simpa [pow_two] using below))
  have inputCells (address : ℕ) (bound : address < 2 + 3 * q) :
      final.nm address = (ruralNatInput I)[address]?.getD 0 :=
    (retained address (bound.trans_le (inputBefore.trans (Nat.le_add_right _ _)))).trans
      (input address bound)
  have square : n ^ 2 ≤ n ^ 3 := by
    calc
      _ = n ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ n ^ 2 * n := Nat.mul_le_mul_left _ rural.1.1
      _ = _ := (pow_succ _ 2).symm
  have vertexBound : n ≤ n ^ 3 :=
    (by simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left n rural.1.1 : n ≤ n ^ 2).trans square
  have positive : 0 < n ^ 3 := pow_pos rural.1.1 _
  have runtime : (49 * n ^ 3 + 24 * n ^ 2 + 36 * n + 33 * q + 38) + steps ≤
      500 * (n ^ 3 + q) := by
    change steps ≤ 300 * (n ^ 3 + q) at occurrenceBound
    omega
  exact ⟨final, table, tree, paths, _, pathsRun.append occurrencesRun, bReady, runtime,
    minimum, expands, short, finalFrame, bNext, zero, reserved, occurrenceBase,
    cursor, occurrences, sound, representative, allRows, inputCells, distances, linkWeights⟩

end VehicleRoutingSurvey.Routing
end RppSource_RawToOccurrences

/-! runtime/EulerAdjacency.lean -/
section RppSource_EulerAdjacency
namespace VehicleRoutingSurvey.Routing

/-- A dart stores the next incident dart, both endpoints, the address of
the occurrence's shared activity bit, and the original traversal code. -/
def insertEulerDartMemory (m : ℕ → ℕ) (head dart source target activity link direction : ℕ) :
    ℕ → ℕ :=
  let m := Function.update m dart (m head)
  let m := Function.update m head dart
  let m := Function.update m (dart + 1) source
  let m := Function.update m (dart + 2) target
  let m := Function.update m (dart + 3) activity
  let m := Function.update m (dart + 4) link
  Function.update m (dart + 5) direction

/-- Prepend one dart to its source vertex's incident list. Register 6
supplies one. Registers 7, 8, 9, 11, 12, 13, 14 hold the head-table base,
source, dart address, target, activity address, link, and direction. -/
def insertEulerDartCell : List ArithmeticInstruction :=
  [.natAdd 0 7 8, .natLoad 2 0, .natStore 9 2, .natStore 0 9,
   .natAdd 0 9 6, .natStore 0 8, .natAdd 0 0 6, .natStore 0 11,
   .natAdd 0 0 6, .natStore 0 12, .natAdd 0 0 6, .natStore 0 13,
   .natAdd 0 0 6, .natStore 0 14]

theorem insertEulerDartCell_correct {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 6 = 1) :
    ∃ t, BlockRuns insertEulerDartCell 14 s t ∧ t.halted = false ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ (∀ r, r ≠ 0 → r ≠ 2 → t.nr r = s.nr r) ∧
      t.nm = insertEulerDartMemory s.nm (s.nr 7 + s.nr 8) (s.nr 9)
        (s.nr 8) (s.nr 11) (s.nr 12) (s.nr 13) (s.nr 14) := by
  let t := {s with
    pc := 14
    nr := Function.update (Function.update (Function.update s.nr 0 (s.nr 7 + s.nr 8))
      2 (s.nm (s.nr 7 + s.nr 8))) 0 (s.nr 9 + 5)
    nm := insertEulerDartMemory s.nm (s.nr 7 + s.nr 8) (s.nr 9)
      (s.nr 8) (s.nr 11) (s.nr 12) (s.nr 13) (s.nr 14)}
  refine ⟨t, ⟨?_, ?_, rfl⟩, running, rfl, rfl, ?_, rfl⟩
  · intro j bound
    interval_cases j <;>
      simp [insertEulerDartCell, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [insertEulerDartCell, arithmeticStep, entry, running, one,
      Function.iterate_succ_apply', insertEulerDartMemory, t, Nat.add_assoc, Function.update_idem]
  · intro r other0 other2
    simp [t, Function.update_of_ne other0, Function.update_of_ne other2]


end VehicleRoutingSurvey.Routing
end RppSource_EulerAdjacency

/-! runtime/EulerBuildOccurrence.lean -/
section RppSource_EulerBuildOccurrence
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- Construct the two incident darts for one occurrence of an original link.
The occurrence IDs and dart cursor run downward, so prepending the darts
leaves each list in the order used by `EulerOccurrences.initial`. -/
def prepareEulerOccurrenceBlock : List ArithmeticInstruction :=
  [.natSub 20 20 6, .natSub 21 21 22,
   .natAdd 0 23 20, .natLoad 13 0,
   .natAdd 0 13 13, .natAdd 0 0 13, .natAdd 0 0 24,
   .natLoad 11 0, .natAdd 0 0 6, .natLoad 8 0,
   .natAdd 12 25 20, .natStore 12 6, .natAdd 9 21 10, .natConst 14 0]

structure EulerOccurrenceOperands where
  index : ℕ
  dart : ℕ
  link : ℕ
  tail : ℕ
  head : ℕ
  activity : ℕ

def EulerOccurrenceOperands.read (s : ArithmeticState) : EulerOccurrenceOperands :=
  let index := s.nr 20 - 1
  let link := s.nm (s.nr 23 + index)
  let inputOffset := link + link + link + 2
  ⟨index, s.nr 21 - 12, link, s.nm inputOffset, s.nm (inputOffset + 1), s.nr 25 + index⟩

def eulerOccurrencePreserved : List ℕ := [6, 7, 10, 17, 18, 22, 23, 24, 25, 26, 27, 28]

theorem prepareEulerOccurrenceBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 6 = 1) (zero : s.nr 10 = 0) (width : s.nr 22 = 12) (two : s.nr 24 = 2) :
    let e := EulerOccurrenceOperands.read s
    ∃ t, BlockRuns prepareEulerOccurrenceBlock 14 s t ∧ t.halted = false ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ r ∈ eulerOccurrencePreserved, t.nr r = s.nr r) ∧
      t.nr 20 = e.index ∧ t.nr 21 = e.dart ∧
      t.nr 8 = e.head ∧ t.nr 11 = e.tail ∧ t.nr 9 = e.dart ∧
      t.nr 12 = e.activity ∧ t.nr 13 = e.link ∧ t.nr 14 = 0 ∧
      t.nm = Function.update s.nm e.activity 1 := by
  let t := (arithmeticStep prepareEulerOccurrenceBlock)^[14] s
  let e := EulerOccurrenceOperands.read s
  have ready : t.halted = false := by
    simp [t, prepareEulerOccurrenceBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = prepareEulerOccurrenceBlock.length := by
    simp [t, prepareEulerOccurrenceBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_⟩
  simp [t, e, prepareEulerOccurrenceBlock, EulerOccurrenceOperands.read, eulerOccurrencePreserved,
    arithmeticStep, entry, running, one, zero, width, two, Function.iterate_succ_apply',
    or_imp, forall_and]

/-- Swap the endpoints and advance six cells to the forward dart. -/
def switchEulerDartBlock : List ArithmeticInstruction :=
  [.natAdd 0 8 10, .natAdd 8 11 10, .natAdd 11 0 10, .natAdd 9 9 26, .natAdd 14 6 10]

theorem switchEulerDartBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 6 = 1) (zero : s.nr 10 = 0) (halfWidth : s.nr 26 = 6) :
    ∃ t, BlockRuns switchEulerDartBlock 5 s t ∧ t.halted = false ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ r ∈ eulerOccurrencePreserved, t.nr r = s.nr r) ∧
      t.nr 8 = s.nr 11 ∧ t.nr 11 = s.nr 8 ∧ t.nr 9 = s.nr 9 + 6 ∧
      t.nr 12 = s.nr 12 ∧ t.nr 13 = s.nr 13 ∧ t.nr 14 = 1 ∧
      t.nr 20 = s.nr 20 ∧ t.nr 21 = s.nr 21 := by
  let t := (arithmeticStep switchEulerDartBlock)^[5] s
  have ready : t.halted = false := by
    simp [t, switchEulerDartBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = switchEulerDartBlock.length := by
    simp [t, switchEulerDartBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_⟩
  simp [t, switchEulerDartBlock, eulerOccurrencePreserved, arithmeticStep, entry, running,
    one, zero, halfWidth, Function.iterate_succ_apply', or_imp, forall_and]

def buildEulerOccurrenceBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock (appendBlock prepareEulerOccurrenceBlock insertEulerDartCell)
    switchEulerDartBlock) insertEulerDartCell

def EulerOccurrenceOperands.write (e : EulerOccurrenceOperands) (heads : ℕ) (memory : ℕ → ℕ) : ℕ → ℕ :=
  let memory := Function.update memory e.activity 1
  let memory := insertEulerDartMemory memory (heads + e.head) e.dart e.head e.tail e.activity e.link 0
  insertEulerDartMemory memory (heads + e.tail) (e.dart + 6) e.tail e.head e.activity e.link 1

/-- Install both darts and the shared live flag in a fixed number of steps. -/
theorem buildEulerOccurrenceBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 6 = 1) (zero : s.nr 10 = 0) (width : s.nr 22 = 12)
    (two : s.nr 24 = 2) (halfWidth : s.nr 26 = 6) :
    let e := EulerOccurrenceOperands.read s
    ∃ t, BlockRuns buildEulerOccurrenceBlock 47 s t ∧ t.halted = false ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ r ∈ eulerOccurrencePreserved, t.nr r = s.nr r) ∧
      t.nr 20 = e.index ∧ t.nr 21 = e.dart ∧ t.nm = e.write (s.nr 7) s.nm := by
  let e := EulerOccurrenceOperands.read s
  obtain ⟨prep, prepRun, prepReady, prepRm, prepRr, prepKeeps, prepIndex, prepCursor,
    prepSource, prepTarget, prepDart, prepFlag, prepLink, prepDirection, prepMem⟩ :=
    prepareEulerOccurrenceBlock_correct entry running one zero width two
  obtain ⟨back, backRun, backReady, backRm, backRr, backKeeps, backMem⟩ :=
    insertEulerDartCell_correct (s := {prep with pc := 0}) rfl prepReady
      ((prepKeeps 6 (by decide)).trans one)
  have backFixed (r) (hr : r ∈ eulerOccurrencePreserved) : back.nr r = s.nr r := by
    have shows0 : r ≠ 0 := by rintro rfl; simp [eulerOccurrencePreserved] at hr
    have shows2 : r ≠ 2 := by rintro rfl; simp [eulerOccurrencePreserved] at hr
    exact (backKeeps r shows0 shows2).trans (prepKeeps r hr)
  obtain ⟨turn, turnRun, turnReady, turnMem, turnRm, turnRr, turnKeeps, turnSource, turnTarget,
    turnDart, turnFlag, turnLink, turnDirection, turnIndex, turnCursor⟩ :=
    switchEulerDartBlock_correct (s := {back with pc := 0}) rfl backReady
      ((backFixed 6 (by decide)).trans one) ((backFixed 10 (by decide)).trans zero)
      ((backFixed 26 (by decide)).trans halfWidth)
  have turnFixed (r) (hr : r ∈ eulerOccurrencePreserved) : turn.nr r = s.nr r :=
    (turnKeeps r hr).trans (backFixed r hr)
  obtain ⟨forward, forwardRun, forwardReady, forwardRm, forwardRr, forwardKeeps, forwardMem⟩ :=
    insertEulerDartCell_correct (s := {turn with pc := 0}) rfl turnReady
      ((turnFixed 6 (by decide)).trans one)
  have forwardFixed (r) (hr : r ∈ eulerOccurrencePreserved) : forward.nr r = s.nr r := by
    have shows0 : r ≠ 0 := by rintro rfl; simp [eulerOccurrencePreserved] at hr
    have shows2 : r ≠ 2 := by rintro rfl; simp [eulerOccurrencePreserved] at hr
    exact (forwardKeeps r shows0 shows2).trans (turnFixed r hr)
  have run := ((prepRun.append backRun).append turnRun).append forwardRun
  refine ⟨_, run, forwardReady, forwardRm.trans (turnRm.trans (backRm.trans prepRm)),
    forwardRr.trans (turnRr.trans (backRr.trans prepRr)), forwardFixed, ?_, ?_, ?_⟩
  · exact (forwardKeeps 20 (by decide) (by decide)).trans
      (turnIndex.trans ((backKeeps 20 (by decide) (by decide)).trans prepIndex))
  · exact (forwardKeeps 21 (by decide) (by decide)).trans
      (turnCursor.trans ((backKeeps 21 (by decide) (by decide)).trans prepCursor))
  · have backMemory : back.nm =
        insertEulerDartMemory (Function.update s.nm e.activity 1)
          (s.nr 7 + e.head) e.dart e.head e.tail e.activity e.link 0 := by
      simpa only [prepMem, prepKeeps 7 (by decide), prepSource, prepTarget, prepDart, prepFlag,
        prepLink, prepDirection] using backMem
    have backSource := (backKeeps 8 (by decide) (by decide)).trans prepSource
    have backTarget := (backKeeps 11 (by decide) (by decide)).trans prepTarget
    have backDart := (backKeeps 9 (by decide) (by decide)).trans prepDart
    have backFlag := (backKeeps 12 (by decide) (by decide)).trans prepFlag
    have backLink := (backKeeps 13 (by decide) (by decide)).trans prepLink
    change forward.nm = e.write (s.nr 7) s.nm
    simpa only [e, EulerOccurrenceOperands.write, turnMem, backMemory, turnFixed 7 (by decide),
      turnSource, turnTarget, turnDart, turnFlag, turnLink, turnDirection, backSource, backTarget,
      backDart, backFlag, backLink] using forwardMem


end VehicleRoutingSurvey.Routing
end RppSource_EulerBuildOccurrence

/-! runtime/EulerBuildLoop.lean -/
section RppSource_EulerBuildLoop
namespace VehicleRoutingSurvey.Routing

structure EulerBuildView where
  remaining : ℕ
  dartCursor : ℕ
  memory : ℕ → ℕ

def EulerBuildView.read (s : ArithmeticState) : EulerBuildView :=
  ⟨s.nr 20, s.nr 21, s.nm⟩

def EulerBuildView.next (heads input flags : ℕ) (view : EulerBuildView) : EulerBuildView :=
  let index := view.remaining - 1
  let link := view.memory (input + index)
  let endpoints := link + link + link + 2
  let e : EulerOccurrenceOperands :=
    ⟨index, view.dartCursor - 12, link, view.memory endpoints, view.memory (endpoints + 1),
      flags + index⟩
  ⟨e.index, e.dart, e.write heads view.memory⟩

def buildEulerOccurrencesBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 17 18 buildEulerOccurrenceBlock

def eulerBuildFixed : List ℕ := [6, 7, 10, 18, 22, 23, 24, 25, 26, 27, 28]

private structure EulerBuildLoopInvariant (s : ArithmeticState) (i : ℕ)
    (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  running : m.halted = false
  index : m.nr 17 = i
  fixed : ∀ r ∈ eulerBuildFixed, m.nr r = s.nr r
  realMemory : m.rm = s.rm
  realRegisters : m.rr = s.rr
  view : EulerBuildView.read m =
    (EulerBuildView.next (s.nr 7) (s.nr 23) (s.nr 25))^[i] (EulerBuildView.read s)

theorem buildEulerOccurrencesBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 6 = 1) (zero : s.nr 10 = 0) (width : s.nr 22 = 12)
    (two : s.nr 24 = 2) (halfWidth : s.nr 26 = 6) :
    ∃ t, BlockRuns buildEulerOccurrencesBlock (1 + (s.nr 18 * 50 + 1)) s t ∧
      t.halted = false ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ r ∈ eulerBuildFixed, t.nr r = s.nr r) ∧
      EulerBuildView.read t =
        (EulerBuildView.next (s.nr 7) (s.nr 23) (s.nr 25))^[s.nr 18] (EulerBuildView.read s) := by
  have initial : EulerBuildLoopInvariant s 0 {s with pc := 0, nr := Function.update s.nr 17 0} := by
    refine ⟨rfl, running, by simp, ?_, rfl, rfl, by simp [EulerBuildView.read]⟩
    intro r present
    have distinct : r ≠ 17 := by rintro rfl; simp [eulerBuildFixed] at present
    exact Function.update_of_ne distinct _ _
  have control (i) (m : ArithmeticState) (inv : EulerBuildLoopInvariant s i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 17 = i ∧ m.nr 18 = s.nr 18 :=
    ⟨inv.entry, inv.running, inv.index, inv.fixed 18 (by decide)⟩
  have iterate (i : ℕ) (_ : i < s.nr 18) (m : ArithmeticState) (inv : EulerBuildLoopInvariant s i m) :
      ∃ t, BlockRuns buildEulerOccurrenceBlock 47 m t ∧ t.halted = false ∧
        EulerBuildLoopInvariant s (i + 1)
          {t with pc := 0, nr := Function.update t.nr 17 (t.nr 17 + t.nr 6)} := by
    obtain ⟨t, run, ready, rm, rr, stable, count, address, memory⟩ :=
      buildEulerOccurrenceBlock_correct inv.entry inv.running
        ((inv.fixed 6 (by decide)).trans one) ((inv.fixed 10 (by decide)).trans zero)
        ((inv.fixed 22 (by decide)).trans width) ((inv.fixed 24 (by decide)).trans two)
        ((inv.fixed 26 (by decide)).trans halfWidth)
    have index := (stable 17 (by decide)).trans inv.index
    have increment := ((stable 6 (by decide)).trans (inv.fixed 6 (by decide))).trans one
    refine ⟨t, run, ready, ⟨rfl, ready, by simp [index, increment], ?_, rm.trans inv.realMemory,
      rr.trans inv.realRegisters, ?_⟩⟩
    · intro r present
      have distinct : r ≠ 17 := by rintro rfl; simp [eulerBuildFixed] at present
      exact (Function.update_of_ne distinct _ _).trans
        ((stable r (by simp [eulerBuildFixed, eulerOccurrencePreserved] at present ⊢; tauto)).trans
          (inv.fixed r present))
    · have nextView : EulerBuildView.read t =
          (EulerBuildView.read m).next (s.nr 7) (s.nr 23) (s.nr 25) := by
        have heads := inv.fixed 7 (by decide)
        have input := inv.fixed 23 (by decide)
        have flags := inv.fixed 25 (by decide)
        simp [EulerBuildView.read, EulerBuildView.next, EulerOccurrenceOperands.read, count, address,
          memory, heads, input, flags]
      rw [inv.view] at nextView
      simpa [EulerBuildView.read, Function.iterate_succ_apply'] using nextView
  obtain ⟨last, inv, run⟩ := countedLoopFromZero_correct 6 17 18 (s.nr 18) 47
    buildEulerOccurrenceBlock (EulerBuildLoopInvariant s) entry running initial control iterate
  exact ⟨_, run, inv.running, inv.realMemory, inv.realRegisters, inv.fixed, inv.view⟩


end VehicleRoutingSurvey.Routing
end RppSource_EulerBuildLoop


