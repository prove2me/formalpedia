-- Prove2me | Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part03
-- name    : VehicleRoutingSurvey_RuralPostman1979_Part03
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T13:57:00.551002+00:00
-- url     : https://prove2.me/theorems/713d8ca9-dd5d-40c4-8c31-a537427e2c25
-- title:
--   Rural postman algorithm — Shortest-path queue refinement and required-component labels
-- statement:
--   This module supplies the Lean definitions and checked auxiliary results for shortest-path queue refinement and required-component labels in the Table 3 proof. It uses the mission’s rural-run and arithmetic-RAM model.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Mathlib.Tactic.Ring
import Mathlib.Data.List.Induction
import Mathlib.Tactic.IntervalCases
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part01
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part02

/-! runtime/TightQueueRowRefinement.lean -/
section RppSource_TightQueueRowRefinement
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

structure TightQueueRowFrame (rowOffsets distances : ℕ) (target v : Fin G.n)
    (table : DirectLinkTable G) (s : ArithmeticState) : Prop where
  floyd : FloydFrame G.n rowOffsets distances s
  target : s.nr 7 = target.val
  dequeued : s.nr 8 = v.val
  links : s.nr 10 = G.q
  sentinel : s.nr 17 = G.n
  queueAfterRank : s.nr 19 ≤ s.nr 20
  nextAfterRank : s.nr 19 ≤ s.nr 21
  separation : QueueSlicesSeparated (s.nr 19) (s.nr 20) (s.nr 21) G.n
  lowRows : ∀ i < G.n, rowOffsets + i < s.nr 19
  lowLinks : ∀ a b : Fin G.n, s.nr 11 + G.n * a.val + b.val < s.nr 19
  direct : ∀ a b : Fin G.n, s.nm (s.nr 11 + G.n * a.val + b.val) =
    ((table a b).map (fun step => step.1.val)).getD G.q
  weights : ∀ e : Fin G.q, s.rm e.val = G.weight e
  distance : ∀ a b : Fin G.n,
    s.rm (distances + G.n * a.val + b.val) = VehicleRoutingSurvey.Routing.distance G a b

private def tightQueueFrameRegisters : List ℕ := [3, 4, 5, 6, 7, 10, 11, 17, 19, 20, 21]

private theorem TightQueueRowFrame.preserved {rowOffsets distances : ℕ} {target v w : Fin G.n}
    {table : DirectLinkTable G} {s t : ArithmeticState}
    (frame : TightQueueRowFrame rowOffsets distances target v table s)
    (fixed : ∀ r ∈ tightQueueFrameRegisters, t.nr r = s.nr r)
    (natural : ∀ a < s.nr 19, t.nm a = s.nm a) (real : t.rm = s.rm)
    (dequeued : t.nr 8 = w.val) :
    TightQueueRowFrame rowOffsets distances target w table t := by
  have rowReg := fixed 3 (by decide)
  have matrixReg := fixed 4 (by decide)
  have dimensionReg := fixed 5 (by decide)
  have oneReg := fixed 6 (by decide)
  have idReg := fixed 11 (by decide)
  have rankReg := fixed 19 (by decide)
  have queueReg := fixed 20 (by decide)
  have nextReg := fixed 21 (by decide)
  refine ⟨⟨rowReg.trans frame.floyd.tableBase, matrixReg.trans frame.floyd.matrixBase,
    dimensionReg.trans frame.floyd.dimension, oneReg.trans frame.floyd.one, ?_⟩,
    (fixed 7 (by decide)).trans frame.target, dequeued,
    (fixed 10 (by decide)).trans frame.links, (fixed 17 (by decide)).trans frame.sentinel,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact (natural _ (frame.lowRows i hi)).trans (frame.floyd.rows i hi)
  · simpa only [rankReg, queueReg] using frame.queueAfterRank
  · simpa only [rankReg, nextReg] using frame.nextAfterRank
  · simpa only [rankReg, queueReg, nextReg] using frame.separation
  · simpa only [rankReg] using frame.lowRows
  · simpa only [rankReg, idReg] using frame.lowLinks
  · intro a b
    rw [idReg, natural _ (frame.lowLinks a b)]
    exact frame.direct a b
  · simpa only [real] using frame.weights
  · simpa only [real] using frame.distance

private theorem TightQueueRowFrame.candidate {rowOffsets distances : ℕ} {target v u : Fin G.n}
    {table : DirectLinkTable G} {model : TightSearchState G} {s : ArithmeticState}
    (frame : TightQueueRowFrame rowOffsets distances target v table s)
    (sound : DirectLinkTableSound table) (index : s.nr 9 = u.val)
    (arrays : TightQueueNaturalMemory (s.nr 19) (s.nr 20) (s.nr 21) model s.nm) :
    TightQueueCandidateFrame rowOffsets distances target v u (table u v) model s :=
  ⟨frame.floyd, frame.target, frame.dequeued, index, frame.links, frame.sentinel,
    arrays.rank u, frame.direct u v, frame.weights, frame.distance u target,
      frame.distance v target,
    fun step selected => ⟨(sound u v step selected).1, (sound u v step selected).2.1⟩⟩

private def setCandidate (s : ArithmeticState) (i : ℕ) : ArithmeticState :=
  {s with pc := 0, nr := Function.update s.nr 9 i}

private theorem setCandidate_footprint (n : ℕ) (s : ArithmeticState) (i : ℕ) :
    QueueWriteFootprint n s (setCandidate s i) :=
  QueueWriteFootprint.noMemoryWrites (by simp [setCandidate]) (by simp [setCandidate])
    (by simp [setCandidate]) rfl

private theorem frameFixedAfterCandidate (s : ArithmeticState) (i r : ℕ)
    (allowed : r ∈ tightQueueFrameRegisters) :
    (setCandidate s i).nr r = s.nr r := by
  apply Function.update_of_ne
  intro same
  subst r
  exact (by decide : 9 ∉ tightQueueFrameRegisters) allowed

private noncomputable def partialIncoming (target v : Fin G.n) (table : DirectLinkTable G)
    (s : TightSearchState G) (cut : ℕ) : TightSearchState G :=
  ((List.finRange G.n).take cut).foldl (fun q u => scanTightCandidate target table v u q) s

private theorem partialIncoming_succ {target v : Fin G.n} {table : DirectLinkTable G}
    {s : TightSearchState G} {cut : ℕ} (more : cut < G.n) :
    partialIncoming target v table s (cut + 1) =
      scanTightCandidate target table v ⟨cut, more⟩ (partialIncoming target v table s cut) := by
  have inRange : cut < (List.finRange G.n).length := by simpa using more
  rw [partialIncoming, List.take_succ_eq_append_getElem inRange]
  simp [partialIncoming]

private theorem partialIncoming_full (target v : Fin G.n) (table : DirectLinkTable G)
    (s : TightSearchState G) :
    partialIncoming target v table s G.n = scanTightIncoming target table v s := by
  rw [partialIncoming, scanTightIncoming, List.take_of_length_le (by simp)]

/-- The n-column row scan refines the abstract dense reverse search;
protected operand tables survive each candidate test and possible append. -/
theorem tightQueueScanRowBlock_refines {rowOffsets distances : ℕ} {target v : Fin G.n}
    {table : DirectLinkTable G} {initial : TightSearchState G} {s : ArithmeticState}
    (frame : TightQueueRowFrame rowOffsets distances target v table s)
    (valid : TightSearchInvariant target initial) (sound : DirectLinkTableSound table)
    (known : v ∈ initial.queue) (tail : s.nr 16 = initial.queue.length)
    (memory : TightQueueNaturalMemory (s.nr 19) (s.nr 20) (s.nr 21) initial s.nm)
    (entry : s.pc = 0) (running : s.halted = false) :
    let out := scanTightIncoming target table v initial
    ∃ t, BlockRuns tightQueueScanRowBlock (tightQueueScanRowSteps G.n) s t ∧
      t.halted = false ∧ TightQueueRowFrame rowOffsets distances target v table t ∧
      t.nr 16 = out.queue.length ∧
      TightQueueNaturalMemory (t.nr 19) (t.nr 20) (t.nr 21) out t.nm ∧ QueueWriteFootprint G.n s t := by
  let through := partialIncoming target v table initial
  let inv (cut : ℕ) (m : ArithmeticState) :=
    m.pc = 0 ∧ m.halted = false ∧ m.nr 9 = cut ∧
      TightQueueRowFrame rowOffsets distances target v table m ∧
      TightSearchInvariant target (through cut) ∧ v ∈ (through cut).queue ∧
      m.nr 16 = (through cut).queue.length ∧
      TightQueueNaturalMemory (m.nr 19) (m.nr 20) (m.nr 21) (through cut) m.nm ∧
      QueueWriteFootprint G.n s m
  have init : inv 0 (setCandidate s 0) := by
    refine ⟨rfl, running, by simp [setCandidate],
      frame.preserved (fun r => frameFixedAfterCandidate s 0 r) (fun _ _ => rfl) rfl
        (by simpa [setCandidate] using frame.dequeued),
      valid, known, ?_, ?_, setCandidate_footprint G.n s 0⟩
    · simpa [setCandidate, through, partialIncoming] using tail
    · change TightQueueNaturalMemory ((setCandidate s 0).nr 19)
        ((setCandidate s 0).nr 20) ((setCandidate s 0).nr 21) initial s.nm
      simpa only [frameFixedAfterCandidate s 0 19 (by decide),
        frameFixedAfterCandidate s 0 20 (by decide), frameFixedAfterCandidate s 0 21 (by decide)]
        using memory
  have control (cut : ℕ) (m : ArithmeticState) (w : inv cut m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 9 = cut ∧ m.nr 5 = G.n :=
    ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1.floyd.dimension⟩
  have advance (cut : ℕ) (more : cut < G.n) (m : ArithmeticState) (w : inv cut m) :
      ∃ t, BlockRuns tightQueueScanBlock 28 m t ∧ t.halted = false ∧
        inv (cut + 1) {t with pc := 0, nr := Function.update t.nr 9 (t.nr 9 + t.nr 6)} := by
    obtain ⟨mEntry, mRunning, mIndex, mFrame, mValid, mKnown, mTail, mMemory, earlierWrites⟩ := w
    let u : Fin G.n := ⟨cut, more⟩
    have candidate := mFrame.candidate (u := u) sound mIndex mMemory
    obtain ⟨t, run, ready, real, newTail, newMemory⟩ := tightQueueScanBlock_refines candidate
      mValid sound mKnown mTail mFrame.separation mMemory mEntry mRunning
    have fixed (r : ℕ) (allowed : r ∈ tightQueueFrameRegisters) : t.nr r = m.nr r := by
      apply tightQueueScanBlock_fixed run mEntry mRunning mFrame.floyd.one r
      intro changed
      simp [tightQueueFrameRegisters] at allowed
      simp at changed
      omega
    have fixedIndex := tightQueueScanBlock_fixed run mEntry mRunning mFrame.floyd.one 9 (by decide)
    have writeStep : QueueWriteFootprint G.n m t :=
      ⟨fixed 19 (by decide), fixed 20 (by decide), fixed 21 (by decide),
        fun _ outside => tightQueueScanBlock_preserves_other_cells candidate mValid sound mKnown mTail
          mEntry mRunning run outside⟩
    have keepsPrefix (a : ℕ) (below : a < m.nr 19) : t.nm a = m.nm a :=
      tightQueueScanBlock_preserves_prefix candidate mValid mEntry mRunning run a below
        (below.trans_le mFrame.queueAfterRank) (below.trans_le mFrame.nextAfterRank)
    have fixedDequeue := tightQueueScanBlock_fixed run mEntry mRunning mFrame.floyd.one 8 (by decide)
    have tFrame : TightQueueRowFrame rowOffsets distances target v table t :=
      mFrame.preserved fixed keepsPrefix real (fixedDequeue.trans mFrame.dequeued)
    have resetFrame := tFrame.preserved (fun r => frameFixedAfterCandidate t (cut + 1) r)
      (fun _ _ => rfl) rfl
      (by simpa [setCandidate] using tFrame.dequeued)
    have reset : {t with pc := 0, nr := Function.update t.nr 9 (t.nr 9 + t.nr 6)} =
        setCandidate t (cut + 1) := by
      simp [setCandidate, fixedIndex, mIndex, tFrame.floyd.one]
    obtain ⟨qValid, grows, _⟩ := scanTightCandidate_correct sound u v (through cut) mKnown mValid
    have nextModel : through (cut + 1) = scanTightCandidate target table v u (through cut) :=
      partialIncoming_succ more
    refine ⟨t, run, ready, ?_⟩
    rw [reset]
    have newTail' : (setCandidate t (cut + 1)).nr 16 = (through (cut + 1)).queue.length := by
      rw [nextModel]
      simpa [setCandidate] using newTail
    refine ⟨rfl, ready, by simp [setCandidate], resetFrame, ?_, ?_, newTail', ?_,
      earlierWrites.trans (writeStep.trans (setCandidate_footprint G.n t (cut + 1)))⟩
    · rwa [nextModel]
    · rw [nextModel]
      exact grows.sublist.subset mKnown
    · rw [nextModel]
      have fixedBase (r : ℕ) (hr : r ∈ tightQueueFrameRegisters) :
          (setCandidate t (cut + 1)).nr r = m.nr r :=
        (frameFixedAfterCandidate t (cut + 1) r hr).trans (fixed r hr)
      rw [fixedBase 19 (by decide), fixedBase 20 (by decide), fixedBase 21 (by decide)]
      exact newMemory
  obtain ⟨last, hLast, run⟩ :=
    countedLoopFromZero_correct 6 9 5 G.n 28 tightQueueScanBlock inv entry running init control advance
  obtain ⟨_, lastReady, _, lastFrame, _, _, lastTail, lastMemory, lastWrites⟩ := hLast
  change last.nr 16 = (partialIncoming target v table initial G.n).queue.length at lastTail
  change TightQueueNaturalMemory (last.nr 19) (last.nr 20) (last.nr 21)
    (partialIncoming target v table initial G.n) last.nm at lastMemory
  rw [partialIncoming_full target v table initial] at lastTail lastMemory
  exact ⟨_, run, lastReady, lastFrame.preserved (fun _ _ => rfl) (fun _ _ => rfl) rfl lastFrame.dequeued,
    lastTail, lastMemory, lastWrites.trans (QueueWriteFootprint.noMemoryWrites rfl rfl rfl rfl)⟩

private def setDequeued (s : ArithmeticState) (v : Fin G.n) : ArithmeticState :=
  {s with nr := Function.update s.nr 8 v.val}

/-- A destination loop has the same operand frame as an incoming scan.
Its current-vertex register is free until a queue entry is read. -/
def TightDestinationFrame (rowOffsets distances : ℕ) (target : Fin G.n)
    (table : DirectLinkTable G) (s : ArithmeticState) : Prop :=
  TightQueueRowFrame rowOffsets distances target target table (setDequeued s target)

private theorem fixedWhenDequeued (s : ArithmeticState) (v : Fin G.n) (r : ℕ)
    (different : r ≠ 8) : (setDequeued s v).nr r = s.nr r :=
  Function.update_of_ne different _ _

private theorem frameRegister_ne_dequeued (r : ℕ) (member : r ∈ tightQueueFrameRegisters) :
    r ≠ 8 := by
  intro same
  subst r
  exact (by decide : 8 ∉ tightQueueFrameRegisters) member

private theorem rowFrame_to_destination {rowOffsets distances : ℕ} {target v : Fin G.n}
    {table : DirectLinkTable G} {s : ArithmeticState}
    (row : TightQueueRowFrame rowOffsets distances target v table s) :
    TightDestinationFrame rowOffsets distances target table s :=
  row.preserved (fun r member => fixedWhenDequeued s target r (frameRegister_ne_dequeued r member))
    (fun _ _ => rfl) rfl (by simp [setDequeued])

private theorem frameMember_not_dequeueScratch (r : ℕ) (member : r ∈ tightQueueFrameRegisters) :
    r ∉ ([13, 8] : List ℕ) := by
  intro changed
  simp [tightQueueFrameRegisters] at member
  simp at changed
  omega

/-- Dequeueing and scanning the resulting row implements one indexed
step of the abstract search. The next head is managed by the caller. -/
theorem tightQueueHandleVertexBlock_refines {rowOffsets distances head : ℕ}
    {target : Fin G.n} {table : DirectLinkTable G} {model : TightSearchState G}
    {s : ArithmeticState} (frame : TightDestinationFrame rowOffsets distances target table s)
    (sound : DirectLinkTableSound table) (valid : TightSearchInvariant target model)
    (hasEntry : head < model.queue.length) (index : s.nr 27 = head)
    (tail : s.nr 16 = model.queue.length)
    (memory : TightQueueNaturalMemory (s.nr 19) (s.nr 20) (s.nr 21) model s.nm)
    (entry : s.pc = 0) (running : s.halted = false) :
    let out := scanTightQueueIndex target table head model
    ∃ t, BlockRuns tightQueueHandleVertexBlock (tightQueueHandleVertexSteps G.n) s t ∧
      t.halted = false ∧ TightDestinationFrame rowOffsets distances target table t ∧
      t.nr 27 = head ∧ t.nr 16 = out.queue.length ∧
      TightQueueNaturalMemory (t.nr 19) (t.nr 20) (t.nr 21) out t.nm ∧ QueueWriteFootprint G.n s t := by
  change TightQueueRowFrame rowOffsets distances target target table (setDequeued s target) at frame
  have one : s.nr 6 = 1 := (fixedWhenDequeued s target 6 (by decide)).symm.trans frame.floyd.one
  let v := model.queue[head]
  obtain ⟨d, dequeues, ready, readVertex, sameNatural, sameReal, fixed⟩ :=
    tightQueueDequeueBlock_correct s entry running one
  have actualVertex : d.nr 8 = v.val := by
    rw [readVertex, index]
    exact memory.queue head hasEntry
  let rowStart := {d with pc := 0}
  have rowFrame : TightQueueRowFrame rowOffsets distances target v table rowStart :=
    frame.preserved (fun r member => (fixed r (frameMember_not_dequeueScratch r member)).trans
      (fixedWhenDequeued s target r (frameRegister_ne_dequeued r member)).symm)
      (fun a _ => congrFun sameNatural a) sameReal actualVertex
  have observedTail : rowStart.nr 16 = model.queue.length := (fixed 16 (by decide)).trans tail
  have observedMemory : TightQueueNaturalMemory (rowStart.nr 19) (rowStart.nr 20)
      (rowStart.nr 21) model rowStart.nm := by
    change TightQueueNaturalMemory (d.nr 19) (d.nr 20) (d.nr 21) model d.nm
    rwa [fixed 19 (by decide), fixed 20 (by decide), fixed 21 (by decide), sameNatural]
  obtain ⟨after, scans, afterReady, afterFrame, nextTail, nextMemory, scannedWrites⟩ :=
    tightQueueScanRowBlock_refines rowFrame valid sound (List.getElem_mem hasEntry)
      observedTail observedMemory rfl ready
  have sameHead : after.nr 27 = head :=
    (tightQueueScanRowBlock_fixed scans rfl ready rowFrame.floyd.one rowFrame.floyd.dimension 27
      (by decide)).trans ((fixed 27 (by decide)).trans index)
  have abstract : scanTightQueueIndex target table head model = scanTightIncoming target table v model := by
    simp [scanTightQueueIndex, List.getElem?_eq_getElem hasEntry, v]
  have relocatedFrame :
      TightQueueRowFrame rowOffsets distances target v table
        (relocateState tightQueueDequeueBlock.length after) :=
    afterFrame.preserved (fun _ _ => rfl) (fun _ _ => rfl) rfl afterFrame.dequeued
  have readWrites : QueueWriteFootprint G.n s rowStart :=
    QueueWriteFootprint.noMemoryWrites (fixed 19 (by decide)) (fixed 20 (by decide))
      (fixed 21 (by decide)) sameNatural
  refine ⟨_, dequeues.append scans, afterReady, rowFrame_to_destination relocatedFrame, sameHead, ?_, ?_,
    readWrites.trans (scannedWrites.trans (QueueWriteFootprint.noMemoryWrites rfl rfl rfl rfl))⟩
  · simpa only [relocateState, abstract] using nextTail
  · simpa only [relocateState, abstract] using nextMemory

private theorem TightDestinationFrame.preserved {rowOffsets distances : ℕ} {target : Fin G.n}
    {table : DirectLinkTable G} {s t : ArithmeticState}
    (frame : TightDestinationFrame rowOffsets distances target table s)
    (fixed : ∀ r ∈ tightQueueFrameRegisters, t.nr r = s.nr r)
    (natural : t.nm = s.nm) (real : t.rm = s.rm) :
    TightDestinationFrame rowOffsets distances target table t := by
  have same (r : ℕ) (member : r ∈ tightQueueFrameRegisters) :
      (setDequeued t target).nr r = (setDequeued s target).nr r :=
    (fixedWhenDequeued t target r (frameRegister_ne_dequeued r member)).trans
      ((fixed r member).trans (fixedWhenDequeued s target r (frameRegister_ne_dequeued r member)).symm)
  exact TightQueueRowFrame.preserved frame same (fun a _ => congrFun natural a) real
    (by simp [setDequeued])

private theorem TightDestinationFrame.preserved_prefix {rowOffsets distances : ℕ}
    {target : Fin G.n} {table : DirectLinkTable G} {s t : ArithmeticState}
    (frame : TightDestinationFrame rowOffsets distances target table s)
    (fixed : ∀ r ∈ tightQueueFrameRegisters, t.nr r = s.nr r)
    (natural : ∀ a < s.nr 19, t.nm a = s.nm a) (real : t.rm = s.rm) :
    TightDestinationFrame rowOffsets distances target table t := by
  have same (r : ℕ) (member : r ∈ tightQueueFrameRegisters) :
      (setDequeued t target).nr r = (setDequeued s target).nr r :=
    (fixedWhenDequeued t target r (frameRegister_ne_dequeued r member)).trans
      ((fixed r member).trans (fixedWhenDequeued s target r (frameRegister_ne_dequeued r member)).symm)
  exact TightQueueRowFrame.preserved frame same
    (fun a bound => natural a (by simpa [setDequeued] using bound)) real
    (by simp [setDequeued])

private theorem TightDestinationFrame.dimension {rowOffsets distances : ℕ} {target : Fin G.n}
    {table : DirectLinkTable G} {s : ArithmeticState}
    (frame : TightDestinationFrame rowOffsets distances target table s) : s.nr 5 = G.n :=
  (fixedWhenDequeued s target 5 (by decide)).symm.trans frame.floyd.dimension

private theorem TightDestinationFrame.one {rowOffsets distances : ℕ} {target : Fin G.n}
    {table : DirectLinkTable G} {s : ArithmeticState}
    (frame : TightDestinationFrame rowOffsets distances target table s) : s.nr 6 = 1 :=
  (fixedWhenDequeued s target 6 (by decide)).symm.trans frame.floyd.one

private def setHead (s : ArithmeticState) (i : ℕ) : ArithmeticState :=
  {s with pc := 0, nr := Function.update s.nr 27 i}

private theorem setHead_footprint (n : ℕ) (s : ArithmeticState) (i : ℕ) :
    QueueWriteFootprint n s (setHead s i) :=
  QueueWriteFootprint.noMemoryWrites (by simp [setHead]) (by simp [setHead])
    (by simp [setHead]) rfl

private theorem frameFixedAfterHead (s : ArithmeticState) (i r : ℕ)
    (allowed : r ∈ tightQueueFrameRegisters) : (setHead s i).nr r = s.nr r := by
  apply Function.update_of_ne
  intro same
  subst r
  exact (by decide : 27 ∉ tightQueueFrameRegisters) allowed

/-- Starting with a seeded destination, the prescribed n-dequeue machine
loop implements the complete abstract reverse search and its pointer table. -/
theorem tightQueueFromSeed_refines {rowOffsets distances : ℕ} {target : Fin G.n}
    {table : DirectLinkTable G} {s : ArithmeticState}
    (connected : Connected G) (nonnegative : Nonnegative G)
    (frame : TightDestinationFrame rowOffsets distances target table s)
    (sound : DirectLinkTableSound table)
    (representative : DirectLinkRepresentatives G (tableChooses table))
    (tail : s.nr 16 = 1)
    (memory : TightQueueNaturalMemory (s.nr 19) (s.nr 20) (s.nr 21) (initialTightSearch target) s.nm)
    (entry : s.pc = 0) (running : s.halted = false) :
    let out := tightSearchAfter target table G.n
    ∃ t, BlockRuns (countedLoopFromZero 6 27 5 tightQueueHandleVertexBlock)
        (1 + (G.n * (tightQueueHandleVertexSteps G.n + 3) + 1)) s t ∧
      t.halted = false ∧ TightDestinationFrame rowOffsets distances target table t ∧
      t.nr 16 = out.queue.length ∧
      TightQueueNaturalMemory (t.nr 19) (t.nr 20) (t.nr 21) out t.nm ∧ QueueWriteFootprint G.n s t := by
  let through := tightSearchAfter target table
  let inv (cut : ℕ) (m : ArithmeticState) :=
    m.pc = 0 ∧ m.halted = false ∧ m.nr 27 = cut ∧
      TightDestinationFrame rowOffsets distances target table m ∧
      m.nr 16 = (through cut).queue.length ∧
      TightQueueNaturalMemory (m.nr 19) (m.nr 20) (m.nr 21) (through cut) m.nm ∧
      QueueWriteFootprint G.n s m
  have init : inv 0 (setHead s 0) := by
    refine ⟨rfl, running, by simp [setHead],
      frame.preserved (fun r => frameFixedAfterHead s 0 r) rfl rfl, ?_, ?_,
      setHead_footprint G.n s 0⟩
    · simpa [setHead, through, tightSearchAfter, initialTightSearch] using tail
    · simpa [setHead, through, tightSearchAfter] using memory
  have control (cut : ℕ) (m : ArithmeticState) (w : inv cut m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 27 = cut ∧ m.nr 5 = G.n :=
    ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1.dimension⟩
  have advance (cut : ℕ) (more : cut < G.n) (m : ArithmeticState) (w : inv cut m) :
      ∃ t, BlockRuns tightQueueHandleVertexBlock (tightQueueHandleVertexSteps G.n) m t ∧
        t.halted = false ∧ inv (cut + 1)
          {t with pc := 0, nr := Function.update t.nr 27 (t.nr 27 + t.nr 6)} := by
    obtain ⟨mEntry, mRunning, mIndex, mFrame, mTail, mMemory, mWrites⟩ := w
    obtain ⟨valid, scanned⟩ :=
      tightSearchAfter_invariant connected nonnegative target table sound representative cut more.le
    have hasEntry := tightQueue_no_underflow connected nonnegative target (tableChooses table)
      representative (through cut).queue valid.seed cut scanned more
    obtain ⟨t, run, ready, tFrame, tHead, tTail, tMemory, tWrites⟩ := tightQueueHandleVertexBlock_refines
      mFrame sound valid hasEntry mIndex mTail mMemory mEntry mRunning
    have reset : {t with pc := 0, nr := Function.update t.nr 27 (t.nr 27 + t.nr 6)} =
        setHead t (cut + 1) := by simp [setHead, tHead, tFrame.one]
    have nextModel : through (cut + 1) = scanTightQueueIndex target table cut (through cut) := by
      simp [through, tightSearchAfter, List.range_succ, List.foldl_append]
    refine ⟨t, run, ready, ?_⟩
    rw [reset]
    refine ⟨rfl, ready, by simp [setHead],
      tFrame.preserved (fun r => frameFixedAfterHead t (cut + 1) r) rfl rfl, ?_, ?_,
      mWrites.trans (tWrites.trans (setHead_footprint G.n t (cut + 1)))⟩
    · rw [nextModel]
      simpa [setHead] using tTail
    · rw [nextModel]
      simpa [setHead] using tMemory
  obtain ⟨last, final, run⟩ := countedLoopFromZero_correct 6 27 5 G.n
    (tightQueueHandleVertexSteps G.n) tightQueueHandleVertexBlock inv entry running init control advance
  obtain ⟨_, finalRunning, _, finalFrame, finalTail, finalMemory, finalWrites⟩ := final
  exact ⟨_, run, finalRunning, finalFrame.preserved (fun _ _ => rfl) rfl rfl, finalTail, finalMemory,
    finalWrites.trans (QueueWriteFootprint.noMemoryWrites rfl rfl rfl rfl)⟩

def reserveTargetRow (s : ArithmeticState) (target : Fin G.n) : ArithmeticState :=
  {s with nr := Function.update s.nr 21 (s.nr 26 + G.n * target.val)}

/-- Before seeding a destination, the future row base is determined by
the global next-edge table and the natural row-offset table. -/
def TightTargetSetupFrame (rowOffsets distances : ℕ) (target : Fin G.n)
    (table : DirectLinkTable G) (s : ArithmeticState) : Prop :=
  TightDestinationFrame rowOffsets distances target table (reserveTargetRow s target)

theorem TightTargetSetupFrame.separation {rowOffsets distances : ℕ} {target : Fin G.n}
    {table : DirectLinkTable G} {s : ArithmeticState}
    (frame : TightTargetSetupFrame rowOffsets distances target table s) :
    QueueSlicesSeparated (s.nr 19) (s.nr 20) (s.nr 26 + G.n * target.val) G.n := by
  change TightQueueRowFrame rowOffsets distances target target table
    (setDequeued (reserveTargetRow s target) target) at frame
  simpa [reserveTargetRow, setDequeued] using frame.separation

theorem TightTargetSetupFrame.basesOrdered {rowOffsets distances : ℕ} {target : Fin G.n}
    {table : DirectLinkTable G} {s : ArithmeticState}
    (frame : TightTargetSetupFrame rowOffsets distances target table s) :
    s.nr 19 ≤ s.nr 20 ∧ s.nr 19 ≤ s.nr 26 + G.n * target.val := by
  change TightQueueRowFrame rowOffsets distances target target table
    (setDequeued (reserveTargetRow s target) target) at frame
  exact ⟨by simpa [reserveTargetRow, setDequeued] using frame.queueAfterRank,
    by simpa [reserveTargetRow, setDequeued] using frame.nextAfterRank⟩

theorem TightTargetSetupFrame.preserved {rowOffsets distances : ℕ} {target : Fin G.n}
    {table : DirectLinkTable G} {s t : ArithmeticState}
    (frame : TightTargetSetupFrame rowOffsets distances target table s)
    (fixed : ∀ r ∈ tightQueueGlobalRegisters, t.nr r = s.nr r)
    (natural : ∀ a < s.nr 19, t.nm a = s.nm a) (real : t.rm = s.rm) :
    TightTargetSetupFrame rowOffsets distances target table t := by
  apply TightDestinationFrame.preserved_prefix frame
  · intro r stable
    by_cases row : r = 21
    · subst r
      simp [reserveTargetRow, fixed 26 (by decide)]
    · have globalReg : r ∈ tightQueueGlobalRegisters := by
        simp [tightQueueFrameRegisters] at stable
        simp [tightQueueGlobalRegisters]
        omega
      simp [reserveTargetRow, Function.update_of_ne row, fixed r globalReg]
  · intro a low
    exact natural a (by simpa [reserveTargetRow] using low)
  · exact real

/-- A contiguous natural-memory layout and the initialized matrices
provide the target setup frame, with no initialization of the work slices
required from the caller. -/
theorem TightTargetSetupFrame.ofMatrices {rowOffsets distances : ℕ} {target : Fin G.n}
    {table : DirectLinkTable G} {s : ArithmeticState}
    (floyd : FloydFrame G.n rowOffsets distances s)
    (targetAt : s.nr 7 = target.val) (count : s.nr 10 = G.q) (sentinel : s.nr 17 = G.n)
    (rowsBelow : rowOffsets + G.n ≤ s.nr 19)
    (linksBelow : s.nr 11 + G.n * G.n ≤ s.nr 19)
    (ranksBeforeQueue : s.nr 19 + G.n ≤ s.nr 20)
    (queueBeforeNext : s.nr 20 + G.n ≤ s.nr 26)
    (direct : ∀ a b : Fin G.n,
      s.nm (s.nr 11 + G.n * a.val + b.val) =
        ((table a b).map (fun step => step.1.val)).getD G.q)
    (weights : ∀ e : Fin G.q, s.rm e.val = G.weight e)
    (distanceData : ∀ a b : Fin G.n,
      s.rm (distances + G.n * a.val + b.val) = distance G a b) :
    TightTargetSetupFrame rowOffsets distances target table s := by
  let planned := setDequeued (reserveTargetRow s target) target
  have fixed (r : ℕ) (notDequeue : r ≠ 8) (notRow : r ≠ 21) : planned.nr r = s.nr r := by
    simp [planned, setDequeued, reserveTargetRow, Function.update_of_ne notDequeue,
      Function.update_of_ne notRow]
  have plannedRow : planned.nr 21 = s.nr 26 + G.n * target.val := by
    simp [planned, setDequeued, reserveTargetRow]
  have copied : FloydFrame G.n rowOffsets distances planned :=
    floyd.preserved (fun r lower upper => fixed r (by omega) (by omega)) rfl
  change TightQueueRowFrame rowOffsets distances target target table planned
  refine ⟨copied, (fixed 7 (by decide) (by decide)).trans targetAt, by simp [planned, setDequeued],
    (fixed 10 (by decide) (by decide)).trans count,
    (fixed 17 (by decide) (by decide)).trans sentinel, ?_, ?_, ?_, ?_, ?_, ?_, weights, distanceData⟩
  · rw [fixed 19 (by decide) (by decide), fixed 20 (by decide) (by decide)]
    omega
  · rw [fixed 19 (by decide) (by decide), plannedRow]
    omega
  · rw [fixed 19 (by decide) (by decide), fixed 20 (by decide) (by decide), plannedRow]
    refine ⟨?_, ?_, ?_⟩ <;> intro i hi j hj eq <;> omega
  · intro i hi
    rw [fixed 19 (by decide) (by decide)]
    omega
  · intro a b
    have within : G.n * a.val + b.val < G.n * G.n := by
      have rowBound : G.n * (a.val + 1) ≤ G.n * G.n :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt a.isLt)
      rw [Nat.mul_succ] at rowBound
      exact (Nat.add_lt_add_left b.isLt _).trans_le rowBound
    rw [fixed 11 (by decide) (by decide), fixed 19 (by decide) (by decide)]
    omega
  · intro a b
    change s.nm (planned.nr 11 + G.n * a.val + b.val) = _
    rw [fixed 11 (by decide) (by decide)]
    exact direct a b

/-- The actual clear and seed blocks establish the rank and queue arrays
for a fresh destination while preserving its read-only operands. -/
theorem tightQueueInitializeDestination_refines {rowOffsets distances : ℕ} {target : Fin G.n}
    {table : DirectLinkTable G} {s : ArithmeticState}
    (setup : TightTargetSetupFrame rowOffsets distances target table s)
    (zero : s.nr 28 = 0) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns (appendBlock tightQueueClearBlock tightQueueSeedBlock)
        (tightQueueClearSteps G.n + 9) s t ∧
      t.halted = false ∧ TightDestinationFrame rowOffsets distances target table t ∧
      t.nr 21 = s.nr 26 + G.n * target.val ∧ t.nr 16 = 1 ∧
      TightQueueNaturalMemory (t.nr 19) (t.nr 20) (t.nr 21) (initialTightSearch target) t.nm ∧
      QueueWriteFootprint G.n (reserveTargetRow s target) t := by
  let row := s.nr 26 + G.n * target.val
  let planned := reserveTargetRow s target
  change TightDestinationFrame rowOffsets distances target table planned at setup
  have frame : TightQueueRowFrame rowOffsets distances target target table (setDequeued planned target) :=
    setup
  have one : s.nr 6 = 1 := by simpa [reserveTargetRow, planned] using setup.one
  have size : s.nr 5 = G.n := by simpa [reserveTargetRow, planned] using setup.dimension
  have targetAt : s.nr 7 = target.val := by
    simpa [reserveTargetRow, planned, setDequeued] using frame.target
  have linkCount : s.nr 10 = G.q := by
    simpa [reserveTargetRow, planned, setDequeued] using frame.links
  have sentinel : s.nr 17 = G.n := by
    simpa [reserveTargetRow, planned, setDequeued] using frame.sentinel
  have queueAfterRank : s.nr 19 ≤ s.nr 20 := by
    simpa [reserveTargetRow, planned, setDequeued] using frame.queueAfterRank
  have rowAfterRank : s.nr 19 ≤ row := by
    simpa [reserveTargetRow, planned, setDequeued, row] using frame.nextAfterRank
  have separated : QueueSlicesSeparated (s.nr 19) (s.nr 20) row G.n := by
    simpa [reserveTargetRow, planned, setDequeued, row] using frame.separation
  have lowRow : rowOffsets + target.val < s.nr 19 := by
    simpa [reserveTargetRow, planned, setDequeued] using frame.lowRows target.val target.isLt
  have rowBase : s.nr 3 = rowOffsets := by
    simpa [reserveTargetRow, planned, setDequeued] using frame.floyd.tableBase
  have rawOffset : s.nm (rowOffsets + target.val) = G.n * target.val :=
    frame.floyd.rows target.val target.isLt
  obtain ⟨c, clear, cReady, cReal, cFixed, cleared⟩ := tightQueueClearBlock_correct s entry running one
  have clearRun : BlockRuns tightQueueClearBlock (tightQueueClearSteps G.n) s c := by
    simpa only [size] using clear
  have clearedRanks (u : Fin G.n) : c.nm (s.nr 19 + u.val) = G.n := by
    rw [cleared, size, if_pos ⟨by omega, Nat.add_lt_add_left u.isLt _⟩, sentinel]
  let seeded := Function.update
    (Function.update c.nm (s.nr 19 + target.val) 0) (s.nr 20) target.val
  have readRow : c.nr 26 + seeded (c.nr 3 + c.nr 7) = row := by
    rw [cFixed 26 (by decide), cFixed 3 (by decide), cFixed 7 (by decide), rowBase, targetAt]
    unfold seeded
    rw [Function.update_of_ne (show rowOffsets + target.val ≠ s.nr 20 by omega),
      Function.update_of_ne (show rowOffsets + target.val ≠ s.nr 19 + target.val by omega),
      cleared, if_neg (by omega), rawOffset]
  have readExpanded : c.nr 26 + Function.update
      (Function.update c.nm (s.nr 19 + target.val) 0) (s.nr 20) target.val
        (c.nr 3 + target.val) = row := by
    simpa only [seeded, cFixed 7 (by decide), targetAt] using readRow
  obtain ⟨seed, writes, seedReady, seedReal, seedFixed, tail, targetRow, stored⟩ :=
    tightQueueSeedBlock_correct {c with pc := 0} rfl cReady ((cFixed 6 (by decide)).trans one)
  have targetRow' : seed.nr 21 = row := by
    simpa only [cFixed 19 (by decide), cFixed 7 (by decide), cFixed 28 (by decide),
      cFixed 20 (by decide), targetAt, zero, seeded, readExpanded] using targetRow
  have naturalWrites : seed.nm = Function.update seeded (row + target.val) G.q := by
    simpa only [cFixed 19 (by decide), cFixed 7 (by decide), cFixed 28 (by decide),
      cFixed 20 (by decide), cFixed 10 (by decide), targetAt, zero, linkCount, seeded, readExpanded]
      using stored
  have fixedOther (r : ℕ) (notRow : r ≠ 21) (member : r ∈ tightQueueFrameRegisters) :
      seed.nr r = s.nr r := by
    have unmodifiedClear : r ∉ ([9, 12] : List ℕ) := by
      intro touched
      simp [tightQueueFrameRegisters] at member
      simp at touched
      omega
    have unmodifiedSeed : r ∉ ([12, 16, 21, 14] : List ℕ) := by
      intro touched
      simp [tightQueueFrameRegisters] at member
      simp at touched
      omega
    exact (seedFixed r unmodifiedSeed).trans (cFixed r unmodifiedClear)
  have preserved (a : ℕ) (low : a < s.nr 19) : seed.nm a = s.nm a := by
    rw [naturalWrites, Function.update_of_ne (show a ≠ row + target.val by omega)]
    unfold seeded
    rw [Function.update_of_ne (show a ≠ s.nr 20 by omega),
      Function.update_of_ne (show a ≠ s.nr 19 + target.val by omega), cleared, if_neg (by omega)]
  let t := relocateState tightQueueClearBlock.length seed
  have fixPlanned (r : ℕ) (member : r ∈ tightQueueFrameRegisters) : t.nr r = planned.nr r := by
    by_cases isRow : r = 21
    · subst r
      simpa [t, relocateState, planned, reserveTargetRow, row] using targetRow'
    · exact (fixedOther r isRow member).trans (Function.update_of_ne isRow _ _).symm
  have resultFrame : TightDestinationFrame rowOffsets distances target table t :=
    setup.preserved_prefix fixPlanned
      (fun a low => preserved a (by simpa [planned, reserveTargetRow] using low))
      (seedReal.trans cReal)
  have resultMemory := tightSearchSeed_memory target (s.nr 19) (s.nr 20) row c.nm separated clearedRanks
  refine ⟨t, clearRun.append writes, seedReady, resultFrame, targetRow', tail, ?_, ?_⟩
  · change TightQueueNaturalMemory (seed.nr 19) (seed.nr 20) (seed.nr 21)
      (initialTightSearch target) seed.nm
    rw [fixedOther 19 (by decide) (by decide), fixedOther 20 (by decide) (by decide),
      targetRow', naturalWrites]
    exact resultMemory
  · refine ⟨fixPlanned 19 (by decide), fixPlanned 20 (by decide),
      fixPlanned 21 (by decide), fun a unaffected => ?_⟩
    have outside : OutsideQueueSlices (s.nr 19) (s.nr 20) row G.n a := by
      simpa [planned, reserveTargetRow, row] using unaffected
    have notCleared : ¬(s.nr 19 ≤ a ∧ a < s.nr 19 + G.n) := by
      rintro ⟨lower, upper⟩
      exact outside.1 (a - s.nr 19) (by omega) (by omega)
    have otherQueue : a ≠ s.nr 20 := by
      simpa using outside.2.1 0 (Nat.zero_lt_of_lt target.isLt)
    change seed.nm a = s.nm a
    rw [naturalWrites, Function.update_of_ne (outside.2.2 target.val target.isLt)]
    unfold seeded
    rw [Function.update_of_ne otherQueue, Function.update_of_ne (outside.1 target.val target.isLt),
      cleared, size, if_neg notCleared]

/-- The fixed program for one target initializes its arrays and executes
the whole dense reverse search in quadratic time. Every non-target
vertex then has its tight next edge stored at the expected row address. -/
theorem tightQueueTargetBlock_refines {rowOffsets distances : ℕ} {target : Fin G.n}
    {table : DirectLinkTable G} {s : ArithmeticState}
    (connected : Connected G) (nonnegative : Nonnegative G)
    (setup : TightTargetSetupFrame rowOffsets distances target table s)
    (sound : DirectLinkTableSound table)
    (representative : DirectLinkRepresentatives G (tableChooses table))
    (zero : s.nr 28 = 0) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns tightQueueTargetBlock (tightQueueTargetSteps G.n) s t ∧
      t.halted = false ∧
      TightDestinationFrame rowOffsets distances target table t ∧
      t.nr 21 = s.nr 26 + G.n * target.val ∧
      QueueWriteFootprint G.n (reserveTargetRow s target) t ∧
      ∀ u : Fin G.n, u ≠ target → ∃ step : Traversal G,
        start G step = u ∧ (G.directed step.1 = false ∨ step.2 = true) ∧
        tightTraversal G target step ∧
        t.nm (s.nr 26 + G.n * target.val + u.val) = step.1.val ∧
        (tightSearchAfter target table G.n).rank (finish G step) <
          (tightSearchAfter target table G.n).rank u := by
  obtain ⟨seed, initializes, seedReady, seededFrame, row, tail, seeded, initialWrites⟩ :=
    tightQueueInitializeDestination_refines setup zero entry running
  let seededEntry := {seed with pc := 0}
  have pcFrame : TightDestinationFrame rowOffsets distances target table seededEntry :=
    seededFrame.preserved (fun _ _ => rfl) rfl rfl
  obtain ⟨searched, executes, ready, searchedFrame, _, encoded, searchWrites⟩ := tightQueueFromSeed_refines
    connected nonnegative pcFrame sound representative tail seeded rfl seedReady
  let final := relocateState (appendBlock tightQueueClearBlock tightQueueSeedBlock).length searched
  have finalFrame : TightDestinationFrame rowOffsets distances target table final :=
    searchedFrame.preserved (fun _ _ => rfl) rfl rfl
  have finalRow : searched.nr 21 = s.nr 26 + G.n * target.val :=
    (tightQueueFromSeed_fixedNextRow executes rfl seedReady pcFrame.one pcFrame.dimension).trans row
  obtain ⟨valid, all⟩ := tightSearchAfter_complete connected nonnegative target table sound representative
  have footprint : QueueWriteFootprint G.n (reserveTargetRow s target) final :=
    initialWrites.trans ((QueueWriteFootprint.noMemoryWrites rfl rfl rfl rfl :
      QueueWriteFootprint G.n seed seededEntry).trans
        (searchWrites.trans (QueueWriteFootprint.noMemoryWrites rfl rfl rfl rfl)))
  refine ⟨final, initializes.append executes, ready, finalFrame, finalRow, footprint, ?_⟩
  intro u away
  obtain ⟨step, stored, begins, legal, tight, _, lower⟩ := valid.pointers u (all u) away
  have value := encoded.next u step stored
  rw [finalRow] at value
  exact ⟨step, begins, legal, tight, value, lower⟩

end VehicleRoutingSurvey.Routing
end RppSource_TightQueueRowRefinement

/-! runtime/TightQueueAllRows.lean -/
section RppSource_TightQueueAllRows
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

def setQueueDestination (s : ArithmeticState) (i : ℕ) : ArithmeticState :=
  {s with pc := 0, nr := Function.update s.nr 7 i}

def TightAllTargetsFrame (rowOffsets distances : ℕ) (table : DirectLinkTable G)
    (s : ArithmeticState) : Prop :=
  ∀ target : Fin G.n,
    TightTargetSetupFrame rowOffsets distances target table (setQueueDestination s target.val)

private theorem TightAllTargetsFrame.preserved {rowOffsets distances : ℕ}
    {table : DirectLinkTable G} {s t : ArithmeticState}
    (frame : TightAllTargetsFrame rowOffsets distances table s)
    (fixed : ∀ r ∈ tightQueueGlobalRegisters, r ≠ 7 → t.nr r = s.nr r)
    (natural : ∀ a < s.nr 19, t.nm a = s.nm a) (real : t.rm = s.rm) :
    TightAllTargetsFrame rowOffsets distances table t := by
  intro target
  apply (frame target).preserved
  · intro r stable
    by_cases selected : r = 7
    · subst r
      simp [setQueueDestination]
    · simp [setQueueDestination, Function.update_of_ne selected, fixed r stable selected]
  · intro a low
    exact natural a (by simpa [setQueueDestination] using low)
  · exact real

private theorem TightAllTargetsFrame.setCounter {rowOffsets distances : ℕ}
    {table : DirectLinkTable G} {s : ArithmeticState}
    (frame : TightAllTargetsFrame rowOffsets distances table s) (i : ℕ) :
    TightAllTargetsFrame rowOffsets distances table (setQueueDestination s i) :=
  frame.preserved (fun _ _ different => Function.update_of_ne different _ _) (fun _ _ => rfl) rfl

/-- The exact fields in one complete next-edge row. Ranks are proof
witnesses from the abstract search for that destination. -/
def TightStoredRow (target : Fin G.n) (table : DirectLinkTable G) (nextBase : ℕ)
    (memory : ℕ → ℕ) : Prop :=
  ∀ source : Fin G.n, source ≠ target → ∃ step : Traversal G,
    start G step = source ∧ (G.directed step.1 = false ∨ step.2 = true) ∧
    tightTraversal G target step ∧
    memory (nextBase + G.n * target.val + source.val) = step.1.val ∧
    (tightSearchAfter target table G.n).rank (finish G step) <
      (tightSearchAfter target table G.n).rank source

private theorem previousRowOutside {rowOffsets distances : ℕ}
    {table : DirectLinkTable G} {s : ArithmeticState}
    (frame : TightAllTargetsFrame rowOffsets distances table s)
    {previous current source : Fin G.n} (different : previous ≠ current) :
    OutsideQueueSlices (s.nr 19) (s.nr 20) (s.nr 26 + G.n * current.val) G.n
      (s.nr 26 + G.n * previous.val + source.val) := by
  have disjoint : QueueSlicesSeparated (s.nr 19) (s.nr 20)
      (s.nr 26 + G.n * previous.val) G.n := by
    simpa [setQueueDestination] using (frame previous).separation
  refine ⟨fun i hi => (disjoint.rankNext i hi _ source.isLt).symm,
    fun i hi => (disjoint.queueNext i hi _ source.isLt).symm, ?_⟩
  intro j hj eq
  have offsets : G.n * previous.val + source.val = G.n * current.val + j :=
    Nat.add_left_cancel (by simpa only [Nat.add_assoc] using eq)
  exact different (Fin.ext ((denseMatrixOffset_eq_iff source.isLt hj).mp offsets).1)

/-- With sentinel registers initialized, the outer loop generates every
destination row and preserves each previously generated row. -/
theorem tightQueueAllRowsFromSetup_refines {rowOffsets distances : ℕ}
    {table : DirectLinkTable G} {s : ArithmeticState}
    (connected : Connected G) (nonnegative : Nonnegative G)
    (sound : DirectLinkTableSound table)
    (representative : DirectLinkRepresentatives G (tableChooses table))
    (frame : TightAllTargetsFrame rowOffsets distances table s)
    (size : s.nr 5 = G.n) (one : s.nr 6 = 1) (zero : s.nr 28 = 0)
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns (countedLoopFromZero 6 7 5 tightQueueTargetBlock)
        (1 + (G.n * (tightQueueTargetSteps G.n + 3) + 1)) s t ∧
      t.halted = false ∧ t.rm = s.rm ∧ t.nr 26 = s.nr 26 ∧
      (∀ a < s.nr 19, t.nm a = s.nm a) ∧
      ∀ target, TightStoredRow target table (s.nr 26) t.nm := by
  let inv (cut : ℕ) (m : ArithmeticState) :=
    m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = cut ∧ m.nr 5 = G.n ∧ m.nr 6 = 1 ∧
      m.nr 28 = 0 ∧ m.nr 26 = s.nr 26 ∧ m.rm = s.rm ∧
      m.nr 19 = s.nr 19 ∧ (∀ a < s.nr 19, m.nm a = s.nm a) ∧
      TightAllTargetsFrame rowOffsets distances table m ∧
      ∀ target : Fin G.n, target.val < cut → TightStoredRow target table (s.nr 26) m.nm
  have initial : inv 0 (setQueueDestination s 0) := by
    refine ⟨rfl, running, by simp [setQueueDestination], ?_, ?_, ?_, ?_, rfl,
      by simp [setQueueDestination], fun _ _ => rfl,
      frame.setCounter 0, fun target impossible => (Nat.not_lt_zero _ impossible).elim⟩
    · simpa [setQueueDestination] using size
    · simpa [setQueueDestination] using one
    · simpa [setQueueDestination] using zero
    · simp [setQueueDestination]
  have control (cut : ℕ) (m : ArithmeticState) (valid : inv cut m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = cut ∧ m.nr 5 = G.n :=
    ⟨valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1⟩
  have advance (cut : ℕ) (more : cut < G.n) (m : ArithmeticState) (valid : inv cut m) :
      ∃ t, BlockRuns tightQueueTargetBlock (tightQueueTargetSteps G.n) m t ∧
        t.halted = false ∧ inv (cut + 1)
          {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 6)} := by
    obtain ⟨mEntry, mRunning, mIndex, mSize, mOne, mZero, mBase, mReal,
      mRankBase, mNatural, mFrame, done⟩ := valid
    let current : Fin G.n := ⟨cut, more⟩
    have currentSetup : TightTargetSetupFrame rowOffsets distances current table m := by
      have unchanged : setQueueDestination m current.val = m := by
        have registered : current.val = m.nr 7 := mIndex.symm
        unfold setQueueDestination
        rw [registered, Function.update_eq_self]
        cases m
        cases mEntry
        rfl
      simpa only [unchanged] using mFrame current
    obtain ⟨t, run, ready, _, _, footprint, recent⟩ :=
      tightQueueTargetBlock_refines connected nonnegative currentSetup sound representative
        mZero mEntry mRunning
    obtain ⟨real, fixed⟩ := tightQueueTargetBlock_preserves run mEntry mRunning mOne mSize
    have low (a : ℕ) (below : a < m.nr 19) : t.nm a = m.nm a := by
      obtain ⟨queueBound, nextBound⟩ := currentSetup.basesOrdered
      have outside : OutsideQueueSlices (m.nr 19) (m.nr 20)
          (m.nr 26 + G.n * current.val) G.n a :=
        ⟨fun i _ eq => by omega, fun i _ eq => by omega, fun i _ eq => by omega⟩
      exact footprint.outside a (by simpa [reserveTargetRow] using outside)
    have tFrame := mFrame.preserved (fun r hr _ => fixed r hr) low real
    have nextRows (target : Fin G.n) (considered : target.val < cut + 1) :
        TightStoredRow target table (s.nr 26) t.nm := by
      by_cases thisRow : target = current
      · subst target
        simpa only [TightStoredRow, mBase] using recent
      · have earlier : target.val < cut := by
          have different : target.val ≠ cut := fun eq => thisRow (Fin.ext eq)
          omega
        intro source away
        obtain ⟨step, begins, legal, tight, stored, falls⟩ := done target earlier source away
        have location := previousRowOutside (source := source) mFrame thisRow
        have stable := footprint.outside (m.nr 26 + G.n * target.val + source.val) (by
          simpa [reserveTargetRow] using location)
        rw [mBase] at stable
        exact ⟨step, begins, legal, tight, stable.trans stored, falls⟩
    have reset : {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 6)} =
        setQueueDestination t (cut + 1) := by
      simp [setQueueDestination, fixed 7 (by decide), fixed 6 (by decide), mIndex, mOne]
    refine ⟨t, run, ready, ?_⟩
    rw [reset]
    refine ⟨rfl, ready, by simp [setQueueDestination], ?_, ?_, ?_, ?_, real.trans mReal,
      by simpa [setQueueDestination] using (fixed 19 (by decide)).trans mRankBase,
      fun a h => (low a (by simpa only [mRankBase] using h)).trans (mNatural a h),
      tFrame.setCounter (cut + 1), nextRows⟩
    · simpa [setQueueDestination] using (fixed 5 (by decide)).trans mSize
    · simpa [setQueueDestination] using (fixed 6 (by decide)).trans mOne
    · simpa [setQueueDestination] using (fixed 28 (by decide)).trans mZero
    · simpa [setQueueDestination] using (fixed 26 (by decide)).trans mBase
  obtain ⟨last, final, run⟩ := countedLoopFromZero_correct 6 7 5 G.n
    (tightQueueTargetSteps G.n) tightQueueTargetBlock inv entry running initial control advance
  obtain ⟨_, ready, _, _, _, _, next, real, _, natural, _, rows⟩ := final
  exact ⟨_, run, ready, real, next, natural, fun target => rows target target.isLt⟩

def tightQueuePreparedState (s : ArithmeticState) : ArithmeticState :=
  {s with pc := 0, nr := Function.update (Function.update s.nr 28 0) 17 (s.nr 5)}

theorem TightAllTargetsFrame.ofMatrices {rowOffsets distances : ℕ}
    {table : DirectLinkTable G} {s : ArithmeticState}
    (floyd : FloydFrame G.n rowOffsets distances s)
    (count : s.nr 10 = G.q)
    (rowsBelow : rowOffsets + G.n ≤ s.nr 19)
    (linksBelow : s.nr 11 + G.n * G.n ≤ s.nr 19)
    (ranksBeforeQueue : s.nr 19 + G.n ≤ s.nr 20)
    (queueBeforeNext : s.nr 20 + G.n ≤ s.nr 26)
    (direct : ∀ a b : Fin G.n,
      s.nm (s.nr 11 + G.n * a.val + b.val) =
        ((table a b).map (fun step => step.1.val)).getD G.q)
    (weights : ∀ e : Fin G.q, s.rm e.val = G.weight e)
    (distanceData : ∀ a b : Fin G.n,
      s.rm (distances + G.n * a.val + b.val) = distance G a b) :
    TightAllTargetsFrame rowOffsets distances table (tightQueuePreparedState s) := by
  intro target
  let prepared := setQueueDestination (tightQueuePreparedState s) target.val
  have preparedFrame : FloydFrame G.n rowOffsets distances prepared :=
    floyd.preserved (fun r lower upper => by
      simp [prepared, setQueueDestination, tightQueuePreparedState,
        Function.update_of_ne (show r ≠ 7 by omega), Function.update_of_ne (show r ≠ 17 by omega),
        Function.update_of_ne (show r ≠ 28 by omega)]) rfl
  refine TightTargetSetupFrame.ofMatrices preparedFrame (by simp [prepared, setQueueDestination])
    (by simpa [prepared, setQueueDestination, tightQueuePreparedState] using count)
    (by simp [prepared, setQueueDestination, tightQueuePreparedState, floyd.dimension]) ?_ ?_ ?_ ?_ ?_
    weights distanceData
  · simpa [prepared, setQueueDestination, tightQueuePreparedState] using rowsBelow
  · simpa [prepared, setQueueDestination, tightQueuePreparedState] using linksBelow
  · simpa [prepared, setQueueDestination, tightQueuePreparedState] using ranksBeforeQueue
  · simpa [prepared, setQueueDestination, tightQueuePreparedState] using queueBeforeNext
  · simpa [prepared, setQueueDestination, tightQueuePreparedState] using direct

/-- The actual cubic-time program writes tight noncycling next edges for
all destinations, while preserving its real operand memory. -/
theorem tightQueueAllBlock_rows {rowOffsets distances : ℕ}
    {table : DirectLinkTable G} {s : ArithmeticState}
    (connected : Connected G) (nonnegative : Nonnegative G)
    (sound : DirectLinkTableSound table)
    (representative : DirectLinkRepresentatives G (tableChooses table))
    (frame : TightAllTargetsFrame rowOffsets distances table (tightQueuePreparedState s))
    (size : s.nr 5 = G.n) (one : s.nr 6 = 1) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns tightQueueAllBlock
        (31 * G.n ^ 3 + 12 * G.n ^ 2 + 16 * G.n + 4) s t ∧
      t.halted = false ∧ t.rm = s.rm ∧ t.nr 26 = s.nr 26 ∧
      (∀ a < s.nr 19, t.nm a = s.nm a) ∧
      ∀ target, TightStoredRow target table (s.nr 26) t.nm := by
  let afterSetup := tightQueuePreparedState s
  have setupRun : BlockRuns tightQueueSetupBlock 2 s {afterSetup with pc := 2} :=
    tightQueueSetupBlock_correct s entry running one
  have preparedSize : afterSetup.nr 5 = G.n := by simpa [afterSetup, tightQueuePreparedState] using size
  have preparedOne : afterSetup.nr 6 = 1 := by simpa [afterSetup, tightQueuePreparedState] using one
  have preparedZero : afterSetup.nr 28 = 0 := by simp [afterSetup, tightQueuePreparedState]
  obtain ⟨result, search, ready, real, next, natural, rows⟩ := tightQueueAllRowsFromSetup_refines
    connected nonnegative sound representative frame preparedSize preparedOne preparedZero rfl running
  have combined : BlockRuns tightQueueAllBlock (tightQueueAllSteps G.n) s
      (relocateState tightQueueSetupBlock.length result) :=
    setupRun.append search
  refine ⟨relocateState tightQueueSetupBlock.length result,
    tightQueueAllSteps_eq _ ▸ combined, ready, real, ?_, ?_, ?_⟩
  · simpa [afterSetup, tightQueuePreparedState, relocateState] using next
  · intro a below
    exact natural a (by simpa [afterSetup, tightQueuePreparedState] using below)
  · simpa [afterSetup, tightQueuePreparedState, relocateState] using rows

end VehicleRoutingSurvey.Routing
end RppSource_TightQueueAllRows

/-! runtime/APSPPaths.lean -/
section RppSource_APSPPaths
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

def apspAndTightPathsBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock floydWarshallBlock apspQueueLayoutBlock) tightQueueAllBlock

/-- From dense initialized adjacency tables, the exact machine produces
all graph distances and every next-edge pointer. The weight input prefix
remains available to subsequent routing blocks. -/
theorem apspAndTightPathsBlock_correct {rowOffsets distances : ℕ}
    {table : DirectLinkTable G} {s : ArithmeticState}
    (connected : Connected G) (nonnegative : Nonnegative G)
    (frame : FloydFrame G.n rowOffsets distances s)
    (sound : DirectLinkTableSound table)
    (representative : DirectLinkRepresentatives G (tableChooses table))
    (count : s.nm 1 = G.q) (weightsBelow : G.q ≤ distances)
    (weights : ∀ e : Fin G.q, s.rm e.val = G.weight e)
    (ids : ∀ a b : Fin G.n,
      s.nm (rowOffsets + G.n + G.n * a.val + b.val) =
        ((table a b).map (fun step => step.1.val)).getD G.q)
    (diagonal : ∀ u : Fin G.n, s.rm (distances + G.n * u.val + u.val) = 0)
    (edgeUpper : ∀ step : Traversal G, (G.directed step.1 = false ∨ step.2 = true) →
      s.rm (distances + G.n * (start G step).val + (finish G step).val) ≤ G.weight step.1)
    (lower : ∀ u v : Fin G.n, distance G u v ≤ s.rm (distances + G.n * u.val + v.val))
    (entry : s.pc = 0) (running : s.halted = false) :
    let nextBase := rowOffsets + G.n + G.n * G.n + G.n + G.n
    ∃ t, BlockRuns apspAndTightPathsBlock
        (49 * G.n ^ 3 + 17 * G.n ^ 2 + 21 * G.n + 15) s t ∧
      t.halted = false ∧ FloydFrame G.n rowOffsets distances t ∧ t.nr 26 = nextBase ∧
      (∀ a < rowOffsets + G.n + G.n * G.n, t.nm a = s.nm a) ∧
      (∀ u v : Fin G.n, t.rm (distances + G.n * u.val + v.val) = distance G u v) ∧
      (∀ e : Fin G.q, t.rm e.val = G.weight e) ∧
      ∀ target, TightStoredRow target table nextBase t.nm := by
  obtain ⟨d, floyd, dRunning, dFixed, dNat, shortest⟩ := floydWarshallBlock_distances
    connected nonnegative frame entry running diagonal edgeUpper lower
  let dEntry := {d with pc := 0}
  have dFrame : FloydFrame G.n rowOffsets distances dEntry :=
    frame.preserved (fun r hlo hhi => dFixed r hlo hhi) dNat
  have dWeights (e : Fin G.q) : d.rm e.val = G.weight e :=
    (floydWarshallBlock_preserves_input frame entry running floyd (e.isLt.trans_le weightsBelow)).trans
      (weights e)
  have dCount : dEntry.nm 1 = G.q := (congrFun dNat 1).trans count
  obtain ⟨allocated, allocation, aRunning, aFrame, aNat, aReal, aCount, aIds, aRank, aQueue, aNext⟩ :=
    apspQueueLayoutBlock_correct dFrame connected.1 dCount rfl dRunning
  let allocatedExit := relocateState floydWarshallBlock.length allocated
  have prep := floyd.append allocation
  let queueEntry := {allocatedExit with pc := 0}
  have queueFrame : FloydFrame G.n rowOffsets distances queueEntry :=
    aFrame.preserved (fun _ _ _ => rfl) rfl
  have exactDistances (u v : Fin G.n) :
      queueEntry.rm (distances + G.n * u.val + v.val) = distance G u v := by
    change allocated.rm _ = _
    rw [aReal]
    exact shortest u v
  have sourceWeights (e : Fin G.q) : queueEntry.rm e.val = G.weight e := by
    change allocated.rm _ = _
    rw [aReal]
    exact dWeights e
  have exactIds (u v : Fin G.n) :
      queueEntry.nm (queueEntry.nr 11 + G.n * u.val + v.val) =
        ((table u v).map (fun step => step.1.val)).getD G.q := by
    change allocated.nm (allocated.nr 11 + _ + _) = _
    rw [aIds, aNat]
    change d.nm _ = _
    rw [dNat]
    exact ids u v
  have setup : TightAllTargetsFrame rowOffsets distances table (tightQueuePreparedState queueEntry) := by
    refine TightAllTargetsFrame.ofMatrices queueFrame aCount ?_ ?_ ?_ ?_ exactIds sourceWeights exactDistances
    · change rowOffsets + G.n ≤ allocated.nr 19
      rw [aRank]
      omega
    · change allocated.nr 11 + G.n * G.n ≤ allocated.nr 19
      rw [aIds, aRank]
    · change allocated.nr 19 + G.n ≤ allocated.nr 20
      rw [aRank, aQueue]
    · change allocated.nr 20 + G.n ≤ allocated.nr 26
      rw [aQueue, aNext]
  obtain ⟨t, searches, ready, real, next, natural, allRows⟩ := tightQueueAllBlock_rows
    connected nonnegative sound representative setup queueFrame.dimension queueFrame.one rfl aRunning
  have fixed := tightQueueAllBlock_fixedFloydRegisters searches rfl aRunning queueFrame.one queueFrame.dimension
  have finalFrame : FloydFrame G.n rowOffsets distances t := by
    refine ⟨(fixed 3 (by decide) (by decide)).trans queueFrame.tableBase,
      (fixed 4 (by decide) (by decide)).trans queueFrame.matrixBase,
      (fixed 5 (by decide) (by decide)).trans queueFrame.dimension,
      (fixed 6 (by decide) (by decide)).trans queueFrame.one, ?_⟩
    intro i hi
    have below : rowOffsets + i < queueEntry.nr 19 := by
      change rowOffsets + i < allocated.nr 19
      rw [aRank]
      omega
    exact (natural _ below).trans (queueFrame.rows i hi)
  have steps : (18 * G.n ^ 3 + 5 * G.n ^ 2 + 5 * G.n + 2 + 9) +
        (31 * G.n ^ 3 + 12 * G.n ^ 2 + 16 * G.n + 4) =
      49 * G.n ^ 3 + 17 * G.n ^ 2 + 21 * G.n + 15 := by ring
  have executes := prep.append searches
  rw [steps] at executes
  have relocatedFrame : FloydFrame G.n rowOffsets distances
      (relocateState (appendBlock floydWarshallBlock apspQueueLayoutBlock).length t) :=
    finalFrame.preserved (fun _ _ _ => rfl) rfl
  refine ⟨_, executes, ready, relocatedFrame, next.trans aNext, ?_, ?_, ?_, ?_⟩
  · intro a below
    have low : a < queueEntry.nr 19 := by
      change a < allocated.nr 19
      rwa [aRank]
    change t.nm a = s.nm a
    rw [natural a low]
    change allocated.nm a = s.nm a
    rw [aNat]
    exact congrFun dNat a
  · intro u v
    change t.rm _ = _
    rw [real]
    exact exactDistances u v
  · intro e
    change t.rm _ = _
    rw [real]
    exact sourceWeights e
  · intro target
    change TightStoredRow target table (rowOffsets + G.n + G.n * G.n + G.n + G.n) t.nm
    have base : queueEntry.nr 26 = rowOffsets + G.n + G.n * G.n + G.n + G.n := aNext
    simpa only [base] using allRows target

end VehicleRoutingSurvey.Routing
end RppSource_APSPPaths

/-! runtime/LinkScan.lean -/
section RppSource_LinkScan
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- Read one input link and compute both row-major addresses for the real weight
and natural edge-ID matrices. The natural-register cursor advances by three.
Registers 7–10 contain the link index, link count, input cursor, and ID-matrix base. -/
def readLinkBlock : List ArithmeticInstruction :=
  [.natLoad 11 9, .natAdd 9 9 6, .natLoad 12 9, .natAdd 9 9 6,
    .natLoad 13 9, .natAdd 9 9 6, .realLoad 1 7,
    .natAdd 15 3 11, .natLoad 15 15, .natAdd 17 15 12,
    .natAdd 19 4 17, .natAdd 21 10 17,
    .natAdd 16 3 12, .natLoad 16 16, .natAdd 18 16 11,
    .natAdd 20 4 18, .natAdd 22 10 18]

private def readLinkState (s : ArithmeticState) : ArithmeticState :=
  let input := s.nr 9
  let one := s.nr 6
  let u := s.nm input
  let v := s.nm (input + one)
  let required := s.nm (input + one + one)
  let rowU := s.nm (s.nr 3 + u)
  let rowV := s.nm (s.nr 3 + v)
  let uv := rowU + v
  let vu := rowV + u
  let nr := Function.update s.nr 11 u
  let nr := Function.update nr 9 (input + one)
  let nr := Function.update nr 12 v
  let nr := Function.update nr 9 (input + one + one)
  let nr := Function.update nr 13 required
  let nr := Function.update nr 9 (input + one + one + one)
  let nr := Function.update nr 15 rowU
  let nr := Function.update nr 17 uv
  let nr := Function.update nr 19 (s.nr 4 + uv)
  let nr := Function.update nr 21 (s.nr 10 + uv)
  let nr := Function.update nr 16 rowV
  let nr := Function.update nr 18 vu
  let nr := Function.update nr 20 (s.nr 4 + vu)
  let nr := Function.update nr 22 (s.nr 10 + vu)
  {s with pc := 17, rr := Function.update s.rr 1 (s.rm (s.nr 7)), nr}

private theorem readLinkState_run {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) : BlockRuns readLinkBlock 17 s (readLinkState s) := by
  refine ⟨?_, ?_, rfl⟩
  · intro i hi
    have counter (j : ℕ) (within : j ≤ 17) :
        ((arithmeticStep readLinkBlock)^[j] s).pc = j ∧
          ((arithmeticStep readLinkBlock)^[j] s).halted = false := by
      induction j with
      | zero => exact ⟨entry, running⟩
      | succ j ih =>
        have below : j < 17 := by omega
        have previous := ih (by omega)
        rw [Function.iterate_succ_apply']
        simp only [arithmeticStep, previous.1, previous.2, Bool.false_eq_true, ↓reduceIte]
        interval_cases j <;> exact ⟨rfl, rfl⟩
    change ((arithmeticStep readLinkBlock)^[i] s).pc < 17
    rwa [(counter i (by omega)).1]
  · simp [readLinkState, readLinkBlock, arithmeticStep, entry, running,
      Function.iterate_succ_apply', Function.update_idem]

private def edgeRelaxBlock (weightAddress idAddress : ℕ) : List ArithmeticInstruction :=
  [.realLoad 2 weightAddress, .realBranch 2 1 2 4, .jump 3, .jump 6,
    .realStore weightAddress 1, .natStore idAddress 7]

private noncomputable def relaxLinkMemory
    (weightAddress idAddress e : ℕ) (w : ℝ)
    (memory : (ℕ → ℝ) × (ℕ → ℕ)) : (ℕ → ℝ) × (ℕ → ℕ) :=
  if memory.1 weightAddress ≤ w then memory
  else (Function.update memory.1 weightAddress w, Function.update memory.2 idAddress e)

private theorem edgeRelaxBlock_runs (weightAddress idAddress : ℕ) {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    let t := (arithmeticStep (edgeRelaxBlock weightAddress idAddress))^[4] s
    BlockRuns (edgeRelaxBlock weightAddress idAddress) 4 s t ∧
      t.halted = false ∧ t.nr = s.nr ∧ t.rr 1 = s.rr 1 ∧
      (t.rm, t.nm) = relaxLinkMemory (s.nr weightAddress) (s.nr idAddress) (s.nr 7)
        (s.rr 1) (s.rm, s.nm) := by
  by_cases keep : s.rm (s.nr weightAddress) ≤ s.rr 1
  all_goals
    refine ⟨⟨?_, rfl, ?_⟩, ?_⟩
    · intro j hj
      have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl <;>
        simp [edgeRelaxBlock, arithmeticStep, entry, running, Function.iterate_succ_apply', keep]
    · simp [edgeRelaxBlock, arithmeticStep, entry, running, Function.iterate_succ_apply', keep]
    · simp [relaxLinkMemory, edgeRelaxBlock, arithmeticStep, entry, running,
        Function.iterate_succ_apply', keep]

private theorem flatMap_triple_getElem? {α β : Type*} (xs : List α) (record : α → List β)
    (length : ∀ a, (record a).length = 3) {i j : ℕ} (index : i < xs.length)
    (slot : j < 3) :
    (xs.flatMap record)[3 * i + j]? = (record xs[i])[j]? := by
  induction xs generalizing i with
  | nil => simp at index
  | cons x rest ih =>
    cases i with
    | zero =>
      rw [List.flatMap_cons, List.getElem?_append_left (by simpa [length] using slot)]
      simp
    | succ i =>
      rw [List.flatMap_cons, List.getElem?_append_right (by rw [length]; omega), length]
      rw [show 3 * (i + 1) + j - 3 = 3 * i + j by omega]
      exact ih (by simpa using index)

theorem ruralNatInput_link_record (I : Service) (e : Fin I.graph.q) {j : ℕ} (slot : j < 3) :
    (ruralNatInput I)[2 + 3 * e.val + j]? =
      [(I.graph.tail e).val, (I.graph.head e).val, if e ∈ I.links then 1 else 0][j]? := by
  have index : e.val < (List.finRange I.graph.q).length := by simpa using e.isLt
  change ([I.graph.n, I.graph.q] ++ (List.finRange I.graph.q).flatMap _)[2 + 3 * e.val + j]? = _
  rw [List.getElem?_append_right (by simp <;> omega)]
  simp only [List.length_cons, List.length_nil]
  rw [show 2 + 3 * e.val + j - 2 = 3 * e.val + j by omega]
  simpa using flatMap_triple_getElem? (List.finRange I.graph.q)
    (fun f => [(I.graph.tail f).val, (I.graph.head f).val, if f ∈ I.links then 1 else 0])
    (fun _ => rfl) index slot

theorem ruralRealInput_link_weight (I : Service) (e : Fin I.graph.q) :
    (ruralRealInput I)[e.val]? = some (I.graph.weight e) := by
  have index : e.val < (List.finRange I.graph.q).length := by simpa using e.isLt
  simp [ruralRealInput, List.getElem?_eq_getElem index]

/-- The scan uses separate matrices for real weights and natural edge IDs.
The layout inequalities keep both the input records and row offsets intact. -/
structure LinkScanFrame (I : Service) (table matrix ids : ℕ) (s : ArithmeticState) : Prop where
  floyd : FloydFrame I.graph.n table matrix s
  linkCount : s.nr 8 = I.graph.q
  idBase : s.nr 10 = ids
  naturalInput : ∀ j < 2 + 3 * I.graph.q,
    s.nm j = (ruralNatInput I)[j]?.getD 0
  realInput : ∀ e : Fin I.graph.q, s.rm e.val = I.graph.weight e
  idsAfterInput : 2 + 3 * I.graph.q ≤ ids
  idsAfterRows : table + I.graph.n ≤ ids
  matrixAfterWeights : I.graph.q ≤ matrix

def linkStepBlock : List ArithmeticInstruction :=
  appendBlock readLinkBlock (appendBlock (edgeRelaxBlock 19 21) (edgeRelaxBlock 20 22))

/-- Update the cells in both orientations and retain the earlier edge on a tie. -/
noncomputable def linkStepMemory (I : Service) (matrix ids : ℕ) (e : Fin I.graph.q)
    (memory : (ℕ → ℝ) × (ℕ → ℕ)) : (ℕ → ℝ) × (ℕ → ℕ) :=
  let uv := I.graph.n * (I.graph.tail e).val + (I.graph.head e).val
  let vu := I.graph.n * (I.graph.head e).val + (I.graph.tail e).val
  relaxLinkMemory (matrix + vu) (ids + vu) e.val (I.graph.weight e)
    (relaxLinkMemory (matrix + uv) (ids + uv) e.val (I.graph.weight e) memory)

structure LinkStepResult (I : Service) (matrix ids : ℕ) (e : Fin I.graph.q)
    (s t : ArithmeticState) : Prop where
  run : BlockRuns linkStepBlock 25 s t
  running : t.halted = false
  fixed : ∀ r < 9, t.nr r = s.nr r
  cursor : t.nr 9 = 2 + 3 * (e.val + 1)
  idBase : t.nr 10 = ids
  required : t.nr 13 = if e ∈ I.links then 1 else 0
  memory : (t.rm, t.nm) = linkStepMemory I matrix ids e (s.rm, s.nm)

theorem linkStepBlock_correct {I : Service} {table matrix ids : ℕ}
    (e : Fin I.graph.q) {s : ArithmeticState} (frame : LinkScanFrame I table matrix ids s)
    (entry : s.pc = 0) (running : s.halted = false)
    (index : s.nr 7 = e.val) (cursor : s.nr 9 = 2 + 3 * e.val) :
    ∃ t, LinkStepResult I matrix ids e s t := by
  let read := readLinkState s
  let first := {read with pc := 0}
  let mid := (arithmeticStep (edgeRelaxBlock 19 21))^[4] first
  let second := {mid with pc := 0}
  let last := (arithmeticStep (edgeRelaxBlock 20 22))^[4] second
  let t := relocateState 17 (relocateState 6 last)
  have readRun : BlockRuns readLinkBlock 17 s read := readLinkState_run entry running
  have firstRunning : first.halted = false := running
  obtain ⟨firstRun, midRunning, firstRegisters, firstWeight, firstMemory⟩ :=
    edgeRelaxBlock_runs 19 21 (s := first) rfl firstRunning
  obtain ⟨secondRun, lastRunning, secondRegisters, _, secondMemory⟩ :=
    edgeRelaxBlock_runs 20 22 (s := second) rfl midRunning
  have run : BlockRuns linkStepBlock 25 s t := readRun.append (firstRun.append secondRun)
  have registers : t.nr = read.nr := secondRegisters.trans firstRegisters
  have inputCell (j : ℕ) (inRecord : j < 3) :
      s.nm (2 + 3 * e.val + j) =
        ([(I.graph.tail e).val, (I.graph.head e).val, if e ∈ I.links then 1 else 0][j]?).getD 0 := by
    have edgeBound := e.isLt
    rw [frame.naturalInput _ (by omega), ruralNatInput_link_record I e inRecord]
  have tail : s.nm (s.nr 9) = (I.graph.tail e).val := by
    simpa [cursor] using inputCell 0 (by decide)
  have head : s.nm (s.nr 9 + 1) = (I.graph.head e).val := by
    simpa [cursor] using inputCell 1 (by decide)
  have flag : s.nm (s.nr 9 + 1 + 1) = if e ∈ I.links then 1 else 0 := by
    simpa [cursor, Nat.add_assoc] using inputCell 2 (by decide)
  have preserved (r : ℕ) (below : r < 9) : read.nr r = s.nr r := by
    simp [read, readLinkState, Function.update_of_ne (show r ≠ 9 by omega),
      Function.update_of_ne (show r ≠ 11 by omega), Function.update_of_ne (show r ≠ 12 by omega),
      Function.update_of_ne (show r ≠ 13 by omega), Function.update_of_ne (show r ≠ 15 by omega),
      Function.update_of_ne (show r ≠ 16 by omega), Function.update_of_ne (show r ≠ 17 by omega),
      Function.update_of_ne (show r ≠ 18 by omega), Function.update_of_ne (show r ≠ 19 by omega),
      Function.update_of_ne (show r ≠ 20 by omega), Function.update_of_ne (show r ≠ 21 by omega),
      Function.update_of_ne (show r ≠ 22 by omega)]
  have seed : read.rr 1 = I.graph.weight e := by
    simp [read, readLinkState, index, frame.realInput e]
  have rowsU := frame.floyd.rows _ (I.graph.tail e).isLt
  have rowsV := frame.floyd.rows _ (I.graph.head e).isLt
  have forwardReal : read.nr 19 = matrix + (I.graph.n * (I.graph.tail e).val + (I.graph.head e).val) := by
    simp [read, readLinkState, tail, head, frame.floyd.one, frame.floyd.tableBase,
      frame.floyd.matrixBase, rowsU]
  have forwardId : read.nr 21 = ids + (I.graph.n * (I.graph.tail e).val + (I.graph.head e).val) := by
    simp [read, readLinkState, tail, head, frame.floyd.one, frame.floyd.tableBase,
      frame.idBase, rowsU]
  have reverseReal : read.nr 20 = matrix + (I.graph.n * (I.graph.head e).val + (I.graph.tail e).val) := by
    simp [read, readLinkState, tail, head, frame.floyd.one, frame.floyd.tableBase,
      frame.floyd.matrixBase, rowsV]
  have reverseId : read.nr 22 = ids + (I.graph.n * (I.graph.head e).val + (I.graph.tail e).val) := by
    simp [read, readLinkState, tail, head, frame.floyd.one, frame.floyd.tableBase,
      frame.idBase, rowsV]
  refine ⟨t, run, lastRunning, fun r below => by rw [registers, preserved r below], ?_, ?_, ?_, ?_⟩
  · rw [registers]
    simp [read, readLinkState, cursor, frame.floyd.one] <;> omega
  · simpa [registers, read, readLinkState] using frame.idBase
  · rw [registers]
    simpa [read, readLinkState, frame.floyd.one] using flag
  · change (last.rm, last.nm) = _
    change (last.rm, last.nm) =
      relaxLinkMemory (mid.nr 20) (mid.nr 22) (mid.nr 7) (mid.rr 1) (mid.rm, mid.nm) at secondMemory
    change mid.nr = read.nr at firstRegisters
    change mid.rr 1 = read.rr 1 at firstWeight
    change (mid.rm, mid.nm) =
      relaxLinkMemory (read.nr 19) (read.nr 21) (read.nr 7) (read.rr 1) (s.rm, s.nm) at firstMemory
    rw [secondMemory, firstRegisters, firstWeight, firstMemory, forwardReal, forwardId, reverseReal,
      reverseId, preserved 7 (by decide), index, seed, linkStepMemory]

private theorem relaxLinkMemory_real_other {a b e j : ℕ} {w : ℝ}
    {memory : (ℕ → ℝ) × (ℕ → ℕ)} (different : j ≠ a) :
    (relaxLinkMemory a b e w memory).1 j = memory.1 j := by
  unfold relaxLinkMemory
  split <;> simp [Function.update_of_ne different]

private theorem relaxLinkMemory_nat_other {a b e j : ℕ} {w : ℝ}
    {memory : (ℕ → ℝ) × (ℕ → ℕ)} (different : j ≠ b) :
    (relaxLinkMemory a b e w memory).2 j = memory.2 j := by
  unfold relaxLinkMemory
  split <;> simp [Function.update_of_ne different]

theorem linkStepMemory_preserves_weights {I : Service} {matrix ids j : ℕ}
    (e : Fin I.graph.q) (memory : (ℕ → ℝ) × (ℕ → ℕ)) (before : j < matrix) :
    (linkStepMemory I matrix ids e memory).1 j = memory.1 j := by
  unfold linkStepMemory
  rw [relaxLinkMemory_real_other (by omega), relaxLinkMemory_real_other (by omega)]

theorem linkStepMemory_preserves_input {I : Service} {matrix ids j : ℕ}
    (e : Fin I.graph.q) (memory : (ℕ → ℝ) × (ℕ → ℕ)) (before : j < ids) :
    (linkStepMemory I matrix ids e memory).2 j = memory.2 j := by
  unfold linkStepMemory
  rw [relaxLinkMemory_nat_other (by omega), relaxLinkMemory_nat_other (by omega)]

noncomputable def linkScanMemory (I : Service) (matrix ids count : ℕ)
    (memory : (ℕ → ℝ) × (ℕ → ℕ)) : (ℕ → ℝ) × (ℕ → ℕ) :=
  ((List.finRange I.graph.q).take count).foldl
    (fun m e => linkStepMemory I matrix ids e m) memory

private theorem linkScanMemory_succ (I : Service) (matrix ids k : ℕ)
    (bound : k < I.graph.q) (memory : (ℕ → ℝ) × (ℕ → ℕ)) :
    linkScanMemory I matrix ids (k + 1) memory =
      linkStepMemory I matrix ids ⟨k, bound⟩ (linkScanMemory I matrix ids k memory) := by
  have atIndex : k < (List.finRange I.graph.q).length := by simpa using bound
  simp [linkScanMemory, List.take_succ_eq_append_getElem atIndex, List.foldl_append]

def linkScanBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 7 8 linkStepBlock

private structure LinkScanInvariant (I : Service) (table matrix ids : ℕ)
    (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 7 = i
  cursor : s.nr 9 = 2 + 3 * i
  frame : LinkScanFrame I table matrix ids s
  memory : (s.rm, s.nm) = linkScanMemory I matrix ids i (initial.rm, initial.nm)

/-- Scan the exact rural input, retaining the least direct weight and its edge ID
according to the fold. The block leaves the input records and row table intact. -/
theorem linkScanBlock_correct {I : Service} {table matrix ids : ℕ} {s : ArithmeticState}
    (frame : LinkScanFrame I table matrix ids s) (entry : s.pc = 0) (running : s.halted = false)
    (cursor : s.nr 9 = 2) :
    ∃ t, BlockRuns linkScanBlock (28 * I.graph.q + 2) s t ∧
      t.halted = false ∧ LinkScanFrame I table matrix ids t ∧
      (t.rm, t.nm) = linkScanMemory I matrix ids I.graph.q (s.rm, s.nm) := by
  let inv := LinkScanInvariant I table matrix ids s
  let first := {s with pc := 0, nr := Function.update s.nr 7 0}
  have firstFrame : LinkScanFrame I table matrix ids first := by
    refine ⟨⟨?_, ?_, ?_, ?_, frame.floyd.rows⟩, ?_, ?_, frame.naturalInput, frame.realInput,
      frame.idsAfterInput, frame.idsAfterRows, frame.matrixAfterWeights⟩
    all_goals
      simp [first, frame.floyd.tableBase, frame.floyd.matrixBase, frame.floyd.dimension,
        frame.floyd.one, frame.linkCount, frame.idBase]
  have initial : inv 0 first :=
    ⟨rfl, running, by simp [first], by simpa [first] using cursor, firstFrame,
      by simp [first, linkScanMemory]⟩
  have control (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 8 = I.graph.q :=
    ⟨hm.entry, hm.running, hm.index, hm.frame.linkCount⟩
  have iterate (i : ℕ) (bound : i < I.graph.q) (m : ArithmeticState) (hm : inv i m) :
      ∃ t, BlockRuns linkStepBlock 25 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 6)} := by
    let e : Fin I.graph.q := ⟨i, bound⟩
    obtain ⟨t, changed⟩ := linkStepBlock_correct e hm.frame hm.entry hm.running hm.index hm.cursor
    let next := {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 6)}
    have still (r : ℕ) (before : r < 9) (different : r ≠ 7) :
        next.nr r = m.nr r := by
      change Function.update t.nr 7 (t.nr 7 + t.nr 6) r = m.nr r
      rw [Function.update_of_ne different, changed.fixed _ before]
    have sameReal (j : ℕ) (before : j < matrix) : t.rm j = m.rm j := by
      rw [show t.rm j = (t.rm, t.nm).1 j by rfl, changed.memory]
      exact linkStepMemory_preserves_weights e _ before
    have sameNat (j : ℕ) (before : j < ids) : t.nm j = m.nm j := by
      rw [show t.nm j = (t.rm, t.nm).2 j by rfl, changed.memory]
      exact linkStepMemory_preserves_input e _ before
    have rows (j : ℕ) (hj : j < I.graph.n) : next.nm (table + j) = I.graph.n * j :=
      (sameNat _ (by have keep := hm.frame.idsAfterRows; omega)).trans (hm.frame.floyd.rows j hj)
    have natInput (j : ℕ) (hj : j < 2 + 3 * I.graph.q) :
        next.nm j = (ruralNatInput I)[j]?.getD 0 :=
      (sameNat _ (hj.trans_le hm.frame.idsAfterInput)).trans (hm.frame.naturalInput j hj)
    have realInput (f : Fin I.graph.q) : next.rm f.val = I.graph.weight f :=
      (sameReal _ (f.isLt.trans_le hm.frame.matrixAfterWeights)).trans (hm.frame.realInput f)
    have nextFrame : LinkScanFrame I table matrix ids next := by
      refine ⟨⟨(still 3 (by decide) (by decide)).trans hm.frame.floyd.tableBase,
        (still 4 (by decide) (by decide)).trans hm.frame.floyd.matrixBase,
        (still 5 (by decide) (by decide)).trans hm.frame.floyd.dimension,
        (still 6 (by decide) (by decide)).trans hm.frame.floyd.one, rows⟩,
        (still 8 (by decide) (by decide)).trans hm.frame.linkCount, ?_, natInput, realInput,
        hm.frame.idsAfterInput, hm.frame.idsAfterRows, hm.frame.matrixAfterWeights⟩
      simpa [next] using changed.idBase
    refine ⟨t, changed.run, changed.running, rfl, changed.running, ?_, ?_, nextFrame, ?_⟩
    · simp [next, changed.fixed 7 (by decide), changed.fixed 6 (by decide),
        hm.index, hm.frame.floyd.one]
    · simpa [next] using changed.cursor
    · change (t.rm, t.nm) = _
      rw [changed.memory, hm.memory, linkScanMemory_succ I matrix ids i bound]
  obtain ⟨last, complete, steps⟩ :=
    countedLoopFromZero_correct 6 7 8 I.graph.q 25 linkStepBlock inv entry running initial control iterate
  let finish := relocateState 1 {last with pc := (countedLoop 6 7 8 linkStepBlock).length}
  have finalFrame : LinkScanFrame I table matrix ids finish :=
    let f := complete.frame
    ⟨⟨f.floyd.tableBase, f.floyd.matrixBase, f.floyd.dimension, f.floyd.one, f.floyd.rows⟩,
      f.linkCount, f.idBase, f.naturalInput, f.realInput, f.idsAfterInput, f.idsAfterRows,
      f.matrixAfterWeights⟩
  refine ⟨finish, ?_, complete.running, finalFrame, complete.memory⟩
  have ticks : 1 + (I.graph.q * (25 + 3) + 1) = 28 * I.graph.q + 2 := by omega
  simpa only [linkScanBlock, ticks] using steps

private theorem relaxLinkMemory_real_formula (a b e j : ℕ) (w : ℝ)
    (memory : (ℕ → ℝ) × (ℕ → ℕ)) :
    (relaxLinkMemory a b e w memory).1 j =
      if j = a then min (memory.1 j) w else memory.1 j := by
  by_cases same : j = a
  · subst j
    by_cases keep : memory.1 a ≤ w
    · simp [relaxLinkMemory, keep, min_eq_left keep]
    · simp [relaxLinkMemory, keep, min_eq_right (le_of_not_ge keep)]
  · simp [same, relaxLinkMemory_real_other same]

private theorem matrixAddress_eq_iff {n : ℕ} (base : ℕ) (u v x y : Fin n) :
    base + (n * u.val + v.val) = base + (n * x.val + y.val) ↔ u = x ∧ v = y := by
  constructor
  · intro same
    obtain ⟨rows, columns⟩ :=
      (denseMatrixOffset_eq_iff v.isLt y.isLt).mp (Nat.add_left_cancel same)
    exact ⟨Fin.ext rows, Fin.ext columns⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private abbrev Joins {I : Service} (e : Fin I.graph.q) (u v : Fin I.graph.n) : Prop :=
  (u = I.graph.tail e ∧ v = I.graph.head e) ∨ (u = I.graph.head e ∧ v = I.graph.tail e)

private theorem linkStepMemory_real_formula {I : Service} (matrix ids : ℕ)
    (e : Fin I.graph.q) (u v : Fin I.graph.n) (memory : (ℕ → ℝ) × (ℕ → ℕ)) :
    let a := matrix + I.graph.n * u.val + v.val
    (linkStepMemory I matrix ids e memory).1 a =
      if Joins e u v then min (memory.1 a) (I.graph.weight e) else memory.1 a := by
  classical
  simp only [Nat.add_assoc, linkStepMemory, relaxLinkMemory_real_formula, matrixAddress_eq_iff]
  by_cases forward : u = I.graph.tail e ∧ v = I.graph.head e
  · by_cases reverse : u = I.graph.head e ∧ v = I.graph.tail e
    · rw [if_pos reverse, if_pos forward, if_pos (Or.inl forward)]
      simp [min_assoc]
    · rw [if_neg reverse, if_pos forward, if_pos (Or.inl forward)]
  · by_cases reverse : u = I.graph.head e ∧ v = I.graph.tail e
    · rw [if_pos reverse, if_neg forward, if_pos (Or.inr reverse)]
    · rw [if_neg reverse, if_neg forward, if_neg (not_or_intro forward reverse)]

private theorem distance_le_join_weight {I : Service} (rural : Rural I) (e : Fin I.graph.q)
    {u v : Fin I.graph.n} (joins : Joins e u v) : distance I.graph u v ≤ I.graph.weight e := by
  rcases joins with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have path : IsPath I.graph (I.graph.tail e) [(e, true)] (I.graph.head e) :=
      ⟨rfl, Or.inr rfl, rfl⟩
    simpa [pathCost] using distance_le_pathCost rural.2.1 path
  · have path : IsPath I.graph (I.graph.head e) [(e, false)] (I.graph.tail e) :=
      ⟨rfl, Or.inl (rural.2.2.1 e), rfl⟩
    simpa [pathCost] using distance_le_pathCost rural.2.1 path

private theorem linkFold_floyd_bounds {I : Service} (rural : Rural I) (matrix ids : ℕ)
    (links : List (Fin I.graph.q)) (memory : (ℕ → ℝ) × (ℕ → ℕ))
    (diagonal : ∀ u : Fin I.graph.n, memory.1 (matrix + I.graph.n * u.val + u.val) = 0)
    (lower : ∀ u v : Fin I.graph.n,
      distance I.graph u v ≤ memory.1 (matrix + I.graph.n * u.val + v.val)) :
    let final := links.foldl (fun m e => linkStepMemory I matrix ids e m) memory
    (∀ u : Fin I.graph.n, final.1 (matrix + I.graph.n * u.val + u.val) = 0) ∧
    (∀ u v : Fin I.graph.n, distance I.graph u v ≤ final.1 (matrix + I.graph.n * u.val + v.val)) ∧
    (∀ u v : Fin I.graph.n, final.1 (matrix + I.graph.n * u.val + v.val) ≤
      memory.1 (matrix + I.graph.n * u.val + v.val)) ∧
    (∀ e ∈ links, ∀ u v : Fin I.graph.n, Joins e u v →
      final.1 (matrix + I.graph.n * u.val + v.val) ≤ I.graph.weight e) := by
  classical
  induction links generalizing memory with
  | nil => exact ⟨diagonal, lower, fun _ _ => le_rfl, fun _ h => by simp at h⟩
  | cons e rest ih =>
    let next := linkStepMemory I matrix ids e memory
    have nextDiagonal (u : Fin I.graph.n) : next.1 (matrix + I.graph.n * u.val + u.val) = 0 := by
      dsimp only [next]
      rw [linkStepMemory_real_formula, diagonal]
      simp [min_eq_left (rural.2.1 e)]
    have nextLower (u v : Fin I.graph.n) :
        distance I.graph u v ≤ next.1 (matrix + I.graph.n * u.val + v.val) := by
      dsimp only [next]
      rw [linkStepMemory_real_formula]
      split
      · exact le_min (lower u v) (distance_le_join_weight rural e ‹Joins e u v›)
      · exact lower u v
    have decreases (u v : Fin I.graph.n) :
        next.1 (matrix + I.graph.n * u.val + v.val) ≤
          memory.1 (matrix + I.graph.n * u.val + v.val) := by
      dsimp only [next]
      rw [linkStepMemory_real_formula]
      split
      · exact min_le_left _ _
      · exact le_rfl
    obtain ⟨diag, dist, mono, direct⟩ := ih next nextDiagonal nextLower
    refine ⟨diag, dist, fun u v => (mono u v).trans (decreases u v), ?_⟩
    intro f member u v joins
    rcases List.mem_cons.mp member with rfl | later
    · apply (mono u v).trans
      dsimp only [next]
      rw [linkStepMemory_real_formula, if_pos joins]
      exact min_le_right _ _
    · exact direct f later u v joins

/-- A zero diagonal and lower-bounding initialization, such as the weight-sum
sentinel, become the three matrix conditions for the Floyd–Warshall proof. -/
theorem linkScanMemory_floyd_bounds {I : Service} (rural : Rural I) (matrix ids : ℕ)
    (memory : (ℕ → ℝ) × (ℕ → ℕ))
    (diagonal : ∀ u : Fin I.graph.n, memory.1 (matrix + I.graph.n * u.val + u.val) = 0)
    (lower : ∀ u v : Fin I.graph.n,
      distance I.graph u v ≤ memory.1 (matrix + I.graph.n * u.val + v.val)) :
    let final := (linkScanMemory I matrix ids I.graph.q memory).1
    (∀ u : Fin I.graph.n, final (matrix + I.graph.n * u.val + u.val) = 0) ∧
    (∀ t : Traversal I.graph, final (matrix + I.graph.n * (start I.graph t).val +
      (finish I.graph t).val) ≤ I.graph.weight t.1) ∧
    (∀ u v : Fin I.graph.n, distance I.graph u v ≤ final (matrix + I.graph.n * u.val + v.val)) := by
  obtain ⟨diag, dist, _, direct⟩ :=
    linkFold_floyd_bounds rural matrix ids (List.finRange I.graph.q) memory diagonal lower
  have whole : (List.finRange I.graph.q).take I.graph.q = List.finRange I.graph.q := by
    simpa only [List.length_finRange] using
      (show (List.finRange I.graph.q).take (List.finRange I.graph.q).length = List.finRange I.graph.q from
        List.take_length)
  simp only [linkScanMemory, whole]
  refine ⟨diag, fun t => direct t.1 (List.mem_finRange t.1) _ _ ?_, dist⟩
  cases direction : t.2 <;> simp [Joins, start, finish, direction]

private def fillAdjacencyCell : List ArithmeticInstruction :=
  [.natAdd 19 4 7, .natAdd 21 10 7, .realStore 19 0, .natStore 21 8]

private def zeroAdjacencyDiagonalCell : List ArithmeticInstruction :=
  [.natAdd 19 3 7, .natLoad 19 19, .natAdd 19 19 7, .natAdd 19 4 19,
    .realConst 2 0, .realStore 19 2]

/-- Initialize all direct distances to the sentinel in real register zero, all
edge IDs to the link count, and all diagonal distances to zero. Register 23
contains the number of matrix cells. -/
def initAdjacencyBlock : List ArithmeticInstruction :=
  appendBlock (countedLoopFromZero 6 7 23 fillAdjacencyCell)
    (countedLoopFromZero 6 7 5 zeroAdjacencyDiagonalCell)

private theorem fillAdjacencyCell_runs {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) :
    let weightCell := s.nr 4 + s.nr 7
    let idCell := s.nr 10 + s.nr 7
    BlockRuns fillAdjacencyCell 4 s
      {s with
        pc := 4
        nr := Function.update (Function.update s.nr 19 weightCell) 21 idCell
        nm := Function.update s.nm idCell (s.nr 8)
        rm := Function.update s.rm weightCell (s.rr 0)} := by
  refine ⟨?_, ?_, rfl⟩
  · intro j hj
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [fillAdjacencyCell, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [fillAdjacencyCell, arithmeticStep, entry, running, Function.iterate_succ_apply']

private theorem zeroAdjacencyDiagonalCell_runs {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) :
    let cell := s.nr 4 + (s.nm (s.nr 3 + s.nr 7) + s.nr 7)
    BlockRuns zeroAdjacencyDiagonalCell 6 s
      {s with
        pc := 6
        nr := Function.update s.nr 19 cell
        rr := Function.update s.rr 2 0
        rm := Function.update s.rm cell 0} := by
  refine ⟨?_, ?_, rfl⟩
  · intro j hj
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [zeroAdjacencyDiagonalCell, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [zeroAdjacencyDiagonalCell, arithmeticStep, entry, running,
      Function.iterate_succ_apply', Function.update_idem]

private abbrev InitRegistersFixed (s t : ArithmeticState) :=
  ∀ r, (r < 19 ∧ r ≠ 7) ∨ r = 23 → t.nr r = s.nr r

private theorem update_filled_interval {α : Type*} (original current : ℕ → α)
    (base i : ℕ) (value : α)
    (filled : ∀ k, current k = if base ≤ k ∧ k < base + i then value else original k) :
    ∀ k, Function.update current (base + i) value k =
      if base ≤ k ∧ k < base + (i + 1) then value else original k := by
  intro k
  by_cases last : k = base + i
  · subst k
    rw [Function.update_self, if_pos (by omega)]
  · have same : (base ≤ k ∧ k < base + (i + 1)) ↔ (base ≤ k ∧ k < base + i) := by omega
    rw [Function.update_of_ne last, filled]
    simp only [same]

private structure FillAdjacencyInvariant (initial : ArithmeticState) (i : ℕ)
    (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 7 = i
  fixed : InitRegistersFixed initial s
  sentinel : s.rr 0 = initial.rr 0
  weights : ∀ k, s.rm k =
    if initial.nr 4 ≤ k ∧ k < initial.nr 4 + i then initial.rr 0 else initial.rm k
  ids : ∀ k, s.nm k =
    if initial.nr 10 ≤ k ∧ k < initial.nr 10 + i then initial.nr 8 else initial.nm k

private theorem fillAdjacency_correct {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 6 = 1) (count : ℕ) (cells : s.nr 23 = count) :
    ∃ t, BlockRuns (countedLoopFromZero 6 7 23 fillAdjacencyCell) (7 * count + 2) s t ∧
      t.halted = false ∧ InitRegistersFixed s t ∧
      (∀ k, t.rm k = if s.nr 4 ≤ k ∧ k < s.nr 4 + count then s.rr 0 else s.rm k) ∧
      (∀ k, t.nm k = if s.nr 10 ≤ k ∧ k < s.nr 10 + count then s.nr 8 else s.nm k) := by
  let inv := FillAdjacencyInvariant s
  let start := {s with pc := 0, nr := Function.update s.nr 7 0}
  have initial : inv 0 start := by
    refine ⟨rfl, running, by simp [start], ?_, rfl, fun k => by simp [start], fun k => by simp [start]⟩
    intro r fixed
    simp [start, Function.update_of_ne (show r ≠ 7 by omega)]
  have control (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 23 = count :=
    ⟨hm.entry, hm.running, hm.index, (hm.fixed 23 (Or.inr rfl)).trans cells⟩
  have iterate (i : ℕ) (_ : i < count) (m : ArithmeticState) (hm : inv i m) :
      ∃ t, BlockRuns fillAdjacencyCell 4 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 6)} := by
    let weightCell := m.nr 4 + m.nr 7
    let idCell := m.nr 10 + m.nr 7
    let t := {m with
      pc := 4
      nr := Function.update (Function.update m.nr 19 weightCell) 21 idCell
      nm := Function.update m.nm idCell (m.nr 8)
      rm := Function.update m.rm weightCell (m.rr 0)}
    have run : BlockRuns fillAdjacencyCell 4 m t := fillAdjacencyCell_runs hm.entry hm.running
    have keeps (r : ℕ) (fixed : (r < 19 ∧ r ≠ 7) ∨ r = 23) : t.nr r = s.nr r := by
      simp [t, Function.update_of_ne (show r ≠ 19 by omega),
        Function.update_of_ne (show r ≠ 21 by omega), hm.fixed r fixed]
    refine ⟨t, run, hm.running, rfl, hm.running, ?_, ?_, hm.sentinel, ?_, ?_⟩
    · change Function.update t.nr 7 (t.nr 7 + t.nr 6) 7 = i + 1
      rw [Function.update_self, keeps 6 (by decide), one]
      simp [t, hm.index]
    · intro r fixed
      change Function.update t.nr 7 (t.nr 7 + t.nr 6) r = s.nr r
      rw [Function.update_of_ne (show r ≠ 7 by omega)]
      exact keeps r fixed
    · simpa [t, weightCell, hm.fixed 4 (by decide), hm.index, hm.sentinel] using
        update_filled_interval s.rm m.rm (s.nr 4) i (s.rr 0) hm.weights
    · simpa [t, idCell, hm.fixed 10 (by decide), hm.index, hm.fixed 8 (by decide)] using
        update_filled_interval s.nm m.nm (s.nr 10) i (s.nr 8) hm.ids
  obtain ⟨last, complete, steps⟩ :=
    countedLoopFromZero_correct 6 7 23 count 4 fillAdjacencyCell inv entry running initial control iterate
  let finish := relocateState 1 {last with pc := (countedLoop 6 7 23 fillAdjacencyCell).length}
  have ticks : 1 + (count * (4 + 3) + 1) = 7 * count + 2 := by omega
  exact ⟨finish, by simpa only [ticks] using steps, complete.running, complete.fixed,
    complete.weights, complete.ids⟩

private def diagonalAddresses (n matrix count : ℕ) : List ℕ :=
  (List.range count).map (fun i => matrix + (n * i + i))

private structure ZeroAdjacencyInvariant (n matrix : ℕ) (initial : ArithmeticState)
    (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 7 = i
  fixed : InitRegistersFixed initial s
  natural : s.nm = initial.nm
  weights : ∀ k, s.rm k = if k ∈ diagonalAddresses n matrix i then 0 else initial.rm k

private theorem zeroAdjacency_correct {n table matrix : ℕ} {s : ArithmeticState}
    (frame : FloydFrame n table matrix s) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns (countedLoopFromZero 6 7 5 zeroAdjacencyDiagonalCell) (9 * n + 2) s t ∧
      t.halted = false ∧ InitRegistersFixed s t ∧ t.nm = s.nm ∧
      ∀ k, t.rm k = if k ∈ diagonalAddresses n matrix n then 0 else s.rm k := by
  let inv := ZeroAdjacencyInvariant n matrix s
  let start := {s with pc := 0, nr := Function.update s.nr 7 0}
  have initial : inv 0 start := by
    refine ⟨rfl, running, by simp [start], ?_, rfl, fun k => by simp [start, diagonalAddresses]⟩
    intro r fixed
    simp [start, Function.update_of_ne (show r ≠ 7 by omega)]
  have control (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 5 = n :=
    ⟨hm.entry, hm.running, hm.index, (hm.fixed 5 (by decide)).trans frame.dimension⟩
  have iterate (i : ℕ) (bound : i < n) (m : ArithmeticState) (hm : inv i m) :
      ∃ t, BlockRuns zeroAdjacencyDiagonalCell 6 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 6)} := by
    let cell := m.nr 4 + (m.nm (m.nr 3 + m.nr 7) + m.nr 7)
    let t := {m with
      pc := 6
      nr := Function.update m.nr 19 cell
      rr := Function.update m.rr 2 0
      rm := Function.update m.rm cell 0}
    have run : BlockRuns zeroAdjacencyDiagonalCell 6 m t := zeroAdjacencyDiagonalCell_runs hm.entry hm.running
    have address : cell = matrix + (n * i + i) := by
      simp [cell, hm.fixed 4 (by decide), hm.fixed 3 (by decide), frame.matrixBase,
        frame.tableBase, hm.index, hm.natural, frame.rows i bound]
    have keeps (r : ℕ) (fixed : (r < 19 ∧ r ≠ 7) ∨ r = 23) : t.nr r = s.nr r := by
      simp [t, Function.update_of_ne (show r ≠ 19 by omega), hm.fixed r fixed]
    refine ⟨t, run, hm.running, rfl, hm.running, ?_, ?_, hm.natural, ?_⟩
    · change Function.update t.nr 7 (t.nr 7 + t.nr 6) 7 = i + 1
      rw [Function.update_self, keeps 6 (by decide), frame.one]
      simp [t, hm.index]
    · intro r fixed
      change Function.update t.nr 7 (t.nr 7 + t.nr 6) r = s.nr r
      rw [Function.update_of_ne (show r ≠ 7 by omega)]
      exact keeps r fixed
    · intro k
      change Function.update m.rm cell 0 k =
        if k ∈ diagonalAddresses n matrix (i + 1) then 0 else s.rm k
      rw [address]
      by_cases last : k = matrix + (n * i + i)
      · subst k
        simp [diagonalAddresses, List.range_succ]
      · rw [Function.update_of_ne last, hm.weights]
        simp [diagonalAddresses, List.range_succ, last]
  obtain ⟨last, complete, steps⟩ :=
    countedLoopFromZero_correct 6 7 5 n 6 zeroAdjacencyDiagonalCell inv entry running initial control iterate
  let finish := relocateState 1 {last with pc := (countedLoop 6 7 5 zeroAdjacencyDiagonalCell).length}
  have ticks : 1 + (n * (6 + 3) + 1) = 9 * n + 2 := by omega
  exact ⟨finish, by simpa only [ticks] using steps, complete.running, complete.fixed,
    complete.natural, complete.weights⟩

private theorem denseCell_lt_count {n : ℕ} (u v : Fin n) :
    n * u.val + v.val < n ^ 2 := by
  rw [pow_two]
  calc
    _ < n * (u.val + 1) := by
      rw [Nat.mul_succ]
      exact Nat.add_lt_add_left v.isLt _
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt u.isLt)

private theorem mem_diagonalAddresses_iff {n : ℕ} (matrix : ℕ) (u v : Fin n) :
    matrix + n * u.val + v.val ∈ diagonalAddresses n matrix n ↔ u = v := by
  simp only [Nat.add_assoc, diagonalAddresses, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, bounded, address⟩
    let w : Fin n := ⟨i, bounded⟩
    have ends := (matrixAddress_eq_iff matrix w w u v).mp address
    exact ends.1.symm.trans ends.2
  · rintro rfl
    exact ⟨u.val, u.isLt, rfl⟩

/-- Fill the dense adjacency matrices and clear the real diagonal in
7 * n^2 + 9 * n + 4 instructions. The input and row table remain available. -/
theorem initAdjacencyBlock_correct {I : Service} {table matrix ids : ℕ} {s : ArithmeticState}
    (frame : LinkScanFrame I table matrix ids s) (entry : s.pc = 0) (running : s.halted = false)
    (cells : s.nr 23 = I.graph.n ^ 2) :
    ∃ t, BlockRuns initAdjacencyBlock (7 * I.graph.n ^ 2 + 9 * I.graph.n + 4) s t ∧
      t.halted = false ∧ LinkScanFrame I table matrix ids t ∧ t.nr 9 = s.nr 9 ∧
      (∀ u v : Fin I.graph.n, t.rm (matrix + I.graph.n * u.val + v.val) =
        if u = v then 0 else s.rr 0) ∧
      (∀ u v : Fin I.graph.n, t.nm (ids + I.graph.n * u.val + v.val) = I.graph.q) := by
  obtain ⟨filled, fillRun, fillReady, fillFixed, fillWeights, fillIds⟩ :=
    fillAdjacency_correct entry running frame.floyd.one _ cells
  have keepsNat (k : ℕ) (below : k < ids) : filled.nm k = s.nm k := by
    rw [fillIds, frame.idBase, if_neg (fun h => (not_le.mpr below) h.1)]
  have fillFrame : FloydFrame I.graph.n table matrix {filled with pc := 0} :=
    ⟨(fillFixed 3 (by decide)).trans frame.floyd.tableBase,
      (fillFixed 4 (by decide)).trans frame.floyd.matrixBase,
      (fillFixed 5 (by decide)).trans frame.floyd.dimension,
      (fillFixed 6 (by decide)).trans frame.floyd.one,
      fun i bound => (keepsNat _ (by have afterRows := frame.idsAfterRows; omega)).trans
        (frame.floyd.rows i bound)⟩
  obtain ⟨cleared, clearRun, clearReady, clearFixed, clearNat, clearWeights⟩ :=
    zeroAdjacency_correct fillFrame rfl fillReady
  let finish := relocateState (countedLoopFromZero 6 7 23 fillAdjacencyCell).length cleared
  have executes := fillRun.append clearRun
  have fixed : InitRegistersFixed s finish :=
    fun r stable => (clearFixed r stable).trans (fillFixed r stable)
  have beforeMatrix (k : ℕ) (below : k < matrix) : finish.rm k = s.rm k := by
    change cleared.rm k = _
    have offDiagonal : k ∉ diagonalAddresses I.graph.n matrix I.graph.n := by
      simp only [diagonalAddresses, List.mem_map, List.mem_range]
      rintro ⟨i, _, equal⟩
      omega
    rw [clearWeights, if_neg offDiagonal, fillWeights, frame.floyd.matrixBase,
      if_neg (fun h => (not_le.mpr below) h.1)]
  have finalFrame : LinkScanFrame I table matrix ids finish :=
    ⟨⟨(fixed 3 (by decide)).trans frame.floyd.tableBase,
      (fixed 4 (by decide)).trans frame.floyd.matrixBase,
      (fixed 5 (by decide)).trans frame.floyd.dimension,
      (fixed 6 (by decide)).trans frame.floyd.one,
      fun i bound =>
        (congrFun clearNat (table + i)).trans (fillFrame.rows i bound)⟩,
      (fixed 8 (by decide)).trans frame.linkCount,
      (fixed 10 (by decide)).trans frame.idBase,
      fun k bound => (congrFun clearNat k).trans
        ((keepsNat k (bound.trans_le frame.idsAfterInput)).trans (frame.naturalInput k bound)),
      fun e => (beforeMatrix e.val (e.isLt.trans_le frame.matrixAfterWeights)).trans (frame.realInput e),
      frame.idsAfterInput, frame.idsAfterRows, frame.matrixAfterWeights⟩
  have ticks : (7 * I.graph.n ^ 2 + 2) + (9 * I.graph.n + 2) =
      7 * I.graph.n ^ 2 + 9 * I.graph.n + 4 := by omega
  refine ⟨finish, by simpa only [initAdjacencyBlock, ticks] using executes,
    clearReady, finalFrame, fixed 9 (by decide), ?_, ?_⟩
  · intro u v
    change cleared.rm _ = _
    rw [clearWeights]
    simp only [mem_diagonalAddresses_iff]
    by_cases diagonal : u = v
    · simp [diagonal]
    · simp only [diagonal, if_false]
      rw [fillWeights, frame.floyd.matrixBase, if_pos]
      have bounded := denseCell_lt_count u v
      omega
  · intro u v
    change cleared.nm _ = _
    rw [clearNat, fillIds, frame.idBase, frame.linkCount, if_pos]
    have bounded := denseCell_lt_count u v
    omega

abbrev UndirectedLinkJoins (G : Network) (e : Fin G.q) (u v : Fin G.n) : Prop :=
  (u = G.tail e ∧ v = G.head e) ∨ (u = G.head e ∧ v = G.tail e)

private def linkCell (memory : (ℕ → ℝ) × (ℕ → ℕ)) (realAddress idAddress : ℕ) : ℝ × ℕ :=
  (memory.1 realAddress, memory.2 idAddress)

private noncomputable def preferLink (w : ℝ) (e : ℕ) (old : ℝ × ℕ) : ℝ × ℕ :=
  if w < old.1 then (w, e) else old

private theorem preferLink_twice (w : ℝ) (e : ℕ) (old : ℝ × ℕ) :
    preferLink w e (preferLink w e old) = preferLink w e old := by
  by_cases cheaper : w < old.1 <;> simp [preferLink, cheaper]

private theorem relaxLinkMemory_cell {a b e r i : ℕ} {w : ℝ} {memory : (ℕ → ℝ) × (ℕ → ℕ)}
    (associated : r = a ↔ i = b) :
    linkCell (relaxLinkMemory a b e w memory) r i =
      if r = a then preferLink w e (linkCell memory r i) else linkCell memory r i := by
  by_cases same : r = a
  · have sameId := associated.mp same
    subst r
    subst i
    by_cases cheaper : w < memory.1 a
    · simp [relaxLinkMemory, preferLink, linkCell, cheaper, not_le.mpr cheaper]
    · simp [relaxLinkMemory, preferLink, linkCell, cheaper, le_of_not_gt cheaper]
  · have different := mt associated.mpr same
    simp [linkCell, same, relaxLinkMemory_real_other same, relaxLinkMemory_nat_other different]

private theorem linkStepMemory_cell {I : Service} (matrix ids : ℕ)
    (e : Fin I.graph.q) (u v : Fin I.graph.n) (memory : (ℕ → ℝ) × (ℕ → ℕ)) :
    let r := matrix + I.graph.n * u.val + v.val
    let i := ids + I.graph.n * u.val + v.val
    let old := linkCell memory r i
    linkCell (linkStepMemory I matrix ids e memory) r i =
      if UndirectedLinkJoins I.graph e u v ∧ I.graph.weight e < old.1
      then (I.graph.weight e, e.val) else old := by
  have alignedAt (a b : Fin I.graph.n) :
      matrix + (I.graph.n * u.val + v.val) = matrix + (I.graph.n * a.val + b.val) ↔
        ids + (I.graph.n * u.val + v.val) = ids + (I.graph.n * a.val + b.val) :=
    (matrixAddress_eq_iff matrix u v a b).trans (matrixAddress_eq_iff ids u v a b).symm
  simp only [Nat.add_assoc, linkStepMemory]
  rw [relaxLinkMemory_cell (alignedAt (I.graph.head e) (I.graph.tail e)),
    relaxLinkMemory_cell (alignedAt (I.graph.tail e) (I.graph.head e))]
  simp only [matrixAddress_eq_iff]
  by_cases forward : u = I.graph.tail e ∧ v = I.graph.head e
  · have joins : UndirectedLinkJoins I.graph e u v := Or.inl forward
    by_cases reverse : u = I.graph.head e ∧ v = I.graph.tail e
    · rw [if_pos reverse, if_pos forward, preferLink_twice]
      simp only [joins, true_and, preferLink]
    · rw [if_neg reverse, if_pos forward]
      simp only [joins, true_and, preferLink]
  · by_cases reverse : u = I.graph.head e ∧ v = I.graph.tail e
    · have joins : UndirectedLinkJoins I.graph e u v := Or.inr reverse
      rw [if_pos reverse, if_neg forward]
      simp only [joins, true_and, preferLink]
    · have missing : ¬UndirectedLinkJoins I.graph e u v := not_or_intro forward reverse
      rw [if_neg reverse, if_neg forward]
      simp only [missing, false_and, if_false]

private def LightestLinkCell (G : Network) (u v : Fin G.n) (sentinel : ℝ)
    (edges : List (Fin G.q)) (cell : ℝ × ℕ) : Prop :=
  (cell = (sentinel, G.q) ∧ ∀ e ∈ edges, ¬UndirectedLinkJoins G e u v) ∨
    ∃ e ∈ edges, cell = (G.weight e, e.val) ∧ UndirectedLinkJoins G e u v ∧
      ∀ f ∈ edges, UndirectedLinkJoins G f u v → G.weight e ≤ G.weight f

private theorem linkFold_lightestLinkCell {I : Service} (matrix ids : ℕ)
    (u v : Fin I.graph.n) (sentinel : ℝ) (upper : ∀ e, I.graph.weight e < sentinel)
    (memory : (ℕ → ℝ) × (ℕ → ℕ))
    (initial : linkCell memory (matrix + I.graph.n * u.val + v.val)
      (ids + I.graph.n * u.val + v.val) = (sentinel, I.graph.q))
    (edges : List (Fin I.graph.q)) :
    LightestLinkCell I.graph u v sentinel edges
      (linkCell (edges.foldl (fun m e => linkStepMemory I matrix ids e m) memory)
        (matrix + I.graph.n * u.val + v.val) (ids + I.graph.n * u.val + v.val)) := by
  classical
  induction edges using List.reverseRecOn with
  | nil => exact Or.inl ⟨initial, fun _ he => by simp at he⟩
  | append_singleton edges e ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [linkStepMemory_cell]
    let cell := linkCell (edges.foldl (fun m e => linkStepMemory I matrix ids e m) memory)
      (matrix + I.graph.n * u.val + v.val) (ids + I.graph.n * u.val + v.val)
    by_cases replaces : UndirectedLinkJoins I.graph e u v ∧ I.graph.weight e < cell.1
    · rw [if_pos replaces]
      refine Or.inr ⟨e, List.mem_append_right _ List.mem_cons_self, rfl, replaces.1, ?_⟩
      intro f member joins
      rcases List.mem_append.mp member with earlier | newest
      · rcases ih with ⟨_, missing⟩ | ⟨g, _, represented, _, cheapest⟩
        · exact False.elim (missing f earlier joins)
        · have less := replaces.2
          dsimp only [cell] at less
          rw [represented] at less
          exact less.le.trans (cheapest f earlier joins)
      · have equal : f = e := List.mem_singleton.mp newest
        subst f
        exact le_rfl
    · rw [if_neg replaces]
      rcases ih with ⟨emptyCell, missing⟩ | ⟨g, found, represented, good, cheapest⟩
      · refine Or.inl ⟨emptyCell, fun f member joins => ?_⟩
        rcases List.mem_append.mp member with earlier | newest
        · exact missing f earlier joins
        · have equal : f = e := List.mem_singleton.mp newest
          apply replaces
          refine ⟨equal ▸ joins, ?_⟩
          dsimp only [cell]
          rw [emptyCell]
          exact upper e
      · refine Or.inr ⟨g, List.mem_append_left _ found, represented, good, ?_⟩
        intro f member joins
        rcases List.mem_append.mp member with earlier | newest
        · exact cheapest f earlier joins
        · have equal : f = e := List.mem_singleton.mp newest
          subst f
          have kept : cell.1 ≤ I.graph.weight e := le_of_not_gt (fun cheaper => replaces ⟨joins, cheaper⟩)
          dsimp only [cell] at kept
          rw [represented] at kept
          exact kept

/-- Each off-diagonal adjacency slot is absent exactly when no input link
joins its endpoints. Otherwise its natural ID names a lightest such link. -/
theorem linkScanMemory_lightestLinkId {I : Service} (matrix ids : ℕ) (sentinel : ℝ)
    (upper : ∀ e, I.graph.weight e < sentinel) (memory : (ℕ → ℝ) × (ℕ → ℕ))
    (initialWeight : ∀ u v : Fin I.graph.n, u ≠ v →
      memory.1 (matrix + I.graph.n * u.val + v.val) = sentinel)
    (initialId : ∀ u v : Fin I.graph.n, memory.2 (ids + I.graph.n * u.val + v.val) = I.graph.q) :
    let final := linkScanMemory I matrix ids I.graph.q memory
    ∀ u v : Fin I.graph.n, u ≠ v →
      (final.2 (ids + I.graph.n * u.val + v.val) = I.graph.q ∧
        ∀ e, ¬UndirectedLinkJoins I.graph e u v) ∨
      ∃ e : Fin I.graph.q, final.2 (ids + I.graph.n * u.val + v.val) = e.val ∧
        UndirectedLinkJoins I.graph e u v ∧
        final.1 (matrix + I.graph.n * u.val + v.val) = I.graph.weight e ∧
        ∀ f, UndirectedLinkJoins I.graph f u v → I.graph.weight e ≤ I.graph.weight f := by
  intro final u v distinct
  have initial : linkCell memory (matrix + I.graph.n * u.val + v.val)
      (ids + I.graph.n * u.val + v.val) = (sentinel, I.graph.q) :=
    Prod.ext (initialWeight u v distinct) (initialId u v)
  have complete := linkFold_lightestLinkCell matrix ids u v sentinel upper memory initial
    (List.finRange I.graph.q)
  have allLinks : (List.finRange I.graph.q).take I.graph.q = List.finRange I.graph.q := by
    apply List.take_of_length_le
    simp
  change LightestLinkCell I.graph u v sentinel (List.finRange I.graph.q)
    (linkCell ((List.finRange I.graph.q).foldl (fun m e => linkStepMemory I matrix ids e m) memory)
      (matrix + I.graph.n * u.val + v.val) (ids + I.graph.n * u.val + v.val)) at complete
  have foldEq : final = (List.finRange I.graph.q).foldl (fun m e => linkStepMemory I matrix ids e m) memory := by
    simp only [final, linkScanMemory, allLinks]
  rw [foldEq]
  rcases complete with ⟨empty, missing⟩ | ⟨e, _, named, joins, least⟩
  · exact Or.inl ⟨congrArg Prod.snd empty, fun e => missing e (List.mem_finRange e)⟩
  · exact Or.inr ⟨e, congrArg Prod.snd named, joins, congrArg Prod.fst named,
      fun f => least f (List.mem_finRange f)⟩

/-- A zero diagonal never accepts a nonnegative self-loop, so each diagonal
slot retains its initial absence marker. -/
theorem linkScanMemory_diagonalId {I : Service} (matrix ids : ℕ)
    (nonnegative : Nonnegative I.graph) (memory : (ℕ → ℝ) × (ℕ → ℕ))
    (u : Fin I.graph.n)
    (zero : memory.1 (matrix + I.graph.n * u.val + u.val) = 0)
    (absent : memory.2 (ids + I.graph.n * u.val + u.val) = I.graph.q) :
    (linkScanMemory I matrix ids I.graph.q memory).2 (ids + I.graph.n * u.val + u.val) =
      I.graph.q := by
  have fixed (edges : List (Fin I.graph.q)) (m : (ℕ → ℝ) × (ℕ → ℕ))
      (initial : linkCell m (matrix + I.graph.n * u.val + u.val)
        (ids + I.graph.n * u.val + u.val) = (0, I.graph.q)) :
      linkCell (edges.foldl (fun m e => linkStepMemory I matrix ids e m) m)
        (matrix + I.graph.n * u.val + u.val)
        (ids + I.graph.n * u.val + u.val) = (0, I.graph.q) := by
    induction edges generalizing m with
    | nil => exact initial
    | cons e rest ih =>
      apply ih
      rw [linkStepMemory_cell, initial]
      simp [not_lt_of_ge (nonnegative e)]
  exact congrArg Prod.snd (fixed ((List.finRange I.graph.q).take I.graph.q)
    memory (Prod.ext zero absent))

end VehicleRoutingSurvey.Routing
end RppSource_LinkScan

/-! runtime/LinkIds.lean -/
section RppSource_LinkIds
namespace VehicleRoutingSurvey.Routing

theorem ruralRawWeight_lt_sentinel (I : Service) (nonnegative : Nonnegative I.graph)
    (e : Fin I.graph.q) : I.graph.weight e < 1 + (ruralRealInput I).sum := by
  have bounded : I.graph.weight e ≤ ∑ f, I.graph.weight f :=
    Finset.single_le_sum (fun f _ => nonnegative f) (Finset.mem_univ e)
  simpa [ruralRealInput, ← List.ofFn_eq_map, List.sum_ofFn] using
    bounded.trans_lt (lt_add_of_pos_left _ zero_lt_one)

/-- Read an oriented direct traversal from the dense edge-ID matrix.
The link count denotes absence, and diagonal entries are skipped. -/
def directLinkTableOfMemory (G : Network) (base : ℕ) (memory : ℕ → ℕ) : DirectLinkTable G :=
  fun u v =>
    if u = v then none else
    let id := memory (base + G.n * u.val + v.val)
    if valid : id < G.q then
      let edge : Fin G.q := ⟨id, valid⟩
      some (edge, decide (G.tail edge = u))
    else none

private theorem directLinkTableOfMemory_entry {G : Network} {base : ℕ} {memory : ℕ → ℕ}
    {u v : Fin G.n} (distinct : u ≠ v) {edge : Fin G.q}
    (selected : memory (base + G.n * u.val + v.val) = edge.val) :
    directLinkTableOfMemory G base memory u v = some (edge, decide (G.tail edge = u)) := by
  simp [directLinkTableOfMemory, distinct, selected, edge.isLt]

private theorem orientedLink_endpoints {G : Network} {u v : Fin G.n} (distinct : u ≠ v)
    {edge : Fin G.q} (joins : UndirectedLinkJoins G edge u v) :
    start G (edge, decide (G.tail edge = u)) = u ∧
      finish G (edge, decide (G.tail edge = u)) = v := by
  rcases joins with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [start, finish]
  · simp [start, finish, Ne.symm distinct]

/-- The edge IDs written by the input scan supply the sound and lightest
direct-link representatives required by the reverse tight-edge search. -/
theorem directLinkTableOfScan_correct {I : Service} (rural : Rural I)
    (matrix ids : ℕ) (sentinel : ℝ) (upper : ∀ e, I.graph.weight e < sentinel)
    (memory : (ℕ → ℝ) × (ℕ → ℕ))
    (initialWeight : ∀ u v : Fin I.graph.n, u ≠ v →
      memory.1 (matrix + I.graph.n * u.val + v.val) = sentinel)
    (initialId : ∀ u v : Fin I.graph.n, memory.2 (ids + I.graph.n * u.val + v.val) = I.graph.q) :
    let final := linkScanMemory I matrix ids I.graph.q memory
    let table := directLinkTableOfMemory I.graph ids final.2
    DirectLinkTableSound table ∧ DirectLinkRepresentatives I.graph (tableChooses table) := by
  intro final table
  have find := linkScanMemory_lightestLinkId matrix ids sentinel upper memory initialWeight initialId
  constructor
  · intro u v step found
    have distinct : u ≠ v := by
      rintro rfl
      simp [table, directLinkTableOfMemory] at found
    rcases find u v distinct with ⟨missing, _⟩ | ⟨edge, selected, joins, _, _⟩
    · change final.2 (ids + I.graph.n * u.val + v.val) = I.graph.q at missing
      simp [table, directLinkTableOfMemory, distinct, missing] at found
    · have entry : table u v = some (edge, decide (I.graph.tail edge = u)) :=
        directLinkTableOfMemory_entry distinct selected
      rw [entry] at found
      have equal := Option.some.inj found
      subst step
      have ends := orientedLink_endpoints distinct joins
      exact ⟨ends.1, ends.2, Or.inl (rural.2.2.1 edge)⟩
  · intro original _ distinct
    let u := start I.graph original
    let v := finish I.graph original
    have originalJoins : UndirectedLinkJoins I.graph original.1 u v := by
      cases direction : original.2 <;> simp [u, v, UndirectedLinkJoins, start, finish, direction]
    rcases find u v distinct with ⟨_, missing⟩ | ⟨edge, selected, joins, _, least⟩
    · exact False.elim (missing original.1 originalJoins)
    · let replacement : Traversal I.graph := (edge, decide (I.graph.tail edge = u))
      have ends : start I.graph replacement = u ∧ finish I.graph replacement = v :=
        orientedLink_endpoints distinct joins
      have entry : table u v = some replacement := directLinkTableOfMemory_entry distinct selected
      refine ⟨replacement, ?_, Or.inl (rural.2.2.1 edge), ends.1, ends.2, least _ originalJoins⟩
      change table (start I.graph replacement) (finish I.graph replacement) = some replacement
      rwa [ends.1, ends.2]

/-- Every natural cell agrees with the ID of the decoded direct traversal.
Absent cells, including the diagonal, use the link count. -/
theorem directLinkTableOfScan_idProjection {I : Service} (rural : Rural I)
    (matrix ids : ℕ) (sentinel : ℝ) (upper : ∀ e, I.graph.weight e < sentinel)
    (memory : (ℕ → ℝ) × (ℕ → ℕ))
    (initialWeight : ∀ u v : Fin I.graph.n, u ≠ v →
      memory.1 (matrix + I.graph.n * u.val + v.val) = sentinel)
    (initialDiagonal : ∀ u : Fin I.graph.n, memory.1 (matrix + I.graph.n * u.val + u.val) = 0)
    (initialId : ∀ u v : Fin I.graph.n, memory.2 (ids + I.graph.n * u.val + v.val) = I.graph.q) :
    let final := linkScanMemory I matrix ids I.graph.q memory
    let table := directLinkTableOfMemory I.graph ids final.2
    ∀ u v : Fin I.graph.n, final.2 (ids + I.graph.n * u.val + v.val) =
      ((table u v).map (fun step => step.1.val)).getD I.graph.q := by
  intro final table u v
  by_cases diagonal : u = v
  · subst v
    simpa [table, directLinkTableOfMemory] using
      linkScanMemory_diagonalId matrix ids rural.2.1 memory u (initialDiagonal u) (initialId u u)
  · rcases linkScanMemory_lightestLinkId matrix ids sentinel upper memory initialWeight initialId u v diagonal
      with ⟨missing, _⟩ | ⟨edge, selected, _, _, _⟩
    · change final.2 (ids + I.graph.n * u.val + v.val) = I.graph.q at missing
      simp [table, directLinkTableOfMemory, diagonal, missing]
    · have entry : table u v = some (edge, decide (I.graph.tail edge = u)) :=
        directLinkTableOfMemory_entry diagonal selected
      rw [entry]
      exact selected

end VehicleRoutingSurvey.Routing
end RppSource_LinkIds

/-! runtime/APSPInput.lean -/
section RppSource_APSPInput
namespace VehicleRoutingSurvey.Routing

def apspInputToPathsBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock initAdjacencyBlock linkScanBlock) apspAndTightPathsBlock

private theorem LinkScanFrame.controlOnly {I : Service} {table matrix ids : ℕ}
    {s t : ArithmeticState} (frame : LinkScanFrame I table matrix ids s)
    (fixed : t.nr = s.nr) (natural : t.nm = s.nm) (real : t.rm = s.rm) :
    LinkScanFrame I table matrix ids t := by
  exact ⟨frame.floyd.preserved (fun r _ _ => congrFun fixed r) natural,
    (congrFun fixed 8).trans frame.linkCount, (congrFun fixed 10).trans frame.idBase,
    fun a ha => (congrFun natural a).trans (frame.naturalInput a ha),
    fun e => (congrFun real e.val).trans (frame.realInput e),
    frame.idsAfterInput, frame.idsAfterRows, frame.matrixAfterWeights⟩

/-- From the encoded network and its prepared row offsets and sentinel,
the machine initializes adjacency, scans all links, and computes all
shortest distances and next-edge rows in cubic-plus-linear time. -/
theorem apspInputToPathsBlock_correct {I : Service} {rowOffsets distances : ℕ}
    {s : ArithmeticState} (rural : Rural I)
    (frame : LinkScanFrame I rowOffsets distances (rowOffsets + I.graph.n) s)
    (cells : s.nr 23 = I.graph.n ^ 2) (cursor : s.nr 9 = 2)
    (sentinel : s.rr 0 = 1 + (ruralRealInput I).sum)
    (entry : s.pc = 0) (running : s.halted = false) :
    let n := I.graph.n
    let q := I.graph.q
    let nextBase := rowOffsets + n + n * n + n + n
    ∃ t table, BlockRuns apspInputToPathsBlock
        (49 * n ^ 3 + 24 * n ^ 2 + 30 * n + 28 * q + 21) s t ∧
      t.halted = false ∧ FloydFrame n rowOffsets distances t ∧ t.nr 26 = nextBase ∧
      (∀ a < 2 + 3 * q, t.nm a = (ruralNatInput I)[a]?.getD 0) ∧
      DirectLinkTableSound table ∧
      DirectLinkRepresentatives I.graph (tableChooses table) ∧
      (∀ u v : Fin n, t.rm (distances + n * u.val + v.val) = distance I.graph u v) ∧
      (∀ e : Fin q, t.rm e.val = I.graph.weight e) ∧
      ∀ target, TightStoredRow target table nextBase t.nm := by
  let n := I.graph.n
  let ids := rowOffsets + n
  obtain ⟨i, fill, iReady, iFrame, iCursor, initialWeights, initialIds⟩ :=
    initAdjacencyBlock_correct frame entry running cells
  let scanEntry := {i with pc := 0}
  have scanFrame : LinkScanFrame I rowOffsets distances ids scanEntry :=
    iFrame.controlOnly rfl rfl rfl
  have initialDiagonal (u : Fin n) : i.rm (distances + n * u.val + u.val) = 0 := by
    simpa using initialWeights u u
  have missing (u v : Fin n) (different : u ≠ v) :
      i.rm (distances + n * u.val + v.val) = s.rr 0 := by
    rw [initialWeights, if_neg different]
  have rawUpper (e : Fin I.graph.q) : I.graph.weight e < s.rr 0 := by
    rw [sentinel]
    exact ruralRawWeight_lt_sentinel I rural.2.1 e
  have distanceUpper (u v : Fin n) : distance I.graph u v < s.rr 0 := by
    rw [sentinel]
    simpa [ruralRealInput, ← List.ofFn_eq_map, List.sum_ofFn] using
      distance_lt_weight_sentinel rural.1 rural.2.1 u v
  have initialLower (u v : Fin n) :
      distance I.graph u v ≤ i.rm (distances + n * u.val + v.val) := by
    by_cases same : u = v
    · subst v
      rw [initialDiagonal, distance_self rural.2.1]
    · rw [missing u v same]
      exact (distanceUpper u v).le
  obtain ⟨a, scan, aReady, aFrame, scansMemory⟩ :=
    linkScanBlock_correct scanFrame rfl iReady (iCursor.trans cursor)
  let finishScan := relocateState initAdjacencyBlock.length a
  let apspEntry := {finishScan with pc := 0}
  have prep := fill.append scan
  let table := directLinkTableOfMemory I.graph ids a.nm
  have real := congrArg Prod.fst scansMemory
  have natural := congrArg Prod.snd scansMemory
  change a.rm = (linkScanMemory I distances ids I.graph.q (i.rm, i.nm)).1 at real
  change a.nm = (linkScanMemory I distances ids I.graph.q (i.rm, i.nm)).2 at natural
  have tableCorrect : DirectLinkTableSound table ∧
      DirectLinkRepresentatives I.graph (tableChooses table) := by
    simpa [table, natural] using directLinkTableOfScan_correct rural distances ids (s.rr 0) rawUpper
      (i.rm, i.nm) missing initialIds
  have idCorrect (u v : Fin n) :
      a.nm (ids + n * u.val + v.val) = ((table u v).map (fun step => step.1.val)).getD I.graph.q := by
    simpa [table, natural] using directLinkTableOfScan_idProjection rural distances ids (s.rr 0) rawUpper
      (i.rm, i.nm) missing initialDiagonal initialIds u v
  obtain ⟨diag, edgeUpper, lower⟩ :=
    linkScanMemory_floyd_bounds rural distances ids (i.rm, i.nm) initialDiagonal initialLower
  have count : apspEntry.nm 1 = I.graph.q := by
    change a.nm 1 = I.graph.q
    rw [aFrame.naturalInput 1 (by omega)]
    simp [ruralNatInput]
  have apspFrame : FloydFrame n rowOffsets distances apspEntry :=
    aFrame.floyd.preserved (fun _ _ _ => rfl) rfl
  obtain ⟨t, searches, ready, finalFrame, next, naturalInput, finalDistances, weights, paths⟩ :=
    apspAndTightPathsBlock_correct rural.1 rural.2.1 apspFrame tableCorrect.1 tableCorrect.2
      count aFrame.matrixAfterWeights aFrame.realInput idCorrect
      (fun u => by change a.rm _ = _; rw [real]; exact diag u)
      (fun step _ => by change a.rm _ ≤ _; rw [real]; exact edgeUpper step)
      (fun u v => by change _ ≤ a.rm _; rw [real]; exact lower u v) rfl aReady
  have steps : (7 * n ^ 2 + 9 * n + 4 + (28 * I.graph.q + 2)) +
      (49 * n ^ 3 + 17 * n ^ 2 + 21 * n + 15) =
      49 * n ^ 3 + 24 * n ^ 2 + 30 * n + 28 * I.graph.q + 21 := by ring
  have executes := prep.append searches
  rw [steps] at executes
  have relocatedFrame : FloydFrame n rowOffsets distances
      (relocateState (appendBlock initAdjacencyBlock linkScanBlock).length t) :=
    finalFrame.preserved (fun _ _ _ => rfl) rfl
  refine ⟨_, table, executes, ready, relocatedFrame, next, ?_, tableCorrect.1, tableCorrect.2,
    finalDistances, weights, paths⟩
  intro address bound
  have low : address < rowOffsets + n + n * n :=
    bound.trans_le (aFrame.idsAfterInput.trans (Nat.le_add_right _ _))
  exact (naturalInput address low).trans (aFrame.naturalInput address bound)

/-- The retained encoded link cells supply the tail and head used by the
constant-time next-edge decoder. -/
theorem ruralInputs_preserveLinkEndpoints {I : Service} {s : ArithmeticState}
    (input : ∀ a < 2 + 3 * I.graph.q, s.nm a = (ruralNatInput I)[a]?.getD 0)
    (edge : Fin I.graph.q) :
    s.nm (2 + 3 * edge.val) = (I.graph.tail edge).val ∧
      s.nm (3 + 3 * edge.val) = (I.graph.head edge).val := by
  have valid := edge.isLt
  constructor
  · rw [input _ (by omega)]
    simpa using congrArg (fun cell => cell.getD 0)
      (ruralNatInput_link_record I edge (j := 0) (by decide))
  · rw [show 3 + 3 * edge.val = 2 + 3 * edge.val + 1 by omega, input _ (by omega)]
    exact congrArg (fun cell => cell.getD 0)
      (ruralNatInput_link_record I edge (j := 1) (by decide))

end VehicleRoutingSurvey.Routing
end RppSource_APSPInput

/-! runtime/APSPPreprocess.lean -/
section RppSource_APSPPreprocess
namespace VehicleRoutingSurvey.Routing

def apspInputHeaderBlock : List ArithmeticInstruction :=
  [.natConst 0 0, .natConst 6 1, .natConst 9 2, .natLoad 5 0, .natLoad 8 6,
    .natAdd 4 8 0, .natAdd 3 8 8, .natAdd 3 3 8, .natAdd 3 3 9, .natAdd 10 3 5,
    .natConst 24 0, .realConst 0 1]

private def apspHeaderResult (I : Service) (s : ArithmeticState) : ArithmeticState :=
  let table := I.graph.q + I.graph.q + I.graph.q + 2
  let setup := Function.update (Function.update (Function.update s.nr 0 0) 6 1) 9 2
  let layout := Function.update (Function.update (Function.update setup 5 I.graph.n) 8 I.graph.q)
    4 I.graph.q
  {s with
    pc := 12
    nr := Function.update (Function.update (Function.update layout 3 table) 10 (table + I.graph.n)) 24 0
    rr := Function.update s.rr 0 1}

private theorem apspHeader_runs (I : Service) (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (n : s.nm 0 = I.graph.n) (q : s.nm 1 = I.graph.q) :
    BlockRuns apspInputHeaderBlock 12 s (apspHeaderResult I s) := by
  refine ⟨?_, ?_, rfl⟩
  · intro i less
    interval_cases i <;> simp [apspInputHeaderBlock, arithmeticStep, entry, running,
      Function.iterate_succ_apply']
  · simp [apspInputHeaderBlock, apspHeaderResult, arithmeticStep, entry, running,
      Function.iterate_succ_apply', Function.update_idem, n, q]

private def addWeightCell : List ArithmeticInstruction := [.realLoad 1 7, .realAdd 0 0 1]

private def addWeightCellResult (s : ArithmeticState) : ArithmeticState :=
  {s with
    pc := 2
    rr := Function.update (Function.update s.rr 1 (s.rm (s.nr 7))) 0 (s.rr 0 + s.rm (s.nr 7))}

private theorem addWeightCell_runs (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) : BlockRuns addWeightCell 2 s (addWeightCellResult s) := by
  refine ⟨?_, ?_, rfl⟩
  · intro i less
    interval_cases i <;> simp [addWeightCell, arithmeticStep, entry, running,
      Function.iterate_succ_apply']
  · simp [addWeightCell, addWeightCellResult, arithmeticStep, entry, running,
      Function.iterate_succ_apply']

def apspWeightBlock : List ArithmeticInstruction := countedLoopFromZero 6 7 8 addWeightCell

theorem apspWeightBlock_correct (I : Service) (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1)
    (count : s.nr 8 = I.graph.q) (initial : s.rr 0 = 1)
    (weights : ∀ e : Fin I.graph.q, s.rm e.val = I.graph.weight e) :
    ∃ t, BlockRuns apspWeightBlock (5 * I.graph.q + 2) s t ∧ t.halted = false ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr 0 = 1 + (ruralRealInput I).sum ∧
      ∀ r ≠ 7, t.nr r = s.nr r := by
  let inv (i : ℕ) (m : ArithmeticState) :=
    m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nm = s.nm ∧ m.rm = s.rm ∧
      m.rr 0 = 1 + ((ruralRealInput I).take i).sum ∧ ∀ r ≠ 7, m.nr r = s.nr r
  have startOK : inv 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, rfl, rfl, ?_, ?_⟩
    · simpa using initial
    · intro r different
      exact Function.update_of_ne different _ _
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 8 = I.graph.q := by
    exact ⟨h.1, h.2.1, h.2.2.1, (h.2.2.2.2.2.2 8 (by decide)).trans count⟩
  have next (i : ℕ) (more : i < I.graph.q) (m : ArithmeticState) (h : inv i m) :
      ∃ t, BlockRuns addWeightCell 2 m t ∧ t.halted = false ∧ inv (i + 1)
        {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 6)} := by
    obtain ⟨mEntry, mReady, atIndex, mNatural, mReal, mSum, fixed⟩ := h
    have mOne : m.nr 6 = 1 := (fixed 6 (by decide)).trans one
    let t := addWeightCellResult m
    have observed : m.rm i = (ruralRealInput I)[i]'(by simpa [ruralRealInput] using more) := by
      rw [mReal]
      have gets := ruralRealInput_link_weight I ⟨i, more⟩
      have inside : i < (ruralRealInput I).length := by simpa [ruralRealInput] using more
      rw [List.getElem?_eq_getElem inside, Option.some.injEq] at gets
      exact (weights ⟨i, more⟩).trans gets.symm
    refine ⟨t, addWeightCell_runs m mEntry mReady, mReady, rfl, mReady, ?_, mNatural,
      mReal, ?_, ?_⟩
    · simp [t, addWeightCellResult, atIndex, mOne]
    · have inside : i < (ruralRealInput I).length := by simpa [ruralRealInput] using more
      rw [List.take_succ_eq_append_getElem inside, List.sum_append, List.sum_singleton]
      simp [t, addWeightCellResult, atIndex, mSum, observed, add_assoc]
    · intro r different
      exact (Function.update_of_ne different _ _).trans (fixed r different)
  obtain ⟨last, done, run⟩ := countedLoopFromZero_correct 6 7 8 I.graph.q 2
    addWeightCell inv entry running startOK control next
  obtain ⟨_, ready, _, natural, real, sum, fixed⟩ := done
  have all : (ruralRealInput I).take I.graph.q = ruralRealInput I :=
    List.take_of_length_le (by simp [ruralRealInput])
  rw [all] at sum
  have steps : 1 + (I.graph.q * (2 + 3) + 1) = 5 * I.graph.q + 2 := by omega
  rw [steps] at run
  exact ⟨_, run, ready, natural, real, sum, fixed⟩

private def writeRowOffsetCell : List ArithmeticInstruction :=
  [.natAdd 22 3 7, .natStore 22 24, .natAdd 24 24 5]

private def writeRowOffsetResult (s : ArithmeticState) : ArithmeticState :=
  {s with
    pc := 3
    nr := Function.update (Function.update s.nr 22 (s.nr 3 + s.nr 7)) 24 (s.nr 24 + s.nr 5)
    nm := Function.update s.nm (s.nr 3 + s.nr 7) (s.nr 24)}

private theorem writeRowOffset_runs (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    BlockRuns writeRowOffsetCell 3 s (writeRowOffsetResult s) := by
  refine ⟨?_, ?_, rfl⟩
  · intro i less
    interval_cases i <;> simp [writeRowOffsetCell, arithmeticStep, entry, running,
      Function.iterate_succ_apply']
  · simp [writeRowOffsetCell, writeRowOffsetResult, arithmeticStep, entry, running,
      Function.iterate_succ_apply']

def apspRowOffsetBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 7 5 writeRowOffsetCell

private theorem apspRowOffsetBlock_correct (n : ℕ) (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1)
    (count : s.nr 5 = n) (offset : s.nr 24 = 0) :
    ∃ t, BlockRuns apspRowOffsetBlock (6 * n + 2) s t ∧ t.halted = false ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ r ∉ ([7, 22, 24] : List ℕ), t.nr r = s.nr r) ∧ t.nr 24 = n * n ∧
      (∀ j < n, t.nm (s.nr 3 + j) = n * j) ∧
      ∀ a < s.nr 3, t.nm a = s.nm a := by
  let inv (i : ℕ) (m : ArithmeticState) :=
    m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.rm = s.rm ∧ m.rr = s.rr ∧
      (∀ r ∉ ([7, 22, 24] : List ℕ), m.nr r = s.nr r) ∧ m.nr 24 = n * i ∧
      (∀ j < i, m.nm (s.nr 3 + j) = n * j) ∧ ∀ a < s.nr 3, m.nm a = s.nm a
  have startOK : inv 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, rfl, rfl, ?_, ?_, ?_, fun _ _ => rfl⟩
    · intro r unchanged
      have different : r ≠ 7 := by
        rintro rfl
        exact unchanged (by decide)
      exact Function.update_of_ne different _ _
    · simpa using offset
    · intro _ impossible
      omega
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 5 = n :=
    ⟨h.1, h.2.1, h.2.2.1, (h.2.2.2.2.2.1 5 (by decide)).trans count⟩
  have next (i : ℕ) (_ : i < n) (m : ArithmeticState) (h : inv i m) :
      ∃ t, BlockRuns writeRowOffsetCell 3 m t ∧ t.halted = false ∧ inv (i + 1)
        {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 6)} := by
    obtain ⟨mEntry, mReady, index, real, regs, fixed, current, rows, raw⟩ := h
    let t := writeRowOffsetResult m
    have mOne : m.nr 6 = 1 := (fixed 6 (by decide)).trans one
    have mCount : m.nr 5 = n := (fixed 5 (by decide)).trans count
    have mTable : m.nr 3 = s.nr 3 := fixed 3 (by decide)
    refine ⟨t, writeRowOffset_runs m mEntry mReady, mReady, rfl, mReady, ?_,
      real, regs, ?_, ?_, ?_, ?_⟩
    · simp [t, writeRowOffsetResult, index, mOne]
    · intro r unchanged
      have different (j : ℕ) (member : j ∈ ([7, 22, 24] : List ℕ)) : r ≠ j :=
        fun eq => unchanged (eq.symm ▸ member)
      simp [t, writeRowOffsetResult, Function.update_of_ne (different 7 (by decide)),
        Function.update_of_ne (different 22 (by decide)),
        Function.update_of_ne (different 24 (by decide)), fixed r unchanged]
    · simp [t, writeRowOffsetResult, current, mCount, Nat.mul_succ]
    · intro j present
      change (writeRowOffsetResult m).nm (s.nr 3 + j) = n * j
      by_cases newest : j = i
      · subst j
        simp [writeRowOffsetResult, mTable, index, current]
      · have distinct : s.nr 3 + j ≠ m.nr 3 + m.nr 7 := by omega
        change Function.update m.nm (m.nr 3 + m.nr 7) (m.nr 24) (s.nr 3 + j) = _
        rw [Function.update_of_ne distinct]
        exact rows _ (by omega)
    · intro a outside
      change Function.update m.nm (m.nr 3 + m.nr 7) (m.nr 24) a = s.nm a
      rw [Function.update_of_ne (show a ≠ m.nr 3 + m.nr 7 by omega)]
      exact raw a outside
  obtain ⟨last, done, run⟩ := countedLoopFromZero_correct 6 7 5 n 3
    writeRowOffsetCell inv entry running startOK control next
  obtain ⟨_, ready, _, real, regs, fixed, finalOffset, rows, raw⟩ := done
  have steps : 1 + (n * (3 + 3) + 1) = 6 * n + 2 := by omega
  rw [steps] at run
  exact ⟨_, run, ready, real, regs, fixed, finalOffset, rows, raw⟩

private def saveCellCountBlock : List ArithmeticInstruction := [.natAdd 23 24 0]

private theorem saveCellCount_runs (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    BlockRuns saveCellCountBlock 1 s {s with
      pc := 1
      nr := Function.update s.nr 23 (s.nr 24 + s.nr 0)} := by
  refine ⟨?_, ?_, rfl⟩
  · intro i less
    have zero : i = 0 := by omega
    simp [zero, entry, saveCellCountBlock]
  · simp [saveCellCountBlock, arithmeticStep, entry, running]

/-- Decode the input header, sum the weights, and fill all natural row
offsets. The ID matrix begins immediately after the row offsets. -/
def apspPreprocessBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock (appendBlock apspInputHeaderBlock apspWeightBlock) apspRowOffsetBlock)
    saveCellCountBlock

theorem apspPreprocessBlock_correct (I : Service) :
    let source := arithmeticInput (ruralNatInput I) (ruralRealInput I)
    let base := 2 + 3 * I.graph.q
    ∃ t, BlockRuns apspPreprocessBlock (5 * I.graph.q + 6 * I.graph.n + 17) source t ∧
      t.halted = false ∧ LinkScanFrame I base I.graph.q (base + I.graph.n) t ∧
      t.nr 23 = I.graph.n ^ 2 ∧ t.nr 9 = 2 ∧
      t.rr 0 = 1 + (ruralRealInput I).sum := by
  let source := arithmeticInput (ruralNatInput I) (ruralRealInput I)
  let base := 2 + 3 * I.graph.q
  let header := apspHeaderResult I source
  have hReadN : source.nm 0 = I.graph.n := by simp [source, arithmeticInput, ruralNatInput]
  have hReadQ : source.nm 1 = I.graph.q := by simp [source, arithmeticInput, ruralNatInput]
  have headerRun := apspHeader_runs I source rfl rfl hReadN hReadQ
  have baseEq : I.graph.q + I.graph.q + I.graph.q + 2 = base := by simp [base]; omega
  have headerOne : header.nr 6 = 1 := by simp [header, apspHeaderResult]
  have headerLinks : header.nr 8 = I.graph.q := by simp [header, apspHeaderResult]
  have headerMatrix : header.nr 4 = I.graph.q := by simp [header, apspHeaderResult]
  have headerN : header.nr 5 = I.graph.n := by simp [header, apspHeaderResult]
  have headerBase : header.nr 3 = base := by simp [header, apspHeaderResult, baseEq]
  have headerIds : header.nr 10 = base + I.graph.n := by simp [header, apspHeaderResult, baseEq]
  have headerZero : header.nr 0 = 0 := by simp [header, apspHeaderResult]
  have headerOffset : header.nr 24 = 0 := by simp [header, apspHeaderResult]
  have headerCursor : header.nr 9 = 2 := by simp [header, apspHeaderResult]
  have headerSum : header.rr 0 = 1 := by simp [header, apspHeaderResult]
  have weights (e : Fin I.graph.q) : source.rm e.val = I.graph.weight e := by
    simp [source, arithmeticInput, ruralRealInput_link_weight]
  obtain ⟨w, sumRun, wReady, wNatural, wReal, sum, wFixed⟩ :=
    apspWeightBlock_correct I {header with pc := 0} rfl rfl headerOne headerLinks headerSum weights
  let sumExit := relocateState apspInputHeaderBlock.length w
  let rowsEntry := {sumExit with pc := 0}
  have beginOffset : rowsEntry.nr 24 = 0 := (wFixed 24 (by decide)).trans headerOffset
  have beginOne : rowsEntry.nr 6 = 1 := (wFixed 6 (by decide)).trans headerOne
  have beginSize : rowsEntry.nr 5 = I.graph.n := (wFixed 5 (by decide)).trans headerN
  obtain ⟨rowState, rowRun, rReady, rReal, rRegisters, rFixed, squared, offsets, raw⟩ :=
    apspRowOffsetBlock_correct I.graph.n rowsEntry rfl wReady beginOne beginSize beginOffset
  let rowsExit := relocateState (appendBlock apspInputHeaderBlock apspWeightBlock).length rowState
  let saved := {rowState with pc := 1, nr := Function.update rowState.nr 23 (rowState.nr 24 + rowState.nr 0)}
  have saves : BlockRuns saveCellCountBlock 1 {rowsExit with pc := 0} saved :=
    saveCellCount_runs {rowsExit with pc := 0} rfl rReady
  let final := relocateState
    (appendBlock (appendBlock apspInputHeaderBlock apspWeightBlock) apspRowOffsetBlock).length saved
  have combined := ((headerRun.append sumRun).append rowRun).append saves
  have steps : 12 + (5 * I.graph.q + 2) + (6 * I.graph.n + 2) + 1 =
      5 * I.graph.q + 6 * I.graph.n + 17 := by omega
  rw [steps] at combined
  have unchanged (r : ℕ) (noRow : r ∉ ([7, 22, 24] : List ℕ)) (notSaved : r ≠ 23) :
      final.nr r = header.nr r := by
    have notWeight : r ≠ 7 := fun eq => noRow (eq.symm ▸ (by decide : 7 ∈ ([7, 22, 24] : List ℕ)))
    change Function.update rowState.nr 23 (rowState.nr 24 + rowState.nr 0) r = _
    exact (Function.update_of_ne notSaved _ _).trans
      ((rFixed r noRow).trans (wFixed r notWeight))
  have tableAt : rowsEntry.nr 3 = base := (wFixed 3 (by decide)).trans headerBase
  have theoremFrame : LinkScanFrame I base I.graph.q (base + I.graph.n) final := by
    refine ⟨⟨(unchanged 3 (by decide) (by decide)).trans headerBase,
      (unchanged 4 (by decide) (by decide)).trans headerMatrix,
      (unchanged 5 (by decide) (by decide)).trans headerN,
      (unchanged 6 (by decide) (by decide)).trans headerOne, ?_⟩,
      (unchanged 8 (by decide) (by decide)).trans headerLinks,
      (unchanged 10 (by decide) (by decide)).trans headerIds, ?_, ?_, ?_, le_rfl, le_rfl⟩
    · intro j hj
      have known := offsets j hj
      rwa [tableAt] at known
    · intro a below
      have inside := raw a (by simpa only [tableAt] using below)
      change rowState.nm a = _
      rw [inside]
      exact congrFun wNatural a
    · intro e
      change rowState.rm e.val = _
      rw [rReal]
      exact (congrFun wReal e.val).trans (weights e)
    · dsimp [base]
      omega
  refine ⟨final, combined, rReady, theoremFrame, ?_,
    (unchanged 9 (by decide) (by decide)).trans headerCursor, ?_⟩
  · have zero : rowState.nr 0 = 0 :=
      (rFixed 0 (by decide)).trans ((wFixed 0 (by decide)).trans headerZero)
    simp [final, saved, relocateState, squared, zero, pow_two]
  · exact (congrFun rRegisters 0).trans sum

end VehicleRoutingSurvey.Routing
end RppSource_APSPPreprocess

/-! runtime/APSPComplete.lean -/
section RppSource_APSPComplete
namespace VehicleRoutingSurvey.Routing

def apspFromRawInputBlock : List ArithmeticInstruction :=
  appendBlock apspPreprocessBlock apspInputToPathsBlock

/-- Starting with exactly the mission's encoded input, this block computes
all distances and the associated path pointers, retains the input links,
and exits ready to run the following block of a larger program. -/
theorem apspFromRawInputBlock_correct {I : Service} (rural : Rural I) :
    let n := I.graph.n
    let q := I.graph.q
    let rowOffsets := 2 + 3 * q
    let nextBase := rowOffsets + n + n * n + n + n
    let source := arithmeticInput (ruralNatInput I) (ruralRealInput I)
    ∃ t table, BlockRuns apspFromRawInputBlock
        (49 * n ^ 3 + 24 * n ^ 2 + 36 * n + 33 * q + 38) source t ∧
      t.halted = false ∧ FloydFrame n rowOffsets q t ∧ t.nr 26 = nextBase ∧
      (∀ a < 2 + 3 * q, t.nm a = (ruralNatInput I)[a]?.getD 0) ∧
      DirectLinkTableSound table ∧
      DirectLinkRepresentatives I.graph (tableChooses table) ∧
      (∀ u v : Fin n, t.rm (q + n * u.val + v.val) = distance I.graph u v) ∧
      (∀ edge : Fin q, t.rm edge.val = I.graph.weight edge) ∧
      ∀ target, TightStoredRow target table nextBase t.nm := by
  obtain ⟨prepared, preproc, preparedReady, frame, cells, cursor, sentinel⟩ :=
    apspPreprocessBlock_correct I
  let start := {prepared with pc := 0}
  have inputFrame : LinkScanFrame I (2 + 3 * I.graph.q) I.graph.q
      (2 + 3 * I.graph.q + I.graph.n) start :=
    ⟨frame.floyd.preserved (fun _ _ _ => rfl) rfl, frame.linkCount, frame.idBase,
      frame.naturalInput, frame.realInput, frame.idsAfterInput,
      frame.idsAfterRows, frame.matrixAfterWeights⟩
  obtain ⟨t, table, computes, ready, finalFrame, base, retained, sound, representative,
      distances, weights, rows⟩ :=
    apspInputToPathsBlock_correct rural inputFrame cells cursor sentinel rfl preparedReady
  let final := relocateState apspPreprocessBlock.length t
  have copied : FloydFrame I.graph.n (2 + 3 * I.graph.q) I.graph.q final :=
    finalFrame.preserved (fun _ _ _ => rfl) rfl
  have steps : (5 * I.graph.q + 6 * I.graph.n + 17) +
      (49 * I.graph.n ^ 3 + 24 * I.graph.n ^ 2 + 30 * I.graph.n + 28 * I.graph.q + 21) =
      49 * I.graph.n ^ 3 + 24 * I.graph.n ^ 2 + 36 * I.graph.n + 33 * I.graph.q + 38 := by ring
  have executes := preproc.append computes
  rw [steps] at executes
  exact ⟨final, table, executes, ready, copied, base, retained, sound, representative,
    distances, weights, rows⟩

end VehicleRoutingSurvey.Routing
end RppSource_APSPComplete

/-! runtime/RequiredBitScan.lean -/
section RppSource_RequiredBitScan
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- Read one raw link and mark its ordered endpoint pair when it is required.
Natural register 37 holds the bit-matrix base, and register 33 holds zero. -/
def requiredBitStep : List ArithmeticInstruction :=
  [.natLoad 11 9, .natAdd 9 9 6, .natLoad 12 9, .natAdd 9 9 6,
    .natLoad 13 9, .natAdd 9 9 6,
    .natAdd 38 3 11, .natLoad 38 38, .natAdd 38 38 12, .natAdd 38 37 38,
    .natBranch 13 33 11 12, .jump 13, .natStore 38 13]

private def requiredBitStepState (s : ArithmeticState) : ArithmeticState :=
  let input := s.nr 9
  let one := s.nr 6
  let u := s.nm input
  let v := s.nm (input + one)
  let flag := s.nm (input + one + one)
  let lookup := s.nr 37 + (s.nm (s.nr 3 + u) + v)
  let nr := Function.update s.nr 11 u
  let nr := Function.update nr 9 (input + one)
  let nr := Function.update nr 12 v
  let nr := Function.update nr 9 (input + one + one)
  let nr := Function.update nr 13 flag
  let nr := Function.update nr 9 (input + one + one + one)
  let nr := Function.update nr 38 lookup
  {s with
    pc := 13
    nr := nr
    nm := if flag ≤ s.nr 33 then s.nm else Function.update s.nm lookup flag}

private theorem requiredBitStep_runs {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) : BlockRuns requiredBitStep 12 s (requiredBitStepState s) := by
  by_cases skip : s.nm (s.nr 9 + s.nr 6 + s.nr 6) ≤ s.nr 33
  all_goals
    refine ⟨?_, ?_, rfl⟩
    · intro i hi
      interval_cases i <;> simp [requiredBitStep, arithmeticStep, entry, running,
        Function.iterate_succ_apply', skip]
    · simp [requiredBitStepState, requiredBitStep, arithmeticStep, entry, running,
        Function.iterate_succ_apply', Function.update_idem, skip]

structure RequiredBitFrame (I : Service) (rows matrix bits : ℕ) (s : ArithmeticState) : Prop where
  floyd : FloydFrame I.graph.n rows matrix s
  count : s.nr 8 = I.graph.q
  bitBase : s.nr 37 = bits
  zero : s.nr 33 = 0
  input : ∀ k < 2 + 3 * I.graph.q, s.nm k = (ruralNatInput I)[k]?.getD 0
  bitsAfterInput : 2 + 3 * I.graph.q ≤ bits
  bitsAfterRows : rows + I.graph.n ≤ bits

def markRequiredPair (I : Service) (bits : ℕ) (e : Fin I.graph.q)
    (memory : ℕ → ℕ) : ℕ → ℕ :=
  if e ∈ I.links then
    Function.update memory (bits + I.graph.n * (I.graph.tail e).val + (I.graph.head e).val) 1
  else memory

theorem markRequiredPair_before {I : Service} {bits k : ℕ} (e : Fin I.graph.q)
    (memory : ℕ → ℕ) (before : k < bits) : markRequiredPair I bits e memory k = memory k := by
  unfold markRequiredPair
  split <;> simp [Function.update_of_ne (by omega :
    k ≠ bits + I.graph.n * (I.graph.tail e).val + (I.graph.head e).val)]

theorem requiredBitStep_correct {I : Service} {rows matrix bits : ℕ} {s : ArithmeticState}
    (frame : RequiredBitFrame I rows matrix bits s) (entry : s.pc = 0) (running : s.halted = false)
    (e : Fin I.graph.q) (cursor : s.nr 9 = 2 + 3 * e.val) :
    ∃ t, BlockRuns requiredBitStep 12 s t ∧ t.halted = false ∧
      (∀ r, r ≠ 9 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 38 → t.nr r = s.nr r) ∧
      t.nr 9 = 2 + 3 * (e.val + 1) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      t.nm = markRequiredPair I bits e s.nm := by
  let t := requiredBitStepState s
  have cell (j : ℕ) (part : j < 3) :
      s.nm (2 + 3 * e.val + j) =
        ([(I.graph.tail e).val, (I.graph.head e).val, if e ∈ I.links then 1 else 0][j]?).getD 0 := by
    have inInput := e.isLt
    rw [frame.input _ (by omega), ruralNatInput_link_record I e part]
  have head : s.nm (s.nr 9 + 1) = (I.graph.head e).val := by
    simpa [cursor] using cell 1 (by decide)
  have tail : s.nm (s.nr 9) = (I.graph.tail e).val := by
    simpa [cursor] using cell 0 (by decide)
  have flag : s.nm (s.nr 9 + 1 + 1) = if e ∈ I.links then 1 else 0 := by
    simpa [cursor, Nat.add_assoc] using cell 2 (by decide)
  refine ⟨t, requiredBitStep_runs entry running, running, ?_, ?_, rfl, rfl, ?_⟩
  · intro r p q u v w
    simp [t, requiredBitStepState, Function.update_of_ne p, Function.update_of_ne q,
      Function.update_of_ne u, Function.update_of_ne v, Function.update_of_ne w]
  · simp [t, requiredBitStepState, cursor, frame.floyd.one] <;> omega
  · by_cases required : e ∈ I.links <;>
      simp [t, requiredBitStepState, markRequiredPair, frame.floyd.one, frame.zero, flag,
        required, head, tail, frame.bitBase, frame.floyd.tableBase, frame.floyd.rows _ (I.graph.tail e).isLt,
        Nat.add_assoc]

def requiredBitScanBlock : List ArithmeticInstruction :=
  countedLoopFromZero 6 7 8 requiredBitStep

def requiredBitScanMemory (I : Service) (bits count : ℕ) (memory : ℕ → ℕ) : ℕ → ℕ :=
  ((List.finRange I.graph.q).take count).foldl (fun m e => markRequiredPair I bits e m) memory

theorem requiredBitScanMemory_before {I : Service} {bits k : ℕ} (count : ℕ)
    (memory : ℕ → ℕ) (before : k < bits) :
    requiredBitScanMemory I bits count memory k = memory k := by
  unfold requiredBitScanMemory
  generalize (List.finRange I.graph.q).take count = edges
  induction edges generalizing memory with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.foldl_cons, ih, markRequiredPair_before _ _ before]

private theorem requiredBitScanMemory_succ (I : Service) (bits k : ℕ) (bound : k < I.graph.q)
    (memory : ℕ → ℕ) :
    requiredBitScanMemory I bits (k + 1) memory =
      markRequiredPair I bits ⟨k, bound⟩ (requiredBitScanMemory I bits k memory) := by
  have atIndex : k < (List.finRange I.graph.q).length := by simpa using bound
  simp [requiredBitScanMemory, List.take_succ_eq_append_getElem atIndex, List.foldl_append]

private structure RequiredBitScanState (I : Service) (rows matrix bits : ℕ)
    (initial : ArithmeticState) (index : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  atIndex : s.nr 7 = index
  cursor : s.nr 9 = 2 + 3 * index
  frame : RequiredBitFrame I rows matrix bits s
  realMemory : s.rm = initial.rm
  realRegisters : s.rr = initial.rr
  naturalMemory : s.nm = requiredBitScanMemory I bits index initial.nm
  labelBase : s.nr 24 = initial.nr 24

/-- Collect the ordered endpoint pairs of all required links in one
linear scan. Parallel links simply write the same bit again. -/
theorem requiredBitScanBlock_correct {I : Service} {rows matrix bits : ℕ} {s : ArithmeticState}
    (frame : RequiredBitFrame I rows matrix bits s) (entry : s.pc = 0) (running : s.halted = false)
    (cursor : s.nr 9 = 2) :
    ∃ t, BlockRuns requiredBitScanBlock (15 * I.graph.q + 2) s t ∧
      t.halted = false ∧ RequiredBitFrame I rows matrix bits t ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      t.nm = requiredBitScanMemory I bits I.graph.q s.nm ∧ t.nr 24 = s.nr 24 := by
  let inv := RequiredBitScanState I rows matrix bits s
  let first := {s with pc := 0, nr := Function.update s.nr 7 0}
  have firstFrame : RequiredBitFrame I rows matrix bits first := by
    refine ⟨⟨?_, ?_, ?_, ?_, frame.floyd.rows⟩, ?_, ?_, ?_, frame.input,
      frame.bitsAfterInput, frame.bitsAfterRows⟩
    all_goals simp [first, frame.floyd.tableBase, frame.floyd.matrixBase, frame.floyd.dimension,
      frame.floyd.one, frame.count, frame.bitBase, frame.zero]
  have initial : inv 0 first :=
    ⟨rfl, running, by simp [first], by simpa [first] using cursor, firstFrame, rfl, rfl,
      by simp [first, requiredBitScanMemory], by simp [first]⟩
  have control (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 8 = I.graph.q :=
    ⟨hm.entry, hm.running, hm.atIndex, hm.frame.count⟩
  have iterate (i : ℕ) (bound : i < I.graph.q) (m : ArithmeticState) (hm : inv i m) :
      ∃ t, BlockRuns requiredBitStep 12 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 6)} := by
    let e : Fin I.graph.q := ⟨i, bound⟩
    obtain ⟨t, steps, ready, fixed, cursorAt, rm, rr, nm⟩ :=
      requiredBitStep_correct hm.frame hm.entry hm.running e hm.cursor
    let next := {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 6)}
    have keeps (r : ℕ) (safe : r ≠ 7 ∧ r ≠ 9 ∧ r ≠ 11 ∧ r ≠ 12 ∧ r ≠ 13 ∧ r ≠ 38) :
        next.nr r = m.nr r := by
      change Function.update t.nr 7 (t.nr 7 + t.nr 6) r = m.nr r
      rw [Function.update_of_ne safe.1]
      exact fixed r safe.2.1 safe.2.2.1 safe.2.2.2.1 safe.2.2.2.2.1 safe.2.2.2.2.2
    have before (k : ℕ) (earlier : k < bits) : next.nm k = m.nm k := by
      change t.nm k = m.nm k
      rw [nm, markRequiredPair_before _ _ earlier]
    have nextFrame : RequiredBitFrame I rows matrix bits next :=
      ⟨⟨(keeps 3 (by decide)).trans hm.frame.floyd.tableBase,
        (keeps 4 (by decide)).trans hm.frame.floyd.matrixBase,
        (keeps 5 (by decide)).trans hm.frame.floyd.dimension,
        (keeps 6 (by decide)).trans hm.frame.floyd.one,
        fun k hk => (before _ ((Nat.add_lt_add_left hk _).trans_le hm.frame.bitsAfterRows)).trans
          (hm.frame.floyd.rows k hk)⟩,
        (keeps 8 (by decide)).trans hm.frame.count,
        (keeps 37 (by decide)).trans hm.frame.bitBase,
        (keeps 33 (by decide)).trans hm.frame.zero,
        fun k hk => (before _ (hk.trans_le hm.frame.bitsAfterInput)).trans (hm.frame.input k hk),
        hm.frame.bitsAfterInput, hm.frame.bitsAfterRows⟩
    refine ⟨t, steps, ready, rfl, ready, ?_, ?_, nextFrame, rm.trans hm.realMemory,
      rr.trans hm.realRegisters, ?_, (keeps 24 (by decide)).trans hm.labelBase⟩
    · simp [next, fixed 7 (by decide) (by decide) (by decide) (by decide) (by decide),
        fixed 6 (by decide) (by decide) (by decide) (by decide) (by decide),
        hm.atIndex, hm.frame.floyd.one]
    · simpa [next] using cursorAt
    · change t.nm = _
      rw [nm, hm.naturalMemory, requiredBitScanMemory_succ I bits i bound]
  obtain ⟨last, complete, run⟩ :=
    countedLoopFromZero_correct 6 7 8 I.graph.q 12 requiredBitStep inv entry running initial control iterate
  let finish := relocateState 1 {last with pc := (countedLoop 6 7 8 requiredBitStep).length}
  let f := complete.frame
  have finalFrame : RequiredBitFrame I rows matrix bits finish :=
    ⟨⟨f.floyd.tableBase, f.floyd.matrixBase, f.floyd.dimension, f.floyd.one, f.floyd.rows⟩,
      f.count, f.bitBase, f.zero, f.input, f.bitsAfterInput, f.bitsAfterRows⟩
  have ticks : 1 + (I.graph.q * (12 + 3) + 1) = 15 * I.graph.q + 2 := by omega
  exact ⟨finish, by simpa only [requiredBitScanBlock, ticks] using run, complete.running,
    finalFrame, complete.realMemory, complete.realRegisters, complete.naturalMemory,
    complete.labelBase⟩

private abbrev RequiredOrderedPair (I : Service) (e : Fin I.graph.q) (u v : Fin I.graph.n) : Prop :=
  e ∈ I.links ∧ I.graph.tail e = u ∧ I.graph.head e = v

private theorem markRequiredPair_at {I : Service} (bits : ℕ) (e : Fin I.graph.q)
    (u v : Fin I.graph.n) (memory : ℕ → ℕ) :
    let address := bits + I.graph.n * u.val + v.val
    markRequiredPair I bits e memory address =
      if RequiredOrderedPair I e u v then 1 else memory address := by
  intro address
  by_cases needed : e ∈ I.links
  · unfold markRequiredPair
    rw [if_pos needed]
    by_cases endpoints : I.graph.tail e = u ∧ I.graph.head e = v
    · rw [if_pos ⟨needed, endpoints⟩]
      simp [address, endpoints]
    · rw [if_neg (fun found => endpoints found.2)]
      apply Function.update_of_ne
      intro collision
      have equal : bits + (I.graph.n * u.val + v.val) =
          bits + (I.graph.n * (I.graph.tail e).val + (I.graph.head e).val) := by
        simpa only [address, Nat.add_assoc] using collision
      obtain ⟨first, last⟩ :=
        (denseMatrixOffset_eq_iff v.isLt (I.graph.head e).isLt).mp (Nat.add_left_cancel equal)
      exact endpoints ⟨Fin.ext first.symm, Fin.ext last.symm⟩
  · simp [markRequiredPair, RequiredOrderedPair, needed]

open Classical in
private theorem requiredBitFold_at {I : Service} (bits : ℕ)
    (links : List (Fin I.graph.q)) (u v : Fin I.graph.n) (memory : ℕ → ℕ) :
    let address := bits + I.graph.n * u.val + v.val
    (links.foldl (fun m e => markRequiredPair I bits e m) memory) address =
      if ∃ e ∈ links, RequiredOrderedPair I e u v then 1 else memory address := by
  induction links using List.reverseRecOn with
  | nil => simp
  | append_singleton links e ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [markRequiredPair_at]
    by_cases pair : RequiredOrderedPair I e u v
    · have found : ∃ f ∈ links ++ [e], RequiredOrderedPair I f u v :=
        ⟨e, List.mem_append_right _ List.mem_cons_self, pair⟩
      rw [if_pos pair, if_pos found]
    · have same : (∃ f ∈ links ++ [e], RequiredOrderedPair I f u v) ↔
          ∃ f ∈ links, RequiredOrderedPair I f u v := by
        constructor
        · rintro ⟨f, used, yes⟩
          rcases List.mem_append.mp used with earlier | newest
          · exact ⟨f, earlier, yes⟩
          · have equal : f = e := List.mem_singleton.mp newest
            subst f
            exact False.elim (pair yes)
        · rintro ⟨f, earlier, yes⟩
          exact ⟨f, List.mem_append_left _ earlier, yes⟩
      simp only [if_neg pair, same]
      exact ih

noncomputable def requiredPairFlag (I : Service) (u v : Fin I.graph.n) : Bool := by
  classical
  exact decide (∃ e, RequiredOrderedPair I e u v)

theorem requiredPairFlag_exact (I : Service) (u v : Fin I.graph.n) :
    requiredPairFlag I u v = true ↔ ∃ e ∈ I.links, I.graph.tail e = u ∧ I.graph.head e = v := by
  classical
  simp [requiredPairFlag, RequiredOrderedPair]

theorem requiredPairFlag_vertex {I : Service} (u : Fin I.graph.n) :
    u ∈ requiredVertices I ↔ ∃ v, requiredPairFlag I u v = true ∨ requiredPairFlag I v u = true := by
  constructor
  · intro vertex
    rcases Finset.mem_union.mp vertex with isTail | isHead
    · obtain ⟨e, needed, ends⟩ := Finset.mem_image.mp isTail
      exact ⟨I.graph.head e, Or.inl ((requiredPairFlag_exact _ _ _).mpr ⟨e, needed, ends, rfl⟩)⟩
    · obtain ⟨e, needed, ends⟩ := Finset.mem_image.mp isHead
      exact ⟨I.graph.tail e, Or.inr ((requiredPairFlag_exact _ _ _).mpr ⟨e, needed, rfl, ends⟩)⟩
  · rintro ⟨v, forward | backward⟩
    · obtain ⟨e, needed, ends, _⟩ := (requiredPairFlag_exact I u v).mp forward
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, needed, ends⟩)
    · obtain ⟨e, needed, _, ends⟩ := (requiredPairFlag_exact I v u).mp backward
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, needed, ends⟩)

/-- A zero-initialized bit matrix represents exactly the input's ordered
required endpoint pairs after the scan. -/
theorem requiredBitScanMemory_exact {I : Service} (bits : ℕ) (memory : ℕ → ℕ)
    (zeros : ∀ u v : Fin I.graph.n, memory (bits + I.graph.n * u.val + v.val) = 0)
    (u v : Fin I.graph.n) :
    requiredBitScanMemory I bits I.graph.q memory (bits + I.graph.n * u.val + v.val) =
      if requiredPairFlag I u v then 1 else 0 := by
  classical
  have whole : (List.finRange I.graph.q).take I.graph.q = List.finRange I.graph.q :=
    List.take_of_length_le (by simp)
  simp only [requiredBitScanMemory, whole]
  rw [requiredBitFold_at, zeros]
  have same : (∃ e ∈ List.finRange I.graph.q, RequiredOrderedPair I e u v) ↔
      requiredPairFlag I u v = true := by simp [requiredPairFlag, List.mem_finRange]
  simp only [same]

end VehicleRoutingSurvey.Routing
end RppSource_RequiredBitScan

/-! runtime/RequiredLabels.lean -/
section RppSource_RequiredLabels
namespace VehicleRoutingSurvey.Routing

/-- Merge the class of the second endpoint into the class of the first.
The two labels are read before any entry is changed. -/
def mergeComponentLabels {V : Type*} (labels : V → ℕ) (x y : V) : V → ℕ :=
  fun w => if labels w = labels y then labels x else labels w

def labelComponentPairs {n : ℕ} (pairs : List (Fin n × Fin n)) : Fin n → ℕ :=
  pairs.foldl (fun labels p => mergeComponentLabels labels p.1 p.2) Fin.val

private abbrev PairListAdjacent {V : Type*} (pairs : List (V × V)) (u v : V) : Prop :=
  (u, v) ∈ pairs ∨ (v, u) ∈ pairs

private theorem pairListAdjacent_append {V : Type*} (pairs : List (V × V)) (x y u v : V) :
    PairListAdjacent (pairs ++ [(x, y)]) u v ↔
      PairListAdjacent pairs u v ∨ (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
  simp only [PairListAdjacent, List.mem_append, List.mem_singleton, Prod.mk.injEq]
  tauto

private theorem mergeComponentLabels_eq_iff {V : Type*} (labels : V → ℕ) (x y u v : V) :
    mergeComponentLabels labels x y u = mergeComponentLabels labels x y v ↔
      labels u = labels v ∨
      (labels u = labels x ∧ labels v = labels y) ∨ (labels u = labels y ∧ labels v = labels x) := by
  unfold mergeComponentLabels
  split <;> split <;> grind

private theorem mergeComponentLabels_preserves {V : Type*} {labels : V → ℕ}
    (x y : V) {u v : V} (equal : labels u = labels v) :
    mergeComponentLabels labels x y u = mergeComponentLabels labels x y v :=
  (mergeComponentLabels_eq_iff labels x y u v).mpr (.inl equal)

private theorem mergeComponentLabels_connects {V : Type*} (labels : V → ℕ) (x y : V) :
    mergeComponentLabels labels x y x = mergeComponentLabels labels x y y :=
  (mergeComponentLabels_eq_iff labels x y x y).mpr (.inr (.inl ⟨rfl, rfl⟩))

private theorem mergeComponentLabels_correct {V : Type*} {pairs : List (V × V)}
    {labels : V → ℕ}
    (invariant : ∀ u v, labels u = labels v ↔ Relation.ReflTransGen (PairListAdjacent pairs) u v)
    (x y u v : V) :
    mergeComponentLabels labels x y u = mergeComponentLabels labels x y v ↔
      Relation.ReflTransGen (PairListAdjacent (pairs ++ [(x, y)])) u v := by
  have oldPath {a b : V} (equal : labels a = labels b) :
      Relation.ReflTransGen (PairListAdjacent (pairs ++ [(x, y)])) a b :=
    Relation.ReflTransGen.mono (fun a b step => (pairListAdjacent_append pairs x y a b).mpr (.inl step))
      _ _ ((invariant a b).mp equal)
  constructor
  · intro merged
    rcases (mergeComponentLabels_eq_iff labels x y u v).mp merged with old | ⟨first, last⟩ | ⟨first, last⟩
    · exact oldPath old
    · exact ((oldPath first).tail ((pairListAdjacent_append pairs x y x y).mpr (.inr (.inl ⟨rfl, rfl⟩)))).trans
        (oldPath last.symm)
    · exact ((oldPath first).tail ((pairListAdjacent_append pairs x y y x).mpr (.inr (.inr ⟨rfl, rfl⟩)))).trans
        (oldPath last.symm)
  · intro reachable
    induction reachable with
    | refl => rfl
    | tail _ adjacent ih =>
      apply ih.trans
      rcases (pairListAdjacent_append pairs x y _ _).mp adjacent with old | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact mergeComponentLabels_preserves x y ((invariant _ _).mpr (.single old))
      · rw [ha, hb]
        exact mergeComponentLabels_connects labels x y
      · rw [ha, hb]
        exact (mergeComponentLabels_connects labels x y).symm

private theorem labelComponentPairs_eq_iff {n : ℕ} (pairs : List (Fin n × Fin n)) (u v : Fin n) :
    labelComponentPairs pairs u = labelComponentPairs pairs v ↔
      Relation.ReflTransGen (PairListAdjacent pairs) u v := by
  induction pairs using List.reverseRecOn generalizing u v with
  | nil =>
    constructor
    · intro equal
      have same : u = v := Fin.ext equal
      subst v
      exact .refl
    · intro reachable
      induction reachable with
      | refl => rfl
      | tail _ step _ => simp [PairListAdjacent] at step
  | append_singleton rest p ih =>
    simp only [labelComponentPairs, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact mergeComponentLabels_correct ih p.1 p.2 u v

/-- Any scan retaining exactly the ordered required endpoint pairs computes
labels whose equality is precisely the mission's required-component relation.
Repeated parallel links and loops may be retained or collapsed. -/
theorem labelComponentPairs_sameComponent {I : Service}
    (pairs : List (Fin I.graph.n × Fin I.graph.n))
    (coverage : ∀ u v, (u, v) ∈ pairs ↔
      ∃ e ∈ I.links, I.graph.tail e = u ∧ I.graph.head e = v)
    (u v : Fin I.graph.n) :
    labelComponentPairs pairs u = labelComponentPairs pairs v ↔ sameComponent I u v := by
  have adjacency (a b : Fin I.graph.n) : PairListAdjacent pairs a b ↔ requiredAdjacent I a b := by
    constructor
    · rintro (forward | reverse)
      · obtain ⟨e, member, ends⟩ := (coverage a b).mp forward
        exact ⟨e, member, .inl ends⟩
      · obtain ⟨e, member, ends⟩ := (coverage b a).mp reverse
        exact ⟨e, member, .inr ends⟩
    · rintro ⟨e, member, forward | reverse⟩
      · exact .inl ((coverage a b).mpr ⟨e, member, forward⟩)
      · exact .inr ((coverage b a).mpr ⟨e, member, reverse⟩)
  rw [labelComponentPairs_eq_iff]
  exact ⟨Relation.ReflTransGen.mono (fun a b => (adjacency a b).mp) _ _,
    Relation.ReflTransGen.mono (fun a b => (adjacency a b).mpr) _ _⟩

end VehicleRoutingSurvey.Routing
end RppSource_RequiredLabels


