-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_11
-- name    : LinearSetReconciliation327_Main_B65_11
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T14:32:37.999352+00:00
-- url     : https://prove2.me/theorems/37e8bdfe-1eba-5405-a846-5b0e70ab7fe5
-- title:
--   Theorem 6.5 supporting machine proof B65_11
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_11Part1
set_option autoImplicit false

section S_HintDirectPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintDirectPhase_step {CR : CRFamily} (P : Program) (E : RAMEnv) (state : RAMState)
    (sch : RowScheme) (t : ℕ) (r : sch.LocalSeed) (x : Finset ℕ)
    (node word transcript descriptor base : ℕ) (i : Fin (sch.m * sch.ℓ))
    (event : HintTreeEvent)
    (hEvent : (hintDirectReads sch node (word * E.W))[i.val]? = some event)
    (hRecord : ∀ row col offset, event = .directBit node row col offset →
      (hintDirectBitBlock E.W transcript sch.m row col offset).At E descriptor)
    (hPacked : ∀ a < wordsOf E.W (synLen CR (.direct sch t)),
      state.mem (word + a) = packMem E.W (hintSketchVector CR (.direct sch t) r x) a)
    (hRead : HintTranscriptCorrect sch r x transcript (fun j s => j.val * sch.ℓ + s.val < i.val) state.mem)
    (hW : 0 < E.W) (hWord : 2 < 2 ^ E.W) (hDescSpan : descriptor + 3 < 2 ^ E.W)
    (hInput : word * E.W + synLen CR (.direct sch t) ≤ 2 ^ E.W)
    (hSep : word + wordsOf E.W (synLen CR (.direct sch t)) ≤ transcript)
    (hBefore : (word * E.W + synLen CR (.direct sch t)) / E.W < transcript)
    (hTranscript : transcript + sch.m * sch.ℓ ≤ 2 ^ E.W)
    (hArg : state.regs 6 = descriptor)
    (hAt : At P base (hintUnpackAction.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 22) state (fun k out => k ≤ 24 ∧
      out.regs 14 = state.regs 14 ∧
      (∀ a < wordsOf E.W (synLen CR (.direct sch t)),
        out.mem (word + a) = packMem E.W (hintSketchVector CR (.direct sch t) r x) a) ∧
      HintTranscriptCorrect sch r x transcript (fun j s => j.val * sch.ℓ + s.val < i.val + 1) out.mem ∧
      CRMemFrame transcript (transcript + sch.m * sch.ℓ) state.mem out.mem) := by
  obtain ⟨j, s, hIdx⟩ := hintDirectReads_split i
  have hEvent' := hintDirectReads_at sch node (word * E.W) j s
  rw [hIdx, hEvent'] at hEvent
  have hTab := hRecord j.val s.val (word * E.W + j.val * sch.ℓ + s.val) (Option.some.inj hEvent.symm)
  have hPre := hintDirectBit_pre (CR := CR) E sch t word transcript j s hW hWord hInput hBefore hTranscript
  have hRun := hintDirectBit_sem (CR := CR) P E state sch t r x j s word transcript descriptor base
    hPacked hArg hWord hDescSpan hTab hPre hAt hPc
  apply Sem.mono hRun
  rintro k out ⟨hk, hc, hb, hf⟩
  have hPrev := hRead
  simp only [hIdx] at hPrev ⊢
  have hCell := hintPairOffset_lt s j
  rw [Nat.mul_comm sch.ℓ sch.m] at hCell
  have hKeep : CRMemFrame transcript (transcript + sch.m * sch.ℓ) state.mem out.mem := by
    intro addr ha
    apply hf
    unfold hintTranscriptCell
    rcases ha with ha | ha
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  refine ⟨hk, hc, ?_, hintTranscript_read_step sch r x transcript state.mem out.mem j s hPrev hb hf, hKeep⟩
  intro a ha
  rw [hKeep _ (Or.inl (by omega)), hPacked a ha]

theorem hintDirectPhase_end (sch : RowScheme) (r : sch.LocalSeed) (x : Finset ℕ)
    (transcript : ℕ) (mem : ℕ → ℕ)
    (h : HintTranscriptCorrect sch r x transcript (fun j s => j.val * sch.ℓ + s.val < sch.m * sch.ℓ) mem) :
    HintTranscriptCorrect sch r x transcript (fun _ _ => True) mem :=
  fun j s _ => h j s (hintPairOffset_lt j s)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectPhase_step
#print axioms LinearSetReconciliation327.Main.hintDirectPhase_end
end S_HintDirectPhase20261120
section S_HintPlacedDirectRead20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintPlacedDirectRead_step (S : CRSourceBundle) (H : HintParams)
    (N X Y t W Bc header : ℕ) (lr : (H.scheme N X Y).LocalSeed) (x : Finset ℕ)
    (E : RAMEnv) (state : RAMState) (up previous : ℕ → ℕ) (base : ℕ)
    (i : Fin ((H.scheme N X Y).m * (H.scheme N X Y).ℓ))
    (hWidth : E.W = W) (hHeader : 3 < header)
    (hDet : E.det = (hintDecoderTables S H (.direct N X Y t) W Bc header).det S H up previous header N)
    (hWord : 2 < 2 ^ E.W) (hW : 0 < E.W)
    (hInput : synLen (crFamily S) (.direct (H.scheme N X Y) t) ≤ 2 ^ E.W)
    (hPacked : ∀ a < wordsOf E.W (synLen (crFamily S) (.direct (H.scheme N X Y) t)),
      state.mem a = packMem E.W (hintSketchVector (crFamily S) (.direct (H.scheme N X Y) t) lr x) a)
    (hAt : At (hintNativeProgram S) base (hintUnpackAction.compile base)) (hPc : state.pc = base) :
    let sch := H.scheme N X Y
    let D := hintDecoderTables S H (.direct N X Y t) W Bc header
    let transcript := (D.placement.arena 0).transcript
    let record := hintEventRecord S H D.placement
    let descriptor := hintEventDescriptor header D.events record i.val
    descriptor + 3 < 2 ^ E.W → state.regs 6 = descriptor →
    transcript + sch.m * sch.ℓ ≤ 2 ^ E.W →
    HintTranscriptCorrect sch lr x transcript (fun j s => j.val * sch.ℓ + s.val < i.val) state.mem →
    Sem (hintNativeProgram S) E base (base + 22) state (fun k out =>
      k ≤ 24 ∧ out.regs 14 = state.regs 14 ∧
      (∀ a < wordsOf E.W (synLen (crFamily S) (.direct sch t)),
        out.mem a = packMem E.W (hintSketchVector (crFamily S) (.direct sch t) lr x) a) ∧
      HintTranscriptCorrect sch lr x transcript (fun j s => j.val * sch.ℓ + s.val < i.val + 1) out.mem ∧
      CRMemFrame transcript (transcript + sch.m * sch.ℓ) state.mem out.mem) := by
  let CR := crFamily S
  let sch := H.scheme N X Y
  let D := hintDecoderTables S H (.direct N X Y t) W Bc header
  let A := D.placement.arena 0
  let M := synLen CR (.direct sch t)
  let record := hintEventRecord S H D.placement
  let desc := hintEventDescriptor header D.events record i.val
  have hPrefix : D.events = hintDirectReads sch 0 0 ++
      (List.range sch.m).map (.finishRow 0 0) ++ hintResidualEvents CR 0 (sch.m * sch.ℓ) sch.N t := by
    change hintTreeEvents CR (fun node => if node = 0 then 0 else (D.placement.arena node).payload * W)
      (.direct sch t) 0 0 0 = _
    simpa only [Nat.zero_add] using
      (hintTreeEvents_direct (CR := CR) (fun node => if node = 0 then 0 else (D.placement.arena node).payload * W)
        sch t 0 0 0)
  have hReadLt : i.val < (hintDirectReads sch 0 0).length := by
    rw [hintDirectReads_length]
    exact i.isLt
  have hIn : i.val < D.events.length := by
    simp only [hPrefix, List.length_append]
    omega
  let pos : Fin D.events.length := ⟨i.val, hIn⟩
  have hEvent : (hintDirectReads sch 0 0)[i.val]? = some D.events[pos.val] := by
    have hIdx : D.events[i.val]? = (hintDirectReads sch 0 0)[i.val]? := by
      rw [hPrefix, List.append_assoc, List.getElem?_append_left hReadLt]
    exact hIdx.symm.trans (List.getElem?_eq_getElem (l := D.events) hIn)
  have hPlaced := hintDecoderTables_event_At S H D E up previous header N hHeader hDet pos
  have hTable (row col off : ℕ) (h : D.events[pos.val] = .directBit 0 row col off) :
      (hintDirectBitBlock E.W A.transcript sch.m row col off).At E desc := by
    change (record D.events[pos.val]).At E desc at hPlaced
    rw [h] at hPlaced
    rw [hWidth]
    exact hPlaced
  have hArena (start : ℕ) :
      (hintArenaFor S H W (hintNodeInfo (P := H) CR (.direct N X Y t) 0 0) start).transcript =
        (hintNodeArena start W M 1 sch.m sch.ℓ N (S.data N t).R (S.data N t).W (crSourceSteps S N t)).transcript := rfl
  have hMemBefore : M / E.W < A.transcript := by
    rw [hWidth]
    change M / W < (hintArenaFor S H W (hintNodeInfo (P := H) CR (.direct N X Y t) 0 0)
      (hintArenaStart D.heap D.stride 0)).transcript
    rw [hArena]
    have h := hintNodeArena_input_before (hintArenaStart D.heap D.stride 0)
      W M 1 sch.m sch.ℓ N (S.data N t).R (S.data N t).W (crSourceSteps S N t)
      (hWidth ▸ hW) 0 (Nat.zero_le _)
    simpa only [Nat.zero_mul, Nat.zero_add] using h
  have hSep : wordsOf E.W M ≤ A.transcript := by
    rw [hWidth]
    change wordsOf W M ≤ (hintArenaFor S H W (hintNodeInfo (P := H) CR (.direct N X Y t) 0 0)
      (hintArenaStart D.heap D.stride 0)).transcript
    rw [hArena]
    dsimp only [hintNodeArena]
    omega
  dsimp only
  intro hDesc hArg hFit hRead
  have hRun := hintDirectPhase_step (CR := CR) (hintNativeProgram S) E state sch t lr x
    0 0 A.transcript desc base i D.events[pos.val] (by simpa only [Nat.zero_mul] using hEvent)
    hTable (by simpa only [Nat.zero_add] using hPacked) hRead hW hWord hDesc
    (by simpa only [Nat.zero_mul, Nat.zero_add] using hInput)
    (by simpa only [Nat.zero_add] using hSep)
    (by simpa only [Nat.zero_mul, Nat.zero_add] using hMemBefore)
    hFit hArg hAt hPc
  simpa only [Nat.zero_add] using hRun

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedDirectRead_step
end S_HintPlacedDirectRead20261120
section S_HintDirectReadPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintDirectRoot_events (S : CRSourceBundle) (H : HintParams) (N X Y t W Bc header : ℕ) :
    let sch := H.scheme N X Y
    let D := hintDecoderTables S H (.direct N X Y t) W Bc header
    D.events = hintDirectReads sch 0 0 ++ (List.range sch.m).map (.finishRow 0 0) ++
      hintResidualEvents (crFamily S) 0 (sch.m * sch.ℓ) sch.N t := by
  let sch := H.scheme N X Y
  let D := hintDecoderTables S H (.direct N X Y t) W Bc header
  let offset := fun node => if node = 0 then 0 else (D.placement.arena node).payload * W
  change hintTreeEvents (crFamily S) offset (.direct sch t) 0 0 0 = _
  simpa only [Nat.zero_add] using
    (hintTreeEvents_direct (CR := crFamily S) offset sch t 0 0 0)

noncomputable def hintDirectRead_phase (S : CRSourceBundle) (H : HintParams)
    (N X Y t W Bc header : ℕ) (lr : (H.scheme N X Y).LocalSeed) (x : Finset ℕ)
    (E : RAMEnv) (up previous : ℕ → ℕ) (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = W) (hHeader : 3 < header)
    (hDet : E.det = (hintDecoderTables S H (.direct N X Y t) W Bc header).det S H up previous header N)
    (hWord : 2 < 2 ^ E.W) (hW : 0 < E.W)
    (hInput : synLen (crFamily S) (.direct (H.scheme N X Y) t) ≤ 2 ^ E.W) :
    let sch := H.scheme N X Y
    let D := hintDecoderTables S H (.direct N X Y t) W Bc header
    let transcript := (D.placement.arena 0).transcript
    let M := synLen (crFamily S) (.direct sch t)
    let packed := fun m : ℕ → ℕ => ∀ a < wordsOf E.W M, m a =
      packMem E.W (hintSketchVector (crFamily S) (.direct sch t) lr x) a
    transcript + sch.m * sch.ℓ ≤ 2 ^ E.W →
    wordsOf E.W M ≤ D.control + 2 → D.control + 2 < transcript →
    (∀ j : Fin D.events.length, hintEventDescriptor header D.events
      (hintEventRecord S H D.placement) j.val + 3 < 2 ^ E.W) →
    (∀ m m', CRMemFrame transcript (transcript + sch.m * sch.ℓ) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header 0 (sch.m * sch.ℓ)
      (fun m => packed m ∧ keep m)
      (fun m => packed m ∧ HintTranscriptCorrect sch lr x transcript (fun _ _ => True) m ∧ keep m) := by
  let sch := H.scheme N X Y
  let D := hintDecoderTables S H (.direct N X Y t) W Bc header
  let A := D.placement.arena 0
  let M := synLen (crFamily S) (.direct sch t)
  let packed := fun m : ℕ → ℕ => ∀ a < wordsOf E.W M, m a =
    packMem E.W (hintSketchVector (crFamily S) (.direct sch t) lr x) a
  let inv := fun i m =>
    packed m ∧ HintTranscriptCorrect sch lr x A.transcript (fun j s => j.val * sch.ℓ + s.val < i) m ∧ keep m
  dsimp only
  intro hFit hControlLow hControlHigh hDescriptors hKeep hKeepCursor
  change wordsOf E.W M ≤ D.control + 2 at hControlLow
  change D.control + 2 < A.transcript at hControlHigh
  refine ⟨fun _ => 24, inv, ?_, ?_, ?_, ?_⟩
  · intro m
    constructor
    · rintro ⟨hP, _, hK⟩
      exact ⟨hP, hK⟩
    · rintro ⟨hP, hK⟩
      exact ⟨hP, fun j s h => (Nat.not_lt_zero _ h).elim, hK⟩
  · intro m
    constructor
    · rintro ⟨hP, hT, hK⟩
      exact ⟨hP, hintDirectPhase_end sch lr x _ m hT, hK⟩
    · rintro ⟨hP, hT, hK⟩
      exact ⟨hP, fun j s _ => hT j s trivial, hK⟩
  · intro i m v hm
    rcases hm with ⟨hP, hT, hK⟩
    refine ⟨?_, ?_, hKeepCursor m v hK⟩
    · intro a ha
      rw [Function.update_of_ne (by omega : a ≠ D.control + 2)]
      exact hP a ha
    · intro j s hs
      have hAddr : hintTranscriptCell A.transcript sch.m j.val s.val ≠ D.control + 2 := by
        unfold hintTranscriptCell
        omega
      rw [Function.update_of_ne hAddr]
      exact hT j s hs
  · intro i hi j hj act base state
    dsimp only
    intro hSelect _ hAt hPc hArg hCtx _ hInv _
    have hPos : j.val = i := by omega
    let p : Fin (sch.m * sch.ℓ) := ⟨i, hi⟩
    obtain ⟨row, col, hRC⟩ := hintDirectReads_split p
    have hIn : i < (hintDirectReads sch 0 0).length := by
      rw [hintDirectReads_length]
      exact hi
    have hEv : D.events[j.val]? = some (.directBit 0 row.val col.val (row.val * sch.ℓ + col.val)) := by
      rw [hPos, hintDirectRoot_events S H N X Y t W Bc header, List.append_assoc,
        List.getElem?_append_left hIn]
      change p.val = _ at hRC
      rw [show i = row.val * sch.ℓ + col.val from hRC]
      simpa only [Nat.zero_add] using hintDirectReads_at sch 0 0 row col
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) j.isLt).symm.trans hEv)
    have hTag : D.events[j.val].tag = 0 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintUnpackAction := (Option.some.inj hSelect).symm
    subst act
    obtain ⟨hP, hT, hK⟩ := hInv
    have hArg' : state.regs 6 = hintEventDescriptor header D.events (hintEventRecord S H D.placement) p.val := by
      simpa only [p, hPos] using hArg
    have hStep := hintPlacedDirectRead_step S H N X Y t W Bc header lr x E state up previous base p
      hWidth hHeader hDet hWord hW hInput hP hAt hPc
      (by simpa only [p, hPos] using hDescriptors j) hArg' hFit hT
    change Sem (hintNativeProgram S) E base (base + 22) state _
    apply Sem.mono hStep
    rintro k out ⟨hk, hc, hP', hT', hf⟩
    refine ⟨hk, ⟨hP', hT', hKeep _ _ hf hK⟩, hc.trans hCtx, ?_⟩
    intro a _ ha
    exact hf a (Or.inl (ha.trans_lt hControlHigh))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectRead_phase
end S_HintDirectReadPhase20261120
section S_HintRecursiveSchedule20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintRecursiveColumnEvents (CR : CRFamily) (payloadOffset : ℕ → ℕ)
    (sch : RowScheme) (children : Fin sch.ℓ → Node) (node seed offset : ℕ) (s : Fin sch.ℓ) :
    List HintTreeEvent :=
  let childNode := hintChildPhysicalIndex children node s
  let childSeed := hintChildSchemeIndex children seed s
  let childOff := offset + ((List.ofFn fun i => synLen CR (children i)).take s.val).sum
  (List.range sch.m).map (.predict node seed s.val) ++
    [.childCopy node s.val childNode childOff (synLen CR (children s))] ++
    (List.range sch.m).map (.childToggle node s.val childNode childSeed) ++
    hintTreeEvents CR payloadOffset (children s) childNode childSeed (payloadOffset childNode) ++
    [.recoverColumn node s.val childNode]

theorem hintTreeEvents_recursive {CR : CRFamily} (payloadOffset : ℕ → ℕ) (sch : RowScheme)
    (t : ℕ) (Xs Ys : Fin sch.ℓ → ℕ) (children : Fin sch.ℓ → Node) (node seed offset : ℕ) :
    hintTreeEvents CR payloadOffset (.recursive sch t Xs Ys children) node seed offset =
      (List.ofFn (hintRecursiveColumnEvents CR payloadOffset sch children node seed offset)).flatten ++
        (List.range sch.m).map (.finishRow node seed) ++
        hintResidualEvents CR node (offset + ∑ s, synLen CR (children s)) sch.N t := by
  rw [hintTreeEvents]
  rfl

theorem hintRecursiveColumnEvents_at (CR : CRFamily) (payloadOffset : ℕ → ℕ)
    (sch : RowScheme) (children : Fin sch.ℓ → Node) (node seed offset : ℕ)
    (s : Fin sch.ℓ) (j : ℕ)
    (hj : j < (hintRecursiveColumnEvents CR payloadOffset sch children node seed offset s).length) :
    let columns := hintRecursiveColumnEvents CR payloadOffset sch children node seed offset
    let k := ((List.ofFn fun q => (columns q).length).take s.val).sum + j
    (List.ofFn columns).flatten[k]? = (columns s)[j]? :=
  getElem?_flatten_ofFn' sch.ℓ _ s j hj

theorem hintResidualEvents_length (CR : CRFamily) (node offset N t : ℕ) :
    (hintResidualEvents CR node offset N t).length = N + 3 := by
  simp [hintResidualEvents]

theorem hintResidualEvents_toggle (CR : CRFamily) (node offset N t q : ℕ) (hq : q < N) :
    (hintResidualEvents CR node offset N t)[1 + q]? = some (.residualToggle node q) := by
  have hq' : q < (List.range N).length := by simpa using hq
  have hMap : q < ((List.range N).map (HintTreeEvent.residualToggle node)).length := by simpa using hq
  simp only [hintResidualEvents, List.cons_append, List.nil_append, Nat.one_add,
    List.getElem?_cons_succ, List.getElem?_append_left hMap, List.getElem?_map,
    List.getElem?_eq_getElem hq', List.getElem_range, Option.map_some]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintTreeEvents_recursive
#print axioms LinearSetReconciliation327.Main.hintRecursiveColumnEvents_at
#print axioms LinearSetReconciliation327.Main.hintResidualEvents_toggle
end S_HintRecursiveSchedule20261120
section S_HintDirectRootIndex20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintResidualEvents_copy (CR : CRFamily) (node offset N t : ℕ) :
    (hintResidualEvents CR node offset N t)[0]? = some (.residualCopy node offset (CR.rows N t)) := rfl

theorem hintResidualEvents_decode (CR : CRFamily) (node offset N t : ℕ) :
    (hintResidualEvents CR node offset N t)[1 + N]? = some (.decodeResidual node N t) := by
  let body := [.residualCopy node offset (CR.rows N t)] ++ (List.range N).map (HintTreeEvent.residualToggle node)
  have hLen : body.length = 1 + N := by simp [body, Nat.add_comm]
  change (body ++ [.decodeResidual node N t, .correctEstimate node])[1 + N]? = _
  rw [List.getElem?_append_right (by omega), hLen, Nat.sub_self]
  rfl

theorem hintResidualEvents_correct (CR : CRFamily) (node offset N t : ℕ) :
    (hintResidualEvents CR node offset N t)[1 + N + 1]? = some (.correctEstimate node) := by
  let body := [.residualCopy node offset (CR.rows N t)] ++ (List.range N).map (HintTreeEvent.residualToggle node)
  have hLen : body.length = 1 + N := by simp [body, Nat.add_comm]
  change (body ++ [.decodeResidual node N t, .correctEstimate node])[1 + N + 1]? = _
  rw [List.getElem?_append_right (by omega), hLen]
  rw [show 1 + N + 1 - (1 + N) = 1 by omega]
  rfl

theorem hintDirectRoot_row (S : CRSourceBundle) (H : HintParams) (N X Y t W Bc header q : ℕ)
    (hq : q < H.rows X Y) :
    let sch := H.scheme N X Y
    let D := hintDecoderTables S H (.direct N X Y t) W Bc header
    D.events[sch.m * sch.ℓ + q]? = some (.finishRow 0 0 q) := by
  let sch := H.scheme N X Y
  let D := hintDecoderTables S H (.direct N X Y t) W Bc header
  let body := (List.range sch.m).map (HintTreeEvent.finishRow 0 0)
  have hLen := hintDirectReads_length sch 0 0
  change q < sch.m at hq
  have hBody : q < body.length := by simpa [body] using hq
  have hRange : q < (List.range sch.m).length := by simpa using hq
  have hEvents := hintDirectRoot_events S H N X Y t W Bc header
  change D.events[sch.m * sch.ℓ + q]? = _
  rw [hEvents, List.append_assoc]
  change ((hintDirectReads sch 0 0) ++ (body ++ _))[sch.m * sch.ℓ + q]? = _
  rw [List.getElem?_append_right (by rw [hLen]; omega), hLen]
  have hOffset : sch.m * sch.ℓ + q - sch.m * sch.ℓ = q := by omega
  rw [hOffset, List.getElem?_append_left hBody]
  simp [body, List.getElem?_map, List.getElem?_eq_getElem hRange]

theorem hintDirectRoot_residual (S : CRSourceBundle) (H : HintParams) (N X Y t W Bc header q : ℕ) :
    let sch := H.scheme N X Y
    let D := hintDecoderTables S H (.direct N X Y t) W Bc header
    D.events[sch.m * sch.ℓ + sch.m + q]? =
      (hintResidualEvents (crFamily S) 0 (sch.m * sch.ℓ) sch.N t)[q]? := by
  let sch := H.scheme N X Y
  let D := hintDecoderTables S H (.direct N X Y t) W Bc header
  let body := hintDirectReads sch 0 0 ++ (List.range sch.m).map (HintTreeEvent.finishRow 0 0)
  have hLen : body.length = sch.m * sch.ℓ + sch.m := by simp [body, hintDirectReads_length]
  have hEvents := hintDirectRoot_events S H N X Y t W Bc header
  change D.events[sch.m * sch.ℓ + sch.m + q]? = _
  rw [hEvents]
  change (body ++ hintResidualEvents (crFamily S) 0 (sch.m * sch.ℓ) sch.N t)[sch.m * sch.ℓ + sch.m + q]? = _
  rw [List.getElem?_append_right (by omega), hLen]
  have hOffset : sch.m * sch.ℓ + sch.m + q - (sch.m * sch.ℓ + sch.m) = q := by omega
  rw [hOffset]

theorem hintDirectRoot_count (S : CRSourceBundle) (H : HintParams) (N X Y t W Bc header : ℕ) :
    let sch := H.scheme N X Y
    let D := hintDecoderTables S H (.direct N X Y t) W Bc header
    D.events.length = sch.m * sch.ℓ + sch.m + (1 + sch.N + 1 + 1) := by
  let sch := H.scheme N X Y
  let D := hintDecoderTables S H (.direct N X Y t) W Bc header
  have hEvents := hintDirectRoot_events S H N X Y t W Bc header
  change D.events.length = sch.m * sch.ℓ + sch.m + (1 + sch.N + 1 + 1)
  rw [hEvents]
  simp only [List.length_append, hintDirectReads_length, List.length_map, List.length_range,
    hintResidualEvents_length]
  change sch.m * sch.ℓ + sch.m + (sch.N + 3) = sch.m * sch.ℓ + sch.m + (1 + sch.N + 1 + 1)
  omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectRoot_row
#print axioms LinearSetReconciliation327.Main.hintDirectRoot_residual
#print axioms LinearSetReconciliation327.Main.hintDirectRoot_count
end S_HintDirectRootIndex20261120
section S_HintDirectRootGeometry20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintDirectRoot_arena (S : CRSourceBundle) (H : HintParams) (N X Y t W Bc header : ℕ) :
    let sch := H.scheme N X Y
    let D := hintDecoderTables S H (.direct N X Y t) W Bc header
    let M := synLen (crFamily S) (.direct sch t)
    let data := S.data N t
    D.placement.arena 0 = hintNodeArena (D.listBase + N) W M 1 sch.m sch.ℓ N data.R data.W (crSourceSteps S N t) :=
  rfl

theorem hintFinalScratchEnd_add (H : HintParams) (start N X Y : ℕ) :
    hintFinalScratchEnd H start N X Y = start + hintFinalScratchEnd H 0 N X Y := by
  simp only [hintFinalScratchEnd, hintRowWorkspace, hintGaussDenseArea, Nat.zero_add, Nat.add_assoc]

theorem hintDirectRoot_scratch (S : CRSourceBundle) (H : HintParams) (N X Y t W Bc header : ℕ) :
    let D := hintDecoderTables S H (.direct N X Y t) W Bc header
    hintFinalScratchEnd H D.placement.rowScratch N X Y = D.listBase := by
  let D := hintDecoderTables S H (.direct N X Y t) W Bc header
  let I := hintNodeInfo (P := H) (crFamily S) (.direct N X Y t) 0 0
  change hintFinalScratchEnd H D.placement.rowScratch N X Y =
    D.placement.rowScratch + ([hintRowScratchSize H I] : List ℕ).foldl max 0
  rw [hintFinalScratchEnd_add, List.foldl_cons, List.foldl_nil, zero_max]
  rfl

theorem hintDirectRoot_geometry (S : CRSourceBundle) (H : HintParams)
    (N X Y t W Bc header : ℕ) (hW : 0 < W) :
    let sch := H.scheme N X Y
    let D := hintDecoderTables S H (.direct N X Y t) W Bc header
    let A := D.placement.arena 0
    let M := synLen (crFamily S) (.direct sch t)
    let data := S.data N t
    D.placement.control = D.control ∧
    D.control = wordsOf W M + N ∧
    D.control + 2 < D.placement.rowScratch ∧
    D.placement.rowScratch ≤ D.listBase ∧
    D.listBase + N ≤ A.transcript ∧
    M / W < A.transcript ∧
    A.transcript + sch.ℓ * sch.m ≤ A.hints ∧
    A.hints + N < A.result ∧
    A.result + N < A.residual ∧
    A.residual + (wordsOf W data.R + 2) ≤ A.residualBitmap + 1 ∧
    A.residualBitmap + N < A.crRegisters ∧
    A.limit = A.crRegisters + 16 + (2 ^ (data.W + 1) + 1) + crSourceSteps S N t + 1 := by
  let sch := H.scheme N X Y
  let D := hintDecoderTables S H (.direct N X Y t) W Bc header
  let M := synLen (crFamily S) (.direct sch t)
  let data := S.data N t
  let start := D.listBase + N
  have hArena : D.placement.arena 0 =
      hintNodeArena start W M 1 sch.m sch.ℓ N data.R data.W (crSourceSteps S N t) :=
    hintDirectRoot_arena S H N X Y t W Bc header
  have hControl : D.control + 2 < D.placement.rowScratch := by
    change D.control + 2 < D.control + 3
    omega
  have hScratch : D.placement.rowScratch ≤ D.listBase := by
    rw [← hintDirectRoot_scratch S H N X Y t W Bc header, hintFinalScratchEnd_add]
    exact Nat.le_add_right _ _
  have hBefore := hintNodeArena_input_before start W M 1 sch.m sch.ℓ N data.R data.W (crSourceSteps S N t)
    hW 0 (Nat.zero_le _)
  have hBefore' : M / W < (D.placement.arena 0).transcript := by
    rw [hArena]
    simpa only [Nat.zero_mul, Nat.zero_add] using hBefore
  dsimp only
  refine ⟨rfl, rfl, hControl, hScratch, ?_, hBefore', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change start ≤ (D.placement.arena 0).transcript
    rw [hArena]
    simp only [hintNodeArena]
    omega
  · change (D.placement.arena 0).transcript + sch.ℓ * sch.m ≤ (D.placement.arena 0).hints
    rw [hArena]
    simp [hintNodeArena, Nat.mul_comm sch.ℓ sch.m]
  · rw [hArena]
    simp only [hintNodeArena]
    omega
  · rw [hArena]
    simp only [hintNodeArena]
    omega
  · change (D.placement.arena 0).residual + (wordsOf W data.R + 2) ≤
      (D.placement.arena 0).residualBitmap + 1
    rw [hArena]
    simp only [hintNodeArena]
    omega
  · rw [hArena]
    simp only [hintNodeArena]
    omega
  · rw [hArena]
    rfl

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectRoot_geometry
end S_HintDirectRootGeometry20261120
section S_HintPlacedAuxBounds20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintDetBlockOffset_end (blocks : List HintDetBlock) (j : Fin blocks.length) :
    hintDetBlockOffset blocks j.val + blocks[j.val].length ≤ (blocks.map HintDetBlock.length).sum := by
  let lengths := blocks.map HintDetBlock.length
  have hj : j.val < lengths.length := by simp [lengths]
  have hLen : lengths[j.val] = blocks[j.val].length := by simp [lengths]
  have h := hintTakeSum_mono lengths (Nat.succ_le_of_lt hj)
  rw [hintTakeSum_succ lengths j.val hj, hLen, List.take_of_length_le le_rfl] at h
  simpa only [lengths, hintDetBlockOffset, ← List.map_take] using h

noncomputable def hintDecoderDetEnd (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header : ℕ) : ℕ :=
  hintEventDescriptor header D.events (hintEventRecord S H D.placement) D.events.length +
    (D.aux.map HintDetBlock.length).sum

theorem hintDecoderEvent_end (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header : ℕ) (j : Fin D.events.length) :
    hintEventDescriptor header D.events (hintEventRecord S H D.placement) j.val +
      (hintEventRecord S H D.placement D.events[j.val]).length ≤ hintDecoderDetEnd S H D header := by
  have h := hintEventDescriptor_end header D.events (hintEventRecord S H D.placement) j
  exact h.trans (Nat.le_add_right _ _)

theorem hintDecoderTables_aux_end (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (W Bc header : ℕ) :
    let D := hintDecoderTables S H hT W Bc header
    ∀ n : Fin D.infos.length, ∀ j : Fin (D.nodeAux S H Bc n.val).length,
      D.auxAddress S H Bc header n.val j.val + (D.nodeAux S H Bc n.val)[j.val].length ≤
        hintDecoderDetEnd S H D header := by
  dsimp only
  let D := hintDecoderTables S H hT W Bc header
  intro n j
  have hAux : D.aux = List.ofFn (fun i : Fin D.infos.length => hintJoinDetBlocks (D.nodeAux S H Bc i.val)) := rfl
  have hLength : D.aux.length = D.infos.length := by rw [hAux, List.length_ofFn]
  let p : Fin D.aux.length := ⟨n.val, hLength.symm ▸ n.isLt⟩
  have hAt : D.aux[p.val] = hintJoinDetBlocks (D.nodeAux S H Bc n.val) := by
    have h := List.getElem_ofFn (f := fun i : Fin D.infos.length => hintJoinDetBlocks (D.nodeAux S H Bc i.val))
      (i := n.val) (by simp only [List.length_ofFn]; exact n.isLt)
    simp only [hAux]
    exact h
  have hInner := hintDetBlockOffset_end (D.nodeAux S H Bc n.val) j
  have hOuter := hintDetBlockOffset_end D.aux p
  rw [hAt] at hOuter
  change hintDetBlockOffset D.aux n.val + ((D.nodeAux S H Bc n.val).map HintDetBlock.length).sum ≤
    (D.aux.map HintDetBlock.length).sum at hOuter
  change D.auxAddress S H Bc header n.val j.val + (D.nodeAux S H Bc n.val)[j.val].length ≤
    hintDecoderDetEnd S H D header
  unfold HintDecoderTables.auxAddress hintAuxAddress hintDecoderDetEnd
  omega

theorem hintDecoderTables_rowAux (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (E : RAMEnv) (up previous : ℕ → ℕ)
    (W Bc header N X Y t : ℕ) (hHeader : 3 < header)
    (hDet : E.det = (hintDecoderTables S H hT W Bc header).det S H up previous header T.N) :
    let D := hintDecoderTables S H hT W Bc header
    let L := D.placement
    let R := (S.data N t).R
    let data := S.data N t
    let update := hintSubtreeBlock (crFamily S) W D.control Bc (.cr N t) 0 (wordsOf W R)
    let cr := hintCRTableBlock data.W data.det
    ∀ node : Fin D.infos.length,
      (L.info node.val).universeSize = N → (L.info node.val).residualCapacity = t →
      (L.info node.val).rowParams = some (X, Y) →
      (update.At E (L.residualTable node.val) ∧
        L.residualTable node.val + update.length ≤ hintDecoderDetEnd S H D header) ∧
      (cr.At E (L.crTable node.val) ∧ L.crTable node.val + cr.length ≤ hintDecoderDetEnd S H D header) ∧
      (∀ j : Fin (H.rows X Y),
        let block := hintWaitDetBlock (H.Nmax N X Y) (rowLen N (H.rows X Y) j.val)
          (H.BY N X Y) (H.ell N X Y) (H.c N X Y)
        block.At E (L.threshold node.val j.val) ∧
          L.threshold node.val j.val + block.length ≤ hintDecoderDetEnd S H D header) := by
  dsimp only
  let D := hintDecoderTables S H hT W Bc header
  let L := D.placement
  let data := S.data N t
  let update := hintSubtreeBlock (crFamily S) W D.control Bc (.cr N t) 0 (wordsOf W data.R)
  let cr := hintCRTableBlock data.W data.det
  let wait := fun j : ℕ => hintWaitDetBlock (H.Nmax N X Y) (rowLen N (H.rows X Y) j)
    (H.BY N X Y) (H.ell N X Y) (H.c N X Y)
  intro node hSize hCapacity hXY
  change (L.info node.val).universeSize = N at hSize
  change (L.info node.val).residualCapacity = t at hCapacity
  change (L.info node.val).rowParams = some (X, Y) at hXY
  have hPair : ((L.info node.val).universeSize, (L.info node.val).residualCapacity) = (N, t) :=
    Prod.ext hSize hCapacity
  have hR := congrArg (fun p : ℕ × ℕ => (S.data p.1 p.2).R) hPair
  have hW := congrArg (fun p : ℕ × ℕ => (S.data p.1 p.2).W) hPair
  have hD := congrArg (fun p : ℕ × ℕ => (S.data p.1 p.2).det) hPair
  dsimp only at hR hW hD
  let head := hintSubtreeBlock (crFamily S) W D.control Bc (L.info node.val).subtree
    (L.info node.val).seedIndex (L.arena node.val).saveOffset
  have hBlocks : D.nodeAux S H Bc node.val =
      head :: update :: cr :: (List.range (H.rows X Y)).map wait := by
    unfold HintDecoderTables.nodeAux
    change (let info := L.info node.val
      let a := L.arena node.val
      hintNodeAuxBlocks S H W D.control Bc info a) = _
    simp [hintNodeAuxBlocks, hSize, hCapacity, hXY, head, update, cr, wait, data, hR, hW, hD]
  have hAt (i : Fin (D.nodeAux S H Bc node.val).length) :
      (D.nodeAux S H Bc node.val)[i.val].At E (D.auxAddress S H Bc header node.val i.val) ∧
        D.auxAddress S H Bc header node.val i.val + (D.nodeAux S H Bc node.val)[i.val].length ≤
          hintDecoderDetEnd S H D header :=
    ⟨hintDecoderTables_aux_At S H hT E up previous W Bc header hHeader hDet node i,
      hintDecoderTables_aux_end S H hT W Bc header node i⟩
  have hAddr (j : ℕ) := hintDecoderTables_aux_addresses S H hT W Bc header node.val j
  refine ⟨?_, ?_, ?_⟩
  · let i : Fin (D.nodeAux S H Bc node.val).length := ⟨1, by rw [hBlocks]; simp⟩
    have hIt : (D.nodeAux S H Bc node.val)[i.val] = update := by simp only [hBlocks, i] <;> rfl
    have h := hAt i
    rw [hIt] at h
    rw [(hAddr 0).2.1]
    exact h
  · let i : Fin (D.nodeAux S H Bc node.val).length := ⟨2, by rw [hBlocks]; simp⟩
    have hIt : (D.nodeAux S H Bc node.val)[i.val] = cr := by simp only [hBlocks, i] <;> rfl
    have h := hAt i
    rw [hIt] at h
    rw [(hAddr 0).2.2.1]
    exact h
  · intro j
    let i : Fin (D.nodeAux S H Bc node.val).length := ⟨3 + j.val, by rw [hBlocks]; simp; omega⟩
    have hIt : (D.nodeAux S H Bc node.val)[i.val] = wait j.val := by
      have hi : i.val = j.val + 1 + 1 + 1 := by dsimp only [i]; omega
      simp only [hBlocks, hi, List.getElem_cons_succ, List.getElem_map, List.getElem_range]
    have h := hAt i
    rw [hIt] at h
    rw [(hAddr j.val).2.2.2]
    exact h

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_aux_end
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_rowAux
end S_HintPlacedAuxBounds20261120
section S_HintDirectWordBounds20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintDirectWordBounds (S : CRSourceBundle) (H : HintParams)
    (N X Y t W Bc header : ℕ) : Prop where
  word : 30 < 2 ^ W
  bc : Bc + 1 < 2 ^ W
  keys : H.Nmax N X Y < 2 ^ W
  cols : H.ell N X Y < 2 ^ W
  hx : H.BX N X Y < 2 ^ W
  hy : H.BY N X Y + 1 < 2 ^ W
  coeff : H.rows X Y * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ W
  cr : (S.data N t).W + 1 < W
  input : synLen (crFamily S) (.direct (H.scheme N X Y) t) < 2 ^ W
  det : hintDecoderDetEnd S H (hintDecoderTables S H (.direct N X Y t) W Bc header) header < 2 ^ W
  mem : ((hintDecoderTables S H (.direct N X Y t) W Bc header).placement.arena 0).limit < 2 ^ W
  residual : ((hintDecoderTables S H (.direct N X Y t) W Bc header).placement.arena 0).residual * W +
    (S.data N t).R < 2 ^ W

noncomputable def HintDecoderPhase.append_at {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables}
    {E : RAMEnv} {header first second n m : ℕ} {A B C : (ℕ → ℕ) → Prop}
    (p : HintDecoderPhase S H D E header first n A B)
    (q : HintDecoderPhase S H D E header second m B C)
    (h : second = first + n) :
    HintDecoderPhase S H D E header first (n + m) A C :=
  p.append (h ▸ q)

end LinearSetReconciliation327.Main
end S_HintDirectWordBounds20261120
section S_HintRecursiveCompose20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintEventSlice (D : HintDecoderTables) (first : ℕ) (events : List HintTreeEvent) : Prop :=
  ∃ before after : List HintTreeEvent, before.length = first ∧ D.events = before ++ events ++ after

theorem HintEventSlice.read {D : HintDecoderTables} {first : ℕ} {events : List HintTreeEvent}
    (h : HintEventSlice D first events) (i : ℕ) (hi : i < events.length) :
    D.events[first + i]? = events[i]? := by
  obtain ⟨before, after, hFirst, hEvents⟩ := h
  rw [← hFirst, hEvents, List.append_assoc]
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact List.getElem?_append_left hi

theorem HintEventSlice.left {D : HintDecoderTables} {first : ℕ} {a b : List HintTreeEvent}
    (h : HintEventSlice D first (a ++ b)) : HintEventSlice D first a := by
  obtain ⟨before, after, hLen, hList⟩ := h
  exact ⟨before, b ++ after, hLen, by simpa only [List.append_assoc] using hList⟩

theorem HintEventSlice.right {D : HintDecoderTables} {first : ℕ} {a b : List HintTreeEvent}
    (h : HintEventSlice D first (a ++ b)) : HintEventSlice D (first + a.length) b := by
  obtain ⟨before, after, hLen, hList⟩ := h
  exact ⟨before ++ a, after, by rw [List.length_append, hLen],
    by simpa only [List.append_assoc] using hList⟩

theorem HintEventSlice.flatten {D : HintDecoderTables} {first : ℕ} {blocks : List (List HintTreeEvent)}
    (h : HintEventSlice D first blocks.flatten) (j : ℕ) (hj : j < blocks.length) :
    HintEventSlice D (first + (blocks.take j).flatten.length) blocks[j] := by
  induction blocks generalizing first j with
  | nil => simp at hj
  | cons block blocks ih =>
    cases j with
    | zero =>
      simpa only [List.take_zero, List.flatten_nil, List.length_nil, Nat.add_zero, List.getElem_cons_zero]
        using h.left
    | succ j =>
      have hj' : j < blocks.length := Nat.lt_of_succ_lt_succ hj
      simpa only [List.take_succ_cons, List.flatten_cons, List.length_append, Nat.add_assoc,
        List.getElem_cons_succ] using ih h.right j hj'

def hintPhasePrefixCount (size : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => hintPhasePrefixCount size i + size i

theorem hintFlattenTake_length_succ {α : Type} (blocks : List (List α)) (i : ℕ)
    (hi : i < blocks.length) :
    ((blocks.take (i + 1)).flatten).length = ((blocks.take i).flatten).length + blocks[i].length := by
  induction blocks generalizing i with
  | nil => simp at hi
  | cons block blocks ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.take_succ_cons, List.flatten_cons, List.length_append, List.getElem_cons_succ]
      rw [ih i (Nat.lt_of_succ_lt_succ hi), Nat.add_assoc]

theorem hintPhasePrefixCount_ofFn {m : ℕ} (events : Fin m → List HintTreeEvent)
    (size : ℕ → ℕ) (hSize : ∀ i : Fin m, size i.val = (events i).length) :
    ∀ j ≤ m, hintPhasePrefixCount size j = ((List.ofFn events).take j).flatten.length := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    let i : Fin m := ⟨j, by omega⟩
    have hj' : j < (List.ofFn events).length := by rw [List.length_ofFn]; omega
    rw [hintPhasePrefixCount, ih (by omega), hSize i, hintFlattenTake_length_succ _ _ hj']
    rw [List.getElem_ofFn]

noncomputable def HintDecoderPhase.empty {S : CRSourceBundle} {H : HintParams}
    {D : HintDecoderTables} {E : RAMEnv} {header first : ℕ}
    (inv : (ℕ → ℕ) → Prop)
    (cursor : ∀ m v, inv m → inv (Function.update m (D.control + 2) v)) :
    HintDecoderPhase S H D E header first 0 inv inv :=
  ⟨fun _ => 0, fun _ => inv, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => cursor,
    fun i hi => (Nat.not_lt_zero i hi).elim⟩

noncomputable def HintDecoderPhase.concat {S : CRSourceBundle} {H : HintParams}
    {D : HintDecoderTables} {E : RAMEnv} {header first m : ℕ}
    (size : ℕ → ℕ) (inv : ℕ → (ℕ → ℕ) → Prop)
    (start : ∀ mem v, inv 0 mem → inv 0 (Function.update mem (D.control + 2) v))
    (phase : ∀ i < m, HintDecoderPhase S H D E header (first + hintPhasePrefixCount size i)
      (size i) (inv i) (inv (i + 1))) :
    HintDecoderPhase S H D E header first (hintPhasePrefixCount size m) (inv 0) (inv m) := by
  induction m with
  | zero => exact HintDecoderPhase.empty (inv 0) start
  | succ m ih =>
    exact (ih (fun i hi => phase i (Nat.lt_succ_of_lt hi))).append (phase m (Nat.lt_succ_self m))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintEventSlice.flatten
#print axioms LinearSetReconciliation327.Main.hintPhasePrefixCount_ofFn
#print axioms LinearSetReconciliation327.Main.HintDecoderPhase.concat
end S_HintRecursiveCompose20261120
section S_HintBinaryDirectAt20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintDirectReadAt_total (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node first word N X Y t : ℕ)
    (keep : (ℕ → ℕ) → Prop)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
    (hWidth : E.W = D.placement.width) (hWord : 2 < 2 ^ E.W) (hW : 0 < E.W)
    (hSlice : HintEventSlice D first (hintDirectReads (H.scheme N X Y) node (word * E.W))) :
    let sch := H.scheme N X Y
    let A := D.placement.arena node
    let M := synLen (crFamily S) (.direct sch t)
    A.transcript + sch.m * sch.ℓ ≤ 2 ^ E.W →
    D.control + 2 < A.transcript →
    word + wordsOf E.W M ≤ A.transcript →
    (word * E.W + M) / E.W < A.transcript →
    (D.control + 2 < word ∨ word + wordsOf E.W M ≤ D.control + 2) →
    (∀ pos : Fin D.events.length, first ≤ pos.val → pos.val < first + sch.m * sch.ℓ →
      hintEventDescriptor header D.events (hintEventRecord S H D.placement) pos.val + 3 < 2 ^ E.W) →
    (∀ m m', CRMemFrame A.transcript (A.transcript + sch.m * sch.ℓ) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    word * E.W + M ≤ 2 ^ E.W →
    HintDecoderPhase S H D E header first (sch.m * sch.ℓ)
      keep
      (fun m => HintTranscriptBinary sch A.transcript sch.ℓ m ∧ keep m) := by
  let sch := H.scheme N X Y
  let CR := crFamily S
  let A := D.placement.arena node
  let M := synLen CR (.direct sch t)
  let inv := fun i m =>
    (∀ (j : Fin sch.m) (s : Fin sch.ℓ), j.val * sch.ℓ + s.val < i →
      m (hintTranscriptCell A.transcript sch.m j.val s.val) < 2) ∧ keep m
  dsimp only
  intro hFit hControlHigh _ hInputBefore _ hDescriptors hKeep hKeepCursor hInput
  change D.control + 2 < A.transcript at hControlHigh
  refine ⟨fun _ => 24, inv, ?_, ?_, ?_, ?_⟩
  · intro m
    exact ⟨And.right, fun h => ⟨fun j s h => (Nat.not_lt_zero _ h).elim, h⟩⟩
  · intro m
    exact ⟨fun h => ⟨fun j s _ => h.1 j s (hintPairOffset_lt j s), h.2⟩,
      fun h => ⟨fun j s _ => h.1 j s s.isLt, h.2⟩⟩
  · intro i m v hm
    rcases hm with ⟨hT, hK⟩
    refine ⟨?_, hKeepCursor m v hK⟩
    intro j s hs
    have hAddr : hintTranscriptCell A.transcript sch.m j.val s.val ≠ D.control + 2 := by
      unfold hintTranscriptCell
      omega
    rw [Function.update_of_ne hAddr]
    exact hT j s hs
  · intro i hi j hj act base state
    dsimp only
    intro hSelect _ hAt hPc hArg hCtx _ hInv hRecord
    let p : Fin (sch.m * sch.ℓ) := ⟨i, hi⟩
    have hIn : i < (hintDirectReads sch node (word * E.W)).length := by
      rw [hintDirectReads_length]
      exact hi
    have hEv : (hintDirectReads sch node (word * E.W))[p.val]? = some D.events[j.val] := by
      have h := (hSlice.read i hIn).symm
      rw [← hj] at h
      exact h.trans (List.getElem?_eq_getElem (l := D.events) j.isLt)
    obtain ⟨row, col, hRC⟩ := hintDirectReads_split p
    have hAtEvent := hintDirectReads_at sch node (word * E.W) row col
    have hAtI : (hintDirectReads sch node (word * E.W))[p.val]? =
        some (.directBit node row.val col.val (word * E.W + row.val * sch.ℓ + col.val)) := by
      rw [hRC]
      exact hAtEvent
    have hEq := Option.some.inj (hEv.symm.trans hAtI)
    have hTag : D.events[j.val].tag = 0 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintUnpackAction := (Option.some.inj hSelect).symm
    subst act
    obtain ⟨hT, hK⟩ := hInv
    let desc := hintEventDescriptor header D.events (hintEventRecord S H D.placement) j.val
    have hTable (row col offset : ℕ) (h : D.events[j.val] = .directBit node row col offset) :
        (hintDirectBitBlock E.W A.transcript sch.m row col offset).At E desc := by
      rw [h] at hRecord
      simp only [hintEventRecord, hInfoXY, Option.getD_some] at hRecord
      rw [hWidth]
      exact hRecord
    let dest := hintTranscriptCell A.transcript sch.m row.val col.val
    let offset := word * E.W + row.val * sch.ℓ + col.val
    have hPre := hintDirectBit_pre (CR := CR) E sch t word A.transcript row col hW hWord hInput hInputBefore hFit
    have hSlot := HintUnpackTable.of_block E desc dest offset 1 (hTable _ _ _ hEq)
      hWord (hDescriptors j (by omega) (by omega)) (Nat.lt_of_succ_le hPre.destination)
      (Nat.lt_of_succ_le hPre.offset_span) hPre.count_fit
    have hRun := hintUnpackAction_sem (hintNativeProgram S) E state desc dest offset 1 base
      hSlot hArg hPre hAt hPc
    change Sem (hintNativeProgram S) E base (base + 22) state _
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hb, hf⟩
    have hCell := hintPairOffset_lt col row
    rw [Nat.mul_comm sch.ℓ sch.m] at hCell
    have hFrame : CRMemFrame A.transcript (A.transcript + sch.m * sch.ℓ) state.mem out.mem := by
      intro a ha
      apply hf
      unfold dest hintTranscriptCell
      rcases ha with h | h <;> omega
    refine ⟨by simpa using hk, ⟨?_, hKeep _ _ hFrame hK⟩, hc.trans hCtx, ?_⟩
    · intro row' col' hRead
      by_cases h : hintTranscriptCell A.transcript sch.m row'.val col'.val = dest
      · rw [h, ← Nat.add_zero dest, hb 0 (by decide)]
        unfold bitAt
        exact Nat.mod_lt _ (by decide)
      · rw [hf _ (by omega)]
        apply hT row' col'
        have hIndex : i = row.val * sch.ℓ + col.val := hRC
        have hNe : row'.val * sch.ℓ + col'.val ≠ i := by
          intro hEqIndex
          have hSwap : hintTranscriptCell 0 sch.ℓ col'.val row'.val =
              hintTranscriptCell 0 sch.ℓ col.val row.val := by
            simpa only [hintTranscriptCell, Nat.zero_add, ← hIndex] using hEqIndex
          obtain ⟨hc', hr'⟩ := (hintTranscriptCell_eq_iff 0 col' col row' row).mp hSwap
          subst col'
          subst row'
          exact h rfl
        omega
    · intro a _ ha
      exact hFrame a (Or.inl (ha.trans_lt hControlHigh))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectReadAt_total
end S_HintBinaryDirectAt20261120
section S_HintPrimitiveBudget20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintChildCopy_total_budget (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node childNode first word : ℕ) (sch : RowScheme) (t : ℕ)
    (Xs Ys : Fin sch.ℓ → ℕ) (children : Fin sch.ℓ → Node)
    (col : Fin sch.ℓ)
    (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = D.placement.width) (hWord : 2 < 2 ^ E.W)
    (hW : 0 < E.W) :
    let L := D.placement
    let CR := crFamily S
    let child := children col
    let dest := (L.arena childNode).payload
    let offset := word * E.W + ((List.ofFn fun s => synLen CR (children s)).take col.val).sum
    let count := synLen CR child
    let words := wordsOf E.W count
    ∀
      (hEvent : D.events[first]? = some (.childCopy node col.val childNode offset count))
      (hControl : D.control + 2 < dest)
      (hAddress : dest < 2 ^ E.W)
      (hInput : word * E.W + synLen CR (.recursive sch t Xs Ys children) < 2 ^ E.W)
      (hDest : dest + words ≤ 2 ^ E.W)
      (hSeparate : (word * E.W + synLen CR (.recursive sch t Xs Ys children)) / E.W < dest)
      (hDescriptor : (∀ pos : Fin D.events.length, pos.val = first →
          hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 3 < 2 ^ E.W))
      (hKeep : (∀ m m', CRMemFrame dest (dest + words) m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (i : ℕ),
      (hintChildCopy_total S H D E header node childNode first word sch t Xs Ys children col keep hWidth hWord hW
        hEvent hControl hAddress hInput hDest hSeparate hDescriptor hKeep hCursor).budget i = 17 * count + 13 := by
  intros
  rfl

theorem hintChildToggle_total_budget (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node child seed col first X Y Bc workStart sav : ℕ)
    (T : Node) (r : T.Seed)
    (keep : (ℕ → ℕ) → Prop)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
    (hEvent : ∀ q < T.N, D.events[first + q]? = some (.childToggle node col child seed q))
    (hWord : 16 < 2 ^ E.W) (hSize : T.N ≤ 2 ^ E.W) :
    let L := D.placement
    let CR := crFamily S
    let gate := (L.arena node).transcript + col * H.rows X Y
    let dest := (L.arena child).payload
    let words := wordsOf E.W (synLen CR T)
    let colBase := hintSubtreeColBase Bc T
    let items := hintChildUpdateSchedule CR Bc colBase T seed sav
    let detBase := L.updateTable child
    ∀
      (hCtrl : D.control + 2 < gate)
      (hBefore : gate + T.N ≤ dest)
      (hPay : dest + (sav + 2) ≤ 2 ^ E.W)
      (hGap : words ≤ workStart)
      (hRoom : UpSaveRoom workStart sav T)
      (hDet : detBase + 3 < 2 ^ E.W)
      (hReturn : E.det (detBase + 3) = D.control)
      (hLayout : UpSavedLayout E detBase items)
      (hCount : E.det (detBase % 2 ^ E.W) % 2 ^ E.W = items.length)
      (hLocal : (∀ i < T.N, UpLocalTree CR (upShiftDetEnv E detBase) i Bc colBase T r seed 0 0))
      (hDescriptor : (∀ p : Fin D.events.length, first ≤ p.val → p.val < first + T.N →
          hintEventDescriptor header D.events (hintEventRecord S H L) p.val + 3 < 2 ^ E.W))
      (hKeep : (∀ m m', CRMemFrame dest (dest + sav + 2) m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (i : ℕ),
      (hintChildToggle_total S H D E header node child seed col first X Y Bc workStart sav T r keep hInfoXY hEvent hWord hSize
        hCtrl hBefore hPay hGap hRoom hDet hReturn hLayout hCount hLocal hDescriptor hKeep hCursor).budget i = 147 * items.length + 24 := by
  intros
  rfl

theorem hintRecoverColumn_total_budget (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node child first N X Y : ℕ)
    (col : Fin (H.scheme N X Y).ℓ) (keep : (ℕ → ℕ) → Prop)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
    (hEvent : D.events[first]? = some (.recoverColumn node col.val child)) :
    let L := D.placement
    let sch := H.scheme N X Y
    let transcript := (L.arena node).transcript
    let dest := transcript + col.val * sch.m
    let source := (L.arena child).result
    ∀
      (hWord : 1 < 2 ^ E.W)
      (hCtrl : D.control + 2 < transcript)
      (hCtrlSrc : D.control + 2 < source)
      (hDest : dest < 2 ^ E.W)
      (hSource : source < 2 ^ E.W)
      (hSize : sch.m < 2 ^ E.W)
      (hDestEnd : dest + sch.m ≤ 2 ^ E.W)
      (hSourceEnd : source + sch.m ≤ 2 ^ E.W)
      (hSep : (dest + sch.m ≤ source ∨ source + sch.m ≤ dest))
      (hDescriptor : (∀ pos : Fin D.events.length, pos.val = first →
          hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 2 < 2 ^ E.W))
      (hKeep : (∀ m m', CRMemFrame dest (dest + sch.m) m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (i : ℕ),
      (hintRecoverColumn_total S H D E header node child first N X Y col keep hInfoXY hEvent
        hWord hCtrl hCtrlSrc hDest hSource hSize hDestEnd hSourceEnd hSep hDescriptor hKeep hCursor).budget i = 11 * sch.m + 11 := by
  intros
  rfl

theorem hintResidualCopy_total_budget (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header node first t offset : ℕ) (N : ℕ)
    (E : RAMEnv) (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = D.placement.width) (hWord : 2 < 2 ^ E.W)
    (hEvent : D.events[first]? = some (.residualCopy node offset (S.data N t).R)) :
    let L := D.placement
    let A := L.arena node
    let count := (S.data N t).R
    let words := wordsOf E.W count
    ∀
      (hControl : D.control + 2 < A.result)
      (hSeparate : A.result + N ≤ A.residual)
      (hAddress : A.residual < 2 ^ E.W)
      (hPre : HintStagePre E E.W count offset A.residual)
      (hDescriptor : (∀ pos : Fin D.events.length, pos.val = first →
          hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 3 < 2 ^ E.W))
      (hKeep : (∀ m m', CRMemFrame A.residual (A.residual + words) m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (i : ℕ),
      (hintResidualCopy_total S H D header node first t offset N E keep hWidth hWord hEvent
        hControl hSeparate hAddress hPre hDescriptor hKeep hCursor).budget i = 17 * count + 13 := by
  intros
  rfl

theorem hintResidualToggle_total_budget (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header node first t Bc : ℕ) (N : ℕ)
    (E : RAMEnv) (keep : (ℕ → ℕ) → Prop)
    (hControl : D.placement.control = D.control)
    (hEvent : ∀ q < N, D.events[first + q]? = some (.residualToggle node q))
    (hWord : 16 < 2 ^ E.W) (hSize : N ≤ 2 ^ E.W) :
    let L := D.placement
    let A := L.arena node
    let CR := crFamily S
    let leaf := Node.cr N t
    let words := wordsOf E.W (synLen CR leaf)
    let colBase := hintSubtreeColBase Bc leaf
    let items := hintChildUpdateSchedule CR Bc colBase leaf 0 words
    let detBase := L.residualTable node
    ∀
      (hCtrl : D.control + 2 < A.result)
      (hBefore : A.result + N ≤ A.residual)
      (hPay : A.residual + (words + 2) ≤ 2 ^ E.W)
      (hDet : detBase + 3 < 2 ^ E.W)
      (hReturn : E.det (detBase + 3) = D.control)
      (hLayout : UpSavedLayout E detBase items)
      (hCount : E.det (detBase % 2 ^ E.W) % 2 ^ E.W = items.length)
      (hLocal : (∀ i < N, UpLocalTree CR (upShiftDetEnv E detBase) i Bc colBase leaf () 0 0 0))
      (hDescriptor : (∀ p : Fin D.events.length, first ≤ p.val → p.val < first + N →
          hintEventDescriptor header D.events (hintEventRecord S H L) p.val + 3 < 2 ^ E.W))
      (hKeep : (∀ m m', CRMemFrame A.residual (A.residual + words + 2) m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (i : ℕ),
      (hintResidualToggle_total S H D header node first t Bc N E keep hControl hEvent hWord hSize
        hCtrl hBefore hPay hDet hReturn hLayout hCount hLocal hDescriptor hKeep hCursor).budget i = 147 * items.length + 24 := by
  intros
  rfl

theorem hintResidualDecode_total_budget (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header node first t : ℕ) (N : ℕ)
    (E : RAMEnv) (keep : (ℕ → ℕ) → Prop)
    (hControl : D.placement.control = D.control)
    (hWidth : E.W = D.placement.width) (hW : 0 < E.W)
    (hN : 1 ≤ N) (ht : t ≤ N) (hWord : 11 < 2 ^ E.W)
    (hEvent : D.events[first]? = some (.decodeResidual node N t)) :
    let L := D.placement
    let A := L.arena node
    let w := (S.data N t).W
    let spill := A.crRegisters + 16
    let spillSize := 2 ^ (w + 1) + 1
    let spillEnd := spill + spillSize + crSourceSteps S N t + 1
    ∀
      (hCtrl : D.control + 2 < A.result)
      (hPayload : A.result + N ≤ A.residual)
      (hBefore : A.result + N ≤ A.residualBitmap)
      (hOut : A.residualBitmap + N < A.crRegisters)
      (hEnd : spillEnd < 2 ^ E.W)
      (hSM : w + 1 < E.W)
      (hTable : L.crTable node + 2 ^ w < 2 ^ E.W)
      (hIn : A.residual * E.W + (S.data N t).R < 2 ^ E.W)
      (hInSep : (A.residual * E.W + (S.data N t).R) / E.W < spill)
      (hCRTable : (hintCRTableBlock w (S.data N t).det).At E (L.crTable node))
      (hDesc : (∀ p : Fin D.events.length, p.val = first →
          hintEventDescriptor header D.events (hintEventRecord S H L) p.val + 11 < 2 ^ E.W))
      (hKeep : (∀ m m', CRMemFrame A.residualBitmap spillEnd m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (i : ℕ),
      (hintResidualDecode_total S H D header node first t N E keep hControl hWidth hW hN ht hWord hEvent
        hCtrl hPayload hBefore hOut hEnd hSM hTable hIn hInSep hCRTable hDesc hKeep hCursor).budget i = hintCRNodeBudget S N t := by
  intros
  rfl

theorem hintCorrectEstimate_total_budget (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header node first : ℕ) (N : ℕ)
    (E : RAMEnv) (keep : (ℕ → ℕ) → Prop)
    (hInfo : (D.placement.info node).universeSize = N)
    (hEvent : D.events[first]? = some (.correctEstimate node)) :
    let A := D.placement.arena node
    ∀
      (hWord : 1 < 2 ^ E.W)
      (hCtrl : D.control + 2 < A.result)
      (hDest : A.result < 2 ^ E.W)
      (hSource : A.residualBitmap < 2 ^ E.W)
      (hSize : N < 2 ^ E.W)
      (hSep : A.result + N ≤ A.residualBitmap)
      (hEnd : A.residualBitmap + N ≤ 2 ^ E.W)
      (hDescriptor : (∀ p : Fin D.events.length, p.val = first →
          hintEventDescriptor header D.events (hintEventRecord S H D.placement) p.val + 2 < 2 ^ E.W))
      (hKeep : (∀ m m', CRMemFrame A.result (A.result + N) m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (i : ℕ),
      (hintCorrectEstimate_total S H D header node first N E keep hInfo hEvent
        hWord hCtrl hDest hSource hSize hSep hEnd hDescriptor hKeep hCursor).budget i = 11 * N + 11 := by
  intros
  rfl

theorem hintDirectReadAt_total_budget (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node first word N X Y t : ℕ)
    (keep : (ℕ → ℕ) → Prop)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
    (hWidth : E.W = D.placement.width) (hWord : 2 < 2 ^ E.W) (hW : 0 < E.W)
    (hSlice : HintEventSlice D first (hintDirectReads (H.scheme N X Y) node (word * E.W))) :
    let sch := H.scheme N X Y
    let A := D.placement.arena node
    let M := synLen (crFamily S) (.direct sch t)
    ∀
      (hFit : A.transcript + sch.m * sch.ℓ ≤ 2 ^ E.W)
      (hControlHigh : D.control + 2 < A.transcript)
      (hSep : word + wordsOf E.W M ≤ A.transcript)
      (hInputBefore : (word * E.W + M) / E.W < A.transcript)
      (hControlOutside : (D.control + 2 < word ∨ word + wordsOf E.W M ≤ D.control + 2))
      (hDescriptors : (∀ pos : Fin D.events.length, first ≤ pos.val → pos.val < first + sch.m * sch.ℓ →
          hintEventDescriptor header D.events (hintEventRecord S H D.placement) pos.val + 3 < 2 ^ E.W))
      (hKeep : (∀ m m', CRMemFrame A.transcript (A.transcript + sch.m * sch.ℓ) m m' → keep m → keep m'))
      (hKeepCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (hInput : word * E.W + M ≤ 2 ^ E.W)
      (i : ℕ),
      (hintDirectReadAt_total S H D E header node first word N X Y t keep hInfoXY hWidth hWord hW hSlice
        hFit hControlHigh hSep hInputBefore hControlOutside hDescriptors hKeep hKeepCursor hInput).budget i = 24 := by
  intros
  rfl

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintChildToggle_total_budget
#print axioms LinearSetReconciliation327.Main.hintResidualDecode_total_budget
#print axioms LinearSetReconciliation327.Main.hintDirectReadAt_total_budget
end S_HintPrimitiveBudget20261120


