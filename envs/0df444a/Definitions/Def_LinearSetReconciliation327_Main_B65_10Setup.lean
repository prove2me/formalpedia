-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_10Setup
-- name    : LinearSetReconciliation327_Main_B65_10Setup
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T13:52:54.391803+00:00
-- url     : https://prove2.me/theorems/626c4a50-cf50-5798-8aec-2604b82a2935
-- title:
--   Theorem 6.5 supporting machine proof B65_10Setup
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_HintDecodeBridge20261120
import Definitions.Def_LinearSetReconciliation327_Main_B65_09
set_option autoImplicit false

section S_HintDecoderPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintEventStep (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables) (E : RAMEnv)
    (header : ℕ) (j : Fin D.events.length) (budget : ℕ)
    (pre post : (ℕ → ℕ) → Prop) : Prop :=
  ∀ (act : Stmt) (base : ℕ) (state : RAMState),
    let event := D.events[j.val]
    let desc := hintEventDescriptor header D.events (hintEventRecord S H D.placement) j.val
    (hintNativeActions S)[event.tag]? = some act →
    base = hintActionEntry (hintNativeActions S) 75 event.tag →
    At (hintNativeProgram S) base (act.compile base) →
    state.pc = base → state.regs 6 = desc → state.regs 14 = D.control →
    UpWordState E state → pre state.mem → (hintEventRecord S H D.placement event).At E desc →
    Sem (hintNativeProgram S) E base (base + act.len) state (fun k out =>
      k ≤ budget ∧ post out.mem ∧ out.regs 14 = D.control ∧
      ∀ a, D.control ≤ a → a ≤ D.control + 2 → out.mem a = state.mem a)

theorem HintEventStep.mono {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables}
    {E : RAMEnv} {header : ℕ} {j : Fin D.events.length} {time time' : ℕ}
    {before after pre post : (ℕ → ℕ) → Prop}
    (hStep : HintEventStep S H D E header j time before after)
    (hTime : time ≤ time') (hPre : ∀ m, pre m → before m) (hPost : ∀ m, after m → post m) :
    HintEventStep S H D E header j time' pre post := by
  intro act base state
  dsimp only
  intro hSelect hEntry hAt hPc hArg hCtx hWord hInv hRecord
  apply Sem.mono (hStep act base state hSelect hEntry hAt hPc hArg hCtx hWord (hPre _ hInv) hRecord)
  rintro k out ⟨hk, hOut, hc, hFrame⟩
  exact ⟨hk.trans hTime, hPost _ hOut, hc, hFrame⟩

structure HintDecoderPhase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header first count : ℕ) (before after : (ℕ → ℕ) → Prop) where
  budget : ℕ → ℕ
  inv : ℕ → (ℕ → ℕ) → Prop
  start : ∀ m, inv 0 m ↔ before m
  stop : ∀ m, inv count m ↔ after m
  cursor : ∀ i m v, inv i m → inv i (Function.update m (D.control + 2) v)
  step : ∀ i < count, ∀ j : Fin D.events.length, j.val = first + i →
    HintEventStep S H D E header j (budget i) (inv i) (inv (i + 1))

noncomputable def HintDecoderPhase.append {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables}
    {E : RAMEnv} {header first n m : ℕ} {A B C : (ℕ → ℕ) → Prop}
    (p : HintDecoderPhase S H D E header first n A B)
    (q : HintDecoderPhase S H D E header (first + n) m B C) :
    HintDecoderPhase S H D E header first (n + m) A C := by
  classical
  let inv := fun i a => if i < n then p.inv i a else q.inv (i - n) a
  let budget := fun i => if i < n then p.budget i else q.budget (i - n)
  refine ⟨budget, inv, ?_, ?_, ?_, ?_⟩
  · intro a
    by_cases h : 0 < n
    · simpa only [inv, if_pos h] using p.start a
    · have he : n = 0 := by omega
      have hp : B a ↔ A a := (p.stop a).symm.trans (by simpa only [he] using p.start a)
      simpa only [inv, if_neg h, Nat.zero_sub] using (q.start a).trans hp
  · intro a
    have hn : ¬ n + m < n := by omega
    simpa only [inv, if_neg hn, Nat.add_sub_cancel_left] using q.stop a
  · intro i a v ha
    by_cases hi : i < n
    · simp only [inv, if_pos hi] at ha ⊢
      exact p.cursor i a v ha
    · simp only [inv, if_neg hi] at ha ⊢
      exact q.cursor (i - n) a v ha
  · intro i hi j hj
    by_cases hLeft : i < n
    · have hRun := p.step i hLeft j hj
      apply hRun.mono (by simp [budget, hLeft])
      · intro a h
        simpa only [inv, if_pos hLeft] using h
      · intro a h
        by_cases hNext : i + 1 < n
        · simpa only [inv, if_pos hNext] using h
        · have he : i + 1 = n := by omega
          rw [he] at h ⊢
          simp only [inv, lt_self_iff_false, if_false, Nat.sub_self]
          exact (q.start a).mpr ((p.stop a).mp h)
    · have hRight : i - n < m := by omega
      have hIdx : j.val = first + n + (i - n) := by omega
      have hRun := q.step (i - n) hRight j hIdx
      apply hRun.mono (by simp [budget, hLeft])
      · intro a h
        simpa only [inv, if_neg hLeft] using h
      · intro a h
        have hNext : ¬ i + 1 < n := by omega
        have he : i + 1 - n = i - n + 1 := by omega
        simpa only [inv, if_neg hNext, he] using h

theorem HintDecoderPhase.actions {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables}
    {E : RAMEnv} {header : ℕ} {A B : (ℕ → ℕ) → Prop}
    (p : HintDecoderPhase S H D E header 0 D.events.length A B)
    (up previous : ℕ → ℕ) (N : ℕ) (hHeader : 3 < header)
    (hDet : E.det = D.det S H up previous header N) :
    HintLocatedActions (hintNativeProgram S) E D.control (header + 16) 75 (hintNativeActions S)
      (hintTreeEntries header D.events (hintEventRecord S H D.placement)) p.budget p.inv := by
  apply hintLocatedActions_of_events S H D E up previous header N p.budget p.inv hHeader hDet
  intro j
  exact p.step j.val j.isLt j (Nat.zero_add _).symm

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintDecoderPhase.append
#print axioms LinearSetReconciliation327.Main.HintDecoderPhase.actions
end S_HintDecoderPhase20261120
section S_HintResidualExact20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintCRSketchVector_native (S : CRSourceBundle) (N t : ℕ)
    (r : (Node.cr N t).Seed) (x : Finset ℕ) (hx : x ⊆ Finset.range N) :
    hintSketchVector (crFamily S) (.cr N t) r x = (S.data N t).H (crInput N x) := by
  classical
  funext q
  have h := hintCRBit_eq S N t x hx q
  have hB : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  change (if q.val ∈ (crFamily S).sketch N t x then 1 else 0) = (S.data N t).H (crInput N x) q
  rcases hB ((S.data N t).H (crInput N x) q) with h0 | h1
  · rw [h0] at h ⊢
    have hNot : q.val ∉ (crFamily S).sketch N t x := by
      intro hYes
      simp [hintTruth, hYes] at h
    simp [hNot]
  · rw [h1] at h ⊢
    have hYes : q.val ∈ (crFamily S).sketch N t x := by
      by_contra hNot
      simp [hintTruth, hNot] at h
    simp [hYes]

theorem hintExactEstimate_subset (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ) :
    sch.exactEstimate lr x J ⊆ Finset.range sch.N := by
  intro i hi
  unfold RowScheme.exactEstimate RowScheme.assembled assemble at hi
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_range.mpr u.isLt

theorem hintResidual_input (S : CRSourceBundle) (sch : RowScheme) (lr : sch.LocalSeed)
    (x J : Finset ℕ) (t : ℕ) (r : (Node.cr sch.N t).Seed)
    (hx : x ⊆ Finset.range sch.N) (hZ : sch.Z lr x J ≤ t) :
    let residual := symmDiff x (sch.exactEstimate lr x J)
    (Finset.univ.filter fun i : Fin sch.N => crInput sch.N residual i = 1).card ≤ t ∧
      hintSketchVector (crFamily S) (.cr sch.N t) r x +
          hintSketchVector (crFamily S) (.cr sch.N t) r (sch.exactEstimate lr x J) =
        (S.data sch.N t).H (crInput sch.N residual) := by
  let est := sch.exactEstimate lr x J
  let res := symmDiff x est
  have hEst : est ⊆ Finset.range sch.N := hintExactEstimate_subset sch lr x J
  have hRes : res ⊆ Finset.range sch.N := by
    intro i hi
    rcases Finset.mem_symmDiff.mp hi with ⟨h, _⟩ | ⟨h, _⟩
    · exact hx h
    · exact hEst h
  refine ⟨?_, ?_⟩
  · rw [crInput_card sch.N res hRes]
    exact hZ
  · exact (hintSketchVector_xor (crFamily S) (.cr sch.N t) r x est).symm.trans
      (hintCRSketchVector_native S sch.N t r res hRes)
 
theorem hintColumnRecovered (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ) (s : Fin sch.ℓ) :
    symmDiff (sch.exactP lr x J s) (sch.exactChildInput lr x J s) = sch.column lr x s :=
  hintPlusResidual _ _

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintResidual_input
#print axioms LinearSetReconciliation327.Main.hintColumnRecovered
end S_HintResidualExact20261120
section S_HintPlacedResidual20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintUpdate_prefix_step (CR : CRFamily) (T : Node) (r : T.Seed)
    (selected : Finset ℕ) (y : Fin (synLen CR T) → ZMod 2) (i : Fin T.N)
    (P : Program) (E : RAMEnv) (state : RAMState)
    (seed base descriptor gate detBase payBase control Bc colBase workStart sav : ℕ)
    (tbl : HintToggleGateTable E descriptor gate i.val detBase payBase control)
    (hArg : state.regs 6 = descriptor) (hWord : UpWordState E state)
    (hAt : At P base (hintToggleGateAction.compile base)) (hPc : state.pc = base)
    (hGate : state.mem gate = hintTruth (i.val ∈ selected))
    (hPayEnd : payBase + (sav + 2) ≤ 2 ^ E.W)
    (hGap : wordsOf E.W (synLen CR T) ≤ workStart)
    (h16 : 16 < 2 ^ E.W) (hN : T.N ≤ 2 ^ E.W)
    (hPayload : ∀ q < wordsOf E.W (synLen CR T), state.mem (payBase + q) =
      packMem E.W (y + hintSketchVector CR T r (selected ∩ Finset.range i.val)) q)
    (hLocal : UpLocalTree CR (upShiftDetEnv E detBase) i.val Bc colBase T r seed 0 0)
    (hRoom : UpSaveRoom workStart sav T) :
    let items := hintChildUpdateSchedule CR Bc colBase T seed sav
    UpSavedLayout E detBase items →
    E.det (detBase % 2 ^ E.W) % 2 ^ E.W = items.length →
    Sem P E base (base + hintToggleGateAction.len) state (fun k out =>
      k ≤ 147 * items.length + 24 ∧ out.regs 14 = control ∧
      (∀ q < wordsOf E.W (synLen CR T), out.mem (payBase + q) =
        packMem E.W (y + hintSketchVector CR T r (selected ∩ Finset.range (i.val + 1))) q) ∧
      UpMemFrame (UpTwoRegion payBase (wordsOf E.W (synLen CR T)) workStart (sav + 2)) state out) := by
  dsimp only
  intro hLayout hCount
  have hStep := hintChildUpdateAction_sem P E state CR T r seed base descriptor gate detBase payBase
    control Bc colBase workStart sav _ (y + hintSketchVector CR T r (selected ∩ Finset.range i.val)) i
    rfl tbl hArg hWord hAt hPc hLayout hPayEnd hGap h16 hN hCount hPayload hLocal hRoom
  apply Sem.mono hStep
  rintro k out ⟨hk, hCtrl, hNew, hFrame⟩
  refine ⟨hk, hCtrl, ?_, hFrame⟩
  intro q hq
  rw [hNew q hq, hGate, hintToggleTrace_step]

theorem hintResidualDecode_placed (S : CRSourceBundle) (L : HintDecoderPlacement)
    (node descriptor t base switchBase : ℕ) (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (other : List Stmt) (act : Stmt)
    (hW : E.W = L.width) (hWidth : 0 < E.W)
    (hx : x ⊆ Finset.range sch.N) (hZ : sch.Z lr x J ≤ t)
    (hN : 1 ≤ sch.N) (ht : t ≤ sch.N)
    (hWord : 11 < 2 ^ E.W) (hDesc : descriptor + 11 < 2 ^ E.W)
    (hSmall : (S.data sch.N t).W + 1 < E.W)
    (hControl : L.control < 2 ^ E.W)
    (hSpill : (L.arena node).crRegisters + 16 + 2 ^ ((S.data sch.N t).W + 1) + 1 +
      crSourceSteps S sch.N t + 1 < 2 ^ E.W)
    (hTableFit : L.crTable node + 2 ^ (S.data sch.N t).W < 2 ^ E.W)
    (hOut : (L.arena node).residualBitmap + sch.N < (L.arena node).crRegisters)
    (hInput : (L.arena node).residual * E.W + (S.data sch.N t).R < 2 ^ E.W)
    (hInputSep : ((L.arena node).residual * E.W + (S.data sch.N t).R) / E.W <
      (L.arena node).crRegisters + 16)
    (hCRTable : (hintCRTableBlock (S.data sch.N t).W (S.data sch.N t).det).At E (L.crTable node))
    (hRecord : (hintCREventBlock S L node ((L.arena node).residual * L.width)
      (L.arena node).residualBitmap sch.N t).At E descriptor)
    (hFresh : ∀ a ≤ 2 ^ ((S.data sch.N t).W + 1), state.mem ((L.arena node).crRegisters + 16 + a) = 0)
    (hPc : state.pc = base) (hArg : state.regs 6 = descriptor)
    (hSelect : (hintActionsWithCR S switchBase other hintNormalizeStmt)[other.length]? = some act)
    (hEntry : base = hintActionEntry (hintActionsWithCR S switchBase other hintNormalizeStmt) switchBase other.length)
    (hAt : At P base (act.compile base)) :
    let A := L.arena node
    let r : (Node.cr sch.N t).Seed := ()
    let estimate := sch.exactEstimate lr x J
    let residual := symmDiff x estimate
    let layout := hintCRArea (S.data sch.N t).W (A.residual * E.W) A.crRegisters (L.crTable node)
                    descriptor A.residualBitmap L.control
    (∀ q < wordsOf E.W (S.data sch.N t).R, state.mem (A.residual + q) =
      packMem E.W (hintSketchVector (crFamily S) (.cr sch.N t) r x +
                   hintSketchVector (crFamily S) (.cr sch.N t) r estimate) q) →
    Sem P E base (base + act.len) state (fun k out =>
      k ≤ hintCRNodeBudget S sch.N t ∧ out.regs 14 = L.control ∧
      HintBitmap out.mem A.residualBitmap sch.N residual ∧
      HintCRNodeFrame S layout sch.N t state.mem out.mem) := by
  let A := L.arena node
  let r : (Node.cr sch.N t).Seed := ()
  let estimate := sch.exactEstimate lr x J
  let residual := symmDiff x estimate
  let layout := hintCRArea (S.data sch.N t).W (A.residual * E.W) A.crRegisters (L.crTable node)
                    descriptor A.residualBitmap L.control
  dsimp only
  intro hPacked
  have hReq : (hintCRCallBlock layout E.W (S.data sch.N t).W (S.data sch.N t).R
      (crSourceSteps S sch.N t) sch.N).At E descriptor := by
    rw [hintCREventBlock_descriptor S L node _ _ _ _ descriptor] at hRecord
    simpa only [layout, A, hW] using hRecord
  have hPre := hintCRArea_pre S E sch.N t (A.residual * E.W) A.crRegisters (L.crTable node)
    descriptor A.residualBitmap L.control hN ht hSmall hWord hDesc hControl hSpill hTableFit
    hOut hInput hInputSep hCRTable hReq
  obtain ⟨hSupport, hVector⟩ := hintResidual_input S sch lr x J t r hx hZ
  have hBits (i : Fin (S.data sch.N t).R) :
      bitAt state.mem E.W 0 (layout.offset + i.val) =
        if (S.data sch.N t).H (crInput sch.N residual) i = 1 then 1 else 0 := by
    apply hintBitAt_aligned state.mem E.W A.residual _ i hWidth
    intro q hq
    rw [← hVector]
    exact hPacked q hq
  apply Sem.mono (hintCRNode_correct S P E state layout sch.N t base switchBase other act
    (crInput sch.N residual) hPre hSupport hPc hArg hBits hFresh hSelect hEntry hAt)
  rintro k out ⟨hk, hc, hFrame, hb⟩
  refine ⟨hk, hc, ?_, hFrame⟩
  intro a ha
  change out.mem (layout.destination + (⟨a, ha⟩ : Fin sch.N).val) = hintTruth (a ∈ residual)
  rw [hb ⟨a, ha⟩]
  change (if a ∈ residual then (1 : ZMod 2) else 0).val = hintTruth (a ∈ residual)
  by_cases h : a ∈ residual
  · rw [if_pos h, hintTruth, if_pos h]
    decide
  · rw [if_neg h, hintTruth, if_neg h]
    decide

theorem hintCorrectEstimate_placed (S : CRSourceBundle) (H : HintParams) (L : HintDecoderPlacement)
    (node descriptor base : ℕ) (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState)
    (hInfo : (L.info node).universeSize = sch.N)
    (hWord : 1 < 2 ^ E.W) (hDesc : descriptor + 2 < 2 ^ E.W)
    (hResult : (L.arena node).result < 2 ^ E.W)
    (hResid : (L.arena node).residualBitmap < 2 ^ E.W)
    (hSize : sch.N < 2 ^ E.W)
    (hSep : (L.arena node).result + sch.N ≤ (L.arena node).residualBitmap)
    (hEnd : (L.arena node).residualBitmap + sch.N ≤ 2 ^ E.W)
    (hRecord : (hintEventRecord S H L (.correctEstimate node)).At E descriptor)
    (hArg : state.regs 6 = descriptor)
    (hEst : HintBitmap state.mem (L.arena node).result sch.N (sch.exactEstimate lr x J))
    (hError : HintBitmap state.mem (L.arena node).residualBitmap sch.N
      (symmDiff x (sch.exactEstimate lr x J)))
    (hAt : At P base (hintColumnAddAction.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 20) state (fun k out =>
      k ≤ 11 * sch.N + 11 ∧ out.regs 14 = state.regs 14 ∧
      HintBitmap out.mem (L.arena node).result sch.N x ∧
      CRMemFrame (L.arena node).result ((L.arena node).result + sch.N) state.mem out.mem) := by
  have hBlock : (hintColumnAddBlock (L.arena node).result (L.arena node).residualBitmap sch.N).At E descriptor := by
    simpa only [hintEventRecord, hInfo] using hRecord
  have hTable := HintColumnAddTable.of_block E descriptor (L.arena node).result (L.arena node).residualBitmap
    sch.N hBlock hWord hDesc hResult hResid (by omega) hEnd hSize
  apply Sem.mono (hintAddBitmaps_sem P E state descriptor (L.arena node).result (L.arena node).residualBitmap
    sch.N base _ _ hTable hArg hEst hError (Or.inl hSep) hAt hPc)
  rintro k out ⟨hk, hc, hb, hf⟩
  rw [hintPlusResidual] at hb
  exact ⟨hk, hc, hb, hf⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintUpdate_prefix_step
#print axioms LinearSetReconciliation327.Main.hintResidualDecode_placed
#print axioms LinearSetReconciliation327.Main.hintCorrectEstimate_placed
end S_HintPlacedResidual20261120
section S_HintResidualTailPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def HintDecoderPhase.single {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables}
    {E : RAMEnv} {header first time : ℕ} {A B : (ℕ → ℕ) → Prop}
    (before : ∀ m v, A m → A (Function.update m (D.control + 2) v))
    (after : ∀ m v, B m → B (Function.update m (D.control + 2) v))
    (step : ∀ j : Fin D.events.length, j.val = first → HintEventStep S H D E header j time A B) :
    HintDecoderPhase S H D E header first 1 A B := by
  let inv := fun i m => if i = 0 then A m else B m
  refine ⟨fun _ => time, inv, ?_, ?_, ?_, ?_⟩
  · intro m
    simp [inv]
  · intro m
    simp [inv]
  · intro i m v h
    by_cases hi : i = 0
    · simpa only [inv, if_pos hi] using before m v (by simpa only [inv, if_pos hi] using h)
    · simpa only [inv, if_neg hi] using after m v (by simpa only [inv, if_neg hi] using h)
  · intro i hi j hj
    have he : i = 0 := by omega
    subst i
    have h := step j (by simpa only [Nat.add_zero] using hj)
    simpa only [inv, if_true, Nat.zero_add, Nat.one_ne_zero, if_false] using h

def HintMemoryWords {M : ℕ} (W base : ℕ) (y : Fin M → ZMod 2) (m : ℕ → ℕ) : Prop :=
  ∀ q < wordsOf W M, m (base + q) = packMem W y q

def HintFreshWords (base count : ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ a < count, m (base + a) = 0

theorem HintBitmap.update_below {m : ℕ → ℕ} {base N : ℕ} {X : Finset ℕ}
    (h : HintBitmap m base N X) (index value : ℕ) (hLow : index < base) :
    HintBitmap (Function.update m index value) base N X := by
  intro a ha
  rw [Function.update_of_ne (by omega : base + a ≠ index)]
  exact h a ha

theorem HintMemoryWords.update_below {M W base : ℕ} {m : ℕ → ℕ} {y : Fin M → ZMod 2}
    (h : HintMemoryWords W base y m) (index value : ℕ) (hLow : index < base) :
    HintMemoryWords W base y (Function.update m index value) := by
  intro a ha
  rw [Function.update_of_ne (by omega : base + a ≠ index)]
  exact h a ha

theorem HintFreshWords.update_below {m : ℕ → ℕ} {base count : ℕ}
    (h : HintFreshWords base count m) (index value : ℕ) (hLow : index < base) :
    HintFreshWords base count (Function.update m index value) := by
  intro a ha
  rw [Function.update_of_ne (by omega : base + a ≠ index)]
  exact h a ha

noncomputable def hintResidualSyndrome (S : CRSourceBundle) (N t : ℕ) (x estimate : Finset ℕ) :
    Fin (synLen (crFamily S) (.cr N t)) → ZMod 2 :=
  hintSketchVector (crFamily S) (.cr N t) () x + hintSketchVector (crFamily S) (.cr N t) () estimate

noncomputable def hintResidualDecode_phase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header node first t : ℕ) (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (E : RAMEnv) (keep : (ℕ → ℕ) → Prop)
    (hControl : D.placement.control = D.control)
    (hWidth : E.W = D.placement.width) (hW : 0 < E.W)
    (hx : x ⊆ Finset.range sch.N) (hZ : sch.Z lr x J ≤ t)
    (hN : 1 ≤ sch.N) (ht : t ≤ sch.N) (hWord : 11 < 2 ^ E.W)
    (hEvent : D.events[first]? = some (.decodeResidual node sch.N t)) :
    let L := D.placement
    let A := L.arena node
    let w := (S.data sch.N t).W
    let spill := A.crRegisters + 16
    let spillSize := 2 ^ (w + 1) + 1
    let spillEnd := spill + spillSize + crSourceSteps S sch.N t + 1
    let estimate := sch.exactEstimate lr x J
    let err := symmDiff x estimate
    D.control + 2 < A.result →
    A.result + sch.N ≤ A.residual →
    A.result + sch.N ≤ A.residualBitmap →
    A.residualBitmap + sch.N < A.crRegisters →
    spillEnd < 2 ^ E.W →
    w + 1 < E.W →
    L.crTable node + 2 ^ w < 2 ^ E.W →
    A.residual * E.W + (S.data sch.N t).R < 2 ^ E.W →
    (A.residual * E.W + (S.data sch.N t).R) / E.W < spill →
    (hintCRTableBlock w (S.data sch.N t).det).At E (L.crTable node) →
    (∀ p : Fin D.events.length, p.val = first →
      hintEventDescriptor header D.events (hintEventRecord S H L) p.val + 11 < 2 ^ E.W) →
    (∀ m m', CRMemFrame A.residualBitmap spillEnd m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first 1
      (fun m => HintBitmap m A.result sch.N estimate ∧
        HintMemoryWords E.W A.residual (hintResidualSyndrome S sch.N t x estimate) m ∧
        HintFreshWords spill spillSize m ∧ keep m)
      (fun m => HintBitmap m A.result sch.N estimate ∧ HintBitmap m A.residualBitmap sch.N err ∧ keep m) := by
  let L := D.placement
  let A := L.arena node
  let w := (S.data sch.N t).W
  let spill := A.crRegisters + 16
  let spillSize := 2 ^ (w + 1) + 1
  let spillEnd := spill + spillSize + crSourceSteps S sch.N t + 1
  dsimp only
  intro hCtrl hPayload hBefore hOut hEnd hSM hTable hIn hInSep hCRTable hDesc hKeep hCursor
  change D.control + 2 < A.result at hCtrl
  change A.result + sch.N ≤ A.residual at hPayload
  change A.result + sch.N ≤ A.residualBitmap at hBefore
  change A.residualBitmap + sch.N < A.crRegisters at hOut
  change spillEnd < 2 ^ E.W at hEnd
  have hPow : 0 < 2 ^ (w + 1) := Nat.two_pow_pos _
  have hSpillAfter : A.crRegisters < spillEnd := by dsimp [spillEnd, spill, spillSize]; omega
  have hControlWord : L.control < 2 ^ E.W := by
    change D.placement.control < 2 ^ E.W
    rw [hControl]
    omega
  have hCtrlP : D.control + 2 < A.residual := by omega
  have hCtrlB : D.control + 2 < A.residualBitmap := by omega
  have hCtrlSpill : D.control + 2 < spill := by
    change D.control + 2 < A.crRegisters + 16
    omega
  apply HintDecoderPhase.single (time := hintCRNodeBudget S sch.N t)
  · rintro m v ⟨hb, hp, hf, hk⟩
    exact ⟨hb.update_below _ _ hCtrl, hp.update_below _ _ hCtrlP,
      hf.update_below _ _ hCtrlSpill, hCursor _ _ hk⟩
  · rintro m v ⟨hb, he, hk⟩
    exact ⟨hb.update_below _ _ hCtrl, he.update_below _ _ hCtrlB, hCursor _ _ hk⟩
  · intro pos hPos act base state
    dsimp only
    intro hSelect hEntry hAt hPc hArg hCtx _ hStart hRec
    have hOpt : D.events[pos.val]? = some (.decodeResidual node sch.N t) := by
      rw [hPos]
      exact hEvent
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans hOpt)
    have hTag : D.events[pos.val].tag = 6 := by rw [hEq]; rfl
    rw [hTag] at hSelect hEntry
    rw [hEq] at hRec
    obtain ⟨hEst, hPacked, hFresh, hK⟩ := hStart
    let descriptor := hintEventDescriptor header D.events (hintEventRecord S H L) pos.val
    have hRec' : (hintCREventBlock S L node (A.residual * L.width) A.residualBitmap sch.N t).At E
        descriptor := hRec
    have hRun := hintResidualDecode_placed S L node descriptor t base 75 sch lr x J
      (hintNativeProgram S) E state hintNativeOtherActions act hWidth hW hx hZ hN ht hWord
      (hDesc pos hPos) hSM hControlWord hEnd hTable hOut hIn hInSep hCRTable hRec'
      (fun a ha => hFresh a (Nat.lt_succ_of_le ha)) hPc hArg hSelect hEntry hAt hPacked
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hb, hf⟩
    have hf' : ∀ a, (a < A.residualBitmap ∨ A.residualBitmap + sch.N < a) →
        (a < A.crRegisters ∨ spillEnd ≤ a) → out.mem a = state.mem a := hf
    have frame : CRMemFrame A.residualBitmap spillEnd state.mem out.mem := by
      intro a ha
      rcases ha with h | h
      · exact hf' a (Or.inl h) (Or.inl (h.trans (by omega)))
      · exact hf' a (Or.inr (by omega)) (Or.inr h)
    refine ⟨hk, ⟨?_, hb, hKeep _ _ frame hK⟩, hc.trans hControl, ?_⟩
    · intro q hq
      have hBeforeBit : A.result + q < A.residualBitmap := by omega
      rw [frame _ (Or.inl hBeforeBit)]
      exact hEst q hq
    · intro a _ ha
      exact frame a (Or.inl (by omega))

noncomputable def hintCorrectEstimate_phase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header node first : ℕ) (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (E : RAMEnv) (keep : (ℕ → ℕ) → Prop)
    (hInfo : (D.placement.info node).universeSize = sch.N)
    (hEvent : D.events[first]? = some (.correctEstimate node)) :
    let A := D.placement.arena node
    let estimate := sch.exactEstimate lr x J
    1 < 2 ^ E.W →
    D.control + 2 < A.result →
    A.result < 2 ^ E.W →
    A.residualBitmap < 2 ^ E.W →
    sch.N < 2 ^ E.W →
    A.result + sch.N ≤ A.residualBitmap →
    A.residualBitmap + sch.N ≤ 2 ^ E.W →
    (∀ p : Fin D.events.length, p.val = first →
      hintEventDescriptor header D.events (hintEventRecord S H D.placement) p.val + 2 < 2 ^ E.W) →
    (∀ m m', CRMemFrame A.result (A.result + sch.N) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first 1
      (fun m => HintBitmap m A.result sch.N estimate ∧
        HintBitmap m A.residualBitmap sch.N (symmDiff x estimate) ∧ keep m)
      (fun m => HintBitmap m A.result sch.N x ∧ keep m) := by
  let A := D.placement.arena node
  dsimp only
  intro hWord hCtrl hDest hSource hSize hSep hEnd hDescriptor hKeep hCursor
  have hCtrlSrc : D.control + 2 < A.residualBitmap := by
    change D.control + 2 < A.result at hCtrl
    change A.result + sch.N ≤ A.residualBitmap at hSep
    omega
  apply HintDecoderPhase.single (time := 11 * sch.N + 11)
  · rintro m v ⟨hE, hR, hk⟩
    exact ⟨hE.update_below _ _ hCtrl, hR.update_below _ _ hCtrlSrc, hCursor _ _ hk⟩
  · rintro m v ⟨hX, hk⟩
    exact ⟨hX.update_below _ _ hCtrl, hCursor _ _ hk⟩
  · intro pos hPos act base state
    dsimp only
    intro hSelect _ hAt hPc hArg hCtx _ hPre hRec
    have hOpt : D.events[pos.val]? = some (.correctEstimate node) := by
      rw [hPos]
      exact hEvent
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans hOpt)
    have hTag : D.events[pos.val].tag = 5 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintColumnAddAction := (Option.some.inj hSelect).symm
    subst act
    rw [hEq] at hRec
    obtain ⟨hE, hR, hk⟩ := hPre
    have hRun := hintCorrectEstimate_placed S H D.placement node _ base sch lr x J (hintNativeProgram S)
      E state hInfo hWord (hDescriptor pos hPos) hDest hSource hSize hSep hEnd hRec hArg hE hR hAt hPc
    change Sem (hintNativeProgram S) E base (base + 20) state _
    apply Sem.mono hRun
    rintro k out ⟨ht, hc, hX, hf⟩
    exact ⟨ht, ⟨hX, hKeep _ _ hf hk⟩, hc.trans hCtx,
      fun a _ ha => hf a (Or.inl (ha.trans_lt hCtrl))⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintResidualDecode_phase
#print axioms LinearSetReconciliation327.Main.hintCorrectEstimate_phase
end S_HintResidualTailPhase20261120
section S_HintDecoderArenaFit20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintArenaFor_limit (S : CRSourceBundle) (H : HintParams) (W : ℕ)
    (info : HintNodeInfo) (start : ℕ) :
    (hintArenaFor S H W info start).limit = start + (hintArenaFor S H W info 0).limit := by
  unfold hintArenaFor
  cases hr : info.rowParams with
  | none =>
    by_cases hc : (info.isCR || info.rowParams.isSome) = true <;>
      simp only [hr, hc, if_true, if_false, hintNodeArena, Nat.zero_add, Nat.add_assoc]
  | some a =>
    obtain ⟨X, Y⟩ := a
    by_cases hc : (info.isCR || info.rowParams.isSome) = true <;>
      simp only [hr, hc, if_true, if_false, hintNodeArena, Nat.zero_add, Nat.add_assoc]

theorem hintFoldMax_ge (xs : List ℕ) (base value : ℕ) (h : value ∈ xs ∨ value ≤ base) :
    value ≤ xs.foldl max base := by
  induction xs generalizing base with
  | nil =>
      simpa using h
  | cons a rest ih =>
      simp only [List.foldl_cons]
      apply ih
      rcases h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr (le_max_right _ _)
        · exact Or.inl h
      · exact Or.inr (h.trans (le_max_left _ _))

theorem hintRowWorkspace_pivot_bound (start a K BY node row steps h : ℕ) (ha : a ≤ steps) :
    (hintRowWorkspace start a K BY node row steps h).gauss.pivotRow + a ≤
      start + ((hintRowWorkspace 0 steps K BY 0 0 steps K).gauss.pivotRow + steps) := by
  have hSquare : a * a ≤ steps * steps := Nat.mul_le_mul ha ha
  have hRectangle : K * a ≤ K * steps := Nat.mul_le_mul_left K ha
  dsimp only [hintRowWorkspace, hintGaussDenseArea]
  omega

theorem hintDecoderTables_arena_fits (S : CRSourceBundle) (H : HintParams)
    {T : Node} (hT : IsSchemeTree H T) (W Bc header : ℕ) :
    let D := hintDecoderTables S H hT W Bc header
    ∀ node : Fin D.infos.length,
      (D.placement.arena node.val).limit ≤ hintArenaStart D.heap D.stride node.val + D.stride := by
  dsimp only
  let D := hintDecoderTables S H hT W Bc header
  intro node
  have hInfo : D.placement.info node.val = D.infos[node.val] := by
    change D.infos[node.val]?.getD _ = _
    rw [List.getElem?_eq_getElem node.isLt, Option.getD_some]
  change (hintArenaFor S H W (D.placement.info node.val) (hintArenaStart D.heap D.stride node.val)).limit ≤ _
  rw [hintArenaFor_limit, hInfo]
  apply Nat.add_le_add_left
  apply hintFoldMax_ge
  exact Or.inl (List.mem_map.mpr ⟨D.infos[node.val], List.getElem_mem node.isLt, rfl⟩)

theorem hintDecoderTables_arena_separate (S : CRSourceBundle) (H : HintParams)
    {T : Node} (hT : IsSchemeTree H T) (W Bc header : ℕ) :
    let D := hintDecoderTables S H hT W Bc header
    ∀ i j : Fin D.infos.length, i.val < j.val →
      (D.placement.arena i.val).limit ≤ (D.placement.arena j.val).payload := by
  dsimp only
  let D := hintDecoderTables S H hT W Bc header
  intro i j hij
  have hFits := hintDecoderTables_arena_fits S H hT W Bc header i
  have hStart := hintArenaStart_disjoint D.heap D.stride i.val j.val hij
  have hPayload (info : HintNodeInfo) (base : ℕ) :
      (hintArenaFor S H W info base).payload = base := by
    unfold hintArenaFor
    cases info.rowParams <;> cases h : (info.isCR || info.rowParams.isSome) <;> rfl
  change (D.placement.arena i.val).limit ≤
    (hintArenaFor S H W (D.placement.info j.val) (hintArenaStart D.heap D.stride j.val)).payload
  rw [hPayload]
  exact hFits.trans hStart

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_arena_fits
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_arena_separate
end S_HintDecoderArenaFit20261120


