-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_11Part1
-- name    : LinearSetReconciliation327_Main_B65_11Part1
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T14:14:45.881211+00:00
-- url     : https://prove2.me/theorems/1fa388d1-1aeb-5286-9493-d08d085bcbbc
-- title:
--   Theorem 6.5 supporting machine proof B65_11Part1
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_09
import Definitions.Def_LinearSetReconciliation327_Main_B65_10
set_option autoImplicit false

section S_HintPredictBinaryRows20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintTranscriptBinary (sch : RowScheme) (base limit : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ (j : Fin sch.m) (s : Fin sch.ℓ), s.val < limit → mem (hintTranscriptCell base sch.m j.val s.val) < 2

def HintBinaryMemory (mem : ℕ → ℕ) (base count : ℕ) : Prop :=
  ∀ a < count, mem (base + a) < 2

noncomputable def hintPredictBinaryRows_phase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header N X Y node child seed first : ℕ) (lr : (H.scheme N X Y).LocalSeed)
    (J : Finset ℕ) (col : Fin (H.scheme N X Y).ℓ) (keep : (ℕ → ℕ) → Prop)
    (hInfoN : (D.placement.info node).universeSize = N)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
    (hChild : (D.placement.info node).children[col.val]? = some child)
    (hControl : D.placement.control = D.control)
    (hMap : ∀ q < H.rows X Y, D.events[first + q]? = some (.predict node seed col.val q))
    (hm : H.rows X Y ≤ N)
    (hSteps : 0 < H.ell N X Y) (hWord : 30 < 2 ^ E.W)
    (hSeedFit : seed < 2 ^ E.W) (hKFit : H.Nmax N X Y < 2 ^ E.W)
    (hStepsFit : H.ell N X Y < 2 ^ E.W) (hBXFit : H.BX N X Y < 2 ^ E.W)
    (hBYFit : H.BY N X Y + 1 < 2 ^ E.W)
    (hCoeffSpace : H.rows X Y * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ E.W)
    (hCoeff : ∀ (j : Fin (H.rows X Y)) (q : Fin (H.Nmax N X Y)) (s : Fin (H.ell N X Y)),
      E.coeff seed (j.val * H.ell N X Y * H.Nmax N X Y + q.val + s.val * H.Nmax N X Y) =
        (lr.2 j s q).val)
    (hPerm : ∀ i : Fin N, E.permInv seed i.val = (lr.1.symm i).val) :
    let sch := H.scheme N X Y
    let A := D.placement.arena node
    let start := D.placement.rowScratch
    let scratchEnd := hintPredictScratchEnd H start N X Y col.val
    let dest := A.transcript + col.val * sch.m
    let abstention := (D.placement.arena child).hints
    let ready := fun m => HintBitmap m A.hints N J ∧
      HintTranscriptBinary sch A.transcript col.val m ∧ keep m
    D.control + 2 < start →
    D.control + 2 < A.transcript →
    scratchEnd < 2 ^ E.W →
    scratchEnd ≤ A.transcript →
    A.transcript + sch.ℓ * sch.m ≤ A.hints →
    A.hints + N ≤ abstention →
    abstention + sch.m ≤ 2 ^ E.W →
    (∀ j : Fin (H.rows X Y),
      let threshold := D.placement.threshold node j.val
      let block := hintWaitDetBlock (H.Nmax N X Y) (rowLen N (H.rows X Y) j.val)
        (H.BY N X Y) (H.ell N X Y) (H.c N X Y)
      block.At E threshold ∧ threshold + block.length ≤ 2 ^ E.W) →
    (∀ p : Fin D.events.length, first ≤ p.val → p.val < first + sch.m →
      hintEventDescriptor header D.events (hintEventRecord S H D.placement) p.val + 31 ≤ 2 ^ E.W) →
    (∀ m m', (∀ a, (a < start ∨ scratchEnd ≤ a) →
      (a < dest ∨ dest + sch.m ≤ a) → (a < abstention ∨ abstention + sch.m ≤ a) →
        m' a = m a) → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first sch.m ready
      (fun m => ready m ∧ HintBinaryMemory m dest sch.m ∧ HintBinaryMemory m abstention sch.m) := by
  let sch := H.scheme N X Y
  let A := D.placement.arena node
  let start := D.placement.rowScratch
  let scratchEnd := hintPredictScratchEnd H start N X Y col.val
  let dest := A.transcript + col.val * sch.m
  let abstention := (D.placement.arena child).hints
  let ready := fun m => HintBitmap m A.hints N J ∧
    HintTranscriptBinary sch A.transcript col.val m ∧ keep m
  let writes := fun i (m : ℕ → ℕ) => ∀ j < min i sch.m, m (dest + j) < 2 ∧ m (abstention + j) < 2
  let inv := fun i m => ready m ∧ writes i m
  let budget := fun j =>
    let h := (hintRowMembers N sch.m j lr.1 J).length
    let Nj := rowLen N sch.m j
    let w := hintRowWorkspace start col.val (H.Nmax N X Y) (H.BY N X Y) seed j sch.ℓ h
    hintPredictCallCost w.gauss Nj (min (H.BY N X Y) (Nj - h))
  dsimp only
  intro hCtrlStart hCtrlTran hSpace hScratch hTran hHint hAbstain hThreshold hDescriptors hKeep hCursor
  change D.control + 2 < A.transcript at hCtrlTran
  change scratchEnd < 2 ^ E.W at hSpace
  change scratchEnd ≤ A.transcript at hScratch
  change A.transcript + sch.ℓ * sch.m ≤ A.hints at hTran
  change A.hints + N ≤ abstention at hHint
  change abstention + sch.m ≤ 2 ^ E.W at hAbstain
  have hCol := Nat.mul_le_mul_right sch.m col.isLt
  change (col.val + 1) * sch.m ≤ sch.ℓ * sch.m at hCol
  rw [Nat.add_mul, Nat.one_mul] at hCol
  have hTranscriptDest : A.transcript ≤ dest := by dsimp only [dest]; omega
  have hDestEnd : dest + sch.m ≤ A.hints := by dsimp only [dest]; omega
  have hCtrlWord : D.placement.control < 2 ^ E.W := by rw [hControl]; omega
  have hHintCursor : D.control + 2 < A.hints := by omega
  refine ⟨budget, inv, ?_, ?_, ?_, ?_⟩
  · intro m
    exact ⟨And.left, fun h => ⟨h, fun j hj => (Nat.not_lt_zero j ((Nat.lt_min.mp hj).1)).elim⟩⟩
  · intro m
    change ready m ∧ writes sch.m m ↔ _
    unfold writes
    rw [min_self]
    constructor
    · rintro ⟨hr, hp⟩
      exact ⟨hr, fun j hj => (hp j hj).1, fun j hj => (hp j hj).2⟩
    · rintro ⟨hr, hp, ha⟩
      exact ⟨hr, fun j hj => ⟨hp j hj, ha j hj⟩⟩
  · rintro i m v ⟨⟨hJ, hT, hK⟩, hPred⟩
    refine ⟨⟨hJ.update_below _ _ hHintCursor, ?_, hCursor _ _ hK⟩, ?_⟩
    · intro j s hs
      rw [Function.update_of_ne (by unfold hintTranscriptCell; omega :
        hintTranscriptCell A.transcript sch.m j.val s.val ≠ D.control + 2)]
      exact hT j s hs
    · intro j hj
      rw [Function.update_of_ne (by omega : dest + j ≠ D.control + 2),
        Function.update_of_ne (by omega : abstention + j ≠ D.control + 2)]
      exact hPred j hj
  · intro i hi pos hPos act base state
    dsimp only
    intro hSelect _ hAt hPc hArg hCtx _ hInv hRecord
    let j : Fin (H.rows X Y) := ⟨i, hi⟩
    have hEv := (List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans
      (by rw [hPos]; exact hMap i hi : D.events[pos.val]? = some (.predict node seed col.val i))
    have hEq := Option.some.inj hEv
    have hTag : D.events[pos.val].tag = 2 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintRunPredict := (Option.some.inj hSelect).symm
    subst act
    obtain ⟨⟨hJ, hT, hK⟩, hPrev⟩ := hInv
    rw [hEq] at hRecord
    let desc := hintEventDescriptor header D.events (hintEventRecord S H D.placement) pos.val
    have hBlock : (hintRowEventBlock H D.placement node seed j.val col.val dest abstention).At E desc := by
      simp only [hintEventRecord, hInfoXY, Option.getD_some, hChild] at hRecord
      exact hRecord
    have hBound := hDescriptors pos (by omega) (by omega)
    have hCoeffAddr : (j.val + 1) * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ E.W :=
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ j.isLt)).trans hCoeffSpace
    have hReadSpan : A.transcript + j.val + col.val * sch.m ≤ 2 ^ E.W := by
      let jr : Fin sch.m := j
      have ho := hintPairOffset_lt col jr
      change col.val * sch.m + j.val < sch.ℓ * sch.m at ho
      omega
    have hHintFit : A.hints + N ≤ 2 ^ E.W := by omega
    have hDestAfter : scratchEnd ≤ dest := hScratch.trans hTranscriptDest
    have hAbstainAfter : scratchEnd ≤ abstention := by omega
    have hDestFit : dest + sch.m ≤ 2 ^ E.W := by omega
    have hDisjoint : dest + sch.m ≤ abstention := by omega
    have hObs (a : ℕ) (ha : a < col.val) :
        state.mem (A.transcript + j.val + a * sch.m) < 2 := by
      rw [Nat.add_right_comm A.transcript j.val (a * sch.m)]
      exact hT j ⟨a, ha.trans col.isLt⟩ ha
    have hRun := hintPredictPlaced_binary_step H D.placement N X Y node seed desc base dest abstention j col lr J
      (hintNativeProgram S) E state hInfoN hInfoXY hAt hPc hArg (hCtx.trans hControl.symm) hm hSteps hWord
      hBound hCtrlWord hSeedFit hKFit hStepsFit hBXFit hBYFit hCoeffAddr (hCoeff j) hPerm
      (hintRowLen_le_Nmax H N X Y j) hBlock (hThreshold j).1 (fun a => hJ a.val a.isLt) hObs
      hSpace hScratch hReadSpan hTran hHintFit hDestAfter hAbstainAfter hDestFit hAbstain
      (Or.inl hDisjoint) (hThreshold j).2
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hp, ha, hf⟩
    change (∀ a, (a < start ∨ scratchEnd ≤ a) →
      a ≠ dest + j.val → a ≠ abstention + j.val → out.mem a = state.mem a) at hf
    have hRows : writes (i + 1) out.mem := by
      intro q hq
      have hq' := Nat.lt_min.mp hq
      change out.mem (dest + j.val) < 2 at hp
      change out.mem (abstention + j.val) < 2 at ha
      have hj : j.val = i := rfl
      by_cases hEq : q = i
      · rw [hEq, ← hj]
        exact ⟨hp, ha⟩
      · have hPast : q < min i sch.m := Nat.lt_min.mpr ⟨by omega, hq'.2⟩
        have hOld := hPrev q hPast
        have hP : out.mem (dest + q) = state.mem (dest + q) :=
          hf _ (Or.inr (by omega)) (by omega) (by omega)
        have hA : out.mem (abstention + q) = state.mem (abstention + q) :=
          hf _ (Or.inr (by omega)) (by omega) (by omega)
        rw [hP, hA]
        exact hOld
    have hFrame (a : ℕ) (hs : a < start ∨ scratchEnd ≤ a)
        (hd : a < dest ∨ dest + sch.m ≤ a) (ha : a < abstention ∨ abstention + sch.m ≤ a) :
        out.mem a = state.mem a := by
      have hj : j.val < sch.m := j.isLt
      exact hf a hs (by rcases hd with h | h <;> omega) (by rcases ha with h | h <;> omega)
    refine ⟨hk, ⟨⟨?_, ?_, hKeep _ _ hFrame hK⟩, hRows⟩, hc.trans hControl, ?_⟩
    · intro q hq
      rw [hFrame _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))]
      exact hJ q hq
    · intro j' s hs
      have hb := hintTranscriptCell_beforeColumn sch A.transcript j' s col.val hs
      change hintTranscriptCell A.transcript sch.m j'.val s.val < dest at hb
      have hAfter : A.transcript ≤ hintTranscriptCell A.transcript sch.m j'.val s.val := by
        unfold hintTranscriptCell
        omega
      rw [hFrame _ (Or.inr (by omega)) (Or.inl hb) (Or.inl (by omega))]
      exact hT j' s hs
    · intro a _ ha
      exact hFrame a (Or.inl (ha.trans_lt hCtrlStart)) (Or.inl (by omega)) (Or.inl (by omega))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPredictBinaryRows_phase
end S_HintPredictBinaryRows20261120
section S_HintArbitraryInput20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintBitmap_of_binary (mem : ℕ → ℕ) (base N : ℕ)
    (hBits : ∀ i < N, mem (base + i) = 0 ∨ mem (base + i) = 1) :
    ∃ S : Finset ℕ, S ⊆ Finset.range N ∧ HintBitmap mem base N S := by
  let S := (Finset.range N).filter fun i => mem (base + i) = 1
  refine ⟨S, Finset.filter_subset _ _, ?_⟩
  intro i hi
  have hS : i ∈ S ↔ mem (base + i) = 1 := by
    simp [S, hi]
  rw [hintTruth, hS]
  rcases hBits i hi with h | h <;> simp [h]

theorem hintStageAction_total (P : Program) (E : RAMEnv) (state : RAMState)
    (descriptor dest offset count base : ℕ) (hTable : HintUnpackTable E descriptor dest offset count)
    (hArg : state.regs 6 = descriptor) (pre : HintStagePre E E.W count offset dest)
    (hFresh : ∀ a < wordsOf E.W count, state.mem (dest + a) = 0)
    (hAt : At P base (hintStageAction.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 28) state (fun k out => k ≤ 17 * count + 13 ∧
      out.regs 14 = state.regs 14 ∧
      (∃ y : Fin count → ZMod 2, ∀ a < wordsOf E.W count, out.mem (dest + a) = packMem E.W y a) ∧
      CRMemFrame dest (dest + wordsOf E.W count) state.mem out.mem) := by
  let y : Fin count → ZMod 2 := fun i =>
    if bitAt state.mem E.W 0 (offset + i.val) = 1 then 1 else 0
  have hBit (i : Fin count) :
      bitAt state.mem E.W 0 (offset + i.val) = if y i = 1 then 1 else 0 := by
    have hBound : bitAt state.mem E.W 0 (offset + i.val) < 2 := by
      unfold bitAt
      exact Nat.mod_lt _ (by decide)
    by_cases h : bitAt state.mem E.W 0 (offset + i.val) = 1
    · simp [y, h]
    · have hz : bitAt state.mem E.W 0 (offset + i.val) = 0 := by omega
      simp [y, hz]
  apply Sem.mono (hintStageAction_sem P E state descriptor dest offset count base hTable hArg pre
    y hBit hFresh hAt hPc)
  rintro k out ⟨hk, hc, hOut, hf⟩
  exact ⟨hk, hc, ⟨y, hOut⟩, hf⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintBitmap_of_binary
#print axioms LinearSetReconciliation327.Main.hintStageAction_total
end S_HintArbitraryInput20261120
section S_HintBinaryResidualPrefix20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintPackedMemory (W base count : ℕ) (m : ℕ → ℕ) : Prop :=
  ∃ y : Fin count → ZMod 2, HintMemoryWords W base y m

theorem HintPackedMemory.update_below {W base count : ℕ} {m : ℕ → ℕ}
    (h : HintPackedMemory W base count m) (v : ℕ) {a : ℕ} (ha : a < base) :
    HintPackedMemory W base count (Function.update m a v) := by
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy.update_below _ _ ha⟩

theorem HintBinaryMemory.update_below {m : ℕ → ℕ} {base count a : ℕ}
    (h : HintBinaryMemory m base count) (v : ℕ) (ha : a < base) :
    HintBinaryMemory (Function.update m a v) base count := by
  intro q hq
  rw [Function.update_of_ne (by omega : base + q ≠ a)]
  exact h q hq

theorem HintBinaryMemory.of_bitmap {m : ℕ → ℕ} {base count : ℕ} {x : Finset ℕ}
    (h : HintBitmap m base count x) : HintBinaryMemory m base count := by
  intro q hq
  rw [h q hq]
  unfold hintTruth
  split <;> decide

theorem HintBinaryMemory.to_bitmap {m : ℕ → ℕ} {base count : ℕ}
    (h : HintBinaryMemory m base count) : ∃ x : Finset ℕ, x ⊆ Finset.range count ∧ HintBitmap m base count x :=
  hintBitmap_of_binary m base count fun q hq => by
    have hb := h q hq
    change m (base + q) < 2 at hb
    omega

noncomputable def hintResidualCopy_total (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header node first t offset : ℕ) (N : ℕ)
    (E : RAMEnv) (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = D.placement.width) (hWord : 2 < 2 ^ E.W)
    (hEvent : D.events[first]? = some (.residualCopy node offset (S.data N t).R)) :
    let L := D.placement
    let A := L.arena node
    let count := (S.data N t).R
    let words := wordsOf E.W count
    D.control + 2 < A.result →
    A.result + N ≤ A.residual →
    A.residual < 2 ^ E.W →
    HintStagePre E E.W count offset A.residual →
    (∀ pos : Fin D.events.length, pos.val = first →
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 3 < 2 ^ E.W) →
    (∀ m m', CRMemFrame A.residual (A.residual + words) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first 1
      (fun m => HintBinaryMemory m A.result N ∧ HintFreshWords A.residual words m ∧ keep m)
      (fun m => HintBinaryMemory m A.result N ∧
        HintPackedMemory E.W A.residual count m ∧ keep m) := by
  let L := D.placement
  let A := L.arena node
  let count := (S.data N t).R
  let words := wordsOf E.W count
  dsimp only
  intro hControl hSeparate hAddress hPre hDescriptor hKeep hCursor
  change D.control + 2 < A.result at hControl
  change A.result + N ≤ A.residual at hSeparate
  have hCtrl : D.control + 2 < A.residual := by omega
  apply HintDecoderPhase.single (time := 17 * count + 13)
  · rintro m v ⟨he, hf, hk⟩
    exact ⟨he.update_below _ hControl, hf.update_below _ _ hCtrl, hCursor _ _ hk⟩
  · rintro m v ⟨he, hp, hk⟩
    exact ⟨he.update_below _ hControl, hp.update_below _ hCtrl, hCursor _ _ hk⟩
  · intro pos hPos act base state
    dsimp only
    intro hSelect _ hAt hPc hArg hCtx _ hInv hRecord
    have hEvent' : D.events[pos.val]? = some (.residualCopy node offset count) := by
      rw [hPos]
      exact hEvent
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans hEvent')
    have hTag : D.events[pos.val].tag = 1 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintStageAction := (Option.some.inj hSelect).symm
    subst act
    rw [hEq] at hRecord
    obtain ⟨hEst, hFresh, hK⟩ := hInv
    let desc := hintEventDescriptor header D.events (hintEventRecord S H L) pos.val
    have hSlot : (hintUnpackDetBlock A.residual offset E.W count).At E desc := by
      rw [hWidth]
      exact hRecord
    have hTable := HintUnpackTable.of_block E desc A.residual offset count hSlot hWord
      (hDescriptor pos hPos) hAddress (lt_of_le_of_lt (Nat.le_add_right _ _) hPre.input_span)
      (lt_of_le_of_lt (Nat.le_add_left _ _) hPre.input_span)
    have hRun := hintStageAction_total (hintNativeProgram S) E state desc A.residual offset count base
      hTable hArg hPre hFresh hAt hPc
    change Sem (hintNativeProgram S) E base (base + 28) state _
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hp, hf⟩
    have hFrame : CRMemFrame A.residual (A.residual + words) state.mem out.mem := hf
    refine ⟨hk, ⟨?_, hp, hKeep _ _ hFrame hK⟩, hc.trans hCtx, ?_⟩
    · intro q hq
      rw [hFrame (A.result + q) (Or.inl (by omega))]
      exact hEst q hq
    · intro a _ ha
      exact hFrame a (Or.inl (ha.trans_lt hCtrl))

noncomputable def hintResidualToggle_total (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
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
    D.control + 2 < A.result →
    A.result + N ≤ A.residual →
    A.residual + (words + 2) ≤ 2 ^ E.W →
    detBase + 3 < 2 ^ E.W →
    E.det (detBase + 3) = D.control →
    UpSavedLayout E detBase items →
    E.det (detBase % 2 ^ E.W) % 2 ^ E.W = items.length →
    (∀ i < N, UpLocalTree CR (upShiftDetEnv E detBase) i Bc colBase leaf () 0 0 0) →
    (∀ p : Fin D.events.length, first ≤ p.val → p.val < first + N →
      hintEventDescriptor header D.events (hintEventRecord S H L) p.val + 3 < 2 ^ E.W) →
    (∀ m m', CRMemFrame A.residual (A.residual + words + 2) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first N
      (fun m => HintBinaryMemory m A.result N ∧ HintPackedMemory E.W A.residual (synLen CR leaf) m ∧ keep m)
      (fun m => HintBinaryMemory m A.result N ∧
        HintPackedMemory E.W A.residual (synLen CR leaf) m ∧ keep m) := by
  let L := D.placement
  let A := L.arena node
  let CR := crFamily S
  let leaf := Node.cr N t
  let words := wordsOf E.W (synLen CR leaf)
  let colBase := hintSubtreeColBase Bc leaf
  let items := hintChildUpdateSchedule CR Bc colBase leaf 0 words
  let detBase := L.residualTable node
  let inv := fun m => HintBinaryMemory m A.result N ∧
    HintPackedMemory E.W A.residual (synLen CR leaf) m ∧ keep m
  dsimp only
  intro hCtrl hBefore hPay hDet hReturn hLayout hCount hLocal hDescriptor hKeep hCursor
  change D.control + 2 < A.result at hCtrl
  change A.result + N ≤ A.residual at hBefore
  change A.residual + (words + 2) ≤ 2 ^ E.W at hPay
  have hPayFit : A.residual < 2 ^ E.W := by omega
  have hCtrlWord : D.control < 2 ^ E.W := by omega
  have hCtrlPay : D.control + 2 < A.residual := by omega
  refine ⟨fun _ => 147 * items.length + 24, fun _ => inv, fun _ => Iff.rfl, fun _ => Iff.rfl, ?_, ?_⟩
  · rintro i m v ⟨he, hp, hk⟩
    exact ⟨he.update_below _ hCtrl, hp.update_below _ hCtrlPay, hCursor _ _ hk⟩
  · intro i hi pos hPos act base state
    dsimp only
    intro hSelect _ hAt hPc hArg _ hWState hInv hRec
    have hEvent' : D.events[pos.val]? = some (.residualToggle node i) := by
      rw [hPos]
      exact hEvent i hi
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans hEvent')
    have hTag : D.events[pos.val].tag = 4 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintToggleGateAction := (Option.some.inj hSelect).symm
    subst act
    rw [hEq] at hRec
    obtain ⟨hEst, hPacked, hK⟩ := hInv
    let coord : Fin leaf.N := ⟨i, hi⟩
    let desc := hintEventDescriptor header D.events (hintEventRecord S H L) pos.val
    have hOrd : A.result + i < 2 ^ E.W := by omega
    have hCoord : i < 2 ^ E.W := hi.trans_le hSize
    have hTable := HintToggleGateTable.of_block E desc (A.result + i) i detBase A.residual D.control
      hRec (by omega) (hDescriptor pos (by omega) (by omega)) hDet hOrd hCoord hPayFit hCtrlWord hReturn
    have hRoom : UpSaveRoom words words leaf := by
      change words + 2 * 0 ≤ words
      simp
    obtain ⟨initial, hY⟩ := hPacked
    let est := if state.mem (A.result + i) = 1 then {i} else (∅ : Finset ℕ)
    have hPast : est ∩ Finset.range i = ∅ := by
      ext q
      by_cases h : state.mem (A.result + i) = 1
      · simp only [est, if_pos h, Finset.mem_inter, Finset.mem_singleton, Finset.mem_range, Finset.notMem_empty, iff_false]
        exact fun ⟨he, hq⟩ => (Nat.ne_of_lt hq) he
      · simp [est, h]
    have hInit : HintMemoryWords E.W A.residual
        (initial + hintSketchVector CR leaf () (est ∩ Finset.range i)) state.mem := by
      rw [hPast, hintSketchVector_empty CR leaf (() : leaf.Seed), add_zero]
      exact hY
    have hGate : state.mem (A.result + i) = hintTruth (i ∈ est) := by
      have hb := hEst i hi
      change state.mem (A.result + i) < 2 at hb
      by_cases h : state.mem (A.result + i) = 1
      · simp [est, hintTruth, h]
      · have hz : state.mem (A.result + i) = 0 := by omega
        simp [est, hintTruth, h, hz]
    have hRun := hintUpdate_prefix_step CR leaf () est initial coord (hintNativeProgram S) E state
      0 base desc (A.result + i) detBase A.residual D.control Bc colBase words words hTable hArg hWState hAt hPc
      hGate hPay le_rfl hWord hSize hInit (hLocal i hi) hRoom hLayout hCount
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hp, hf⟩
    have frame : CRMemFrame A.residual (A.residual + words + 2) state.mem out.mem := by
      intro a ha
      apply hf a
      intro h
      unfold UpTwoRegion at h
      rcases h with h | h <;> omega
    refine ⟨hk, ⟨?_, ⟨_, hp⟩, hKeep _ _ frame hK⟩, hc, ?_⟩
    · intro q hq
      rw [frame (A.result + q) (Or.inl (by omega))]
      exact hEst q hq
    · intro a _ ha
      exact frame a (Or.inl (ha.trans_lt hCtrlPay))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintResidualCopy_total
#print axioms LinearSetReconciliation327.Main.hintResidualToggle_total
end S_HintBinaryResidualPrefix20261120
section S_HintBinaryChild20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintChildCopy_total (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
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
    D.events[first]? = some (.childCopy node col.val childNode offset count) →
    D.control + 2 < dest →
    dest < 2 ^ E.W →
    word * E.W + synLen CR (.recursive sch t Xs Ys children) < 2 ^ E.W →
    dest + words ≤ 2 ^ E.W →
    (word * E.W + synLen CR (.recursive sch t Xs Ys children)) / E.W < dest →
    (∀ pos : Fin D.events.length, pos.val = first →
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 3 < 2 ^ E.W) →
    (∀ m m', CRMemFrame dest (dest + words) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first 1
      (fun m => HintFreshWords dest words m ∧ keep m)
      (fun m => HintPackedMemory E.W dest count m ∧ keep m) := by
  let L := D.placement
  let CR := crFamily S
  let child := children col
  let dest := (L.arena childNode).payload
  let offset := word * E.W + ((List.ofFn fun s => synLen CR (children s)).take col.val).sum
  let count := synLen CR child
  let words := wordsOf E.W count
  dsimp only
  intro hEvent hControl hAddress hInput hDest hSeparate hDescriptor hKeep hCursor
  change D.control + 2 < dest at hControl
  have hPre : HintStagePre E E.W count offset dest :=
    hintStageChild_pre E sch t Xs Ys children col word dest (Nat.lt_trans (by decide) hWord)
      hW hInput hDest hSeparate
  apply HintDecoderPhase.single (time := 17 * count + 13)
  · rintro m v ⟨hf, hk⟩
    exact ⟨hf.update_below _ _ hControl, hCursor _ _ hk⟩
  · rintro m v ⟨hp, hk⟩
    exact ⟨hp.update_below _ hControl, hCursor _ _ hk⟩
  · intro pos hPos act base state
    dsimp only
    intro hSelect _ hAt hPc hArg hCtx _ hInv hRecord
    have hEvent' : D.events[pos.val]? = some (.childCopy node col.val childNode offset count) := by
      rw [hPos]
      exact hEvent
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans hEvent')
    have hTag : D.events[pos.val].tag = 1 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintStageAction := (Option.some.inj hSelect).symm
    subst act
    rw [hEq] at hRecord
    obtain ⟨hFresh, hK⟩ := hInv
    let desc := hintEventDescriptor header D.events (hintEventRecord S H L) pos.val
    have hSlot : (hintUnpackDetBlock dest offset E.W count).At E desc := by
      rw [hWidth]
      exact hRecord
    have hTable := HintUnpackTable.of_block E desc dest offset count hSlot hWord (hDescriptor pos hPos) hAddress
      (lt_of_le_of_lt (Nat.le_add_right _ _) hPre.input_span)
      (lt_of_le_of_lt (Nat.le_add_left _ _) hPre.input_span)
    have hRun := hintStageAction_total (hintNativeProgram S) E state desc dest offset count base
      hTable hArg hPre hFresh hAt hPc
    change Sem (hintNativeProgram S) E base (base + 28) state _
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hp, hf⟩
    exact ⟨hk, ⟨hp, hKeep _ _ hf hK⟩, hc.trans hCtx, fun a _ ha => hf a (Or.inl (ha.trans_lt hControl))⟩

noncomputable def hintChildToggle_total (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
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
    D.control + 2 < gate →
    gate + T.N ≤ dest →
    dest + (sav + 2) ≤ 2 ^ E.W →
    words ≤ workStart → UpSaveRoom workStart sav T →
    detBase + 3 < 2 ^ E.W →
    E.det (detBase + 3) = D.control →
    UpSavedLayout E detBase items →
    E.det (detBase % 2 ^ E.W) % 2 ^ E.W = items.length →
    (∀ i < T.N, UpLocalTree CR (upShiftDetEnv E detBase) i Bc colBase T r seed 0 0) →
    (∀ p : Fin D.events.length, first ≤ p.val → p.val < first + T.N →
      hintEventDescriptor header D.events (hintEventRecord S H L) p.val + 3 < 2 ^ E.W) →
    (∀ m m', CRMemFrame dest (dest + sav + 2) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first T.N
      (fun m => HintBinaryMemory m gate T.N ∧ HintPackedMemory E.W dest (synLen CR T) m ∧ keep m)
      (fun m => HintBinaryMemory m gate T.N ∧
        HintPackedMemory E.W dest (synLen CR T) m ∧ keep m) := by
  let L := D.placement
  let CR := crFamily S
  let gate := (L.arena node).transcript + col * H.rows X Y
  let dest := (L.arena child).payload
  let words := wordsOf E.W (synLen CR T)
  let colBase := hintSubtreeColBase Bc T
  let items := hintChildUpdateSchedule CR Bc colBase T seed sav
  let detBase := L.updateTable child
  let inv := fun m => HintBinaryMemory m gate T.N ∧
    HintPackedMemory E.W dest (synLen CR T) m ∧ keep m
  dsimp only
  intro hCtrl hBefore hPay hGap hRoom hDet hReturn hLayout hCount hLocal hDescriptor hKeep hCursor
  change D.control + 2 < gate at hCtrl
  change gate + T.N ≤ dest at hBefore
  change dest + (sav + 2) ≤ 2 ^ E.W at hPay
  change words ≤ workStart at hGap
  have hPayFit : dest < 2 ^ E.W := by omega
  have hCtrlWord : D.control < 2 ^ E.W := by omega
  have hCtrlPay : D.control + 2 < dest := by omega
  refine ⟨fun _ => 147 * items.length + 24, fun _ => inv, fun _ => Iff.rfl, fun _ => Iff.rfl, ?_, ?_⟩
  · rintro i m v ⟨he, hp, hk⟩
    exact ⟨he.update_below _ hCtrl, hp.update_below _ hCtrlPay, hCursor _ _ hk⟩
  · intro i hi pos hPos act base state
    dsimp only
    intro hSelect _ hAt hPc hArg _ hWState hInv hRec
    have hEvent' : D.events[pos.val]? = some (.childToggle node col child seed i) := by
      rw [hPos]
      exact hEvent i hi
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans hEvent')
    have hTag : D.events[pos.val].tag = 4 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintToggleGateAction := (Option.some.inj hSelect).symm
    subst act
    rw [hEq] at hRec
    obtain ⟨hEst, hPacked, hK⟩ := hInv
    let coord : Fin T.N := ⟨i, hi⟩
    let desc := hintEventDescriptor header D.events (hintEventRecord S H L) pos.val
    have hOrd : gate + i < 2 ^ E.W := by omega
    have hCoord : i < 2 ^ E.W := hi.trans_le hSize
    have hRecord : (hintGateBlock (gate + i) i detBase dest).At E desc := by
      simpa only [hintEventRecord, hInfoXY, Option.getD_some] using hRec
    have hTable := HintToggleGateTable.of_block E desc (gate + i) i detBase dest D.control
      hRecord (by omega) (hDescriptor pos (by omega) (by omega)) hDet hOrd hCoord hPayFit hCtrlWord hReturn
    obtain ⟨initial, hY⟩ := hPacked
    let selected := if state.mem (gate + i) = 1 then {i} else (∅ : Finset ℕ)
    have hPast : selected ∩ Finset.range i = ∅ := by
      ext q
      by_cases h : state.mem (gate + i) = 1
      · simp only [selected, if_pos h, Finset.mem_inter, Finset.mem_singleton, Finset.mem_range, Finset.notMem_empty, iff_false]
        exact fun ⟨he, hq⟩ => (Nat.ne_of_lt hq) he
      · simp [selected, h]
    have hInit : HintMemoryWords E.W dest
        (initial + hintSketchVector CR T r (selected ∩ Finset.range i)) state.mem := by
      rw [hPast, hintSketchVector_empty CR T r, add_zero]
      exact hY
    have hGate : state.mem (gate + i) = hintTruth (i ∈ selected) := by
      have hb := hEst i hi
      change state.mem (gate + i) < 2 at hb
      by_cases h : state.mem (gate + i) = 1
      · simp [selected, hintTruth, h]
      · have hz : state.mem (gate + i) = 0 := by omega
        simp [selected, hintTruth, h, hz]
    have hRun := hintUpdate_prefix_step CR T r selected initial coord (hintNativeProgram S) E state
      seed base desc (gate + i) detBase dest D.control Bc colBase workStart sav hTable hArg hWState hAt hPc
      hGate hPay hGap hWord hSize hInit (hLocal i hi) hRoom hLayout hCount
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hp, hf⟩
    have frame : CRMemFrame dest (dest + sav + 2) state.mem out.mem := by
      intro a ha
      apply hf a
      intro h
      unfold UpTwoRegion at h
      have hWork : workStart ≤ sav := Nat.le_trans (Nat.le_add_right _ _) hRoom
      rcases h with h | h <;> omega
    refine ⟨hk, ⟨?_, ⟨_, hp⟩, hKeep _ _ frame hK⟩, hc, ?_⟩
    · intro q hq
      rw [frame (gate + q) (Or.inl (by omega))]
      exact hEst q hq
    · intro a _ ha
      exact frame a (Or.inl (ha.trans_lt hCtrlPay))

noncomputable def hintRecoverColumn_total (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node child first N X Y : ℕ)
    (col : Fin (H.scheme N X Y).ℓ) (keep : (ℕ → ℕ) → Prop)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
    (hEvent : D.events[first]? = some (.recoverColumn node col.val child)) :
    let L := D.placement
    let sch := H.scheme N X Y
    let transcript := (L.arena node).transcript
    let dest := transcript + col.val * sch.m
    let source := (L.arena child).result
    1 < 2 ^ E.W →
    D.control + 2 < transcript →
    D.control + 2 < source →
    dest < 2 ^ E.W →
    source < 2 ^ E.W →
    sch.m < 2 ^ E.W →
    dest + sch.m ≤ 2 ^ E.W →
    source + sch.m ≤ 2 ^ E.W →
    (dest + sch.m ≤ source ∨ source + sch.m ≤ dest) →
    (∀ pos : Fin D.events.length, pos.val = first →
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 2 < 2 ^ E.W) →
    (∀ m m', CRMemFrame dest (dest + sch.m) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first 1
      (fun m => HintTranscriptBinary sch transcript col.val m ∧
        HintBinaryMemory m dest sch.m ∧
        HintBinaryMemory m source sch.m ∧ keep m)
      (fun m => HintTranscriptBinary sch transcript (col.val + 1) m ∧ keep m) := by
  let L := D.placement
  let sch := H.scheme N X Y
  let transcript := (L.arena node).transcript
  let dest := transcript + col.val * sch.m
  let source := (L.arena child).result
  dsimp only
  intro hWord hCtrl hCtrlSrc hDest hSource hSize hDestEnd hSourceEnd hSep hDescriptor hKeep hCursor
  change D.control + 2 < transcript at hCtrl
  have hCtrlDest : D.control + 2 < dest := by dsimp only [dest]; omega
  have hCursorTranscript (cols : ℕ) (m : ℕ → ℕ) (v : ℕ)
      (hm : HintTranscriptBinary sch transcript cols m) :
      HintTranscriptBinary sch transcript cols (Function.update m (D.control + 2) v) := by
    intro j s hs
    rw [Function.update_of_ne (by unfold hintTranscriptCell; omega :
      hintTranscriptCell transcript sch.m j.val s.val ≠ D.control + 2)]
    exact hm j s hs
  apply HintDecoderPhase.single (time := 11 * sch.m + 11)
  · rintro m v ⟨ht, hp, hx, hk⟩
    exact ⟨hCursorTranscript _ _ _ ht, hp.update_below _ hCtrlDest, hx.update_below _ hCtrlSrc, hCursor _ _ hk⟩
  · rintro m v ⟨ht, hk⟩
    exact ⟨hCursorTranscript _ _ _ ht, hCursor _ _ hk⟩
  · intro pos hPos act base state
    dsimp only
    intro hSelect _ hAt hPc hArg hCtx _ hInv hRecord
    have hEvent' : D.events[pos.val]? = some (.recoverColumn node col.val child) := by
      rw [hPos]
      exact hEvent
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans hEvent')
    have hTag : D.events[pos.val].tag = 5 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintColumnAddAction := (Option.some.inj hSelect).symm
    subst act
    rw [hEq] at hRecord
    obtain ⟨hT, hP, hX, hK⟩ := hInv
    let desc := hintEventDescriptor header D.events (hintEventRecord S H L) pos.val
    have hBlock : (hintColumnAddBlock dest source sch.m).At E desc := by
      simp only [hintEventRecord, hInfoXY, Option.getD_some] at hRecord
      exact hRecord
    let table := HintColumnAddTable.of_block E desc dest source sch.m hBlock hWord
      (hDescriptor pos hPos) hDest hSource hDestEnd hSourceEnd hSize
    obtain ⟨prediction, _, hPrediction⟩ := hP.to_bitmap
    obtain ⟨decoded, _, hDecoded⟩ := hX.to_bitmap
    have hRun := hintAddBitmaps_sem (hintNativeProgram S) E state desc dest source sch.m base
      prediction decoded table hArg hPrediction hDecoded hSep hAt hPc
    change Sem (hintNativeProgram S) E base (base + 20) state _
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hb, hf⟩
    have hAfter : HintTranscriptBinary sch transcript (col.val + 1) out.mem := by
      intro j s hs
      by_cases h : s = col
      · subst s
        exact HintBinaryMemory.of_bitmap hb j.val j.isLt
      · have hNe : s.val ≠ col.val := fun hEq => h (Fin.ext hEq)
        have hLt : s.val < col.val := by omega
        rw [hf _ (Or.inl (hintTranscriptCell_beforeColumn sch transcript j s col.val hLt))]
        exact hT j s hLt
    exact ⟨hk, ⟨hAfter, hKeep _ _ hf hK⟩, hc.trans hCtx, fun a _ ha => hf a (Or.inl (ha.trans_lt hCtrlDest))⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintChildCopy_total
#print axioms LinearSetReconciliation327.Main.hintChildToggle_total
#print axioms LinearSetReconciliation327.Main.hintRecoverColumn_total
end S_HintBinaryChild20261120
section S_HintBinaryLeafAt20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintStoreAt_total (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node first word N : ℕ) (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = D.placement.width) (hWord : 2 < 2 ^ E.W)
    (hEvent : D.events[first]? = some (.store node (word * E.W) N)) :
    let A := D.placement.arena node
    D.control + 2 < A.result →
    A.result < 2 ^ E.W →
    word * E.W < 2 ^ E.W →
    HintUnpackPre E A.result (word * E.W) N →
    (∀ pos : Fin D.events.length, pos.val = first →
      hintEventDescriptor header D.events (hintEventRecord S H D.placement) pos.val + 3 < 2 ^ E.W) →
    (D.control + 2 < word ∨ word + wordsOf E.W N ≤ D.control + 2) →
    (∀ m m', CRMemFrame A.result (A.result + N) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first 1
      keep
      (fun m => (∀ q < N, m (A.result + q) < 2) ∧ keep m) := by
  let A := D.placement.arena node
  dsimp only
  intro hCtrl hDest hOffset hPre hDescriptor hInputFrame hKeep hCursor
  change D.control + 2 < A.result at hCtrl
  apply HintDecoderPhase.single (time := 12 * N + 12)
  · exact hCursor
  · rintro m v ⟨hb, hk⟩
    refine ⟨?_, hCursor m v hk⟩
    intro a ha
    rw [Function.update_of_ne (by omega : A.result + a ≠ D.control + 2)]
    exact hb a ha
  · intro pos hPos act base state
    dsimp only
    intro hSelect _ hAt hPc hArg hCtx _ hInv hRecord
    have he : D.events[pos.val]? = some (.store node (word * E.W) N) := by
      rw [hPos]
      exact hEvent
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans he)
    have hTag : D.events[pos.val].tag = 0 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintUnpackAction := (Option.some.inj hSelect).symm
    subst act
    rw [hEq] at hRecord
    let desc := hintEventDescriptor header D.events (hintEventRecord S H D.placement) pos.val
    have hBlock : (hintUnpackDetBlock A.result (word * E.W) E.W N).At E desc := by
      change (hintUnpackDetBlock A.result (word * E.W) D.placement.width N).At E desc at hRecord
      rw [← hWidth] at hRecord
      exact hRecord
    have hTable := HintUnpackTable.of_block E desc A.result (word * E.W) N hBlock hWord
      (hDescriptor pos hPos) hDest hOffset hPre.count_fit
    have hRun := hintUnpackAction_sem (hintNativeProgram S) E state desc A.result (word * E.W) N base
      hTable hArg hPre hAt hPc
    change Sem (hintNativeProgram S) E base (base + 22) state _
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hb, hf⟩
    refine ⟨hk, ⟨?_, hKeep _ _ hf hInv⟩, hc.trans hCtx, fun a _ ha => hf a (Or.inl (ha.trans_lt hCtrl))⟩
    intro i hi
    rw [hb i hi]
    unfold bitAt
    exact Nat.mod_lt _ (by decide)

noncomputable def hintCRAt_total (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node first word N t : ℕ) (keep : (ℕ → ℕ) → Prop)
    (hControl : D.placement.control = D.control)
    (hWidth : E.W = D.placement.width) (hW : 0 < E.W)
    (hN : 1 ≤ N) (ht : t ≤ N)
    (hWord : 11 < 2 ^ E.W) (hEvent : D.events[first]? = some (.decodeLeaf node (word * E.W) N t)) :
    let L := D.placement
    let A := L.arena node
    let data := S.data N t
    let spill := A.crRegisters + 16
    let spillSize := 2 ^ (data.W + 1) + 1
    let spillEnd := spill + spillSize + crSourceSteps S N t + 1
    D.control + 2 < A.result →
    A.result + N < A.crRegisters →
    spillEnd < 2 ^ E.W →
    data.W + 1 < E.W →
    L.crTable node + 2 ^ data.W < 2 ^ E.W →
    word * E.W + data.R < 2 ^ E.W →
    (word * E.W + data.R) / E.W < spill →
    (hintCRTableBlock data.W data.det).At E (L.crTable node) →
    (∀ pos : Fin D.events.length, pos.val = first →
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 11 < 2 ^ E.W) →
    (D.control + 2 < word ∨ word + wordsOf E.W data.R ≤ D.control + 2) →
    (∀ m m', CRMemFrame A.result spillEnd m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first 1
      (fun m => HintFreshWords spill spillSize m ∧ keep m)
      (fun m => (∀ q < N, m (A.result + q) < 2) ∧ keep m) := by
  let L := D.placement
  let A := L.arena node
  let data := S.data N t
  let spill := A.crRegisters + 16
  let spillSize := 2 ^ (data.W + 1) + 1
  let spillEnd := spill + spillSize + crSourceSteps S N t + 1
  dsimp only
  intro hCtrl hOut hSpill hSmall hTable hInput hSep hCRTable hDescriptor hInputFrame hKeep hCursor
  change D.control + 2 < A.result at hCtrl
  change A.result + N < A.crRegisters at hOut
  change spillEnd < 2 ^ E.W at hSpill
  change (D.control + 2 < word ∨ word + wordsOf E.W data.R ≤ D.control + 2) at hInputFrame
  have hCtrlSpill : D.control + 2 < spill := by dsimp only [spill]; omega
  have hRegEnd : A.crRegisters < spillEnd := by
    dsimp only [spillEnd, spill]
    exact (Nat.lt_add_of_pos_right (by decide : 0 < 16)).trans_le
      ((Nat.le_add_right _ spillSize).trans ((Nat.le_add_right _ (crSourceSteps S N t)).trans (Nat.le_add_right _ 1)))
  have hCtrlWord : L.control < 2 ^ E.W := by change D.placement.control < _; rw [hControl]; omega
  apply HintDecoderPhase.single (time := hintCRNodeBudget S N t)
  · rintro m v ⟨hf, hk⟩
    exact ⟨hf.update_below _ _ hCtrlSpill, hCursor _ _ hk⟩
  · rintro m v ⟨hb, hk⟩
    refine ⟨?_, hCursor m v hk⟩
    intro a ha
    rw [Function.update_of_ne (by omega : A.result + a ≠ D.control + 2)]
    exact hb a ha
  · intro pos hPos act base state
    dsimp only
    intro hSelect hEntry hAt hPc hArg _ _ hInv hRecord
    have he : D.events[pos.val]? = some (.decodeLeaf node (word * E.W) N t) := by
      rw [hPos]
      exact hEvent
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans he)
    have hTag : D.events[pos.val].tag = hintNativeOtherActions.length := by rw [hEq]; rfl
    rw [hTag] at hSelect hEntry
    rw [hEq] at hRecord
    obtain ⟨hFresh, hK⟩ := hInv
    let desc := hintEventDescriptor header D.events (hintEventRecord S H L) pos.val
    let area := hintCRArea data.W (word * E.W) A.crRegisters (L.crTable node) desc A.result L.control
    have hBlock : (hintCREventBlock S L node (word * E.W) A.result N t).At E desc := hRecord
    have hReq : (hintCRCallBlock area E.W data.W data.R (crSourceSteps S N t) N).At E desc := by
      rw [hintCREventBlock_descriptor S L node _ _ _ _ desc] at hBlock
      simpa only [area, A, hWidth] using hBlock
    have hEnd : spill + 2 ^ (data.W + 1) + 1 + crSourceSteps S N t + 1 < 2 ^ E.W := by
      simpa only [spillEnd, spillSize, Nat.add_assoc] using hSpill
    have hPre := hintCRArea_pre S E N t (word * E.W) A.crRegisters (L.crTable node)
      desc A.result L.control hN ht hSmall hWord (hDescriptor pos hPos) hCtrlWord hEnd hTable
      hOut hInput hSep hCRTable hReq
    have hRun := hintCRNode_total S (hintNativeProgram S) E state area N t base 75 hintNativeOtherActions act
      hPre hPc hArg
      (fun a ha => hFresh a (Nat.lt_succ_of_le ha)) hSelect hEntry hAt
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hf, hb⟩
    have hFrame (a : ℕ) (ha : a < A.result ∨ spillEnd ≤ a) : out.mem a = state.mem a := by
      change (∀ q, (q < A.result ∨ A.result + N < q) →
        (q < A.crRegisters ∨ spillEnd ≤ q) → out.mem q = state.mem q) at hf
      rcases ha with h | h
      · exact hf a (Or.inl h) (Or.inl (by omega))
      · exact hf a (Or.inr (by omega)) (Or.inr h)
    refine ⟨hk, ⟨?_, hKeep _ _ hFrame hK⟩, hc.trans hControl, fun a _ ha => hFrame a (Or.inl (ha.trans_lt hCtrl))⟩
    intro i hi
    exact (hb i hi).elim (fun h => h ▸ (by decide : 0 < 2)) (fun h => h ▸ (by decide : 1 < 2))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintStoreAt_total
#print axioms LinearSetReconciliation327.Main.hintCRAt_total
end S_HintBinaryLeafAt20261120
section S_HintBinaryResidualTail20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintResidualDecode_total (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
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
    D.control + 2 < A.result →
    A.result + N ≤ A.residual →
    A.result + N ≤ A.residualBitmap →
    A.residualBitmap + N < A.crRegisters →
    spillEnd < 2 ^ E.W →
    w + 1 < E.W →
    L.crTable node + 2 ^ w < 2 ^ E.W →
    A.residual * E.W + (S.data N t).R < 2 ^ E.W →
    (A.residual * E.W + (S.data N t).R) / E.W < spill →
    (hintCRTableBlock w (S.data N t).det).At E (L.crTable node) →
    (∀ p : Fin D.events.length, p.val = first →
      hintEventDescriptor header D.events (hintEventRecord S H L) p.val + 11 < 2 ^ E.W) →
    (∀ m m', CRMemFrame A.residualBitmap spillEnd m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first 1
      (fun m => HintBinaryMemory m A.result N ∧
        HintFreshWords spill spillSize m ∧ keep m)
      (fun m => HintBinaryMemory m A.result N ∧ HintBinaryMemory m A.residualBitmap N ∧ keep m) := by
  let L := D.placement
  let A := L.arena node
  let w := (S.data N t).W
  let spill := A.crRegisters + 16
  let spillSize := 2 ^ (w + 1) + 1
  let spillEnd := spill + spillSize + crSourceSteps S N t + 1
  dsimp only
  intro hCtrl hPayload hBefore hOut hEnd hSM hTable hIn hInSep hCRTable hDesc hKeep hCursor
  change D.control + 2 < A.result at hCtrl
  change A.result + N ≤ A.residual at hPayload
  change A.result + N ≤ A.residualBitmap at hBefore
  change A.residualBitmap + N < A.crRegisters at hOut
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
  apply HintDecoderPhase.single (time := hintCRNodeBudget S N t)
  · rintro m v ⟨hb, hf, hk⟩
    exact ⟨hb.update_below _ hCtrl,
      hf.update_below _ _ hCtrlSpill, hCursor _ _ hk⟩
  · rintro m v ⟨hb, he, hk⟩
    exact ⟨hb.update_below _ hCtrl, he.update_below _ hCtrlB, hCursor _ _ hk⟩
  · intro pos hPos act base state
    dsimp only
    intro hSelect hEntry hAt hPc hArg hCtx _ hStart hRec
    have hOpt : D.events[pos.val]? = some (.decodeResidual node N t) := by
      rw [hPos]
      exact hEvent
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans hOpt)
    have hTag : D.events[pos.val].tag = 6 := by rw [hEq]; rfl
    rw [hTag] at hSelect hEntry
    rw [hEq] at hRec
    obtain ⟨hEst, hFresh, hK⟩ := hStart
    let descriptor := hintEventDescriptor header D.events (hintEventRecord S H L) pos.val
    have hRec' : (hintCREventBlock S L node (A.residual * L.width) A.residualBitmap N t).At E
        descriptor := hRec
    let data := S.data N t
    let area := hintCRArea data.W (A.residual * E.W) A.crRegisters (L.crTable node) descriptor A.residualBitmap L.control
    have hReq : (hintCRCallBlock area E.W data.W data.R (crSourceSteps S N t) N).At E descriptor := by
      rw [hintCREventBlock_descriptor S L node _ _ _ _ descriptor] at hRec'
      have hWidth' : L.width = E.W := hWidth.symm
      simpa only [area, A, data, hWidth'] using hRec'
    have hSpillBound : spill + 2 ^ (data.W + 1) + 1 + crSourceSteps S N t + 1 < 2 ^ E.W := by
      simpa only [spillEnd, spillSize, w, data, Nat.add_assoc] using hEnd
    have hPre := hintCRArea_pre S E N t (A.residual * E.W) A.crRegisters (L.crTable node)
      descriptor A.residualBitmap L.control hN ht hSM hWord (hDesc pos hPos) hControlWord hSpillBound hTable
      hOut hIn hInSep hCRTable hReq
    have hRun := hintCRNode_total S (hintNativeProgram S) E state area N t base 75 hintNativeOtherActions act
      hPre hPc hArg (fun a ha => hFresh a (Nat.lt_succ_of_le ha)) hSelect hEntry hAt
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hf, hb⟩
    have hBinary : HintBinaryMemory out.mem A.residualBitmap N := by
      intro q hq
      have he : area.destination = A.residualBitmap := rfl
      have hBit := hb q hq
      rw [he] at hBit
      change out.mem (A.residualBitmap + q) < 2
      omega
    have hf' : ∀ a, (a < A.residualBitmap ∨ A.residualBitmap + N < a) →
        (a < A.crRegisters ∨ spillEnd ≤ a) → out.mem a = state.mem a := hf
    have frame : CRMemFrame A.residualBitmap spillEnd state.mem out.mem := by
      intro a ha
      rcases ha with h | h
      · exact hf' a (Or.inl h) (Or.inl (h.trans (by omega)))
      · exact hf' a (Or.inr (by omega)) (Or.inr h)
    refine ⟨hk, ⟨?_, hBinary, hKeep _ _ frame hK⟩, hc.trans hControl, ?_⟩
    · intro q hq
      have hBeforeBit : A.result + q < A.residualBitmap := by omega
      rw [frame _ (Or.inl hBeforeBit)]
      exact hEst q hq
    · intro a _ ha
      exact frame a (Or.inl (by omega))

noncomputable def hintCorrectEstimate_total (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header node first : ℕ) (N : ℕ)
    (E : RAMEnv) (keep : (ℕ → ℕ) → Prop)
    (hInfo : (D.placement.info node).universeSize = N)
    (hEvent : D.events[first]? = some (.correctEstimate node)) :
    let A := D.placement.arena node
    1 < 2 ^ E.W →
    D.control + 2 < A.result →
    A.result < 2 ^ E.W →
    A.residualBitmap < 2 ^ E.W →
    N < 2 ^ E.W →
    A.result + N ≤ A.residualBitmap →
    A.residualBitmap + N ≤ 2 ^ E.W →
    (∀ p : Fin D.events.length, p.val = first →
      hintEventDescriptor header D.events (hintEventRecord S H D.placement) p.val + 2 < 2 ^ E.W) →
    (∀ m m', CRMemFrame A.result (A.result + N) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first 1
      (fun m => HintBinaryMemory m A.result N ∧
        HintBinaryMemory m A.residualBitmap N ∧ keep m)
      (fun m => HintBinaryMemory m A.result N ∧ keep m) := by
  let A := D.placement.arena node
  dsimp only
  intro hWord hCtrl hDest hSource hSize hSep hEnd hDescriptor hKeep hCursor
  have hCtrlSrc : D.control + 2 < A.residualBitmap := by
    change D.control + 2 < A.result at hCtrl
    change A.result + N ≤ A.residualBitmap at hSep
    omega
  apply HintDecoderPhase.single (time := 11 * N + 11)
  · rintro m v ⟨hE, hR, hk⟩
    exact ⟨hE.update_below _ hCtrl, hR.update_below _ hCtrlSrc, hCursor _ _ hk⟩
  · rintro m v ⟨hX, hk⟩
    exact ⟨hX.update_below _ hCtrl, hCursor _ _ hk⟩
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
    obtain ⟨estimate, _, hEstimate⟩ := hE.to_bitmap
    obtain ⟨err, _, hError⟩ := hR.to_bitmap
    let descriptor := hintEventDescriptor header D.events (hintEventRecord S H D.placement) pos.val
    have hBlock : (hintColumnAddBlock A.result A.residualBitmap N).At E descriptor := by
      simpa only [hintEventRecord, hInfo] using hRec
    have hTable := HintColumnAddTable.of_block E descriptor A.result A.residualBitmap N
      hBlock hWord (hDescriptor pos hPos) hDest hSource (hSep.trans hSource.le) hEnd hSize
    have hRun := hintAddBitmaps_sem (hintNativeProgram S) E state descriptor A.result A.residualBitmap N base
      estimate err hTable hArg hEstimate hError (Or.inl hSep) hAt hPc
    change Sem (hintNativeProgram S) E base (base + 20) state _
    apply Sem.mono hRun
    rintro k out ⟨ht, hc, hX, hf⟩
    exact ⟨ht, ⟨HintBinaryMemory.of_bitmap hX, hKeep _ _ hf hk⟩, hc.trans hCtx,
      fun a _ ha => hf a (Or.inl (ha.trans_lt hCtrl))⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintResidualDecode_total
#print axioms LinearSetReconciliation327.Main.hintCorrectEstimate_total
end S_HintBinaryResidualTail20261120
section S_HintDirectSchedule20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintDirectReads (sch : RowScheme) (node offset : ℕ) : List HintTreeEvent :=
  (List.ofFn fun j : Fin sch.m => (List.range sch.ℓ).map fun s =>
    HintTreeEvent.directBit node j.val s (offset + j.val * sch.ℓ + s)).flatten

theorem hintTreeEvents_direct {CR : CRFamily} (payloadOffset : ℕ → ℕ)
    (sch : RowScheme) (t node seedIndex offset : ℕ) :
    hintTreeEvents CR payloadOffset (.direct sch t) node seedIndex offset =
      hintDirectReads sch node offset ++
        (List.range sch.m).map (.finishRow node seedIndex) ++
        hintResidualEvents CR node (offset + sch.m * sch.ℓ) sch.N t := by
  rw [hintTreeEvents]
  rfl

theorem hintDirectReads_length (sch : RowScheme) (node offset : ℕ) :
    (hintDirectReads sch node offset).length = sch.m * sch.ℓ := by
  unfold hintDirectReads
  rw [length_flatten_ofFn]
  simp

theorem hintDirectReads_at (sch : RowScheme) (node offset : ℕ)
    (j : Fin sch.m) (s : Fin sch.ℓ) :
    (hintDirectReads sch node offset)[j.val * sch.ℓ + s.val]? =
      some (.directBit node j.val s.val (offset + j.val * sch.ℓ + s.val)) := by
  let row : Fin sch.m → List HintTreeEvent := fun i =>
    (List.range sch.ℓ).map fun c => .directBit node i.val c (offset + i.val * sch.ℓ + c)
  have hLen (i : Fin sch.m) : (row i).length = sch.ℓ := by simp [row]
  have hAt := getElem?_flatten_ofFn' sch.m row j s.val (by rw [hLen]; exact s.isLt)
  have hBefore : ((List.ofFn fun i => (row i).length).take j.val).sum = j.val * sch.ℓ := by
    rw [take_sum_ofFn_eq_sum_fin _ j.isLt.le]
    simp [hLen]
  rw [hBefore] at hAt
  change (List.ofFn row).flatten[j.val * sch.ℓ + s.val]? = _
  rw [hAt]
  have hInside : s.val < (List.range sch.ℓ).length := by simpa using s.isLt
  simp [row, List.getElem?_map, List.getElem?_eq_getElem hInside]

theorem hintDirectReads_split {sch : RowScheme} (i : Fin (sch.m * sch.ℓ)) :
    ∃ j : Fin sch.m, ∃ s : Fin sch.ℓ, i.val = j.val * sch.ℓ + s.val := by
  let js := finProdFinEquiv.symm i
  refine ⟨js.1, js.2, ?_⟩
  have h := congrArg Fin.val (Equiv.apply_symm_apply finProdFinEquiv i)
  change js.2.val + sch.ℓ * js.1.val = i.val at h
  rw [Nat.mul_comm sch.ℓ, Nat.add_comm] at h
  exact h.symm

theorem hintTranscript_read_step (sch : RowScheme) (r : sch.LocalSeed) (x : Finset ℕ)
    (transcript : ℕ) (before after : ℕ → ℕ) (j : Fin sch.m) (s : Fin sch.ℓ)
    (hPrev : HintTranscriptCorrect sch r x transcript
      (fun j' s' => j'.val * sch.ℓ + s'.val < j.val * sch.ℓ + s.val) before)
    (hNew : after (hintTranscriptCell transcript sch.m j.val s.val) =
       (sch.code j (r.2 j) (sch.rowOf r x j) s).val)
    (hFrame : CRMemFrame (hintTranscriptCell transcript sch.m j.val s.val)
      (hintTranscriptCell transcript sch.m j.val s.val + 1) before after) :
    HintTranscriptCorrect sch r x transcript
      (fun j' s' => j'.val * sch.ℓ + s'.val < j.val * sch.ℓ + s.val + 1) after := by
  have hWrite := hintTranscript_write sch r x transcript _ before after j s hPrev hNew hFrame
  intro j' s' hRead
  apply hWrite j' s'
  by_cases hEq : j'.val * sch.ℓ + s'.val = j.val * sch.ℓ + s.val
  · have hCell : hintTranscriptCell 0 sch.ℓ s'.val j'.val =
        hintTranscriptCell 0 sch.ℓ s.val j.val := by
      simpa only [hintTranscriptCell, Nat.zero_add] using hEq
    obtain ⟨hs, hj⟩ := (hintTranscriptCell_eq_iff 0 s' s j' j).mp hCell
    exact Or.inr ⟨hj, hs⟩
  · exact Or.inl (by omega)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectReads_at
#print axioms LinearSetReconciliation327.Main.hintTranscript_read_step
end S_HintDirectSchedule20261120


