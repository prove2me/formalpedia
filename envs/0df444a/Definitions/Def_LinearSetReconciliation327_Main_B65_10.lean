-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_10
-- name    : LinearSetReconciliation327_Main_B65_10
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T14:13:10.468837+00:00
-- url     : https://prove2.me/theorems/c24b7932-3bb9-5d16-909f-c85ae3db17dd
-- title:
--   Theorem 6.5 supporting machine proof B65_10
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_10Part1
set_option autoImplicit false

section S_HintFinishRowExact20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintEstimateRows (sch : RowScheme) (r : sch.LocalSeed) (x J : Finset ℕ)
    (output : ℕ) (done : ℕ → Prop) (mem : ℕ → ℕ) : Prop :=
  ∀ i : Fin sch.N, done ((r.1 i).val % sch.m) →
    mem (output + i.val) = hintTruth (i.val ∈ sch.exactEstimate r x J)

theorem hintEstimateRows_write (sch : RowScheme) (r : sch.LocalSeed) (x J : Finset ℕ)
    (output row scratchEnd : ℕ) (done : ℕ → Prop) (before after : ℕ → ℕ)
    (hSpace : scratchEnd ≤ output)
    (hPrev : HintEstimateRows sch r x J output done before)
    (hNew : ∀ i : Fin sch.N, (r.1 i).val % sch.m = row →
      after (output + i.val) = hintTruth (i.val ∈ sch.exactEstimate r x J))
    (hFrame : ∀ addr ≥ scratchEnd,
      (∀ i : Fin sch.N, (r.1 i).val % sch.m = row → addr ≠ output + i.val) → after addr = before addr) :
    HintEstimateRows sch r x J output (fun n => done n ∨ n = row) after := by
  intro i hi
  by_cases hRow : (r.1 i).val % sch.m = row
  · exact hNew i hRow
  · have hOld := hi.resolve_right hRow
    rw [hFrame _ (by omega)]
    · exact hPrev i hOld
    · intro k hk h
      exact hRow ((show i = k from Fin.ext (by omega)) ▸ hk)

open HintParams in
theorem hintFinishRow_exact (H : HintParams) (N X Y : ℕ)
    (lr : (H.scheme N X Y).LocalSeed) (j : Fin (H.scheme N X Y).m)
    (x J : Finset ℕ) (start node hints hintMap transcript threshold output descriptor control base : ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState)
    (coords : Fin hints → Fin (H.Nmax N X Y))
    (pre : let S := hintRowWorkspace start (H.ell N X Y) (H.Nmax N X Y) (H.BY N X Y)
                  node j.val (H.ell N X Y) hints
           let F := S.fields (rowLen N (H.rows X Y) j.val) (H.rows X Y)
                  hintMap (transcript + j.val) (H.BX N X Y) (H.BY N X Y) threshold output 0
           HintRowCallPre E S.gauss F coords (lr.2 j) (le_refl _) N S.parent lr.1 J)
    (rec : let S := hintRowWorkspace start (H.ell N X Y) (H.Nmax N X Y) (H.BY N X Y)
                  node j.val (H.ell N X Y) hints
           let F := S.fields (rowLen N (H.rows X Y) j.val) (H.rows X Y)
                  hintMap (transcript + j.val) (H.BX N X Y) (H.BY N X Y) threshold output 0
           HintRowRecord E descriptor S.parent (F.value S.gauss))
    (hDesc : state.regs 6 = descriptor) (hCtx : state.regs 14 = control)
    (hControl : control < 2 ^ E.W)
    (hBits : ∀ i : Fin N, state.mem (hintMap + i.val) = hintTruth (i.val ∈ J))
    (hTranscript : HintTranscriptCorrect (H.scheme N X Y) lr x transcript (fun _ _ => True) state.mem)
    (hBY : H.BY N X Y + 1 < 2 ^ E.W)
    (hTableFit : threshold + (H.BY N X Y + 1) * hints < 2 ^ E.W)
    (hOutFit : output < 2 ^ E.W) (hOutSpan : output + N ≤ 2 ^ E.W)
    (hAt : At P base (hintRunFinal.compile base)) (hPc : state.pc = base) :
    let sch := H.scheme N X Y
    let S := hintRowWorkspace start sch.ℓ (H.Nmax N X Y) (H.BY N X Y) node j.val sch.ℓ hints
    let Nj := rowLen N sch.m j.val
    let r := min (H.BY N X Y) (Nj - hints)
    let budget := (hintFinalBudget S.gauss Nj r + 2) * (r + 1) + hintFinalBudget S.gauss Nj r +
      37 * Nj + 9 * sch.ℓ + 18 * hints + 8 * r + 470
    let scratchEnd := S.gauss.pivotRow + sch.ℓ
    scratchEnd ≤ output →
    Sem P E base (base + hintRunFinal.len) state (fun k out =>
      k ≤ budget ∧ out.regs 14 = control ∧
      HintEstimateRows sch lr x J output (· = j.val) out.mem ∧
      (∀ addr, (addr < start ∨ scratchEnd ≤ addr) →
        (∀ i : Fin N, (lr.1 i).val % sch.m = j.val → addr ≠ output + i.val) →
        out.mem addr = state.mem addr)) := by
  let sch := H.scheme N X Y
  let S := hintRowWorkspace start sch.ℓ (H.Nmax N X Y) (H.BY N X Y) node j.val sch.ℓ hints
  let F := S.fields (rowLen N sch.m j.val) sch.m hintMap (transcript + j.val)
    (H.BX N X Y) (H.BY N X Y) threshold output 0
  let v := fun s : Fin sch.ℓ => sch.code j (lr.2 j) (sch.rowOf lr x j) s
  have hObs (s : Fin S.gauss.rows) :
      state.mem (F.transcriptBase + s.val * F.rowCount) = (v s).val := by
    have h := hTranscript j s trivial
    change state.mem (transcript + j.val + s.val * sch.m) = (v s).val
    rw [Nat.add_right_comm]
    exact h
  have hv : List.ofFn v = sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) sch.ℓ :=
    hintTruePrefix_ofFn sch lr x sch.ℓ (le_refl _) j
  dsimp only
  intro hAfter
  have hRun := hintRunFinal_sem S.gauss F coords v (lr.2 j) (le_refl _) N S.parent descriptor control base
    lr.1 J P E state j rfl pre rec hDesc hCtx hControl hBits hObs hBY hTableFit hOutFit hOutSpan
    hAfter hAt hPc
  apply Sem.mono hRun
  rintro k out ⟨hk, hc, hNew, hFrame⟩
  refine ⟨hk, hc, ?_, ?_⟩
  · intro i hi
    have hb := hNew i hi
    have hEst := hintExactEstimate_mem sch lr x J i j hi
    change out.mem (output + i.val) = _
    change out.mem (output + i.val) = hintTruth ((lr.1 i).val / sch.m ∈
      workerFinal N sch.m sch.ℓ (H.Nmax N X Y) (H.BX N X Y) (H.BY N X Y)
        j (lr.2 j) (sch.rowOf lr J j) (List.ofFn v)) at hb
    rw [hb, hv]
    apply congrArg hintTruth
    exact propext hEst.symm
  · intro addr ha hAway
    apply hFrame addr _ hAway
    change addr < start + 1 - 1 ∨ S.gauss.pivotRow + sch.ℓ ≤ addr
    simpa using ha

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintEstimateRows_write
#print axioms LinearSetReconciliation327.Main.hintFinishRow_exact
end S_HintFinishRowExact20261120
section S_HintPredictRowExact20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintPredictedRows (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (s : Fin sch.ℓ) (predictions abstentions done : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ j < min done sch.m,
    mem (predictions + j) = hintTruth (j ∈ sch.exactP lr x J s) ∧
    mem (abstentions + j) = hintTruth (j ∈ sch.exactHint lr x J s)

theorem hintPredictedRows_write (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (s : Fin sch.ℓ) (j : Fin sch.m) (predictions abstentions scratchEnd : ℕ)
    (before after : ℕ → ℕ)
    (hAfterP : scratchEnd ≤ predictions) (hAfterA : scratchEnd ≤ abstentions)
    (hSeparate : predictions + sch.m ≤ abstentions ∨ abstentions + sch.m ≤ predictions)
    (hPrev : HintPredictedRows sch lr x J s predictions abstentions j.val before)
    (hNewP : after (predictions + j.val) = hintTruth (j.val ∈ sch.exactP lr x J s))
    (hNewA : after (abstentions + j.val) = hintTruth (j.val ∈ sch.exactHint lr x J s))
    (hFrame : ∀ a ≥ scratchEnd, a ≠ predictions + j.val → a ≠ abstentions + j.val → after a = before a) :
    HintPredictedRows sch lr x J s predictions abstentions (j.val + 1) after := by
  intro q hq
  by_cases hqj : q = j.val
  · simpa [hqj] using And.intro hNewP hNewA
  have hq' : q < min j.val sch.m := by omega
  obtain ⟨hP, hA⟩ := hPrev q hq'
  rw [hFrame (predictions + q) (by omega) (by omega) (by rcases hSeparate with h | h <;> omega),
    hFrame (abstentions + q) (by omega) (by rcases hSeparate with h | h <;> omega) (by omega)]
  exact ⟨hP, hA⟩

open HintParams in
theorem hintPredictRow_exact_word (H : HintParams) (N X Y : ℕ)
    (lr : (H.scheme N X Y).LocalSeed) (x J : Finset ℕ)
    (j : Fin (H.scheme N X Y).m) (s : Fin (H.scheme N X Y).ℓ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base endPc cost control pred abstain : ℕ)
    (F : (ℕ → ℕ) → Prop)
    (exec : Sem P E base endPc state (fun k out =>
      let sch := H.scheme N X Y
      let v := fun t : Fin s.val =>
        sch.code j (lr.2 j) (sch.rowOf lr x j) ⟨t.val, t.isLt.trans s.isLt⟩
      let ans := workerPredict N sch.m sch.ℓ (H.Nmax N X Y) (H.BX N X Y) (H.BY N X Y)
        (H.c N X Y) j (lr.2 j) (sch.rowOf lr J j) (List.ofFn v)
      k ≤ cost ∧ out.regs 14 = control ∧
      out.mem pred = hintTruth (ans = some 1) ∧ out.mem abstain = hintTruth (ans = none) ∧ F out.mem)) :
    Sem P E base endPc state (fun k out =>
      k ≤ cost ∧ out.regs 14 = control ∧
      out.mem pred = hintTruth (j.val ∈ (H.scheme N X Y).exactP lr x J s) ∧
      out.mem abstain = hintTruth (j.val ∈ (H.scheme N X Y).exactHint lr x J s) ∧ F out.mem) := by
  let sch := H.scheme N X Y
  have hPrefix := hintTruePrefix_ofFn sch lr x s.val s.isLt.le j
  have hPred (b : Option (ZMod 2)) : j.val ∈ sch.rowsWhere (fun a => sch.exactPred lr x J s a = b) ↔
      sch.exactPred lr x J s j = b := HintCanonicalDecode.mem_rowsWhere _ j
  apply Sem.mono exec
  rintro k out ⟨hk, hc, hp, ha, hf⟩
  have hP : j.val ∈ sch.exactP lr x J s ↔ sch.exactPred lr x J s j = some 1 := hPred (some 1)
  have hA : j.val ∈ sch.exactHint lr x J s ↔ sch.exactPred lr x J s j = none := hPred none
  rw [hPrefix] at hp ha
  refine ⟨hk, hc, ?_, ?_, hf⟩
  · change out.mem pred = hintTruth (j.val ∈ sch.exactP lr x J s)
    rw [hP]
    exact hp
  · change out.mem abstain = hintTruth (j.val ∈ sch.exactHint lr x J s)
    rw [hA]
    exact ha

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPredictRow_exact_word
#print axioms LinearSetReconciliation327.Main.hintPredictedRows_write
end S_HintPredictRowExact20261120
section S_HintPredictPlaced20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintPredictCallCost (G : HintGaussArea) (Nj maxR : ℕ) : ℕ :=
  (hintRowOuterBudget G Nj maxR + 2) * (maxR + 1) + 12 * Nj + 9 * G.rows + 390

set_option maxHeartbeats 800000 in
theorem hintPredictPlaced_step (H : HintParams) (L : HintDecoderPlacement)
    (N X Y node seed descriptor base output abstention : ℕ) (j : Fin (H.rows X Y))
    (s : Fin (H.ell N X Y))
    (lr : (H.scheme N X Y).LocalSeed) (x J : Finset ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState)
    (hInfoN : (L.info node).universeSize = N) (hInfoXY : (L.info node).rowParams = some (X, Y))
    (hAt : At P base (hintRunPredict.compile base)) (hPc : state.pc = base)
    (hDesc : state.regs 6 = descriptor) (hCtx : state.regs 14 = L.control)
    (hm : H.rows X Y ≤ N) (hSteps : 0 < H.ell N X Y) (hWord : 30 < 2 ^ E.W)
    (hDescFit : descriptor + 31 ≤ 2 ^ E.W)
    (hControlFit : L.control < 2 ^ E.W) (hSeedFit : seed < 2 ^ E.W)
    (hKFit : H.Nmax N X Y < 2 ^ E.W) (hStepsFit : H.ell N X Y < 2 ^ E.W)
    (hBXFit : H.BX N X Y < 2 ^ E.W) (hBYFit : H.BY N X Y + 1 < 2 ^ E.W)
    (hCoeffSpace : (j.val + 1) * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ E.W)
    (hCoeff : ∀ q : Fin (H.Nmax N X Y), ∀ s : Fin (H.ell N X Y),
      E.coeff seed (j.val * H.ell N X Y * H.Nmax N X Y + q.val + s.val * H.Nmax N X Y) =
        (lr.2 j s q).val)
    (hPerm : ∀ i : Fin N, E.permInv seed i.val = (lr.1.symm i).val)
    (hK : rowLen N (H.rows X Y) j.val ≤ H.Nmax N X Y) :
    let sch := H.scheme N X Y
    let A := L.arena node
    let K := H.Nmax N X Y
    let BY := H.BY N X Y
    let threshold := L.threshold node j.val
    let Nj := rowLen N sch.m j.val
    let h := (hintRowMembers N sch.m j.val lr.1 J).length
    let G := hintRowWorkspace L.rowScratch s.val K BY seed j.val sch.ℓ h
    let scratchEnd := G.gauss.pivotRow + s.val
    let maxR := min BY (Nj - h)
    (hintRowEventBlock H L node seed j.val s.val output abstention).At E descriptor →
    (hintWaitDetBlock K Nj BY sch.ℓ (H.c N X Y)).At E threshold →
    (∀ i : Fin N, state.mem (A.hints + i.val) = hintTruth (i.val ∈ J)) →
    HintTranscriptCorrect sch lr x A.transcript (fun _ col => col.val < s.val) state.mem →
    HintPredictedRows sch lr x J s output abstention j.val state.mem →
    scratchEnd < 2 ^ E.W →
    scratchEnd ≤ A.transcript →
    A.transcript + j.val + s.val * sch.m ≤ 2 ^ E.W →
    A.transcript + sch.ℓ * sch.m ≤ A.hints →
    A.hints + N ≤ 2 ^ E.W →
    scratchEnd ≤ output → scratchEnd ≤ abstention →
    output + sch.m ≤ 2 ^ E.W → abstention + sch.m ≤ 2 ^ E.W →
    (output + sch.m ≤ abstention ∨ abstention + sch.m ≤ output) →
    threshold + (K + 1) * (BY + 1) ≤ 2 ^ E.W →
    Sem P E base (base + hintRunPredict.len) state (fun k out =>
      k ≤ hintPredictCallCost G.gauss Nj maxR ∧ out.regs 14 = L.control ∧
      HintPredictedRows sch lr x J s output abstention (j.val + 1) out.mem ∧
      (∀ a, (a < L.rowScratch ∨ scratchEnd ≤ a) →
        a ≠ output + j.val → a ≠ abstention + j.val → out.mem a = state.mem a)) := by
  let sch := H.scheme N X Y
  let A := L.arena node
  let K := H.Nmax N X Y
  let BY := H.BY N X Y
  let threshold := L.threshold node j.val
  let Nj := rowLen N sch.m j.val
  let h := (hintRowMembers N sch.m j.val lr.1 J).length
  let G := hintRowWorkspace L.rowScratch s.val K BY seed j.val sch.ℓ h
  let Gmax := hintRowWorkspace L.rowScratch s.val K BY seed j.val sch.ℓ K
  let F := Gmax.fields Nj sch.m A.hints (A.transcript + j.val) (H.BX N X Y) BY threshold output abstention
  let scratchEnd := G.gauss.pivotRow + s.val
  let maxR := min BY (Nj - h)
  dsimp only
  intro hRecord hWait hJ hTranscript hPrev hSpace hScratch hReadSpan hTran hHint
    hOutputAfter hAbstainAfter hOutput hAbstain hSeparate hTable
  change scratchEnd < 2 ^ E.W at hSpace
  change scratchEnd ≤ A.transcript at hScratch
  change A.transcript + j.val + s.val * sch.m ≤ 2 ^ E.W at hReadSpan
  change A.transcript + sch.ℓ * sch.m ≤ A.hints at hTran
  change A.hints + N ≤ 2 ^ E.W at hHint
  change output + sch.m ≤ 2 ^ E.W at hOutput
  change abstention + sch.m ≤ 2 ^ E.W at hAbstain
  change output + sch.m ≤ abstention ∨ abstention + sch.m ≤ output at hSeparate
  change threshold + (K + 1) * (BY + 1) ≤ 2 ^ E.W at hTable
  change Nj ≤ K at hK
  have hSpaceMax : Gmax.gauss.pivotRow + s.val < 2 ^ E.W := hSpace
  have hPn : Gmax.parent + 30 ≤ scratchEnd :=
    (hintRowWorkspace_addresses L.rowScratch s.val K BY seed j.val sch.ℓ K Nj 0
      s.isLt.le le_rfl hK (Nat.zero_le _)).2.2.2.2.2.2.2
  have hRow : j.val < sch.m := j.isLt
  have hOutputFit : output < 2 ^ E.W := by omega
  have hAbstainFit : abstention < 2 ^ E.W := by omega
  have hNfit : N < 2 ^ E.W := by
    have hp : 0 < A.hints := by omega
    omega
  have hLen : h ≤ Nj := by
    simpa only [h, Nj, hintRowMembers] using
      hintGatherList_length_le (fun q => decide (q ∈ rowImage N sch.m lr.1 j.val J)) Nj
  have hWaitRead := hintWaitDetBlock_read E K Nj BY sch.ℓ (H.c N X Y) threshold
    h maxR hWait hTable (hLen.trans hK) (Nat.min_le_left _ _)
  have hAtBlock : (hintRowDetBlock Gmax.parent (F.value Gmax.gauss)).At E descriptor := by
    unfold hintRowEventBlock at hRecord
    simp only [hInfoN, hInfoXY, Option.getD_some] at hRecord
    exact hRecord
  have hHintAfter : Gmax.parent + 30 ≤ A.hints := by omega
  have hTranscriptAfter : Gmax.parent + 30 ≤ A.transcript + j.val := by omega
  have hParentFit : Gmax.parent + 30 ≤ 2 ^ E.W := by omega
  obtain ⟨coords, hPre⟩ := hintRowWorkspace_callPre E L.rowScratch s.val K BY seed j.val sch.ℓ
    N sch.m A.hints (A.transcript + j.val) (H.BX N X Y) threshold output abstention lr.1 J (lr.2 j)
    s.isLt.le hSteps j.isLt hm hK hKFit hSeedFit hStepsFit hSpaceMax
    hHintAfter (by omega) hTranscriptAfter hReadSpan hCoeffSpace (fun q t => hCoeff q ⟨t.val, t.isLt.trans s.isLt⟩) hPerm
  have hFits : ∀ i < 30, F.value Gmax.gauss i < 2 ^ E.W := by
    intro i hi
    have hHead := hintRowWorkspace_headerFits E L.rowScratch s.val K BY seed j.val sch.ℓ K le_rfl
      s.isLt.le hKFit hSeedFit (j.isLt.trans (hm.trans_lt hNfit)) hStepsFit hSpaceMax
    by_cases hi' : 16 ≤ i
    · by_cases h17 : i = 17
      · simpa only [HintRowFields.value, if_pos hi', if_pos h17] using Nat.two_pow_pos E.W
      · simpa only [HintRowFields.value, if_pos hi', if_neg h17] using hHead.values (i - 16) (by omega)
    have hi16 : i < 16 := by omega
    have hOutside : Gmax.outside < 2 ^ E.W := by
      dsimp only [Gmax, hintRowWorkspace, hintGaussDenseArea] at hSpaceMax ⊢
      omega
    have hBitmap : Gmax.bitmap < 2 ^ E.W := by
      dsimp only [Gmax, hintRowWorkspace, hintGaussDenseArea] at hSpaceMax ⊢
      omega
    have hMfit : sch.m < 2 ^ E.W := by
      change H.rows X Y < 2 ^ E.W
      omega
    have hNjFit : Nj < 2 ^ E.W := hK.trans_lt hKFit
    have hTfit : A.transcript + j.val < 2 ^ E.W := by
      have hSteps' : 0 < sch.ℓ := hSteps
      have hProduct : sch.m ≤ sch.ℓ * sch.m := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right sch.m (Nat.succ_le_of_lt hSteps')
      omega
    have hHintFit : A.hints < 2 ^ E.W := by omega
    have hThreshFit : threshold < 2 ^ E.W := by omega
    have hBYsmall : BY < 2 ^ E.W := by
      dsimp only [BY]
      omega
    have hZero := Nat.two_pow_pos E.W
    simp only [HintRowFields.value, if_neg hi']
    interval_cases i <;>
      first
      | exact hOutside
      | exact hBitmap
      | exact hNjFit
      | exact hTfit
      | exact hMfit
      | exact hHintFit
      | exact hThreshFit
      | exact hOutputFit
      | exact hAbstainFit
      | exact hBYsmall
      | exact hBXFit
      | exact hZero
  have hRec := hintRowWorkspace_record E descriptor L.rowScratch s.val K BY seed j.val sch.ℓ h F
    hAtBlock hWord hDescFit hParentFit hFits
  let v : HintVec s.val := fun a =>
    sch.code j (lr.2 j) (sch.rowOf lr x j) ⟨a.val, a.isLt.trans s.isLt⟩
  have hObs (a : Fin s.val) :
      state.mem (A.transcript + j.val + a.val * sch.m) = (v a).val := by
    rw [Nat.add_right_comm]
    exact hTranscript j ⟨a.val, a.isLt.trans s.isLt⟩ a.isLt
  have hNext (hs : s.val < sch.ℓ) (q : Fin K) :
      E.coeff seed ((j.val * sch.ℓ + s.val) * K + q.val) = (lr.2 j ⟨s.val, hs⟩ q).val := by
    rw [Nat.add_mul, Nat.add_right_comm]
    exact hCoeff q s
  have hDistinct : output + j.val ≠ abstention + j.val := by
    rcases hSeparate with h | h <;> omega
  have hRun := hintRunPredict_sem G.gauss F coords v (lr.2 j) s.isLt.le N G.parent
    descriptor L.control base (H.c N X Y) lr.1 J P E state j rfl hPre hRec hDesc hCtx
    hControlFit hJ hObs hBYFit hWaitRead.1 hWaitRead.2 hNext
    (show output + j.val < 2 ^ E.W by omega) (show abstention + j.val < 2 ^ E.W by omega)
    hOutputAfter hAbstainAfter hDistinct hAt hPc
  let frame : (ℕ → ℕ) → Prop := fun mem =>
    ∀ a, (a < L.rowScratch ∨ scratchEnd ≤ a) →
      a ≠ output + j.val → a ≠ abstention + j.val → mem a = state.mem a
  have hPred := hintPredictRow_exact_word H N X Y lr x J j s P E state base
    (base + hintRunPredict.len) (hintPredictCallCost G.gauss Nj maxR) L.control
    (output + j.val) (abstention + j.val) frame (by
      apply Sem.mono hRun
      rintro k out ⟨hk, hc, hp, hb, hf⟩
      refine ⟨hk, hc, hp, hb, ?_⟩
      intro a ha hp ht
      apply hf a _ hp ht
      change a < L.rowScratch + 1 - 1 ∨ scratchEnd ≤ a
      simpa only [Nat.add_sub_cancel] using ha)
  apply Sem.mono hPred
  rintro k out ⟨hk, hc, hp, ha, hf⟩
  exact ⟨hk, hc, hintPredictedRows_write sch lr x J s j output abstention scratchEnd state.mem out.mem
    hOutputAfter hAbstainAfter hSeparate hPrev hp ha (fun a hs => hf a (Or.inr hs)), hf⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPredictPlaced_step
end S_HintPredictPlaced20261120
section S_HintFinalPlaced20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFinalCallCost (G : HintGaussArea) (Nj maxR : ℕ) : ℕ :=
  (hintFinalBudget G Nj maxR + 2) * (maxR + 1) + hintFinalBudget G Nj maxR +
    37 * Nj + 9 * G.rows + 18 * G.hints + 8 * maxR + 470

set_option maxHeartbeats 800000 in
theorem hintFinalPlaced_step (H : HintParams) (L : HintDecoderPlacement)
    (N X Y node seed descriptor base : ℕ) (j : Fin (H.rows X Y))
    (lr : (H.scheme N X Y).LocalSeed) (x J : Finset ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState)
    (hInfoN : (L.info node).universeSize = N) (hInfoXY : (L.info node).rowParams = some (X, Y))
    (hAt : At P base (hintRunFinal.compile base)) (hPc : state.pc = base)
    (hDesc : state.regs 6 = descriptor) (hCtx : state.regs 14 = L.control)
    (hm : H.rows X Y ≤ N) (hSteps : 0 < H.ell N X Y) (hWord : 30 < 2 ^ E.W)
    (hDescFit : descriptor + 31 ≤ 2 ^ E.W)
    (hControlFit : L.control < 2 ^ E.W) (hSeedFit : seed < 2 ^ E.W)
    (hKFit : H.Nmax N X Y < 2 ^ E.W) (hStepsFit : H.ell N X Y < 2 ^ E.W)
    (hBXFit : H.BX N X Y < 2 ^ E.W) (hBYFit : H.BY N X Y + 1 < 2 ^ E.W)
    (hCoeffSpace : (j.val + 1) * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ E.W)
    (hCoeff : ∀ q : Fin (H.Nmax N X Y), ∀ s : Fin (H.ell N X Y),
      E.coeff seed (j.val * H.ell N X Y * H.Nmax N X Y + q.val + s.val * H.Nmax N X Y) =
        (lr.2 j s q).val)
    (hPerm : ∀ i : Fin N, E.permInv seed i.val = (lr.1.symm i).val)
    (hK : rowLen N (H.rows X Y) j.val ≤ H.Nmax N X Y) :
    let sch := H.scheme N X Y
    let A := L.arena node
    let K := H.Nmax N X Y
    let BY := H.BY N X Y
    let threshold := L.threshold node j.val
    let Nj := rowLen N sch.m j.val
    let h := (hintRowMembers N sch.m j.val lr.1 J).length
    let G := hintRowWorkspace L.rowScratch sch.ℓ K BY seed j.val sch.ℓ h
    let scratchEnd := G.gauss.pivotRow + sch.ℓ
    let maxR := min BY (Nj - h)
    (hintRowEventBlock H L node seed j.val sch.ℓ A.result 0).At E descriptor →
    (∀ i : Fin N, state.mem (A.hints + i.val) = hintTruth (i.val ∈ J)) →
    HintTranscriptCorrect sch lr x A.transcript (fun _ _ => True) state.mem →
    HintEstimateRows sch lr x J A.result (· < j.val) state.mem →
    scratchEnd < 2 ^ E.W →
    scratchEnd ≤ A.transcript →
    A.transcript + j.val + sch.ℓ * sch.m ≤ 2 ^ E.W →
    A.transcript + sch.ℓ * sch.m ≤ A.hints →
    A.hints + N ≤ A.result →
    A.result + N ≤ 2 ^ E.W →
    threshold + (K + 1) * (BY + 1) ≤ 2 ^ E.W →
    Sem P E base (base + hintRunFinal.len) state (fun k out =>
      k ≤ hintFinalCallCost G.gauss Nj maxR ∧ out.regs 14 = L.control ∧
      HintEstimateRows sch lr x J A.result (· < j.val + 1) out.mem ∧
      (∀ a, (a < L.rowScratch ∨ scratchEnd ≤ a) →
        (a < A.result ∨ A.result + N ≤ a) → out.mem a = state.mem a)) := by
  let sch := H.scheme N X Y
  let A := L.arena node
  let K := H.Nmax N X Y
  let BY := H.BY N X Y
  let threshold := L.threshold node j.val
  let Nj := rowLen N sch.m j.val
  let h := (hintRowMembers N sch.m j.val lr.1 J).length
  let G := hintRowWorkspace L.rowScratch sch.ℓ K BY seed j.val sch.ℓ h
  let Gmax := hintRowWorkspace L.rowScratch sch.ℓ K BY seed j.val sch.ℓ K
  let F := Gmax.fields Nj sch.m A.hints (A.transcript + j.val) (H.BX N X Y) BY threshold A.result 0
  let scratchEnd := G.gauss.pivotRow + sch.ℓ
  dsimp only
  intro hRecord hJ hTranscript hPrev hSpace hScratch hReadSpan hTran hHint hOut hTable
  change scratchEnd < 2 ^ E.W at hSpace
  change scratchEnd ≤ A.transcript at hScratch
  change A.transcript + j.val + sch.ℓ * sch.m ≤ 2 ^ E.W at hReadSpan
  change A.transcript + sch.ℓ * sch.m ≤ A.hints at hTran
  change A.hints + N ≤ A.result at hHint
  change A.result + N ≤ 2 ^ E.W at hOut
  change threshold + (K + 1) * (BY + 1) ≤ 2 ^ E.W at hTable
  change Nj ≤ K at hK
  have hSpaceMax : Gmax.gauss.pivotRow + sch.ℓ < 2 ^ E.W := hSpace
  have hPn : Gmax.parent + 30 ≤ scratchEnd :=
    (hintRowWorkspace_addresses L.rowScratch sch.ℓ K BY seed j.val sch.ℓ K Nj 0
      le_rfl le_rfl hK (Nat.zero_le _)).2.2.2.2.2.2.2
  have hPos : 0 < N := Nat.zero_lt_of_lt (j.isLt.trans_le hm)
  have hResult : A.result < 2 ^ E.W := by omega
  have hNfit : N < 2 ^ E.W := by omega
  have hThresh : threshold + (BY + 1) * h < 2 ^ E.W := by
    have hLen : h ≤ Nj := by
      simpa only [h, Nj, hintRowMembers] using
        hintGatherList_length_le (fun q => decide (q ∈ rowImage N sch.m lr.1 j.val J)) Nj
    have hProduct := Nat.mul_lt_mul_of_pos_left (show h < K + 1 by omega) (show 0 < BY + 1 by omega)
    rw [Nat.mul_comm (BY + 1) (K + 1)] at hProduct
    omega
  have hAtBlock : (hintRowDetBlock Gmax.parent (F.value Gmax.gauss)).At E descriptor := by
    unfold hintRowEventBlock at hRecord
    simp only [hInfoN, hInfoXY, Option.getD_some] at hRecord
    exact hRecord
  have hHintAfter : Gmax.parent + 30 ≤ A.hints := by omega
  have hTranscriptAfter : Gmax.parent + 30 ≤ A.transcript + j.val := by omega
  have hParentFit : Gmax.parent + 30 ≤ 2 ^ E.W := by omega
  have hOutAfter : scratchEnd ≤ A.result := by omega
  obtain ⟨coords, hPre⟩ := hintRowWorkspace_callPre E L.rowScratch sch.ℓ K BY seed j.val sch.ℓ
    N sch.m A.hints (A.transcript + j.val) (H.BX N X Y) threshold A.result 0 lr.1 J (lr.2 j)
    le_rfl hSteps j.isLt hm hK hKFit hSeedFit hStepsFit hSpaceMax
    hHintAfter (by omega) hTranscriptAfter hReadSpan hCoeffSpace hCoeff hPerm
  have hFits : ∀ i < 30, F.value Gmax.gauss i < 2 ^ E.W := by
    intro i hi
    have hHead := hintRowWorkspace_headerFits E L.rowScratch sch.ℓ K BY seed j.val sch.ℓ K le_rfl
      le_rfl hKFit hSeedFit (j.isLt.trans (hm.trans_lt hNfit)) hStepsFit hSpaceMax
    by_cases hi' : 16 ≤ i
    · by_cases h17 : i = 17
      · simpa only [HintRowFields.value, if_pos hi', if_pos h17] using Nat.two_pow_pos E.W
      · simpa only [HintRowFields.value, if_pos hi', if_neg h17] using hHead.values (i - 16) (by omega)
    have hi16 : i < 16 := by omega
    have hOutside : Gmax.outside < 2 ^ E.W := by
      dsimp only [Gmax, hintRowWorkspace, hintGaussDenseArea] at hSpaceMax ⊢
      omega
    have hBitmap : Gmax.bitmap < 2 ^ E.W := by
      dsimp only [Gmax, hintRowWorkspace, hintGaussDenseArea] at hSpaceMax ⊢
      omega
    have hMfit : sch.m < 2 ^ E.W := by
      change H.rows X Y < 2 ^ E.W
      omega
    have hNjFit : Nj < 2 ^ E.W := hK.trans_lt hKFit
    have hTfit : A.transcript + j.val < 2 ^ E.W := by
      have hProduct : 0 < sch.ℓ * sch.m := Nat.mul_pos hSteps (Nat.zero_lt_of_lt j.isLt)
      omega
    have hHintFit : A.hints < 2 ^ E.W := by omega
    have hThreshFit : threshold < 2 ^ E.W := by omega
    have hBYsmall : BY < 2 ^ E.W := by
      dsimp only [BY]
      omega
    have hZero := Nat.two_pow_pos E.W
    simp only [HintRowFields.value, if_neg hi']
    interval_cases i <;>
      first
      | exact hOutside
      | exact hBitmap
      | exact hNjFit
      | exact hTfit
      | exact hMfit
      | exact hHintFit
      | exact hThreshFit
      | exact hResult
      | exact hBYsmall
      | exact hBXFit
      | exact hZero
  have hRec := hintRowWorkspace_record E descriptor L.rowScratch sch.ℓ K BY seed j.val sch.ℓ h F
    hAtBlock hWord hDescFit hParentFit hFits
  have hRun := hintFinishRow_exact H N X Y lr j x J L.rowScratch seed h A.hints A.transcript threshold
    A.result descriptor L.control base P E state coords hPre hRec hDesc hCtx hControlFit hJ hTranscript
    hBYFit hThresh hResult hOut hAt hPc hOutAfter
  apply Sem.mono hRun
  rintro k out ⟨hk, hc, hFinished, hFrame⟩
  refine ⟨hk, hc, ?_, ?_⟩
  · have hAcc := hintEstimateRows_write sch lr x J A.result j.val scratchEnd (· < j.val)
      state.mem out.mem hOutAfter hPrev hFinished (fun a ha hs => hFrame a (Or.inr ha) hs)
    intro i hi
    apply hAcc i
    change (lr.1 i).val % sch.m < j.val + 1 at hi
    omega
  · intro a ha hb
    change a < A.result ∨ A.result + N ≤ a at hb
    apply hFrame a ha
    intro i _ he
    change a = A.result + i.val at he
    have hi := i.isLt
    omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalPlaced_step
end S_HintFinalPlaced20261120
section S_HintFinalRowsPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintRowLen_le_Nmax (H : HintParams) (N X Y : ℕ) (j : Fin (H.rows X Y)) :
    rowLen N (H.rows X Y) j.val ≤ H.Nmax N X Y := by
  have hm : 0 < H.rows X Y := Nat.zero_lt_of_lt j.isLt
  have hmR : (0 : ℝ) < H.rows X Y := by exact_mod_cast hm
  have hK : (N : ℝ) / (H.rows X Y : ℝ) ≤ H.Nmax N X Y :=
    Nat.le_ceil _
  have hSpace : N ≤ H.Nmax N X Y * H.rows X Y := by
    have h := (div_le_iff₀ hmR).mp hK
    exact_mod_cast h
  by_contra! h
  have hBad := HintRowCoordinates.index_lt N (H.rows X Y) j.val (H.Nmax N X Y) hm j.isLt h
  omega

noncomputable def hintFinalScratchEnd (H : HintParams) (start N X Y : ℕ) : ℕ :=
  (hintRowWorkspace start (H.ell N X Y) (H.Nmax N X Y) (H.BY N X Y)
    0 0 (H.ell N X Y) (H.Nmax N X Y)).gauss.pivotRow + H.ell N X Y

noncomputable def hintFinalRows_phase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header N X Y node seed first : ℕ) (lr : (H.scheme N X Y).LocalSeed)
    (x J : Finset ℕ) (keep : (ℕ → ℕ) → Prop)
    (hInfoN : (D.placement.info node).universeSize = N)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
    (hControl : D.placement.control = D.control)
    (hMap : ∀ q < H.rows X Y, D.events[first + q]? = some (.finishRow node seed q))
    (hmPos : 0 < H.rows X Y) (hm : H.rows X Y ≤ N)
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
    let scratchEnd := hintFinalScratchEnd H start N X Y
    D.control + 2 < start →
    D.control + 2 < A.transcript →
    scratchEnd < 2 ^ E.W →
    scratchEnd ≤ A.transcript →
    A.transcript + sch.ℓ * sch.m ≤ A.hints →
    A.hints + N ≤ A.result →
    A.result + N ≤ 2 ^ E.W →
    (∀ j : Fin (H.rows X Y),
      D.placement.threshold node j.val + (H.Nmax N X Y + 1) * (H.BY N X Y + 1) ≤ 2 ^ E.W) →
    (∀ j : Fin D.events.length, first ≤ j.val → j.val < first + sch.m →
      hintEventDescriptor header D.events (hintEventRecord S H D.placement) j.val + 31 ≤ 2 ^ E.W) →
    (∀ m m', (∀ a, (a < start ∨ scratchEnd ≤ a) → (a < A.result ∨ A.result + N ≤ a) → m' a = m a) →
      keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first sch.m
      (fun m => HintBitmap m A.hints N J ∧ HintTranscriptCorrect sch lr x A.transcript (fun _ _ => True) m ∧ keep m)
      (fun m => HintBitmap m A.result N (sch.exactEstimate lr x J) ∧ keep m) := by
  let sch := H.scheme N X Y
  let A := D.placement.arena node
  let start := D.placement.rowScratch
  let scratchEnd := hintFinalScratchEnd H start N X Y
  let inv := fun i m => HintBitmap m A.hints N J ∧
    HintTranscriptCorrect sch lr x A.transcript (fun _ _ => True) m ∧
    HintEstimateRows sch lr x J A.result (· < i) m ∧ keep m
  let budget := fun j =>
    let h := (hintRowMembers N sch.m j lr.1 J).length
    let Nj := rowLen N sch.m j
    let w := hintRowWorkspace start sch.ℓ (H.Nmax N X Y) (H.BY N X Y) seed j sch.ℓ h
    hintFinalCallCost w.gauss Nj (min (H.BY N X Y) (Nj - h))
  dsimp only
  intro hCtrlStart hCtrlTran hSpace hScratch hTran hHint hOut hThreshold hDescriptors hKeep hKeepCursor
  change D.control + 2 < start at hCtrlStart
  change D.control + 2 < A.transcript at hCtrlTran
  change scratchEnd < 2 ^ E.W at hSpace
  change scratchEnd ≤ A.transcript at hScratch
  change A.transcript + sch.ℓ * sch.m ≤ A.hints at hTran
  change A.hints + N ≤ A.result at hHint
  change A.result + N ≤ 2 ^ E.W at hOut
  have hBeforeHint : D.control + 2 < A.hints := by omega
  have hBeforeResult : D.control + 2 < A.result := by omega
  have hAfterHint : scratchEnd ≤ A.hints := by omega
  have hCtrlWord : D.placement.control < 2 ^ E.W := by rw [hControl]; omega
  let target := fun m => HintBitmap m A.result N (sch.exactEstimate lr x J) ∧ keep m
  -- At the last boundary the row-local data is no longer required.
  let phaseInv := fun i m => if i = sch.m then target m else inv i m
  refine ⟨budget, phaseInv, ?_, ?_, ?_, ?_⟩
  · intro m
    have hne : 0 ≠ sch.m := Nat.ne_of_lt hmPos
    simp only [phaseInv, if_neg hne]
    constructor
    · rintro ⟨hJ, hT, _, hK⟩
      exact ⟨hJ, hT, hK⟩
    · rintro ⟨hJ, hT, hK⟩
      exact ⟨hJ, hT, fun _ h => (Nat.not_lt_zero _ h).elim, hK⟩
  · intro m
    change phaseInv sch.m m ↔ target m
    simp only [phaseInv, if_pos rfl]
  · intro i m v h
    by_cases hi : i = sch.m
    · simp only [phaseInv, if_pos hi] at h ⊢
      obtain ⟨hR, hK⟩ := h
      refine ⟨?_, hKeepCursor m v hK⟩
      intro a ha
      rw [Function.update_of_ne (by omega : A.result + a ≠ D.control + 2)]
      exact hR a ha
    · simp only [phaseInv, if_neg hi] at h ⊢
      obtain ⟨hJ, hT, hA, hK⟩ := h
      refine ⟨?_, ?_, ?_, hKeepCursor m v hK⟩
      · intro a ha
        rw [Function.update_of_ne (by omega : A.hints + a ≠ D.control + 2)]
        exact hJ a ha
      · intro j s hs
        rw [Function.update_of_ne (by unfold hintTranscriptCell; omega :
          hintTranscriptCell A.transcript sch.m j.val s.val ≠ D.control + 2)]
        exact hT j s hs
      · intro a ha
        rw [Function.update_of_ne (by omega : A.result + a.val ≠ D.control + 2)]
        exact hA a ha
  · intro i hi pos hPos act base state
    dsimp only
    intro hSelect _ hAt hPc hArg hCtx _ hInv hRecord
    let j : Fin (H.rows X Y) := ⟨i, hi⟩
    have hEv := (List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans
      (by rw [hPos]; exact hMap i hi : D.events[pos.val]? = some (.finishRow node seed i))
    have hEq := Option.some.inj hEv
    have hTag : D.events[pos.val].tag = 3 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintRunFinal := (Option.some.inj hSelect).symm
    subst act
    have hNe : i ≠ sch.m := Nat.ne_of_lt hi
    simp only [phaseInv, if_neg hNe] at hInv
    obtain ⟨hJ, hT, hPrev, hK⟩ := hInv
    rw [hEq] at hRecord
    have hBlock : (hintRowEventBlock H D.placement node seed j.val sch.ℓ A.result 0).At E
        (hintEventDescriptor header D.events (hintEventRecord S H D.placement) pos.val) := by
      simp only [hintEventRecord, hInfoN, hInfoXY, Option.getD_some] at hRecord
      exact hRecord
    have hBound := hDescriptors pos (by omega) (by omega)
    have hCoeffAddr : (j.val + 1) * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ E.W :=
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ j.isLt)).trans hCoeffSpace
    have hReadSpan : A.transcript + j.val + sch.ℓ * sch.m ≤ 2 ^ E.W := by
      have hj := j.isLt.trans_le hm
      omega
    have hRun := hintFinalPlaced_step H D.placement N X Y node seed _ base j lr x J
      (hintNativeProgram S) E state hInfoN hInfoXY hAt hPc hArg (hCtx.trans hControl.symm) hm hSteps hWord
      hBound hCtrlWord hSeedFit hKFit hStepsFit hBXFit hBYFit hCoeffAddr (hCoeff j) hPerm
      (hintRowLen_le_Nmax H N X Y j) hBlock (fun a => hJ a.val a.isLt) hT hPrev hSpace hScratch
      hReadSpan hTran hHint hOut (hThreshold j)
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hRows, hf⟩
    have hFrame : ∀ a, (a < start ∨ scratchEnd ≤ a) → (a < A.result ∨ A.result + N ≤ a) → out.mem a = state.mem a := hf
    have hKeepOut := hKeep _ _ hFrame hK
    refine ⟨hk, ?_, hc.trans hControl, ?_⟩
    · by_cases hlast : i + 1 = sch.m
      · simp only [phaseInv, if_pos hlast, target]
        refine ⟨?_, hKeepOut⟩
        intro a ha
        apply hRows ⟨a, ha⟩
        change (lr.1 (⟨a, ha⟩ : Fin N)).val % sch.m < i + 1
        rw [hlast]
        exact Nat.mod_lt _ hmPos
      · simp only [phaseInv, if_neg hlast]
        refine ⟨?_, ?_, hRows, hKeepOut⟩
        · intro a ha
          rw [hFrame (A.hints + a) (Or.inr (by omega)) (Or.inl (by omega))]
          exact hJ a ha
        · intro j' s hs
          have hAddr := hintPairOffset_lt s j'
          rw [hFrame (hintTranscriptCell A.transcript sch.m j'.val s.val)
            (Or.inr (by unfold hintTranscriptCell; omega)) (Or.inl (by unfold hintTranscriptCell; omega))]
          exact hT j' s hs
    · intro a _ ha
      exact hFrame a (Or.inl (ha.trans_lt hCtrlStart)) (Or.inl (ha.trans_lt hBeforeResult))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalRows_phase
end S_HintFinalRowsPhase20261120
section S_HintPredictRowsPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintPredictScratchEnd (H : HintParams) (start N X Y prefixLen : ℕ) : ℕ :=
  (hintRowWorkspace start prefixLen (H.Nmax N X Y) (H.BY N X Y)
    0 0 (H.ell N X Y) (H.Nmax N X Y)).gauss.pivotRow + prefixLen

noncomputable def hintPredictRows_phase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header N X Y node child seed first : ℕ) (lr : (H.scheme N X Y).LocalSeed)
    (x J : Finset ℕ) (col : Fin (H.scheme N X Y).ℓ) (keep : (ℕ → ℕ) → Prop)
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
      HintTranscriptCorrect sch lr x A.transcript (fun _ s => s.val < col.val) m ∧ keep m
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
      (fun m => ready m ∧ HintBitmap m dest sch.m (sch.exactP lr x J col) ∧
        HintBitmap m abstention sch.m (sch.exactHint lr x J col)) := by
  let sch := H.scheme N X Y
  let A := D.placement.arena node
  let start := D.placement.rowScratch
  let scratchEnd := hintPredictScratchEnd H start N X Y col.val
  let dest := A.transcript + col.val * sch.m
  let abstention := (D.placement.arena child).hints
  let ready := fun m => HintBitmap m A.hints N J ∧
    HintTranscriptCorrect sch lr x A.transcript (fun _ s => s.val < col.val) m ∧ keep m
  let inv := fun i m => ready m ∧ HintPredictedRows sch lr x J col dest abstention i m
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
    change ready m ∧ HintPredictedRows sch lr x J col dest abstention sch.m m ↔ _
    unfold HintPredictedRows
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
    have hRun := hintPredictPlaced_step H D.placement N X Y node seed desc base dest abstention j col lr x J
      (hintNativeProgram S) E state hInfoN hInfoXY hAt hPc hArg (hCtx.trans hControl.symm) hm hSteps hWord
      hBound hCtrlWord hSeedFit hKFit hStepsFit hBXFit hBYFit hCoeffAddr (hCoeff j) hPerm
      (hintRowLen_le_Nmax H N X Y j) hBlock (hThreshold j).1 (fun a => hJ a.val a.isLt) hT hPrev
      hSpace hScratch hReadSpan hTran hHintFit hDestAfter hAbstainAfter hDestFit hAbstain
      (Or.inl hDisjoint) (hThreshold j).2
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hRows, hf⟩
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
#print axioms LinearSetReconciliation327.Main.hintPredictRows_phase
end S_HintPredictRowsPhase20261120
section S_HintPredictBinary20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

set_option maxHeartbeats 800000 in
theorem hintPredictPlaced_binary_step (H : HintParams) (L : HintDecoderPlacement)
    (N X Y node seed descriptor base output abstention : ℕ) (j : Fin (H.rows X Y))
    (s : Fin (H.ell N X Y))
    (lr : (H.scheme N X Y).LocalSeed) (J : Finset ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState)
    (hInfoN : (L.info node).universeSize = N) (hInfoXY : (L.info node).rowParams = some (X, Y))
    (hAt : At P base (hintRunPredict.compile base)) (hPc : state.pc = base)
    (hDesc : state.regs 6 = descriptor) (hCtx : state.regs 14 = L.control)
    (hm : H.rows X Y ≤ N) (hSteps : 0 < H.ell N X Y) (hWord : 30 < 2 ^ E.W)
    (hDescFit : descriptor + 31 ≤ 2 ^ E.W)
    (hControlFit : L.control < 2 ^ E.W) (hSeedFit : seed < 2 ^ E.W)
    (hKFit : H.Nmax N X Y < 2 ^ E.W) (hStepsFit : H.ell N X Y < 2 ^ E.W)
    (hBXFit : H.BX N X Y < 2 ^ E.W) (hBYFit : H.BY N X Y + 1 < 2 ^ E.W)
    (hCoeffSpace : (j.val + 1) * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ E.W)
    (hCoeff : ∀ q : Fin (H.Nmax N X Y), ∀ s : Fin (H.ell N X Y),
      E.coeff seed (j.val * H.ell N X Y * H.Nmax N X Y + q.val + s.val * H.Nmax N X Y) =
        (lr.2 j s q).val)
    (hPerm : ∀ i : Fin N, E.permInv seed i.val = (lr.1.symm i).val)
    (hK : rowLen N (H.rows X Y) j.val ≤ H.Nmax N X Y) :
    let sch := H.scheme N X Y
    let A := L.arena node
    let K := H.Nmax N X Y
    let BY := H.BY N X Y
    let threshold := L.threshold node j.val
    let Nj := rowLen N sch.m j.val
    let h := (hintRowMembers N sch.m j.val lr.1 J).length
    let G := hintRowWorkspace L.rowScratch s.val K BY seed j.val sch.ℓ h
    let scratchEnd := G.gauss.pivotRow + s.val
    let maxR := min BY (Nj - h)
    (hintRowEventBlock H L node seed j.val s.val output abstention).At E descriptor →
    (hintWaitDetBlock K Nj BY sch.ℓ (H.c N X Y)).At E threshold →
    (∀ i : Fin N, state.mem (A.hints + i.val) = hintTruth (i.val ∈ J)) →
    (∀ a < s.val, state.mem (A.transcript + j.val + a * sch.m) < 2) →
    scratchEnd < 2 ^ E.W →
    scratchEnd ≤ A.transcript →
    A.transcript + j.val + s.val * sch.m ≤ 2 ^ E.W →
    A.transcript + sch.ℓ * sch.m ≤ A.hints →
    A.hints + N ≤ 2 ^ E.W →
    scratchEnd ≤ output → scratchEnd ≤ abstention →
    output + sch.m ≤ 2 ^ E.W → abstention + sch.m ≤ 2 ^ E.W →
    (output + sch.m ≤ abstention ∨ abstention + sch.m ≤ output) →
    threshold + (K + 1) * (BY + 1) ≤ 2 ^ E.W →
    Sem P E base (base + hintRunPredict.len) state (fun k out =>
      k ≤ hintPredictCallCost G.gauss Nj maxR ∧ out.regs 14 = L.control ∧
      out.mem (output + j.val) < 2 ∧ out.mem (abstention + j.val) < 2 ∧
      (∀ a, (a < L.rowScratch ∨ scratchEnd ≤ a) →
        a ≠ output + j.val → a ≠ abstention + j.val → out.mem a = state.mem a)) := by
  let sch := H.scheme N X Y
  let A := L.arena node
  let K := H.Nmax N X Y
  let BY := H.BY N X Y
  let threshold := L.threshold node j.val
  let Nj := rowLen N sch.m j.val
  let h := (hintRowMembers N sch.m j.val lr.1 J).length
  let G := hintRowWorkspace L.rowScratch s.val K BY seed j.val sch.ℓ h
  let Gmax := hintRowWorkspace L.rowScratch s.val K BY seed j.val sch.ℓ K
  let F := Gmax.fields Nj sch.m A.hints (A.transcript + j.val) (H.BX N X Y) BY threshold output abstention
  let scratchEnd := G.gauss.pivotRow + s.val
  let maxR := min BY (Nj - h)
  dsimp only
  intro hRecord hWait hJ hTranscript hSpace hScratch hReadSpan hTran hHint
    hOutputAfter hAbstainAfter hOutput hAbstain hSeparate hTable
  change scratchEnd < 2 ^ E.W at hSpace
  change scratchEnd ≤ A.transcript at hScratch
  change A.transcript + j.val + s.val * sch.m ≤ 2 ^ E.W at hReadSpan
  change A.transcript + sch.ℓ * sch.m ≤ A.hints at hTran
  change A.hints + N ≤ 2 ^ E.W at hHint
  change output + sch.m ≤ 2 ^ E.W at hOutput
  change abstention + sch.m ≤ 2 ^ E.W at hAbstain
  change output + sch.m ≤ abstention ∨ abstention + sch.m ≤ output at hSeparate
  change threshold + (K + 1) * (BY + 1) ≤ 2 ^ E.W at hTable
  change Nj ≤ K at hK
  have hSpaceMax : Gmax.gauss.pivotRow + s.val < 2 ^ E.W := hSpace
  have hPn : Gmax.parent + 30 ≤ scratchEnd :=
    (hintRowWorkspace_addresses L.rowScratch s.val K BY seed j.val sch.ℓ K Nj 0
      s.isLt.le le_rfl hK (Nat.zero_le _)).2.2.2.2.2.2.2
  have hRow : j.val < sch.m := j.isLt
  have hOutputFit : output < 2 ^ E.W := by omega
  have hAbstainFit : abstention < 2 ^ E.W := by omega
  have hNfit : N < 2 ^ E.W := by
    have hp : 0 < A.hints := by omega
    omega
  have hLen : h ≤ Nj := by
    simpa only [h, Nj, hintRowMembers] using
      hintGatherList_length_le (fun q => decide (q ∈ rowImage N sch.m lr.1 j.val J)) Nj
  have hWaitRead := hintWaitDetBlock_read E K Nj BY sch.ℓ (H.c N X Y) threshold
    h maxR hWait hTable (hLen.trans hK) (Nat.min_le_left _ _)
  have hAtBlock : (hintRowDetBlock Gmax.parent (F.value Gmax.gauss)).At E descriptor := by
    unfold hintRowEventBlock at hRecord
    simp only [hInfoN, hInfoXY, Option.getD_some] at hRecord
    exact hRecord
  have hHintAfter : Gmax.parent + 30 ≤ A.hints := by omega
  have hTranscriptAfter : Gmax.parent + 30 ≤ A.transcript + j.val := by omega
  have hParentFit : Gmax.parent + 30 ≤ 2 ^ E.W := by omega
  obtain ⟨coords, hPre⟩ := hintRowWorkspace_callPre E L.rowScratch s.val K BY seed j.val sch.ℓ
    N sch.m A.hints (A.transcript + j.val) (H.BX N X Y) threshold output abstention lr.1 J (lr.2 j)
    s.isLt.le hSteps j.isLt hm hK hKFit hSeedFit hStepsFit hSpaceMax
    hHintAfter (by omega) hTranscriptAfter hReadSpan hCoeffSpace (fun q t => hCoeff q ⟨t.val, t.isLt.trans s.isLt⟩) hPerm
  have hFits : ∀ i < 30, F.value Gmax.gauss i < 2 ^ E.W := by
    intro i hi
    have hHead := hintRowWorkspace_headerFits E L.rowScratch s.val K BY seed j.val sch.ℓ K le_rfl
      s.isLt.le hKFit hSeedFit (j.isLt.trans (hm.trans_lt hNfit)) hStepsFit hSpaceMax
    by_cases hi' : 16 ≤ i
    · by_cases h17 : i = 17
      · simpa only [HintRowFields.value, if_pos hi', if_pos h17] using Nat.two_pow_pos E.W
      · simpa only [HintRowFields.value, if_pos hi', if_neg h17] using hHead.values (i - 16) (by omega)
    have hi16 : i < 16 := by omega
    have hOutside : Gmax.outside < 2 ^ E.W := by
      dsimp only [Gmax, hintRowWorkspace, hintGaussDenseArea] at hSpaceMax ⊢
      omega
    have hBitmap : Gmax.bitmap < 2 ^ E.W := by
      dsimp only [Gmax, hintRowWorkspace, hintGaussDenseArea] at hSpaceMax ⊢
      omega
    have hMfit : sch.m < 2 ^ E.W := by
      change H.rows X Y < 2 ^ E.W
      omega
    have hNjFit : Nj < 2 ^ E.W := hK.trans_lt hKFit
    have hTfit : A.transcript + j.val < 2 ^ E.W := by
      have hSteps' : 0 < sch.ℓ := hSteps
      have hProduct : sch.m ≤ sch.ℓ * sch.m := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right sch.m (Nat.succ_le_of_lt hSteps')
      omega
    have hHintFit : A.hints < 2 ^ E.W := by omega
    have hThreshFit : threshold < 2 ^ E.W := by omega
    have hBYsmall : BY < 2 ^ E.W := by
      dsimp only [BY]
      omega
    have hZero := Nat.two_pow_pos E.W
    simp only [HintRowFields.value, if_neg hi']
    interval_cases i <;>
      first
      | exact hOutside
      | exact hBitmap
      | exact hNjFit
      | exact hTfit
      | exact hMfit
      | exact hHintFit
      | exact hThreshFit
      | exact hOutputFit
      | exact hAbstainFit
      | exact hBYsmall
      | exact hBXFit
      | exact hZero
  have hRec := hintRowWorkspace_record E descriptor L.rowScratch s.val K BY seed j.val sch.ℓ h F
    hAtBlock hWord hDescFit hParentFit hFits
  let v : HintVec s.val := fun a => if state.mem (A.transcript + j.val + a.val * sch.m) = 0 then 0 else 1
  have hObs (a : Fin s.val) :
      state.mem (A.transcript + j.val + a.val * sch.m) = (v a).val := by
    have hBit := hTranscript a.val a.isLt
    change state.mem (A.transcript + j.val + a.val * sch.m) < 2 at hBit
    by_cases h0 : state.mem (A.transcript + j.val + a.val * sch.m) = 0
    · rw [h0]; simp [v, h0]
    · have h1 : state.mem (A.transcript + j.val + a.val * sch.m) = 1 := by omega
      rw [h1]
      simp only [v, h0, if_false]
      rfl
  have hNext (hs : s.val < sch.ℓ) (q : Fin K) :
      E.coeff seed ((j.val * sch.ℓ + s.val) * K + q.val) = (lr.2 j ⟨s.val, hs⟩ q).val := by
    rw [Nat.add_mul, Nat.add_right_comm]
    exact hCoeff q s
  have hDistinct : output + j.val ≠ abstention + j.val := by
    rcases hSeparate with h | h <;> omega
  have hRun := hintRunPredict_sem G.gauss F coords v (lr.2 j) s.isLt.le N G.parent
    descriptor L.control base (H.c N X Y) lr.1 J P E state j rfl hPre hRec hDesc hCtx
    hControlFit hJ hObs hBYFit hWaitRead.1 hWaitRead.2 hNext
    (show output + j.val < 2 ^ E.W by omega) (show abstention + j.val < 2 ^ E.W by omega)
    hOutputAfter hAbstainAfter hDistinct hAt hPc
  apply Sem.mono hRun
  rintro k out ⟨hk, hc, hp, hb, hf⟩
  have hBinary (P : Prop) [Decidable P] : hintTruth P < 2 := by
    by_cases h : P <;> simp [hintTruth, h]
  refine ⟨hk, hc, ?_, ?_, ?_⟩
  · change out.mem (output + j.val) = hintTruth _ at hp
    rw [hp]
    exact hBinary _
  · change out.mem (abstention + j.val) = hintTruth _ at hb
    rw [hb]
    exact hBinary _
  · intro a ha hp hb
    apply hf a _ hp hb
    change a < L.rowScratch + 1 - 1 ∨ scratchEnd ≤ a
    simpa only [Nat.add_sub_cancel] using ha

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPredictPlaced_binary_step
end S_HintPredictBinary20261120


