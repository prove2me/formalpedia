-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Bundle51_11a
-- name    : LinearSetReconciliation327_Main_Bundle51_11a
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T15:37:41.395473+00:00
-- url     : https://prove2.me/theorems/0c19cef1-4706-4e78-9072-1a9c6af04390
-- title:
--   LinearSetReconciliation327 鈥?Bundle51_11a
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_Bundle51_11a` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_09
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_10

/-! Bundled module: LinearSetReconciliation327_Main_Bundle51_11a
    Members (declaration text copied byte-identically, dependency order):
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalPlaced20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalRowsPhase20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPredictRowsPhase20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPredictBinary20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPredictBinaryRows20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintArbitraryInput20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintBinaryResidualPrefix20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintBinaryChild20261120
    Only `import` lines were merged; every member body is wrapped in its own
    `section ... end` so that per-file `set_option`s stay scoped. -/

section -- Def_LinearSetReconciliation327_Main_HintFinalPlaced20261120
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
end -- Def_LinearSetReconciliation327_Main_HintFinalPlaced20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalRowsPhase20261120
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
end -- Def_LinearSetReconciliation327_Main_HintFinalRowsPhase20261120

section -- Def_LinearSetReconciliation327_Main_HintPredictRowsPhase20261120
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
end -- Def_LinearSetReconciliation327_Main_HintPredictRowsPhase20261120

section -- Def_LinearSetReconciliation327_Main_HintPredictBinary20261120
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
end -- Def_LinearSetReconciliation327_Main_HintPredictBinary20261120

section -- Def_LinearSetReconciliation327_Main_HintPredictBinaryRows20261120
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
end -- Def_LinearSetReconciliation327_Main_HintPredictBinaryRows20261120

section -- Def_LinearSetReconciliation327_Main_HintArbitraryInput20261120
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
end -- Def_LinearSetReconciliation327_Main_HintArbitraryInput20261120

section -- Def_LinearSetReconciliation327_Main_HintBinaryResidualPrefix20261120
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
end -- Def_LinearSetReconciliation327_Main_HintBinaryResidualPrefix20261120

section -- Def_LinearSetReconciliation327_Main_HintBinaryChild20261120
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
end -- Def_LinearSetReconciliation327_Main_HintBinaryChild20261120


