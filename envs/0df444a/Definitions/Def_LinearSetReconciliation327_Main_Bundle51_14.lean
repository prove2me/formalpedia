-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Bundle51_14
-- name    : LinearSetReconciliation327_Main_Bundle51_14
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T08:11:07.730947+00:00
-- url     : https://prove2.me/theorems/df381a48-1772-472e-9b6e-4575d187b136
-- title:
--   LinearSetReconciliation327 鈥?Bundle51_14
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_Bundle51_14` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_09
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_10
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_11a
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_12
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_13

/-! Bundled module: LinearSetReconciliation327_Main_Bundle51_14
    Members (declaration text copied byte-identically, dependency order):
      * Definitions.Def_LinearSetReconciliation327_Main_HintBinaryPrepare20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPrepareBudget20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalBinary20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalBinaryRows20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowCostCap20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowPhaseBudget20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintResidualTablePlaced20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedBinaryTail20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedBinaryDirect20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowTailBudget20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintBinaryColumn20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintColumnBudget20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintLeafBudget20261120
    Only `import` lines were merged; every member body is wrapped in its own
    `section ... end` so that per-file `set_option`s stay scoped. -/

section -- Def_LinearSetReconciliation327_Main_HintBinaryPrepare20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintPrepareChild_total (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node seed first word N X Y t Bc : ℕ)
    (Xs Ys : Fin (H.scheme N X Y).ℓ → ℕ) (children : Fin (H.scheme N X Y).ℓ → Node)
    (r : (Node.recursive (H.scheme N X Y) t Xs Ys children).Seed)
    (col : Fin (H.scheme N X Y).ℓ)
    (payloadOffset : ℕ → ℕ) (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = D.placement.width) (hW : 0 < E.W) (hWord : 16 < 2 ^ E.W)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
    (hChildSize : (children col).N = (H.scheme N X Y).m)
    (hSlice : HintEventSlice D first (hintRecursiveColumnEvents (crFamily S) payloadOffset
      (H.scheme N X Y) children node seed (word * E.W) col)) :
    let sch := H.scheme N X Y
    let CR := crFamily S
    let L := D.placement
    let child := children col
    let childNode := hintChildPhysicalIndex children node col
    let childSeed := hintChildSchemeIndex children seed col
    let B := L.arena childNode
    let dest := B.payload
    let gate := (L.arena node).transcript + col.val * sch.m
    let words := wordsOf E.W (synLen CR child)
    let table := L.updateTable childNode
    let colBase := hintSubtreeColBase Bc child
    let items := hintChildUpdateSchedule CR Bc colBase child childSeed B.saveOffset
    let predicts := fun m => HintBinaryMemory m gate sch.m
    let fresh := HintFreshWords dest words
    let input := HintPackedMemory E.W dest (synLen CR child)
    D.control + 2 < gate →
    gate + sch.m ≤ dest →
    dest + (B.saveOffset + 2) ≤ 2 ^ E.W →
    words ≤ B.workStart →
    UpSaveRoom B.workStart B.saveOffset child →
    word * E.W + synLen CR (.recursive sch t Xs Ys children) < 2 ^ E.W →
    (word * E.W + synLen CR (.recursive sch t Xs Ys children)) / E.W < dest →
    table + 3 < 2 ^ E.W →
    E.det (table + 3) = D.control →
    UpSavedLayout E table items →
    E.det (table % 2 ^ E.W) % 2 ^ E.W = items.length →
    (∀ i < child.N, UpLocalTree CR (upShiftDetEnv E table) i Bc colBase child (r.2 col) childSeed 0 0) →
    (∀ pos : Fin D.events.length, first + sch.m ≤ pos.val → pos.val < first + sch.m + 1 + sch.m →
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 3 < 2 ^ E.W) →
    (∀ m m', CRMemFrame dest (dest + B.saveOffset + 2) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header (first + sch.m) (1 + sch.m)
      (fun m => predicts m ∧ fresh m ∧ keep m) (fun m => predicts m ∧ input m ∧ keep m) := by
  let sch := H.scheme N X Y
  let CR := crFamily S
  let L := D.placement
  let child := children col
  let childNode := hintChildPhysicalIndex children node col
  let childSeed := hintChildSchemeIndex children seed col
  let B := L.arena childNode
  let dest := B.payload
  let gate := (L.arena node).transcript + col.val * sch.m
  let words := wordsOf E.W (synLen CR child)
  let table := L.updateTable childNode
  let colBase := hintSubtreeColBase Bc child
  let items := hintChildUpdateSchedule CR Bc colBase child childSeed B.saveOffset
  let predicts := fun m => HintBinaryMemory m gate sch.m
  let fresh := HintFreshWords dest words
  let raw := HintPackedMemory E.W dest (synLen CR child)
  let input := HintPackedMemory E.W dest (synLen CR child)
  dsimp only
  intro hCtrl hGateEnd hDestEnd hGap hRoom hInputFit hInputSep hTable hReturn hLayout hCount hLocal hDesc hKeep hCursor
  change D.control + 2 < gate at hCtrl
  change gate + sch.m ≤ dest at hGateEnd
  change dest + (B.saveOffset + 2) ≤ 2 ^ E.W at hDestEnd
  change words ≤ B.workStart at hGap
  change (∀ p : Fin D.events.length, first + sch.m ≤ p.val →
    p.val < first + sch.m + 1 + sch.m →
    hintEventDescriptor header D.events (hintEventRecord S H L) p.val + 3 < 2 ^ E.W) at hDesc
  change (∀ m m', CRMemFrame dest (dest + B.saveOffset + 2) m m' → keep m → keep m') at hKeep
  change child.N = sch.m at hChildSize
  have hWord2 : 2 < 2 ^ E.W := by omega
  have hDest : dest < 2 ^ E.W := by omega
  have hDestCtrl : D.control + 2 < dest := by omega
  have hSizeFit : child.N ≤ 2 ^ E.W := by omega
  have hWork : B.workStart ≤ B.saveOffset := (Nat.le_add_right _ _).trans hRoom
  have hWordsEnd : dest + words ≤ 2 ^ E.W := by omega
  obtain ⟨_, hCopy, hToggle, _, _⟩ := hintRecursiveColumn_slice CR D payloadOffset sch children node seed
    (word * E.W) first col hSlice
  have hCopyPos : D.events[first + sch.m]? = some (.childCopy node col.val childNode
      (word * E.W + ((List.ofFn fun i => synLen CR (children i)).take col.val).sum) (synLen CR child)) := hCopy
  have hTogglePos (q : ℕ) (hq : q < child.N) :
      D.events[first + sch.m + 1 + q]? = some (.childToggle node col.val childNode childSeed q) :=
    hToggle q (hChildSize ▸ hq)
  let copy := hintChildCopy_total S H D E header node childNode (first + sch.m) word sch t Xs Ys children col
    (fun m => predicts m ∧ keep m) hWidth hWord2 hW hCopyPos hDestCtrl hDest hInputFit hWordsEnd hInputSep
    (by
      intro pos hp
      change pos.val = first + sch.m at hp
      exact hDesc pos hp.ge (by omega)) 
    (by
      intro m m' hf hk
      have frame : CRMemFrame dest (dest + words) m m' := hf
      refine ⟨(fun q hq => by
        rw [frame (gate + q) (Or.inl (by omega))]
        exact hk.1 q hq), hKeep m m' ?_ hk.2⟩
      intro a ha
      rcases ha with h | h
      · exact frame a (Or.inl h)
      · exact frame a (Or.inr (by omega)))
    (fun m v hk => ⟨hk.1.update_below _ hCtrl, hCursor m v hk.2⟩)
  have updated := hintChildToggle_total S H D E header node childNode childSeed col.val (first + sch.m + 1)
    X Y Bc B.workStart B.saveOffset child (r.2 col) keep
    hInfoXY hTogglePos hWord hSizeFit
    hCtrl (by change gate + child.N ≤ dest; rwa [hChildSize]) hDestEnd hGap hRoom
    hTable hReturn hLayout hCount hLocal
    (by
      intro pos hp hb
      change first + sch.m + 1 ≤ pos.val at hp
      change pos.val < first + sch.m + 1 + child.N at hb
      exact hDesc pos (by omega) (by omega))
    hKeep hCursor
  have hCountEq : 1 + sch.m = 1 + child.N := congrArg (fun a => 1 + a) hChildSize.symm
  change HintDecoderPhase S H D E header (first + sch.m) (1 + sch.m)
    (fun m => predicts m ∧ fresh m ∧ keep m) (fun m => predicts m ∧ input m ∧ keep m)
  rw [hCountEq]
  exact (copy.relabel
    (fun m => show (fresh m ∧ predicts m ∧ keep m) ↔ (predicts m ∧ fresh m ∧ keep m) by tauto)
    (fun m => show (raw m ∧ predicts m ∧ keep m) ↔
      (HintBinaryMemory m gate child.N ∧ raw m ∧ keep m) by rw [hChildSize]; unfold predicts; tauto)).append
    (updated.relabel (fun _ => Iff.rfl)
      (fun m => show (HintBinaryMemory m gate child.N ∧ input m ∧ keep m) ↔
        (predicts m ∧ input m ∧ keep m) by rw [hChildSize]))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPrepareChild_total
end -- Def_LinearSetReconciliation327_Main_HintBinaryPrepare20261120

section -- Def_LinearSetReconciliation327_Main_HintPrepareBudget20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintAndRec_value {A B : Prop} {C : Sort*} (f : A → B → C) (h : A ∧ B) :
    And.rec f h = f h.1 h.2 := by
  cases h
  rfl

theorem HintDecoderPhase.cast_budget_follows {S : CRSourceBundle} {H : HintParams}
    {D : HintDecoderTables} {E : RAMEnv} {header first n m : ℕ} {A B : (ℕ → ℕ) → Prop}
    (h : n = m) (p : HintDecoderPhase S H D E header first m A B) (cap : HintTreeEvent → ℕ)
    (hp : HintBudgetFollows D.events first m p.budget cap) :
    HintBudgetFollows D.events first n
      ((cast (congrArg (fun k => HintDecoderPhase S H D E header first k A B) h.symm) p)).budget cap := by
  subst n
  exact hp

theorem HintDecoderPhase.relabel_budget_follows {S : CRSourceBundle} {H : HintParams}
    {D : HintDecoderTables} {E : RAMEnv} {header first n : ℕ} {A B A' B' : (ℕ → ℕ) → Prop}
    (p : HintDecoderPhase S H D E header first n A B) (before : ∀ mem, A mem ↔ A' mem)
    (after : ∀ mem, B mem ↔ B' mem) (cap : HintTreeEvent → ℕ)
    (hp : HintBudgetFollows D.events first n p.budget cap) :
    HintBudgetFollows D.events first n (p.relabel before after).budget cap := hp

theorem hintPrepareChild_total_budget_follows (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node seed first word N X Y t Bc : ℕ)
    (Xs Ys : Fin (H.scheme N X Y).ℓ → ℕ) (children : Fin (H.scheme N X Y).ℓ → Node)
    (r : (Node.recursive (H.scheme N X Y) t Xs Ys children).Seed)
    (col : Fin (H.scheme N X Y).ℓ)
    (payloadOffset : ℕ → ℕ) (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = D.placement.width) (hW : 0 < E.W) (hWord : 16 < 2 ^ E.W)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
    (hChildSize : (children col).N = (H.scheme N X Y).m)
    (hSlice : HintEventSlice D first (hintRecursiveColumnEvents (crFamily S) payloadOffset
      (H.scheme N X Y) children node seed (word * E.W) col)) (base extra : ℕ) :
    let sch := H.scheme N X Y
    let CR := crFamily S
    let L := D.placement
    let child := children col
    let childNode := hintChildPhysicalIndex children node col
    let childSeed := hintChildSchemeIndex children seed col
    let B := L.arena childNode
    let dest := B.payload
    let gate := (L.arena node).transcript + col.val * sch.m
    let words := wordsOf E.W (synLen CR child)
    let table := L.updateTable childNode
    let colBase := hintSubtreeColBase Bc child
    let items := hintChildUpdateSchedule CR Bc colBase child childSeed B.saveOffset
    let predicts := fun m => HintBinaryMemory m gate sch.m
    let fresh := HintFreshWords dest words
    let input := HintPackedMemory E.W dest (synLen CR child)
    ∀
      (hCtrl : D.control + 2 < gate)
      (hGateEnd : gate + sch.m ≤ dest)
      (hDestEnd : dest + (B.saveOffset + 2) ≤ 2 ^ E.W)
      (hGap : words ≤ B.workStart)
      (hRoom : UpSaveRoom B.workStart B.saveOffset child)
      (hInputFit : word * E.W + synLen CR (.recursive sch t Xs Ys children) < 2 ^ E.W)
      (hInputSep : (word * E.W + synLen CR (.recursive sch t Xs Ys children)) / E.W < dest)
      (hTable : table + 3 < 2 ^ E.W)
      (hReturn : E.det (table + 3) = D.control)
      (hLayout : UpSavedLayout E table items)
      (hCount : E.det (table % 2 ^ E.W) % 2 ^ E.W = items.length)
      (hLocal : (∀ i < child.N, UpLocalTree CR (upShiftDetEnv E table) i Bc colBase child (r.2 col) childSeed 0 0))
      (hDesc : (∀ pos : Fin D.events.length, first + sch.m ≤ pos.val → pos.val < first + sch.m + 1 + sch.m →
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 3 < 2 ^ E.W))
      (hKeep : (∀ m m', CRMemFrame dest (dest + B.saveOffset + 2) m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (hCopyCost : 17 * synLen CR child + 13 ≤ extra)
      (hToggleCost : 147 * items.length + 24 ≤ base),
      HintBudgetFollows D.events (first + sch.m) (1 + sch.m) (hintPrepareChild_total S H D E header node seed first word N X Y t Bc Xs Ys children r col payloadOffset keep hWidth hW hWord hInfoXY hChildSize hSlice hCtrl hGateEnd hDestEnd hGap hRoom hInputFit hInputSep hTable hReturn hLayout hCount hLocal hDesc hKeep hCursor).budget
        (fun e => base + (if e.linearWork then extra else 0)) := by
  dsimp only
  intro hCtrl hGateEnd hDestEnd hGap hRoom hInputFit hInputSep hTable hReturn hLayout hCount hLocal hDesc hKeep hCursor
    hCopyCost hToggleCost
  have hParts := hintRecursiveColumn_slice (crFamily S) D payloadOffset (H.scheme N X Y) children node seed
    (word * E.W) first col hSlice
  have hCopy := hParts.2.1
  have hToggle := hParts.2.2.1
  simp only [hintPrepareChild_total, id, hintAndRec_value]
  apply HintDecoderPhase.cast_budget_follows (h := congrArg (fun k => 1 + k) hChildSize.symm)
  apply HintDecoderPhase.append_plain_budget_follows
  · apply HintDecoderPhase.relabel_budget_follows
    intro i hi e he
    have hz : i = 0 := by omega
    subst i
    rw [Nat.add_zero] at he
    have hEq := Option.some.inj (he.symm.trans hCopy)
    subst e
    change 17 * synLen (crFamily S) (children col) + 13 ≤ base + extra
    exact hCopyCost.trans (Nat.le_add_left _ _)
  · apply HintDecoderPhase.relabel_budget_follows
    intro i hi e he
    have hi' : i < (H.scheme N X Y).m := hChildSize ▸ hi
    have hEq := Option.some.inj (he.symm.trans (hToggle i hi'))
    subst e
    exact le_trans hToggleCost (Nat.le_add_right _ _)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPrepareChild_total_budget_follows
end -- Def_LinearSetReconciliation327_Main_HintPrepareBudget20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalBinary20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

set_option maxHeartbeats 800000 in
theorem hintFinalPlaced_binary_step (H : HintParams) (L : HintDecoderPlacement)
    (N X Y node seed descriptor base : ℕ) (j : Fin (H.rows X Y))
    (lr : (H.scheme N X Y).LocalSeed) (J : Finset ℕ)
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
    (∀ a < sch.ℓ, state.mem (A.transcript + j.val + a * sch.m) < 2) →
    (∀ i : Fin N, (lr.1 i).val % sch.m < j.val → state.mem (A.result + i.val) < 2) →
    scratchEnd < 2 ^ E.W →
    scratchEnd ≤ A.transcript →
    A.transcript + j.val + sch.ℓ * sch.m ≤ 2 ^ E.W →
    A.transcript + sch.ℓ * sch.m ≤ A.hints →
    A.hints + N ≤ A.result →
    A.result + N ≤ 2 ^ E.W →
    threshold + (K + 1) * (BY + 1) ≤ 2 ^ E.W →
    Sem P E base (base + hintRunFinal.len) state (fun k out =>
      k ≤ hintFinalCallCost G.gauss Nj maxR ∧ out.regs 14 = L.control ∧
      (∀ i : Fin N, (lr.1 i).val % sch.m < j.val + 1 → out.mem (A.result + i.val) < 2) ∧
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
  let v : HintVec sch.ℓ := fun a =>
    if state.mem (A.transcript + j.val + a.val * sch.m) = 0 then 0 else 1
  have hObs (a : Fin sch.ℓ) :
      state.mem (A.transcript + j.val + a.val * sch.m) = (v a).val := by
    have hBit := hTranscript a.val a.isLt
    change state.mem (A.transcript + j.val + a.val * sch.m) < 2 at hBit
    by_cases h0 : state.mem (A.transcript + j.val + a.val * sch.m) = 0
    · rw [h0]; simp [v, h0]
    · have h1 : state.mem (A.transcript + j.val + a.val * sch.m) = 1 := by omega
      rw [h1]
      simp only [v, h0, if_false]
      rfl
  have hRun := hintRunFinal_sem G.gauss F coords v (lr.2 j) (le_refl _) N G.parent descriptor
    L.control base lr.1 J P E state j rfl hPre hRec hDesc hCtx hControlFit hJ hObs hBYFit hThresh
    hResult hOut hOutAfter hAt hPc
  apply Sem.mono hRun
  rintro k out ⟨hk, hc, hw, hf⟩
  have frame (a : ℕ) (ha : a < L.rowScratch ∨ scratchEnd ≤ a)
      (hn : ∀ i : Fin N, (lr.1 i).val % sch.m = j.val → a ≠ A.result + i.val) :
      out.mem a = state.mem a := by
    apply hf a _ hn
    change a < L.rowScratch + 1 - 1 ∨ scratchEnd ≤ a
    simpa only [Nat.add_sub_cancel] using ha
  refine ⟨hk, hc, ?_, ?_⟩
  · intro i hi
    change (lr.1 i).val % sch.m < j.val + 1 at hi
    by_cases he : (lr.1 i).val % sch.m = j.val
    · have hw' := hw i he
      change out.mem (A.result + i.val) = hintTruth _ at hw'
      rw [hw']
      unfold hintTruth
      split <;> decide
    · change out.mem (A.result + i.val) < 2
      rw [frame (A.result + i.val) (Or.inr (hOutAfter.trans (Nat.le_add_right _ _))) (by
        intro i' hi' heq
        have eq : i = i' := Fin.ext (Nat.add_left_cancel heq)
        exact he (eq.symm ▸ hi'))]
      exact hPrev i (show (lr.1 i).val % sch.m < j.val by omega)
  · intro a ha hb
    change a < A.result ∨ A.result + N ≤ a at hb
    apply frame a ha
    intro i _ he
    have hi := i.isLt
    omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalPlaced_binary_step
end -- Def_LinearSetReconciliation327_Main_HintFinalBinary20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalBinaryRows20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintFinalBinaryRows_phase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header N X Y node seed first : ℕ) (lr : (H.scheme N X Y).LocalSeed)
    (J : Finset ℕ) (keep : (ℕ → ℕ) → Prop)
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
      (fun m => HintBitmap m A.hints N J ∧ HintTranscriptBinary sch A.transcript sch.ℓ m ∧ keep m)
      (fun m => HintBinaryMemory m A.result N ∧ keep m) := by
  let sch := H.scheme N X Y
  let A := D.placement.arena node
  let start := D.placement.rowScratch
  let scratchEnd := hintFinalScratchEnd H start N X Y
  let inv := fun i m => HintBitmap m A.hints N J ∧
    HintTranscriptBinary sch A.transcript sch.ℓ m ∧
    (∀ a : Fin N, (lr.1 a).val % sch.m < i → m (A.result + a.val) < 2) ∧ keep m
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
  let target := fun m => HintBinaryMemory m A.result N ∧ keep m
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
    have hObs (a : ℕ) (ha : a < sch.ℓ) :
        state.mem (A.transcript + j.val + a * sch.m) < 2 := by
      rw [Nat.add_right_comm A.transcript j.val (a * sch.m)]
      exact hT j ⟨a, ha⟩ ha
    have hRun := hintFinalPlaced_binary_step H D.placement N X Y node seed _ base j lr J
      (hintNativeProgram S) E state hInfoN hInfoXY hAt hPc hArg (hCtx.trans hControl.symm) hm hSteps hWord
      hBound hCtrlWord hSeedFit hKFit hStepsFit hBXFit hBYFit hCoeffAddr (hCoeff j) hPerm
      (hintRowLen_le_Nmax H N X Y j) hBlock (fun a => hJ a.val a.isLt) hObs hPrev hSpace hScratch
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
#print axioms LinearSetReconciliation327.Main.hintFinalBinaryRows_phase
end -- Def_LinearSetReconciliation327_Main_HintFinalBinaryRows20261120

section -- Def_LinearSetReconciliation327_Main_HintRowCostCap20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintScanCostCap (U : ℕ) : ℕ :=
  11 * U * U + 23 * U + 52 + (9 * U + 23 + (20 * U + 50) * U + 512 * (U + U + 1) ^ 3)

def hintRowIterationCap (U R : ℕ) : ℕ :=
  50 * U + 200 + 2 * ((hintScanCostCap U + 2) * (U + 1) ^ R)

def hintRowCallCap (U R : ℕ) : ℕ :=
  let B := (R + 1) * hintRowIterationCap U R
  (B + 2) * (R + 1) + B + 64 * U + 8 * R + 470

theorem hintRowCallCost_le (G : HintGaussArea) (Nj maxR U R : ℕ)
    (hA : G.rows ≤ U) (hH : G.hints ≤ U) (hNj : Nj ≤ U) (hR : maxR ≤ R)
    (hRU : R ≤ U) :
    hintPredictCallCost G Nj maxR ≤ hintRowCallCap U R ∧
      hintFinalCallCost G Nj maxR ≤ hintRowCallCap U R := by
  have hBody (r : ℕ) (hr : r ≤ R) : hintScanBodyTime G r ≤ hintScanCostCap U := by
    have hu := hr.trans hRU
    unfold hintScanBodyTime hintScanCostCap
    gcongr
  have hPow (r : ℕ) (hr : r ≤ R) : Nj ^ r ≤ (U + 1) ^ R :=
    (Nat.pow_le_pow_left (hNj.trans (Nat.le_add_right _ _)) _).trans
      (pow_le_pow_right₀ (by omega) hr)
  have hFull (r : ℕ) (hr : r ≤ R) :
      (hintScanBodyTime G r + 2) * Nj ^ r ≤ (hintScanCostCap U + 2) * (U + 1) ^ R :=
    Nat.mul_le_mul (Nat.add_le_add_right (hBody r hr) 2) (hPow r hr)
  have hPredict (r : ℕ) (hr : r ≤ R) :
      hintRowOuterStepTime G Nj r ≤ hintRowIterationCap U R := by
    unfold hintRowOuterStepTime hintRowIterationCap
    have hSmall : 7 * Nj + 20 * G.hints + 23 * r + 152 ≤ 50 * U + 200 := by
      have hu := hr.trans hRU
      omega
    exact Nat.add_le_add hSmall (Nat.mul_le_mul_left _ (hFull r hr))
  have hFinal (r : ℕ) (hr : r ≤ R) :
      hintFinalBodyTime G Nj r ≤ hintRowIterationCap U R := by
    unfold hintFinalBodyTime hintRowIterationCap
    have hSmall : 7 * r + 73 ≤ 50 * U + 200 := by
      have hu := hr.trans hRU
      omega
    exact Nat.add_le_add hSmall ((hFull r hr).trans (by omega))
  let B := (R + 1) * hintRowIterationCap U R
  have hSum (f : ℕ → ℕ) (hf : ∀ r ≤ R, f r ≤ hintRowIterationCap U R) :
      ∑ r ∈ Finset.range (maxR + 1), f r ≤ B := by
    calc
      _ ≤ ∑ _ ∈ Finset.range (maxR + 1), hintRowIterationCap U R := by
        apply Finset.sum_le_sum
        intro r hr
        exact hf r (Nat.le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hr)) hR)
      _ = (maxR + 1) * hintRowIterationCap U R := by simp
      _ ≤ B := Nat.mul_le_mul_right _ (Nat.succ_le_succ hR)
  have hPB : hintRowOuterBudget G Nj maxR ≤ B := hSum _ hPredict
  have hFB : hintFinalBudget G Nj maxR ≤ B := hSum _ hFinal
  have hP := Nat.mul_le_mul (Nat.add_le_add_right hPB 2) (Nat.succ_le_succ hR)
  have hF := Nat.mul_le_mul (Nat.add_le_add_right hFB 2) (Nat.succ_le_succ hR)
  change (hintRowOuterBudget G Nj maxR + 2) * (maxR + 1) ≤ (B + 2) * (R + 1) at hP
  change (hintFinalBudget G Nj maxR + 2) * (maxR + 1) ≤ (B + 2) * (R + 1) at hF
  change (_ : ℕ) ≤ (B + 2) * (R + 1) + B + 64 * U + 8 * R + 470 ∧
    (_ : ℕ) ≤ (B + 2) * (R + 1) + B + 64 * U + 8 * R + 470
  constructor
  · unfold hintPredictCallCost
    omega
  · unfold hintFinalCallCost
    omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowCallCost_le
end -- Def_LinearSetReconciliation327_Main_HintRowCostCap20261120

section -- Def_LinearSetReconciliation327_Main_HintRowPhaseBudget20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintPredictBinaryRows_budget_le (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
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
    (hPerm : ∀ i : Fin N, E.permInv seed i.val = (lr.1.symm i).val) (U R : ℕ) (hK : H.Nmax N X Y ≤ U) (hL : H.ell N X Y ≤ U)
    (hR : H.BY N X Y ≤ R) (hRU : R ≤ U) :
    let sch := H.scheme N X Y
    let A := D.placement.arena node
    let start := D.placement.rowScratch
    let scratchEnd := hintPredictScratchEnd H start N X Y col.val
    let dest := A.transcript + col.val * sch.m
    let abstention := (D.placement.arena child).hints
    ∀
      (hCtrlStart : D.control + 2 < start)
      (hCtrlTran : D.control + 2 < A.transcript)
      (hSpace : scratchEnd < 2 ^ E.W)
      (hScratch : scratchEnd ≤ A.transcript)
      (hTran : A.transcript + sch.ℓ * sch.m ≤ A.hints)
      (hHint : A.hints + N ≤ abstention)
      (hAbstain : abstention + sch.m ≤ 2 ^ E.W)
      (hThreshold : (∀ j : Fin (H.rows X Y),
              let threshold := D.placement.threshold node j.val
              let block := hintWaitDetBlock (H.Nmax N X Y) (rowLen N (H.rows X Y) j.val)
                (H.BY N X Y) (H.ell N X Y) (H.c N X Y)
              block.At E threshold ∧ threshold + block.length ≤ 2 ^ E.W))
      (hDescriptors : (∀ p : Fin D.events.length, first ≤ p.val → p.val < first + sch.m →
              hintEventDescriptor header D.events (hintEventRecord S H D.placement) p.val + 31 ≤ 2 ^ E.W))
      (hKeep : (∀ m m', (∀ a, (a < start ∨ scratchEnd ≤ a) →
              (a < dest ∨ dest + sch.m ≤ a) → (a < abstention ∨ abstention + sch.m ≤ a) →
                m' a = m a) → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (j : Fin sch.m),
      (hintPredictBinaryRows_phase S H D E header N X Y node child seed first lr J col keep
        hInfoN hInfoXY hChild hControl hMap hm hSteps hWord hSeedFit hKFit
        hStepsFit hBXFit hBYFit hCoeffSpace hCoeff hPerm hCtrlStart hCtrlTran hSpace hScratch hTran hHint hAbstain hThreshold hDescriptors hKeep hCursor).budget j.val ≤ hintRowCallCap U R := by
  dsimp only
  intro hCtrlStart hCtrlTran hSpace hScratch hTran hHint hAbstain hThreshold hDescriptors hKeep hCursor j
  let sch := H.scheme N X Y
  let Nj := rowLen N sch.m j.val
  let h := (hintRowMembers N sch.m j.val lr.1 J).length
  let a := col.val
  let w := hintRowWorkspace D.placement.rowScratch a (H.Nmax N X Y) (H.BY N X Y) seed j.val sch.ℓ h
  have hNj : Nj ≤ H.Nmax N X Y := hintRowLen_le_Nmax H N X Y j
  have hHints : h ≤ Nj := hintGatherList_length_le _ _
  have hA : w.gauss.rows ≤ U := col.isLt.le.trans hL
  have hR' : min (H.BY N X Y) (Nj - h) ≤ R := (min_le_left _ _).trans hR
  change hintPredictCallCost w.gauss Nj (min (H.BY N X Y) (Nj - h)) ≤ _
  exact (hintRowCallCost_le w.gauss Nj _ U R hA (hHints.trans (hNj.trans hK)) (hNj.trans hK) hR' hRU).1

theorem hintFinalBinaryRows_budget_le (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header N X Y node seed first : ℕ) (lr : (H.scheme N X Y).LocalSeed)
    (J : Finset ℕ) (keep : (ℕ → ℕ) → Prop)
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
    (hPerm : ∀ i : Fin N, E.permInv seed i.val = (lr.1.symm i).val) (U R : ℕ) (hK : H.Nmax N X Y ≤ U) (hL : H.ell N X Y ≤ U)
    (hR : H.BY N X Y ≤ R) (hRU : R ≤ U) :
    let sch := H.scheme N X Y
    let A := D.placement.arena node
    let start := D.placement.rowScratch
    let scratchEnd := hintFinalScratchEnd H start N X Y
    ∀
      (hCtrlStart : D.control + 2 < start)
      (hCtrlTran : D.control + 2 < A.transcript)
      (hSpace : scratchEnd < 2 ^ E.W)
      (hScratch : scratchEnd ≤ A.transcript)
      (hTran : A.transcript + sch.ℓ * sch.m ≤ A.hints)
      (hHint : A.hints + N ≤ A.result)
      (hOut : A.result + N ≤ 2 ^ E.W)
      (hThreshold : (∀ j : Fin (H.rows X Y),
              D.placement.threshold node j.val + (H.Nmax N X Y + 1) * (H.BY N X Y + 1) ≤ 2 ^ E.W))
      (hDescriptors : (∀ j : Fin D.events.length, first ≤ j.val → j.val < first + sch.m →
              hintEventDescriptor header D.events (hintEventRecord S H D.placement) j.val + 31 ≤ 2 ^ E.W))
      (hKeep : (∀ m m', (∀ a, (a < start ∨ scratchEnd ≤ a) → (a < A.result ∨ A.result + N ≤ a) → m' a = m a) →
              keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (j : Fin sch.m),
      (hintFinalBinaryRows_phase S H D E header N X Y node seed first lr J keep
        hInfoN hInfoXY hControl hMap hmPos hm hSteps hWord hSeedFit hKFit
        hStepsFit hBXFit hBYFit hCoeffSpace hCoeff hPerm hCtrlStart hCtrlTran hSpace hScratch hTran hHint hOut hThreshold hDescriptors hKeep hCursor).budget j.val ≤ hintRowCallCap U R := by
  dsimp only
  intro hCtrlStart hCtrlTran hSpace hScratch hTran hHint hOut hThreshold hDescriptors hKeep hCursor j
  let sch := H.scheme N X Y
  let Nj := rowLen N sch.m j.val
  let h := (hintRowMembers N sch.m j.val lr.1 J).length
  let a := sch.ℓ
  let w := hintRowWorkspace D.placement.rowScratch a (H.Nmax N X Y) (H.BY N X Y) seed j.val sch.ℓ h
  have hNj : Nj ≤ H.Nmax N X Y := hintRowLen_le_Nmax H N X Y j
  have hHints : h ≤ Nj := hintGatherList_length_le _ _
  have hA : w.gauss.rows ≤ U := hL
  have hR' : min (H.BY N X Y) (Nj - h) ≤ R := (min_le_left _ _).trans hR
  change hintFinalCallCost w.gauss Nj (min (H.BY N X Y) (Nj - h)) ≤ _
  exact (hintRowCallCost_le w.gauss Nj _ U R hA (hHints.trans (hNj.trans hK)) (hNj.trans hK) hR' hRU).2

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPredictBinaryRows_budget_le
#print axioms LinearSetReconciliation327.Main.hintFinalBinaryRows_budget_le
end -- Def_LinearSetReconciliation327_Main_HintRowPhaseBudget20261120

section -- Def_LinearSetReconciliation327_Main_HintResidualTablePlaced20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintResidualTable_placed (S : CRSourceBundle) (H : HintParams) (R : Node)
    (seedData : (hintSpec R).Seed) (W : ℕ) (det : ℕ → ℕ)
    (N t Bc control detBase : ℕ) (hW : 0 < W) (hWord : 16 < 2 ^ W)
    (hFit : (hintSpec R).Fits W) (hN : N < 2 ^ W)
    (hCols : UpCRColumns (crFamily S) Bc N t) (hBc : Bc + 1 < 2 ^ W) :
    let E := (hintSpec R).env W det seedData
    let CR := crFamily S
    let leaf := Node.cr N t
    let words := wordsOf W (synLen CR leaf)
    let colBase := hintSubtreeColBase Bc leaf
    let items := hintChildUpdateSchedule CR Bc colBase leaf 0 words
    words + 1 < 2 ^ W →
    synLen CR leaf < 2 ^ W →
    detBase + colBase + upTabLen Bc leaf < 2 ^ W →
    (hintSubtreeBlock CR W control Bc leaf 0 words).At E detBase →
    UpSavedLayout E detBase items ∧
      E.det (detBase % 2 ^ W) % 2 ^ W = items.length ∧ E.det (detBase + 3) = control ∧
      ∀ i < N, UpLocalTree CR (upShiftDetEnv E detBase) i Bc colBase leaf () 0 0 0 := by
  let E := (hintSpec R).env W det seedData
  let CR := crFamily S
  let leaf := Node.cr N t
  let words := wordsOf W (synLen CR leaf)
  let colBase := hintSubtreeColBase Bc leaf
  let items := hintChildUpdateSchedule CR Bc colBase leaf 0 words
  dsimp only
  intro hSav hBits hSpace hAt
  change words + 1 < 2 ^ W at hSav
  change synLen CR leaf < 2 ^ W at hBits
  change detBase + colBase + upTabLen Bc leaf < 2 ^ W at hSpace
  have hEnd : colBase + upTabLen Bc leaf < 2 ^ W := by omega
  have hTotal : detBase + (colBase + upTabLen Bc leaf) ≤ 2 ^ W := by omega
  have hSched : items = upSched CR Bc colBase leaf 0 0 0 words [] := by
    simp only [items, hintChildUpdateSchedule, upSched_decomp, upHead_zero, List.nil_append,
      List.singleton_append]
  have hFields : ∀ it ∈ items, ∀ f < 16, it.fld f < 2 ^ E.W := by
    intro it hi f hf
    rw [hSched] at hi
    let cap := 2 ^ W - 1
    have hDim : UpDimsBound cap leaf := by change N ≤ cap; dsimp [cap]; omega
    have hNum : 0 + (schemeNodes leaf).length ≤ cap := by change 0 ≤ cap; omega
    have hF := upSched_fields_le CR Bc colBase cap (by dsimp [cap]; omega) (by dsimp [cap]; omega)
      leaf 0 0 0 words [] hDim hNum
      (by change 0 + synLen CR leaf ≤ cap; dsimp only [cap]; omega)
      (by change colBase + 0 + upTabLen Bc leaf ≤ cap; dsimp only [cap]; omega)
      (by dsimp only [cap]; omega)
      (by simp) it hi f hf
    change it.fld f < 2 ^ W
    dsimp only [cap] at hF
    omega
  have hValid : ∀ it ∈ items, UpItemKind it ∧ it.sav + 1 < 2 ^ E.W := by
    rw [hSched]
    exact upSched_valid_records CR Bc colBase leaf 0 0 0 words W hSav hBc
  have hSpecs := hintSubtreeBlock_specs CR E control Bc leaf 0 words detBase hAt hEnd hTotal
    hFields (fun it hi => (hValid it hi).1) (fun it hi _ => (hValid it hi).2)
  refine ⟨hSpecs.1, hSpecs.2.1, hSpecs.2.2, ?_⟩
  intro i hi
  have hBlock : BlockOf R 0 (schemeNodes leaf) := by
    intro j hj
    have h : j < 0 := hj
    omega
  have hStatic : UpTreeStatic CR Bc N leaf := ⟨le_rfl, hCols⟩
  have hAt' : ∀ q < colBase + upTabLen Bc leaf,
      det (detBase + q) = hintSubtreeDet W control colBase items (upTabFun CR Bc leaf 0) q := hAt
  exact hintSubtreeLocal_of_placed CR H R leaf (.cr N t) seedData W det detBase control Bc colBase N i 0
    items (upTabFun CR Bc leaf 0) (by omega) hW hFit (by unfold colBase hintSubtreeColBase; omega)
    hN.le hBlock hStatic (upTabFullTree_self CR Bc leaf 0) hEnd hBits hTotal hAt'

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintResidualTable_placed
end -- Def_LinearSetReconciliation327_Main_HintResidualTablePlaced20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedBinaryTail20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintPlacedRowTail_total (S : CRSourceBundle) (H : HintParams)
    {R T : Node} (hR : IsSchemeTree H R) (hT : IsSchemeTree H T)
    (seedData : (hintSpec R).Seed) (up previous : ℕ → ℕ)
    (W Bc header node seed first offset N X Y t : ℕ)
    (lr : (H.scheme N X Y).LocalSeed) (J : Finset ℕ) (keep : (ℕ → ℕ) → Prop)
    (hHeader : 3 < header) (hW : 0 < W) (hWord : 30 < 2 ^ W) (hBc : Bc + 1 < 2 ^ W)
    (hFit : (hintSpec R).Fits W) (hSeed : seed < 2 ^ W)
    (hK : H.Nmax N X Y < 2 ^ W) (hEll : H.ell N X Y < 2 ^ W)
    (hBX : H.BX N X Y < 2 ^ W) (hBY : H.BY N X Y + 1 < 2 ^ W)
    (hmPos : 0 < H.rows X Y) (hm : H.rows X Y ≤ N) (hSteps : 0 < H.ell N X Y)
    (ht : t ≤ N)
    (hSmall : (S.data N t).W + 1 < W) (hCR : UpCRColumns (crFamily S) Bc N t) :
    let D := hintDecoderTables S H hR W Bc header
    let A := D.placement.arena node
    let E := (hintSpec R).env W (D.det S H up previous header R.N) seedData
    let sch := H.scheme N X Y
    let word := D.placement.inputWord node
    let arena := hintArenaStart D.heap D.stride
    let ownFresh := fun (mem : ℕ → ℕ) => ∀ a, A.result ≤ a → a < arena (node + 1) → mem a = 0
    HintPlacedSubtree (crFamily S) H D hT node seed →
    (D.placement.info node).universeSize = N → (D.placement.info node).rowParams = some (X, Y) →
    (D.placement.info node).residualCapacity = t →
    (node = 0 → synLen (crFamily S) T ≤ synLen (crFamily S) R) →
    arena D.infos.length * W < 2 ^ W → hintDecoderDetEnd S H D header < 2 ^ W →
    offset + (S.data N t).R = word * W + synLen (crFamily S) T →
    (∀ (j : Fin (H.rows X Y)) (q : Fin (H.Nmax N X Y)) (s : Fin (H.ell N X Y)),
      E.coeff seed (j.val * H.ell N X Y * H.Nmax N X Y + q.val + s.val * H.Nmax N X Y) =
        (lr.2 j s q).val) →
    (∀ i : Fin N, E.permInv seed i.val = (lr.1.symm i).val) →
    H.rows X Y * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ W →
    (∀ q < sch.m, D.events[first + q]? = some (.finishRow node seed q)) →
    HintEventSlice D (first + sch.m) (hintResidualEvents (crFamily S) node offset sch.N t) →
    (∀ m m', HintSubtreeFrame D node T.nodeCount m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first (sch.m + (1 + sch.N + 1 + 1))
      (fun m => HintBitmap m A.hints N J ∧ HintTranscriptBinary sch A.transcript sch.ℓ m ∧
        ownFresh m ∧ keep m)
      (fun m => HintBinaryMemory m A.result N ∧ keep m) := by
  let D := hintDecoderTables S H hR W Bc header
  let L := D.placement
  let A := L.arena node
  let det := D.det S H up previous header R.N
  let E := (hintSpec R).env W det seedData
  let sch := H.scheme N X Y
  let word := L.inputWord node
  let arena := hintArenaStart D.heap D.stride
  let maxAddr := arena D.infos.length
  let last := arena (node + T.nodeCount)
  let ownFresh := fun (mem : ℕ → ℕ) => ∀ a, A.result ≤ a → a < arena (node + 1) → mem a = 0
  let data := S.data N t
  let words := wordsOf W data.R
  let spill := A.crRegisters + 16
  let spillSize := 2 ^ (data.W + 1) + 1
  let rowKeep := fun m => HintFreshWords A.residual words m ∧ HintFreshWords spill spillSize m ∧ keep m
  let bitmap := fun m => HintBitmap m A.hints N J
  let transcript := HintTranscriptBinary sch A.transcript sch.ℓ
  dsimp only
  intro hp hInfoN hInfoXY hInfoT hRoot hMem hDet hOffset hCoeff hPerm hCoeffSpace hRows hSlice hKeep hCursor
  change maxAddr * W < 2 ^ W at hMem
  change hintDecoderDetEnd S H D header < 2 ^ W at hDet
  change offset + data.R = word * W + synLen (crFamily S) T at hOffset
  have hInfo : (L.info node).universeSize = N := hInfoN
  have hMemA := hintDecoderTables_placedMemory S H hR hT W Bc header node seed hp hRoot
  have hSpan : node + T.nodeCount ≤ D.infos.length := hp.span
  have hn : node < D.infos.length := by have := hintNodeCount_pos T; omega
  let i : Fin D.infos.length := ⟨node, hn⟩
  have hLast : last ≤ maxAddr := hintArenaStart_mono D.heap D.stride hSpan
  have hAEnd : A.limit ≤ last := hMemA.own.trans hMemA.finish
  have hAFit : A.limit < 2 ^ W := by
    have hLe : maxAddr ≤ maxAddr * W := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left maxAddr (show 1 ≤ W from hW)
    exact (hAEnd.trans (hLast.trans hLe)).trans_lt hMem
  have hShape := hintArenaFor_rowOrder S H W (L.info node) (arena node) N X Y t hInfoN hInfoT hInfoXY
  change A.transcript + sch.m * sch.ℓ ≤ A.hints ∧ A.hints + N < A.result ∧ A.result + N < A.residual ∧
    A.residual + words + 2 ≤ A.residualBitmap + 1 ∧ A.residualBitmap + N < A.crRegisters ∧
    A.limit = spill + spillSize + crSourceSteps S N t + 1 at hShape
  obtain ⟨hTran, hHint, hRes, hBitmap, hCRReg, hEnd⟩ := hShape
  have hTran' : A.transcript + sch.ℓ * sch.m ≤ A.hints := by rw [Nat.mul_comm]; exact hTran
  have hSpill : A.crRegisters + 16 = spill := rfl
  have hSpillEnd : spill + spillSize ≤ A.limit := by rw [hEnd]; omega
  have hSpillFit : spill + spillSize + crSourceSteps S N t + 1 < 2 ^ W := hEnd ▸ hAFit
  have hSrcSpace : A.transcript ≤ A.result := by omega
  have hN : 1 ≤ N := by omega
  have hRegsSpill : A.crRegisters ≤ spill := hSpill ▸ Nat.le_add_right _ _
  have hResEnd : A.residual + words ≤ A.limit := by
    have h : A.residual + words ≤ A.residualBitmap + 1 :=
      (Nat.le_add_right _ 2).trans hBitmap
    exact h.trans ((Nat.add_le_add_left hN _).trans
      (hCRReg.le.trans (hRegsSpill.trans ((Nat.le_add_right _ _).trans hSpillEnd))))
  have hHeapTran : D.listBase ≤ A.transcript := hMemA.heap.trans
    ((hMemA.payload ▸ Nat.le_add_right _ _ : D.heap ≤ A.payload).trans hMemA.transcript)
  have hCtrl : D.control + 2 < A.transcript := hMemA.scratch.trans_le (hMemA.list.trans hHeapTran)
  have hInfoAt : L.info node = D.infos[i.val] := by
    change D.infos[node]?.getD _ = _
    rw [List.getElem?_eq_getElem hn, Option.getD_some]
  have hWork : hintFinalScratchEnd H L.rowScratch N X Y ≤ D.listBase :=
    hintDecoderTables_rowScratch S H hR W Bc header N X Y sch.ℓ 0 0 (H.Nmax N X Y)
      le_rfl i (hInfoAt ▸ hInfoN) (hInfoAt ▸ hInfoXY)
  have hWorkTran := hWork.trans hHeapTran
  have hWorkFit := (hWorkTran.trans hSrcSpace).trans_lt (by omega : A.result < 2 ^ W)
  obtain ⟨upTable, crTable, thresholds⟩ := hintDecoderTables_rowAux S H hR E up previous W Bc header N X Y t
    hHeader rfl i hInfoN hInfoT hInfoXY
  have hTableEnd : L.residualTable node + hintSubtreeColBase Bc (.cr N t) + upTabLen Bc (.cr N t) < 2 ^ W := by
    have hh := upTable.2.trans_lt hDet
    change L.residualTable node + (hintSubtreeColBase Bc (.cr N t) + upTabLen Bc (.cr N t)) < 2 ^ W at hh
    omega
  have hTable3 : L.residualTable node + 3 < 2 ^ W := by unfold hintSubtreeColBase at hTableEnd; omega
  have hCrSpace : L.crTable node + 2 ^ data.W < 2 ^ W := by
    have hh := crTable.2.trans_lt hDet
    change L.crTable node + (2 ^ data.W + 1) < 2 ^ W at hh
    omega
  have hPackBound : word + wordsOf W (synLen (crFamily S) T) ≤ A.transcript := hMemA.packed
  have hSourceFit : offset + data.R < 2 ^ W := by
    rw [hOffset]
    exact hintWordSpan_lt W _ _ maxAddr hW (hPackBound.trans (hSrcSpace.trans (by omega))) hMem
  have hResidualFit : A.residual * W + data.R < 2 ^ W :=
    hintWordSpan_lt W _ _ maxAddr hW (hResEnd.trans (hAEnd.trans hLast)) hMem
  have hSeparate : (A.residual * W + data.R) / W < spill := by
    rw [Nat.mul_comm A.residual W, Nat.mul_add_div hW]
    have h := Nat.div_le_div_right (c := W) (up_words_cover_budget W data.R hW)
    rw [Nat.mul_comm (wordsOf W data.R), Nat.mul_div_cancel_left _ hW] at h
    change data.R / W ≤ words at h
    omega
  have hStage : HintStagePre E W data.R offset A.residual := by
    refine ⟨by change 1 < 2 ^ W; omega, hW, le_rfl, hSourceFit, by change A.residual + words ≤ 2 ^ W; omega, ?_⟩
    change (offset + data.R) / W < A.residual
    rw [hOffset]
    exact (hMemA.readable hW).trans_le (hSrcSpace.trans ((Nat.le_add_right _ N).trans hRes.le))
  obtain ⟨hLayout, hCount, hReturn, hLocal⟩ := hintResidualTable_placed S H R seedData W det N t Bc
    D.control (L.residualTable node) hW (by omega) hFit (by omega) hCR hBc
    (show words + 1 < 2 ^ W by omega) (show data.R < 2 ^ W by omega) hTableEnd upTable.1
  have hDesc (j : Fin D.events.length) :
      hintEventDescriptor header D.events (hintEventRecord S H L) j.val +
        D.events[j.val].recordLength < 2 ^ W := by
    rw [← hintEventRecord_length S H L]
    exact (hintDecoderEvent_end S H D header j).trans_lt hDet
  have hRowDesc (j : Fin D.events.length) (h0 : first ≤ j.val) (h1 : j.val < first + sch.m) :
      hintEventDescriptor header D.events (hintEventRecord S H L) j.val + 31 ≤ 2 ^ W := by
    have eq : D.events[j.val]? = some (.finishRow node seed (j.val - first)) := by
      nth_rw 1 [show j.val = first + (j.val - first) by omega]
      exact hRows _ (by change j.val - first < sch.m; omega)
    have hj := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) j.isLt).symm.trans eq)
    have hd := hDesc j
    rw [hj] at hd
    exact hd.le
  have hOwnFrame (m m' : ℕ → ℕ)
      (hf : ∀ a, (a < L.rowScratch ∨ D.listBase ≤ a) →
        (a < A.result ∨ A.limit ≤ a) → m' a = m a) (hk : keep m) : keep m' := by
    apply hKeep m m' ?_ hk
    intro a hs ho
    have hBase : A.payload = arena node := hMemA.payload
    have hLo : arena node ≤ A.result := by rw [← hBase]; exact hMemA.transcript.trans hSrcSpace
    exact hf a hs (ho.imp (fun h => h.trans_le hLo) (fun h => hAEnd.trans h))
  let rows := hintFinalBinaryRows_phase S H D E header N X Y node seed first lr J rowKeep
    hInfoN hInfoXY rfl hRows hmPos hm hSteps hWord hSeed hK hEll hBX hBY hCoeffSpace hCoeff hPerm
    hMemA.scratch hCtrl hWorkFit hWorkTran hTran' hHint.le
    (show A.result + N ≤ 2 ^ W by omega)
    (fun k => ((thresholds k).2.trans_lt hDet).le) hRowDesc
    (by
      intro m m' hf hk
      have frame : ∀ a, (a < L.rowScratch ∨ hintFinalScratchEnd H L.rowScratch N X Y ≤ a) →
          (a < A.result ∨ A.result + N ≤ a) → m' a = m a := hf
      refine ⟨hk.1.frame (fun q _ => frame _ (Or.inr (by omega)) (Or.inr (by omega))),
        hk.2.1.frame (fun q _ => frame _ (Or.inr (by omega)) (Or.inr (by omega))), ?_⟩
      exact hOwnFrame m m' (fun a hs ho => frame a (hs.imp id (hWork.trans ·))
        (ho.imp id (by omega))) hk.2.2)
    (fun m v h => ⟨h.1.update_below _ _ (by omega), h.2.1.update_below _ _ (by omega),
      hCursor m v h.2.2⟩)
  let residual := hintNodeResidual_total S H D E header node (first + sch.m) offset Bc t N keep
    rfl hW rfl hInfo (show 1 ≤ N by omega) ht (by omega : 16 < 2 ^ W) hSlice
    (show D.control + 2 < A.result by omega) hRes.le hBitmap hCRReg hSpillFit hStage
    hTable3 hReturn hLayout hCount hLocal hSmall hCrSpace hResidualFit hSeparate crTable.1 hDesc
    (by
      intro m m' hf hk
      have frame : CRMemFrame A.result A.limit m m' := hEnd ▸ hf
      exact hOwnFrame m m' (fun a _ ha => frame a ha) hk)
    hCursor
  let complete := rows.append residual
  have hHintsCtrl : D.control + 2 < A.hints := by omega
  have hResultCtrl : D.control + 2 < A.result := by omega
  have hResidualFresh (m : ℕ → ℕ) (hf : ownFresh m) : HintFreshWords A.residual words m := by
    intro q hq
    exact hf (A.residual + q) (by omega) (by
      have he : A.limit ≤ arena (node + 1) := hMemA.own
      omega)
  have hSpillFresh (m : ℕ → ℕ) (hf : ownFresh m) : HintFreshWords spill spillSize m := by
    intro q hq
    exact hf (spill + q) (by omega) (by
      have he : A.limit ≤ arena (node + 1) := hMemA.own
      omega)
  change HintDecoderPhase S H D E header first (sch.m + (1 + sch.N + 1 + 1))
    (fun m => bitmap m ∧ transcript m ∧ ownFresh m ∧ keep m)
    (fun m => HintBinaryMemory m A.result N ∧ keep m)
  refine complete.adapt (by omega) ?_ (fun _ h => h) ?_ ?_
  · rintro m ⟨hh, ht, hf, hk⟩
    exact ⟨hh, ht, hResidualFresh m hf, hSpillFresh m hf, hk⟩
  · rintro m v ⟨hh, ht, hf, hk⟩
    refine ⟨hh.update_below _ _ hHintsCtrl, ?_, ?_, hCursor m v hk⟩
    · intro j s hs
      rw [Function.update_of_ne (by unfold hintTranscriptCell; omega)]
      exact ht j s hs
    · intro a ha hb
      change A.result ≤ a at ha
      rw [Function.update_of_ne (Nat.ne_of_gt (hResultCtrl.trans_le ha))]
      exact hf a ha hb
  · rintro m v ⟨hx, hk⟩
    exact ⟨hx.update_below _ hResultCtrl, hCursor m v hk⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedRowTail_total
end -- Def_LinearSetReconciliation327_Main_HintPlacedBinaryTail20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedBinaryDirect20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintPlacedDirect_total (S : CRSourceBundle) (H : HintParams)
    {R : Node} (hR : IsSchemeTree H R) (seedData : (hintSpec R).Seed)
    (up previous : ℕ → ℕ) (W Bc header node seed first N X Y t : ℕ)
    (J : Finset ℕ)
    (hHeader : 3 < header) (hW : 0 < W) (hWord : 30 < 2 ^ W) (hBc : Bc + 1 < 2 ^ W)
    (hFit : (hintSpec R).Fits W) (hSeed : seed < 2 ^ W)
    (hK : H.Nmax N X Y < 2 ^ W) (hEll : H.ell N X Y < 2 ^ W)
    (hBX : H.BX N X Y < 2 ^ W) (hBY : H.BY N X Y + 1 < 2 ^ W)
    (hmPos : 0 < H.rows X Y) (hm : H.rows X Y ≤ N) (hSteps : 0 < H.ell N X Y)
    (ht : t ≤ N)
    (hSmall : (S.data N t).W + 1 < W) (hCR : UpCRColumns (crFamily S) Bc N t) :
    let sch := H.scheme N X Y
    let T := Node.direct sch t
    let D := hintDecoderTables S H hR W Bc header
    let E := (hintSpec R).env W (D.det S H up previous header R.N) seedData
    let offsets := fun i => D.placement.inputWord i * W
    BlockOf R seed (schemeNodes T) →
    HintPlacedSubtree (crFamily S) H D (.direct N X Y t) node seed →
    (node = 0 → synLen (crFamily S) T ≤ synLen (crFamily S) R) →
    hintArenaStart D.heap D.stride D.infos.length * W < 2 ^ W →
    hintDecoderDetEnd S H D header < 2 ^ W →
    HintEventSlice D first (hintTreeEvents (crFamily S) offsets T node seed (offsets node)) →
    ∀ keep : (ℕ → ℕ) → Prop,
      (∀ m m', HintSubtreeFrame D node T.nodeCount m m' → keep m → keep m') →
      (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
      HintDecoderPhase S H D E header first (hintTreeEvents (crFamily S) offsets T node seed (offsets node)).length
        (fun m => (HintBitmap m (D.placement.arena node).hints N J ∧ HintNodeFreshTail D node T.nodeCount m) ∧ keep m)
        (fun m => HintBinaryMemory m (D.placement.arena node).result N ∧ keep m) := by
  let sch := H.scheme N X Y
  let CR := crFamily S
  let T := Node.direct sch t
  let hT : IsSchemeTree H T := .direct N X Y t
  let D := hintDecoderTables S H hR W Bc header
  let L := D.placement
  let det := D.det S H up previous header R.N
  let E := (hintSpec R).env W det seedData
  let arena := hintArenaStart D.heap D.stride
  let maxAddr := arena D.infos.length
  let A := L.arena node
  let word := L.inputWord node
  let offsets := fun i => L.inputWord i * W
  let r := hintKappaAux H R seedData T hT seed
  let readCount := sch.m * sch.ℓ
  let prelude_ := hintDirectReads sch node (word * W)
  let offset := word * W + readCount
  let parentHints := fun m => HintBitmap m A.hints N J
  let transcript := HintTranscriptBinary sch A.transcript sch.ℓ
  let ownFresh := fun (m : ℕ → ℕ) => ∀ a, A.result ≤ a → a < arena (node + 1) → m a = 0
  dsimp only
  intro hBlock hPlaced hRoot hMem hDet hSlice keep hKeep hCursor
  change maxAddr * W < 2 ^ W at hMem
  change hintDecoderDetEnd S H D header < 2 ^ W at hDet
  have hAM := hintDecoderTables_placedMemory S H hR hT W Bc header node seed hPlaced hRoot
  have hSpan : node + 1 ≤ D.infos.length := hPlaced.span
  have hAEnd : A.limit ≤ maxAddr := hAM.own.trans (hintArenaStart_mono D.heap D.stride hSpan)
  have hAFit : A.limit < 2 ^ W := by
    have hLe : maxAddr ≤ maxAddr * W := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left maxAddr (show 1 ≤ W from hW)
    exact (hAEnd.trans hLe).trans_lt hMem
  have hInfo : L.info node = hintNodeInfo CR hT node seed :=
    HintPlacedSubtree.info S H hR hT W Bc header node seed hPlaced
  have hInfoN : (L.info node).universeSize = N := by rw [hInfo]; rfl
  have hInfoXY : (L.info node).rowParams = some (X, Y) := by rw [hInfo]; rfl
  have hInfoT : (L.info node).residualCapacity = t := by rw [hInfo]; rfl
  have hPay : A.payload = arena node := hAM.payload
  have hTranLo : arena node ≤ A.transcript := by rw [← hPay]; exact hAM.transcript
  have hCtrl : D.control + 2 < A.transcript :=
    hAM.scratch.trans_le (hAM.list.trans (hAM.heap.trans ((Nat.le_add_right _ _).trans hTranLo)))
  have hShape := hintArenaFor_rowOrder S H W (L.info node) (arena node) N X Y t hInfoN hInfoT hInfoXY
  have hTran : A.transcript + readCount ≤ A.hints := hShape.1
  have hRes : A.hints + N < A.result := hAM.result
  have hLimit : A.result + N < A.limit := hAM.limit
  have hWordInput : word * W + synLen CR T < 2 ^ W := by
    have hAMEnd : word + wordsOf W (synLen CR T) ≤ A.transcript := hAM.packed
    exact hintWordSpan_lt W _ _ maxAddr hW (hAMEnd.trans (by omega)) hMem
  have hPreLen : prelude_.length = readCount := hintDirectReads_length sch node (word * W)
  have hs : HintEventSlice D first (prelude_ ++ (List.range sch.m).map (HintTreeEvent.finishRow node seed) ++
      hintResidualEvents CR node offset N t) := by
    change HintEventSlice D first (hintTreeEvents CR offsets (.direct sch t) node seed (word * W)) at hSlice
    rw [hintTreeEvents_direct] at hSlice
    exact hSlice
  obtain ⟨hRead, hRows, hTail⟩ := hintNodeEventSlice_rowTail CR sch node seed t first offset prelude_ hs
  rw [hPreLen] at hRows hTail
  have hDesc (pos : Fin D.events.length) :
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 3 < 2 ^ W := by
    apply lt_of_le_of_lt (Nat.add_le_add_left ?_ _) ((hintDecoderEvent_end S H D header pos).trans_lt hDet)
    rw [hintEventRecord_length]
    cases D.events[pos.val] <;> simp [HintTreeEvent.recordLength]
  let reads := hintDirectReadAt_total S H D E header node first word N X Y t
    (fun m => parentHints m ∧ ownFresh m ∧ keep m) hInfoXY rfl (show 2 < 2 ^ W by omega) hW hRead
    (show A.transcript + sch.m * sch.ℓ ≤ 2 ^ W by omega) hCtrl hAM.packed (hAM.readable hW)
    hAM.outsideCursor.symm (fun pos _ _ => hDesc pos)
    (by
      intro m m' hf hk
      have frame : CRMemFrame A.transcript (A.transcript + readCount) m m' := hf
      refine ⟨hk.1.frame (fun q _ => frame _ (Or.inr (by omega))), ?_, ?_⟩
      · intro a ha hb
        exact (frame a (Or.inr (by omega))).trans (hk.2.1 a ha hb)
      · apply hKeep m m' ?_ hk.2.2
        intro a _ ha
        change a < arena node ∨ arena (node + 1) ≤ a at ha
        have hi : A.transcript + readCount ≤ arena (node + 1) := by
          have he : A.limit ≤ arena (node + 1) := hAM.own
          omega
        exact frame a (ha.imp (fun h => h.trans_le hTranLo) (fun h => hi.trans h)))
    (fun m v hk => by
      refine ⟨hk.1.update_below _ _ (by omega), ?_, hCursor m v hk.2.2⟩
      intro a ha hb
      rw [Function.update_of_ne (by omega)]
      exact hk.2.1 a ha hb)
    hWordInput.le
  have hHead : (schemeNodes R)[seed]? = some T := BlockOf_head hBlock
  obtain ⟨hPerm, hCoeff, _⟩ := hintRowPublic_of_head H R T seedData W det seed N X Y hHead rfl
  have hCoeffSpace : H.rows X Y * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ W :=
    (hintSpec_sizes_of_head R T seed W hHead hFit).2
  have hOffset : offset + (S.data N t).R = word * W + synLen CR T := by
    change word * W + readCount + (S.data N t).R = word * W + (readCount + (S.data N t).R)
    rw [Nat.add_assoc]
  let tail := hintPlacedRowTail_total S H hR hT seedData up previous W Bc header node seed
    (first + readCount) offset N X Y t r J keep
    hHeader hW hWord hBc hFit hSeed hK hEll hBX hBY hmPos hm hSteps ht hSmall hCR
    hPlaced hInfoN hInfoXY hInfoT hRoot hMem hDet hOffset (fun j q s => hCoeff j s q) hPerm hCoeffSpace
    hRows hTail hKeep hCursor
  have hCount : (hintTreeEvents CR offsets T node seed (offsets node)).length =
      readCount + (sch.m + (1 + sch.N + 1 + 1)) := by
    change (hintTreeEvents CR offsets (.direct sch t) node seed (word * W)).length = _
    rw [hintTreeEvents_direct]
    change (prelude_ ++ (List.range sch.m).map (HintTreeEvent.finishRow node seed) ++
      hintResidualEvents CR node offset sch.N t).length = _
    simp only [List.length_append, List.length_map, List.length_range, hPreLen, hintResidualEvents_length]
    omega
  change HintDecoderPhase S H D E header first (hintTreeEvents CR offsets T node seed (offsets node)).length _ _
  rw [hCount]
  exact (reads.relabel
    (fun m => show (parentHints m ∧ ownFresh m ∧ keep m) ↔
      ((HintBitmap m A.hints N J ∧ HintNodeFreshTail D node 1 m) ∧ keep m) by
      change (parentHints m ∧ ownFresh m ∧ keep m) ↔ ((parentHints m ∧ ownFresh m) ∧ keep m)
      tauto)
    (fun m => show (transcript m ∧ parentHints m ∧ ownFresh m ∧ keep m) ↔
      (parentHints m ∧ transcript m ∧ ownFresh m ∧ keep m) by tauto)).append tail

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedDirect_total
end -- Def_LinearSetReconciliation327_Main_HintPlacedBinaryDirect20261120

section -- Def_LinearSetReconciliation327_Main_HintRowTailBudget20261120
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearSetReconciliation327.Main

theorem HintDecoderPhase.adapt_budget_eq {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables}
    {E : RAMEnv} {header first count : ℕ} {A B A' B' : (ℕ → ℕ) → Prop}
    (p : HintDecoderPhase S H D E header first count A B) (hCount : 0 < count)
    (before : ∀ m, A' m → A m) (after : ∀ m, B m → B' m)
    (hA : ∀ m v, A' m → A' (Function.update m (D.control + 2) v))
    (hB : ∀ m v, B' m → B' (Function.update m (D.control + 2) v)) :
    (p.adapt hCount before after hA hB).budget = p.budget := rfl

theorem HintDecoderPhase.relabel_budget_eq {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables}
    {E : RAMEnv} {header first count : ℕ} {A B A' B' : (ℕ → ℕ) → Prop}
    (p : HintDecoderPhase S H D E header first count A B) (before : ∀ m, A m ↔ A' m)
    (after : ∀ m, B m ↔ B' m) :
    (p.relabel before after).budget = p.budget := rfl

structure HintRowTimeBounds (S : CRSourceBundle) (H : HintParams)
    (N X Y t Bc keys radius base extra : ℕ) : Prop where
  keys_fit : H.Nmax N X Y ≤ keys
  columns_fit : H.ell N X Y ≤ keys
  radius_bound : H.BY N X Y ≤ radius
  radius_fit : radius ≤ keys
  row : hintRowCallCap keys radius ≤ base
  residual_copy : 17 * (S.data N t).R + 13 ≤ extra
  residual_toggle : 147 * (1 + Bc) + 24 ≤ base
  residual_decode : hintCRNodeBudget S N t ≤ extra
  residual_correct : 11 * N + 11 ≤ extra

theorem hintPlacedRowTail_total_budget_follows (S : CRSourceBundle) (H : HintParams)
    {R T : Node} (hR : IsSchemeTree H R) (hT : IsSchemeTree H T)
    (seedData : (hintSpec R).Seed) (up previous : ℕ → ℕ)
    (W Bc header node seed first offset N X Y t : ℕ)
    (lr : (H.scheme N X Y).LocalSeed) (J : Finset ℕ) (keep : (ℕ → ℕ) → Prop)
    (hHeader : 3 < header) (hW : 0 < W) (hWord : 30 < 2 ^ W) (hBc : Bc + 1 < 2 ^ W)
    (hFit : (hintSpec R).Fits W) (hSeed : seed < 2 ^ W)
    (hK : H.Nmax N X Y < 2 ^ W) (hEll : H.ell N X Y < 2 ^ W)
    (hBX : H.BX N X Y < 2 ^ W) (hBY : H.BY N X Y + 1 < 2 ^ W)
    (hmPos : 0 < H.rows X Y) (hm : H.rows X Y ≤ N) (hSteps : 0 < H.ell N X Y)
    (ht : t ≤ N)
    (hSmall : (S.data N t).W + 1 < W) (hCR : UpCRColumns (crFamily S) Bc N t)
    (U radius : ℕ) (base extra : ℕ) :
    let D := hintDecoderTables S H hR W Bc header
    let A := D.placement.arena node
    let E := (hintSpec R).env W (D.det S H up previous header R.N) seedData
    let sch := H.scheme N X Y
    let word := D.placement.inputWord node
    let arena := hintArenaStart D.heap D.stride
    let ownFresh := fun (mem : ℕ → ℕ) => ∀ a, A.result ≤ a → a < arena (node + 1) → mem a = 0
    ∀
      (hp : HintPlacedSubtree (crFamily S) H D hT node seed)
      (hInfoN : (D.placement.info node).universeSize = N)
      (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
      (hInfoT : (D.placement.info node).residualCapacity = t)
      (hRoot : (node = 0 → synLen (crFamily S) T ≤ synLen (crFamily S) R))
      (hMem : arena D.infos.length * W < 2 ^ W)
      (hDet : hintDecoderDetEnd S H D header < 2 ^ W)
      (hOffset : offset + (S.data N t).R = word * W + synLen (crFamily S) T)
      (hCoeff : (∀ (j : Fin (H.rows X Y)) (q : Fin (H.Nmax N X Y)) (s : Fin (H.ell N X Y)),
      E.coeff seed (j.val * H.ell N X Y * H.Nmax N X Y + q.val + s.val * H.Nmax N X Y) =
        (lr.2 j s q).val))
      (hPerm : (∀ i : Fin N, E.permInv seed i.val = (lr.1.symm i).val))
      (hCoeffSpace : H.rows X Y * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ W)
      (hRows : (∀ q < sch.m, D.events[first + q]? = some (.finishRow node seed q)))
      (hSlice : HintEventSlice D (first + sch.m) (hintResidualEvents (crFamily S) node offset sch.N t))
      (hKeep : (∀ m m', HintSubtreeFrame D node T.nodeCount m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (_hCost : HintRowTimeBounds S H N X Y t Bc U radius base extra),
      HintBudgetFollows D.events first (sch.m + (1 + sch.N + 1 + 1)) (hintPlacedRowTail_total (R := R) (T := T) S H hR hT seedData up previous W Bc header node seed first offset N X Y t lr J keep hHeader hW hWord hBc hFit hSeed hK hEll hBX hBY hmPos hm hSteps ht hSmall hCR hp hInfoN hInfoXY hInfoT hRoot hMem hDet hOffset hCoeff hPerm hCoeffSpace hRows hSlice hKeep hCursor).budget
        (fun e => base + (if e.linearWork then extra else 0)) := by
  dsimp only
  intro hp hInfoN hInfoXY hInfoT hRoot hMem hDet hOffset hCoeff hPerm hCoeffSpace hRows hSlice hKeep hCursor hCost
  simp only [hintPlacedRowTail_total, id, hintAndRec_value]
  with_unfolding_all simp only [HintDecoderPhase.adapt_budget_eq]
  apply HintDecoderPhase.append_plain_budget_follows
  · intro i hi e he
    have hEq := Option.some.inj (he.symm.trans (hRows i hi))
    subst e
    apply le_trans ?_ (Nat.le_add_right base 0)
    refine le_trans ?_ hCost.row
    exact hintFinalBinaryRows_budget_le S H _ _ header N X Y node seed first _ J _
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ U radius hCost.keys_fit hCost.columns_fit hCost.radius_bound
      hCost.radius_fit _ _ _ _ _ _ _ _ _ _ _ ⟨i, hi⟩
  · apply hintNodeResidual_total_budget_follows
    · exact hCost.residual_copy
    · rw [hintChildUpdateSchedule_length]
      exact hCost.residual_toggle
    · exact hCost.residual_decode
    · exact hCost.residual_correct

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedRowTail_total_budget_follows
end -- Def_LinearSetReconciliation327_Main_HintRowTailBudget20261120

section -- Def_LinearSetReconciliation327_Main_HintBinaryColumn20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem HintBinaryMemory.frame {m m' : ℕ → ℕ} {base count : ℕ}
    (h : HintBinaryMemory m base count) (hf : ∀ q < count, m' (base + q) = m (base + q)) :
    HintBinaryMemory m' base count := by
  intro q hq
  rw [hf q hq]
  exact h q hq

theorem HintTranscriptBinary.frame {m m' : ℕ → ℕ} {sch : RowScheme} {base count : ℕ}
    (h : HintTranscriptBinary sch base count m)
    (hf : ∀ (j : Fin sch.m) (s : Fin sch.ℓ), s.val < count →
      m' (hintTranscriptCell base sch.m j.val s.val) = m (hintTranscriptCell base sch.m j.val s.val)) :
    HintTranscriptBinary sch base count m' := by
  intro j s hs
  rw [hf j s hs]
  exact h j s hs

noncomputable def hintRecursiveColumn_total (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node seed first N X Y t Bc : ℕ)
    (Xs Ys : Fin (H.scheme N X Y).ℓ → ℕ) (children : Fin (H.scheme N X Y).ℓ → Node)
    (r : (Node.recursive (H.scheme N X Y) t Xs Ys children).Seed)
    (J : Finset ℕ) (col : Fin (H.scheme N X Y).ℓ)
    (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = D.placement.width) (hW : 0 < E.W) (hWord : 30 < 2 ^ E.W)
    (hControl : D.placement.control = D.control)
    (hInfoN : (D.placement.info node).universeSize = N)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
    (hChild : (D.placement.info node).children[col.val]? =
      some (hintChildPhysicalIndex children node col))
    (hm : H.rows X Y ≤ N)
    (hSize : (children col).N = (H.scheme N X Y).m)
    (hSteps : 0 < H.ell N X Y)
    (hSeedFit : seed < 2 ^ E.W) (hKFit : H.Nmax N X Y < 2 ^ E.W)
    (hStepsFit : H.ell N X Y < 2 ^ E.W) (hBXFit : H.BX N X Y < 2 ^ E.W)
    (hBYFit : H.BY N X Y + 1 < 2 ^ E.W)
    (hCoeffSpace : H.rows X Y * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ E.W)
    (hCoeff : ∀ (j : Fin (H.rows X Y)) (q : Fin (H.Nmax N X Y)) (s : Fin (H.ell N X Y)),
      E.coeff seed (j.val * H.ell N X Y * H.Nmax N X Y + q.val + s.val * H.Nmax N X Y) =
        (r.1.2 j s q).val)
    (hPerm : ∀ i : Fin N, E.permInv seed i.val = (r.1.1.symm i).val) :
    let sch := H.scheme N X Y
    let CR := crFamily S
    let L := D.placement
    let A := L.arena node
    let child := children col
    let cn := hintChildPhysicalIndex children node col
    let cs := hintChildSchemeIndex children seed col
    let B := L.arena cn
    let lo := hintArenaStart D.heap D.stride cn
    let hi := hintArenaStart D.heap D.stride (cn + child.nodeCount)
    let word := L.inputWord node
    let offsets := fun i => L.inputWord i * E.W
    let gate := A.transcript + col.val * sch.m
    let words := wordsOf E.W (synLen CR child)
    let scratchEnd := hintPredictScratchEnd H L.rowScratch N X Y col.val
    let table := L.updateTable cn
    let colBase := hintSubtreeColBase Bc child
    let items := hintChildUpdateSchedule CR Bc colBase child cs B.saveOffset
    let events := hintRecursiveColumnEvents CR offsets sch children node seed (word * E.W) col
    let run := hintTreeEvents CR offsets child cn cs (offsets cn)
    let parentHints := fun m => HintBitmap m A.hints sch.N J
    let transcript := HintTranscriptBinary sch A.transcript col.val
    let next := HintTranscriptBinary sch A.transcript (col.val + 1)
    let ready := fun m => parentHints m ∧ transcript m ∧ keep m
    let childFresh := HintFreshWords B.payload words
    let tail := HintNodeFreshTail D cn child.nodeCount
    HintEventSlice D first events →
    D.control + 2 < L.rowScratch →
    L.rowScratch ≤ D.listBase →
    D.listBase ≤ A.transcript →
    scratchEnd ≤ D.listBase →
    A.transcript + sch.ℓ * sch.m ≤ A.hints →
    A.hints + N ≤ B.payload →
    B.payload = lo → L.inputWord cn = B.payload →
    B.payload + B.saveOffset + 2 ≤ B.hints →
    B.hints + sch.m ≤ B.result →
    B.result + sch.m ≤ hi → hi < 2 ^ E.W →
    words ≤ B.workStart → UpSaveRoom B.workStart B.saveOffset child →
    word * E.W + synLen CR (.recursive sch t Xs Ys children) < 2 ^ E.W →
    (word * E.W + synLen CR (.recursive sch t Xs Ys children)) / E.W < B.payload →
    table + 3 < 2 ^ E.W → E.det (table + 3) = D.control →
    UpSavedLayout E table items → E.det (table % 2 ^ E.W) % 2 ^ E.W = items.length →
    (∀ i < child.N, UpLocalTree CR (upShiftDetEnv E table) i Bc colBase child (r.2 col) cs 0 0) →
    (∀ j : Fin (H.rows X Y),
      let threshold := L.threshold node j.val
      let block := hintWaitDetBlock (H.Nmax N X Y) (rowLen N (H.rows X Y) j.val)
        (H.BY N X Y) (H.ell N X Y) (H.c N X Y)
      block.At E threshold ∧ threshold + block.length ≤ 2 ^ E.W) →
    (∀ p : Fin D.events.length, hintEventDescriptor header D.events (hintEventRecord S H L) p.val +
      (D.events[p.val]).recordLength < 2 ^ E.W) →
    (∀ m m', (∀ a, (a < L.rowScratch ∨ D.listBase ≤ a) →
      (a < gate ∨ gate + sch.m ≤ a) → (a < lo ∨ hi ≤ a) → m' a = m a) → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintBinarySubtreePhase S H D E header cn cs (first + sch.m + 1 + sch.m) child →
    HintDecoderPhase S H D E header first events.length
      (fun m => ready m ∧ childFresh m ∧ tail m)
      (fun m => parentHints m ∧ next m ∧ keep m) := by
  let sch := H.scheme N X Y
  let CR := crFamily S
  let L := D.placement
  let A := L.arena node
  let child := children col
  let cn := hintChildPhysicalIndex children node col
  let cs := hintChildSchemeIndex children seed col
  let B := L.arena cn
  let lo := hintArenaStart D.heap D.stride cn
  let hi := hintArenaStart D.heap D.stride (cn + child.nodeCount)
  let word := L.inputWord node
  let offsets := fun i => L.inputWord i * E.W
  let gate := A.transcript + col.val * sch.m
  let words := wordsOf E.W (synLen CR child)
  let scratchEnd := hintPredictScratchEnd H L.rowScratch N X Y col.val
  let events := hintRecursiveColumnEvents CR offsets sch children node seed (word * E.W) col
  let run := hintTreeEvents CR offsets child cn cs (offsets cn)
  let parentHints := fun m => HintBitmap m A.hints sch.N J
  let transcript := HintTranscriptBinary sch A.transcript col.val
  let next := HintTranscriptBinary sch A.transcript (col.val + 1)
  let ready := fun m => parentHints m ∧ transcript m ∧ keep m
  let childFresh := HintFreshWords B.payload words
  let tail := HintNodeFreshTail D cn child.nodeCount
  let pred := fun m => HintBinaryMemory m gate sch.m
  let abstain := fun m => HintBinaryMemory m B.hints sch.m
  let childWords := HintPackedMemory E.W B.payload (synLen CR child)
  let result := fun m => HintBinaryMemory m B.result sch.m
  dsimp only
  intro hSlice hCtrl hScratch hTran hWork hTranEnd hParent hPayload hChildInput hChildWork hHints hResult hEnd
  intro hRoom1 hRoom2 hInputFit hInputSep hTable hReturn hLayout hCount hLocal hThreshold hDesc hKeep hCursor call
  change D.control + 2 < L.rowScratch at hCtrl
  change L.rowScratch ≤ D.listBase at hScratch
  change D.listBase ≤ A.transcript at hTran
  change scratchEnd ≤ D.listBase at hWork
  change A.transcript + sch.ℓ * sch.m ≤ A.hints at hTranEnd
  change A.hints + sch.N ≤ B.payload at hParent
  change B.payload = lo at hPayload
  change L.inputWord cn = B.payload at hChildInput
  change B.payload + B.saveOffset + 2 ≤ B.hints at hChildWork
  change B.hints + sch.m ≤ B.result at hHints
  change B.result + sch.m ≤ hi at hResult
  change hi < 2 ^ E.W at hEnd
  change words ≤ B.workStart at hRoom1
  change UpSaveRoom B.workStart B.saveOffset child at hRoom2
  change child.N = sch.m at hSize
  change ∀ m m', (∀ a, (a < L.rowScratch ∨ D.listBase ≤ a) →
    (a < gate ∨ gate + sch.m ≤ a) → (a < lo ∨ hi ≤ a) → m' a = m a) → keep m → keep m' at hKeep
  have hControlTran : D.control + 2 < A.transcript := by omega
  have hColumn : col.val * sch.m + sch.m ≤ sch.ℓ * sch.m := by
    have h := Nat.mul_le_mul_right sch.m col.isLt
    rwa [Nat.succ_mul] at h
  have hGate : A.transcript ≤ gate := by dsimp only [gate]; omega
  have hGateEnd : gate + sch.m ≤ A.hints := by dsimp only [gate]; omega
  have hRoom : B.workStart ≤ B.saveOffset := (Nat.le_add_right _ _).trans hRoom2
  have hChildFreshEnd : B.payload + words ≤ B.hints := by omega
  have hGCtrl : D.control + 2 < gate := hControlTran.trans_le hGate
  have hPCtrl : D.control + 2 < A.hints := by omega
  have hBCtrl : D.control + 2 < B.payload := by omega
  have hHCtrl : D.control + 2 < B.hints := by omega
  have hRCtrl : D.control + 2 < B.result := by omega
  have hScratchFit : scratchEnd < 2 ^ E.W := by omega
  have hScratchTran : scratchEnd ≤ A.transcript := by omega
  have hParentBeforeHints : A.hints + N ≤ B.hints := by change A.hints + sch.N ≤ B.hints; omega
  have hChildHintFit : B.hints + sch.m ≤ 2 ^ E.W := by omega
  obtain ⟨hPredict, _, _, _, hRecover⟩ := hintRecursiveColumn_slice CR D offsets sch children node seed
    (word * E.W) first col hSlice
  have hDescriptor {pos : Fin D.events.length} {e : HintTreeEvent}
      (he : D.events[pos.val]? = some e) (len : ℕ) (hlen : len ≤ e.recordLength) :
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + len < 2 ^ E.W := by
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans he)
    have hb : len ≤ D.events[pos.val].recordLength := by rw [hEq]; exact hlen
    exact (Nat.add_le_add_left hb _).trans_lt (hDesc pos)
  have hPredictDesc (pos : Fin D.events.length) (hLo : first ≤ pos.val) (hHi : pos.val < first + sch.m) :
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 31 ≤ 2 ^ E.W := by
    have he : D.events[pos.val]? = some (.predict node seed col.val (pos.val - first)) := by
      nth_rw 1 [show pos.val = first + (pos.val - first) by omega]
      exact hPredict _ (by omega)
    exact (hDescriptor he 31 (by simp [HintTreeEvent.recordLength])).le
  have hPrepareDesc (pos : Fin D.events.length) :
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 3 < 2 ^ E.W := by
    apply lt_of_le_of_lt (Nat.add_le_add_left ?_ _) (hDesc pos)
    cases D.events[pos.val] <;> simp [HintTreeEvent.recordLength]
  have hCursorTranscript (m : ℕ → ℕ) (v : ℕ) (h : transcript m) :
      transcript (Function.update m (D.control + 2) v) := by
    apply h.frame
    intro j s _
    have ha : A.transcript ≤ hintTranscriptCell A.transcript sch.m j.val s.val := by
      unfold hintTranscriptCell
      omega
    rw [Function.update_of_ne (Nat.ne_of_gt (hControlTran.trans_le ha))]
  let predict := hintPredictBinaryRows_phase S H D E header N X Y node cn seed first r.1 J col
    (fun m => keep m ∧ childFresh m ∧ tail m) hInfoN hInfoXY hChild hControl hPredict hm hSteps
    hWord hSeedFit hKFit hStepsFit hBXFit hBYFit hCoeffSpace hCoeff hPerm hCtrl hControlTran
    hScratchFit hScratchTran hTranEnd hParentBeforeHints hChildHintFit hThreshold hPredictDesc
    (by
      intro m m' hf hk
      have hf' : ∀ a, (a < L.rowScratch ∨ scratchEnd ≤ a) →
          (a < gate ∨ gate + sch.m ≤ a) → (a < B.hints ∨ B.hints + sch.m ≤ a) → m' a = m a := hf
      refine ⟨hKeep m m' (fun a ha hg hc => hf' a
        (ha.imp id (hWork.trans ·)) hg (hc.imp (by omega) (by omega))) hk.1, ?_, ?_⟩
      · exact hk.2.1.frame (fun q hq => hf' _
          (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)))
      · apply hk.2.2.frame
        intro a ha _
        change B.result ≤ a at ha
        exact hf' a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)))
    (fun m v hk => ⟨hCursor m v hk.1, hk.2.1.update_below _ _ hBCtrl, hk.2.2.update_below v hRCtrl⟩)
  let prepare := hintPrepareChild_total S H D E header node seed first word N X Y t Bc Xs Ys children
    r col offsets (fun m => ready m ∧ abstain m ∧ tail m) hWidth hW (by omega : 16 < 2 ^ E.W)
    hInfoXY hSize hSlice hGCtrl (by omega : gate + sch.m ≤ B.payload)
    (by omega : B.payload + (B.saveOffset + 2) ≤ 2 ^ E.W) hRoom1 hRoom2 hInputFit hInputSep
    hTable hReturn hLayout hCount hLocal (fun p _ _ => hPrepareDesc p)
    (by
      intro m m' hf hk
      have frame : CRMemFrame B.payload (B.payload + B.saveOffset + 2) m m' := hf
      obtain ⟨⟨hh, ht, hk⟩, hb, hfresh⟩ := hk
      refine ⟨⟨hh.frame (fun q hq => frame _ (Or.inl (by omega))), ht.frame ?_,
        hKeep m m' (fun a _ _ hc => frame a (hc.imp (by omega) (by omega))) hk⟩,
        hb.frame (fun q _ => frame _ (Or.inr (by omega))), hfresh.frame ?_⟩
      · intro j s hs
        have hb := hintTranscriptCell_beforeColumn sch A.transcript j s col.val hs
        change hintTranscriptCell A.transcript sch.m j.val s.val < gate at hb
        exact frame _ (Or.inl (by omega))
      · intro a ha _
        change B.result ≤ a at ha
        exact frame a (Or.inr (by omega)))
    (fun m v hk => ⟨⟨hk.1.1.update_below _ _ hPCtrl, hCursorTranscript m v hk.1.2.1,
      hCursor m v hk.1.2.2⟩, hk.2.1.update_below _ hHCtrl, hk.2.2.update_below v hRCtrl⟩)
  let called := call (fun m => ready m ∧ pred m)
    (by
      intro m m' hf hk
      have low (a : ℕ) (ha : A.transcript ≤ a) (hb : a < lo) : m' a = m a :=
        hf a (Or.inr (hTran.trans ha)) (Or.inl hb)
      refine ⟨⟨hk.1.1.frame (fun q hq => low _ (by omega) (by omega)), hk.1.2.1.frame ?_,
        hKeep m m' (fun a hs _ hb => hf a hs hb) hk.1.2.2⟩, hk.2.frame (fun q hq => low _ (by omega) (by omega))⟩
      intro j s hs
      have hb := hintTranscriptCell_beforeColumn sch A.transcript j s col.val hs
      change hintTranscriptCell A.transcript sch.m j.val s.val < gate at hb
      exact low _ (by unfold hintTranscriptCell; omega) (by omega))
    (fun m v hk => ⟨⟨hk.1.1.update_below _ _ hPCtrl, hCursorTranscript m v hk.1.2.1,
      hCursor m v hk.1.2.2⟩, hk.2.update_below _ hGCtrl⟩)
  let recovered := hintRecoverColumn_total S H D E header node cn (first + sch.m + 1 + sch.m + run.length)
    N X Y col (fun m => parentHints m ∧ keep m) hInfoXY hRecover
    (by omega : 1 < 2 ^ E.W) hControlTran hRCtrl
    (by omega : gate < 2 ^ E.W) (by omega : B.result < 2 ^ E.W) (by omega : sch.m < 2 ^ E.W)
    (by omega : gate + sch.m ≤ 2 ^ E.W) (by omega : B.result + sch.m ≤ 2 ^ E.W)
    (Or.inl (by omega : gate + sch.m ≤ B.result))
    (fun pos hp => hDescriptor (show D.events[pos.val]? = some (.recoverColumn node col.val cn) by
      rw [hp]; exact hRecover) 2 (by simp [HintTreeEvent.recordLength]))
    (by
      intro m m' hf hk
      have frame : CRMemFrame gate (gate + sch.m) m m' := hf
      exact ⟨hk.1.frame (fun q _ => frame _ (Or.inr (by omega))),
        hKeep m m' (fun a _ hg _ => frame a hg) hk.2⟩)
    (fun m v hk => ⟨hk.1.update_below _ _ hPCtrl, hCursor m v hk.2⟩)
  have hLen : events.length = sch.m + (1 + sch.m) + run.length + 1 := by
    simp only [events, hintRecursiveColumnEvents, List.length_append, List.length_map, List.length_range,
      List.length_cons, List.length_nil, Nat.zero_add]
    change sch.m + 1 + sch.m + run.length + 1 = _
    omega
  let prepared := (predict.relabel
      (fun m => show (parentHints m ∧ transcript m ∧ keep m ∧ childFresh m ∧ tail m) ↔
        (ready m ∧ childFresh m ∧ tail m) by unfold ready; tauto)
      (fun _ => Iff.rfl)).append
    (prepare.relabel
      (fun m => show (pred m ∧ childFresh m ∧ ready m ∧ abstain m ∧ tail m) ↔
        ((parentHints m ∧ transcript m ∧ keep m ∧ childFresh m ∧ tail m) ∧ pred m ∧ abstain m) by
        unfold ready; tauto)
      (fun _ => Iff.rfl))
  let called' : HintDecoderPhase S H D E header (first + sch.m + 1 + sch.m) run.length
      (fun m => pred m ∧ childWords m ∧ ready m ∧ abstain m ∧ tail m)
      (fun m => transcript m ∧ pred m ∧ result m ∧ parentHints m ∧ keep m) :=
    called.adapt (hintTreeEvents_pos CR offsets child cn cs (offsets cn))
      (by
        rintro m ⟨hp, _, hr, ha, hf⟩
        exact ⟨⟨hSize.symm ▸ ha, hf⟩, hr, hp⟩)
      (by
        rintro m ⟨ho, ⟨hh, ht, hk⟩, hp⟩
        have hOut : result m := by
          change HintBinaryMemory m B.result sch.m
          rw [← hSize]
          exact ho
        exact ⟨ht, hp, hOut, hh, hk⟩)
      (by
        rintro m v ⟨hp, hw, ⟨hh, ht, hk⟩, ha, hf⟩
        exact ⟨hp.update_below v hGCtrl, hw.update_below v hBCtrl,
          ⟨hh.update_below _ _ hPCtrl, hCursorTranscript m v ht, hCursor m v hk⟩,
          ha.update_below v hHCtrl, hf.update_below v hRCtrl⟩)
      (by
        rintro m v ⟨ht, hp, ho, hh, hk⟩
        exact ⟨hCursorTranscript m v ht, hp.update_below v hGCtrl, ho.update_below v hRCtrl,
          hh.update_below _ _ hPCtrl, hCursor m v hk⟩)
  let decoded := prepared.append_at called'
    (by omega : first + sch.m + 1 + sch.m = first + (sch.m + (1 + sch.m)))
  change HintDecoderPhase S H D E header first events.length
    (fun m => ready m ∧ childFresh m ∧ tail m) (fun m => parentHints m ∧ next m ∧ keep m)
  rw [hLen]
  exact decoded.append_at (recovered.relabel (fun _ => Iff.rfl) (fun _ => by tauto))
    (by change first + sch.m + 1 + sch.m + run.length = first + (sch.m + (1 + sch.m) + run.length); omega)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRecursiveColumn_total
end -- Def_LinearSetReconciliation327_Main_HintBinaryColumn20261120

section -- Def_LinearSetReconciliation327_Main_HintColumnBudget20261120
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearSetReconciliation327.Main

def HintBinarySubtreePhase.BudgetFollows {S : CRSourceBundle} {H : HintParams}
    {D : HintDecoderTables} {E : RAMEnv} {header node seed first : ℕ} {T : Node}
    (p : HintBinarySubtreePhase S H D E header node seed first T) (cap : HintTreeEvent → ℕ) : Prop :=
  ∀ keep hKeep hCursor, HintBudgetFollows D.events first
    (hintTreeEvents (crFamily S) (fun a => D.placement.inputWord a * E.W)
      T node seed (D.placement.inputWord node * E.W)).length (p keep hKeep hCursor).budget cap

theorem hintRecursiveColumn_total_budget_follows (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node seed first N X Y t Bc : ℕ)
    (Xs Ys : Fin (H.scheme N X Y).ℓ → ℕ) (children : Fin (H.scheme N X Y).ℓ → Node)
    (r : (Node.recursive (H.scheme N X Y) t Xs Ys children).Seed)
    (J : Finset ℕ) (col : Fin (H.scheme N X Y).ℓ)
    (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = D.placement.width) (hW : 0 < E.W) (hWord : 30 < 2 ^ E.W)
    (hControl : D.placement.control = D.control)
    (hInfoN : (D.placement.info node).universeSize = N)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
    (hChild : (D.placement.info node).children[col.val]? =
      some (hintChildPhysicalIndex children node col))
    (hm : H.rows X Y ≤ N)
    (hSize : (children col).N = (H.scheme N X Y).m)
    (hSteps : 0 < H.ell N X Y)
    (hSeedFit : seed < 2 ^ E.W) (hKFit : H.Nmax N X Y < 2 ^ E.W)
    (hStepsFit : H.ell N X Y < 2 ^ E.W) (hBXFit : H.BX N X Y < 2 ^ E.W)
    (hBYFit : H.BY N X Y + 1 < 2 ^ E.W)
    (hCoeffSpace : H.rows X Y * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ E.W)
    (hCoeff : ∀ (j : Fin (H.rows X Y)) (q : Fin (H.Nmax N X Y)) (s : Fin (H.ell N X Y)),
      E.coeff seed (j.val * H.ell N X Y * H.Nmax N X Y + q.val + s.val * H.Nmax N X Y) =
        (r.1.2 j s q).val)
    (hPerm : ∀ i : Fin N, E.permInv seed i.val = (r.1.1.symm i).val)
    (U radius : ℕ) (base extra : ℕ) :
    let sch := H.scheme N X Y
    let CR := crFamily S
    let L := D.placement
    let A := L.arena node
    let child := children col
    let cn := hintChildPhysicalIndex children node col
    let cs := hintChildSchemeIndex children seed col
    let B := L.arena cn
    let lo := hintArenaStart D.heap D.stride cn
    let hi := hintArenaStart D.heap D.stride (cn + child.nodeCount)
    let word := L.inputWord node
    let offsets := fun i => L.inputWord i * E.W
    let gate := A.transcript + col.val * sch.m
    let words := wordsOf E.W (synLen CR child)
    let scratchEnd := hintPredictScratchEnd H L.rowScratch N X Y col.val
    let table := L.updateTable cn
    let colBase := hintSubtreeColBase Bc child
    let items := hintChildUpdateSchedule CR Bc colBase child cs B.saveOffset
    let events := hintRecursiveColumnEvents CR offsets sch children node seed (word * E.W) col
    let run := hintTreeEvents CR offsets child cn cs (offsets cn)
    let parentHints := fun m => HintBitmap m A.hints sch.N J
    let transcript := HintTranscriptBinary sch A.transcript col.val
    let next := HintTranscriptBinary sch A.transcript (col.val + 1)
    let ready := fun m => parentHints m ∧ transcript m ∧ keep m
    let childFresh := HintFreshWords B.payload words
    let tail := HintNodeFreshTail D cn child.nodeCount
    ∀
      (hSlice : HintEventSlice D first events)
      (hCtrl : D.control + 2 < L.rowScratch)
      (hScratch : L.rowScratch ≤ D.listBase)
      (hTran : D.listBase ≤ A.transcript)
      (hWork : scratchEnd ≤ D.listBase)
      (hTranEnd : A.transcript + sch.ℓ * sch.m ≤ A.hints)
      (hParent : A.hints + N ≤ B.payload)
      (hPayload : B.payload = lo)
      (hChildInput : L.inputWord cn = B.payload)
      (hChildWork : B.payload + B.saveOffset + 2 ≤ B.hints)
      (hHints : B.hints + sch.m ≤ B.result)
      (hResult : B.result + sch.m ≤ hi)
      (hEnd : hi < 2 ^ E.W)
      (hRoom1 : words ≤ B.workStart)
      (hRoom2 : UpSaveRoom B.workStart B.saveOffset child)
      (hInputFit : word * E.W + synLen CR (.recursive sch t Xs Ys children) < 2 ^ E.W)
      (hInputSep : (word * E.W + synLen CR (.recursive sch t Xs Ys children)) / E.W < B.payload)
      (hTable : table + 3 < 2 ^ E.W)
      (hReturn : E.det (table + 3) = D.control)
      (hLayout : UpSavedLayout E table items)
      (hCount : E.det (table % 2 ^ E.W) % 2 ^ E.W = items.length)
      (hLocal : (∀ i < child.N, UpLocalTree CR (upShiftDetEnv E table) i Bc colBase child (r.2 col) cs 0 0))
      (hThreshold : (∀ j : Fin (H.rows X Y),
      let threshold := L.threshold node j.val
      let block := hintWaitDetBlock (H.Nmax N X Y) (rowLen N (H.rows X Y) j.val)
        (H.BY N X Y) (H.ell N X Y) (H.c N X Y)
      block.At E threshold ∧ threshold + block.length ≤ 2 ^ E.W))
      (hDesc : (∀ p : Fin D.events.length, hintEventDescriptor header D.events (hintEventRecord S H L) p.val +
      (D.events[p.val]).recordLength < 2 ^ E.W))
      (hKeep : (∀ m m', (∀ a, (a < L.rowScratch ∨ D.listBase ≤ a) →
      (a < gate ∨ gate + sch.m ≤ a) → (a < lo ∨ hi ≤ a) → m' a = m a) → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (call : HintBinarySubtreePhase S H D E header cn cs (first + sch.m + 1 + sch.m) child)
      (_hRowCost : HintRowTimeBounds S H N X Y t Bc U radius base extra)
      (_hCopyCost : 17 * synLen CR child + 13 ≤ extra)
      (_hToggleCost : 147 * items.length + 24 ≤ base)
      (_hXorCost : 11 * sch.m + 11 ≤ extra)
      (_hChild : call.BudgetFollows (fun e => base + (if e.linearWork then extra else 0))),
      HintBudgetFollows D.events first events.length (hintRecursiveColumn_total S H D E header node seed first N X Y t Bc Xs Ys children r J col keep hWidth hW hWord hControl hInfoN hInfoXY hChild hm hSize hSteps hSeedFit hKFit hStepsFit hBXFit hBYFit hCoeffSpace hCoeff hPerm hSlice hCtrl hScratch hTran hWork hTranEnd hParent hPayload hChildInput hChildWork hHints hResult hEnd hRoom1 hRoom2 hInputFit hInputSep hTable hReturn hLayout hCount hLocal hThreshold hDesc hKeep hCursor call).budget
        (fun e => base + (if e.linearWork then extra else 0)) := by
  dsimp only
  intro hSlice hCtrl hScratch hTran hWork hTranEnd hParent hPayload hChildInput hChildWork hHints hResult hEnd
    hRoom1 hRoom2 hInputFit hInputSep hTable hReturn hLayout hCount hLocal hThreshold hDesc hKeep hCursor call
    hRowCost hCopyCost hToggleCost hXorCost hChild
  let sch := H.scheme N X Y
  have hAt := (hintRecursiveColumn_slice (crFamily S) D (fun i => D.placement.inputWord i * E.W)
    sch children node seed (D.placement.inputWord node * E.W) first col hSlice).2.2.2.2
  with_unfolding_all simp only [hintRecursiveColumn_total, id, hintAndRec_value]
  apply HintDecoderPhase.cast_budget_follows
  · simp only [hintTreeEvents_direct, hintRecursiveColumnEvents, List.length_append, List.length_map,
      List.length_range, List.length_cons, List.length_nil, hintResidualEvents_length]
    omega
  apply HintDecoderPhase.append_budget_follows
  · apply HintDecoderPhase.append_budget_follows
    · apply HintDecoderPhase.append_plain_budget_follows
      · apply HintDecoderPhase.relabel_budget_follows
        intro i hi e he
        apply le_trans ?_ (Nat.le_add_right base _)
        refine le_trans ?_ hRowCost.row
        exact hintPredictBinaryRows_budget_le S H D E header N X Y node _ seed first r.1 J col _
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ U radius hRowCost.keys_fit hRowCost.columns_fit hRowCost.radius_bound
          hRowCost.radius_fit _ _ _ _ _ _ _ _ _ _ _ ⟨i, hi⟩
      · apply HintDecoderPhase.relabel_budget_follows
        exact hintPrepareChild_total_budget_follows _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
          base extra _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hCopyCost hToggleCost
    · with_unfolding_all simp only [HintDecoderPhase.adapt_budget_eq]
      exact hChild _ _ _
  · apply HintDecoderPhase.relabel_budget_follows
    intro i hi e he
    have hz : i = 0 := by omega
    subst i
    rw [Nat.add_zero] at he
    have hEq := Option.some.inj (he.symm.trans hAt)
    subst e
    change 11 * sch.m + 11 ≤ base + extra
    exact hXorCost.trans (Nat.le_add_left _ _)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRecursiveColumn_total_budget_follows
end -- Def_LinearSetReconciliation327_Main_HintColumnBudget20261120

section -- Def_LinearSetReconciliation327_Main_HintLeafBudget20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem HintDecoderPhase.concat_budget_follows {S : CRSourceBundle} {H : HintParams}
    {D : HintDecoderTables} {E : RAMEnv} {header first m : ℕ}
    (size : ℕ → ℕ) (inv : ℕ → (ℕ → ℕ) → Prop)
    (start : ∀ mem v, inv 0 mem → inv 0 (Function.update mem (D.control + 2) v))
    (phase : ∀ i < m, HintDecoderPhase S H D E header (first + hintPhasePrefixCount size i)
      (size i) (inv i) (inv (i + 1))) (cap : HintTreeEvent → ℕ)
    (hp : ∀ i (hi : i < m),
      HintBudgetFollows D.events (first + hintPhasePrefixCount size i) (size i) (phase i hi).budget cap) :
    HintBudgetFollows D.events first (hintPhasePrefixCount size m)
      (HintDecoderPhase.concat size inv start phase).budget cap := by
  induction m with
  | zero =>
    exact fun i hi => (Nat.not_lt_zero i hi).elim
  | succ m ih =>
    let p : ∀ i < m, HintDecoderPhase S H D E header (first + hintPhasePrefixCount size i)
        (size i) (inv i) (inv (i + 1)) := fun i hi => phase i (Nat.lt_succ_of_lt hi)
    have hPrefix := ih p (fun i hi => hp i (Nat.lt_succ_of_lt hi))
    exact hPrefix.append (hp m (Nat.lt_succ_self m))

theorem hintPlacedStore_total_budget (S : CRSourceBundle) (H : HintParams)
    {R : Node} (hR : IsSchemeTree H R) (E : RAMEnv)
    (Bc header node seed first N : ℕ)
    (hW : 0 < E.W) (hWord : 2 < 2 ^ E.W) :
    let D := hintDecoderTables S H hR E.W Bc header
    let offsets := fun i => D.placement.inputWord i * E.W
    ∀ (hp : HintPlacedSubtree (crFamily S) H D (.store N) node seed)
      (hRoot : node = 0 → N ≤ synLen (crFamily S) R)
      (hMem : hintArenaStart D.heap D.stride D.infos.length * E.W < 2 ^ E.W)
      (hDet : hintDecoderDetEnd S H D header < 2 ^ E.W)
      (hSlice : HintEventSlice D first (hintTreeEvents (crFamily S) offsets (.store N) node seed (offsets node)))
      (keep : (ℕ → ℕ) → Prop)
      (hKeep : ∀ m m', HintSubtreeFrame D node 1 m m' → keep m → keep m')
      (hCursor : ∀ m v, keep m → keep (Function.update m (D.control + 2) v))
      (i : ℕ),
      (hintPlacedStore_total S H hR E E.W Bc header node seed first N rfl hW hWord
        hp hRoot hMem hDet hSlice keep hKeep hCursor).budget i = 12 * N + 12 := by
  intros
  rfl

theorem hintPlacedCR_total_budget (S : CRSourceBundle) (H : HintParams)
    {R : Node} (hR : IsSchemeTree H R) (E : RAMEnv) (up previous : ℕ → ℕ)
    (Bc header node seed first N t : ℕ)
    (hHeader : 3 < header) (hW : 0 < E.W) (hWord : 11 < 2 ^ E.W)
    (hSmall : (S.data N t).W + 1 < E.W) (hN : 1 ≤ N) (ht : t ≤ N) :
    let D := hintDecoderTables S H hR E.W Bc header
    let offsets := fun i => D.placement.inputWord i * E.W
    ∀ (hDet : E.det = D.det S H up previous header R.N)
      (hp : HintPlacedSubtree (crFamily S) H D (.cr N t) node seed)
      (hRoot : node = 0 → (S.data N t).R ≤ synLen (crFamily S) R)
      (hMem : hintArenaStart D.heap D.stride D.infos.length * E.W < 2 ^ E.W)
      (hEnd : hintDecoderDetEnd S H D header < 2 ^ E.W)
      (hSlice : HintEventSlice D first (hintTreeEvents (crFamily S) offsets (.cr N t) node seed (offsets node)))
      (keep : (ℕ → ℕ) → Prop)
      (hKeep : ∀ m m', HintSubtreeFrame D node 1 m m' → keep m → keep m')
      (hCursor : ∀ m v, keep m → keep (Function.update m (D.control + 2) v))
      (i : ℕ),
      (hintPlacedCR_total S H hR E up previous E.W Bc header node seed first N t hHeader
        rfl hW hWord hSmall hN ht hDet hp hRoot hMem hEnd hSlice keep hKeep hCursor).budget i =
      hintCRNodeBudget S N t := by
  intros
  rfl

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedStore_total_budget
#print axioms LinearSetReconciliation327.Main.hintPlacedCR_total_budget
end -- Def_LinearSetReconciliation327_Main_HintLeafBudget20261120


