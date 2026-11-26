-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_12Support
-- name    : LinearSetReconciliation327_Main_B65_12Support
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T14:33:33.375083+00:00
-- url     : https://prove2.me/theorems/d8a2fc7e-796f-5f6d-ba0e-07bfb937dfbb
-- title:
--   Theorem 6.5 supporting machine proof B65_12Support
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_09
set_option autoImplicit false

section S_HintDecoderStart20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintLength_le_of_valid (J : List ℕ) (N : ℕ)
    (hDistinct : J.Nodup) (hInside : ∀ a ∈ J, a < N) : J.length ≤ N := by
  have hSub : J.toFinset ⊆ Finset.range N := by
    intro a ha
    exact Finset.mem_range.mpr (hInside a (List.mem_toFinset.mp ha))
  have hCard := Finset.card_le_card hSub
  simpa only [List.toFinset_card_of_nodup hDistinct, Finset.card_range] using hCard

theorem hintDecoderStart_word (E : RAMEnv) {M : ℕ} (y : Fin M → ZMod 2) (J : List ℕ)
    (hW : 0 < E.W) (hWords : wordsOf E.W M < 2 ^ E.W) (hLength : J.length < 2 ^ E.W)
    (hJ : ∀ a ∈ J, a < 2 ^ E.W) : UpWordState E (decoderStart E.W y J) := by
  constructor
  · intro r
    simp only [decoderStart, initState]
    split_ifs <;> first | exact hWords | exact hLength | exact Nat.two_pow_pos E.W
  · intro a
    simp only [decoderStart, initState, hintMem]
    split_ifs with ha
    · exact packMem_lt E.W hW y a
    · rw [List.getD_eq_getElem?_getD]
      cases hh : J[a - wordsOf E.W M]? with
      | none => exact Nat.two_pow_pos E.W
      | some k => exact hJ k (List.mem_of_getElem? hh)

theorem hintDecoderStart_packed (W : ℕ) {M : ℕ} (y : Fin M → ZMod 2) (J : List ℕ) :
    ∀ a < wordsOf W M, (decoderStart W y J).mem a = packMem W y a := by
  intro a ha
  simp [decoderStart, initState, hintMem, ha]

theorem hintDecoderStart_hintList (W : ℕ) {M : ℕ} (y : Fin M → ZMod 2) (J : List ℕ) :
    ∀ i (hi : i < J.length), (decoderStart W y J).mem (wordsOf W M + i) = J[i] := by
  intro i hi
  have h : ¬ wordsOf W M + i < wordsOf W M := by omega
  simp [decoderStart, initState, hintMem, h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem hintDecoderStart_fresh (W : ℕ) {M : ℕ} (y : Fin M → ZMod 2) (J : List ℕ) :
    ∀ a, wordsOf W M + J.length ≤ a → (decoderStart W y J).mem a = 0 := by
  intro a ha
  have h : ¬ a < wordsOf W M := by omega
  simp [decoderStart, initState, hintMem, h, List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by omega : J.length ≤ a - wordsOf W M)]

theorem hintDecoderStart_stamp_bits (E : RAMEnv) {M : ℕ} (y : Fin M → ZMod 2) (J : List ℕ)
    (N q : ℕ) (hN : N < 2 ^ E.W)
    (hDistinct : J.Nodup) (hInside : ∀ a ∈ J, a < N) :
    hintStampValue E ((decoderStart E.W y J).regs 1) (min ((decoderStart E.W y J).regs 2) N)
      (decoderStart E.W y J).mem q = hintTruth (q ∈ J.toFinset) := by
  have hLen := hintLength_le_of_valid J N hDistinct hInside
  change hintStampValue E (wordsOf E.W M) (min J.length N) (decoderStart E.W y J).mem q = _
  rw [Nat.min_eq_left hLen]
  unfold hintStampValue
  apply hintTruth_congr
  rw [List.mem_toFinset, List.mem_iff_getElem]
  have hAt (j : ℕ) (hj : j < J.length) :
      (decoderStart E.W y J).mem (wordsOf E.W M + j) % 2 ^ E.W = J[j] := by
    rw [hintDecoderStart_hintList E.W y J j hj,
      Nat.mod_eq_of_lt ((hInside _ (List.getElem_mem hj)).trans hN)]
  constructor
  · rintro ⟨j, hj, he⟩
    exact ⟨j, hj, (hAt j hj).symm.trans he⟩
  · rintro ⟨j, hj, he⟩
    exact ⟨j, hj, (hAt j hj).trans he⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecoderStart_word
#print axioms LinearSetReconciliation327.Main.hintDecoderStart_fresh
#print axioms LinearSetReconciliation327.Main.hintDecoderStart_stamp_bits
end S_HintDecoderStart20261120
section S_HintPlacedSubtree20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintPlacedSubtree (CR : CRFamily) (H : HintParams)
    (D : HintDecoderTables) {T : Node} (hT : IsSchemeTree H T) (node seed : ℕ) : Prop where
  span : node + T.nodeCount ≤ D.infos.length
  read : ∀ i < T.nodeCount, D.infos[node + i]? = (hintNodeInfos CR hT node seed)[i]?

theorem hintNodeCount_pos (T : Node) : 0 < T.nodeCount := by
  cases T <;> simp [Node.nodeCount]

theorem HintPlacedSubtree.root (S : CRSourceBundle) (H : HintParams)
    {T : Node} (hT : IsSchemeTree H T) (W Bc header : ℕ) :
    HintPlacedSubtree (crFamily S) H (hintDecoderTables S H hT W Bc header) hT 0 0 := by
  constructor
  · change 0 + T.nodeCount ≤ (hintNodeInfos (crFamily S) hT 0 0).length
    rw [hintNodeInfos_length, Nat.zero_add]
  · intro i _
    change (hintNodeInfos (crFamily S) hT 0 0)[0 + i]? = _
    rw [Nat.zero_add]

theorem HintPlacedSubtree.child {CR : CRFamily} {H : HintParams} {D : HintDecoderTables}
    {N X Y t node seed : ℕ} {Xs Ys : Fin (H.scheme N X Y).ℓ → ℕ}
    {children : Fin (H.scheme N X Y).ℓ → Node} {hchild : ∀ s, IsSchemeTree H (children s)}
    (parent : HintPlacedSubtree CR H D (.recursive N X Y t Xs Ys children hchild) node seed)
    (col : Fin (H.scheme N X Y).ℓ) :
    HintPlacedSubtree CR H D (hchild col) (hintChildPhysicalIndex children node col)
      (hintChildSchemeIndex children seed col) := by
  let T := Node.recursive (H.scheme N X Y) t Xs Ys children
  let start := ((List.ofFn fun i => (children i).nodeCount).take col.val).sum
  have hEnd : node + 1 + start + (children col).nodeCount ≤ node + T.nodeCount := by
    rw [show T.nodeCount = 1 + ∑ i, (children i).nodeCount from rfl, ← Nat.add_assoc]
    exact hintChildPhysicalIndex_end children node col
  have hSpan : node + T.nodeCount ≤ D.infos.length := parent.span
  constructor
  · exact hEnd.trans hSpan
  · intro i hi
    have hInside : 1 + start + i < T.nodeCount := by omega
    change D.infos[node + 1 + start + i]? =
      (hintNodeInfos CR (hchild col) (hintChildPhysicalIndex children node col)
        (hintChildSchemeIndex children seed col))[i]?
    rw [show node + 1 + start + i = node + (1 + start + i) by omega, parent.read _ hInside]
    exact hintNodeInfos_child CR N X Y t Xs Ys children hchild node seed col i hi

theorem HintPlacedSubtree.head {CR : CRFamily} {H : HintParams} {D : HintDecoderTables}
    {T : Node} {hT : IsSchemeTree H T} {node seed : ℕ}
    (h : HintPlacedSubtree CR H D hT node seed) :
    D.infos[node]? = some (hintNodeInfo CR hT node seed) := by
  have hr := h.read 0 (hintNodeCount_pos T)
  rw [Nat.add_zero] at hr
  have h0 : (hintNodeInfos CR hT node seed)[0]? = some (hintNodeInfo CR hT node seed) := by
    cases hT <;> rfl
  exact hr.trans h0

theorem HintPlacedSubtree.info (S : CRSourceBundle) (H : HintParams)
    {R T : Node} (hR : IsSchemeTree H R) (hT : IsSchemeTree H T) (W Bc header node seed : ℕ) :
    let D := hintDecoderTables S H hR W Bc header
    HintPlacedSubtree (crFamily S) H D hT node seed →
    D.placement.info node = hintNodeInfo (crFamily S) hT node seed := by
  dsimp only
  intro h
  change ((hintDecoderTables S H hR W Bc header).infos[node]?).getD _ = _
  rw [h.head, Option.getD_some]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintPlacedSubtree.child
#print axioms LinearSetReconciliation327.Main.HintPlacedSubtree.info
end S_HintPlacedSubtree20261120
section S_HintNodeGeometry20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintNodeInfo_sizes (CR : CRFamily) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (node seed : ℕ) :
    (hintNodeInfo CR hT node seed).universeSize = T.N ∧
    (hintNodeInfo CR hT node seed).payloadBits = synLen CR T ∧
    (hintNodeInfo CR hT node seed).schemes = (schemeNodes T).length := by
  cases hT <;> exact ⟨rfl, rfl, rfl⟩

theorem hintArenaFor_workspace (S : CRSourceBundle) (H : HintParams) (W : ℕ)
    (info : HintNodeInfo) (start : ℕ) :
    let A := hintArenaFor S H W info start
    A.payload = start ∧ A.workStart = wordsOf W info.payloadBits + 1 ∧
    A.saveOffset = A.workStart + 2 * info.schemes ∧ A.transcript = A.payload + A.saveOffset + 2 := by
  unfold hintArenaFor
  cases info.rowParams with
  | none => cases info.isCR <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | some a => cases a; cases info.isCR <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem hintArenaFor_rowOrder (S : CRSourceBundle) (H : HintParams) (W : ℕ)
    (info : HintNodeInfo) (start N X Y t : ℕ)
    (hN : info.universeSize = N) (hT : info.residualCapacity = t) (hXY : info.rowParams = some (X, Y)) :
    let A := hintArenaFor S H W info start
    let data := S.data N t
    A.transcript + H.rows X Y * H.ell N X Y ≤ A.hints ∧
      A.hints + N < A.result ∧ A.result + N < A.residual ∧
      A.residual + wordsOf W data.R + 2 ≤ A.residualBitmap + 1 ∧
      A.residualBitmap + N < A.crRegisters ∧
      A.limit = A.crRegisters + 16 + (2 ^ (data.W + 1) + 1) + crSourceSteps S N t + 1 := by
  have hPair : (info.universeSize, info.residualCapacity) = (N, t) := Prod.ext hN hT
  have hR := congrArg (fun p : ℕ × ℕ => (S.data p.1 p.2).R) hPair
  have hW := congrArg (fun p : ℕ × ℕ => (S.data p.1 p.2).W) hPair
  dsimp only at hR hW
  have hArea : hintArenaFor S H W info start =
      hintNodeArena start W info.payloadBits info.schemes (H.rows X Y) (H.ell N X Y) N
        (S.data N t).R (S.data N t).W (crSourceSteps S N t) := by
    simp only [hintArenaFor, hN, hT, hXY, Option.isSome_some, Bool.or_true, if_true, hR, hW]
  dsimp only
  rw [hArea]
  dsimp only [hintNodeArena]
  exact ⟨le_rfl, by omega, by omega, by omega, by omega, rfl⟩

theorem hintDecoderTables_localInput (S : CRSourceBundle) (H : HintParams)
    {R T : Node} (hR : IsSchemeTree H R) (hT : IsSchemeTree H T) (W Bc header node seed : ℕ) :
    let D := hintDecoderTables S H hR W Bc header
    let A := D.placement.arena node
    let word := D.placement.inputWord node
    HintPlacedSubtree (crFamily S) H D hT node seed →
    wordsOf W (synLen (crFamily S) T) ≤ A.workStart ∧
      UpSaveRoom A.workStart A.saveOffset T ∧
      A.payload + A.saveOffset + 2 = A.transcript ∧
      word + wordsOf W (synLen (crFamily S) T) ≤ A.transcript ∧
      (0 < W → (word * W + synLen (crFamily S) T) / W < A.transcript) := by
  dsimp only
  intro hPlaced
  let D := hintDecoderTables S H hR W Bc header
  let A := D.placement.arena node
  let word := D.placement.inputWord node
  let M := synLen (crFamily S) T
  let info := D.placement.info node
  have hInfo : info = hintNodeInfo (crFamily S) hT node seed :=
    HintPlacedSubtree.info S H hR hT W Bc header node seed hPlaced
  obtain ⟨_, hBits, hSchemes⟩ := hintNodeInfo_sizes (crFamily S) H hT node seed
  have hBits' : info.payloadBits = M := hInfo ▸ hBits
  have hSchemes' : info.schemes = (schemeNodes T).length := hInfo ▸ hSchemes
  obtain ⟨_, hp, hs, ht⟩ := hintArenaFor_workspace S H W info (hintArenaStart D.heap D.stride node)
  change A.workStart = wordsOf W info.payloadBits + 1 at hp
  change A.saveOffset = A.workStart + 2 * info.schemes at hs
  have hWork : A.workStart = wordsOf W M + 1 := by rwa [hBits'] at hp
  have hSav : A.saveOffset = A.workStart + 2 * (schemeNodes T).length := by rwa [hSchemes'] at hs
  have hTran : A.transcript = A.payload + A.saveOffset + 2 := ht
  have hw : word ≤ A.payload := by
    dsimp only [word, HintDecoderPlacement.inputWord]
    split
    · exact Nat.zero_le _
    · exact le_rfl
  change wordsOf W M ≤ A.workStart ∧ UpSaveRoom A.workStart A.saveOffset T ∧
    A.payload + A.saveOffset + 2 = A.transcript ∧ word + wordsOf W M ≤ A.transcript ∧
    (0 < W → (word * W + M) / W < A.transcript)
  refine ⟨by omega, hSav.ge, hTran.symm, by omega, ?_⟩
  intro hW
  rw [Nat.mul_comm word W, Nat.mul_add_div hW]
  have hCover := Nat.div_le_div_right (c := W) (up_words_cover_budget W M hW)
  rw [Nat.mul_comm (wordsOf W M), Nat.mul_div_cancel_left _ hW] at hCover
  omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_localInput
#print axioms LinearSetReconciliation327.Main.hintArenaFor_rowOrder
end S_HintNodeGeometry20261120
section S_HintChildTableReady20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintChildUpdateSchedule_mem (CR : CRFamily) (Bc colBase : ℕ)
    (T : Node) (seed sav : ℕ) (it : UpIt)
    (hi : it ∈ hintChildUpdateSchedule CR Bc colBase T seed sav) :
    it ∈ upSched CR Bc colBase T seed 0 0 sav [] ∨
      it ∈ upSched CR Bc colBase T 0 0 0 sav [] := by
  rw [hintChildUpdateSchedule, List.mem_cons] at hi
  rcases hi with h | h
  · subst it
    right
    rw [upSched_decomp, upHead_zero]
    simp
  · left
    rw [upSched_decomp]
    simp only [List.mem_append] at h
    simp only [List.nil_append, List.mem_append]
    tauto

theorem hintChildTable_ready (S : CRSourceBundle) (H : HintParams) (R T : Node)
    (hT : IsSchemeTree H T) (seedData : (hintSpec R).Seed) (W : ℕ) (det : ℕ → ℕ)
    (Bc control detBase seed sav : ℕ) (hW : 0 < W) (hWord : 16 < 2 ^ W)
    (hFit : (hintSpec R).Fits W)
    (hDims : UpDimsBound (2 ^ W - 1) T) (hStatic : UpTreeStatic (crFamily S) Bc T.N T)
    (hBlock : BlockOf R seed (schemeNodes T))
    (hSeed : seed + (schemeNodes T).length < 2 ^ W) (hBc : Bc + 1 < 2 ^ W) :
    let E := (hintSpec R).env W det seedData
    let CR := crFamily S
    let colBase := hintSubtreeColBase Bc T
    let items := hintChildUpdateSchedule CR Bc colBase T seed sav
    sav + 1 < 2 ^ W →
    synLen CR T < 2 ^ W →
    detBase + colBase + upTabLen Bc T < 2 ^ W →
    (hintSubtreeBlock CR W control Bc T seed sav).At E detBase →
    UpSavedLayout E detBase items ∧
      E.det (detBase % 2 ^ W) % 2 ^ W = items.length ∧ E.det (detBase + 3) = control ∧
      ∀ i < T.N, UpLocalTree CR (upShiftDetEnv E detBase) i Bc colBase T
        (hintKappaAux H R seedData T hT seed) seed 0 0 := by
  let E := (hintSpec R).env W det seedData
  let CR := crFamily S
  let colBase := hintSubtreeColBase Bc T
  let items := hintChildUpdateSchedule CR Bc colBase T seed sav
  dsimp only
  intro hSav hBits hSpace hAt
  change synLen CR T < 2 ^ W at hBits
  change detBase + colBase + upTabLen Bc T < 2 ^ W at hSpace
  have hEnd : colBase + upTabLen Bc T < 2 ^ W := by omega
  have hTotal : detBase + (colBase + upTabLen Bc T) ≤ 2 ^ W := by omega
  have hFields : ∀ it ∈ items, ∀ f < 16, it.fld f < 2 ^ W := by
    have hAll (k : ℕ) (hk : k ≤ seed) :
        ∀ it ∈ upSched CR Bc colBase T k 0 0 sav [], ∀ f < 16, it.fld f < 2 ^ W := by
      intro it hi f hf
      have hF := upSched_fields_le CR Bc colBase (2 ^ W - 1) (by omega) (by omega)
        T k 0 0 sav [] hDims (by omega : k + (schemeNodes T).length ≤ 2 ^ W - 1)
        (by change 0 + synLen CR T ≤ 2 ^ W - 1; omega)
        (by change colBase + 0 + upTabLen Bc T ≤ 2 ^ W - 1; omega)
        (by omega) (by simp) it hi f hf
      omega
    intro it hi
    rcases hintChildUpdateSchedule_mem CR Bc colBase T seed sav it hi with hp | hp
    · exact hAll seed (Nat.le_refl _) it hp
    · exact hAll 0 (Nat.zero_le _) it hp
  have hValid : ∀ it ∈ items, UpItemKind it ∧ it.sav + 1 < 2 ^ W := by
    intro it hi
    rcases hintChildUpdateSchedule_mem CR Bc colBase T seed sav it hi with hp | hp
    · exact upSched_valid_records CR Bc colBase T seed 0 0 sav W hSav hBc it hp
    · exact upSched_valid_records CR Bc colBase T 0 0 0 sav W hSav hBc it hp
  have hSpecs := hintSubtreeBlock_specs CR E control Bc T seed sav detBase hAt hEnd hTotal
    hFields (fun it hi => (hValid it hi).1) (fun it hi _ => (hValid it hi).2)
  refine ⟨hSpecs.1, hSpecs.2.1, hSpecs.2.2, ?_⟩
  intro i _
  have hBase : 4 < colBase := by unfold colBase hintSubtreeColBase; omega
  have hAt' : ∀ q < colBase + upTabLen Bc T,
      det (detBase + q) = hintSubtreeDet W control colBase items (upTabFun CR Bc T 0) q := hAt
  exact hintSubtreeLocal_of_placed CR H R T hT seedData W det detBase control Bc colBase T.N i seed
    items (upTabFun CR Bc T 0) (by omega) hW hFit hBase
    (Nat.le_trans hDims.universe (Nat.sub_le _ _)) hBlock hStatic
    (upTabFullTree_self CR Bc T 0) hEnd hBits hTotal hAt'

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintChildTable_ready
end S_HintChildTableReady20261120


