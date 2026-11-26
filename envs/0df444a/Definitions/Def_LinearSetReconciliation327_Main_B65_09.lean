-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_09
-- name    : LinearSetReconciliation327_Main_B65_09
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T08:13:51.698912+00:00
-- url     : https://prove2.me/theorems/941a8804-388d-57ea-8ba1-d23ad727e548
-- title:
--   Theorem 6.5 supporting machine proof B65_09
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_09Part1
set_option autoImplicit false

section S_HintWorkspaceRecord20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintRowWorkspace_record (E : RAMEnv) (descriptor start a K BY node row steps h : ℕ)
    (F : HintRowFields)
    (hAt : let S := hintRowWorkspace start a K BY node row steps K
      (hintRowDetBlock S.parent (F.value S.gauss)).At E descriptor)
    (hWord : 30 < 2 ^ E.W) (hDet : descriptor + 31 ≤ 2 ^ E.W)
    (hParent : (hintRowWorkspace start a K BY node row steps K).parent + 30 ≤ 2 ^ E.W)
    (hFits : ∀ i < 30,
      F.value (hintRowWorkspace start a K BY node row steps K).gauss i < 2 ^ E.W) :
    let S := hintRowWorkspace start a K BY node row steps h
    HintRowRecord E descriptor S.parent (F.value S.gauss) := by
  let S := hintRowWorkspace start a K BY node row steps h
  let Smax := hintRowWorkspace start a K BY node row steps K
  have hValues (i : ℕ) (hi : i < 30) : F.value S.gauss i = F.value Smax.gauss i :=
    HintRowFields.hints_irrel F Smax.gauss h i hi
  refine HintRowRecord.of_block E descriptor S.parent (F.value S.gauss) ?_ hWord hDet hParent ?_
  · intro i hi
    cases i with
    | zero =>
        exact hAt 0 (by change 0 < 31; decide)
    | succ i =>
        have hi' : i < 30 := by change i + 1 < 31 at hi; omega
        change E.det (descriptor + (i + 1)) = F.value S.gauss i
        rw [hValues i hi']
        exact hAt (i + 1) hi
  · intro i hi
    rw [hValues i hi]
    exact hFits i hi

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowWorkspace_record
end S_HintWorkspaceRecord20261120
section S_HintPackedRead20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintBitAt_aligned {M : ℕ} (mem : ℕ → ℕ) (W base : ℕ)
    (y : Fin M → ZMod 2) (i : Fin M) (hw : 0 < W)
    (hPacked : ∀ a < wordsOf W M, mem (base + a) = packMem W y a) :
    bitAt mem W 0 (base * W + i.val) = if y i = 1 then 1 else 0 := by
  classical
  have hDiv : (base * W + i.val) / W = base + i.val / W := by
    rw [Nat.mul_comm base W, Nat.mul_add_div hw]
  have hMod : (base * W + i.val) % W = i.val % W := by
    rw [Nat.mul_comm base W, Nat.mul_add_mod]
  have hAddr := crBit_div_lt_words hw i.isLt
  unfold bitAt
  rw [Nat.zero_add, hDiv, hMod, hPacked _ hAddr, Nat.mod_eq_of_lt (packMem_lt W hw y _)]
  have hParts : i.val / W * W + i.val % W = i.val := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod _ _
  let b := packMem W y (i.val / W) / 2 ^ (i.val % W) % 2
  have hTest : decide (b = 1) = decide (∃ p : Fin M, p.val = i.val ∧ y p = 1) := by
    dsimp only [b]
    rw [← Nat.testBit_eq_decide_div_mod_eq, testBit_packMem W hw y _ _ (Nat.mod_lt _ hw), hParts]
  change b = if y i = 1 then 1 else 0
  by_cases hY : y i = 1
  · rw [if_pos hY]
    apply of_decide_eq_true
    rw [hTest]
    exact decide_eq_true ⟨i, rfl, hY⟩
  · have hNo : ¬ ∃ p : Fin M, p.val = i.val ∧ y p = 1 := by
      rintro ⟨p, hpi, hp⟩
      have he : p = i := Fin.ext hpi
      exact hY (he ▸ hp)
    have hNe : b ≠ 1 := by
      intro h
      rw [decide_eq_true h, decide_eq_false hNo] at hTest
      cases hTest
    have hBound : b < 2 := Nat.mod_lt _ (by decide)
    rw [if_neg hY]
    omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintBitAt_aligned
end S_HintPackedRead20261120
section S_HintToggleTrace20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintSketchVector (CR : CRFamily) (T : Node) (r : T.Seed) (X : Finset ℕ) :
    Fin (synLen CR T) → ZMod 2 :=
  fun i => bitVal CR T r i X

theorem hintSketchVector_empty (CR : CRFamily) (T : Node) (r : T.Seed) :
    hintSketchVector CR T r ∅ = 0 := by
  funext i
  exact bitVal_empty CR T r i

theorem hintSketchVector_xor (CR : CRFamily) (T : Node) (r : T.Seed) (X Y : Finset ℕ) :
    hintSketchVector CR T r (symmDiff X Y) =
      hintSketchVector CR T r X + hintSketchVector CR T r Y := by
  funext i
  exact bitVal_symmDiff CR T r i X Y

theorem hintToggleTrace_step (CR : CRFamily) (T : Node) (r : T.Seed) (P : Finset ℕ)
    (y : Fin (synLen CR T) → ZMod 2) (i : Fin T.N) :
    (if hintTruth (i.val ∈ P) = 0 then y + hintSketchVector CR T r (P ∩ Finset.range i.val)
      else y + hintSketchVector CR T r (P ∩ Finset.range i.val) + hintChildToggleVec CR T r i) =
      y + hintSketchVector CR T r (P ∩ Finset.range (i.val + 1)) := by
  classical
  by_cases hi : i.val ∈ P
  · have hSet : P ∩ Finset.range (i.val + 1) =
        symmDiff (P ∩ Finset.range i.val) {i.val} := by
      ext q
      by_cases hq : q = i.val
      · subst q
        simp [hi, Finset.mem_symmDiff]
      · have hlt : q < i.val + 1 ↔ q < i.val := by omega
        simp [Finset.mem_symmDiff, hq, hlt]
    rw [hSet, hintSketchVector_xor]
    simp only [hintTruth, if_pos hi, Nat.one_ne_zero, if_false]
    change y + hintSketchVector CR T r (P ∩ Finset.range i.val) + hintSketchVector CR T r {i.val} = _
    exact add_assoc _ _ _
  · have hSet : P ∩ Finset.range (i.val + 1) = P ∩ Finset.range i.val := by
      ext q
      by_cases hq : q = i.val
      · subst q
        simp [hi]
      · have hlt : q < i.val + 1 ↔ q < i.val := by omega
        simp [hlt]
    rw [hSet]
    simp [hintTruth, hi]

theorem hintToggleTrace_end (CR : CRFamily) (T : Node) (r : T.Seed) (P : Finset ℕ)
    (hP : P ⊆ Finset.range T.N) :
    hintSketchVector CR T r (P ∩ Finset.range T.N) = hintSketchVector CR T r P := by
  rw [Finset.inter_eq_left.mpr hP]

theorem hintRecoverColumn_exact (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (s : Fin sch.ℓ) (j : Fin sch.m) :
    (if j.val ∈ sch.exactP lr x J s then (1 : ZMod 2) else 0) +
      (if j.val ∈ sch.exactChildInput lr x J s then 1 else 0) =
      (if j.val ∈ sch.column lr x s then 1 else 0) := by
  classical
  rw [RowScheme.exactChildInput, ite_mem_symmDiff]
  by_cases h : j.val ∈ sch.exactP lr x J s <;>
    by_cases hCol : j.val ∈ sch.column lr x s <;> simp [h, hCol] <;> decide

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintToggleTrace_step
#print axioms LinearSetReconciliation327.Main.hintRecoverColumn_exact
end S_HintToggleTrace20261120
section S_HintPackedNodeRead20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintDirectPackedBit {CR : CRFamily} (E : RAMEnv) (mem : ℕ → ℕ)
    (word : ℕ) (sch : RowScheme) (t : ℕ) (r : sch.LocalSeed) (x : Finset ℕ)
    (j : Fin sch.m) (s : Fin sch.ℓ) (hW : 0 < E.W)
    (hPacked : ∀ a < wordsOf E.W (synLen CR (.direct sch t)),
      mem (word + a) = packMem E.W (hintSketchVector CR (.direct sch t) r x) a) :
    bitAt mem E.W 0 (word * E.W + j.val * sch.ℓ + s.val) =
      (sch.code j (r.2 j) (sch.rowOf r x j) s).val := by
  let q := finProdFinEquiv (j, s)
  let i : Fin (synLen CR (.direct sch t)) := Fin.castAdd (CR.rows sch.N t) q
  have hI : i.val = j.val * sch.ℓ + s.val := by
    change s.val + sch.ℓ * j.val = j.val * sch.ℓ + s.val
    rw [Nat.mul_comm sch.ℓ, Nat.add_comm]
  have hCode : hintSketchVector CR (.direct sch t) r x i = sch.code j (r.2 j) (sch.rowOf r x j) s := by
    unfold hintSketchVector
    change bitVal CR (.direct sch t) r (Fin.castAdd (CR.rows sch.N t) (finProdFinEquiv (j, s))) x = _
    simpa only [q, Equiv.symm_apply_apply] using
      (bitVal_direct_left (CR := CR) (sch := sch) (t := t) r x q)
  have hRead := hintBitAt_aligned mem E.W word _ i hW hPacked
  rw [hCode, hI, ← Nat.add_assoc] at hRead
  have hBinary : ∀ bit : ZMod 2, bit = 0 ∨ bit = 1 := by decide
  rcases hBinary (sch.code j (r.2 j) (sch.rowOf r x j) s) with h | h
  · rw [h] at hRead ⊢
    simpa using hRead
  · rw [h] at hRead ⊢
    simpa only [if_true, eq_self, show (1 : ZMod 2).val = 1 by decide] using hRead

theorem hintRecursivePackedChild {CR : CRFamily} (E : RAMEnv) (mem : ℕ → ℕ)
    (word : ℕ) (sch : RowScheme) (t : ℕ) (Xs Ys : Fin sch.ℓ → ℕ)
    (child : Fin sch.ℓ → Node) (r : Node.Seed (.recursive sch t Xs Ys child)) (x : Finset ℕ)
    (s : Fin sch.ℓ) (j : Fin (synLen CR (child s))) (hW : 0 < E.W)
    (hPacked : ∀ a < wordsOf E.W (synLen CR (.recursive sch t Xs Ys child)),
      mem (word + a) = packMem E.W (hintSketchVector CR (.recursive sch t Xs Ys child) r x) a) :
    bitAt mem E.W 0
      (word * E.W + ((List.ofFn fun z => synLen CR (child z)).take s.val).sum + j.val) =
      if hintSketchVector CR (child s) (r.2 s) (sch.column r.1 x s) j = 1 then 1 else 0 := by
  let q := finSigmaFinEquiv (⟨s, j⟩ : Sigma fun z : Fin sch.ℓ => Fin (synLen CR (child z)))
  let i : Fin (synLen CR (.recursive sch t Xs Ys child)) := Fin.castAdd (CR.rows sch.N t) q
  have hI : i.val = ((List.ofFn fun z => synLen CR (child z)).take s.val).sum + j.val :=
    finSigmaFinEquiv_val (fun z => synLen CR (child z)) s j
  have hChild : hintSketchVector CR (.recursive sch t Xs Ys child) r x i =
      hintSketchVector CR (child s) (r.2 s) (sch.column r.1 x s) j := by
    unfold hintSketchVector
    change bitVal CR (.recursive sch t Xs Ys child) r
      (Fin.castAdd (CR.rows sch.N t)
        (finSigmaFinEquiv (⟨s, j⟩ : Sigma fun z : Fin sch.ℓ => Fin (synLen CR (child z))))) x = _
    rw [bitVal_rec_left, Equiv.symm_apply_apply]
  have hRead := hintBitAt_aligned mem E.W word _ i hW hPacked
  simpa only [hChild, hI, Nat.add_assoc] using hRead

theorem hintTruePrefix_ofFn (sch : RowScheme) (lr : sch.LocalSeed) (x : Finset ℕ)
    (a : ℕ) (ha : a ≤ sch.ℓ) (j : Fin sch.m) :
    List.ofFn (fun s : Fin a => sch.code j (lr.2 j) (sch.rowOf lr x j) ⟨s.val, s.isLt.trans_le ha⟩) =
      sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) a := by
  unfold RowScheme.truePrefix
  apply List.ext_getElem
  · simp [Nat.min_eq_left ha]
  · intro k hk0 hk1
    simp [List.getElem_map, List.getElem_take, List.getElem_finRange, List.getElem_ofFn]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectPackedBit
#print axioms LinearSetReconciliation327.Main.hintRecursivePackedChild
#print axioms LinearSetReconciliation327.Main.hintTruePrefix_ofFn
end S_HintPackedNodeRead20261120
section S_HintPackedResidual20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintPackedRight {CR : CRFamily} (E : RAMEnv) (T : Node) (r : T.Seed)
    (x : Finset ℕ) (mem : ℕ → ℕ) (word leftLen N t : ℕ)
    (hLen : synLen CR T = leftLen + CR.rows N t) (hW : 0 < E.W)
    (hPacked : ∀ a < wordsOf E.W (synLen CR T),
      mem (word + a) = packMem E.W (hintSketchVector CR T r x) a)
    (hRight : ∀ q : Fin (CR.rows N t),
      bitVal CR T r (Fin.cast hLen.symm (Fin.natAdd leftLen q)) x =
        if q.val ∈ CR.sketch N t x then 1 else 0)
    (q : Fin (CR.rows N t)) :
    bitAt mem E.W 0 (word * E.W + leftLen + q.val) =
      hintTruth (q.val ∈ CR.sketch N t x) := by
  let i : Fin (synLen CR T) := Fin.cast hLen.symm (Fin.natAdd leftLen q)
  have hRead := hintBitAt_aligned mem E.W word (hintSketchVector CR T r x) i hW hPacked
  change bitAt mem E.W 0 (word * E.W + (leftLen + q.val)) =
    (if bitVal CR T r i x = 1 then 1 else 0) at hRead
  dsimp only [i] at hRead
  rw [hRight q] at hRead
  by_cases h : q.val ∈ CR.sketch N t x <;> simpa [h, hintTruth, Nat.add_assoc] using hRead

theorem hintDirectPackedResidual {CR : CRFamily} (E : RAMEnv) (mem : ℕ → ℕ) (word : ℕ)
    (sch : RowScheme) (t : ℕ) (r : (Node.direct sch t).Seed) (x : Finset ℕ) (hW : 0 < E.W)
    (hPacked : ∀ a < wordsOf E.W (synLen CR (.direct sch t)),
      mem (word + a) = packMem E.W (hintSketchVector CR (.direct sch t) r x) a)
    (q : Fin (CR.rows sch.N t)) :
    bitAt mem E.W 0 (word * E.W + sch.m * sch.ℓ + q.val) =
      hintTruth (q.val ∈ CR.sketch sch.N t x) :=
  hintPackedRight E (.direct sch t) r x mem word (sch.m * sch.ℓ) sch.N t rfl hW hPacked
    (fun z => bitVal_direct_right (CR := CR) (sch := sch) (t := t) r x z) q

theorem hintRecursivePackedResidual {CR : CRFamily} (E : RAMEnv) (mem : ℕ → ℕ) (word : ℕ)
    (sch : RowScheme) (t : ℕ) (Xs Ys : Fin sch.ℓ → ℕ) (child : Fin sch.ℓ → Node)
    (r : (Node.recursive sch t Xs Ys child).Seed) (x : Finset ℕ) (hW : 0 < E.W)
    (hPacked : ∀ a < wordsOf E.W (synLen CR (.recursive sch t Xs Ys child)),
      mem (word + a) = packMem E.W (hintSketchVector CR (.recursive sch t Xs Ys child) r x) a)
    (q : Fin (CR.rows sch.N t)) :
    bitAt mem E.W 0 (word * E.W + (∑ s, synLen CR (child s)) + q.val) =
      hintTruth (q.val ∈ CR.sketch sch.N t x) :=
  hintPackedRight E (.recursive sch t Xs Ys child) r x mem word (∑ s, synLen CR (child s))
    sch.N t rfl hW hPacked
    (fun z => bitVal_rec_right (CR := CR) (sch := sch) (t := t) (child := child) r x z) q

theorem hintCRBit_eq (S : CRSourceBundle) (N t : ℕ) (x : Finset ℕ)
    (hx : x ⊆ Finset.range N) (q : Fin (S.data N t).R) :
    hintTruth (q.val ∈ (crFamily S).sketch N t x) =
      if (S.data N t).H (crInput N x) q = 1 then 1 else 0 := by
  rw [crFamily_sketch S N t x hx]
  classical
  have h : q.val ∈ support ((S.data N t).H (crInput N x)) ↔
      (S.data N t).H (crInput N x) q = 1 := by
    unfold support
    constructor
    · intro h
      obtain ⟨i, hi, hiq⟩ := Finset.mem_image.mp h
      have he : i = q := Fin.ext hiq
      subst i
      exact (Finset.mem_filter.mp hi).2
    · intro h
      exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
  simp only [hintTruth, h]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectPackedResidual
#print axioms LinearSetReconciliation327.Main.hintRecursivePackedResidual
#print axioms LinearSetReconciliation327.Main.hintCRBit_eq
end S_HintPackedResidual20261120
section S_HintDirectBit20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintTranscriptCell (transcript rows row column : ℕ) : ℕ :=
  transcript + column * rows + row

def hintDirectBitBlock (W transcript rows row column offset : ℕ) : HintDetBlock :=
  hintUnpackDetBlock (hintTranscriptCell transcript rows row column) offset W 1

theorem hintDirectBit_sem {CR : CRFamily} (P : Program) (E : RAMEnv) (state : RAMState)
    (sch : RowScheme) (t : ℕ) (r : sch.LocalSeed) (x : Finset ℕ)
    (j : Fin sch.m) (s : Fin sch.ℓ) (word transcript descriptor base : ℕ)
    (hPacked : ∀ a < wordsOf E.W (synLen CR (.direct sch t)),
      state.mem (word + a) = packMem E.W (hintSketchVector CR (.direct sch t) r x) a)
    (hArg : state.regs 6 = descriptor)
    (hWord : 2 < 2 ^ E.W) (hDescSpan : descriptor + 3 < 2 ^ E.W)
    (hRead : (hintDirectBitBlock E.W transcript sch.m j.val s.val
      (word * E.W + j.val * sch.ℓ + s.val)).At E descriptor)
    (pre : HintUnpackPre E (hintTranscriptCell transcript sch.m j.val s.val)
      (word * E.W + j.val * sch.ℓ + s.val) 1)
    (hAt : At P base (hintUnpackAction.compile base)) (hPc : state.pc = base) :
    let dest := hintTranscriptCell transcript sch.m j.val s.val
    Sem P E base (base + 22) state (fun k out => k ≤ 24 ∧
      out.regs 14 = state.regs 14 ∧
      out.mem dest = (sch.code j (r.2 j) (sch.rowOf r x j) s).val ∧
      CRMemFrame dest (dest + 1) state.mem out.mem) := by
  let dest := hintTranscriptCell transcript sch.m j.val s.val
  let offset := word * E.W + j.val * sch.ℓ + s.val
  have hDest : dest < 2 ^ E.W := Nat.lt_of_succ_le pre.destination
  have hOffset : offset < 2 ^ E.W := Nat.lt_of_succ_le pre.offset_span
  have hTable := HintUnpackTable.of_block E descriptor dest offset 1 hRead
    hWord hDescSpan hDest hOffset pre.count_fit
  apply Sem.mono (hintUnpackAction_sem P E state descriptor dest offset 1 base hTable hArg pre hAt hPc)
  rintro k out ⟨hk, hCtx, hData, hFrame⟩
  have hBit := hintDirectPackedBit (CR := CR) E state.mem word sch t r x j s pre.positive hPacked
  have hCell := hData 0 (by decide)
  simp only [Nat.add_zero] at hCell
  exact ⟨by simpa using hk, hCtx, hCell.trans hBit, hFrame⟩

theorem hintExactEstimate_mem (sch : RowScheme) (lr : sch.LocalSeed)
    (x J : Finset ℕ) (i : Fin sch.N) (j : Fin sch.m)
    (hRow : (lr.1 i).val % sch.m = j.val) :
    i.val ∈ sch.exactEstimate lr x J ↔ (lr.1 i).val / sch.m ∈ sch.exactRowEst lr x J j := by
  classical
  unfold RowScheme.exactEstimate RowScheme.assembled assemble
  constructor
  · intro hi
    obtain ⟨u, hu, hui⟩ := Finset.mem_image.mp hi
    have he : u = i := Fin.ext hui
    subst u
    have h := (Finset.mem_filter.mp hu).2
    simpa only [hRow, dif_pos j.isLt, RowScheme.exactRowEst] using h
  · intro hi
    refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    simpa only [hRow, dif_pos j.isLt, RowScheme.exactRowEst] using hi

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectBit_sem
#print axioms LinearSetReconciliation327.Main.hintExactEstimate_mem
end S_HintDirectBit20261120
section S_HintStageChildExact20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintStageChild_exact {CR : CRFamily} (P : Program) (E : RAMEnv) (state : RAMState)
    (sch : RowScheme) (t : ℕ) (Xs Ys : Fin sch.ℓ → ℕ) (child : Fin sch.ℓ → Node)
    (r : (Node.recursive sch t Xs Ys child).Seed) (x : Finset ℕ) (s : Fin sch.ℓ)
    (word dest descriptor base : ℕ)
    (hPacked : ∀ a < wordsOf E.W (synLen CR (.recursive sch t Xs Ys child)),
      state.mem (word + a) = packMem E.W (hintSketchVector CR (.recursive sch t Xs Ys child) r x) a)
    (hWord : 2 < 2 ^ E.W) (hSpan : descriptor + 3 < 2 ^ E.W) (hDest : dest < 2 ^ E.W)
    (hTable : let off := word * E.W + ((List.ofFn fun z => synLen CR (child z)).take s.val).sum
      (hintUnpackDetBlock dest off E.W (synLen CR (child s))).At E descriptor)
    (pre : let off := word * E.W + ((List.ofFn fun z => synLen CR (child z)).take s.val).sum
      HintStagePre E E.W (synLen CR (child s)) off dest)
    (hFresh : ∀ a < wordsOf E.W (synLen CR (child s)), state.mem (dest + a) = 0)
    (hArg : state.regs 6 = descriptor)
    (hAt : At P base (hintStageAction.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 28) state (fun k out =>
      k ≤ 17 * synLen CR (child s) + 13 ∧
      out.regs 14 = state.regs 14 ∧
      (∀ a < wordsOf E.W (synLen CR (child s)), out.mem (dest + a) =
        packMem E.W (hintSketchVector CR (child s) (r.2 s) (sch.column r.1 x s)) a) ∧
      CRMemFrame dest (dest + wordsOf E.W (synLen CR (child s))) state.mem out.mem) := by
  let off := word * E.W + ((List.ofFn fun z => synLen CR (child z)).take s.val).sum
  let count := synLen CR (child s)
  have span : off + count < 2 ^ E.W := pre.input_span
  have hAbi := HintUnpackTable.of_block E descriptor dest off count hTable hWord hSpan hDest (by omega) (by omega)
  apply hintStageAction_sem P E state descriptor dest off count base hAbi hArg pre
    (hintSketchVector CR (child s) (r.2 s) (sch.column r.1 x s)) _ hFresh hAt hPc
  intro i
  exact hintRecursivePackedChild E state.mem word sch t Xs Ys child r x s i pre.width_pos hPacked

theorem hintCRStage_exact (S : CRSourceBundle) (P : Program) (E : RAMEnv) (state : RAMState)
    (N t descriptor dest offset base : ℕ) (x : Finset ℕ) (hx : x ⊆ Finset.range N)
    (hWord : 2 < 2 ^ E.W) (hSpan : descriptor + 3 < 2 ^ E.W) (hDest : dest < 2 ^ E.W)
    (hTable : (hintUnpackDetBlock dest offset E.W (S.data N t).R).At E descriptor)
    (pre : HintStagePre E E.W (S.data N t).R offset dest)
    (hBits : ∀ q : Fin (S.data N t).R, bitAt state.mem E.W 0 (offset + q.val) =
      hintTruth (q.val ∈ (crFamily S).sketch N t x))
    (hFresh : ∀ a < wordsOf E.W (S.data N t).R, state.mem (dest + a) = 0)
    (hArg : state.regs 6 = descriptor)
    (hAt : At P base (hintStageAction.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 28) state (fun k out =>
      k ≤ 17 * (S.data N t).R + 13 ∧ out.regs 14 = state.regs 14 ∧
      (∀ a < wordsOf E.W (S.data N t).R, out.mem (dest + a) =
        packMem E.W ((S.data N t).H (crInput N x)) a) ∧
      CRMemFrame dest (dest + wordsOf E.W (S.data N t).R) state.mem out.mem) := by
  have span := pre.input_span
  have hAbi := HintUnpackTable.of_block E descriptor dest offset _ hTable hWord hSpan hDest
    (by omega) (by omega)
  apply hintStageAction_sem P E state descriptor dest offset _ base hAbi hArg pre
    ((S.data N t).H (crInput N x)) _ hFresh hAt hPc
  intro q
  exact (hBits q).trans (hintCRBit_eq S N t x hx q)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintStageChild_exact
#print axioms LinearSetReconciliation327.Main.hintCRStage_exact
end S_HintStageChildExact20261120
section S_HintCombineBitmaps20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintColumnAddBlock (dest source count : ℕ) : HintDetBlock where
  length := 3
  value
    | 0 => dest
    | 1 => source
    | 2 => count
    | _ => 0

theorem HintColumnAddTable.of_block (E : RAMEnv) (descriptor dest source count : ℕ)
    (hAt : (hintColumnAddBlock dest source count).At E descriptor)
    (hWord : 1 < 2 ^ E.W) (hSpan : descriptor + 2 < 2 ^ E.W)
    (hDest : dest < 2 ^ E.W) (hSource : source < 2 ^ E.W)
    (hDestSpan : dest + count ≤ 2 ^ E.W) (hSourceSpan : source + count ≤ 2 ^ E.W)
    (hCount : count < 2 ^ E.W) :
    HintColumnAddTable E descriptor dest source count :=
  ⟨hWord, hSpan, hDest, hSource, hDestSpan, hSourceSpan, hCount,
    hAt 0 (by change 0 < 3; decide), hAt 1 (by change 1 < 3; decide), hAt 2 (by change 2 < 3; decide)⟩

def hintGateBlock (gate coordinate detBase payBase : ℕ) : HintDetBlock where
  length := 4
  value
    | 0 => gate
    | 1 => coordinate
    | 2 => detBase
    | 3 => payBase
    | _ => 0

theorem HintToggleGateTable.of_block (E : RAMEnv) (descriptor gate coordinate detBase payBase control : ℕ)
    (hAt : (hintGateBlock gate coordinate detBase payBase).At E descriptor)
    (hWord : 3 < 2 ^ E.W) (hSpan : descriptor + 3 < 2 ^ E.W)
    (hTable : detBase + 3 < 2 ^ E.W)
    (hGate : gate < 2 ^ E.W) (hCoordinate : coordinate < 2 ^ E.W)
    (hPayload : payBase < 2 ^ E.W) (hControl : control < 2 ^ E.W)
    (hReturn : E.det (detBase + 3) = control) :
    HintToggleGateTable E descriptor gate coordinate detBase payBase control :=
  ⟨hWord, hSpan, hTable, hGate, hCoordinate, hPayload, hControl,
    hAt 0 (by change 0 < 4; decide), hAt 1 (by change 1 < 4; decide),
    hAt 2 (by change 2 < 4; decide), hAt 3 (by change 3 < 4; decide), hReturn⟩

def HintBitmap (mem : ℕ → ℕ) (base N : ℕ) (A : Finset ℕ) : Prop :=
  ∀ i < N, mem (base + i) = hintTruth (i ∈ A)

theorem hintAddBitmaps_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (descriptor dest source N base : ℕ) (X Y : Finset ℕ)
    (tbl : HintColumnAddTable E descriptor dest source N) (hArg : state.regs 6 = descriptor)
    (hX : HintBitmap state.mem dest N X) (hY : HintBitmap state.mem source N Y)
    (hSeparate : dest + N ≤ source ∨ source + N ≤ dest)
    (hAt : At P base (hintColumnAddAction.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 20) state (fun k out =>
      k ≤ 11 * N + 11 ∧ out.regs 14 = state.regs 14 ∧
      HintBitmap out.mem dest N (symmDiff X Y) ∧
      CRMemFrame dest (dest + N) state.mem out.mem) := by
  let f := fun j : ℕ => if j ∈ X then (1 : ZMod 2) else 0
  let g := fun j : ℕ => if j ∈ Y then (1 : ZMod 2) else 0
  have hBit (j : ℕ) (S : Finset ℕ) :
      (if j ∈ S then (1 : ZMod 2) else 0).val = hintTruth (j ∈ S) := by
    by_cases h : j ∈ S
    · rw [if_pos h, hintTruth, if_pos h]
      decide
    · rw [if_neg h, hintTruth, if_neg h]
      decide
  have hf (i : ℕ) (hi : i < N) : state.mem (dest + i) = (f i).val :=
    (hX i hi).trans (hBit i X).symm
  have hg (i : ℕ) (hi : i < N) : state.mem (source + i) = (g i).val :=
    (hY i hi).trans (hBit i Y).symm
  apply Sem.mono (hintColumnAddAction_sem P E state descriptor dest source N base f g tbl hArg
    hf hg hSeparate hAt hPc)
  rintro k out ⟨hk, hc, hOut, hFrame⟩
  refine ⟨hk, hc, ?_, hFrame⟩
  intro i hi
  rw [hOut i hi, ← hBit]
  change (f i + g i).val = _
  unfold f g
  rw [ite_mem_symmDiff]

theorem hintPlusResidual (x estimate : Finset ℕ) : symmDiff estimate (symmDiff x estimate) = x := by
  ext a
  simp only [Finset.mem_symmDiff]
  tauto

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintToggleGateTable.of_block
#print axioms LinearSetReconciliation327.Main.hintAddBitmaps_sem
#print axioms LinearSetReconciliation327.Main.hintPlusResidual
end S_HintCombineBitmaps20261120
section S_HintEventRecord20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintDecoderPlacement where
  width : ℕ
  control : ℕ
  rowScratch : ℕ
  info : ℕ → HintNodeInfo
  arena : ℕ → HintNodeArena
  threshold : ℕ → ℕ → ℕ
  updateTable : ℕ → ℕ
  residualTable : ℕ → ℕ
  crTable : ℕ → ℕ

def HintDecoderPlacement.inputWord (L : HintDecoderPlacement) (node : ℕ) : ℕ :=
  if node = 0 then 0 else (L.arena node).payload

noncomputable def hintRowEventBlock (H : HintParams) (L : HintDecoderPlacement)
    (node seed row prefixLen output abstentions : ℕ) : HintDetBlock :=
  let info := L.info node
  let N := info.universeSize
  let (X, Y) := info.rowParams.getD (0, 0)
  let A := L.arena node
  let K := H.Nmax N X Y
  let BY := H.BY N X Y
  let m := H.rows X Y
  let S := hintRowWorkspace L.rowScratch prefixLen K BY seed row (H.ell N X Y) K
  let F := S.fields (rowLen N m row) m A.hints (A.transcript + row)
    (H.BX N X Y) BY (L.threshold node row) output abstentions
  hintRowDetBlock S.parent (F.value S.gauss)

noncomputable def hintCREventBlock (S : CRSourceBundle) (L : HintDecoderPlacement)
    (node offset destination N t : ℕ) : HintDetBlock :=
  let data := S.data N t
  let A := hintCRArea data.W offset (L.arena node).crRegisters (L.crTable node) 0 destination L.control
  hintCRCallBlock A L.width data.W data.R (crSourceSteps S N t) N

noncomputable def hintEventRecord (S : CRSourceBundle) (H : HintParams) (L : HintDecoderPlacement) :
    HintTreeEvent → HintDetBlock
  | .store node offset count => hintUnpackDetBlock (L.arena node).result offset L.width count
  | .directBit node row col offset =>
      let (X, Y) := (L.info node).rowParams.getD (0, 0)
      hintDirectBitBlock L.width (L.arena node).transcript (H.rows X Y) row col offset
  | .childCopy _ _ child offset count => hintUnpackDetBlock (L.arena child).payload offset L.width count
  | .residualCopy node offset count => hintUnpackDetBlock (L.arena node).residual offset L.width count
  | .predict node seed col row =>
      let info := L.info node
      let (X, Y) := info.rowParams.getD (0, 0)
      let child := info.children[col]?.getD 0
      hintRowEventBlock H L node seed row col
        ((L.arena node).transcript + col * H.rows X Y) (L.arena child).hints
  | .finishRow node seed row =>
      let info := L.info node
      let (X, Y) := info.rowParams.getD (0, 0)
      hintRowEventBlock H L node seed row (H.ell info.universeSize X Y) (L.arena node).result 0
  | .childToggle parent col child _ coord =>
      let (X, Y) := (L.info parent).rowParams.getD (0, 0)
      hintGateBlock ((L.arena parent).transcript + col * H.rows X Y + coord) coord
        (L.updateTable child) (L.arena child).payload
  | .residualToggle node coord =>
      hintGateBlock ((L.arena node).result + coord) coord (L.residualTable node) (L.arena node).residual
  | .recoverColumn parent col child =>
      let (X, Y) := (L.info parent).rowParams.getD (0, 0)
      hintColumnAddBlock ((L.arena parent).transcript + col * H.rows X Y)
        (L.arena child).result (H.rows X Y)
  | .correctEstimate node =>
      hintColumnAddBlock (L.arena node).result (L.arena node).residualBitmap (L.info node).universeSize
  | .decodeLeaf node offset N t => hintCREventBlock S L node offset (L.arena node).result N t
  | .decodeResidual node N t =>
      hintCREventBlock S L node ((L.arena node).residual * L.width) (L.arena node).residualBitmap N t

def HintTreeEvent.recordLength : HintTreeEvent → ℕ
  | .store .. | .directBit .. | .childCopy .. | .residualCopy ..
  | .childToggle .. | .residualToggle .. => 4
  | .predict .. | .finishRow .. => 31
  | .recoverColumn .. | .correctEstimate .. => 3
  | .decodeLeaf .. | .decodeResidual .. => 12

theorem hintEventRecord_length (S : CRSourceBundle) (H : HintParams) (L : HintDecoderPlacement)
    (e : HintTreeEvent) : (hintEventRecord S H L e).length = e.recordLength := by
  cases e <;> rfl

theorem hintEventRecord_nonempty (S : CRSourceBundle) (H : HintParams) (L : HintDecoderPlacement)
    (e : HintTreeEvent) : 0 < (hintEventRecord S H L e).length := by
  rw [hintEventRecord_length]
  cases e <;> simp [HintTreeEvent.recordLength]

theorem hintCREventBlock_descriptor (S : CRSourceBundle) (L : HintDecoderPlacement)
    (node offset destination N t descriptor : ℕ) :
    hintCREventBlock S L node offset destination N t =
      hintCRCallBlock
        (hintCRArea (S.data N t).W offset (L.arena node).crRegisters (L.crTable node) descriptor destination L.control)
        L.width (S.data N t).W (S.data N t).R (crSourceSteps S N t) N := by
  rfl

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintEventRecord_nonempty
#print axioms LinearSetReconciliation327.Main.hintCREventBlock_descriptor
end S_HintEventRecord20261120
section S_HintTreeDet20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintEventDescriptor (header : ℕ) (events : List HintTreeEvent)
    (record : HintTreeEvent → HintDetBlock) (j : ℕ) : ℕ :=
  header + 16 + 2 * events.length + hintDetBlockOffset (events.map record) j

def hintTreeEntries (header : ℕ) (events : List HintTreeEvent)
    (record : HintTreeEvent → HintDetBlock) : List (ℕ × ℕ) :=
  List.ofFn fun j : Fin events.length =>
    (events[j.val].tag, hintEventDescriptor header events record j.val)

def hintTreeDetBlocks (previous : ℕ → ℕ) (header control hintMap resultMap listBase N : ℕ)
    (events : List HintTreeEvent) (record : HintTreeEvent → HintDetBlock) (aux : List HintDetBlock) :
    List HintDetBlock :=
  hintRootDetBlock previous control hintMap resultMap listBase (header + 16) events.length N ::
    hintDispatchDetBlock (hintTreeEntries header events record) :: (events.map record ++ aux)

theorem hintTreeEntries_length (header : ℕ) (events : List HintTreeEvent)
    (record : HintTreeEvent → HintDetBlock) :
    (hintTreeEntries header events record).length = events.length := by
  simp [hintTreeEntries]

theorem hintEventDescriptor_end (header : ℕ) (events : List HintTreeEvent)
    (record : HintTreeEvent → HintDetBlock) (j : Fin events.length) :
    hintEventDescriptor header events record j.val + (record events[j.val]).length ≤
      header + 16 + 2 * events.length + hintDetBlockOffset (events.map record) events.length := by
  let lengths := (events.map record).map HintDetBlock.length
  have hLen : lengths.length = events.length := by simp [lengths]
  have hj : j.val < lengths.length := by rw [hLen]; exact j.isLt
  have h := hintTakeSum_succ lengths j.val hj
  have hv : lengths[j.val] = (record events[j.val]).length := by simp [lengths]
  have hLe := hintTakeSum_mono lengths (Nat.succ_le_of_lt j.isLt)
  rw [h, hv] at hLe
  simp only [lengths, ← List.map_take] at hLe
  simp only [hintEventDescriptor, hintDetBlockOffset, ← List.map_take]
  omega

theorem hintTreeDet_record (E : RAMEnv) (up previous : ℕ → ℕ)
    (header control hintMap resultMap listBase N : ℕ)
    (events : List HintTreeEvent) (record : HintTreeEvent → HintDetBlock) (aux : List HintDetBlock)
    (hDet : E.det = hintAssembledDet up header
      (hintTreeDetBlocks previous header control hintMap resultMap listBase N events record aux))
    (hHeader : 3 < header) (j : Fin events.length) :
    (record events[j.val]).At E (hintEventDescriptor header events record j.val) := by
  let blocks := hintTreeDetBlocks previous header control hintMap resultMap listBase N events record aux
  have hIndex : j.val + 2 < blocks.length := by
    have hj := j.isLt
    simp only [blocks, hintTreeDetBlocks, List.length_cons, List.length_append, List.length_map]
    omega
  have hRecord : blocks[j.val + 2] = record events[j.val] := by
    have h : j.val < (events.map record).length := by simpa using j.isLt
    simp [blocks, hintTreeDetBlocks, List.getElem_append_left h]
  have hOffset : hintDetBlockOffset blocks (j.val + 2) =
      16 + 2 * events.length + hintDetBlockOffset (events.map record) j.val := by
    have hj : j.val ≤ (events.map record).length := by simpa using j.isLt.le
    simp [blocks, hintTreeDetBlocks, hintDetBlockOffset, hintRootDetBlock, hintDispatchDetBlock,
      hintTreeEntries_length, List.take_append_of_le_length hj, Nat.add_assoc]
  have hAt := hintAssembledDet_block E up header blocks hDet hHeader (j.val + 2) hIndex
  rw [hRecord, hOffset] at hAt
  simpa only [hintEventDescriptor, Nat.add_assoc] using hAt

theorem hintTreeDet_fixed (E : RAMEnv) (up previous : ℕ → ℕ)
    (header control hintMap resultMap listBase N : ℕ)
    (events : List HintTreeEvent) (record : HintTreeEvent → HintDetBlock) (aux : List HintDetBlock)
    (hDet : E.det = hintAssembledDet up header
      (hintTreeDetBlocks previous header control hintMap resultMap listBase N events record aux))
    (hHeader : 3 < header) :
    (hintRootDetBlock previous control hintMap resultMap listBase (header + 16) events.length N).At E header ∧
    (hintDispatchDetBlock (hintTreeEntries header events record)).At E (header + 16) := by
  let blocks := hintTreeDetBlocks previous header control hintMap resultMap listBase N events record aux
  constructor
  · exact hintAssembledDet_block E up header blocks hDet hHeader 0 (by simp [blocks, hintTreeDetBlocks])
  · exact hintAssembledDet_block E up header blocks hDet hHeader 1 (by simp [blocks, hintTreeDetBlocks])

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintTreeDet_record
end S_HintTreeDet20261120
section S_HintAuxDet20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintDetBlockRead_append_right (front tail : List HintDetBlock) (offset : ℕ) :
    hintDetBlockRead (front ++ tail) ((front.map HintDetBlock.length).sum + offset) =
      hintDetBlockRead tail offset := by
  induction front with
  | nil => simp
  | cons block front ih =>
      simp only [List.cons_append, List.map_cons, List.sum_cons, hintDetBlockRead]
      have hSkip : ¬ block.length + (front.map HintDetBlock.length).sum + offset < block.length := by omega
      rw [if_neg hSkip, show block.length + (front.map HintDetBlock.length).sum + offset - block.length =
        (front.map HintDetBlock.length).sum + offset by omega]
      exact ih

def hintAuxAddress (header : ℕ) (events : List HintTreeEvent)
    (record : HintTreeEvent → HintDetBlock) (aux : List HintDetBlock) (i : ℕ) : ℕ :=
  hintEventDescriptor header events record events.length + hintDetBlockOffset aux i

theorem hintTreeDet_aux (E : RAMEnv) (up previous : ℕ → ℕ)
    (header control hintMap resultMap listBase N : ℕ)
    (events : List HintTreeEvent) (record : HintTreeEvent → HintDetBlock) (aux : List HintDetBlock)
    (hDet : E.det = hintAssembledDet up header
      (hintTreeDetBlocks previous header control hintMap resultMap listBase N events record aux))
    (hHeader : 3 < header) (i : Fin aux.length) :
    aux[i.val].At E (hintAuxAddress header events record aux i.val) := by
  let front := [hintRootDetBlock previous control hintMap resultMap listBase (header + 16) events.length N,
    hintDispatchDetBlock (hintTreeEntries header events record)] ++ events.map record
  have hLen : hintEventDescriptor header events record events.length =
      header + (front.map HintDetBlock.length).sum := by
    simp [hintEventDescriptor, hintDetBlockOffset, front, hintRootDetBlock, hintDispatchDetBlock,
      hintTreeEntries_length, Nat.add_assoc]
    rw [List.take_of_length_le (by simp)]
  intro j hj
  rw [hDet, hintAuxAddress, hLen]
  change hintAssembledDet up header (front ++ aux)
      (header + (front.map HintDetBlock.length).sum + hintDetBlockOffset aux i.val + j) = _
  have h3 : header + (front.map HintDetBlock.length).sum + hintDetBlockOffset aux i.val + j ≠ 3 := by omega
  have hBefore : ¬ header + (front.map HintDetBlock.length).sum + hintDetBlockOffset aux i.val + j < header := by omega
  have hSub : header + (front.map HintDetBlock.length).sum + hintDetBlockOffset aux i.val + j - header =
      (front.map HintDetBlock.length).sum + (hintDetBlockOffset aux i.val + j) := by omega
  rw [hintAssembledDet, if_neg h3, if_neg hBefore, hSub, hintDetBlockRead_append_right]
  exact hintDetBlockRead_at aux i.val i.isLt j hj

theorem hintTreeDet_dispatch (E : RAMEnv) (up previous : ℕ → ℕ)
    (header control hintMap resultMap listBase N : ℕ)
    (events : List HintTreeEvent) (record : HintTreeEvent → HintDetBlock) (aux : List HintDetBlock)
    (hDet : E.det = hintAssembledDet up header
      (hintTreeDetBlocks previous header control hintMap resultMap listBase N events record aux))
    (hHeader : 3 < header) (hWord : 6 < 2 ^ E.W)
    (hSpace : hintEventDescriptor header events record events.length ≤ 2 ^ E.W)
    (hNonempty : ∀ j : Fin events.length, 0 < (record events[j.val]).length) :
    HintDispatchTable E (header + 16) (hintTreeEntries header events record) := by
  have hTables := hintTreeDet_fixed E up previous header control hintMap resultMap listBase N
    events record aux hDet hHeader
  apply HintDispatchTable.of_block E _ _ hTables.2
  · rw [hintTreeEntries_length]
    unfold hintEventDescriptor at hSpace
    omega
  · intro j
    have hj : j.val < events.length := by simpa only [hintTreeEntries_length] using j.isLt
    let k : Fin events.length := ⟨j.val, hj⟩
    have hAt : (hintTreeEntries header events record)[j.val] =
        (events[k.val].tag, hintEventDescriptor header events record k.val) := by
      simp [hintTreeEntries, k]
    rw [hAt]
    refine ⟨?_, ?_⟩
    · generalize events[k.val] = e
      cases e <;> simp only [HintTreeEvent.tag, Prod.fst] <;> omega
    · have hEnd := (hintEventDescriptor_end header events record k).trans hSpace
      have hLen := hNonempty k
      omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintTreeDet_aux
#print axioms LinearSetReconciliation327.Main.hintTreeDet_dispatch
end S_HintAuxDet20261120
section S_HintNodeAux20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintChildUpdateSchedule_length (CR : CRFamily) (Bc colBase : ℕ)
    (T : Node) (seed sav : ℕ) :
    (hintChildUpdateSchedule CR Bc colBase T seed sav).length = 1 + upRest Bc T := by
  have h := upSched_length CR Bc colBase T seed 0 0 sav []
  rw [upSched_decomp] at h
  simp only [List.nil_append, List.length_append, List.length_nil, Nat.add_zero] at h
  simp only [hintChildUpdateSchedule, List.length_cons, List.length_append]
  omega

def hintSubtreeColBase (Bc : ℕ) (T : Node) : ℕ := 8 + 16 * (1 + upRest Bc T)

noncomputable def hintSubtreeBlock (CR : CRFamily) (W control Bc : ℕ)
    (T : Node) (seed sav : ℕ) : HintDetBlock :=
  let firstColumn := hintSubtreeColBase Bc T
  let items := hintChildUpdateSchedule CR Bc firstColumn T seed sav
  ⟨firstColumn + upTabLen Bc T, hintSubtreeDet W control firstColumn items (upTabFun CR Bc T 0)⟩

theorem hintSubtreeBlock_specs (CR : CRFamily) (E : RAMEnv)
    (control Bc : ℕ) (T : Node) (seed sav detBase : ℕ)
    (hAt : (hintSubtreeBlock CR E.W control Bc T seed sav).At E detBase)
    (hEnd : hintSubtreeColBase Bc T + upTabLen Bc T < 2 ^ E.W)
    (hSpace : detBase + (hintSubtreeColBase Bc T + upTabLen Bc T) ≤ 2 ^ E.W)
    (hFields : ∀ it ∈ hintChildUpdateSchedule CR Bc (hintSubtreeColBase Bc T) T seed sav,
      ∀ f < 16, it.fld f < 2 ^ E.W)
    (hKinds : ∀ it ∈ hintChildUpdateSchedule CR Bc (hintSubtreeColBase Bc T) T seed sav, UpItemKind it)
    (hSaves : ∀ it ∈ hintChildUpdateSchedule CR Bc (hintSubtreeColBase Bc T) T seed sav,
      2 ≤ it.mode → it.sav + 1 < 2 ^ E.W) :
    let items := hintChildUpdateSchedule CR Bc (hintSubtreeColBase Bc T) T seed sav
    UpSavedLayout E detBase items ∧ E.det (detBase % 2 ^ E.W) % 2 ^ E.W = items.length ∧
      E.det (detBase + 3) = control := by
  apply hintSubtreeDet_specs E detBase control (hintSubtreeColBase Bc T) (upTabLen Bc T) _
    (upTabFun CR Bc T 0) _ hEnd hSpace hAt hFields hKinds hSaves
  rw [hintChildUpdateSchedule_length]
  exact le_rfl

def hintEmptyDetBlock : HintDetBlock := ⟨0, fun _ => 0⟩

noncomputable def hintNodeAuxBlocks (S : CRSourceBundle) (H : HintParams)
    (W control Bc : ℕ) (node : HintNodeInfo) (A : HintNodeArena) : List HintDetBlock :=
  let N := node.universeSize
  let t := node.residualCapacity
  let data := S.data N t
  let up := hintSubtreeBlock (crFamily S) W control Bc node.subtree node.seedIndex A.saveOffset
  let residual := if node.rowParams.isSome then
    hintSubtreeBlock (crFamily S) W control Bc (.cr N t) 0 (wordsOf W data.R)
    else hintEmptyDetBlock
  let cr := if node.isCR || node.rowParams.isSome then hintCRTableBlock data.W data.det else hintEmptyDetBlock
  let wait := match node.rowParams with
    | none => []
    | some (X, Y) => (List.range (H.rows X Y)).map fun j =>
        hintWaitDetBlock (H.Nmax N X Y) (rowLen N (H.rows X Y) j) (H.BY N X Y)
          (H.ell N X Y) (H.c N X Y)
  up :: residual :: cr :: wait

def hintJoinDetBlocks (blocks : List HintDetBlock) : HintDetBlock :=
  ⟨(blocks.map HintDetBlock.length).sum, hintDetBlockRead blocks⟩

theorem hintJoinDetBlocks_at (E : RAMEnv) (address : ℕ)
    (blocks : List HintDetBlock) (hAt : (hintJoinDetBlocks blocks).At E address)
    (i : Fin blocks.length) :
    blocks[i.val].At E (address + hintDetBlockOffset blocks i.val) := by
  intro j hj
  let lengths := blocks.map HintDetBlock.length
  have hIndex : i.val < lengths.length := by simp [lengths]
  have hTake := hintTakeSum_succ lengths i.val hIndex
  have hv : lengths[i.val] = blocks[i.val].length := by simp [lengths]
  have hEnd := hintTakeSum_mono lengths (Nat.succ_le_of_lt hIndex)
  rw [List.take_of_length_le le_rfl, hTake, hv] at hEnd
  simp only [lengths, ← List.map_take] at hEnd
  change hintDetBlockOffset blocks i.val + blocks[i.val].length ≤ (blocks.map HintDetBlock.length).sum at hEnd
  rw [Nat.add_assoc, hAt _ (by change _ < (blocks.map HintDetBlock.length).sum; omega)]
  exact hintDetBlockRead_at blocks i.val i.isLt j hj

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintSubtreeBlock_specs
#print axioms LinearSetReconciliation327.Main.hintJoinDetBlocks_at
end S_HintNodeAux20261120
section S_HintDecoderTableLayout20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintArenaFor (S : CRSourceBundle) (H : HintParams) (W : ℕ)
    (info : HintNodeInfo) (start : ℕ) : HintNodeArena :=
  let N := info.universeSize
  let t := info.residualCapacity
  let (rows, steps) := match info.rowParams with
    | none => (0, 0)
    | some (X, Y) => (H.rows X Y, H.ell N X Y)
  let (R, w, time) := if info.isCR || info.rowParams.isSome then
    ((S.data N t).R, (S.data N t).W, crSourceSteps S N t)
    else (0, 0, 0)
  hintNodeArena start W info.payloadBits info.schemes rows steps N R w time

noncomputable def hintRowScratchSize (H : HintParams) (info : HintNodeInfo) : ℕ :=
  match info.rowParams with
  | none => 0
  | some (X, Y) =>
      let N := info.universeSize
      let a := H.ell N X Y
      let K := H.Nmax N X Y
      (hintRowWorkspace 0 a K (H.BY N X Y) 0 0 a K).gauss.pivotRow + a

structure HintDecoderTables where
  placement : HintDecoderPlacement
  control : ℕ
  listBase : ℕ
  heap : ℕ
  stride : ℕ
  infos : List HintNodeInfo
  events : List HintTreeEvent
  aux : List HintDetBlock

noncomputable def hintDecoderTables (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (width Bc header : ℕ) : HintDecoderTables :=
  let CR := crFamily S
  let infos := hintNodeInfos CR hT 0 0
  let info := fun node => infos[node]?.getD ⟨0, 0, 0, 0, none, [], false, .store 0, 0⟩
  let control := wordsOf width (synLen CR T) + T.N
  let rowScratch := control + 3
  let listBase := rowScratch + (infos.map (hintRowScratchSize H)).foldl max 0
  let heap := listBase + T.N
  let stride := (infos.map fun i => (hintArenaFor S H width i 0).limit).foldl max 0
  let arena := fun node => hintArenaFor S H width (info node) (hintArenaStart heap stride node)
  let offsets := fun node => if node = 0 then 0 else (arena node).payload * width
  let events := hintTreeEvents CR offsets T 0 0 0
  let blocks := fun node => hintNodeAuxBlocks S H width control Bc (info node) (arena node)
  let aux := List.ofFn fun i : Fin infos.length => hintJoinDetBlocks (blocks i.val)
  let firstAux := header + 16 + 2 * events.length + (events.map HintTreeEvent.recordLength).sum
  let auxAddress := fun node i => firstAux + hintDetBlockOffset aux node + hintDetBlockOffset (blocks node) i
  let L : HintDecoderPlacement := ⟨width, control, rowScratch, info, arena,
    fun node row => auxAddress node (3 + row), fun node => auxAddress node 0,
    fun node => auxAddress node 1, fun node => auxAddress node 2⟩
  ⟨L, control, listBase, heap, stride, infos, events, aux⟩

noncomputable def HintDecoderTables.blocks (S : CRSourceBundle) (H : HintParams)
    (D : HintDecoderTables) (previous : ℕ → ℕ) (header N : ℕ) : List HintDetBlock :=
  let A := D.placement.arena 0
  hintTreeDetBlocks previous header D.control A.hints A.result D.listBase N D.events
    (hintEventRecord S H D.placement) D.aux

noncomputable def HintDecoderTables.det (S : CRSourceBundle) (H : HintParams)
    (D : HintDecoderTables) (up previous : ℕ → ℕ) (header N : ℕ) : ℕ → ℕ :=
  hintAssembledDet up header (D.blocks S H previous header N)

theorem hintEventRecords_end (S : CRSourceBundle) (H : HintParams) (L : HintDecoderPlacement)
    (header : ℕ) (events : List HintTreeEvent) :
    hintEventDescriptor header events (hintEventRecord S H L) events.length =
      header + 16 + 2 * events.length + (events.map HintTreeEvent.recordLength).sum := by
  unfold hintEventDescriptor hintDetBlockOffset
  rw [List.take_of_length_le (by simp)]
  simp only [List.map_map, Function.comp_def, hintEventRecord_length]

noncomputable def HintDecoderTables.nodeAux (S : CRSourceBundle) (H : HintParams)
    (D : HintDecoderTables) (Bc node : ℕ) : List HintDetBlock :=
  hintNodeAuxBlocks S H D.placement.width D.control Bc (D.placement.info node) (D.placement.arena node)

noncomputable def HintDecoderTables.auxAddress (S : CRSourceBundle) (H : HintParams)
    (D : HintDecoderTables) (Bc header node index : ℕ) : ℕ :=
  hintAuxAddress header D.events (hintEventRecord S H D.placement) D.aux node +
    hintDetBlockOffset (D.nodeAux S H Bc node) index

theorem hintDecoderTables_aux_At (S : CRSourceBundle) (H : HintParams)
    {T : Node} (hT : IsSchemeTree H T) (E : RAMEnv) (up previous : ℕ → ℕ)
    (width Bc header : ℕ) (hHeader : 3 < header)
    (hDet : E.det = (hintDecoderTables S H hT width Bc header).det S H up previous header T.N) :
    let D := hintDecoderTables S H hT width Bc header
    ∀ node : Fin D.infos.length, ∀ index : Fin (D.nodeAux S H Bc node.val).length,
      (D.nodeAux S H Bc node.val)[index.val].At E (D.auxAddress S H Bc header node.val index.val) := by
  dsimp only
  let D := hintDecoderTables S H hT width Bc header
  intro node index
  change (D.nodeAux S H Bc node.val)[index.val].At E (D.auxAddress S H Bc header node.val index.val)
  have hAux : D.aux = List.ofFn (fun i : Fin D.infos.length => hintJoinDetBlocks (D.nodeAux S H Bc i.val)) := rfl
  have hLength : D.aux.length = D.infos.length := by rw [hAux, List.length_ofFn]
  let n : Fin D.aux.length := ⟨node.val, hLength.symm ▸ node.isLt⟩
  have hRecord := hintTreeDet_aux E up previous header D.control (D.placement.arena 0).hints
    (D.placement.arena 0).result D.listBase T.N D.events (hintEventRecord S H D.placement) D.aux hDet hHeader n
  have hAt : D.aux[n.val] = hintJoinDetBlocks (D.nodeAux S H Bc node.val) := by
    have h := List.getElem_ofFn (f := fun i : Fin D.infos.length => hintJoinDetBlocks (D.nodeAux S H Bc i.val))
      (i := node.val) (by simp only [List.length_ofFn]; exact node.isLt)
    simp only [hAux]
    exact h
  rw [hAt] at hRecord
  exact hintJoinDetBlocks_at E _ _ hRecord index

theorem hintDecoderTables_event_At (S : CRSourceBundle) (H : HintParams)
    (D : HintDecoderTables) (E : RAMEnv) (up previous : ℕ → ℕ) (header N : ℕ)
    (hHeader : 3 < header) (hDet : E.det = D.det S H up previous header N)
    (i : Fin D.events.length) :
    (hintEventRecord S H D.placement D.events[i.val]).At E
      (hintEventDescriptor header D.events (hintEventRecord S H D.placement) i.val) :=
  hintTreeDet_record E up previous header D.control (D.placement.arena 0).hints (D.placement.arena 0).result
    D.listBase N D.events (hintEventRecord S H D.placement) D.aux hDet hHeader i

theorem hintDecoderTables_aux_addresses (S : CRSourceBundle) (H : HintParams)
    {T : Node} (hT : IsSchemeTree H T) (width Bc header node row : ℕ) :
    let D := hintDecoderTables S H hT width Bc header
    D.placement.updateTable node = D.auxAddress S H Bc header node 0 ∧
    D.placement.residualTable node = D.auxAddress S H Bc header node 1 ∧
    D.placement.crTable node = D.auxAddress S H Bc header node 2 ∧
    D.placement.threshold node row = D.auxAddress S H Bc header node (3 + row) := by
  dsimp only [HintDecoderTables.auxAddress, hintAuxAddress]
  rw [hintEventRecords_end]
  exact ⟨rfl, rfl, rfl, rfl⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_aux_At
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_event_At
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_aux_addresses
end S_HintDecoderTableLayout20261120
section S_HintPlacedRoot20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintDecoderTables_header (S : CRSourceBundle) (H : HintParams)
    (D : HintDecoderTables) (E : RAMEnv) (up previous : ℕ → ℕ) (header N : ℕ)
    (hHeader : 3 < header) (hDet : E.det = D.det S H up previous header N)
    (hWord : 15 < 2 ^ E.W)
    (hDetSpace : header + 16 + 2 * D.events.length + (D.events.map HintTreeEvent.recordLength).sum < 2 ^ E.W)
    (hControl : D.control + 2 < 2 ^ E.W)
    (hHint : (D.placement.arena 0).hints + N < 2 ^ E.W)
    (hResult : (D.placement.arena 0).result < 2 ^ E.W)
    (hList : D.listBase < 2 ^ E.W) :
    let A := D.placement.arena 0
    let record := hintEventRecord S H D.placement
    HintRootHeader E header D.control A.hints A.result D.listBase (header + 16) D.events.length N ∧
      HintDispatchTable E (header + 16) (hintTreeEntries header D.events record) := by
  let A := D.placement.arena 0
  let record := hintEventRecord S H D.placement
  have hFixed := hintTreeDet_fixed E up previous header D.control A.hints A.result D.listBase N
    D.events record D.aux hDet hHeader
  have hAnchor : E.det 3 = header := by
    rw [hDet]
    exact hintAssembledDet_anchor up header (D.blocks S H previous header N)
  refine ⟨HintRootHeader.of_block E previous header D.control A.hints A.result D.listBase (header + 16)
    D.events.length N hAnchor hFixed.1 hWord (by omega) hControl hHint (by omega) (by omega)
    hResult hList, ?_⟩
  apply hintTreeDet_dispatch E up previous header D.control A.hints A.result D.listBase N D.events
    record D.aux hDet hHeader (by omega)
  · rw [hintEventRecords_end]
    exact hDetSpace.le
  · intro j
    exact hintEventRecord_nonempty S H D.placement _

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_header
end S_HintPlacedRoot20261120
section S_HintScheduledActions20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem HintDispatchData.of_frame {control table count index : ℕ} {state out : RAMState}
    (before : HintDispatchData control table count index state)
    (context : out.regs 14 = control)
    (frame : ∀ a, control ≤ a → a ≤ control + 2 → out.mem a = state.mem a) :
    HintDispatchData control table count index out :=
  ⟨context, (frame control le_rfl (by omega)).trans before.table_pointer,
    (frame (control + 1) (by omega) (by omega)).trans before.size,
    (frame (control + 2) (by omega) le_rfl).trans before.cursor⟩

theorem hintLocatedActions_of_events (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (up previous : ℕ → ℕ) (header N : ℕ)
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop) (hHeader : 3 < header)
    (hDet : E.det = D.det S H up previous header N)
    (hExec : ∀ (j : Fin D.events.length) (act : Stmt) (base : ℕ) (state : RAMState),
      let event := D.events[j.val]
      let desc := hintEventDescriptor header D.events (hintEventRecord S H D.placement) j.val
      (hintNativeActions S)[event.tag]? = some act →
      base = hintActionEntry (hintNativeActions S) 75 event.tag →
      At (hintNativeProgram S) base (act.compile base) →
      state.pc = base → state.regs 6 = desc → state.regs 14 = D.control →
      UpWordState E state → I j.val state.mem → (hintEventRecord S H D.placement event).At E desc →
      Sem (hintNativeProgram S) E base (base + act.len) state (fun k out =>
        k ≤ budget j.val ∧ I (j.val + 1) out.mem ∧ out.regs 14 = D.control ∧
        ∀ a, D.control ≤ a → a ≤ D.control + 2 → out.mem a = state.mem a)) :
    HintLocatedActions (hintNativeProgram S) E D.control (header + 16) 75 (hintNativeActions S)
      (hintTreeEntries header D.events (hintEventRecord S H D.placement)) budget I := by
  let record := hintEventRecord S H D.placement
  let entries := hintTreeEntries header D.events record
  intro i act base state hSelect hEntry hAt hPc hArg _ hData hWord hInv
  have hI : i.val < D.events.length := by
    simpa only [entries, hintTreeEntries_length] using i.isLt
  let j : Fin D.events.length := ⟨i.val, hI⟩
  have hEntryAt : entries[i.val] = (D.events[j.val].tag, hintEventDescriptor header D.events record j.val) := by
    simp [entries, hintTreeEntries, j]
  change (hintNativeActions S)[entries[i.val].1]? = some act at hSelect
  change base = hintActionEntry (hintNativeActions S) 75 entries[i.val].1 at hEntry
  change state.regs 6 = entries[i.val].2 at hArg
  rw [hEntryAt] at hSelect hEntry hArg
  have hRecord := hintDecoderTables_event_At S H D E up previous header N hHeader hDet j
  apply Sem.mono (hExec j act base state hSelect hEntry hAt hPc hArg hData.context hWord hInv hRecord)
  rintro k out ⟨hk, hI, hContext, hFrame⟩
  exact ⟨hk, hI, hData.of_frame hContext hFrame⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintLocatedActions_of_events
end S_HintScheduledActions20261120


