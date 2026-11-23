-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Bundle51_17
-- name    : LinearSetReconciliation327_Main_Bundle51_17
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T10:17:46.670277+00:00
-- url     : https://prove2.me/theorems/de57d1aa-9c4a-4c6b-8f88-fa9e3dbe158a
-- title:
--   LinearSetReconciliation327 鈥?Bundle51_17
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_Bundle51_17` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintUpdatePrepared20261120
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_10
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_16
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_17a

/-! Bundled module: LinearSetReconciliation327_Main_Bundle51_17
    Members (declaration text copied byte-identically, dependency order):
      * Definitions.Def_LinearSetReconciliation327_Main_HintCommonBudget20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintNativeConjuncts20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintActualDecoder20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintNativeSharedTable20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintSavedTogglesGrown20261120
    Only `import` lines were merged; every member body is wrapped in its own
    `section ... end` so that per-file `set_option`s stay scoped. -/

section -- Def_LinearSetReconciliation327_Main_HintCommonBudget20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintHalted_iterate (P : Program) (E : RAMEnv) (s : RAMState)
    (h : Halted P s) (k : ℕ) : (step P E)^[k] s = s := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, crStep_halted P E s h]

theorem hintHaltsWithin_unique {P : Program} {E : RAMEnv} {s a b : RAMState} {T U : ℝ}
    (hA : HaltsWithin P E T s a) (hB : HaltsWithin P E U s b) : a = b := by
  obtain ⟨k, _, hk, ha⟩ := hA
  obtain ⟨l, _, hl, hb⟩ := hB
  rcases le_total k l with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_comm k d, Function.iterate_add_apply, hk, hintHalted_iterate P E a ha] at hl
    exact hl
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_comm l d, Function.iterate_add_apply, hl, hintHalted_iterate P E b hb] at hk
    exact hk.symm

theorem hintPlacedTree_start_correct_sameBudget (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (seedData : (hintSpec T).Seed) (up previous : ℕ → ℕ)
    (W Bc header X Y : ℕ) (x : Finset ℕ) (J : List ℕ) (hLimits : HintDecoderLimits S H hT W Bc header)
    (hN : 0 < T.N) (hWF : Node.WF T X Y) (hValid : Node.Valid T.N X Y x J.toFinset)
    (hBounds : Node.AllBounds T (hintKappaAux H T seedData T hT 0) x J.toFinset)
    (hDistinct : J.Nodup) (hHints : ∀ j ∈ J, j < T.N) :
    let D := hintDecoderTables S H hT W Bc header
    let E := (hintSpec T).env W (D.det S H up previous header T.N) seedData
    let r := hintKappaAux H T seedData T hT 0
    let y := hintSketchVector (crFamily S) T r x
    let phase := hintPlacedTreeRoot_total S H hT seedData up previous W Bc header X Y hLimits hN hWF
    ∃ out, HaltsWithin (hintNativeProgram S) E (hintPhaseRunBudget S D.events.length T.N phase.budget)
      (decoderStart W y J) out ∧ OutputsSupport out (crInput T.N x) := by
  let r := hintKappaAux H T seedData T hT 0
  let y := hintSketchVector (crFamily S) T r x
  obtain ⟨a, ha⟩ := hintPlacedTree_start_total S H hT seedData up previous W Bc header X Y y J hLimits
    hN hWF hDistinct hHints
  obtain ⟨b, hb, hs⟩ := hintPlacedTree_start_correct S H hT seedData up previous W Bc header X Y x J hLimits
    hN hWF hValid hBounds hDistinct hHints
  exact ⟨a, ha, (hintHaltsWithin_unique ha hb).symm ▸ hs⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedTree_start_correct_sameBudget
end -- Def_LinearSetReconciliation327_Main_HintCommonBudget20261120

section -- Def_LinearSetReconciliation327_Main_HintNativeConjuncts20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

private theorem hintPrU_imp {α : Type} [Fintype α] {P Q : α → Prop}
    (h : ∀ x, P x → Q x) : prU P ≤ prU Q := by
  classical
  unfold prU
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hSub : (Finset.univ.filter P) ⊆ (Finset.univ.filter Q) := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, h a (Finset.mem_filter.mp ha).2⟩
  exact_mod_cast Finset.card_le_card hSub

theorem hintValid_of_list (N X Y : ℕ) (x : Fin N → ZMod 2) (J : List ℕ)
    (hInside : ∀ j ∈ J, j < N) (hLength : J.length ≤ X)
    (hDiff : (Finset.univ.filter fun i : Fin N => x i = 1 ∧ i.val ∉ J).card ≤ Y) :
    Node.Valid N X Y (support x) J.toFinset := by
  classical
  refine ⟨fun i hi => Finset.mem_range.mpr (crSupport_lt x hi), ?_,
    (List.toFinset_card_le J).trans hLength, ?_⟩
  · intro i hi
    exact Finset.mem_range.mpr (hInside i (List.mem_toFinset.mp hi))
  · have hEq : support x \ J.toFinset =
        (Finset.univ.filter fun i : Fin N => x i = 1 ∧ i.val ∉ J).image Fin.val := by
      ext a
      simp only [support, Finset.mem_sdiff, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and, List.mem_toFinset]
      constructor
      · rintro ⟨⟨i, hi, rfl⟩, hJ⟩
        exact ⟨i, ⟨hi, hJ⟩, rfl⟩
      · rintro ⟨i, ⟨hi, hJ⟩, rfl⟩
        exact ⟨⟨i, hi, rfl⟩, hJ⟩
    rw [hEq]
    exact Finset.card_image_le.trans hDiff

theorem hintPlacedDecoder_conjuncts (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (up previous : ℕ → ℕ)
    (W Bc header X Y : ℕ) (time error : ℝ) (hLimits : HintDecoderLimits S H hT W Bc header)
    (hN : 0 < T.N) (hWF : Node.WF T X Y) :
    let D := hintDecoderTables S H hT W Bc header
    let det := D.det S H up previous header T.N
    (∀ r : (hintSpec T).Seed, (hintPhaseRunBudget S D.events.length T.N
      (hintPlacedTreeRoot_total S H hT r up previous W Bc header X Y hLimits hN hWF).budget : ℝ) ≤ time) →
    (∀ x J : Finset ℕ, Node.Valid T.N X Y x J →
      prU (fun r : (hintSpec T).Seed => ¬ T.AllBounds (hintKappa H T hT r) x J) ≤ error) →
    (∀ (r : (hintSpec T).Seed) (y : Fin (synLen (crFamily S) T) → ZMod 2) (J : List ℕ),
      J.Nodup → (∀ v ∈ J, v < T.N) → ∃ out, HaltsWithin (hintNativeProgram S)
        ((hintSpec T).env W det r) time (decoderStart W y J) out) ∧
    (∀ (x : Fin T.N → ZMod 2) (J : List ℕ), J.Nodup → (∀ v ∈ J, v < T.N) → J.length ≤ X →
      (Finset.univ.filter fun i : Fin T.N => x i = 1 ∧ i.val ∉ J).card ≤ Y →
      prU (fun r : (hintSpec T).Seed => ¬ ∃ out, HaltsWithin (hintNativeProgram S)
        ((hintSpec T).env W det r) time (decoderStart W (hintH_trees (crFamily S) H T hT r x) J) out ∧
        OutputsSupport out x) ≤ error) := by
  dsimp only
  intro hTime hProb
  constructor
  · intro r y J hDistinct hInside
    obtain ⟨out, k, hk, hExec, hHalt⟩ := hintPlacedTree_start_total S H hT r up previous
      W Bc header X Y y J hLimits hN hWF hDistinct hInside
    exact ⟨out, k, hk.trans (hTime r), hExec, hHalt⟩
  · intro x J hDistinct hInside hLength hDiff
    have hValid := hintValid_of_list T.N X Y x J hInside hLength hDiff
    refine (hintPrU_imp ?_).trans (hProb (support x) J.toFinset hValid)
    intro r hFail hBounds
    obtain ⟨out, ⟨k, hk, hExec, hHalt⟩, hOut⟩ := hintPlacedTree_start_correct_sameBudget S H hT r
      up previous W Bc header X Y (support x) J hLimits hN hWF hValid hBounds hDistinct hInside
    apply hFail
    refine ⟨out, ⟨k, hk.trans (hTime r), hExec, hHalt⟩, ?_⟩
    simpa only [crInput_support_vec] using hOut

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedDecoder_conjuncts
end -- Def_LinearSetReconciliation327_Main_HintNativeConjuncts20261120

section -- Def_LinearSetReconciliation327_Main_HintActualDecoder20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintActualDecoder_of_bounds (S : CRSourceBundle) (H : HintParams) (K : ℝ)
    (B N X Y fuel base : ℕ) (T : Node)
    (hArgs : H.NodeArgs N X Y) (hTree : H.tree fuel N X Y = some T)
    (hK : 0 ≤ K) (hKB : K ≤ (2 : ℝ) ^ B) (hC : B + 3 * H.A ≤ H.C) (h27 : 27 ≤ H.C)
    (hCount : (T.nodeCount : ℝ) ≤ K * (H.A : ℝ) * H.lgn ^ 27)
    (hBase : 1 ≤ base) (hBaseLog : Nat.clog 2 (H.n + 2) ≤ base)
    (hProb : T.BoundsProb ((2 : ℝ) ^ H.lamStar)⁻¹ X Y)
    (previous : ℕ → ℕ) :
    let Bc := colBc S.K H.n
    let growth := hintWidthScale (hintResourceCoefficient S H.A H.C K) (hintResourceDegree S)
    let W := upWideWord (growth * base)
    let header := decAfterBase (upRootBase Bc T) (upTabLen Bc T)
    let up := upRootDet (crFamily S) (growth * base) Bc T
    let Cd := hintDecoderTimeConstant S H.A H.C K
    let time := Cd * (T.N : ℝ) * Real.exp (Cd * (lg H.lgn) ^ 2)
    ∃ hT : IsSchemeTree H T, T.N = N ∧
      let spec := hintSpec T
      let D := hintDecoderTables S H hT W Bc header
      let det := D.det S H up previous header T.N
      let M := synLen (crFamily S) T
      spec.Fits W ∧
      (∀ (r : spec.Seed) (y : Fin M → ZMod 2) (J : List ℕ),
        J.Nodup → (∀ v ∈ J, v < T.N) → ∃ out, HaltsWithin (hintNativeProgram S)
          (spec.env W det r) time (decoderStart W y J) out) ∧
      (∀ (x : Fin T.N → ZMod 2) (J : List ℕ), J.Nodup → (∀ v ∈ J, v < T.N) → J.length ≤ X →
        (Finset.univ.filter fun i : Fin T.N => x i = 1 ∧ i.val ∉ J).card ≤ Y →
        prU (fun r : spec.Seed => ¬ ∃ out, HaltsWithin (hintNativeProgram S)
          (spec.env W det r) time (decoderStart W (hintH_trees (crFamily S) H T hT r x) J) out ∧
          OutputsSupport out x) ≤ ((2 : ℝ) ^ H.lam)⁻¹) := by
  let Bc := colBc S.K H.n
  let growth := hintWidthScale (hintResourceCoefficient S H.A H.C K) (hintResourceDegree S)
  let W := upWideWord (growth * base)
  let header := decAfterBase (upRootBase Bc T) (upTabLen Bc T)
  let up := upRootDet (crFamily S) (growth * base) Bc T
  let Cd := hintDecoderTimeConstant S H.A H.C K
  let time := Cd * (T.N : ℝ) * Real.exp (Cd * (lg H.lgn) ^ 2)
  obtain ⟨hT, hRoot, hWF, hInputs, hLimit⟩ :=
    hintActualDecoderLimits_withInputs S H K fuel N X Y base T hArgs hTree hCount hBase hBaseLog
  have hN : 0 < T.N := hRoot.symm ▸ hArgs.2.2.1
  refine ⟨hT, hRoot, hLimit.fits, ?_⟩
  apply hintPlacedDecoder_conjuncts S H hT up previous W Bc header X Y time ((2 : ℝ) ^ H.lam)⁻¹ hLimit hN hWF
  · intro r
    exact hintPaperRunBudget S H K hT up previous N X Y fuel W header hArgs hTree hK hCount
      hRoot hWF hN (hInputs 0 0) hLimit r
  · intro x J hValid
    exact HintBoundsBudget.hintPublicAllBounds H T hT X Y K B hArgs.1 hK hKB hC h27 hCount
      hWF hProb x J hValid

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintActualDecoder_of_bounds
end -- Def_LinearSetReconciliation327_Main_HintActualDecoder20261120

section -- Def_LinearSetReconciliation327_Main_HintNativeSharedTable20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
noncomputable section

private theorem hintJoin_packMem_zero_ge_words (W M : ℕ) (hW : 0 < W) (y : Fin M → ZMod 2) (a : ℕ)
    (ha : wordsOf W M ≤ a) : packMem W y a = 0 := by
  unfold packMem
  apply Finset.sum_eq_zero
  intro p _
  apply if_neg
  rintro ⟨he, _⟩
  have hp : p.val / W < wordsOf W M :=
    (Nat.div_lt_iff_lt_mul hW).mpr (p.isLt.trans_le (up_words_cover W M hW))
  omega

private theorem hintJoin_upVirtualMem_zero_pack (W M : ℕ) (hW : 0 < W) (hWords : wordsOf W M ≤ 2 ^ W)
    (y : Fin M → ZMod 2) : upVirtualMem W 0 (packMem W y) = packMem W y := by
  funext a
  by_cases ha : a < 2 ^ W
  · simp only [upVirtualMem, if_pos ha, upCyclicAddr, Nat.zero_add,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (packMem_lt W hW y a)]
  · rw [upVirtualMem, if_neg ha, hintJoin_packMem_zero_ge_words W M hW y a (by omega)]

private theorem hintJoin_upSavedAt_program : At progUpSaved 0 (upSavedSup.compile 0) := by
  intro a ha
  simp only [progUpSaved, Nat.zero_add]
  exact List.getElem?_append_left ha

private theorem hintJoin_upSavedSup_halted (out : RAMState) (hpc : out.pc = 156) : Halted progUpSaved out := by
  have hLen : (upSavedSup.compile 0).length = 156 := by rw [Stmt.length_compile, upSavedSup_len]
  unfold Halted
  simp only [progUpSaved, hpc]
  rw [← hLen]
  simp

private theorem hintJoin_upSaved_toggles_of_fold (E : RAMEnv) (items : List UpIt) {N M : ℕ}
    (H : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2)) (B : ℝ)
    (h16 : 16 < 2 ^ E.W) (hWpos : 0 < E.W) (hWords : wordsOf E.W M ≤ 2 ^ E.W)
    (hLayout : UpSavedLayout E 0 items) (hCount : E.det 0 % 2 ^ E.W = items.length)
    (hBudget : ((147 * items.length + 10 : ℕ) : ℝ) ≤ B)
    (hEffect : ∀ (y : Fin M → ZMod 2) (i : Fin N) (a : ℕ), a < wordsOf E.W M →
      (upFold E i.val (⟨packMem E.W y, 0, 1⟩ : UpAbs) items).mem a =
        packMem E.W (y + H (Pi.single i 1)) a) :
    TogglesWithin progUpSaved E H B := by
  intro y i
  let s := initState (packMem E.W y) i.val 0 0
  let ab : UpAbs := ⟨packMem E.W y, 0, 1⟩
  have hMem : upVirtualMem E.W 0 s.mem = ab.mem := hintJoin_upVirtualMem_zero_pack E.W M hWpos hWords y
  have hRaw : UpBasedRawPayload 0 (wordsOf E.W M) ab s := by
    intro q hq
    simp only [s, ab, initState, Nat.zero_add]
  have hExec := upSavedSup_payload_sem progUpSaved E 0 0 0 i.val (wordsOf E.W M) items s ab
    hintJoin_upSavedAt_program rfl hLayout hMem rfl rfl hRaw (Nat.two_pow_pos E.W)
    (by simpa only [Nat.zero_add] using hWords) h16
    (by simp [s, initState]) (by simp [s, initState]) (by simp [s, initState])
    (by simpa only [Nat.zero_mod] using hCount)
  obtain ⟨_, k, out, hRun, hPc, hCost, hView, hRawOut, hR0, hR14, hR15⟩ := hExec
  refine ⟨out, ⟨k, ?_, hRun, hintJoin_upSavedSup_halted out (by simpa only [Nat.zero_add] using hPc)⟩, ?_⟩
  · have hk : (k : ℝ) ≤ ((147 * items.length + 10 : ℕ) : ℝ) := by exact_mod_cast hCost
    exact hk.trans hBudget
  · intro a ha
    rw [upFold_shift_zero] at hRawOut
    simpa only [Nat.zero_add] using (hRawOut a ha).trans (hEffect y i a ha)

private theorem hintJoin_upSaved_cost_of_old (L nc d bell bc : ℕ) (B : ℝ)
    (hL : L ≤ nc * (d + 2 * bell + bc))
    (hOld : ((125 * (nc * (d + bell + bc)) + 12 : ℕ) : ℝ) ≤ B) :
    ((147 * L + 10 : ℕ) : ℝ) ≤ 3 * B := by
  have hNat : 147 * (nc * (d + 2 * bell + bc)) + 10 ≤
      3 * (125 * (nc * (d + bell + bc)) + 12) := by
    ring_nf
    omega
  have hLe : 147 * L + 10 ≤ 3 * (125 * (nc * (d + bell + bc)) + 12) :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left 147 hL) 10).trans hNat
  have hReal : ((147 * L + 10 : ℕ) : ℝ) ≤ 3 * ((125 * (nc * (d + bell + bc)) + 12 : ℕ) : ℝ) := by
    exact_mod_cast hLe
  exact hReal.trans (mul_le_mul_of_nonneg_left hOld (by norm_num))

private theorem hintJoin_upSavedFold_packMem_of_local (CR : CRFamily) (P : HintParams) (T : Node)
    (hT : IsSchemeTree P T) (r : (hintSpec T).Seed) (E : RAMEnv) (Bc colBase sav : ℕ)
    (hW : 1 < 2 ^ E.W) (hWpos : 0 < E.W) (hN : 0 < T.N) (hNM : T.N ≤ 2 ^ E.W)
    (hLocal : ∀ i : Fin T.N, UpLocalTree CR E i.val Bc colBase T (hintKappa P T hT r) 0 0 0)
    (hRoom : UpSaveRoom (wordsOf E.W (synLen CR T)) sav T) :
    ∀ (y : Fin (synLen CR T) → ZMod 2) (i : Fin T.N) (a : ℕ),
      a < wordsOf E.W (synLen CR T) →
      (upFold E i.val (⟨packMem E.W y, 0, 1⟩ : UpAbs)
        (upSched CR Bc colBase T 0 0 0 sav [])).mem a =
      packMem E.W (y + hintH_trees CR P T hT r (Pi.single i 1)) a := by
  intro y i a ha
  rw [packMem_add_H_single CR P T hT r E.W hWpos y i a]
  exact upFold_root_of_local CR E Bc colBase (wordsOf E.W (synLen CR T)) sav T
    (hintKappa P T hT r) i.val hW hN hNM (hLocal i)
    (up_words_cover E.W (synLen CR T) hWpos) hRoom i.isLt (packMem E.W y)
    (fun a => packMem_lt E.W hWpos y a) a ha

theorem upSavedRoot_toggles_assembled (CR : CRFamily) (P : HintParams) (W Bc U Bell : ℕ)
    (T : Node) (hT : IsSchemeTree P T) (B : ℝ) (header : ℕ) (blocks : List HintDetBlock)
    (hPlacement : upRootBase Bc T + upTabLen Bc T ≤ header)
    (hW : 8 ≤ W) (hFits : (hintSpec T).Fits W)
    (hWords : wordsOf W (synLen CR T) ≤ 2 ^ W)
    (hStatic : UpTreeStatic CR Bc U T) (hU : U ≤ 2 ^ W) (hN : 0 < T.N)
    (hBc : Bc ≤ 4 * (2 ^ W) ^ 3) (hBell : 1 ≤ Bell) (hEll : UpEllOK Bell T)
    (hOld : ((125 * (T.nodeCount * (T.depth + Bell + Bc)) + 12 : ℕ) : ℝ) ≤ B)
    (r : (hintSpec T).Seed) :
    TogglesWithin progUpSaved
      ((hintSpec T).env (upWideWord W)
        (hintAssembledDet (upRootDet CR W Bc T) header blocks) r)
      (hintH_trees CR P T hT r) (3 * B) := by
  have hLayout := upRoot_layout_fits CR P W Bc U T hT hW hFits hWords hStatic hU hN hBc
  let V := upWideWord W
  let items := upRootItems CR W Bc T
  let colBase := upRootBase Bc T
  let merged := hintAssembledDet (upRootDet CR W Bc T) header blocks
  let E := (hintSpec T).env V merged r
  have hVpos : 0 < V := by unfold V upWideWord; omega
  have hCol : colBase = 8 + 16 * items.length := by
    change 8 + 16 * upRootCount Bc T = 8 + 16 * items.length
    rw [hLayout.length_eq]
  let F := (hintSpec T).env V (upRootDet CR W Bc T) r
  have hAgree (a : ℕ) (ha : a < header) (h3 : a ≠ 3) : E.det a = F.det a :=
    hintAssembledDet_up (upRootDet CR W Bc T) header blocks a ha h3
  have hHeaderLo : 4 < header := hLayout.colBase.trans_le ((Nat.le_add_right _ _).trans hPlacement)
  have hLocal : ∀ i : Fin T.N, UpLocalTree CR E i.val Bc colBase T
      (hintKappa P T hT r) 0 0 0 := by
    intro i
    apply UpLocalTree.of_table_extension CR E F i.val Bc colBase hLayout.word rfl rfl rfl
      (hAgree 0 (by omega) (by decide)) (hAgree 1 (by omega) (by decide))
      T (hintKappa P T hT r) 0 0 0
    · change colBase + 0 + upTabLen Bc T < 2 ^ V
      rw [Nat.add_zero]
      exact hLayout.table_end
    · intro a ha hb
      have hLow : 4 < colBase := hLayout.colBase
      have hHigh : colBase + upTabLen Bc T ≤ header := hPlacement
      exact hAgree a (by omega) (by omega)
    · exact upRoot_localTree CR P W Bc U T hT r i.val hW hFits hU hStatic hLayout
  have hEffect := hintJoin_upSavedFold_packMem_of_local CR P T hT r E Bc colBase (upRootSlot CR W T)
    hLayout.word hVpos hN hLayout.universe_fits hLocal hLayout.room
  have hL : items.length ≤ T.nodeCount * (T.depth + 2 * Bell + Bc) :=
    upSched_count_le CR Bc Bell colBase hBell T hEll 0 0 0 (upRootSlot CR W T)
  have hBudget := hintJoin_upSaved_cost_of_old items.length T.nodeCount T.depth Bell Bc B hL hOld
  have hFields : ∀ j (hj : j < items.length), ∀ t, t < 16 →
      E.det (8 + 16 * j + t) % 2 ^ E.W = (items[j]).fld t := by
    intro j hj t ht
    have hField : 8 + 16 * j + t < header := by
      have hh : colBase ≤ header := (Nat.le_add_right _ _).trans hPlacement
      omega
    change E.det (8 + 16 * j + t) % 2 ^ V = _
    rw [hAgree _ hField (by omega)]
    exact hLayout.fields j hj t ht
  have hCount : E.det 0 % 2 ^ E.W = items.length := by
    change E.det 0 % 2 ^ V = _
    rw [hAgree 0 (by omega) (by decide)]
    exact hLayout.count_read
  have hHeaderWidth : upvWw E = E.W := by
    change merged (1 % 2 ^ V) % 2 ^ V = V
    rw [Nat.mod_eq_of_lt hLayout.word]
    change E.det 1 % 2 ^ V = _
    rw [hAgree 1 (by omega) (by decide)]
    change upRootDet CR W Bc T 1 % 2 ^ V = V
    simp only [upRootDet, upDet_one]
    change V % 2 ^ V = V
    exact Nat.mod_eq_of_lt (Nat.lt_two_pow_self (n := V))
  have hSavedLayout : UpSavedLayout E 0 items := by
    refine ⟨hLayout.address, ?_, ?_, ?_, ?_⟩
    · intro j hj t ht
      change E.det ((0 + (8 + 16 * j + t)) % 2 ^ E.W) % 2 ^ E.W = (items[j]).fld t
      rw [Nat.zero_add, Nat.mod_eq_of_lt (by have hh : 8 + 16 * items.length < 2 ^ E.W := hLayout.address; omega : 8 + 16 * j + t < 2 ^ E.W)]
      exact hFields j hj t ht
    · rw [upvWw_shift_zero]
      exact hHeaderWidth
    · exact upSched_kind CR Bc colBase T 0 0 0 (upRootSlot CR W T) [] (by simp)
    · intro it hi _
      exact hLayout.saves it hi
  have h16 : 16 < 2 ^ E.W := by
    have hFive : 5 ≤ V := by unfold V upWideWord; omega
    have hPow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hFive
    norm_num only [Nat.reducePow] at hPow
    exact lt_of_lt_of_le (by decide : 16 < 2 ^ 5) hPow
  have hWordsV : wordsOf V (synLen CR T) ≤ 2 ^ V :=
    (wordsOf_antitone_word (by omega : 0 < W) (upWideWord_ge W)).trans
      (hWords.trans (Nat.pow_le_pow_right (by decide) (upWideWord_ge W)))
  apply hintJoin_upSaved_toggles_of_fold E items (hintH_trees CR P T hT r) (3 * B)
    h16 hVpos hWordsV hSavedLayout hCount hBudget
  exact hEffect

theorem hintSavedToggles_nativeTables (S : CRSourceBundle) {n lam N X Y : ℕ}
    (hArgs : (hintP S.K n lam).NodeArgs N X Y)
    (fuel : ℕ) (T : Node) (hTree : (hintP S.K n lam).tree fuel N X Y = some T)
    (hT : IsSchemeTree (hintP S.K n lam) T) (previous : ℕ → ℕ) (r : (hintSpec T).Seed) :
    let P := hintP S.K n lam
    let W := hintW (hintColK S.K) n
    let V := upWideWord W
    let Bc := colBc S.K n
    let header := decAfterBase (upRootBase Bc T) (upTabLen Bc T)
    let tables := hintDecoderTables S P hT V Bc header
    let det := tables.det S P (upRootDet (crFamily S) W Bc T) previous header T.N
    TogglesWithin progUpSaved ((hintSpec T).env V det r) (hintH_trees (crFamily S) P T hT r)
      ((3 * hintCu (hintColK S.K)) * lg (n : ℝ) ^ hintpu) := by
  let P := hintP S.K n lam
  let W := hintW (hintColK S.K) n
  let Bc := colBc S.K n
  let header := decAfterBase (upRootBase Bc T) (upTabLen Bc T)
  let tables := hintDecoderTables S P hT (upWideWord W) Bc header
  have h := upHint_prepared (crFamily_rows S) (crFamily_columns S)
    (fun Nv t ht c hc => crFamily_range S Nv t c) hArgs fuel T hTree
  have hPlacement : upRootBase Bc T + upTabLen Bc T ≤ header := Nat.le_add_right _ _
  have hh := upSavedRoot_toggles_assembled (crFamily S) P W Bc n (colBℓ S.K n) T hT
    (hintCu (hintColK S.K) * lg (n : ℝ) ^ hintpu) header (tables.blocks S P previous header T.N)
    hPlacement h.word_min h.fits h.words h.static h.universe_fits h.positive h.padding h.ell_pos h.ell h.cost r
  dsimp only [HintDecoderTables.det]
  simpa only [mul_assoc] using hh

end
end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintSavedToggles_nativeTables
#print axioms LinearSetReconciliation327.Main.upRoot_layout_fits
#print axioms LinearSetReconciliation327.Main.upRoot_localTree
#print axioms LinearSetReconciliation327.Main.UpLocalTree.of_table_extension
#print axioms LinearSetReconciliation327.Main.upHint_prepared
#print axioms LinearSetReconciliation327.Main.crFamily_rows
#print axioms LinearSetReconciliation327.Main.crFamily_columns
#print axioms LinearSetReconciliation327.Main.crFamily_range
#print axioms LinearSetReconciliation327.Main.hintH_trees
#print axioms LinearSetReconciliation327.Main.hintW
#print axioms LinearSetReconciliation327.Main.hintP
#print axioms LinearSetReconciliation327.Main.upSavedRoot_toggles_assembled
end -- Def_LinearSetReconciliation327_Main_HintNativeSharedTable20261120

section -- Def_LinearSetReconciliation327_Main_HintSavedTogglesGrown20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintSavedToggles_grown (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (base growth Bc U Bell : ℕ) (B : ℝ) (previous : ℕ → ℕ)
    (hGrowth : 1 ≤ growth) (hW : 8 ≤ base) (hFit : (hintSpec T).Fits base)
    (hWords : wordsOf base (synLen (crFamily S) T) ≤ 2 ^ base)
    (hStatic : UpTreeStatic (crFamily S) Bc U T) (hU : U ≤ 2 ^ base) (hN : 0 < T.N)
    (hBc : Bc ≤ 4 * (2 ^ base) ^ 3) (hBell : 1 ≤ Bell) (hEll : UpEllOK Bell T)
    (hCost : ((125 * (T.nodeCount * (T.depth + Bell + Bc)) + 12 : ℕ) : ℝ) ≤ B)
    (r : (hintSpec T).Seed) :
    let word := growth * base
    let wide := upWideWord word
    let header := decAfterBase (upRootBase Bc T) (upTabLen Bc T)
    let D := hintDecoderTables S H hT wide Bc header
    TogglesWithin progUpSaved
      ((hintSpec T).env wide (D.det S H (upRootDet (crFamily S) word Bc T) previous header T.N) r)
      (hintH_trees (crFamily S) H T hT r) (3 * B) := by
  let word := growth * base
  let wide := upWideWord word
  let header := decAfterBase (upRootBase Bc T) (upTabLen Bc T)
  let D := hintDecoderTables S H hT wide Bc header
  have hLe : base ≤ word := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right base hGrowth
  have hPow : 2 ^ base ≤ 2 ^ word := Nat.pow_le_pow_right (by decide) hLe
  have hPlacement : upRootBase Bc T + upTabLen Bc T ≤ header := Nat.le_add_right _ _
  have hBw : Bc ≤ 4 * (2 ^ word) ^ 3 := hBc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hPow 3))
  have hWords' : wordsOf word (synLen (crFamily S) T) ≤ 2 ^ word :=
    (wordsOf_antitone_word (by omega) hLe).trans (hWords.trans hPow)
  exact upSavedRoot_toggles_assembled (crFamily S) H word Bc U Bell T hT B header
    (D.blocks S H previous header T.N) hPlacement (hW.trans hLe) (fits_mono_word _ hLe hFit)
    hWords' hStatic (hU.trans hPow) hN hBw hBell hEll hCost r

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintSavedToggles_grown
end -- Def_LinearSetReconciliation327_Main_HintSavedTogglesGrown20261120


