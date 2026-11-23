-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Bundle51_17a
-- name    : LinearSetReconciliation327_Main_Bundle51_17a
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T10:15:12.639187+00:00
-- url     : https://prove2.me/theorems/e3f68bb6-7775-42f3-95e5-6835ad9d8e0b
-- title:
--   LinearSetReconciliation327 鈥?Bundle51_17a
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_Bundle51_17a` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintBoundsProof20261120
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_13
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_16

/-! Bundled module: LinearSetReconciliation327_Main_Bundle51_17a
    Members (declaration text copied byte-identically, dependency order):
      * Definitions.Def_LinearSetReconciliation327_Main_HintTimeAnalytic20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRootPhaseBudget20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPaperRunBudget20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintSeedDistribution20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintBoundsBudget20261120
    Only `import` lines were merged; every member body is wrapped in its own
    `section ... end` so that per-file `set_option`s stay scoped. -/

section -- Def_LinearSetReconciliation327_Main_HintTimeAnalytic20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintTimeColFactor (A C : ℕ) : ℝ := 48 * ((A : ℝ) + C + 2) + 2
def hintTimePadFactor (S : CRSourceBundle) : ℝ := 4 * S.K + 1
def hintTimeCRFactor (S : CRSourceBundle) : ℝ := 4 * (33 * S.K + 184) + 1
def hintTimeNodeFactor (A : ℕ) (K : ℝ) : ℝ := K * A

def hintTimeCountFactor (A C : ℕ) (K : ℝ) : ℝ :=
  (4 * hintTimeColFactor A C + 5) * hintTimeNodeFactor A K

def hintTimeLinearFactor (A : ℕ) (K : ℝ) : ℝ := 5 * hintTimeNodeFactor A K

def hintTimeRecordFactor (S : CRSourceBundle) (A C : ℕ) (K : ℝ) : ℝ :=
  (hintTimePadFactor S + hintTimeColFactor A C + 3) * hintTimeNodeFactor A K

def hintTimeBitFactor (S : CRSourceBundle) (A C : ℕ) (K : ℝ) : ℝ :=
  (hintTimeColFactor A C + 1 + hintTimeCRFactor S) * hintTimeNodeFactor A K

noncomputable def hintTimeBaseFactor (S : CRSourceBundle) (A C : ℕ) (K : ℝ) : ℝ :=
  65536 * Real.exp (hintRowExpRate A C) +
    147 * (1 + hintTimePadFactor S + hintTimeRecordFactor S A C K) * Real.exp 15 + 68

def hintTimeExtraFactor (S : CRSourceBundle) (A C : ℕ) (K : ℝ) : ℝ :=
  17 * hintTimeBitFactor S A C K + hintTimeCRFactor S + 37

noncomputable def hintDecoderTimeConstant (S : CRSourceBundle) (A C : ℕ) (K : ℝ) : ℝ :=
  hintCombinedTimeConstant (hintTimeBaseFactor S A C K * hintTimeCountFactor A C K)
    (hintTimeExtraFactor S A C K * hintTimeLinearFactor A K) (hintRowExpRate A C + 15) 30 (27 + 30)

theorem hintRowExpRate_nonneg (A C : ℕ) : 0 ≤ hintRowExpRate A C := by
  have hLog : 0 ≤ Real.log ((hintRowSizeFactor A C : ℝ) + 2) := Real.log_nonneg (by have h : (0 : ℝ) ≤ (hintRowSizeFactor A C : ℝ) := Nat.cast_nonneg _; linarith)
  have hLn2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold hintRowExpRate hintRowLogFactor hintOutsideLogFactor
  positivity

theorem hintDecoderTimeConstant_pos (S : CRSourceBundle) (A C : ℕ) (K : ℝ) :
    0 < hintDecoderTimeConstant S A C K := hintCombinedTimeConstant_pos _ _ _ _ _

theorem hintDecoderTimeBounds (S : CRSourceBundle) (H : HintParams) (K : ℝ)
    (N X Y fuel : ℕ) (T : Node) (offsets : ℕ → ℕ)
    (hArgs : H.NodeArgs N X Y) (hTree : H.tree fuel N X Y = some T) (hWF : Node.WF T X Y)
    (hRoot : T.N = N) (hK : 0 ≤ K)
    (hCount : (T.nodeCount : ℝ) ≤ K * (H.A : ℝ) * H.lgn ^ 27) :
    let CR := crFamily S
    let L := H.lgn
    let Bc := colBc S.K H.n
    let events := hintTreeEvents CR offsets T 0 0 (offsets 0)
    let base := hintDecBase H Bc (upRest Bc T)
    let extra := hintDecExtra S H N (synLen CR T)
    (events.length : ℝ) ≤ hintTimeCountFactor H.A H.C K * N * L ^ 30 ∧
    ((events.filter HintTreeEvent.linearWork).length : ℝ) ≤ hintTimeLinearFactor H.A K * L ^ 27 ∧
    (base : ℝ) + 44 ≤ hintTimeBaseFactor S H.A H.C K * Real.exp ((hintRowExpRate H.A H.C + 15) * (lg L) ^ 2) ∧
    (extra : ℝ) ≤ hintTimeExtraFactor S H.A H.C K * N * L ^ 30 := by
  let CR := crFamily S
  let L := H.lgn
  let Bc := colBc S.K H.n
  let cols := hintEventColCap H
  let events := hintTreeEvents CR offsets T 0 0 (offsets 0)
  let base := hintDecBase H Bc (upRest Bc T)
  let extra := hintDecExtra S H N (synLen CR T)
  let c := hintTimeColFactor H.A H.C
  let b := hintTimePadFactor S
  let d := hintTimeCRFactor S
  let k := hintTimeNodeFactor H.A K
  let rate := hintRowExpRate H.A H.C
  have hL : 1 ≤ L := one_le_lg hArgs.1
  have hL0 : 0 ≤ L := by linarith
  have hL2 : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL (by decide)
  have hL30 : L ^ 2 ≤ L ^ 30 := pow_le_pow_right₀ hL (by decide)
  have hOne3 : 1 ≤ L ^ 3 := one_le_pow₀ hL
  have hOne30 : 1 ≤ L ^ 30 := one_le_pow₀ hL
  have hN : 1 ≤ N := hArgs.2.2.1
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hS0 := S.K_pos.le
  have hb : 0 ≤ b := by unfold b hintTimePadFactor; positivity
  have hc : 0 ≤ c := by unfold c hintTimeColFactor; positivity
  have hd : 0 ≤ d := by unfold d hintTimeCRFactor; positivity
  have hk : 0 ≤ k := by unfold k hintTimeNodeFactor; positivity
  have hCols : (cols : ℝ) ≤ c * L ^ 3 := hintTime_cols_le H hArgs.1
  have hPad : (Bc : ℝ) ≤ b * L ^ 3 :=
    (hintTime_padding_le S H hArgs.1).trans (mul_le_mul_of_nonneg_left hL2 hb)
  have hCount' : (T.nodeCount : ℝ) ≤ k * L ^ 27 := hCount
  have hSum : (Bc : ℝ) + cols + 3 ≤ (b + c + 3) * L ^ 3 := by nlinarith only [hCols, hPad, hOne3]
  have hShape := hintScheduleShape_tree H N fuel N X Y T le_rfl hArgs hTree
  have hUP : (upRest Bc T : ℝ) ≤ hintTimeRecordFactor S H.A H.C K * L ^ 30 := by
    have h := hintUpRest_le Bc cols T (HintScheduleShape.ell T hShape)
    have hCast : (upRest Bc T : ℝ) ≤ ((Bc : ℝ) + cols + 3) * T.nodeCount :=
      by exact_mod_cast (show upRest Bc T ≤ (Bc + cols + 3) * T.nodeCount by omega)
    calc
      _ ≤ _ := hCast
      _ ≤ ((b + c + 3) * L ^ 3) * (k * L ^ 27) :=
        mul_le_mul hSum hCount' (Nat.cast_nonneg _) (by positivity)
      _ = _ := by unfold hintTimeRecordFactor; change _ = (b + c + 3) * k * L ^ 30; ring
  have hCRCap : (hintCRTimeCap S H N : ℝ) ≤ d * N * L ^ 2 := hintCRTimeCap_real_le S H hArgs.1 hN
  have hRows (m t : ℕ) (hm : m ≤ N) (ht : t ≤ m) : CR.rows m t ≤ hintCRTimeCap S H N := by
    change (S.data m t).R ≤ _
    by_cases hm0 : m = 0
    · subst m
      rw [S.invalid 0 t (by simp)]
      exact Nat.zero_le _
    · have hCR := hintCRTimeCap_bounds S H hArgs.1 hArgs.2.2.2.1 (by omega : 1 ≤ m) hm ht
      have hR : (S.data m t).R ≤ hintCRNodeBudget S m t := by unfold hintCRNodeBudget; omega
      exact hR.trans hCR
  have hBits : (synLen CR T : ℝ) ≤ hintTimeBitFactor S H.A H.C K * N * L ^ 30 := by
    have h := hintSynLen_le_of_shape CR N cols (hintCRTimeCap S H N) hRows T X Y hRoot.le hWF hShape
    have hCast : (synLen CR T : ℝ) ≤ ((N : ℝ) * cols + N + hintCRTimeCap S H N) * T.nodeCount := by exact_mod_cast h
    have hP1 := mul_le_mul_of_nonneg_left hCols (Nat.cast_nonneg N)
    have hP2 : (N : ℝ) ≤ N * L ^ 3 := by simpa using mul_le_mul_of_nonneg_left hOne3 (Nat.cast_nonneg N)
    have hP3 : (hintCRTimeCap S H N : ℝ) ≤ d * N * L ^ 3 :=
      hCRCap.trans (mul_le_mul_of_nonneg_left hL2 (by positivity))
    have hP : (N : ℝ) * cols + N + hintCRTimeCap S H N ≤ (c + 1 + d) * N * L ^ 3 :=
      by nlinarith only [hP1, hP2, hP3]
    calc
      _ ≤ _ := hCast
      _ ≤ ((c + 1 + d) * (N : ℝ) * L ^ 3) * (k * L ^ 27) :=
        mul_le_mul hP hCount' (Nat.cast_nonneg _) (by positivity)
      _ = _ := by unfold hintTimeBitFactor; change _ = (c + 1 + d) * k * N * L ^ 30; ring
  have hEvent : (events.length : ℝ) ≤ hintTimeCountFactor H.A H.C K * N * L ^ 30 := by
    have h := hintTreeEvents_count_actual CR offsets fuel T hArgs hTree 0 0 (offsets 0)
    have hCast : (events.length : ℝ) ≤ ((2 * (N : ℝ) + 2) * cols + 2 * N + 3) * T.nodeCount := by exact_mod_cast h
    have hC1 : 2 * (N : ℝ) + 2 ≤ 4 * N := by linarith
    have hC2 := mul_le_mul hC1 hCols (Nat.cast_nonneg cols) (by positivity)
    have hC3 : 2 * (N : ℝ) + 3 ≤ 5 * N * L ^ 3 := by
      have h' := mul_le_mul_of_nonneg_left hOne3 (show 0 ≤ 5 * (N : ℝ) by positivity)
      nlinarith only [h', hNR]
    have hC4 : (2 * (N : ℝ) + 2) * cols + 2 * N + 3 ≤ (4 * c + 5) * N * L ^ 3 :=
      by nlinarith only [hC2, hC3]
    calc
      _ ≤ _ := hCast
      _ ≤ ((4 * c + 5) * (N : ℝ) * L ^ 3) * (k * L ^ 27) :=
        mul_le_mul hC4 hCount' (Nat.cast_nonneg _) (by positivity)
      _ = _ := by unfold hintTimeCountFactor; change _ = (4 * c + 5) * k * N * L ^ 30; ring
  have hLinear : ((events.filter HintTreeEvent.linearWork).length : ℝ) ≤ hintTimeLinearFactor H.A K * L ^ 27 := by
    have hFrom := hintTreeEvents_linearWork_count CR offsets T 0 0 (offsets 0)
    have hCast : ((events.filter HintTreeEvent.linearWork).length : ℝ) ≤ 5 * (T.nodeCount : ℝ) := by
      exact_mod_cast (show (events.filter HintTreeEvent.linearWork).length ≤ 5 * T.nodeCount from by
        change (events.filter HintTreeEvent.linearWork).length + 2 ≤ 5 * T.nodeCount at hFrom
        omega)
    unfold hintTimeLinearFactor
    exact hCast.trans (by nlinarith only [mul_le_mul_of_nonneg_left hCount' (by norm_num : (0 : ℝ) ≤ 5)])
  refine ⟨hEvent, hLinear, ?_, ?_⟩
  · have hR : 0 ≤ rate := hintRowExpRate_nonneg _ _
    have hE : 1 ≤ Real.exp ((rate + 15) * (lg L) ^ 2) :=
      Real.one_le_exp (by positivity)
    have hE1 : Real.exp (rate * (lg L) ^ 2) ≤ Real.exp ((rate + 15) * (lg L) ^ 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
    have hE2 : Real.exp (15 * (lg L) ^ 2) ≤ Real.exp ((rate + 15) * (lg L) ^ 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
    have hPow : L ^ 3 ≤ L ^ 30 := pow_le_pow_right₀ hL (by decide)
    have hPad' := hPad.trans (mul_le_mul_of_nonneg_left hPow hb)
    have hQ : 1 + (Bc : ℝ) + upRest Bc T ≤ (1 + b + hintTimeRecordFactor S H.A H.C K) * L ^ 30 :=
      by nlinarith only [hUP, hPad', hOne30]
    have hQ0 : 0 ≤ 1 + b + hintTimeRecordFactor S H.A H.C K := by
      unfold hintTimeRecordFactor
      change 0 ≤ 1 + b + (b + c + 3) * k
      positivity
    have hPexp : L ^ 30 ≤ Real.exp 15 * Real.exp ((rate + 15) * (lg L) ^ 2) := by
      apply (hintLogPower_le_exp L hL 30).trans
      norm_num
      exact mul_le_mul_of_nonneg_left hE2 (by positivity)
    have hFinal := hQ.trans (mul_le_mul_of_nonneg_left hPexp hQ0)
    have hRow := (hintUniformRowCost_le H hArgs.1).trans
      (mul_le_mul_of_nonneg_left hE1 (by positivity))
    change (base : ℝ) + 44 ≤ _
    unfold base hintDecBase hintTimeBaseFactor
    push_cast
    change _ ≤ (65536 * Real.exp rate + 147 * (1+b+hintTimeRecordFactor S H.A H.C K) * Real.exp 15 + 68) *
      Real.exp ((rate+15) * (lg L)^2)
    nlinarith only [hRow, hFinal, hE]
  · have hCRMax := hCRCap.trans (mul_le_mul_of_nonneg_left hL30 (show 0 ≤ d * (N : ℝ) by positivity))
    have hNmax : (N : ℝ) ≤ N * L ^ 30 := by simpa using mul_le_mul_of_nonneg_left hOne30 (Nat.cast_nonneg N)
    change (extra : ℝ) ≤ _
    unfold extra hintDecExtra hintTimeExtraFactor
    push_cast
    change _ ≤ (17 * hintTimeBitFactor S H.A H.C K + d + 37) * N * L ^ 30
    nlinarith only [hBits, hCRMax, hNmax, hNR]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecoderTimeBounds
end -- Def_LinearSetReconciliation327_Main_HintTimeAnalytic20261120

section -- Def_LinearSetReconciliation327_Main_HintRootPhaseBudget20261120
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearSetReconciliation327.Main

theorem hintActualDecoderLimits_withInputs (S : CRSourceBundle) (H : HintParams) (K : ℝ)
    (fuel N X Y base : ℕ) (T : Node)
    (hArgs : H.NodeArgs N X Y) (hTree : H.tree fuel N X Y = some T)
    (hCount : (T.nodeCount : ℝ) ≤ K * (H.A : ℝ) * H.lgn ^ 27)
    (hBase : 1 ≤ base) (hBaseLog : Nat.clog 2 (H.n + 2) ≤ base) :
    let Bc := colBc S.K H.n
    let growth := hintWidthScale (hintResourceCoefficient S H.A H.C K) (hintResourceDegree S)
    let header := decAfterBase (upRootBase Bc T) (upTabLen Bc T)
    ∃ hT : IsSchemeTree H T, T.N = N ∧ Node.WF T X Y ∧
      (∀ node seed, ∀ info ∈ hintNodeInfos (crFamily S) hT node seed, HintActualNodeInput H N info) ∧
      HintDecoderLimits S H hT (upWideWord (growth * base)) Bc header := by
  let CR := crFamily S
  let Bc := colBc S.K H.n
  let coefficient := hintResourceCoefficient S H.A H.C K
  let degree := hintResourceDegree S
  let growth := hintWidthScale coefficient degree
  let wide := upWideWord (growth * base)
  let q := coefficient * (H.n + 2) ^ degree
  let header := decAfterBase (upRootBase Bc T) (upTabLen Bc T)
  obtain ⟨hT, hRoot, hWF, hInputs⟩ := hintActualTreeInfo H CR fuel N X Y T hArgs hTree
  obtain ⟨hU, hPad, hCol, hCount', hCR⟩ := hintRawResources_polynomial S H K T hArgs.1 hCount
  change H.n ≤ q at hU
  have hs : UpTreeStatic CR Bc H.n T := by
    apply upTreeStatic_tree CR H Bc ?_ fuel N X Y T hArgs hTree
    intro m t hmn ht i hi
    exact ⟨col_card_le_ceil (crFamily_columns S m t ht i) hmn, crFamily_range S m t i⟩
  have hCaps := hintWidthResources_of_actual S H fuel N X Y Bc q hT hArgs hTree hRoot hWF
    (hInputs 0 0) hU hPad hCol hCount' hCR hs
  have hSpan := hintWidthScale_fits H.n coefficient degree base hBase hBaseLog
  change 128 * (hintActualResourceCap q + 1) ^ 4 < 2 ^ (4 * (growth * base)) at hSpan
  have hHeader : 3 < header := by unfold header decAfterBase upRootBase; omega
  have hG : 1 ≤ growth * base := Nat.mul_pos (hintWidthScale_pos coefficient degree) hBase
  have hHalf : 2 ^ (4 * (growth * base)) ≤ 2 ^ wide :=
    Nat.pow_le_pow_right (by decide) (by unfold wide upWideWord; omega)
  have hQ2 : 2 ≤ q := hArgs.1.trans hU
  have hBig : q ^ 3 ≤ 128 * (hintActualResourceCap q + 1) ^ 4 := by
    have h1 : q ≤ hintActualResourceCap q + 1 := by
      unfold hintActualResourceCap
      nlinarith only [show 0 ≤ q from Nat.zero_le _, show 0 ≤ q ^ 2 from Nat.zero_le _,
        show 0 ≤ q ^ 3 from Nat.zero_le _, show 0 ≤ q ^ 4 from Nat.zero_le _]
    have h2 : (hintActualResourceCap q + 1) ^ 3 ≤ (hintActualResourceCap q + 1) ^ 4 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    exact (Nat.pow_le_pow_left h1 3).trans (h2.trans (by omega))
  have hQfit : q ^ 3 ≤ 2 ^ wide := hBig.trans (hSpan.le.trans hHalf)
  have hQle : q ≤ q ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ q) (by decide : 1 ≤ 3)
  have hShape := hintScheduleShape_tree H q fuel N X Y T (hArgs.2.2.2.1.trans hU) hArgs hTree
  have hEll : UpEllOK q T :=
    HintScheduleShape.ell T (HintScheduleShape.mono le_rfl hCol T hShape)
  have hDims := UpDimsBound.mono (max_le hU le_rfl) T (upDims_actual_tree H q fuel N X Y T hArgs hTree hEll)
  have hFit : (hintSpec T).Fits wide :=
    upSpecFits_of_dims T q wide (by omega) hDims (hCount'.trans (hQle.trans hQfit))
      hQfit (hQ2.trans (hQle.trans hQfit))
  have hSize : 2 ≤ hintActualResourceCap q := by
    have hPositive : 1 ≤ (q + 1) ^ 4 := one_le_pow₀ (by omega)
    unfold hintActualResourceCap
    omega
  exact ⟨hT, hRoot, hWF, hInputs, hintDecoderLimits_of_resources S H hT (growth * base) Bc header (hintActualResourceCap q)
    H.n hHeader hG hSize hCaps hs hFit hSpan⟩


theorem hintPlacedTreeRoot_total_budget_follows (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (r : (hintSpec T).Seed) (up previous : ℕ → ℕ)
    (W Bc header X Y U radius base extra : ℕ) (hLimits : HintDecoderLimits S H hT W Bc header)
    (hN : 0 < T.N) (hWF : Node.WF T X Y) (hRead : 24 ≤ base)
    (hCost : HintTreeTimeBounds S H Bc U radius base extra hT) :
    let D := hintDecoderTables S H hT W Bc header
    HintBudgetFollows D.events 0 D.events.length
      (hintPlacedTreeRoot_total S H hT r up previous W Bc header X Y hLimits hN hWF).budget
      (fun e => base + (if e.linearWork then extra else 0)) := by
  let D := hintDecoderTables S H hT W Bc header
  have he : D.events = hintTreeEvents (crFamily S) (fun i => D.placement.inputWord i * W) T 0 0
      (D.placement.inputWord 0 * W) := by
    rw [show D.placement.inputWord 0 = 0 from rfl, Nat.zero_mul]
    exact hintDecoderTables_events S H hT W Bc header
  dsimp only
  with_unfolding_all simp only [hintPlacedTreeRoot_total, id, HintDecoderPhase.relabel_budget_eq]
  apply HintDecoderPhase.cast_budget_follows (h := congrArg List.length he)
  apply hintDecodePlacedTree_total_budget_follows (hRead := hRead)
  exact hCost

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintActualDecoderLimits_withInputs
#print axioms LinearSetReconciliation327.Main.hintPlacedTreeRoot_total_budget_follows
end -- Def_LinearSetReconciliation327_Main_HintRootPhaseBudget20261120

section -- Def_LinearSetReconciliation327_Main_HintPaperRunBudget20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintPaperRunBudget (S : CRSourceBundle) (H : HintParams) (K : ℝ)
    {T : Node} (hT : IsSchemeTree H T) (up previous : ℕ → ℕ)
    (N X Y fuel W header : ℕ) (hArgs : H.NodeArgs N X Y) (hTree : H.tree fuel N X Y = some T)
    (hK : 0 ≤ K) (hCount : (T.nodeCount : ℝ) ≤ K * (H.A : ℝ) * H.lgn ^ 27)
    (hRoot : T.N = N) (hWF : Node.WF T X Y) (hN : 0 < T.N)
    (hInputs : ∀ info ∈ hintNodeInfos (crFamily S) hT 0 0, HintActualNodeInput H N info)
    (hLimits : HintDecoderLimits S H hT W (colBc S.K H.n) header)
    (r : (hintSpec T).Seed) :
    let Bc := colBc S.K H.n
    let D := hintDecoderTables S H hT W Bc header
    (hintPhaseRunBudget S D.events.length T.N
      (hintPlacedTreeRoot_total S H hT r up previous W Bc header X Y hLimits hN hWF).budget : ℝ) ≤
      hintDecoderTimeConstant S H.A H.C K * (T.N : ℝ) *
        Real.exp (hintDecoderTimeConstant S H.A H.C K * (lg H.lgn) ^ 2) := by
  let Bc := colBc S.K H.n
  let D := hintDecoderTables S H hT W Bc header
  let base := hintDecBase H Bc (upRest Bc T)
  let extra := hintDecExtra S H N (synLen (crFamily S) T)
  let offsets := fun i => D.placement.inputWord i * W
  let phase := hintPlacedTreeRoot_total S H hT r up previous W Bc header X Y hLimits hN hWF
  have hRead : 24 ≤ base := by unfold base hintDecBase; omega
  have hCaps := hintTreeTimeBounds_of_inputs S H hT N Bc (synLen (crFamily S) T) (upRest Bc T)
    hArgs.1 hArgs.2.2.2.1 0 0 hInputs le_rfl le_rfl
  have hLocal := hintPlacedTreeRoot_total_budget_follows S H hT r up previous W Bc header X Y
    (hintUniformRowSize H) (hintUniformOutside H) base extra hLimits hN hWF hRead hCaps
  have he : D.events = hintTreeEvents (crFamily S) offsets T 0 0 (offsets 0) := by
    have hOffset0 : offsets 0 = 0 := by change 0 * W = 0; exact Nat.zero_mul _
    rw [hOffset0]
    exact hintDecoderTables_events S H hT W Bc header
  obtain ⟨hLength, hLinear, hBase, hExtra⟩ :=
    hintDecoderTimeBounds S H K N X Y fuel T offsets hArgs hTree hWF hRoot hK hCount
  rw [← he] at hLength hLinear
  rw [← hRoot] at hLength
  have hExtra' : (extra : ℝ) ≤ hintTimeExtraFactor S H.A H.C K * (T.N : ℝ) * H.lgn ^ 30 := by
    rw [hRoot]
    exact hExtra
  have hSK := S.K_pos.le
  have hCount0 : 0 ≤ hintTimeCountFactor H.A H.C K := by
    unfold hintTimeCountFactor hintTimeColFactor hintTimeNodeFactor
    positivity
  have hLinear0 : 0 ≤ hintTimeLinearFactor H.A K := by
    unfold hintTimeLinearFactor hintTimeNodeFactor
    positivity
  have hBase0 : 0 ≤ hintTimeBaseFactor S H.A H.C K := by
    unfold hintTimeBaseFactor hintTimeRecordFactor hintTimePadFactor hintTimeColFactor hintTimeNodeFactor
    positivity
  have hExtra0 : 0 ≤ hintTimeExtraFactor S H.A H.C K := by
    unfold hintTimeExtraFactor hintTimeBitFactor hintTimeColFactor hintTimeCRFactor hintTimeNodeFactor
    positivity
  have hRate : 0 ≤ hintRowExpRate H.A H.C + 15 :=
    add_nonneg (hintRowExpRate_nonneg _ _) (by norm_num)
  exact hintScheduledRunBudget_le S D.events T.N phase.budget base extra H.lgn (hintTimeBaseFactor S H.A H.C K)
    (hintTimeExtraFactor S H.A H.C K) (hintTimeCountFactor H.A H.C K) (hintTimeLinearFactor H.A K)
    (hintRowExpRate H.A H.C + 15) 30 27 30 hN (one_le_lg hArgs.1)
    hBase0 hExtra0 hCount0 hLinear0 hRate hLocal hLength hLinear hBase hExtra'

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPaperRunBudget
end -- Def_LinearSetReconciliation327_Main_HintPaperRunBudget20261120

section -- Def_LinearSetReconciliation327_Main_HintSeedDistribution20261120
set_option autoImplicit false
noncomputable section
open Finset
namespace LinearSetReconciliation327.Main

def SeedReadEq (R : Node) (r r' : (hintSpec R).Seed) (k : ℕ) : Prop :=
  (∀ hp : k < (hintSpec R).permSizes.length, r.1 ⟨k, hp⟩ = r'.1 ⟨k, hp⟩) ∧
  (∀ hc : k < (hintSpec R).coeffShapes.length, r.2 ⟨k, hc⟩ = r'.2 ⟨k, hc⟩)

theorem permNode_injective_at (R : Node) (r r' : (hintSpec R).Seed) (k N : ℕ)
    (hp : k < (hintSpec R).permSizes.length)
    (hn : (hintSpec R).permSizes.get ⟨k, hp⟩ = N)
    (he : permNode R r k N = permNode R r' k N) : r.1 ⟨k, hp⟩ = r'.1 ⟨k, hp⟩ := by
  subst N
  simpa only [permNode, dif_pos hp, dif_pos rfl, dif_pos trivial] using he

/-- All flattened coefficients can be recovered from the row-column-local
reads, including zero-dimensional tables. -/
theorem coeffAt_injective_at (R : Node) (r r' : (hintSpec R).Seed) (k M L V : ℕ)
    (hc : k < (hintSpec R).coeffShapes.length)
    (hl : ((hintSpec R).coeffShapes.get ⟨k, hc⟩).1 = M * L * V)
    (hv : ((hintSpec R).coeffShapes.get ⟨k, hc⟩).2 = 2)
    (he : ∀ j : Fin M, ∀ s : Fin L, ∀ v : Fin V,
      coeffAt R r k ((j.val * L + s.val) * V + v.val) =
        coeffAt R r' k ((j.val * L + s.val) * V + v.val)) :
    r.2 ⟨k, hc⟩ = r'.2 ⟨k, hc⟩ := by
  funext a
  let q : Fin (M * L * V) := ⟨a.val, by simpa only [hl] using a.isLt⟩
  obtain ⟨⟨b, v⟩, hq⟩ := (finProdFinEquiv : Fin (M * L) × Fin V ≃ Fin (M * L * V)).surjective q
  obtain ⟨⟨j, s⟩, hb⟩ := (finProdFinEquiv : Fin M × Fin L ≃ Fin (M * L)).surjective b
  rw [← hb] at hq
  have hidx : (j.val * L + s.val) * V + v.val = a.val := by
    calc
      (j.val * L + s.val) * V + v.val = v.val + V * (s.val + L * j.val) := by ring
      _ = a.val := congrArg Fin.val hq
  have hh := he j s v
  rw [hidx] at hh
  have ha : a.val < ((hintSpec R).coeffShapes.get ⟨k, hc⟩).1 := a.isLt
  simp only [coeffAt, dif_pos hc, dif_pos ha] at hh
  apply Fin.ext
  have hmod := congrArg ZMod.val hh
  have h1 : (r.2 ⟨k, hc⟩ a).val < 2 := by simpa only [hv] using (r.2 ⟨k, hc⟩ a).isLt
  have h2 : (r'.2 ⟨k, hc⟩ a).val < 2 := by simpa only [hv] using (r'.2 ⟨k, hc⟩ a).isLt
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] using hmod

theorem seedReadEq_of_local (P : HintParams) (R : Node) (r r' : (hintSpec R).Seed)
    (T : Node) (k N X Y : ℕ)
    (hhead : (schemeNodes R)[k]? = some T)
    (hN : T.N = N) (hM : nodeM T = P.rows X Y)
    (hL : nodeEll T = P.ell N X Y) (hV : nodeNmax T = P.Nmax N X Y)
    (he1 : permNode R r k N = permNode R r' k N)
    (he2 : coinsNode P R r N X Y k = coinsNode P R r' N X Y k) :
    SeedReadEq R r r' k := by
  obtain ⟨hp, hpN⟩ := permSizes_get_of_block hhead
  obtain ⟨hc, hcS⟩ := coeffShapes_get_of_block hhead
  constructor
  · intro hp'
    exact permNode_injective_at R r r' k N hp' (hpN.trans hN) he1
  · intro hc'
    apply coeffAt_injective_at R r r' k (P.rows X Y) (P.ell N X Y) (P.Nmax N X Y) hc'
    · rw [hcS]
      change nodeM T * nodeEll T * nodeNmax T = _
      rw [hM, hL, hV]
    · rw [hcS]; rfl
    · intro j s v
      exact congrFun (congrFun (congrFun he2 j) s) v

/-- Prefix sums cover every index of a flattened dependent child list. -/
theorem forall_ofFn_offsets (Q : ℕ → Prop) : ∀ (n : ℕ) (len : Fin n → ℕ) (k : ℕ),
    (∀ s : Fin n, ∀ j, j < len s → Q (k + ((List.ofFn len).take s.val).sum + j)) →
    ∀ j, j < (List.ofFn len).sum → Q (k + j) := by
  intro n
  induction n with
  | zero => intro len k h j hj; simp at hj
  | succ n ih =>
      intro len k h j hj
      by_cases hj0 : j < len 0
      · simpa only [Fin.val_zero, List.take_zero, List.sum_nil, Nat.add_zero] using h 0 j hj0
      · have hj1 : j - len 0 < (List.ofFn fun s : Fin n => len s.succ).sum := by
          simp only [List.ofFn_succ, List.sum_cons] at hj
          omega
        have htail : ∀ s : Fin n, ∀ a, a < len s.succ →
            Q (k + len 0 + ((List.ofFn fun s : Fin n => len s.succ).take s.val).sum + a) := by
          intro s a ha
          simpa only [Fin.val_succ, List.ofFn_succ, List.take_succ_cons, List.sum_cons,
            Nat.add_assoc] using h s.succ a ha
        have hh := ih (fun s : Fin n => len s.succ) (k + len 0) htail (j - len 0) hj1
        have he : k + len 0 + (j - len 0) = k + j := by omega
        rwa [he] at hh

end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main

theorem seedReadEq_of_hintKappaAux (P : HintParams) (R : Node)
    (r r' : (hintSpec R).Seed) (T : Node) (hT : IsSchemeTree P T) :
    ∀ k, BlockOf R k (schemeNodes T) →
      hintKappaAux P R r T hT k = hintKappaAux P R r' T hT k →
      ∀ j, j < (schemeNodes T).length → SeedReadEq R r r' (k + j) := by
  induction hT with
  | store N => intro k hb he j hj; simp [schemeNodes] at hj
  | cr N t => intro k hb he j hj; simp [schemeNodes] at hj
  | direct N X Y t =>
      intro k hb he j hj
      have hj0 : j = 0 := by simpa only [schemeNodes, List.length_singleton, Nat.lt_one_iff] using hj
      subst j
      rw [Nat.add_zero]
      exact seedReadEq_of_local P R r r' (.direct (P.scheme N X Y) t) k N X Y
        (BlockOf_head hb) rfl rfl rfl rfl (congrArg Prod.fst he) (congrArg Prod.snd he)
  | recursive N X Y t Xs Ys child hchild ih =>
      intro k hb he j hj
      have hloc := congrArg Prod.fst he
      have hhead := seedReadEq_of_local P R r r' (.recursive (P.scheme N X Y) t Xs Ys child)
        k N X Y (BlockOf_head hb) rfl rfl rfl rfl (congrArg Prod.fst hloc) (congrArg Prod.snd hloc)
      by_cases hj0 : j = 0
      · subst j; simpa only [Nat.add_zero] using hhead
      · have hlen : j - 1 < (List.ofFn fun s : Fin (P.scheme N X Y).ℓ => (schemeNodes (child s)).length).sum := by
          rw [schemeNodes_recursive, List.length_append, List.length_singleton, flatten_length_eq_sum] at hj
          omega
        have hkids : ∀ s : Fin (P.scheme N X Y).ℓ, ∀ a, a < (schemeNodes (child s)).length →
            SeedReadEq R r r' (k + 1 +
              ((List.ofFn fun s : Fin (P.scheme N X Y).ℓ => (schemeNodes (child s)).length).take s.val).sum + a) := by
          intro s a ha
          apply ih s _ (BlockOf_child hb s) _ a ha
          exact congrArg (fun z : Node.Seed (.recursive (P.scheme N X Y) t Xs Ys child) => z.2 s) he
        have hh := forall_ofFn_offsets (SeedReadEq R r r') (P.scheme N X Y).ℓ
          (fun s => (schemeNodes (child s)).length) (k + 1) hkids (j - 1) hlen
        have heq : k + 1 + (j - 1) = k + j := by omega
        rwa [heq] at hh

/-- The implemented preorder seed splitting discards none of its input. -/
theorem hintKappa_injective (P : HintParams) (T : Node) (hT : IsSchemeTree P T) :
    Function.Injective (hintKappa P T hT) := by
  intro r r' he
  have hh := seedReadEq_of_hintKappaAux P T r r' T hT 0 (blockOf_self T) he
  apply Prod.ext
  · funext k
    have hk : k.val < (schemeNodes T).length := by
      simpa only [hintSpec, permSizesOf, List.length_map] using k.isLt
    have hread := hh k.val hk
    simp only [Nat.zero_add] at hread
    exact hread.1 k.isLt
  · funext k
    have hk : k.val < (schemeNodes T).length := by
      simpa only [hintSpec, coeffShapesOf, List.length_map] using k.isLt
    have hread := hh k.val hk
    simp only [Nat.zero_add] at hread
    exact hread.2 k.isLt

end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
open Finset
namespace LinearSetReconciliation327.Main
universe u v

theorem card_list_pi {α : Type u} (L : List α) (F : α → Type v) [∀ a, Fintype (F a)] :
    Fintype.card (∀ k : Fin L.length, F (L.get k)) = (L.map fun a => Fintype.card (F a)).prod := by
  rw [Fintype.card_pi, ← List.prod_ofFn]
  change (List.ofFn fun k : Fin L.length => Fintype.card (F L[k.val])).prod = _
  exact congrArg List.prod (List.ofFn_getElem_eq_map L (fun a => Fintype.card (F a)))

def seedTableCard (T : Node) : ℕ :=
  Fintype.card (Equiv.Perm (Fin T.N)) * 2 ^ (nodeCoins T).1

theorem hintSpec_seed_card (T : Node) :
    Fintype.card (hintSpec T).Seed = ((schemeNodes T).map seedTableCard).prod := by
  change Fintype.card ((∀ k : Fin (hintSpec T).permSizes.length,
    Equiv.Perm (Fin ((hintSpec T).permSizes.get k))) ×
      (∀ k : Fin (hintSpec T).coeffShapes.length,
        Fin ((hintSpec T).coeffShapes.get k).1 → Fin ((hintSpec T).coeffShapes.get k).2)) = _
  rw [Fintype.card_prod,
    card_list_pi (hintSpec T).permSizes (fun a => Equiv.Perm (Fin a)),
    card_list_pi (hintSpec T).coeffShapes (fun a : ℕ × ℕ => Fin a.1 → Fin a.2)]
  simp only [hintSpec, permSizesOf, coeffShapesOf, List.map_map]
  rw [← List.prod_map_mul]
  congr 1
  apply List.map_congr_left
  intro a ha
  simp only [Function.comp_apply, Fintype.card_fun, Fintype.card_fin, seedTableCard, nodeCoins]

theorem hintLocal_seed_card (P : HintParams) (N X Y : ℕ) :
    Fintype.card (P.scheme N X Y).LocalSeed =
      Fintype.card (Equiv.Perm (Fin N)) * 2 ^ (P.rows X Y * P.ell N X Y * P.Nmax N X Y) := by
  change Fintype.card (Equiv.Perm (Fin N) × (Fin (P.rows X Y) → Fin (P.ell N X Y) → Fin (P.Nmax N X Y) → ZMod 2)) = _
  simp only [Fintype.card_prod, NodeCoins, Fintype.card_fun, Fintype.card_fin, ZMod.card, ← pow_mul]
  congr 1
  congr 1
  ring

theorem seed_card_product (P : HintParams) (T : Node) (hT : IsSchemeTree P T) :
    Fintype.card T.Seed = ((schemeNodes T).map seedTableCard).prod := by
  induction hT with
  | store N => change Fintype.card Unit = ([] : List ℕ).prod; simp
  | cr N t => change Fintype.card Unit = ([] : List ℕ).prod; simp
  | direct N X Y t =>
      rw [schemeNodes, List.map_singleton, List.prod_singleton]
      change Fintype.card (P.scheme N X Y).LocalSeed =
        Fintype.card (Equiv.Perm (Fin N)) * 2 ^ (P.rows X Y * P.ell N X Y * P.Nmax N X Y)
      exact hintLocal_seed_card P N X Y
  | recursive N X Y t Xs Ys child hchild ih =>
      have hc : Fintype.card (Node.Seed (.recursive (P.scheme N X Y) t Xs Ys child)) =
          Fintype.card (P.scheme N X Y).LocalSeed * ∏ s, Fintype.card (child s).Seed := by
        change Fintype.card ((P.scheme N X Y).LocalSeed × ∀ s, (child s).Seed) = _
        rw [Fintype.card_prod, Fintype.card_pi]
      rw [hc, schemeNodes_recursive, List.map_append, List.prod_append,
        List.map_singleton, List.prod_singleton]
      have hw : seedTableCard (.recursive (P.scheme N X Y) t Xs Ys child) =
          Fintype.card (P.scheme N X Y).LocalSeed := by
        change Fintype.card (Equiv.Perm (Fin N)) * 2 ^ (P.rows X Y * P.ell N X Y * P.Nmax N X Y) = _
        exact (hintLocal_seed_card P N X Y).symm
      rw [hw]
      congr 1
      rw [List.map_flatten, List.prod_flatten, List.map_map]
      rw [List.map_ofFn, List.prod_ofFn]
      exact Finset.prod_congr rfl (fun s _ => ih s)

theorem hintKappa_bijective (P : HintParams) (T : Node) (hT : IsSchemeTree P T) :
    Function.Bijective (hintKappa P T hT) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨hintKappa_injective P T hT, (hintSpec_seed_card T).trans (seed_card_product P T hT).symm⟩

/-- Exact probability transport through the implemented seed splitter. -/
theorem prU_hintKappa (P : HintParams) (T : Node) (hT : IsSchemeTree P T) (f : T.Seed → Prop) :
    prU (fun r : (hintSpec T).Seed => f (hintKappa P T hT r)) = prU f := by
  classical
  let e := Equiv.ofBijective (hintKappa P T hT) (hintKappa_bijective P T hT)
  have hefun : ∀ a, e a = hintKappa P T hT a := fun _ => rfl
  have hc : (Finset.univ.filter (fun r => f (hintKappa P T hT r))).card = (Finset.univ.filter f).card := by
    apply Finset.card_bij (fun a _ => e a)
    · intro a ha
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hefun] using ha
    · intro a ha b hb he
      exact e.injective he
    · intro b hb
      refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
      have hmap : hintKappa P T hT (e.symm b) = b := (hefun _).symm.trans (e.apply_symm_apply b)
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hmap] using hb
  unfold prU
  rw [hc, Fintype.card_congr e]

end LinearSetReconciliation327.Main
end

#print axioms LinearSetReconciliation327.Main.prU_hintKappa
end -- Def_LinearSetReconciliation327_Main_HintSeedDistribution20261120

section -- Def_LinearSetReconciliation327_Main_HintBoundsBudget20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main.HintBoundsBudget
open Finset

lemma c8_lg_le_two_pow_ceil {n : ℕ} (hn : 2 ≤ n) :
    lg (n : ℝ) ≤ (2 : ℝ) ^ (⌈lg (lg ((n : ℝ) + 2))⌉₊) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have h1 : lg (n : ℝ) ≤ lg ((n : ℝ) + 2) :=
    Real.logb_le_logb_of_le (by norm_num) hn0 (by linarith)
  have hpos : (0 : ℝ) < lg ((n : ℝ) + 2) := by
    have h2 : (2 : ℕ) ≤ n + 2 := by omega
    have h3 := one_le_lg h2
    have h4 : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    rw [h4] at h3
    linarith
  have h3 : lg ((n : ℝ) + 2) = (2 : ℝ) ^ (lg (lg ((n : ℝ) + 2))) := (Real.rpow_logb
    (b := 2) (x := lg ((n : ℝ) + 2)) (by norm_num) (by norm_num) hpos).symm
  have h4 : (2 : ℝ) ^ (lg (lg ((n : ℝ) + 2)))
      ≤ (2 : ℝ) ^ ((⌈lg (lg ((n : ℝ) + 2))⌉₊ : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  rw [Real.rpow_natCast] at h4
  linarith only [h1, h3, h4]
private theorem c8_nodeArgs_child {P : HintParams} {N X Y : ℕ} (h : P.NodeArgs N X Y)
    (hr : P.rule N X Y = .recursive) (s : Fin (P.scheme N X Y).ℓ) :
    P.NodeArgs Y (P.capX N X Y s.val) (P.capY N X Y s.val) := by
  obtain ⟨hn, hlam, _, hNn, _, hYN⟩ := h
  have hRec := rule_recursive_spec hr
  have hY := one_le_Y_of_recursive (one_le_lg hn) hRec.1 hRec.2.2
  exact ⟨hn, hlam, hY, hYN.trans hNn, min_le_left _ _, min_le_left _ _⟩

theorem c8_boundsProb_tree {δ : ℝ} {P : HintParams}
    (hZ : ∀ (N X Y : ℕ), P.NodeArgs N X Y → P.NonLeaf N X Y →
      ∀ x J : Finset ℕ, Node.Valid N X Y x J →
        prU (fun lr : (P.scheme N X Y).LocalSeed =>
          P.resid N X Y < (P.scheme N X Y).Z lr x J) ≤ δ)
    (hUV : ∀ (N X Y : ℕ), P.NodeArgs N X Y → P.rule N X Y = .recursive →
      ∀ x J : Finset ℕ, Node.Valid N X Y x J → ∀ s : Fin (P.scheme N X Y).ℓ,
        prU (fun lr : (P.scheme N X Y).LocalSeed =>
          P.capX N X Y s.val < (P.scheme N X Y).U lr x J s) ≤ δ ∧
        prU (fun lr : (P.scheme N X Y).LocalSeed =>
          P.capY N X Y s.val < (P.scheme N X Y).V lr x J s) ≤ δ) :
    ∀ (fuel N X Y : ℕ) (T : Node), P.tree fuel N X Y = some T → P.NodeArgs N X Y →
      Node.BoundsProb δ T X Y := by
  intro fuel
  induction fuel with
  | zero =>
      intro N X Y T h _
      simp only [HintParams.tree] at h
      exact absurd h (by simp)
  | succ f ih =>
      intro N X Y T h hargs
      simp only [HintParams.tree] at h
      cases hr : P.rule N X Y
      ·
        simp only [hr] at h
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using h.symm
        subst hT
        trivial
      ·
        simp only [hr] at h
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using h.symm
        subst hT
        trivial
      ·
        simp only [hr] at h
        have hex : ∃ child : Fin (P.ell N X Y) → Node,
            HintParams.allSome (fun s : Fin (P.ell N X Y) =>
              P.tree f Y (P.capX N X Y s.val) (P.capY N X Y s.val)) = some child ∧
            (fun child : Fin (P.ell N X Y) → Node =>
              Node.recursive (P.scheme N X Y) (P.resid N X Y)
                (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) child) child = T :=
          Option.map_eq_some_iff.mp h
        obtain ⟨child, hsome, hT⟩ := hex
        rw [← hT]
        refine ⟨?_, ?_⟩
        · intro x J hV
          exact ⟨hZ N X Y hargs (Or.inl hr) x J hV,
            fun s => ⟨(hUV N X Y hargs hr x J hV s).1, (hUV N X Y hargs hr x J hV s).2⟩⟩
        · intro s
          exact ih Y (P.capX N X Y s.val) (P.capY N X Y s.val) (child s)
            (allSome_spec _ _ hsome s) (c8_nodeArgs_child hargs hr s)
      ·
        simp only [hr] at h
        have hT : T = .direct (P.scheme N X Y) (P.resid N X Y) := by simpa using h.symm
        subst hT
        exact hZ N X Y hargs (Or.inr hr)


theorem c8_boundCount_add_two_le (T : Node) : T.boundCount + 2 ≤ 3 * T.nodeCount := by
  induction T with
  | store N => simp [Node.boundCount, Node.nodeCount]
  | cr N t => simp [Node.boundCount, Node.nodeCount]
  | direct sch t => simp [Node.boundCount, Node.nodeCount]
  | recursive sch t Xs Ys child ih =>
      have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin sch.ℓ))) (fun s _ => ih s)
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum] at hs
      simp only [Node.boundCount, Node.nodeCount]
      omega

theorem c8_boundCount_le_three (T : Node) : T.boundCount ≤ 3 * T.nodeCount :=
  le_trans (Nat.le_add_right T.boundCount 2) (c8_boundCount_add_two_le T)

/-- A flat union budget for the whole tree. K and A are the hidden
node-count constants; C has already been chosen before the input parameters. -/
theorem c8_flat_budget (T : Node) (K L : ℝ) (A B C q lam : ℕ)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hKpow : K ≤ (2 : ℝ) ^ B)
    (hC : B + 3 * A ≤ C) (hC27 : 27 ≤ C)
    (hLpow : L ≤ (2 : ℝ) ^ q)
    (hnc : (T.nodeCount : ℝ) ≤ K * (A : ℝ) * L ^ 27) :
    (T.boundCount : ℝ) * ((2 : ℝ) ^ (lam + C * q + C))⁻¹ ≤ ((2 : ℝ) ^ lam)⁻¹ := by
  have hA : (3 * A : ℝ) ≤ (2 : ℝ) ^ (3 * A) := by
    exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n := 3 * A)))
  have hc : 3 * K * (A : ℝ) ≤ (2 : ℝ) ^ C := by
    calc
      3 * K * (A : ℝ) = K * (3 * A : ℝ) := by ring
      _ ≤ (2 : ℝ) ^ B * (2 : ℝ) ^ (3 * A) := mul_le_mul hKpow hA (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (B + 3 * A) := (pow_add _ _ _).symm
      _ ≤ (2 : ℝ) ^ C := pow_le_pow_right₀ (by norm_num) hC
  have hl : L ^ 27 ≤ (2 : ℝ) ^ (C * q) := by
    calc
      L ^ 27 ≤ ((2 : ℝ) ^ q) ^ 27 := pow_le_pow_left₀ hL hLpow _
      _ = (2 : ℝ) ^ (27 * q) := by rw [← pow_mul, Nat.mul_comm q 27]
      _ ≤ (2 : ℝ) ^ (C * q) := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right q hC27)
  have hb : (T.boundCount : ℝ) ≤ (2 : ℝ) ^ (C * q + C) := by
    have ht : (T.boundCount : ℝ) ≤ 3 * (T.nodeCount : ℝ) := by
      exact_mod_cast c8_boundCount_le_three T
    calc
      (T.boundCount : ℝ) ≤ 3 * (K * (A : ℝ) * L ^ 27) :=
        ht.trans (mul_le_mul_of_nonneg_left hnc (by norm_num))
      _ = (3 * K * (A : ℝ)) * L ^ 27 := by ring
      _ ≤ (2 : ℝ) ^ C * (2 : ℝ) ^ (C * q) := mul_le_mul hc hl (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (C * q + C) := by rw [← pow_add, Nat.add_comm C]
  have hmul : (T.boundCount : ℝ) * (2 : ℝ) ^ lam ≤ (2 : ℝ) ^ (lam + C * q + C) := by
    have hh := mul_le_mul_of_nonneg_right hb (show (0 : ℝ) ≤ 2 ^ lam by positivity)
    calc
      (T.boundCount : ℝ) * (2 : ℝ) ^ lam ≤ (2 : ℝ) ^ (C * q + C) * (2 : ℝ) ^ lam := hh
      _ = (2 : ℝ) ^ (lam + C * q + C) := by rw [← pow_add]; congr 1 <;> omega
  rw [← div_eq_mul_inv, ← one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa only [one_mul] using hmul

theorem hintPublicAllBounds (P : HintParams) (T : Node) (hT : IsSchemeTree P T)
    (X Y : ℕ) (K : ℝ) (B : ℕ)
    (hn : 2 ≤ P.n) (hK : 0 ≤ K) (hKB : K ≤ (2 : ℝ) ^ B)
    (hC : B + 3 * P.A ≤ P.C) (h27 : 27 ≤ P.C)
    (hCount : (T.nodeCount : ℝ) ≤ K * (P.A : ℝ) * P.lgn ^ 27)
    (hWF : Node.WF T X Y) (hProb : T.BoundsProb ((2 : ℝ) ^ P.lamStar)⁻¹ X Y)
    (x J : Finset ℕ) (hValid : Node.Valid T.N X Y x J) :
    prU (fun r : (hintSpec T).Seed => ¬ T.AllBounds (hintKappa P T hT r) x J) ≤ ((2 : ℝ) ^ P.lam)⁻¹ := by
  rw [prU_hintKappa P T hT (fun r => ¬ T.AllBounds r x J)]
  exact (HintBoundsProof.allBounds_prob T X Y _ hWF hProb x J hValid).trans
    (c8_flat_budget T K P.lgn P.A B P.C ⌈lg (lg ((P.n : ℝ) + 2))⌉₊ P.lam
      hK (le_trans (by norm_num) (one_le_lg hn)) hKB hC h27 (c8_lg_le_two_pow_ceil hn) hCount)

end LinearSetReconciliation327.Main.HintBoundsBudget
#print axioms LinearSetReconciliation327.Main.HintBoundsBudget.c8_boundsProb_tree
#print axioms LinearSetReconciliation327.Main.HintBoundsBudget.hintPublicAllBounds
end -- Def_LinearSetReconciliation327_Main_HintBoundsBudget20261120


