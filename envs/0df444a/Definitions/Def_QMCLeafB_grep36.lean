-- Prove2me | Definitions.Def_QMCLeafB_grep36
-- name    : QMCLeafB_grep36
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:19:41.329194+00:00
-- url     : https://prove2.me/theorems/008a524e-cebf-4bd4-a9d4-6f2a95aa6b09
-- title:
--   QMCLeafB grep36
-- statement:
--   # `Check_grep36_m5` — phase 36, member m5, direction d2 (`gate-repair-program`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_bh35
import Definitions.Def_QMCLeafB_hokupper34
import Definitions.Def_QMCLeafB_htop_oklower_m7
import Definitions.Def_QMCLeafB_htop_finish_m7
import Definitions.Def_QMCLeafB_ledgerG_m3
import Definitions.Def_QMCLeafB_capguard_m3
import Definitions.Def_QMCLeafB_stateDiag
import Definitions.Def_QMCLeafB_pivexact
import Definitions.Def_QMCLeafB_finalization
import Definitions.Def_QMCLeafB_RStInit
import Definitions.Def_QMCLeafB_LoopRestate
import Definitions.Def_QMCLeafB_pbit33
import Definitions.Def_QMCLeafB_runparams_shallow_m5
import Definitions.Def_QMCLeafB_conformance_m8
/-
# `Check_grep36_m5` — phase 36, member m5, direction d2 (`gate-repair-program`)

**The repaired programme, concretely: the ok test is membership, at the engine's own registers.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section
open scoped BigOperators
open Matrix

namespace QMCLeafB.Grep36M5

open QuantumMaxCutEnergy
open QMCLeafB.RoundProgram
open QMCLeafB.OkLower
open QMCLeafB.BH35M5
open QMCLeafB.StateDiag
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

/-! ## 1.  The gate at the state -/

/-- **The repaired test at the engine's registers.** -/
def StateGateAt (n : ℕ) (s : RSt) : Prop :=
  TopGate (stMat n (stA s)) (stT s - QMCLeafB.RoundT.epsOf s) (dqOf s) (stMat n (stX s))

theorem topPinch_symm {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} {δ : ℚ}
    (hsym : ∀ i j, Q i j = Q j i) : (topPinch Q δ)ᵀ = topPinch Q δ := by
  funext i j
  rw [Matrix.transpose_apply]
  by_cases h : i = j
  · subst h; rfl
  · rw [topPinch_off h, topPinch_off (Ne.symm h)]
    exact hsym j i

#print axioms QMCLeafB.Grep36M5.topPinch_symm

/-- **SOUNDNESS AT THE STATE.** -/
theorem mem_of_StateGateAt {n : ℕ} {s : RSt}
    (hA : ∀ i, stMat n (stA s) i i = 0)
    (hsym : ∀ i j, stMat n (stX s) i j = stMat n (stX s) j i)
    (h : StateGateAt n s) :
    ∃ cX : Matrix (Fin n) (Fin n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (stMat n (stA s)) cX
        (stT s - QMCLeafB.RoundT.epsOf s) (dqOf s) :=
  ⟨topPinch (stMat n (stX s)) (dqOf s), topPinch_symm hsym, mem_of_topGate hA h⟩

#print axioms QMCLeafB.Grep36M5.mem_of_StateGateAt

/-- **COMPLETENESS AT THE STATE.** -/
theorem StateGateAt_of_mem {n : ℕ} {s : RSt}
    (h : QMCLeafB.RelaxOracle.RelaxMem (stMat n (stA s)) (stMat n (stX s))
      (stT s - QMCLeafB.RoundT.epsOf s) (dqOf s)) :
    StateGateAt n s :=
  topGate_of_mem h

#print axioms QMCLeafB.Grep36M5.StateGateAt_of_mem

/-! ## 2.  The ok test as a boolean -/

/-- The per-coordinate diagonal gate as a list test: the indices whose deviation exceeds `δ/4`. -/
def diagBadSt (s : RSt) : List ℕ :=
  (idxs (stN s, stX s)).filter
    (fun i => decide (dqOf s / 4 < absq (entV (stN s, stX s) i i - 1)))

/-- **The per-coordinate diagonal gate**, as a `Bool`. -/
def perCoordGate (s : RSt) : Bool := (diagBadSt s).isEmpty

theorem poly_idxsState : Poly (fun s : RSt => idxs (stN s, stX s)) :=
  Poly.comp (f := fun p : ℕ × List ℚ => idxs p) (g := fun s : RSt => (stN s, stX s))
    QMCLeafB.RoundProgram.poly_idxs
    (Poly.pair (f := fun s : RSt => stN s) (g := fun s : RSt => stX s) poly_stN poly_stX)

#print axioms QMCLeafB.Grep36M5.poly_idxsState

theorem poly_stN_fst : Poly (fun x : RSt × ℕ => stN x.1) :=
  Poly.comp (f := stN) (g := (Prod.fst : RSt × ℕ → RSt)) poly_stN Poly.fst

theorem poly_stX_fst : Poly (fun x : RSt × ℕ => stX x.1) :=
  Poly.comp (f := stX) (g := (Prod.fst : RSt × ℕ → RSt)) poly_stX Poly.fst

theorem poly_dqOf_fst : Poly (fun x : RSt × ℕ => dqOf x.1) :=
  Poly.comp (f := dqOf) (g := (Prod.fst : RSt × ℕ → RSt)) poly_dqOf Poly.fst

theorem poly_diagEntry : Poly (fun x : RSt × ℕ => entV (stN x.1, stX x.1) x.2 x.2) :=
  Poly.comp (f := fun z : (ℕ × List ℚ) × ℕ => entV z.1 z.2 z.2)
    (g := fun x : RSt × ℕ => ((stN x.1, stX x.1), x.2))
    QMCLeafB.RoundProgram.poly_entV2
    (Poly.pair (f := fun x : RSt × ℕ => (stN x.1, stX x.1)) (g := fun x : RSt × ℕ => x.2)
      (Poly.pair (f := fun x : RSt × ℕ => stN x.1) (g := fun x : RSt × ℕ => stX x.1)
        poly_stN_fst poly_stX_fst)
      Poly.snd)

#print axioms QMCLeafB.Grep36M5.poly_diagEntry

theorem poly_absDev : Poly (fun x : RSt × ℕ => absq (entV (stN x.1, stX x.1) x.2 x.2 - 1)) := by
  have h1 : Poly (fun x : RSt × ℕ => entV (stN x.1, stX x.1) x.2 x.2 - 1) :=
    Poly.comp (f := fun q : ℚ × ℚ => q.1 - q.2)
      (g := fun x : RSt × ℕ => (entV (stN x.1, stX x.1) x.2 x.2, (1 : ℚ)))
      Poly.rat_sub
      (Poly.pair (f := fun x : RSt × ℕ => entV (stN x.1, stX x.1) x.2 x.2)
        (g := fun x : RSt × ℕ => (1 : ℚ)) poly_diagEntry (Automatic.Poly.const 1))
  exact Poly.comp (f := absq) (g := fun x : RSt × ℕ => entV (stN x.1, stX x.1) x.2 x.2 - 1)
    QMCLeafB.RoundProgram.poly_absq h1

#print axioms QMCLeafB.Grep36M5.poly_absDev

theorem poly_diagBadEntry :
    Poly (fun x : RSt × ℕ => decide (dqOf x.1 / 4 < absq (entV (stN x.1, stX x.1) x.2 x.2 - 1))) := by
  have hq : Poly (fun x : RSt × ℕ => dqOf x.1 / 4) :=
    Poly.comp (f := fun q : ℚ × ℚ => q.1 / q.2)
      (g := fun x : RSt × ℕ => (dqOf x.1, (4 : ℚ)))
      Poly.rat_div
      (Poly.pair (f := fun x : RSt × ℕ => dqOf x.1) (g := fun x : RSt × ℕ => (4 : ℚ))
        poly_dqOf_fst (Automatic.Poly.const 4))
  exact Poly.rat_lt_comp hq poly_absDev

#print axioms QMCLeafB.Grep36M5.poly_diagBadEntry

theorem poly_diagBadSt : Poly diagBadSt := by
  unfold diagBadSt
  exact Poly.list_filter (f := fun (s : RSt) (i : ℕ) =>
      decide (dqOf s / 4 < absq (entV (stN s, stX s) i i - 1)))
    poly_diagBadEntry poly_idxsState

#print axioms QMCLeafB.Grep36M5.poly_diagBadSt

theorem poly_perCoordGate : Poly perCoordGate :=
  Poly.comp (f := (List.isEmpty : List ℕ → Bool)) (g := diagBadSt)
    (Poly.list_empty (α := ℕ)) poly_diagBadSt

#print axioms QMCLeafB.Grep36M5.poly_perCoordGate

/-- What the per-coordinate gate certifies, elementwise. -/
theorem perCoordGate_spec {s : RSt} (h : perCoordGate s = true) :
    ∀ i ∈ idxs (stN s, stX s), absq (entV (stN s, stX s) i i - 1) ≤ dqOf s / 4 := by
  intro i hi
  have hempty : diagBadSt s = [] := by
    have h1 : diagBadSt s = [] := by simpa [perCoordGate] using h
    exact h1
  have hnot : ¬ (dqOf s / 4 < absq (entV (stN s, stX s) i i - 1)) := by
    intro hlt
    have hmem : i ∈ diagBadSt s := by
      unfold diagBadSt
      exact List.mem_filter.mpr ⟨hi, by simpa using hlt⟩
    rw [hempty] at hmem
    exact List.not_mem_nil hmem
  have hle : absq (entV (stN s, stX s) i i - 1) ≤ dqOf s / 4 := le_of_not_gt hnot
  rw [absq_eq] at hle ⊢
  exact hle

#print axioms QMCLeafB.Grep36M5.perCoordGate_spec

/-- **The per-coordinate gate at the matrix**, at the state's own dimension. -/
theorem perCoordGate_diagSt {s : RSt} (hlen : stN s ≤ (stX s).length)
    (h : perCoordGate s = true) (i : Fin (stN s)) :
    |stMat (stN s) (stX s) i i - 1| ≤ dqOf s / 4 := by
  have hspec := perCoordGate_spec h i.1 ?_
  · rw [absq_eq] at hspec
    rwa [stMat_apply]
  · rw [idxs_of_le hlen]
    exact List.mem_range.mpr i.isLt

#print axioms QMCLeafB.Grep36M5.perCoordGate_diagSt

/-- **The per-coordinate gate at the matrix**, transported to the input's dimension. -/
theorem perCoordGate_diag {n : ℕ} {s : RSt} (hN : stN s = n) (hlen : n ≤ (stX s).length)
    (h : perCoordGate s = true) (i : Fin n) :
    |stMat n (stX s) i i - 1| ≤ dqOf s / 4 := by
  cases hN
  exact perCoordGate_diagSt hlen h i

#print axioms QMCLeafB.Grep36M5.perCoordGate_diag

/-- **The programme's ok test.** -/
def okTopB (psdC : RSt → Bool) (s : RSt) : Bool :=
  decide (0 < dqOf s) && (perCoordGate s && (psdC s && decide (fvR s ≤ levelOf s)))

theorem poly_okTopB {psdC : RSt → Bool} (h : Poly psdC) : Poly (okTopB psdC) := by
  have hpos : Poly (fun s : RSt => decide (0 < dqOf s)) :=
    Poly.rat_lt_comp (Automatic.Poly.const (0 : ℚ)) poly_dqOf
  have hlev : Poly (fun s : RSt => decide (fvR s ≤ levelOf s)) :=
    Poly.rat_le_comp poly_fvR poly_levelOf
  have hand : Poly (fun z : Bool × Bool => z.1 && z.2) := Poly.bool_and
  have hinner : Poly (fun s : RSt => perCoordGate s && (psdC s && decide (fvR s ≤ levelOf s))) :=
    Poly.comp (f := fun z : Bool × Bool => z.1 && z.2)
      (g := fun s : RSt => (perCoordGate s, psdC s && decide (fvR s ≤ levelOf s))) hand
      (Poly.pair (f := fun s : RSt => perCoordGate s)
        (g := fun s : RSt => psdC s && decide (fvR s ≤ levelOf s)) poly_perCoordGate
        (Poly.comp (f := fun z : Bool × Bool => z.1 && z.2)
          (g := fun s : RSt => (psdC s, decide (fvR s ≤ levelOf s))) hand
          (Poly.pair (f := psdC) (g := fun s : RSt => decide (fvR s ≤ levelOf s)) h hlev)))
  exact Poly.comp (f := fun z : Bool × Bool => z.1 && z.2)
    (g := fun s : RSt =>
      (decide (0 < dqOf s), perCoordGate s && (psdC s && decide (fvR s ≤ levelOf s)))) hand
    (Poly.pair (f := fun s : RSt => decide (0 < dqOf s))
      (g := fun s : RSt => perCoordGate s && (psdC s && decide (fvR s ≤ levelOf s))) hpos hinner)

#print axioms QMCLeafB.Grep36M5.poly_okTopB

/-- What the test reports. -/
theorem okTopB_spec {psdC : RSt → Bool} {s : RSt} (h : okTopB psdC s = true) :
    0 < dqOf s ∧ perCoordGate s = true ∧ psdC s = true ∧ fvR s ≤ levelOf s := by
  unfold okTopB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

#print axioms QMCLeafB.Grep36M5.okTopB_spec

/-- The exact-pivot certificate: the descent's own answer is `false`. -/
def pivOk (s : RSt) : Bool := !((pivAns s).1)

theorem poly_pivOk : Poly pivOk :=
  Poly.comp (f := Bool.not) (g := fun s : RSt => (pivAns s).1) Poly.bool_not
    (Poly.comp (f := Prod.fst) (g := pivAns) Poly.fst QMCLeafB.RoundProgram.poly_pivAns)

#print axioms QMCLeafB.Grep36M5.poly_pivOk

theorem pivOk_eq_true {s : RSt} (h : pivOk s = true) : (pivAns s).1 = false := by
  unfold pivOk at h
  simpa using h

#print axioms QMCLeafB.Grep36M5.pivOk_eq_true

/-- **THE CAMPAIGN PROGRAMME'S `ok` TEST** — no hypotheses anywhere. -/
def programGate (s : RSt) : Bool := okTopB pivOk s

theorem poly_programGate : Poly programGate := poly_okTopB poly_pivOk

#print axioms QMCLeafB.Grep36M5.poly_programGate

theorem programGate_spec {s : RSt} (h : programGate s = true) :
    0 < dqOf s ∧ perCoordGate s = true ∧ pivOk s = true ∧ fvR s ≤ levelOf s :=
  okTopB_spec h

#print axioms QMCLeafB.Grep36M5.programGate_spec

/-! ## 3.  The round, its `Poly`, and the registers -/

/-- **The cut branch**: the engine's own trace cut — normal `stA s`, the GLS/snap update `snapY` on
`X`, flag `false`.  (`RoundProgram.threshB`'s above-level branch is exactly this normal, so the
branch is the engine's, not a device.) -/
def roundCutT (s : RSt) : RSt :=
  mkSt (stN s) (stA s) (snapY s) (stT s) (stMu s) (stD s) (stOks s ++ [false]) (stA s)

/-- **The stall branch**: the state is frozen and the round is recorded as a cut.  Only reachable when
the code is not normalised (`|X| ≠ n²`), exactly the case `roundGT` sends to `roundOk`; here it must
report `false`, because `true` is reserved for the gate. -/
def stallT (s : RSt) : RSt :=
  mkSt (stN s) (stA s) (stX s) (stT s) (stMu s) (stD s) (stOks s ++ [false]) (stRec s)

/-- **THE REPAIRED ROUND**: freeze and report `ok` iff the membership test fires; otherwise take the
engine's trace cut and report `false` (and stall on an unnormalised code, which cannot occur on the
campaign orbit).  The flag stream is therefore exactly the gate's values along the orbit (§5), which
is what a `true` bit has to mean. -/
def roundTop (s : RSt) : RSt :=
  if programGate s then roundOk s
  else if (stX s).length = stN s * stN s then roundCutT s else stallT s

theorem poly_roundCutT : Poly roundCutT := by
  have hoks : Poly (fun s : RSt => stOks s ++ ([false] : List Bool)) :=
    Poly.comp (f := fun z : List Bool × List Bool => z.1 ++ z.2)
      (g := fun s : RSt => (stOks s, ([false] : List Bool)))
      (Poly.list_append (α := Bool))
      (Poly.pair (f := fun s : RSt => stOks s) (g := fun s : RSt => ([false] : List Bool))
        poly_stOks (Automatic.Poly.const [false]))
  exact poly_mkSt_c poly_stN poly_stA poly_snapY poly_stT poly_stMu poly_stD hoks poly_stA

#print axioms QMCLeafB.Grep36M5.poly_roundCutT

/-- `Poly` of the stall branch. -/
theorem poly_stallT : Poly stallT := by
  have hoks : Poly (fun s : RSt => stOks s ++ ([false] : List Bool)) :=
    Poly.comp (f := fun z : List Bool × List Bool => z.1 ++ z.2)
      (g := fun s : RSt => (stOks s, ([false] : List Bool)))
      (Poly.list_append (α := Bool))
      (Poly.pair (f := fun s : RSt => stOks s) (g := fun s : RSt => ([false] : List Bool))
        poly_stOks (Automatic.Poly.const [false]))
  exact poly_mkSt_c poly_stN poly_stA poly_stX poly_stT poly_stMu poly_stD hoks poly_stRec

#print axioms QMCLeafB.Grep36M5.poly_stallT

theorem poly_isNormalised : Poly (fun s : RSt => decide ((stX s).length = stN s * stN s)) :=
  Poly.nat_eq_comp
    (Poly.comp (f := List.length) (g := stX) (Poly.list_length (α := ℚ)) poly_stX)
    (Poly.comp (f := fun z : ℕ × ℕ => z.1 * z.2)
      (g := fun s : RSt => (stN s, stN s)) Poly.nat_mul
      (Poly.pair (f := fun s : RSt => stN s) (g := fun s : RSt => stN s) poly_stN poly_stN))

#print axioms QMCLeafB.Grep36M5.poly_isNormalised

theorem poly_roundTop : Poly roundTop := by
  unfold roundTop
  exact Poly.ite (p := programGate) poly_programGate poly_roundOk
    (Poly.ite_prop (p := fun s : RSt => (stX s).length = stN s * stN s) poly_isNormalised
      poly_roundCutT poly_stallT)

#print axioms QMCLeafB.Grep36M5.poly_roundTop

/-! ### 3.1  The state registers are frozen -/

theorem stN_roundCutT (s : RSt) : stN (roundCutT s) = stN s := rfl
theorem stA_roundCutT (s : RSt) : stA (roundCutT s) = stA s := rfl
theorem stX_roundCutT (s : RSt) : stX (roundCutT s) = snapY s := rfl
theorem stT_roundCutT (s : RSt) : stT (roundCutT s) = stT s := rfl
theorem stMu_roundCutT (s : RSt) : stMu (roundCutT s) = stMu s := rfl
theorem stD_roundCutT (s : RSt) : stD (roundCutT s) = stD s := rfl
theorem stOks_roundCutT (s : RSt) : stOks (roundCutT s) = stOks s ++ [false] := rfl
theorem stRec_roundCutT (s : RSt) : stRec (roundCutT s) = stA s := rfl

theorem stN_stallT (s : RSt) : stN (stallT s) = stN s := rfl
theorem stA_stallT (s : RSt) : stA (stallT s) = stA s := rfl
theorem stX_stallT (s : RSt) : stX (stallT s) = stX s := rfl
theorem stT_stallT (s : RSt) : stT (stallT s) = stT s := rfl
theorem stMu_stallT (s : RSt) : stMu (stallT s) = stMu s := rfl
theorem stD_stallT (s : RSt) : stD (stallT s) = stD s := rfl
theorem stOks_stallT (s : RSt) : stOks (stallT s) = stOks s ++ [false] := rfl
theorem stRec_stallT (s : RSt) : stRec (stallT s) = stRec s := rfl

theorem stN_roundTop (s : RSt) : stN (roundTop s) = stN s := by
  unfold roundTop
  split_ifs <;> rfl

theorem stA_roundTop (s : RSt) : stA (roundTop s) = stA s := by
  unfold roundTop
  split_ifs <;> rfl

theorem stT_roundTop (s : RSt) : stT (roundTop s) = stT s := by
  unfold roundTop
  split_ifs <;> rfl

theorem stMu_roundTop (s : RSt) : stMu (roundTop s) = stMu s := by
  unfold roundTop
  split_ifs <;> rfl

theorem stD_roundTop (s : RSt) : stD (roundTop s) = stD s := by
  unfold roundTop
  split_ifs <;> rfl

/-- The flag the round appends is exactly the gate's value. -/
theorem stOks_roundTop (s : RSt) : stOks (roundTop s) = stOks s ++ [programGate s] := by
  unfold roundTop
  by_cases hg : programGate s = true
  · rw [if_pos hg]
    show stOks s ++ [true] = stOks s ++ [programGate s]
    rw [hg]
  · have hf : programGate s = false := by
      cases hp : programGate s
      · rfl
      · exact absurd hp hg
    rw [if_neg hg, hf]
    by_cases hn : (stX s).length = stN s * stN s
    · rw [if_pos hn]; rfl
    · rw [if_neg hn]; rfl

#print axioms QMCLeafB.Grep36M5.stOks_roundTop

theorem stN_roundOk' (s : RSt) : stN (roundOk s) = stN s := rfl
theorem stA_roundOk' (s : RSt) : stA (roundOk s) = stA s := rfl
theorem stT_roundOk' (s : RSt) : stT (roundOk s) = stT s := rfl

/-! ### 3.2  `dqOf` and `levelOf` are orbit invariants -/

theorem massV_congr {s s' : RSt} (h : stA s = stA s') :
    QMCLeafB.RoundT.massV s = QMCLeafB.RoundT.massV s' := by
  unfold QMCLeafB.RoundT.massV
  rw [h]

#print axioms QMCLeafB.Grep36M5.massV_congr

theorem epsOf_congr' {s s' : RSt} (h : stA s = stA s') :
    QMCLeafB.RoundT.epsOf s = QMCLeafB.RoundT.epsOf s' :=
  QMCLeafB.HtopFinish.epsOf_congr h

theorem dqOf_congr {s s' : RSt} (h : stA s = stA s') : dqOf s = dqOf s' := by
  unfold dqOf
  rw [massV_congr h, epsOf_congr' h]

#print axioms QMCLeafB.Grep36M5.dqOf_congr

theorem levelOf_congr {s s' : RSt} (hA : stA s = stA s') (hT : stT s = stT s') :
    levelOf s = levelOf s' := by
  unfold levelOf
  rw [epsOf_congr' hA, hT, dqOf_congr hA]

#print axioms QMCLeafB.Grep36M5.levelOf_congr

theorem stA_iterateTop (s : RSt) (k : ℕ) : stA (roundTop^[k] s) = stA s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stA_roundTop, ih]

theorem stT_iterateTop (s : RSt) (k : ℕ) : stT (roundTop^[k] s) = stT s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stT_roundTop, ih]

#print axioms QMCLeafB.Grep36M5.stA_iterateTop

/-- **THE LEVEL AND TOLERANCE REGISTERS ARE ORBIT INVARIANTS.** -/
theorem dqOf_iterateTop (s : RSt) (k : ℕ) : dqOf (roundTop^[k] s) = dqOf s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', dqOf_congr (stA_roundTop _), ih]

#print axioms QMCLeafB.Grep36M5.dqOf_iterateTop

/-- **THE LEVEL REGISTER IS AN ORBIT INVARIANT.** -/
theorem levelOf_iterateTop (s : RSt) (k : ℕ) : levelOf (roundTop^[k] s) = levelOf s := by
  induction k with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', levelOf_congr (stA_roundTop _) (stT_roundTop _), ih]

#print axioms QMCLeafB.Grep36M5.levelOf_iterateTop

/-! ### 3.3  The registers at `init0` take the campaign's own values -/

theorem massV_init0' (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ) :
    QMCLeafB.RoundT.massV (QMCLeafB.RStInit.init0 p) = QMCLeafB.EngineRuntime.Rq p.1.1 :=
  QMCLeafB.ConformanceM8.massV_init0 p

theorem epsOf_init0' (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ) :
    QMCLeafB.RoundT.epsOf (QMCLeafB.RStInit.init0 p) = QMCLeafB.EngineRuntime.Rq p.1.1 / 40000 :=
  QMCLeafB.ConformanceM8.epsOf_init0 p

/-- At the initial state the tolerance register is the campaign's `dqShallow`. -/
theorem dqOf_init0 (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ) :
    dqOf (QMCLeafB.RStInit.init0 p) = QMCLeafB.RundataParams.dqShallowCore p.1.1 := by
  unfold dqOf QMCLeafB.RundataParams.dqShallowCore QMCLeafB.RundataCert.eps
  rw [massV_init0', epsOf_init0']

#print axioms QMCLeafB.Grep36M5.dqOf_init0

/-- At the initial state the level register is the leaf's own level `t − eps`. -/
theorem levelOf_init0 (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ) :
    QMCLeafB.RoundProgram.stT (QMCLeafB.RStInit.init0 p)
        - QMCLeafB.RoundT.epsOf (QMCLeafB.RStInit.init0 p)
      = p.2 - QMCLeafB.RundataCert.eps p.1.1 := by
  have hT : QMCLeafB.RoundProgram.stT (QMCLeafB.RStInit.init0 p) = p.2 := rfl
  rw [hT, epsOf_init0']
  unfold QMCLeafB.RundataCert.eps
  ring

#print axioms QMCLeafB.Grep36M5.levelOf_init0

/-! ## 4.  The size ledger, and the Poly bit -/

open QMCLeafB.CapGuard
open QMCLeafB.RoundSizeM6

theorem skel_roundCutT (s : RSt) : skel (roundCutT s) = skel s := by
  simp only [skel, stN_roundCutT, stA_roundCutT, stT_roundCutT, stMu_roundCutT, stD_roundCutT]

theorem Lmu_roundCutT (s : RSt) : Lmu (roundCutT s) = Lmu s := by
  simp only [Lmu, stMu_roundCutT]

theorem Ld_roundCutT (s : RSt) : Ld (roundCutT s) = Ld s := by
  simp only [Ld, stD_roundCutT]

theorem aX_roundCutT_le_capX (s : RSt) : aX (roundCutT s) ≤ capX s := by
  have hX : stX (roundCutT s) = snapY s := rfl
  simp only [aX, hX]
  have h1 : (encodeList (enc : ℚ → List Bool) (snapY s)).length
      ≤ (snapY s).length * (6 * (Lmu s + Ld s) + 21) :=
    encodeList_length_le _ _ (snapY_height s)
  have h2 : (snapY s).length ≤ stN s * stN s := snapY_length_le s
  simp only [capX]
  exact le_trans h1 (Nat.mul_le_mul_right _ h2)

#print axioms QMCLeafB.Grep36M5.aX_roundCutT_le_capX

theorem aX_roundCutT_le (s : RSt) (hn : (stX s).length = stN s * stN s) :
    aX (roundCutT s) ≤ max (aX s) (capXG s) := by
  have h := aX_roundCutT_le_capX s
  rw [capX_eq_capXG s hn] at h
  exact le_trans h (le_max_right _ _)

#print axioms QMCLeafB.Grep36M5.aX_roundCutT_le

theorem lenX_roundCutT_le (s : RSt) (hn : (stX s).length = stN s * stN s) :
    (stX (roundCutT s)).length ≤ (stX s).length := by
  have hX : stX (roundCutT s) = snapY s := rfl
  rw [hX, hn]
  exact snapY_length_le s

theorem capXG_roundCutT_le_capXG (s : RSt) (hn : (stX s).length = stN s * stN s) :
    capXG (roundCutT s) ≤ capXG s := by
  simp only [capXG, Lmu_roundCutT, Ld_roundCutT]
  exact Nat.mul_le_mul_right _ (lenX_roundCutT_le s hn)

theorem capXG_roundCutT_le (s : RSt) (hn : (stX s).length = stN s * stN s) :
    capXG (roundCutT s) ≤ max (aX s) (capXG s) :=
  le_trans (capXG_roundCutT_le_capXG s hn) (le_max_right _ _)

#print axioms QMCLeafB.Grep36M5.capXG_roundCutT_le

theorem aRec_roundCutT (s : RSt) :
    aRec (roundCutT s) = (encodeList (enc : ℚ → List Bool) (stA s)).length := by
  simp only [aRec, stRec_roundCutT]

theorem aRec_roundCutT_le (s : RSt) (H : ℕ) :
    aRec (roundCutT s) ≤ capRecG s H := by
  rw [aRec_roundCutT]
  simp only [capRecG]
  omega

#print axioms QMCLeafB.Grep36M5.aRec_roundCutT_le

theorem capRecL_roundCutT (s : RSt) (N H : ℕ) :
    capRecL (roundCutT s) N H = capRecL s N H := by
  simp only [capRecL, stA_roundCutT, Lmu_roundCutT, Ld_roundCutT]

theorem capRecG_roundCutT_le (s : RSt) (hn : (stX s).length = stN s * stN s) (H : ℕ) :
    capRecG (roundCutT s) (max (aX (roundCutT s)) (capXG (roundCutT s)))
      ≤ capRecG s (max (aX s) (capXG s)) := by
  rw [capRecG_eq_capRecL, capRecG_eq_capRecL, capRecL_roundCutT]
  refine le_trans (capRecL_mono_N s (lenX_roundCutT_le s hn)) ?_
  refine capRecL_mono_H s ?_
  exact max_le (aX_roundCutT_le s hn) (capXG_roundCutT_le s hn)

#print axioms QMCLeafB.Grep36M5.capRecG_roundCutT_le

theorem oksLen_roundCutT (s : RSt) :
    (stOks (roundCutT s)).length ≤ (stOks s).length + 1 := by
  rw [stOks_roundCutT, List.length_append]
  simp

/-- **One cut round stays inside the cap.** -/
theorem MszG_roundCutT (s : RSt) (hn : (stX s).length = stN s * stN s) :
    MszG (roundCutT s) ≤ MszG s + 6 :=
  MszG_step (le_of_eq (skel_roundCutT s)) (oksLen_roundCutT s)
    (aX_roundCutT_le s hn) (capXG_roundCutT_le s hn)
    (le_trans (aRec_roundCutT_le s _) (le_max_right _ _))
    (le_trans (capRecG_roundCutT_le s hn
      (max (aX s) (capXG s))) (le_max_right _ _))

#print axioms QMCLeafB.Grep36M5.MszG_roundCutT

theorem enc_roundCutT_le (s : RSt) (hn : (stX s).length = stN s * stN s) :
    (enc (roundCutT s)).length ≤ MszG s := by
  rw [QMCLeafB.RoundSizeM6.enc_decomp (roundCutT s), skel_roundCutT]
  have hoks : (stOks (roundCutT s)).length = (stOks s).length + 1 := by
    rw [stOks_roundCutT, List.length_append]; simp
  have hX := aX_roundCutT_le s hn
  have hR := aRec_roundCutT_le s (max (aX s) (capXG s))
  simp only [MszG] at *
  omega

#print axioms QMCLeafB.Grep36M5.enc_roundCutT_le

theorem skel_stallT (s : RSt) : skel (stallT s) = skel s := by
  simp only [skel, stN_stallT, stA_stallT, stT_stallT, stMu_stallT, stD_stallT]

theorem Lmu_stallT (s : RSt) : Lmu (stallT s) = Lmu s := by simp only [Lmu, stMu_stallT]
theorem Ld_stallT (s : RSt) : Ld (stallT s) = Ld s := by simp only [Ld, stD_stallT]

theorem aRec_stallT (s : RSt) : aRec (stallT s) = aRec s := by
  simp only [aRec, stRec_stallT]

theorem capXG_stallT (s : RSt) : capXG (stallT s) = capXG s := by
  simp only [capXG, Lmu_stallT, Ld_stallT, stX_stallT]

theorem capRecG_stallT (s : RSt) (H : ℕ) : capRecG (stallT s) H = capRecG s H := by
  simp only [capRecG, stA_stallT, stX_stallT, Lmu_stallT, Ld_stallT]

theorem MszG_stallT (s : RSt) : MszG (stallT s) = MszG s + 6 := by
  have hoks : (stOks (stallT s)).length = (stOks s).length + 1 := by
    rw [stOks_stallT, List.length_append]; simp
  simp only [MszG, skel_stallT, aX, stX_stallT, aRec_stallT, hoks, capXG_stallT,
    capRecG_stallT]
  ring

#print axioms QMCLeafB.Grep36M5.MszG_stallT

theorem enc_stallT (s : RSt) : (enc (stallT s)).length = (enc s).length + 6 := by
  have hoks : (stOks (stallT s)).length = (stOks s).length + 1 := by
    rw [stOks_stallT, List.length_append]; simp
  have haX : aX (stallT s) = aX s := by simp only [aX, stX_stallT]
  rw [QMCLeafB.RoundSizeM6.enc_decomp (stallT s), QMCLeafB.RoundSizeM6.enc_decomp s,
    skel_stallT, aRec_stallT, hoks, haX]
  ring

#print axioms QMCLeafB.Grep36M5.enc_stallT

/-! ### 4.1  The ledger at the repaired round -/

theorem MszG_roundTop (s : RSt) : MszG (roundTop s) ≤ MszG s + 6 := by
  unfold roundTop
  by_cases hg : programGate s = true
  · rw [if_pos hg]; rw [MszG_roundOk]
  · rw [if_neg hg]
    by_cases hn : (stX s).length = stN s * stN s
    · rw [if_pos hn]; exact MszG_roundCutT s hn
    · rw [if_neg hn]; exact le_of_eq (MszG_stallT s)

#print axioms QMCLeafB.Grep36M5.MszG_roundTop

theorem enc_roundTop_le (s : RSt) :
    (enc (roundTop s)).length ≤ max ((enc s).length + 6) (MszG s) := by
  unfold roundTop
  by_cases hg : programGate s = true
  · rw [if_pos hg, enc_roundOk]
    exact le_max_left _ _
  · rw [if_neg hg]
    by_cases hn : (stX s).length = stN s * stN s
    · rw [if_pos hn]
      exact le_trans (enc_roundCutT_le s hn) (le_max_right _ _)
    · rw [if_neg hn, enc_stallT]
      exact le_max_left _ _

#print axioms QMCLeafB.Grep36M5.enc_roundTop_le

/-! ### 4.2  The bit -/

/-- **THE REPAIRED PROGRAMME'S BIT**, at the campaign's own count `T33`. -/
abbrev oTop : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 roundTop
    QMCLeafB.RoundProgram.verdict (fun G _ => QMCLeafB.Pbit33.T33 G)

theorem oTop_apply (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    oTop G t = QMCLeafB.RoundProgram.verdict
      (Nat.iterate roundTop (QMCLeafB.Pbit33.T33 G)
        (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))) := rfl

theorem poly_mul_one_T {f : QMCLeafB.FuelWire.Pkg → ℕ}
    (hf : Automatic.Poly f) : Automatic.Poly (fun p => f p * 1) := by
  have h := Automatic.Poly.comp (f := fun x : ℕ × ℕ => x.1 * x.2)
    (g := fun p : QMCLeafB.FuelWire.Pkg => (f p, 1)) Automatic.Poly.nat_mul
    (Automatic.Poly.pair hf
      (Automatic.Poly.const (α := QMCLeafB.FuelWire.Pkg) (β := ℕ) 1))
  simpa using h

/-- **`hoTop` — THE POLY BIT of the repaired programme.** -/
theorem hoTop (k : ℕ) (hk : 21 ≤ 2 ^ k) :
    Automatic.Poly (fun p : QMCLeafB.FuelWire.Pkg => oTop p.1.1 p.2) := by
  have hfuel : Automatic.Poly
      (QMCLeafB.FuelWire.fuelOfProd k (fun G => QMCLeafB.Pbit33.T33 G) (fun _ => (1 : ℕ))) :=
    QMCLeafB.FuelWire.poly_fuelOfProd k _ _ (poly_mul_one_T QMCLeafB.Pbit33.poly_T33)
  have hseed : ∀ p : QMCLeafB.FuelWire.Pkg,
      (fun G => QMCLeafB.Pbit33.T33 G) p.1.1 * (fun _ => (1 : ℕ)) p.1.1
        ≤ QMCLeafB.FuelWire.seedLen p ^ (2 ^ k) :=
    fun p => by
      have h := QMCLeafB.LoopClose.Kbc4_mHalve_le_seed k hk p
      show QMCLeafB.Pbit33.T33 p.1.1 * 1 ≤ QMCLeafB.FuelWire.seedLen p ^ (2 ^ k)
      rw [QMCLeafB.Pbit33.T33_eq, Nat.mul_one]
      exact h
  have hfuelLen : ∀ p : QMCLeafB.FuelWire.Pkg,
      (QMCLeafB.FuelWire.fuelOfProd k (fun G => QMCLeafB.Pbit33.T33 G) (fun _ => (1 : ℕ)) p).length
        = QMCLeafB.Pbit33.T33 p.1.1 :=
    fun p => by
      rw [QMCLeafB.FuelWire.fuelOfProd_length k _ _ hseed p, Nat.mul_one]
  refine QMCLeafB.FinishLine.poly_of_pointwise (α := QMCLeafB.FuelWire.Pkg) (β := Bool)
    (f := fun a : QMCLeafB.FuelWire.Pkg =>
      QMCLeafB.RoundProgram.verdict
        (Nat.iterate roundTop
          (QMCLeafB.FuelWire.fuelOfProd k (fun G => QMCLeafB.Pbit33.T33 G) (fun _ => (1 : ℕ)) a).length
          (QMCLeafB.RStInit.init0 a))) ?_ ?_
  · exact QMCLeafB.LoopRestate.ho_of_loop_bounded (α := QMCLeafB.FuelWire.Pkg)
      QMCLeafB.RStInit.init0 _ roundTop QMCLeafB.RoundProgram.verdict
      QMCLeafB.RStInit.poly_init0 hfuel poly_roundTop
      QMCLeafB.RoundProgram.poly_verdict _
      (QMCLeafB.IntegrateM6.orbit_envelope roundTop QMCLeafB.CapGuard.MszG 11448595 6 6
        (by norm_num) MszG_roundTop enc_roundTop_le QMCLeafB.CapGuard.MszG_le_pow)
  · intro p
    exact QMCLeafB.FinalStroke.hspec_of_tape_free QMCLeafB.RStInit.init0 _ roundTop
      QMCLeafB.RoundProgram.verdict (fun G _ => QMCLeafB.Pbit33.T33 G)
      QMCLeafB.RStInit.init0_tape hfuelLen p

#print axioms QMCLeafB.Grep36M5.hoTop

/-! ## 5.  The flag stream: a `true` bit names a round at which the gate fired -/

theorem stOks_iterateTop (s : RSt) (T : ℕ) :
    stOks (roundTop^[T] s)
      = stOks s ++ (List.range T).map (fun k => programGate (roundTop^[k] s)) := by
  induction T with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', stOks_roundTop, ih, List.range_succ, List.map_append,
        List.map_singleton, List.append_assoc]

#print axioms QMCLeafB.Grep36M5.stOks_iterateTop

theorem filter_id_pos {l : List Bool} : 0 < (l.filter id).length ↔ true ∈ l := by
  induction l with
  | nil => simp
  | cons b bs ih =>
      cases b
      · simpa using ih
      · simp

#print axioms QMCLeafB.Grep36M5.filter_id_pos

theorem true_mem_map_range {T : ℕ} {f : ℕ → Bool} :
    true ∈ (List.range T).map f ↔ ∃ k, k < T ∧ f k = true := by
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, hfk⟩
    exact ⟨k, List.mem_range.mp hk, hfk⟩
  · rintro ⟨k, hk, hfk⟩
    exact ⟨k, List.mem_range.mpr hk, hfk⟩

#print axioms QMCLeafB.Grep36M5.true_mem_map_range

/-- **THE READ-OUT.**  The verdict of the repaired programme is *exactly* "some round's gate fired",
so a `true` bit is a witness round — which is what the upper side consumes. -/
theorem verdict_iterateTop (s : RSt) (hs : stOks s = []) (T : ℕ) :
    verdict (roundTop^[T] s) = true
      ↔ ∃ k, k < T ∧ programGate (roundTop^[k] s) = true := by
  unfold QMCLeafB.RoundProgram.verdict
  rw [decide_eq_true_eq, stOks_iterateTop, hs, List.nil_append, filter_id_pos,
    true_mem_map_range]

#print axioms QMCLeafB.Grep36M5.verdict_iterateTop

/-- **The read-out at the campaign programme's bit.** -/
theorem oTop_eq_true_iff (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    oTop G t = true ↔ ∃ k, k < QMCLeafB.Pbit33.T33 G ∧
      programGate (roundTop^[k] (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))) = true := by
  have hs : stOks (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) = [] := by
    simp [QMCLeafB.RStInit.init0]
  rw [oTop_apply, verdict_iterateTop _ hs _]

#print axioms QMCLeafB.Grep36M5.oTop_eq_true_iff

/-- The `ok` branch of the repaired round is taken exactly when the gate fires. -/
theorem roundTop_of_gate {s : RSt} (h : programGate s = true) : roundTop s = roundOk s := by
  unfold roundTop
  rw [if_pos h]

/-- The gate reads the state only through the fields `roundOk` freezes. -/
theorem programGate_roundOk (s : RSt) : programGate (roundOk s) = programGate s := rfl

#print axioms QMCLeafB.Grep36M5.programGate_roundOk

/-- **ONCE THE GATE FIRES IT STAYS FIRED**: the `ok` branch freezes the state, so every later round of
the orbit reports `ok` too.  This is what makes the visit a one-hit event — the reach lanes only have
to land once. -/
theorem programGate_iterate_of_gate {s : RSt} (h : programGate s = true) (j : ℕ) :
    programGate (roundTop^[j] s) = true := by
  induction j with
  | zero => exact h
  | succ i ih =>
      rw [Function.iterate_succ_apply', roundTop_of_gate ih, programGate_roundOk]
      exact ih

#print axioms QMCLeafB.Grep36M5.programGate_iterate_of_gate

/-! ## 6.  The test's semantics: the gate gives a member at the campaign registers -/

/-- The relaxed-PSD margin at `dqOf`, from the exact-pivot answer. -/
theorem margin_of_pivOk {n : ℕ} {s : RSt} {acc : QMCLeafB.PivotProgram.Acc}
    (hN : stN s = n) (hlenX : n ≤ (stX s).length) (hdq : 0 < dqOf s)
    (hsym : ∀ i j, stMat n (stX s) i j = stMat n (stX s) j i)
    (hpiv : (QMCLeafB.PivotProgram.runPiv
      (toRows (n, stX s), acc)).1 = false) :
    ∀ x : Fin n → ℚ,
      -(dqOf s / 2) * (∑ i, x i ^ 2) ≤ QMCLeafB.SepOracle.qf (stMat n (stX s)) x := by
  have hpsd : QMCLeafB.SepOracle.PSD (stMat n (stX s)) :=
    QMCLeafB.PivExact.psd_of_false (X := stX s) (acc := acc) hlenX
      (fun i j => hsym i j) hpiv
  intro x
  have h1 := hpsd x
  have h2 : (0 : ℚ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have h3 : -(dqOf s / 2) * (∑ i, x i ^ 2) ≤ 0 := by
    have : (0:ℚ) < dqOf s / 2 := by linarith
    nlinarith
  linarith

#print axioms QMCLeafB.Grep36M5.margin_of_pivOk

/-- **THE GATE'S SEMANTICS.**  The `ok` test's report is the repaired test at the engine's own
registers: positive tolerance, per-coordinate diagonal gate, the relaxed-PSD margin and the level
test.  Nothing else is read. -/
theorem stateGateAt_of_programGate {n : ℕ} {s : RSt} {acc : QMCLeafB.PivotProgram.Acc}
    (hN : stN s = n) (hlenA : n ≤ (stA s).length) (hlenX : n ≤ (stX s).length)
    (hsym : ∀ i j, stMat n (stX s) i j = stMat n (stX s) j i)
    (hP : (QMCLeafB.PivotProgram.runPiv (toRows (n, stX s), acc)).1 = false)
    (h : programGate s = true) :
    StateGateAt n s := by
  obtain ⟨hdq, hper, -, hfv⟩ := programGate_spec h
  have hdiag := fun i => perCoordGate_diag hN hlenX hper i
  have hmarg := margin_of_pivOk hN hlenX hdq hsym hP
  have htrace : QMCLeafB.SepOracle.frob (stMat n (stA s)) (stMat n (stX s))
      ≤ (stT s - QMCLeafB.RoundT.epsOf s) + dqOf s / 2 := by
    rw [← QMCLeafB.StateDiag.fvR_eq_frob (s := s) hN hlenA hlenX]
    unfold levelOf at hfv
    exact hfv
  exact ⟨hdq, hdiag, hmarg, htrace⟩

#print axioms QMCLeafB.Grep36M5.stateGateAt_of_programGate

/-- **THE GATE'S SEMANTICS, FOR ANY RELAXED-MARGIN CERTIFICATE.**  If the PSD leg `psdC` certifies
the *relaxed* margin `−(δ/2)‖x‖² ≤ qf` at `dqOf` — which is exactly membership's `psd_margin`, and
what `HokUpper34M8.evGate` certifies through `pivPsdMargin_of_measured` — then the `ok` report IS the
repaired test.  This is the widening of `stateGateAt_of_programGate`: the exact-pivot proxy is only
one instantiation, and the band needs this one. -/
theorem stateGateAt_of_okTopB {n : ℕ} {s : RSt} {psdC : RSt → Bool}
    (hN : stN s = n) (hlenA : n ≤ (stA s).length) (hlenX : n ≤ (stX s).length)
    (hmarg : psdC s = true → ∀ x : Fin n → ℚ,
      -(dqOf s / 2) * (∑ i, x i ^ 2) ≤ QMCLeafB.SepOracle.qf (stMat n (stX s)) x)
    (h : okTopB psdC s = true) :
    StateGateAt n s := by
  obtain ⟨hdq, hper, hpsd, hfv⟩ := okTopB_spec h
  have hdiag := fun i => perCoordGate_diag hN hlenX hper i
  have hmarg' := hmarg hpsd
  have htrace : QMCLeafB.SepOracle.frob (stMat n (stA s)) (stMat n (stX s))
      ≤ (stT s - QMCLeafB.RoundT.epsOf s) + dqOf s / 2 := by
    rw [← QMCLeafB.StateDiag.fvR_eq_frob (s := s) hN hlenA hlenX]
    unfold levelOf at hfv
    exact hfv
  exact ⟨hdq, hdiag, hmarg', htrace⟩

#print axioms QMCLeafB.Grep36M5.stateGateAt_of_okTopB

/-- The same at the member: any relaxed-margin certificate makes the `ok` report produce a symmetric
rational member.  This is the form a widened programme plugs into. -/
theorem member_of_okTopB {n : ℕ} {s : RSt} {psdC : RSt → Bool}
    (hN : stN s = n) (hlenA : n ≤ (stA s).length) (hlenX : n ≤ (stX s).length)
    (hA : ∀ i, stMat n (stA s) i i = 0)
    (hsym : ∀ i j, stMat n (stX s) i j = stMat n (stX s) j i)
    (hmarg : psdC s = true → ∀ x : Fin n → ℚ,
      -(dqOf s / 2) * (∑ i, x i ^ 2) ≤ QMCLeafB.SepOracle.qf (stMat n (stX s)) x)
    (h : okTopB psdC s = true) :
    ∃ cX : Matrix (Fin n) (Fin n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (stMat n (stA s)) cX
        (stT s - QMCLeafB.RoundT.epsOf s) (dqOf s) :=
  mem_of_StateGateAt hA hsym (stateGateAt_of_okTopB hN hlenA hlenX hmarg h)

#print axioms QMCLeafB.Grep36M5.member_of_okTopB

/-- **SOUNDNESS OF THE REPAIRED PROGRAMME'S `ok` TEST.**  A `true` report hands back a symmetric
rational member of the ball relaxation at `(stT − epsOf, dqOf)` — its own matrix with the diagonal
raised to the top edge (`topPinch`).  This is the whole content of the upper side: no trajectory, no
count, no ledger. -/
theorem member_of_programGate {n : ℕ} {s : RSt} {acc : QMCLeafB.PivotProgram.Acc}
    (hN : stN s = n) (hlenA : n ≤ (stA s).length) (hlenX : n ≤ (stX s).length)
    (hA : ∀ i, stMat n (stA s) i i = 0)
    (hsym : ∀ i j, stMat n (stX s) i j = stMat n (stX s) j i)
    (hP : (QMCLeafB.PivotProgram.runPiv (toRows (n, stX s), acc)).1 = false)
    (h : programGate s = true) :
    ∃ cX : Matrix (Fin n) (Fin n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (stMat n (stA s)) cX
        (stT s - QMCLeafB.RoundT.epsOf s) (dqOf s) :=
  mem_of_StateGateAt hA hsym (stateGateAt_of_programGate hN hlenA hlenX hsym hP h)

#print axioms QMCLeafB.Grep36M5.member_of_programGate

/-! ## 6b.  `htop` is NOT free at the repaired gate — the top slice is a reach obligation

The campaign's `htop` (`ConformanceM8.htop_roundGT`) is free because `roundGT`'s `ok` test is the
UPPER event `fvR ≤ stT + epsOf`, which holds at `init0` (`fvR = 0`).  The repaired gate tests the
LOWER body at `levelOf = stT − epsOf + dqOf/2`, and at `init0` that test fails on almost the whole
bracket: `fvR (init0) = 0` while `levelOf (init0) = t − eps + dqShallow/2 < 0` for every
`t < eps − dqShallow/2`.  So the bit at the top slice is only true once the descent has actually
driven the trace down — a REACH obligation, not a round-0 computation.  (It is not an impossibility:
`RelaxMem` is the *tolerated* body, and a matrix with diagonal `1 − dq/4` can carry the margin at a
negative level.)  Consequence for the assembly lane: the repaired programme needs a `roundW`-style
two-regime split (upper event on the top slice, membership gate on the interior), or a proof that the
descent reaches the level inside `T33` rounds. -/

theorem fvR_init0' (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    fvR (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) = 0 :=
  QMCLeafB.HtopInit.fvR_init0 G t

#print axioms QMCLeafB.Grep36M5.fvR_init0'

theorem levelOf_init0' (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    levelOf (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))
      = t - QMCLeafB.RundataCert.eps G + QMCLeafB.RundataParams.dqShallowCore G / 2 := by
  unfold levelOf
  rw [show stT (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) = t from rfl,
    QMCLeafB.ConformanceM8.epsOf_init0, dqOf_init0]
  rfl

#print axioms QMCLeafB.Grep36M5.levelOf_init0'

theorem dqShallowCore_le_eps (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RundataParams.dqShallowCore G ≤ QMCLeafB.RundataCert.eps G := by
  unfold QMCLeafB.RundataParams.dqShallowCore
  have h9 : (1 : ℚ) ≤ 9 * QMCLeafB.EngineRuntime.Rq G + 1 := by
    nlinarith [QMCLeafB.RundataArith.Rq_nonneg G]
  have hpos := QMCLeafB.RundataCert.eps_pos G hRq
  rw [div_le_iff₀ (by linarith : (0 : ℚ) < 9 * QMCLeafB.EngineRuntime.Rq G + 1)]
  nlinarith

#print axioms QMCLeafB.Grep36M5.dqShallowCore_le_eps

/-- **The level test fails at `init0` below `eps − dqShallow/2`** — in particular on the whole
interior bracket and on most of the top slice, where the campaign's `htop` had to be free. -/
theorem init0_level_test_fails (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) (t : ℚ)
    (ht : t < QMCLeafB.RundataCert.eps G - QMCLeafB.RundataParams.dqShallowCore G / 2) :
    ¬ (fvR (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))
        ≤ levelOf (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))) := by
  rw [fvR_init0', levelOf_init0']
  intro h
  have hdle := dqShallowCore_le_eps G hRq
  have hpos := QMCLeafB.RundataCert.eps_pos G hRq
  linarith

#print axioms QMCLeafB.Grep36M5.init0_level_test_fails

/-- **The concrete obstruction**: the repaired gate does not fire at `init0` anywhere on the top slice
below `eps − dqShallow/2 ≥ eps/2` (since `dqShallow ≤ eps`). -/
theorem init0_programGate_false_top (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) (t : ℚ)
    (ht : t < QMCLeafB.RundataCert.eps G - QMCLeafB.RundataParams.dqShallowCore G / 2) :
    programGate (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) = false := by
  by_cases h : programGate (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) = true
  · exact absurd (programGate_spec h).2.2.2 (init0_level_test_fails G hRq t ht)
  · cases hg : programGate (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))
    · rfl
    · exact absurd hg h

#print axioms QMCLeafB.Grep36M5.init0_programGate_false_top

/-! ## 7.  `hcomplete` at the repaired programme is REACH, and what the PSD proxy costs

The two halves of §1 say the repaired test is membership at the state:
`StateGateAt_of_mem` (a member passes) and `mem_of_StateGateAt` (passing gives a member).  So a `true`
bit at `oTop` — which by `oTop_eq_true_iff` names a round — is *exactly* "the orbit visited a state
that is a member at the campaign registers".  This section makes that identity into a reduction of
the completeness horn, and pins the one place where the *concrete* `Bool` test is narrower than the
membership predicate: the PSD certificate. -/

/-- "The orbit visits a gate-passing state." -/
def ReachGate (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Prop :=
  ∃ k, k < QMCLeafB.Pbit33.T33 G ∧
    programGate (roundTop^[k] (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))) = true

#print axioms QMCLeafB.Grep36M5.ReachGate

/-- **The completeness horn at the repaired programme** (m4's `CompleteSlotG` shape, at `oTop`). -/
def CompleteSlotTop : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    ¬ AsmM8.EmptyBody G t (QMCLeafB.Pbit33.P33 G) → oTop G t = true

#print axioms QMCLeafB.Grep36M5.CompleteSlotTop

/-- **`hcomplete` ⟹ REACH.**  The completeness horn, read through the bit's own read-out, is a
statement about the orbit: at every nonempty interior bracket point some round's gate fires. -/
theorem reach_of_completeSlot (H : CompleteSlotTop) (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hn : 2 ≤ G.n) (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hne : ¬ AsmM8.EmptyBody G t (QMCLeafB.Pbit33.P33 G)) :
    ReachGate G t :=
  (oTop_eq_true_iff G t).mp (H G t hn hlo hhi hne)

#print axioms QMCLeafB.Grep36M5.reach_of_completeSlot

/-- **REACH ⟹ `hcomplete`.**  The converse, so the horn and the reach statement are the same
obligation — no test-side slack on either side. -/
theorem completeSlot_of_reach
    (h : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) → ReachGate G t) :
    CompleteSlotTop :=
  fun G t hn hlo hhi _ => (oTop_eq_true_iff G t).mpr (h G t hn hlo hhi)

#print axioms QMCLeafB.Grep36M5.completeSlot_of_reach

/-! ### 7.1  The gate's clauses against membership, one by one -/

/-- The per-coordinate gate is also *complete*: if every deviation is at most `δ/4`, the filter list is
empty.  (The diagonal clause is therefore exactly membership's `diag_near` — unlike the engine's sum
gate, which rejects the band's member.) -/
theorem perCoordGate_complete {s : RSt}
    (h : ∀ i ∈ idxs (stN s, stX s), absq (entV (stN s, stX s) i i - 1) ≤ dqOf s / 4) :
    perCoordGate s = true := by
  have hempty : diagBadSt s = [] := by
    unfold diagBadSt
    rw [List.filter_eq_nil_iff]
    intro i hi
    simp only [decide_eq_true_eq, not_lt]
    exact h i hi
  unfold perCoordGate
  rw [hempty]
  rfl

#print axioms QMCLeafB.Grep36M5.perCoordGate_complete

/-- **The diagonal and level clauses ARE membership.**  A member at the state's own registers passes
the per-coordinate gate and the level test verbatim (its `diag_near` and its `trace_le`).  So the two
clauses the phase-35 barrier was about cost nothing on either side. -/
theorem gate_clauses_of_mem {n : ℕ} {s : RSt}
    (hN : stN s = n) (hlen : n ≤ (stX s).length)
    (hmem : QMCLeafB.RelaxOracle.RelaxMem (stMat n (stA s)) (stMat n (stX s))
      (stT s - QMCLeafB.RoundT.epsOf s) (dqOf s)) :
    perCoordGate s = true := by
  cases hN
  refine perCoordGate_complete (fun i hi => ?_)
  have hi' : i < stN s := by
    rw [idxs_of_le hlen] at hi
    exact List.mem_range.mp hi
  have hdev := hmem.diag_near ⟨i, hi'⟩
  rw [stMat_apply] at hdev
  rwa [absq_eq]

#print axioms QMCLeafB.Grep36M5.gate_clauses_of_mem

/-- The level test from the member's trace clause. -/
theorem level_test_of_mem {n : ℕ} {s : RSt}
    (hN : stN s = n) (hlenA : n ≤ (stA s).length) (hlenX : n ≤ (stX s).length)
    (hmem : QMCLeafB.RelaxOracle.RelaxMem (stMat n (stA s)) (stMat n (stX s))
      (stT s - QMCLeafB.RoundT.epsOf s) (dqOf s)) :
    fvR s ≤ levelOf s := by
  have h := hmem.trace_le
  rw [QMCLeafB.StateDiag.fvR_eq_frob (s := s) hN hlenA hlenX]
  unfold levelOf
  linarith

#print axioms QMCLeafB.Grep36M5.level_test_of_mem

/-- **THE ONE PLACE THE CONCRETE TEST IS NARROWER THAN MEMBERSHIP.**  With the diagonal and level
clauses already satisfied, the `ok` report is *exactly* the exact-pivot answer.  So the whole test-side
gap of the repaired programme is the PSD certificate: `pivOk` certifies exact PSD, and membership only
asks for the relaxed margin `−(δ/2)‖x‖² ≤ qf`. -/
theorem programGate_iff_pivOk {s : RSt}
    (hdq : 0 < dqOf s) (hper : perCoordGate s = true) (hlev : fvR s ≤ levelOf s) :
    programGate s = true ↔ pivOk s = true := by
  constructor
  · intro h
    exact (programGate_spec h).2.2.1
  · intro h
    have h1 : decide (0 < dqOf s) = true := by simpa using hdq
    have h2 : decide (fvR s ≤ levelOf s) = true := by simpa using hlev
    unfold programGate okTopB
    rw [h1, hper, h, h2]
    rfl

#print axioms QMCLeafB.Grep36M5.programGate_iff_pivOk

/-- **RECEIPT — the exact-PSD certificate is NOT membership-complete at the band.**  Every member of
the dreg band's body is strictly non-PSD (`qf Q 1 = −δ`), so an orbit that lands exactly on a member
is invisible to any exact-PSD certificate.  The gate's PSD leg must therefore be the *relaxed-margin*
certificate (`HokUpper34M8.evGate`: `EvRunB` at the measured radius, whose conclusion is
`PivPsdMargin` at `dqOf` by `LdltCertM5.pivPsdMargin_of_measured` with the budget
`2·n²·ε ≤ dqOf`) — the widening, and the only remaining programme-side `Poly` obligation. -/
theorem band_member_not_psd {Q : Matrix (Fin 2) (Fin 2) ℚ}
    (hQ : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁) Q
      ((QMCLeafB.DregM6.tStar + 0) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
      QMCLeafB.DregM6.P₁.dq) :
    ¬ (0 ≤ QMCLeafB.SepOracle.qf Q (fun _ => (1 : ℚ))) := by
  have h := QMCLeafB.BH35M5.member_strictly_not_psd hQ
  have hpos : (0 : ℚ) < 1 / 380000 := by norm_num
  rw [h]
  linarith

#print axioms QMCLeafB.Grep36M5.band_member_not_psd

/-! ## 8.  The upper side at the repaired programme, in the `HokSlot` shape -/

/-- The orbit of the repaired round from the campaign's tape-free initial state. -/
abbrev orbit (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) : RSt :=
  roundTop^[k] (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))

theorem stN_iterateTop (s : RSt) (k : ℕ) : stN (roundTop^[k] s) = stN s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stN_roundTop, ih]

theorem stN_orbit (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    stN (orbit G t k) = G.n := by
  show stN (roundTop^[k] (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))) = G.n
  rw [stN_iterateTop, QMCLeafB.RStInit.stN_init0]
  rfl

theorem stA_orbit (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    stA (orbit G t k) = stA (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) :=
  stA_iterateTop _ k

theorem stT_orbit (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) : stT (orbit G t k) = t := by
  rw [show orbit G t k = roundTop^[k] (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))
    from rfl, stT_iterateTop]
  rfl

theorem epsOf_orbit (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.RoundT.epsOf (orbit G t k) = QMCLeafB.RundataCert.eps G := by
  rw [QMCLeafB.HtopFinish.epsOf_congr (stA_iterateTop _ k), QMCLeafB.ConformanceM8.epsOf_init0]
  rfl

theorem dqOf_orbit (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ)
    (hRq : QMCLeafB.EngineRuntime.Rq G ≠ 0) :
    dqOf (orbit G t k) = QMCLeafB.RundataParams.dqShallow G := by
  have hp : (QMCLeafB.FinalStroke.noTape G t).1.1 = G := rfl
  rw [show orbit G t k = roundTop^[k] (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))
    from rfl, dqOf_iterateTop, dqOf_init0, hp, QMCLeafB.RundataParams.dqShallow, if_neg hRq]

/-- **THE INITIAL WEIGHT CODE IS THE WEIGHT MATRIX.**  (The row-major code `wProg` of the request is
`wMatrixQ G`'s, `RStInit.wProg_correct`; `stMat` reads a code exactly as `MatQ.entry` does.) -/
theorem stMat_stA_init0 (G : QuantumMaxCutEnergy.Input) (coins : List Bool) (t : ℚ) :
    stMat G.n (stA (QMCLeafB.RStInit.init0 ((G, coins), t)))
      = QMCLeafB.Finalization.wMatrixQ G := by
  have hc := QMCLeafB.RStInit.wProg_correct G coins
  ext i j
  have h := hc.2 i j
  rw [stMat_apply]
  exact h

#print axioms QMCLeafB.Grep36M5.stMat_stA_init0

theorem stA_init0_length (G : QuantumMaxCutEnergy.Input) (coins : List Bool) (t : ℚ) :
    (stA (QMCLeafB.RStInit.init0 ((G, coins), t))).length = G.n * G.n :=
  (QMCLeafB.RStInit.wProg_correct G coins).1

/-- **THE UPPER SIDE, AT THE REPAIRED BIT.**  Only three inputs: the bracket's positivity of `Rq`, the
orbit's symmetry at a gate-passing state, and the exact-pivot datum there.  Everything m8's
released-gate interface had to assume separately — the sum gate `dvR ≤ dq/4`, the level test, the two
register transfers `hlev`/`hdqv` — is now *built into the programme* (§3 proves the registers are
orbit invariants; §2 proves the gate is per-coordinate). -/
theorem hok_of_topBit
    (hRq : ∀ G : QuantumMaxCutEnergy.Input, 0 < QMCLeafB.EngineRuntime.Rq G)
    (hsymX : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < QMCLeafB.Pbit33.T33 G →
      programGate (orbit G t k) = true →
      ∀ i j, stMat G.n (stX (orbit G t k)) i j = stMat G.n (stX (orbit G t k)) j i)
    (hlenX : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < QMCLeafB.Pbit33.T33 G →
      programGate (orbit G t k) = true → G.n ≤ (stX (orbit G t k)).length)
    (hpiv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < QMCLeafB.Pbit33.T33 G →
      programGate (orbit G t k) = true → ∃ acc : QMCLeafB.PivotProgram.Acc,
      (QMCLeafB.PivotProgram.runPiv
        (toRows (G.n, stX (orbit G t k)), acc)).1 = false) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      oTop G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G) := by
  intro G t _ _ _ hb
  obtain ⟨k, hk, hgate⟩ := (oTop_eq_true_iff G t).mp hb
  have hN : stN (orbit G t k) = G.n := stN_orbit G t k
  have hAlong : (stA (orbit G t k)).length = G.n * G.n := by
    rw [stA_orbit G t k]
    exact stA_init0_length G ([] : List Bool) t
  have hAX : stMat G.n (stA (orbit G t k)) = QMCLeafB.Finalization.wMatrixQ G := by
    rw [stA_orbit G t k]
    exact stMat_stA_init0 G ([] : List Bool) t
  have hRqPos : 0 < QMCLeafB.EngineRuntime.Rq G := hRq G
  have hRqNe : QMCLeafB.EngineRuntime.Rq G ≠ 0 := ne_of_gt hRqPos
  obtain ⟨acc, hacc⟩ := hpiv G t k hk hgate
  obtain ⟨cX, hsymm, hmem⟩ :=
    member_of_programGate (n := G.n) (s := orbit G t k) (acc := acc) hN
      (by rw [hAlong]
          calc G.n = G.n * 1 := (Nat.mul_one G.n).symm
            _ ≤ G.n * G.n := Nat.mul_le_mul_left _ (by omega))
      (hlenX G t k hk hgate)
      (fun i => by rw [hAX]; exact QMCLeafB.Finalization.wMatrixQ_apply_of_eq)
      (hsymX G t k hk hgate) hacc hgate
  have hlev : stT (orbit G t k) - QMCLeafB.RoundT.epsOf (orbit G t k)
      = t - QMCLeafB.RundataCert.eps G := by
    rw [stT_orbit G t k, epsOf_orbit G t k]
  have hdqv : dqOf (orbit G t k) = QMCLeafB.RundataParams.dqShallow G :=
    dqOf_orbit G t k hRqNe
  rw [hlev, hdqv, hAX] at hmem
  exact ⟨cX, hsymm, hmem⟩

#print axioms QMCLeafB.Grep36M5.hok_of_topBit

/-- **The upper side in the leaf's own slot shape.** -/
def HokSlotTop : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    oTop G t = true →
    ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)

#print axioms QMCLeafB.Grep36M5.HokSlotTop

theorem hokSlotTop_of_orbit
    (hRq : ∀ G : QuantumMaxCutEnergy.Input, 0 < QMCLeafB.EngineRuntime.Rq G)
    (hsymX : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < QMCLeafB.Pbit33.T33 G →
      programGate (orbit G t k) = true →
      ∀ i j, stMat G.n (stX (orbit G t k)) i j = stMat G.n (stX (orbit G t k)) j i)
    (hlenX : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < QMCLeafB.Pbit33.T33 G →
      programGate (orbit G t k) = true → G.n ≤ (stX (orbit G t k)).length)
    (hpiv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < QMCLeafB.Pbit33.T33 G →
      programGate (orbit G t k) = true → ∃ acc : QMCLeafB.PivotProgram.Acc,
      (QMCLeafB.PivotProgram.runPiv
        (toRows (G.n, stX (orbit G t k)), acc)).1 = false) :
    HokSlotTop :=
  hok_of_topBit hRq hsymX hlenX hpiv

#print axioms QMCLeafB.Grep36M5.hokSlotTop_of_orbit

end QMCLeafB.Grep36M5


