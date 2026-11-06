-- Prove2me | Definitions.Def_QMCLeafB_thin32b
-- name    : QMCLeafB_thin32b
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:11:14.89526+00:00
-- url     : https://prove2.me/theorems/a5be2656-fae2-48b5-8038-986041fc4fd1
-- title:
--   QMCLeafB thin32b
-- statement:
--   # `Check_thin32b_m2` — phase 32, member m2, direction `thin-visit` (d2), part (b)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_initdq_m1
import Definitions.Def_QMCLeafB_thin32
/-
# `Check_thin32b_m2` — phase 32, member m2, direction `thin-visit` (d2), part (b)

**The orbit assembly**: `Check_thin32_m2.no_okW_at_window` says that *no state of the campaign's
round at the window* can be `ok` once the pivot certifies the campaign margin (that is `Hpsd`) and
the weight-code coherence holds.  This file folds that over the run: the campaign program
`(RSt, InitDq.init0, LedgerW.roundWG, RoundProgram.verdict, Tbc2)` reads **`false`** at
`(G₁, t_W)` — a point whose relaxed body is non-empty, non-degenerate and ball-bearing.

Hence `Hpsd` and `hcomplete` are *incompatible*: with `Hpsd` in hand the ok stream below the horizon
is empty, so `hcomplete`'s conclusion (`bit = true`) fails at `(G₁,t_W)`.  Conversely without
`Hpsd` the ok rounds that do fire at the window query non-unit-diagonal centres, which `hok`'s
witness route cannot use (`relaxMem_of_oracleV_ok` needs the margin).  The gate must go.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Thin32bM2

open QuantumMaxCutEnergy
open QMCLeafB.Thin32M2

abbrev St : Type := QMCLeafB.RoundProgram.RSt

/-- The campaign's initial state. -/
abbrev init0 : QMCLeafB.FuelWire.Pkg → St := QMCLeafB.InitDq.init0

/-- The campaign's round. -/
abbrev round0 : St → St := QMCLeafB.LedgerW.roundWG

/-- The campaign's verdict. -/
abbrev verdict0 : St → Bool := QMCLeafB.RoundProgram.verdict

/-- The campaign's round count `Tbc2`. -/
abbrev T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ :=
  fun G _ => QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
    * QMCLeafB.HalvePerG.mHalve (G.n * G.n)

/-- The campaign's bit. -/
abbrev bit0 : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  QMCLeafB.FinalStroke.loopBit init0 round0 verdict0 T0

/-- **The orbit at the window point.** -/
abbrev O (G : QuantumMaxCutEnergy.Input) (t : ℚ) : ℕ → St :=
  fun k => round0^[k] (init0 (QMCLeafB.FinalStroke.noTape G t))

/-! ## 1.  The state registers the round preserves -/

theorem stA_roundV (s : St) : QMCLeafB.RoundProgram.stA (QMCLeafB.OkLower.roundV s)
    = QMCLeafB.RoundProgram.stA s := by
  unfold QMCLeafB.OkLower.roundV
  by_cases h : (QMCLeafB.OkLower.oracleV s).1
  · rw [if_pos h]; rfl
  · rw [if_neg h]; rfl

theorem stA_roundWG (s : St) : QMCLeafB.RoundProgram.stA (round0 s) = QMCLeafB.RoundProgram.stA s := by
  unfold round0 QMCLeafB.LedgerW.roundWG
  by_cases h : 0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s
  · rw [if_pos h]; rfl
  · by_cases hn : (QMCLeafB.RoundProgram.stX s).length
        = QMCLeafB.RoundProgram.stN s * QMCLeafB.RoundProgram.stN s
    · rw [if_neg h, if_pos hn]; exact stA_roundV s
    · rw [if_neg h, if_neg hn]; rfl

theorem stN_roundV (s : St) : QMCLeafB.RoundProgram.stN (QMCLeafB.OkLower.roundV s)
    = QMCLeafB.RoundProgram.stN s := by
  unfold QMCLeafB.OkLower.roundV
  by_cases h : (QMCLeafB.OkLower.oracleV s).1
  · rw [if_pos h]; rfl
  · rw [if_neg h]; rfl

theorem stN_roundWG (s : St) : QMCLeafB.RoundProgram.stN (round0 s) = QMCLeafB.RoundProgram.stN s := by
  unfold round0 QMCLeafB.LedgerW.roundWG
  by_cases h : 0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s
  · rw [if_pos h]; rfl
  · by_cases hn : (QMCLeafB.RoundProgram.stX s).length
        = QMCLeafB.RoundProgram.stN s * QMCLeafB.RoundProgram.stN s
    · rw [if_neg h, if_pos hn]; exact stN_roundV s
    · rw [if_neg h, if_neg hn]; rfl

theorem stT_roundV (s : St) : QMCLeafB.RoundProgram.stT (QMCLeafB.OkLower.roundV s)
    = QMCLeafB.RoundProgram.stT s := by
  unfold QMCLeafB.OkLower.roundV
  by_cases h : (QMCLeafB.OkLower.oracleV s).1
  · rw [if_pos h]; rfl
  · rw [if_neg h]; rfl

theorem stT_roundWG (s : St) : QMCLeafB.RoundProgram.stT (round0 s) = QMCLeafB.RoundProgram.stT s := by
  unfold round0 QMCLeafB.LedgerW.roundWG
  by_cases h : 0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s
  · rw [if_pos h]; rfl
  · by_cases hn : (QMCLeafB.RoundProgram.stX s).length
        = QMCLeafB.RoundProgram.stN s * QMCLeafB.RoundProgram.stN s
    · rw [if_neg h, if_pos hn]; exact stT_roundV s
    · rw [if_neg h, if_neg hn]; rfl

theorem stT_O (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.RoundProgram.stT (O G t k) = t := by
  induction k with
  | zero => exact QMCLeafB.InitDq.stT_init0 _
  | succ j ih =>
    have h : O G t (j + 1) = round0 (O G t j) := by
      simp [O, Function.iterate_succ_apply']
    rw [h, stT_roundWG, ih]

theorem stN_O (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.RoundProgram.stN (O G t k) = G.n := by
  induction k with
  | zero => exact QMCLeafB.InitDq.stN_init0 _
  | succ j ih =>
    have h : O G t (j + 1) = round0 (O G t j) := by
      simp [O, Function.iterate_succ_apply']
    rw [h, stN_roundWG, ih]

theorem stA_O (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.RoundProgram.stA (O G t k) = QMCLeafB.RoundProgram.stA (init0 (QMCLeafB.FinalStroke.noTape G t)) := by
  induction k with
  | zero => rfl
  | succ j ih =>
    have h : O G t (j + 1) = round0 (O G t j) := by
      simp [O, Function.iterate_succ_apply']
    rw [h, stA_roundWG, ih]

theorem massV_O (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.RoundT.massV (O G t k)
      = QMCLeafB.RoundT.massV (init0 (QMCLeafB.FinalStroke.noTape G t)) := by
  unfold QMCLeafB.RoundT.massV
  rw [stA_O]

/-! ## 2.  The state's eps/dq registers along the orbit -/

theorem massV_init0 (p : QMCLeafB.FuelWire.Pkg) :
    QMCLeafB.RoundT.massV (init0 p) = QMCLeafB.EngineRuntime.Rq p.1.1 := by
  have h := QMCLeafB.AssemblyM5.epsOf_init0_any p
  unfold QMCLeafB.RoundT.epsOf at h
  linarith

theorem epsOf_O (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.RoundT.epsOf (O G t k) = QMCLeafB.EngineRuntime.Rq G / 40000 := by
  unfold QMCLeafB.RoundT.epsOf
  rw [massV_O, massV_init0]
  simp only [QMCLeafB.FinalStroke.noTape]
  ring

theorem massV_O' (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.RoundT.massV (O G t k) = QMCLeafB.EngineRuntime.Rq G := by
  rw [massV_O, massV_init0]
  simp only [QMCLeafB.FinalStroke.noTape]

theorem dqOf_O (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.OkLower.dqOf (O G t k)
      = (QMCLeafB.EngineRuntime.Rq G / 40000) / (9 * QMCLeafB.EngineRuntime.Rq G + 1) := by
  unfold QMCLeafB.OkLower.dqOf
  rw [epsOf_O, massV_O']

/-! ## 3.  The bit is `false` at the window, given the campaign margin (`Hpsd`) -/

theorem bit_false_of_hpsd
    (hF : ∀ k, k < T0 G₁ tW →
      QMCLeafB.RoundProgram.fvR (O G₁ tW k)
        = QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G₁)
            (QMCLeafB.PivExact.matOf 2 (QMCLeafB.RoundProgram.stX (O G₁ tW k))))
    (hpsd : ∀ k, k < T0 G₁ tW → QMCLeafB.OkLower.okW (O G₁ tW k) = true →
      ∀ x : Fin 2 → ℚ,
        -(QMCLeafB.OkLower.dqOf (O G₁ tW k) / 2) * (∑ i, x i ^ 2) ≤
          QMCLeafB.SepOracle.qf
            (QMCLeafB.PivExact.matOf 2 (QMCLeafB.RoundProgram.stX (O G₁ tW k))) x) :
    bit0 G₁ tW = false := by
  classical
  -- no visited state is `ok`
  have hnotok : ∀ k, k < T0 G₁ tW → QMCLeafB.OkLower.okW (O G₁ tW k) = false := by
    intro k hk
    by_contra hcon
    have hok : QMCLeafB.OkLower.okW (O G₁ tW k) = true := by
      cases h : QMCLeafB.OkLower.okW (O G₁ tW k) with
      | false => exact absurd h hcon
      | true => rfl
    have hN : QMCLeafB.RoundProgram.stN (O G₁ tW k) = 2 := by
      rw [stN_O]
    have hlen : QMCLeafB.RoundProgram.stN (O G₁ tW k)
        ≤ (QMCLeafB.RoundProgram.stX (O G₁ tW k)).length := by
      rw [QMCLeafB.LedgerW.roundWG_iterate_normalised _ (QMCLeafB.InitDq.init_normalised _) k, hN]
      norm_num
    have hT : QMCLeafB.RoundProgram.stT (O G₁ tW k) = tW := stT_O G₁ tW k
    have hEps : QMCLeafB.RoundT.epsOf (O G₁ tW k) = 1 / 20000 := by
      rw [epsOf_O, Rq₁]; norm_num
    have hdq : QMCLeafB.OkLower.dqOf (O G₁ tW k) = 1 / 380000 := by
      rw [dqOf_O, Rq₁]; norm_num
    have hpos : 0 < QMCLeafB.RoundT.massV (O G₁ tW k) := by
      rw [massV_O', Rq₁]; norm_num
    have hlo : ¬ (0 ≤ QMCLeafB.RoundProgram.stT (O G₁ tW k)
        + QMCLeafB.RoundT.epsOf (O G₁ tW k)) := by
      rw [hT, hEps]
      show ¬ (0 : ℚ) ≤ -(2 : ℚ) + 69 / 1520000 + 1 / 20000
      norm_num
    exact no_okW_at_window (O G₁ tW k) hN hlen hT hEps hdq hpos hlo
      (hF k hk) (hpsd k hk hok) hok
  -- read the bit off the ok stream
  have hbit : bit0 G₁ tW
      = QMCLeafB.SimLoop.anyOk (fun k => QMCLeafB.OkLower.okW
          (QMCLeafB.OkLower.roundW^[k]
            (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G₁ tW)))) (T0 G₁ tW) :=
    QMCLeafB.LedgerW.verdict_iterate_eq_anyOk_WG
      (fun p => QMCLeafB.InitDq.stOks_init0 p)
      (fun p => QMCLeafB.InitDq.init_normalised p) (T0 G₁ tW) G₁ tW
  rw [hbit]
  refine (QMCLeafB.SimLoop.anyOk_eq_false_iff _ (T0 G₁ tW)).mpr ?_
  intro k hk
  rw [← QMCLeafB.LedgerW.roundWG_iterate_eq_roundW _ (QMCLeafB.InitDq.init_normalised _) k]
  exact hnotok k hk

/-! ## 4.  `Hpsd` refutes `hcomplete` at the campaign's own program -/

/-- **THE INCOMPATIBILITY.**  With the pivot margin at the visited `ok` states — `Hpsd`'s exact
content — and the weight-code coherence, the campaign's bit reads `false` at `(G₁,t_W)`, a point
whose relaxed body is non-empty and interior.  So `hcomplete` (the second residual of phase 32) is
FALSE at the campaign program as soon as `Hpsd` (the first residual) holds. -/
theorem not_hcomplete_campaign
    (hF : ∀ k, k < T0 G₁ tW →
      QMCLeafB.RoundProgram.fvR (O G₁ tW k)
        = QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G₁)
            (QMCLeafB.PivExact.matOf 2 (QMCLeafB.RoundProgram.stX (O G₁ tW k))))
    (hpsd : ∀ k, k < T0 G₁ tW → QMCLeafB.OkLower.okW (O G₁ tW k) = true →
      ∀ x : Fin 2 → ℚ,
        -(QMCLeafB.OkLower.dqOf (O G₁ tW k) / 2) * (∑ i, x i ^ 2) ≤
          QMCLeafB.SepOracle.qf
            (QMCLeafB.PivExact.matOf 2 (QMCLeafB.RoundProgram.stX (O G₁ tW k))) x) :
    ¬ (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → _root_.AsmM8.Interior G t →
        ¬ _root_.AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) → bit0 G t = true) := by
  intro hC
  have hne : ¬ _root_.AsmM8.EmptyBody G₁ tW (QMCLeafB.UnionShallow.paramsKbc2 G₁) := by
    intro hE
    refine hE Xw ?_
    rw [level_W, dq₁]
    exact nonempty_W
  have htrue := hC G₁ tW hn₁ interior_W hne
  rw [bit_false_of_hpsd hF hpsd] at htrue
  exact Bool.false_ne_true htrue

#print axioms QMCLeafB.Thin32bM2.bit_false_of_hpsd
#print axioms QMCLeafB.Thin32bM2.not_hcomplete_campaign

end QMCLeafB.Thin32bM2


