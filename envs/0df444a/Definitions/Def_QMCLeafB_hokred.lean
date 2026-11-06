-- Prove2me | Definitions.Def_QMCLeafB_hokred
-- name    : QMCLeafB_hokred
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:06:42.146032+00:00
-- url     : https://prove2.me/theorems/a3a82d8d-3b8a-4e7e-9e35-8a6cde09df71
-- title:
--   QMCLeafB hokred
-- statement:
--   `Check_hokred_m7` — phase 31, member m7, direction `symm-invariant` (part 2).
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_eaudit
import Definitions.Def_QMCLeafB_symm31
/-
  `Check_hokred_m7` — phase 31, member m7, direction `symm-invariant` (part 2).

  **The capstone.**  The composite's `hok` slot is

      hok : bit G t = true → ∃ cX, cXᵀ = cX ∧ RelaxMem (wMatrixQ G) cX (t − eps G) (dqShallow G)

  at every interior point.  Between the bit and that certificate stand seven pointwise facts at the
  visited ok state.  Six of them are theorems now:

  | fact | receipt |
  |---|---|
  | `stN s = G.n`, `stT s = t`, `stA`/`stMu`/`stD` frozen | `EAudit2M7.hn_orbitW`/`ht_orbitW`/`stA_orbitW` |
  | `stN s ≤ (stX s).length`, `0 < stD s` | `EAudit2M7.hlen_orbitW`/`hD_orbitW` |
  | `massV s = Rq G`, `dqOf s = dqShallow G` | `EAudit2M7.massV_orbitW`/`dqOf_orbitW` |
  | `diag_near` (`|Xᵢᵢ − 1| ≤ dq/4`) | free from `dvR s = 0` (`StateDiag.stMat_diag_abs_le`; `EAudit2M7.hdiag_free`) |
  | trace clause `frob A cX ≤ (t − eps) + dq/2` | the `ok` test's own `fvR ≤ levelOf`, bridged by `StateDiag.fvR_eq_frob` |
  | **symmetry** `cXᵀ = cX` | `Symm31M7.hCsym_orbitW` (this phase) |

  So `hok` reduces to **one** clause per visited ok state: the PSD clause
  `∀ x, −(dqShallow G/2)·‖x‖² ≤ qf (stMat G.n (stX s)) x` — which is the pivot test's half
  (`LdltCertM5.pivPsdMargin_of_tolerance`, needing `hbox` + the grid, or an exact-PSD descent).
  `hok_of_psd` below is that reduction, machine-checked.

  Discipline: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; `#print axioms` at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

noncomputable section

namespace HokRedM7

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCLeafB.RoundProgram

local instance instRequestCodingHokRed : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- `StateDiag.stMat` is `MatQ.toMatrix` (`entV` and `MatQ.entry` are the same `getD`). -/
theorem stMat_eq_toMatrix (n : ℕ) (X : List ℚ) :
    QMCLeafB.StateDiag.stMat n X = MatQ.toMatrix n X := rfl

abbrev sOf (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) : RSt :=
  QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))

/-! ## 1.  One visited `ok` state gives the certificate, modulo the PSD clause -/

theorem relaxMem_at_stateW {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hint : AsmM8.Interior G t) (k : ℕ)
    (hok : QMCLeafB.OkLower.okW (sOf G t k) = true)
    (hpsd : ∀ x : Fin G.n → ℚ,
      -(QMCLeafB.RundataParams.dqShallow G / 2) * (∑ i, x i ^ 2)
        ≤ QMCLeafB.SepOracle.qf (QMCLeafB.StateDiag.stMat G.n (stX (sOf G t k))) x) :
    ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G) := by
  have hRq : 0 < QMCLeafB.EngineRuntime.Rq G := Asm2M8.Rq_pos_of_interior hint
  have hRqne : QMCLeafB.EngineRuntime.Rq G ≠ 0 := ne_of_gt hRq
  have hN : stN (sOf G t k) = G.n := EAudit2M7.hn_orbitW _ k
  have hlen : G.n ≤ (stX (sOf G t k)).length := by
    rw [← hN]
    exact EAudit2M7.hlen_orbitW _ k
  have ht : stT (sOf G t k) = t := EAudit2M7.ht_orbitW _ k
  have heps : QMCLeafB.RoundT.epsOf (sOf G t k) = QMCLeafB.EngineRuntime.Rq G / 40000 :=
    EAudit2M7.epsOf_orbitW _ k
  have hmass : QMCLeafB.RoundT.massV (sOf G t k) = QMCLeafB.EngineRuntime.Rq G :=
    EAudit2M7.massV_orbitW _ k
  have hdq : QMCLeafB.OkLower.dqOf (sOf G t k) = QMCLeafB.RundataParams.dqShallow G :=
    EAudit2M7.dqOf_orbitW _ k hRqne
  have hA : G.n ≤ (stA (sOf G t k)).length := by
    rw [EAudit2M7.stA_orbitW,
      QMCLeafB.RStInit.stA_length_init0,
      QMCLeafB.RStInit.stN_init0]
    exact Nat.le_mul_self _
  have hreg : ¬ (0 ≤ stT (sOf G t k) + QMCLeafB.RoundT.epsOf (sOf G t k)) := by
    rw [ht, heps]
    intro hcon
    have hR : (((t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
        = (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by push_cast; ring
    have h3 : (0 : ℝ) ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
      rw [← hR]
      exact_mod_cast hcon
    have h2 := hint.2
    linarith
  have hV : (QMCLeafB.OkLower.oracleV (sOf G t k)).1 = false := by
    have h1 := QMCLeafB.OkLower.okW_eq_engine (sOf G t k) 0 hreg
    have h2 : QMCLeafB.OkLower.okW (sOf G t k)
        = !((QMCLeafB.OkLower.oracleV (sOf G t k)).1) := by simpa using h1
    rw [h2] at hok
    simpa using hok
  have hpos : 0 < QMCLeafB.RoundT.massV (sOf G t k) := by
    rw [hmass]; exact hRq
  have hF : QMCLeafB.RoundProgram.fvR (sOf G t k)
      = QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G)
          (QMCLeafB.StateDiag.stMat G.n (stX (sOf G t k))) := by
    rw [QMCLeafB.StateDiag.fvR_eq_frob hN hA hlen]
    have hA2 : QMCLeafB.StateDiag.stMat G.n (stA (sOf G t k))
        = QMCLeafB.Finalization.wMatrixQ G := by
      rw [EAudit2M7.stA_orbitW, stMat_eq_toMatrix,
        QMCLeafB.RStInit.stA_toMatrix_noTape]
      rfl
    rw [hA2]
  have hpsd' : ∀ x : Fin G.n → ℚ,
      -(QMCLeafB.OkLower.dqOf (sOf G t k) / 2) * (∑ i, x i ^ 2)
        ≤ QMCLeafB.SepOracle.qf (QMCLeafB.StateDiag.stMat G.n (stX (sOf G t k))) x := by
    intro x
    rw [hdq]
    exact hpsd x
  have hR := QMCLeafB.StateDiag.relaxMem_of_oracleV_ok_state (n := G.n) hN hlen hF hV hpos hpsd'
  refine ⟨QMCLeafB.StateDiag.stMat G.n (stX (sOf G t k)), ?_, ?_⟩
  · have h := Symm31M7.hCsym_orbitW (QMCLeafB.FinalStroke.noTape G t) k
    rw [hN] at h
    rw [stMat_eq_toMatrix]
    exact h
  · have hlevel : (t - QMCLeafB.RundataCert.eps G)
        = (stT (sOf G t k) - QMCLeafB.RoundT.epsOf (sOf G t k)) := by
      rw [ht, heps]
      rfl
    have hdqe : QMCLeafB.RundataParams.dqShallow G = QMCLeafB.OkLower.dqOf (sOf G t k) := by
      rw [hdq]
    rw [hlevel, hdqe]
    exact hR

/-! ## 2.  `hok` from the PSD clause alone -/

/-- **The composite's `hok`, reduced to the pivot test's PSD clause.**  `Hpsd` quantifies over the
visited `ok` states only; everything else is discharged. -/
theorem hok_of_psd
    (Hpsd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t →
      QMCLeafB.OkLower.okW (sOf G t k) = true →
      ∀ x : Fin G.n → ℚ,
        -(QMCLeafB.RundataParams.dqShallow G / 2) * (∑ i, x i ^ 2)
          ≤ QMCLeafB.SepOracle.qf (QMCLeafB.StateDiag.stMat G.n (stX (sOf G t k))) x) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      EAuditM7.Bit G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G) := by
  intro G t hn hint hb
  obtain ⟨k, hk, hokv⟩ := EAuditM7.okround_of_bit hb
  exact relaxMem_at_stateW hn hint k hokv (Hpsd G t k hn hint hk hokv)

/-! ## 3.  The composite at the pinned program, with `hok` discharged

`Asm2M8.solution_of_residual` asks for seven slots.  At the pinned programme
`(RStInit.init0, OkLower.roundW, RoundProgram.verdict)`:

* `Poly init`, `Poly round`, `Poly verdict`, `hinitTape`, `htop` — banked (see `Check_eaudit_m7`);
* `hok` — **`hok_of_psd` above: a theorem given the PSD clause at visited `ok` states**;
* `hbit`, `hC` — theorems given `hok` and completeness (`Check_eaudit_m7`'s
  `hbit_of_hok_hcomp`/`hC_of_hbit`).

So the leaf stands on exactly: the one-step length bound, the PSD clause, and completeness. -/

theorem solution_of_psd_and_complete
    (k : ℕ) (hk : 20 ≤ 2 ^ k) (c : ℕ)
    (hstepLen : ∀ s : RSt,
      (enc (QMCLeafB.OkLower.roundW s)).length ≤ (enc s).length + c)
    (Hpsd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t →
      QMCLeafB.OkLower.okW (sOf G t k) = true →
      ∀ x : Fin G.n → ℚ,
        -(QMCLeafB.RundataParams.dqShallow G / 2) * (∑ i, x i ^ 2)
          ≤ QMCLeafB.SepOracle.qf (QMCLeafB.StateDiag.stMat G.n (stX (sOf G t k))) x)
    (hcomp : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      EAuditM7.Bit G t = true) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  EAuditM7.solution_of_two (init := EAuditM7.ProgInit) (round := EAuditM7.ProgRound)
    (verdict := EAuditM7.ProgVerdict) k hk
    EAuditM7.poly_init EAuditM7.poly_round EAuditM7.poly_verdict c hstepLen
    EAuditM7.hinitTape_pinned EAuditM7.htop_pinned
    (hok_of_psd Hpsd) hcomp

end HokRedM7

/-! ## Axiom audit -/

#print axioms HokRedM7.stMat_eq_toMatrix
#print axioms HokRedM7.relaxMem_at_stateW
#print axioms HokRedM7.hok_of_psd
#print axioms HokRedM7.solution_of_psd_and_complete


