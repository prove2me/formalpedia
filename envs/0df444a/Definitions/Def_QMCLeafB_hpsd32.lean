-- Prove2me | Definitions.Def_QMCLeafB_hpsd32
-- name    : QMCLeafB_hpsd32
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:54:11.104553+00:00
-- url     : https://prove2.me/theorems/63a016b9-45ac-406b-82bd-c8d19e90e93b
-- title:
--   QMCLeafB hpsd32
-- statement:
--   `Check_hpsd32_m1` — phase 32, member m1, direction `hpsd-chain`.
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_ldltcert2_m5
import Definitions.Def_QMCLeafB_htop_ledgerW_m7
import Definitions.Def_QMCLeafB_hokred
/-
  `Check_hpsd32_m1` — phase 32, member m1, direction `hpsd-chain`.

  **What this file settles.**  `HokRedM7.hok_of_psd` reduced the composite's `hok` slot to the PSD
  clause `Hpsd` at visited `ok` states:

      Hpsd : ∀ G t k, 2 ≤ G.n → Interior G t → k < Tbc2 G t → okW (sOf G t k) = true →
              ∀ x, −(dqShallow G / 2)·‖x‖² ≤ qf (stMat G.n (stX (sOf G t k))) x

  (`sOf G t k = OkLower.roundW^[k] (RStInit.init0 (noTape G t))`).  This file **lands that chain**
  and states exactly what survives:

  * §1 the `ok` answer's own data at a visited state: `dvR = 0`, `fvR ≤ levelOf`, and the pivot
    answer `false` (`OkLower.oracleV_ok` read along the orbit);
  * §2 `PivPsdMargin` at a visited `ok` state from the two gates the interval certificate needs —
    (G) the grid condition `2·n² ≤ dq·d` and (B) the no-clip tracker `BoxRun` — i.e.
    `LdltCertM5.pivPsdMargin_of_tolerance` instantiated at the orbit with `hlen`, `hd`, `hsym` and
    the pivot answer discharged;
  * §3 **`hpsd_of_gates`**: `Hpsd` itself, from (G)+(B) at the visited `ok` states only;
  * §4 the measured-radius variant: (G) can be dropped entirely if the run's *own* rounding error
    `ε` is certified, `2n²ε ≤ dq` (`pivPsdMargin_of_measured`) — no grid enlargement needed on the
    analytic side, only a finer certificate;
  * §5 the receipts on the two gates: (G) FAILS at the campaign's packed grid `gridOf 2 = 81` at
    every interior point (`dqShallow < 1/360000` but the gate needs `dq ≥ 8/81`), so the certified
    route forces the `stD` enlargement (a program change, priced in §5b); (B) is a *finite Boolean
    check* on the run (`BoxRunB`) and can be conjoined to the `ok` test, which makes it definitional;
  * §6 the resulting repair interface: an `ok` test that conjoins the two checks certifies `Hpsd`
    with no side conditions (`pivPsdMargin_of_okCert`, `pivPsdMargin_of_okCertM`), so the residual
    on the `hok` side is a *program* choice, not a theorem.

  Discipline: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; `#print axioms` at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

noncomputable section

namespace Hpsd32M1

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCLeafB.RoundProgram

local instance instRequestCodingHpsd32 : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- The visited state, at the declared initial state (`HokRedM7.sOf`, spelled once). -/
abbrev sOf (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) : RSt := HokRedM7.sOf G t k

/-- `PivExact.matOf` and `MatQ.toMatrix` are the same block (both read the flat code). -/
theorem matOf_eq_toMatrix (n : ℕ) (X : List ℚ) :
    QMCLeafB.PivExact.matOf n X = MatQ.toMatrix n X := rfl

/-- `StateDiag.stMat` is the same block again. -/
theorem stMat_eq_toMatrix (n : ℕ) (X : List ℚ) :
    QMCLeafB.StateDiag.stMat n X = MatQ.toMatrix n X := rfl

/-! ## 1.  The `ok` answer's data at a visited state -/

/-- **`okW` at a visited state is the lower-body oracle reporting `ok`.**  (The regime is an orbit
invariant and the interior bracket sits strictly below it.) -/
theorem oracleV_false_of_okW {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hint : AsmM8.Interior G t)
    (k : ℕ) (hok : QMCLeafB.OkLower.okW (sOf G t k) = true) :
    (QMCLeafB.OkLower.oracleV (sOf G t k)).1 = false := by
  have ht : stT (sOf G t k) = t := EAudit2M7.ht_orbitW _ k
  have heps : QMCLeafB.RoundT.epsOf (sOf G t k) = QMCLeafB.EngineRuntime.Rq G / 40000 :=
    EAudit2M7.epsOf_orbitW _ k
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
  have h1 := QMCLeafB.OkLower.okW_eq_engine (sOf G t k) 0 hreg
  have h2 : QMCLeafB.OkLower.okW (sOf G t k)
      = !((QMCLeafB.OkLower.oracleV (sOf G t k)).1) := by simpa using h1
  rw [h2] at hok
  simpa using hok

/-- **The pivot test answers `false` at a visited `ok` state.** -/
theorem pivAns_false_of_okW {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hint : AsmM8.Interior G t)
    (k : ℕ) (hok : QMCLeafB.OkLower.okW (sOf G t k) = true) :
    (pivAns (sOf G t k)).1 = false :=
  (QMCLeafB.OkLower.oracleV_ok _ (oracleV_false_of_okW hint k hok)).2.2

/-- **The descent's grid and box registers are orbit-invariant**, and the code is long enough. -/
theorem orbit_gates_static (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    stD (sOf G t k) = QMCLeafB.InitVerdict.gridOf G.n := by
  have h : stD (sOf G t k)
      = stD (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) :=
    EAudit2M7.stD_orbitW _ k
  rw [h, QMCLeafB.RStInit.stD_init0_eq]
  rfl

theorem orbit_mu (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    stMu (sOf G t k) = QMCLeafB.RStInit.muOf G.n := by
  have h : stMu (sOf G t k)
      = stMu (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) :=
    EAudit2M7.stMu_orbitW _ k
  rw [h, QMCLeafB.RStInit.stMu_init0_eq]
  rfl

/-- **Symmetry at `PivExact.matOf`'s own spelling.** -/
theorem orbit_symm (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    ∀ i j, QMCLeafB.PivExact.matOf (stN (sOf G t k)) (stX (sOf G t k)) i j
      = QMCLeafB.PivExact.matOf (stN (sOf G t k)) (stX (sOf G t k)) j i := by
  intro i j
  have hM := Symm31M7.hCsym_orbitW (QMCLeafB.FinalStroke.noTape G t) k
  rw [matOf_eq_toMatrix]
  have h := congrArg (fun M => M i j) hM
  simpa [Matrix.transpose_apply] using h.symm

/-! ## 2.  The interval certificate at a visited `ok` state

`LdltCertM5.pivPsdMargin_of_tolerance` asks for five things at the state: the code is long enough,
the grid is positive, the block is symmetric, the descent never clips (`BoxRun`), and the answer is
`false`.  Four of the five are §1; the grid condition `2·n² ≤ dq·d` is the gate (G) and `BoxRun` is
the gate (B). -/

/-- Gate (G): the grid condition at a visited `ok` state. -/
def GridGate (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) : Prop :=
  2 * (stN (sOf G t k) : ℚ) * (stN (sOf G t k) : ℚ)
    ≤ QMCLeafB.RundataParams.dqShallow G * (stD (sOf G t k) : ℚ)

/-- Gate (B): the descent's own no-clip tracker at a visited `ok` state. -/
def BoxGate (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) : Prop :=
  QMCLeafB.LdltCertM5.BoxRun (stMu (sOf G t k)) (stN (sOf G t k))
    ((stMu (sOf G t k), stD (sOf G t k)),
      (toRows (stN (sOf G t k), stX (sOf G t k)), ([] : QMCLeafB.PivotProgram.Acc)))

/-- **The margin at a visited `ok` state, from the two gates.** -/
theorem pivPsdMargin_of_okW_gates {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hint : AsmM8.Interior G t) (k : ℕ)
    (hok : QMCLeafB.OkLower.okW (sOf G t k) = true)
    (hgrid : GridGate G t k) (hbox : BoxGate G t k) :
    QMCLeafB.ContractM7.PivPsdMargin (sOf G t k) (QMCLeafB.RundataParams.dqShallow G) :=
  QMCLeafB.LdltCertM5.pivPsdMargin_of_tolerance (s := sOf G t k)
    (EAudit2M7.hlen_orbitW (QMCLeafB.FinalStroke.noTape G t) k)
    (EAudit2M7.hD_orbitW (QMCLeafB.FinalStroke.noTape G t) k)
    (orbit_symm G t k) hbox (pivAns_false_of_okW hint k hok)
    (QMCLeafB.InitDq.dqOf_pos G) hgrid

/-! ## 3.  `Hpsd`, from the two gates at visited `ok` states only -/

/-- **`Hpsd`, the residual of `HokRedM7.hok_of_psd`, from the two gates.** -/
theorem hpsd_of_gates
    (hgrid : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (sOf G t k) = true →
      GridGate G t k)
    (hbox : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (sOf G t k) = true →
      BoxGate G t k) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (sOf G t k) = true →
      ∀ x : Fin G.n → ℚ,
        -(QMCLeafB.RundataParams.dqShallow G / 2) * (∑ i, x i ^ 2)
          ≤ QMCLeafB.SepOracle.qf (QMCLeafB.StateDiag.stMat G.n (stX (sOf G t k))) x := by
  intro G t k hn hint hk hok
  have hm := pivPsdMargin_of_okW_gates hint k hok (hgrid G t k hn hint hk hok)
    (hbox G t k hn hint hk hok)
  have hN : stN (sOf G t k) = G.n := EAudit2M7.hn_orbitW _ k
  have key : ∀ x : Fin (stN (sOf G t k)) → ℚ,
      -(QMCLeafB.RundataParams.dqShallow G / 2) * (∑ i, x i ^ 2)
        ≤ QMCLeafB.SepOracle.qf
            (QMCLeafB.StateDiag.stMat (stN (sOf G t k)) (stX (sOf G t k))) x := by
    intro x
    rw [stMat_eq_toMatrix]
    exact hm x
  exact hN ▸ key

/-- **The composite's `hok` slot, from the two gates.**  Exactly `HokRedM7.hok_of_psd`'s input. -/
theorem hok_of_gates
    (hgrid : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (sOf G t k) = true →
      GridGate G t k)
    (hbox : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (sOf G t k) = true →
      BoxGate G t k) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      EAuditM7.Bit G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G) :=
  HokRedM7.hok_of_psd (hpsd_of_gates hgrid hbox)



/-! ## 4.  The measured-radius variant: gate (G) is replaceable by the run's own error

`pivPsdMargin_of_measured` needs no grid at all: it asks for `EvRun mu d ε` (the descent's actual
entrywise rounding error, a Boolean check `EvRunB`) and the budget `2·n²·ε ≤ dq`.  So the analytic
content of (G) is only ever "the certificate's own error fits the tolerance". -/

/-- The measured-error gate at a visited `ok` state. -/
def EvGate (ε : ℚ) (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) : Prop :=
  QMCLeafB.LdltCertM5.EvRun (stMu (sOf G t k)) (stD (sOf G t k)) ε (stN (sOf G t k))
    ((stMu (sOf G t k), stD (sOf G t k)),
      (toRows (stN (sOf G t k), stX (sOf G t k)), ([] : QMCLeafB.PivotProgram.Acc)))

/-- **The margin from a measured error, no grid condition.** -/
theorem pivPsdMargin_of_okW_ev {G : QuantumMaxCutEnergy.Input} {t : ℚ} {ε : ℚ} (hε : 0 ≤ ε)
    (hint : AsmM8.Interior G t) (k : ℕ)
    (hok : QMCLeafB.OkLower.okW (sOf G t k) = true)
    (hev : EvGate ε G t k)
    (hbud : 2 * ((stN (sOf G t k) : ℚ) * (stN (sOf G t k) : ℚ) * ε)
      ≤ QMCLeafB.RundataParams.dqShallow G) :
    QMCLeafB.ContractM7.PivPsdMargin (sOf G t k) (QMCLeafB.RundataParams.dqShallow G) :=
  QMCLeafB.LdltCertM5.pivPsdMargin_of_measured (s := sOf G t k)
    (EAudit2M7.hlen_orbitW (QMCLeafB.FinalStroke.noTape G t) k)
    (orbit_symm G t k) hε hev (pivAns_false_of_okW hint k hok) hbud

/-- **The box gate is stronger than the measured gate at `ε = 1/d`** — so (B) is the *checkable*
form of (G)'s and the analytic content is one scalar. -/
theorem evGate_of_boxGate {G : QuantumMaxCutEnergy.Input} {t : ℚ} (k : ℕ) (hbox : BoxGate G t k) :
    EvGate (1 / (stD (sOf G t k) : ℚ)) G t k :=
  QMCLeafB.LdltCertM5.evRun_of_box (EAudit2M7.hD_orbitW (QMCLeafB.FinalStroke.noTape G t) k)
    (stN (sOf G t k)) _ hbox

/-- **`Hpsd` from a measured-error gate instead of the grid gate** — no grid condition. -/
theorem hpsd_of_ev_gate (ε : ℚ) (hε : 0 ≤ ε)
    (hev : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (sOf G t k) = true →
      EvGate ε G t k)
    (hbud : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (sOf G t k) = true →
      2 * ((stN (sOf G t k) : ℚ) * (stN (sOf G t k) : ℚ) * ε)
        ≤ QMCLeafB.RundataParams.dqShallow G) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (sOf G t k) = true →
      ∀ x : Fin G.n → ℚ,
        -(QMCLeafB.RundataParams.dqShallow G / 2) * (∑ i, x i ^ 2)
          ≤ QMCLeafB.SepOracle.qf (QMCLeafB.StateDiag.stMat G.n (stX (sOf G t k))) x := by
  intro G t k hn hint hk hok
  have hm := pivPsdMargin_of_okW_ev hε hint k hok (hev G t k hn hint hk hok)
    (hbud G t k hn hint hk hok)
  have hN : stN (sOf G t k) = G.n := EAudit2M7.hn_orbitW _ k
  have key : ∀ x : Fin (stN (sOf G t k)) → ℚ,
      -(QMCLeafB.RundataParams.dqShallow G / 2) * (∑ i, x i ^ 2)
        ≤ QMCLeafB.SepOracle.qf
            (QMCLeafB.StateDiag.stMat (stN (sOf G t k)) (stX (sOf G t k))) x := by
    intro x
    rw [stMat_eq_toMatrix]
    exact hm x
  exact hN ▸ key

end Hpsd32M1

namespace Hpsd32M1

open QuantumMaxCutEnergy
open QMCLeafB.RoundProgram

/-! ## 5.  The gates on the campaign's own program: (G) fails, and what it costs

The packed campaign state carries `stD = gridOf n = (n+1)⁴`, so gate (G) reads
`2n² ≤ dqShallow·(n+1)⁴`.  At the campaign exemplar (`n = 2`, `dqShallow = 1/380000`) that is
`8 ≤ 81/380000` — false, by four orders of magnitude.  The receipt is unconditional in the interior
bracket (where only `dqShallow < 1/360000` is used). -/

theorem gridOf_two : QMCLeafB.InitVerdict.gridOf 2 = 81 := by
  unfold QMCLeafB.InitVerdict.gridOf
  norm_num

/-- The gate at the packed grid, in closed form. -/
theorem gridGate_pinned_iff (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    GridGate G t k
      ↔ 2 * (G.n : ℚ) * (G.n : ℚ)
          ≤ QMCLeafB.RundataParams.dqShallow G * (QMCLeafB.InitVerdict.gridOf G.n : ℚ) := by
  unfold GridGate
  rw [EAudit2M7.hn_orbitW, orbit_gates_static G t k]
  simp only [QMCLeafB.FinalStroke.noTape]

/-- **Gate (G) FAILS at the campaign's packed grid, at the exemplar's order** — at every interior
point and every round.  So `Hpsd` cannot be had from the certified descent at the packed state: the
`stD` register must be enlarged (a program change, not a proof one). -/
theorem gridGate_fails_pinned {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn2 : G.n = 2)
    (hint : AsmM8.Interior G t) (k : ℕ) : ¬ GridGate G t k := by
  rw [gridGate_pinned_iff, hn2, gridOf_two]
  intro h
  have hRq := Asm2M8.Rq_pos_of_interior hint
  have hlt := QMCLeafB.ContractM7.dqShallow_lt_floor hRq
  norm_num at h
  linarith

/-- **What (G) asks for.**  The gate is exactly `grid ≳ 2n²/dq`, so a grid register chosen at
`⌈2n²/dq⌉` passes it — the enlargement is a small poly number (`≈ 3.04·10⁶` at `n = 2`,
`dqShallow = 1/380000`), i.e. `≈ 22` bits. -/
theorem grid_suffices {n : ℕ} {dq : ℚ} (hdq : 0 < dq) (D : ℕ)
    (hD : (2 * (n : ℚ) * (n : ℚ)) / dq ≤ (D : ℚ)) :
    2 * (n : ℚ) * (n : ℚ) ≤ dq * (D : ℚ) := by
  rw [div_le_iff₀ hdq] at hD
  linarith

/-- Gate (G) is satisfiable at every order and every positive tolerance — the enlargement always
exists (Archimedean), so the gate is a *choice*, not an obstruction. -/
theorem exists_grid {n : ℕ} {dq : ℚ} (hdq : 0 < dq) :
    ∃ D : ℕ, 2 * (n : ℚ) * (n : ℚ) ≤ dq * (D : ℚ) := by
  obtain ⟨D, hD⟩ := exists_nat_gt ((2 * (n : ℚ) * (n : ℚ)) / dq)
  exact ⟨D, grid_suffices hdq D hD.le⟩

/-- **The exemplar's arithmetic**: at `n = 2`, `dqShallow = 1/380000`, any grid `D ≥ 3040000`
passes gate (G). -/
theorem grid_at_exemplar (D : ℕ) (hD : 3040000 ≤ D) :
    2 * (2 : ℚ) * 2 ≤ (1 / 380000) * (D : ℚ) := by
  have hD' : ((3040000 : ℕ) : ℚ) ≤ (D : ℚ) := by exact_mod_cast hD
  have h1 : (1 / 380000 : ℚ) * (3040000 : ℚ) = 8 := by norm_num
  have h3 : (1 / 380000 : ℚ) * (3040000 : ℚ) ≤ (1 / 380000 : ℚ) * (D : ℚ) :=
    mul_le_mul_of_nonneg_left hD' (by norm_num)
  rw [h1] at h3
  linarith

/-! ## 6.  Gate (B) is a finite Boolean check — and conjoining it makes the certificate definitional

`BoxRunB` is the interval routine's own check of the same predicate (`boxRun_of_boxRunB`), of the
shape of the descent loop, so the campaign's `ok` test can *carry* gate (B) rather than inherit it.
The two theorems below are that interface: an `ok` flag that conjoins the checks certifies the
margin with no side conditions at all, because the margin theorem then has nothing left to assume.

The measured-error form is strictly better: `EvRunB` at the run's own error `ε` plus the budget
`2n²ε ≤ dq` needs no grid condition either, so the enlarged grid can be traded for a finer
certificate (and the smallest such `ε` is what the descent actually incurred). -/

/-- **The certified `ok` flag** (grid form): the pivot answer `false`, gate (G), gate (B). -/
def okCert (dq : ℚ) (s : RSt) : Bool :=
  (!(pivAns s).1 && decide (2 * (stN s : ℚ) * (stN s : ℚ) ≤ dq * (stD s : ℚ)))
    && QMCLeafB.LdltCertM5.BoxRunB (stMu s) (stN s)
        ((stMu s, stD s), (toRows (stN s, stX s), ([] : QMCLeafB.PivotProgram.Acc)))

/-- **The certified `ok` flag** (measured-error form): the pivot answer `false`, the error check at
`ε`, and the budget `2n²ε ≤ dq`.  No grid condition. -/
def okCertM (dq ε : ℚ) (s : RSt) : Bool :=
  (!(pivAns s).1 && decide (2 * ((stN s : ℚ) * (stN s : ℚ) * ε) ≤ dq))
    && QMCLeafB.LdltCertM5.EvRunB (stMu s) (stD s) ε (stN s)
        ((stMu s, stD s), (toRows (stN s, stX s), ([] : QMCLeafB.PivotProgram.Acc)))

/-- **`PivPsdMargin` from the certified flag.**  The analytic content is entirely in the flag; what
is left are the state's *structural* invariants (`hlen`, `hd`, `hsym`), which the campaign's orbit
supplies unconditionally (`EAudit2M7.hlen_orbitW`, `hD_orbitW`, `Symm31M7.hCsym_orbitW`). -/
theorem pivPsdMargin_of_okCert {dq : ℚ} (hdq : 0 < dq) {s : RSt}
    (hlen : stN s ≤ (stX s).length) (hd : 0 < stD s)
    (hsym : ∀ i j, QMCLeafB.PivExact.matOf (stN s) (stX s) i j
      = QMCLeafB.PivExact.matOf (stN s) (stX s) j i)
    (hmu : 0 ≤ stMu s) (h : okCert dq s = true) :
    QMCLeafB.ContractM7.PivPsdMargin s dq := by
  have h' := h
  simp only [okCert, Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨⟨hpiv, hgrid⟩, hbox⟩ := h'
  have hpiv' : (pivAns s).1 = false := by simpa using hpiv
  exact QMCLeafB.LdltCertM5.pivPsdMargin_of_tolerance (s := s)
    hlen hd hsym (QMCLeafB.LdltCertM5.boxRun_of_boxRunB hmu _ _ hbox) hpiv' hdq hgrid

/-- **`PivPsdMargin` from the measured-error flag** — no grid condition anywhere. -/
theorem pivPsdMargin_of_okCertM {dq ε : ℚ} {s : RSt}
    (hlen : stN s ≤ (stX s).length)
    (hsym : ∀ i j, QMCLeafB.PivExact.matOf (stN s) (stX s) i j
      = QMCLeafB.PivExact.matOf (stN s) (stX s) j i)
    (hε : 0 ≤ ε) (h : okCertM dq ε s = true) :
    QMCLeafB.ContractM7.PivPsdMargin s dq := by
  have h' := h
  simp only [okCertM, Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨⟨hpiv, hbud⟩, hev⟩ := h'
  have hpiv' : (pivAns s).1 = false := by simpa using hpiv
  exact QMCLeafB.LdltCertM5.pivPsdMargin_of_measured (s := s)
    hlen hsym hε (QMCLeafB.LdltCertM5.evRun_of_evRunB hε _ _ hev) hpiv' hbud

/-! ## 7.  `Hpsd` at a *certified* program, with no side conditions

The two flags are the whole content of gate (G) and gate (B): a program whose `ok` answer carries
either one satisfies `Hpsd` outright.  So the `hok` half of the residual has exactly two possible
shapes — enlarge `stD` and check (G), or certify the descent's own error and check the budget — and
in both the theorem is free.  What is *not* free is the question whether the `ok` test can still
report `true` often enough (`hcomplete`'s remit): a stricter `ok` test makes `hcomplete` harder. -/

/-- **`Hpsd` from a certified `ok` test** (grid form: the `stD` enlargement route). -/
theorem hpsd_of_certified_ok
    (hcert : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (sOf G t k) = true →
      okCert (QMCLeafB.RundataParams.dqShallow G) (sOf G t k) = true)
    (hmu : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 0 ≤ stMu (sOf G t k)) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (sOf G t k) = true →
      ∀ x : Fin G.n → ℚ,
        -(QMCLeafB.RundataParams.dqShallow G / 2) * (∑ i, x i ^ 2)
          ≤ QMCLeafB.SepOracle.qf (QMCLeafB.StateDiag.stMat G.n (stX (sOf G t k))) x := by
  have hgrid : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (sOf G t k) = true →
      GridGate G t k := by
    intro G t k hn hint hk hok
    have h' := hcert G t k hn hint hk hok
    simp only [okCert, Bool.and_eq_true, decide_eq_true_eq] at h'
    exact h'.1.2
  have hbox : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (sOf G t k) = true →
      BoxGate G t k := by
    intro G t k hn hint hk hok
    have h' := hcert G t k hn hint hk hok
    simp only [okCert, Bool.and_eq_true, decide_eq_true_eq] at h'
    exact QMCLeafB.LdltCertM5.boxRun_of_boxRunB (hmu G t k) _ _ h'.2
  exact hpsd_of_gates hgrid hbox

/-- **`Hpsd` from an error-certified `ok` test** (measured-error route: no grid enlargement). -/
theorem hpsd_of_certified_ok_measured (ε : ℚ) (hε : 0 ≤ ε)
    (hcert : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (sOf G t k) = true →
      okCertM (QMCLeafB.RundataParams.dqShallow G) ε (sOf G t k) = true) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (sOf G t k) = true →
      ∀ x : Fin G.n → ℚ,
        -(QMCLeafB.RundataParams.dqShallow G / 2) * (∑ i, x i ^ 2)
          ≤ QMCLeafB.SepOracle.qf (QMCLeafB.StateDiag.stMat G.n (stX (sOf G t k))) x := by
  intro G t k hn hint hk hok
  have hm := pivPsdMargin_of_okCertM
    (EAudit2M7.hlen_orbitW (QMCLeafB.FinalStroke.noTape G t) k)
    (orbit_symm G t k) hε (hcert G t k hn hint hk hok)
  have hN : stN (sOf G t k) = G.n := EAudit2M7.hn_orbitW _ k
  have key : ∀ x : Fin (stN (sOf G t k)) → ℚ,
      -(QMCLeafB.RundataParams.dqShallow G / 2) * (∑ i, x i ^ 2)
        ≤ QMCLeafB.SepOracle.qf
            (QMCLeafB.StateDiag.stMat (stN (sOf G t k)) (stX (sOf G t k))) x := by
    intro x
    rw [stMat_eq_toMatrix]
    exact hm x
  exact hN ▸ key

/-! ## 8.  **FALSIFICATION AT THE CAMPAIGN'S OWN GRID: the `2n²/d` exchange rate is attained at
unit-diagonal states**

`§2` is the *only* bridge from the descent's answer to the margin, and its rate is `2n²/d`.  The
question this section settles: at an `ok` state the block is **unit-diagonal** (`dvR = 0`),
symmetric, on the campaign's grid `stD = gridOf n = (n+1)⁴` and in the campaign's box
`stMu = MOf n = 2n² + 2`.  Could *those* facts — plus the pivot answer `false`, plus the no-clip
tracker `BoxRun` — yield the campaign's margin at `dqShallow < 1/360000`?

**No.**  At `n = 3` (`gridOf 3 = 256`, `MOf 3 = 20`) the state below has every one of those
properties: unit diagonal, symmetric, all entries on `(1/256)ℤ`, in the box `[-20,20]`, its descent
answers `ok`, and its trajectory never clips (`BoxRun` machine-checked at all three levels).  Its
block still has a violated direction of size `753/128` at norm squared `1658`, so the margin clause
fails at **every** `δ < 753/106112 ≈ 7.1·10⁻³` — four orders of magnitude above `dqShallow`
(`< 1/360000` at every interior point).

The mechanism is the ordinary truncation: the second level's exact Schur complement is
`-149/44800 ≈ -3.3·10⁻³`, and `snapDiv 256` truncates it to `0` (step 2 below, machine-checked).
That is precisely the truncation the `2n²/d` rate is priced for, and it survives both the unit
diagonal and the no-clip tracker.

**Consequence for `Hpsd`.**  `Hpsd` at the packed program is *not* a consequence of the `ok` state's
own data — diagonal, symmetry, grid, box, pivot answer, no-clip tracker included.  Any proof of it at
that program must use the orbit's specific geometry; the two routes that do not are the `stD`
enlargement (§5, gate (G) at `≈ 2n²/dqShallow ≈ 3·10⁶` at `n = 2`) and the measured-error certificate
(§4, gate at the run's own `ε`).  And the enlargement is not cosmetic: gate (B) must be re-established
at the new grid, where an exact Schur value with pivot `≈ 1/d` can reach `μ + μ²·d`. -/

/-- The state's flat code: `1` on the diagonal, `9/16, 55/256, -177/256` off it — symmetric,
unit-diagonal, on the campaign's `n = 3` grid `(1/256)ℤ`, and inside the `n = 3` box `20`. -/
def X256 : List ℚ := [1, 9/16, 55/256, 9/16, 1, -177/256, 55/256, -177/256, 1]

/-- The falsifying state: `n = 3`, `μ = 20 = MOf 3`, `d = 256 = gridOf 3` — the campaign's own box
and grid for the order `3`. -/
def sCamp : RSt := mkSt 3 [] X256 0 20 256 [] []

theorem idxs_X256 : QMCLeafB.RoundProgram.idxs (3, X256) = [0, 1, 2] := by
  unfold QMCLeafB.RoundProgram.idxs
  decide

theorem toRows_X256 :
    QMCLeafB.RoundProgram.toRows (3, X256)
      = [[1, 9/16, 55/256], [9/16, 1, -177/256], [55/256, -177/256, 1]] := by
  unfold QMCLeafB.RoundProgram.toRows QMCLeafB.RoundProgram.rowOf
  rw [idxs_X256]
  rfl

theorem matrix_sCamp :
    MatQ.toMatrix 3 X256
      = !![(1 : ℚ), 9/16, 55/256; 9/16, 1, -177/256; 55/256, -177/256, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [MatQ.toMatrix, MatQ.entry, X256]

theorem symm_sCamp : (MatQ.toMatrix 3 X256)ᵀ = MatQ.toMatrix 3 X256 := by
  rw [matrix_sCamp]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **The state is exactly unit-diagonal in the campaign's own reading** (`dvR = 0`). -/
theorem dvR_sCamp : dvR sCamp = 0 := by
  show QMCLeafB.RoundProgram.diagSumV (3, X256) = 0
  unfold QMCLeafB.RoundProgram.diagSumV
  rw [idxs_X256]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have e0 : QMCLeafB.RoundProgram.entV (3, X256) 0 0 = 1 := rfl
  have e1 : QMCLeafB.RoundProgram.entV (3, X256) 1 1 = 1 := rfl
  have e2 : QMCLeafB.RoundProgram.entV (3, X256) 2 2 = 1 := rfl
  rw [e0, e1, e2]
  norm_num [QMCLeafB.RoundProgram.absq]

/-! ### 8a.  The descent, step by step (the second step truncates `-149/44800` to `0`) -/

theorem pivStepL_X256_step1 :
    QMCLeafB.RoundProgram.pivStepL
        ((20, 256), ([[1, 9/16, 55/256], [9/16, 1, -177/256], [55/256, -177/256, 1]],
          ([] : QMCLeafB.PivotProgram.Acc)))
      = Sum.inr ((20, 256), ([[175/256, -207/256], [-207/256, 61/64]],
          [(1, [9/16, 55/256])])) := by
  rw [QMCLeafB.RoundProgram.pivStepL_def]
  norm_num [QMCLeafB.PivotProgram.piv, QMCLeafB.PivotProgram.headRowD,
    QMCLeafB.PivotProgram.headTail, List.isEmpty, QMCLeafB.RoundProgram.brSchurL,
    QMCLeafB.PivotProgram.schurRows, QMCLeafB.PivotProgram.schurRowStep, mul_one,
    QMCLeafB.RoundProgram.nrmRows, QMCLeafB.RoundProgram.nrmRow, QMCLeafB.RoundProgram.nrmQ,
    QMCLeafB.RoundProgram.nrmAcc, QMCLeafB.RoundProgram.nrmPair, QMCLeafB.RoundProgram.clipRat,
    QMCLeafB.RoundProgram.inBoxR, QMCLeafB.RoundPolySnap.snapDiv,
    QMCLeafB.RoundPolySnap.snapTrunc, OAI.MetricKMedian.Binary.Signed.value,
    OAI.MetricKMedian.Binary.Signed.sign]

/-- **The truncation**: the exact Schur complement is `-149/44800`, the snapped value is `0`. -/
theorem schur_X256_step2 :
    QMCLeafB.PivotProgram.schurRows [[175/256, -207/256], [-207/256, 61/64]]
      = [[-149/44800]] := by
  norm_num [QMCLeafB.PivotProgram.schurRows, QMCLeafB.PivotProgram.schurRowStep,
    QMCLeafB.PivotProgram.piv, QMCLeafB.PivotProgram.headRowD,
    QMCLeafB.PivotProgram.headTail]

theorem pivStepL_X256_step2 :
    QMCLeafB.RoundProgram.pivStepL
        ((20, 256), ([[175/256, -207/256], [-207/256, 61/64]], [(1, [9/16, 55/256])]))
      = Sum.inr ((20, 256), ([[0]], [(175/256, [-207/256]), (1, [9/16, 55/256])])) := by
  rw [QMCLeafB.RoundProgram.pivStepL_def]
  norm_num [QMCLeafB.PivotProgram.piv, QMCLeafB.PivotProgram.headRowD,
    QMCLeafB.PivotProgram.headTail, List.isEmpty, QMCLeafB.RoundProgram.brSchurL,
    QMCLeafB.PivotProgram.schurRows, QMCLeafB.PivotProgram.schurRowStep, mul_one,
    QMCLeafB.RoundProgram.nrmRows, QMCLeafB.RoundProgram.nrmRow, QMCLeafB.RoundProgram.nrmQ,
    QMCLeafB.RoundProgram.nrmAcc, QMCLeafB.RoundProgram.nrmPair, QMCLeafB.RoundProgram.clipRat,
    QMCLeafB.RoundProgram.inBoxR, QMCLeafB.RoundPolySnap.snapDiv,
    QMCLeafB.RoundPolySnap.snapTrunc, OAI.MetricKMedian.Binary.Signed.value,
    OAI.MetricKMedian.Binary.Signed.sign]

theorem pivStepL_X256_step3 :
    QMCLeafB.RoundProgram.pivStepL
        ((20, 256), ([[0]], [(175/256, [-207/256]), (1, [9/16, 55/256])]))
      = Sum.inr ((20, 256), ([], [(175/256, [-207/256]), (1, [9/16, 55/256])])) := by
  rw [QMCLeafB.RoundProgram.pivStepL_def]
  norm_num [QMCLeafB.PivotProgram.piv, QMCLeafB.PivotProgram.headRowD,
    QMCLeafB.PivotProgram.headTail, List.isEmpty, QMCLeafB.PivotProgram.rowSq,
    QMCLeafB.RoundProgram.brDropL, QMCLeafB.PivotProgram.dropRows,
    QMCLeafB.RoundProgram.nrmRows, QMCLeafB.RoundProgram.nrmRow, QMCLeafB.RoundProgram.nrmQ,
    QMCLeafB.RoundProgram.nrmAcc, QMCLeafB.RoundProgram.nrmPair, QMCLeafB.RoundProgram.clipRat,
    QMCLeafB.RoundProgram.inBoxR, QMCLeafB.RoundPolySnap.snapDiv,
    QMCLeafB.RoundPolySnap.snapTrunc, OAI.MetricKMedian.Binary.Signed.value,
    OAI.MetricKMedian.Binary.Signed.sign]

/-- **The descent answers `ok` at the campaign's own grid and box.** -/
theorem runPivL_X256 :
    QMCLeafB.RoundProgram.runPivL
        ((20, 256), (QMCLeafB.RoundProgram.toRows (3, X256),
          ([] : QMCLeafB.PivotProgram.Acc)))
      = (false, []) := by
  rw [toRows_X256]
  have hlen : ([[1, 9/16, 55/256], [9/16, 1, -177/256], [55/256, -177/256, 1]] :
      QMCLeafB.PivotProgram.Rows).length = 3 := rfl
  rw [QMCLeafB.RoundProgram.runPivL, hlen]
  show (match QMCLeafB.RoundProgram.pivStepL ((20, 256),
      ([[1, 9/16, 55/256], [9/16, 1, -177/256], [55/256, -177/256, 1]],
        ([] : QMCLeafB.PivotProgram.Acc))) with
    | Sum.inl a => a
    | Sum.inr p' => QMCLeafB.RoundProgram.runPivLFuel 2 p') = (false, [])
  rw [pivStepL_X256_step1]
  show (match QMCLeafB.RoundProgram.pivStepL ((20, 256),
      ([[175/256, -207/256], [-207/256, 61/64]], [(1, [9/16, 55/256])])) with
    | Sum.inl a => a
    | Sum.inr p' => QMCLeafB.RoundProgram.runPivLFuel 1 p') = (false, [])
  rw [pivStepL_X256_step2]
  show (match QMCLeafB.RoundProgram.pivStepL ((20, 256),
      ([[0]], [(175/256, [-207/256]), (1, [9/16, 55/256])])) with
    | Sum.inl a => a
    | Sum.inr p' => QMCLeafB.RoundProgram.runPivLFuel 0 p') = (false, [])
  rw [pivStepL_X256_step3]
  rfl

theorem pivAns_sCamp : (pivAns sCamp).1 = false := by
  rw [QMCLeafB.RoundProgram.pivAns]
  show (QMCLeafB.RoundProgram.runPivL
    ((20, 256), (QMCLeafB.RoundProgram.toRows (3, X256),
      ([] : QMCLeafB.PivotProgram.Acc)))).1 = false
  rw [runPivL_X256]

/-! ### 8b.  The no-clip tracker holds on the whole trajectory -/

theorem nrmBox_of_bound {rows : QMCLeafB.PivotProgram.Rows} {mu : ℚ} (hmu : 0 ≤ mu)
    (h : ∀ (r : List ℚ), r ∈ rows → ∀ q ∈ r, |q| ≤ mu) :
    QMCLeafB.LdltCertM5.NrmBox mu rows := by
  intro i j
  have key : ∀ (l : List ℚ) (k : ℕ), (∀ q ∈ l, |q| ≤ mu) → |l.getD k 0| ≤ mu := by
    intro l k hl
    by_cases hk : k < l.length
    · rw [List.getD_eq_getElem l 0 hk]
      exact hl _ (List.getElem_mem hk)
    · rw [List.getD_eq_default l 0 (by omega)]
      simpa using hmu
  by_cases hi : i < rows.length
  · rw [List.getD_eq_getElem rows [] hi]
    exact key _ j (h _ (List.getElem_mem hi))
  · rw [List.getD_eq_default rows [] (by omega)]
    simpa using hmu

theorem nrmBox_two {mu : ℚ} (hmu : 0 ≤ mu) (p q r s : ℚ)
    (hp : |p| ≤ mu) (hq : |q| ≤ mu) (hr : |r| ≤ mu) (hs : |s| ≤ mu) :
    QMCLeafB.LdltCertM5.NrmBox mu ([[p, q], [r, s]] : QMCLeafB.PivotProgram.Rows) := by
  apply nrmBox_of_bound hmu
  intro row hrow x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hrow
  rcases hrow with rfl | rfl
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · simpa using hp
    · simpa using hq
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · simpa using hr
    · simpa using hs

theorem nrmBox_one {mu : ℚ} (hmu : 0 ≤ mu) (p : ℚ) (hp : |p| ≤ mu) :
    QMCLeafB.LdltCertM5.NrmBox mu ([[p]] : QMCLeafB.PivotProgram.Rows) := by
  apply nrmBox_of_bound hmu
  intro row hrow x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hrow
  subst hrow
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  subst hx
  simpa using hp

theorem boxRun_sCamp :
    QMCLeafB.LdltCertM5.BoxRun 20 3
      ((20, 256), (QMCLeafB.RoundProgram.toRows (3, X256),
        ([] : QMCLeafB.PivotProgram.Acc))) := by
  rw [toRows_X256]
  show QMCLeafB.LdltCertM5.NrmBox 20
        (QMCLeafB.PivotProgram.schurRows
          [[1, 9/16, 55/256], [9/16, 1, -177/256], [55/256, -177/256, 1]])
      ∧ QMCLeafB.LdltCertM5.NrmBox 20
        (QMCLeafB.PivotProgram.dropRows
          [[1, 9/16, 55/256], [9/16, 1, -177/256], [55/256, -177/256, 1]])
      ∧ QMCLeafB.LdltCertM5.BoxRun 20 2
          (QMCLeafB.LdltCertM5.nextL
            ((20, 256), ([[1, 9/16, 55/256], [9/16, 1, -177/256],
              [55/256, -177/256, 1]], ([] : QMCLeafB.PivotProgram.Acc))))
  have hs : QMCLeafB.PivotProgram.schurRows
      [[1, 9/16, 55/256], [9/16, 1, -177/256], [55/256, -177/256, 1]]
      = [[175/256, -3327/4096], [-3327/4096, 62511/65536]] := by
    norm_num [QMCLeafB.PivotProgram.schurRows, QMCLeafB.PivotProgram.schurRowStep,
      QMCLeafB.PivotProgram.piv, QMCLeafB.PivotProgram.headRowD,
      QMCLeafB.PivotProgram.headTail]
  have hd : QMCLeafB.PivotProgram.dropRows
      [[1, 9/16, 55/256], [9/16, 1, -177/256], [55/256, -177/256, 1]]
      = [[1, -177/256], [-177/256, 1]] := rfl
  have hn : QMCLeafB.LdltCertM5.nextL
      ((20, 256), ([[1, 9/16, 55/256], [9/16, 1, -177/256], [55/256, -177/256, 1]],
        ([] : QMCLeafB.PivotProgram.Acc)))
      = ((20, 256), ([[175/256, -207/256], [-207/256, 61/64]],
          [(1, [9/16, 55/256])])) := by
    unfold QMCLeafB.LdltCertM5.nextL
    rw [show QMCLeafB.RoundProgram.pivStepL ((20, 256),
        ([[1, 9/16, 55/256], [9/16, 1, -177/256], [55/256, -177/256, 1]],
          ([] : QMCLeafB.PivotProgram.Acc))) = _ from pivStepL_X256_step1]
  rw [hs, hd, hn]
  refine ⟨nrmBox_two (by norm_num) _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), ?_, ?_⟩
  · exact nrmBox_two (by norm_num) _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · show QMCLeafB.LdltCertM5.NrmBox 20
          (QMCLeafB.PivotProgram.schurRows [[175/256, -207/256], [-207/256, 61/64]])
        ∧ QMCLeafB.LdltCertM5.NrmBox 20
          (QMCLeafB.PivotProgram.dropRows [[175/256, -207/256], [-207/256, 61/64]])
        ∧ QMCLeafB.LdltCertM5.BoxRun 20 1
            (QMCLeafB.LdltCertM5.nextL ((20, 256),
              ([[175/256, -207/256], [-207/256, 61/64]], [(1, [9/16, 55/256])])))
    have hd2 : QMCLeafB.PivotProgram.dropRows [[175/256, -207/256], [-207/256, 61/64]]
        = [[61/64]] := rfl
    have hn2 : QMCLeafB.LdltCertM5.nextL ((20, 256),
        ([[175/256, -207/256], [-207/256, 61/64]], [(1, [9/16, 55/256])]))
        = ((20, 256), ([[0]], [(175/256, [-207/256]), (1, [9/16, 55/256])])) := by
      unfold QMCLeafB.LdltCertM5.nextL
      rw [show QMCLeafB.RoundProgram.pivStepL ((20, 256),
          ([[175/256, -207/256], [-207/256, 61/64]], [(1, [9/16, 55/256])])) = _
          from pivStepL_X256_step2]
    rw [schur_X256_step2, hd2, hn2]
    refine ⟨nrmBox_one (by norm_num) _ (by norm_num), nrmBox_one (by norm_num) _ (by norm_num),
      ?_⟩
    show QMCLeafB.LdltCertM5.NrmBox 20
          (QMCLeafB.PivotProgram.schurRows [[0]])
        ∧ QMCLeafB.LdltCertM5.NrmBox 20
          (QMCLeafB.PivotProgram.dropRows [[0]])
        ∧ QMCLeafB.LdltCertM5.BoxRun 20 0
            (QMCLeafB.LdltCertM5.nextL ((20, 256), ([[0]],
              [(175/256, [-207/256]), (1, [9/16, 55/256])])))
    have hs3 : QMCLeafB.PivotProgram.schurRows [[0]]
        = ([] : QMCLeafB.PivotProgram.Rows) := by
      norm_num [QMCLeafB.PivotProgram.schurRows, QMCLeafB.PivotProgram.schurRowStep,
        QMCLeafB.PivotProgram.piv, QMCLeafB.PivotProgram.headRowD,
        QMCLeafB.PivotProgram.headTail]
    have hd3 : QMCLeafB.PivotProgram.dropRows [[0]]
        = ([] : QMCLeafB.PivotProgram.Rows) := rfl
    rw [hs3, hd3]
    refine ⟨?_, ?_, trivial⟩
    · apply nrmBox_of_bound (by norm_num)
      intro r hr
      simp at hr
    · apply nrmBox_of_bound (by norm_num)
      intro r hr
      simp at hr

/-! ### 8c.  The margin fails at the campaign's tolerance -/

/-- The violated direction: `(20, -27, -23)`, of norm squared `1658`. -/
theorem qf_sCamp_witness :
    QMCLeafB.SepOracle.qf (MatQ.toMatrix 3 X256)
      (fun i : Fin 3 => if (i : ℕ) = 0 then (20 : ℚ) else if (i : ℕ) = 1 then -27 else -23)
      = -753/128 := by
  rw [QMCLeafB.SepOracle.qf_eq_sum]
  simp [MatQ.toMatrix, MatQ.entry, X256, Fin.sum_univ_three]
  norm_num

theorem sum_sq_witness :
    (∑ i : Fin 3, ((if (i : ℕ) = 0 then (20 : ℚ) else if (i : ℕ) = 1 then -27 else -23)) ^ 2)
      = 1658 := by
  rw [Fin.sum_univ_three]
  norm_num

/-- **The margin clause fails by four orders of magnitude.**  `PivPsdMargin` fails at this state for
every `δ ≤ 1/1000` (`753/106112 ≈ 7.1·10⁻³`), in particular at the campaign's `dqShallow`. -/
theorem not_pivPsdMargin_sCamp {δ : ℚ} (hδ : δ ≤ 1/1000) :
    ¬ QMCLeafB.ContractM7.PivPsdMargin sCamp δ := by
  intro hm
  have hm' : ∀ x : Fin 3 → ℚ, -(δ / 2) * (∑ i, x i ^ 2)
      ≤ QMCLeafB.SepOracle.qf (MatQ.toMatrix 3 X256) x := by
    intro x
    exact hm x
  have h0 := hm' (fun i : Fin 3 =>
    if (i : ℕ) = 0 then (20 : ℚ) else if (i : ℕ) = 1 then -27 else -23)
  rw [qf_sCamp_witness, sum_sq_witness] at h0
  nlinarith

/-! ### 8d.  The falsification, as the failure of the state-level implication -/

theorem sCamp_gates :
    stN sCamp = 3 ∧ stD sCamp = 256 ∧ stMu sCamp = 20 ∧ dvR sCamp = 0
      ∧ (MatQ.toMatrix 3 X256)ᵀ = MatQ.toMatrix 3 X256
      ∧ (pivAns sCamp).1 = false
      ∧ QMCLeafB.LdltCertM5.BoxRun (stMu sCamp) (stN sCamp)
          ((stMu sCamp, stD sCamp), (toRows (stN sCamp, stX sCamp), [])) := by
  refine ⟨rfl, rfl, rfl, dvR_sCamp, symm_sCamp, pivAns_sCamp, ?_⟩
  exact boxRun_sCamp

/-- **The state-level implication is FALSE at the campaign's own grid and box.**  A proof of `Hpsd`
at the packed program cannot go through the `ok` state's own data: unit diagonal + symmetry + the
packed grid + the packed box + the answer `false` + `BoxRun` leave `7.1·10⁻³` of margin unexploited,
four orders of magnitude above what `hok` needs.  (Reachability of such a state is *not* claimed —
that is the orbit-geometry question, and it is what any proof of `Hpsd` here must settle.) -/
theorem not_margin_from_state_data :
    ¬ (∀ (s : RSt), stN s = 3 → stD s = 256 → stMu s = 20 → dvR s = 0 →
        (MatQ.toMatrix (stN s) (stX s))ᵀ = MatQ.toMatrix (stN s) (stX s) →
        (pivAns s).1 = false →
        QMCLeafB.LdltCertM5.BoxRun (stMu s) (stN s)
          ((stMu s, stD s), (toRows (stN s, stX s), [])) →
        QMCLeafB.ContractM7.PivPsdMargin s (1/1000)) := by
  intro h
  exact not_pivPsdMargin_sCamp (le_refl (1/1000))
    (h sCamp rfl rfl rfl dvR_sCamp symm_sCamp pivAns_sCamp boxRun_sCamp)

/-! ## 9.  Arithmetic for the enlargement lane: the exact requirement is `n²·(720000 + 80000/Rq)`

`gridGate_fails_pinned` says the packed grid cannot pass gate (G); `exists_grid` says some grid can.
The enlargement's *program* needs the number, so §9 records it in closed form: gate (G) at the
campaign's own `dqShallow` asks for

    stD  ≥  2n²/dqShallow  =  n²·(720000 + 80000/Rq).

(`dqShallow = Rq/(40000(9Rq+1))`.)  So `stD` must be the *ceiling* of a rational read off the
request — the ceiling is what `RoundPolySnap`'s rounding machinery provides — and its bit length is
`≈ 17 + 2·log₂ n + bitCost(1/Rq)`, which is inside the campaign count's `(n + 27)` factor. -/

/-- `dqShallow` in closed form. -/
theorem dqShallow_eq (G : QuantumMaxCutEnergy.Input) (hRq : QMCLeafB.EngineRuntime.Rq G ≠ 0) :
    QMCLeafB.RundataParams.dqShallow G
      = QMCLeafB.EngineRuntime.Rq G
          / (40000 * (9 * QMCLeafB.EngineRuntime.Rq G + 1)) := by
  unfold QMCLeafB.RundataParams.dqShallow QMCLeafB.RundataParams.dqShallowCore
  rw [if_neg hRq]
  have heps : QMCLeafB.RundataCert.eps G = QMCLeafB.EngineRuntime.Rq G / 40000 := rfl
  rw [heps]
  field_simp

/-- **The exact grid requirement.** -/
theorem two_nsq_over_dq (G : QuantumMaxCutEnergy.Input) (hRq : QMCLeafB.EngineRuntime.Rq G ≠ 0) :
    2 * (G.n : ℚ) * (G.n : ℚ) / QMCLeafB.RundataParams.dqShallow G
      = 720000 * (G.n : ℚ) * (G.n : ℚ)
        + 80000 * (G.n : ℚ) * (G.n : ℚ) / QMCLeafB.EngineRuntime.Rq G := by
  rw [dqShallow_eq G hRq]
  have hRqpos : (0 : ℚ) < QMCLeafB.EngineRuntime.Rq G :=
    lt_of_le_of_ne (QMCLeafB.RundataArith.Rq_nonneg G) (Ne.symm hRq)
  field_simp
  ring

/-- **The grid requirement, lower bound**: any grid passing gate (G) is at least `720000·n²`, which
exceeds `gridOf n = (n+1)⁴` up to `n ≈ 300`. -/
theorem grid_requirement_ge (G : QuantumMaxCutEnergy.Input) (hRq : QMCLeafB.EngineRuntime.Rq G ≠ 0) :
    720000 * (G.n : ℚ) * (G.n : ℚ)
      ≤ 2 * (G.n : ℚ) * (G.n : ℚ) / QMCLeafB.RundataParams.dqShallow G := by
  rw [two_nsq_over_dq G hRq]
  have hRqpos : (0 : ℚ) < QMCLeafB.EngineRuntime.Rq G :=
    lt_of_le_of_ne (QMCLeafB.RundataArith.Rq_nonneg G) (Ne.symm hRq)
  have hnn : (0 : ℚ) ≤ (G.n : ℚ) * (G.n : ℚ) := by positivity
  have h2 : (0 : ℚ) ≤ 80000 * (G.n : ℚ) * (G.n : ℚ) / QMCLeafB.EngineRuntime.Rq G := by
    positivity
  linarith

/-! ## 10.  **The program fork**: `MechM6`'s leaf stroke and `HokRedM7`'s `hok` are stated at
DIFFERENT programs

`MechM6.leaf_of_hok_and_complete` takes its `hok` slot at `bit0 = loopBit InitDq.init0
LedgerW.roundWG verdict Tbc2`, while `HokRedM7.hok_of_psd` (and hence `hpsd_of_gates` above)
produces `hok` at `EAuditM7.Bit = loopBit RStInit.init0 OkLower.roundW verdict Tbc2`.  The two inits
are **not equal**: `stMu` is `2n² + 2` at `RStInit.init0` (`MOf`) but `2n² + 2·dqShallow²` at
`InitDq.init0`, and the initial block's diagonal is `1/MOf` versus `1/(2n² + 2dqShallow²)` — so the
orbits, and hence the bits, are different functions as stated.

The *round* registers do agree on the campaign's orbit: `roundWG = roundW` below the slack on a
normalised state, and `roundW` preserves normalisation (§11a).  So bridging needs either (i) an orbit
agreement theorem for the two inits (they differ only in `stMu` and the identity scalar — so it holds
whenever neither orbit's clip fires, i.e. again a no-clip condition), or (ii) a port of the chain to
`InitDq.init0`, which §11 does for the two gates. -/

/-- **The inits differ** whenever the tolerance is not `1`. -/
theorem stMu_initDq_ne_initRSt (p : QMCLeafB.FuelWire.Pkg)
    (hdq : QMCLeafB.RundataParams.dqShallow p.1.1 ≠ 1) :
    stMu (QMCLeafB.InitDq.init0 p) ≠ stMu (QMCLeafB.RStInit.init0 p) := by
  rw [QMCLeafB.InitDq.stMu_init0_dq, QMCLeafB.RStInit.stMu_init0_eq]
  have hM : QMCLeafB.InitVerdict.MOf p.1.1.n
      = 2 * (p.1.1.n : ℚ) * (p.1.1.n : ℚ) + 2 := by
    unfold QMCLeafB.InitVerdict.MOf QMCLeafB.InitVerdict.dqV
    ring
  rw [hM]
  intro h
  apply hdq
  have h2 : QMCLeafB.InitDq.dqOf p.1.1 = 1 := by
    nlinarith [QMCLeafB.InitDq.dqOf_pos p.1.1]
  exact h2

/-! ## 11.  The chain at the campaign's own program: `InitDq.init0` + `roundW`, then `roundWG`

§3's gates are re-derived at `jOf G t k := roundW^[k] (InitDq.init0 (noTape G t))` — the init
`MechM6` actually uses — and then transported to `roundWG`'s orbit on the interior. -/

/-- The campaign program's orbit: `InitDq.init0` with the lower-body round. -/
abbrev jOf (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) : RSt :=
  QMCLeafB.OkLower.roundW^[k] (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t))

theorem jN (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) : stN (jOf G t k) = G.n := by
  have h : stN (jOf G t k) = stN (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)) :=
    EAudit2M7.stN_orbitW _ k
  rw [h, QMCLeafB.InitDq.stN_init0]
  rfl

theorem jT (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) : stT (jOf G t k) = t := by
  have h : stT (jOf G t k) = stT (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)) :=
    EAudit2M7.stT_orbitW _ k
  rw [h, QMCLeafB.InitDq.stT_init0]
  rfl

theorem jDval (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    stD (jOf G t k) = QMCLeafB.InitVerdict.gridOf G.n := by
  have h : stD (jOf G t k) = stD (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)) :=
    EAudit2M7.stD_orbitW _ k
  rw [h, QMCLeafB.InitDq.stD_init0, QMCLeafB.InitDq.stN_init0]
  rfl

theorem jlen (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    stN (jOf G t k) ≤ (stX (jOf G t k)).length := by
  have h := EAudit2M7.stX_length_orbitW
    (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t))
    (QMCLeafB.InitDq.init_normalised (QMCLeafB.FinalStroke.noTape G t)) k
  rw [h]
  exact Nat.le_mul_self _

theorem jDpos (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) : 0 < stD (jOf G t k) := by
  rw [jDval]
  unfold QMCLeafB.InitVerdict.gridOf
  positivity

/-- **`epsOf` at the campaign program's init** — the same weight code as `RStInit.init0`'s. -/
theorem jeps_init (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.RoundT.epsOf (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t))
      = QMCLeafB.EngineRuntime.Rq G / 40000 := by
  have h2 : QMCLeafB.RoundT.epsOf (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t))
      = QMCLeafB.RoundT.epsOf (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) :=
    QMCLeafB.HtopFinish.epsOf_congr rfl
  rw [h2]
  have h3 := EAudit2M7.epsOf_orbitW (QMCLeafB.FinalStroke.noTape G t) 0
  simpa using h3

theorem jeps (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.RoundT.epsOf (jOf G t k) = QMCLeafB.EngineRuntime.Rq G / 40000 := by
  have h1 := QMCLeafB.HtopFinish.epsOf_congr
    (EAudit2M7.stA_orbitW (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)) k)
  rw [h1, jeps_init]

/-- **`CodeSymm` propagates along `roundW`'s orbit** from any normalised symmetric state. -/
theorem codeSymm_orbit_of_init (s : RSt)
    (hx : (stX s).length = stN s * stN s) (hs : Symm31M7.CodeSymm (stN s) (stX s)) (k : ℕ) :
    Symm31M7.CodeSymm (stN (QMCLeafB.OkLower.roundW^[k] s))
      (stX (QMCLeafB.OkLower.roundW^[k] s)) := by
  induction k with
  | zero => exact hs
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact Symm31M7.codeSymm_roundW _ (EAudit2M7.stX_length_orbitW s hx j) ih

theorem jCodeSymm_zero (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    Symm31M7.CodeSymm (stN (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)))
      (stX (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t))) := by
  show Symm31M7.CodeSymm (stN (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)))
    (stX (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)))
  have hx0 : stX (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t))
      = QMCLeafB.InitVerdict.identVia
          (QMCLeafB.InitVerdict.doubleUp
            (QuantumMaxCutEnergy.encodeRequest (QMCLeafB.FinalStroke.noTape G t).1))
          (QMCNumericRuntime.inputWidth
            (QuantumMaxCutEnergy.encodeRequest (QMCLeafB.FinalStroke.noTape G t).1))
          ((QMCLeafB.InitDq.muOfD (QMCLeafB.FinalStroke.noTape G t))⁻¹) := rfl
  rw [hx0, QMCLeafB.InitVerdict.identVia_eq_mk _ _
    (by rw [QMCLeafB.InitVerdict.doubleUp_length]
        exact Nat.le_trans (QMCLeafB.InitVerdict.inputWidth_le_length _)
          (QMCLeafB.RStInit.self_le_mul_self _))]
  refine Symm31M7.mk_symm (fun i j hi hj => ?_)
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]

theorem jCodeSymm (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    Symm31M7.CodeSymm (stN (jOf G t k)) (stX (jOf G t k)) :=
  codeSymm_orbit_of_init _ (QMCLeafB.InitDq.init_normalised _) (jCodeSymm_zero G t) k

theorem jsymm (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    ∀ i j, QMCLeafB.PivExact.matOf (stN (jOf G t k)) (stX (jOf G t k)) i j
      = QMCLeafB.PivExact.matOf (stN (jOf G t k)) (stX (jOf G t k)) j i :=
  Symm31M7.matOf_symm (jCodeSymm G t k)

theorem jPivAns_false {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hint : AsmM8.Interior G t)
    (k : ℕ) (hok : QMCLeafB.OkLower.okW (jOf G t k) = true) :
    (pivAns (jOf G t k)).1 = false := by
  have hreg : ¬ (0 ≤ stT (jOf G t k) + QMCLeafB.RoundT.epsOf (jOf G t k)) := by
    rw [jT, jeps]
    intro hcon
    have hR : (((t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
        = (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by push_cast; ring
    have h3 : (0 : ℝ) ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
      rw [← hR]
      exact_mod_cast hcon
    have h2 := hint.2
    linarith
  have h1 := QMCLeafB.OkLower.okW_eq_engine (jOf G t k) 0 hreg
  have h2 : QMCLeafB.OkLower.okW (jOf G t k)
      = !((QMCLeafB.OkLower.oracleV (jOf G t k)).1) := by simpa using h1
  rw [h2] at hok
  have hV : (QMCLeafB.OkLower.oracleV (jOf G t k)).1 = false := by simpa using hok
  exact (QMCLeafB.OkLower.oracleV_ok _ hV).2.2

/-- Gate (G) at the campaign program's orbit. -/
def JGridGate (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) : Prop :=
  2 * (stN (jOf G t k) : ℚ) * (stN (jOf G t k) : ℚ)
    ≤ QMCLeafB.RundataParams.dqShallow G * (stD (jOf G t k) : ℚ)

/-- Gate (B) at the campaign program's orbit. -/
def JBoxGate (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) : Prop :=
  QMCLeafB.LdltCertM5.BoxRun (stMu (jOf G t k)) (stN (jOf G t k))
    ((stMu (jOf G t k), stD (jOf G t k)),
      (toRows (stN (jOf G t k), stX (jOf G t k)), ([] : QMCLeafB.PivotProgram.Acc)))

theorem jPivPsdMargin_of_gates {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hint : AsmM8.Interior G t) (k : ℕ)
    (hok : QMCLeafB.OkLower.okW (jOf G t k) = true)
    (hgrid : JGridGate G t k) (hbox : JBoxGate G t k) :
    QMCLeafB.ContractM7.PivPsdMargin (jOf G t k) (QMCLeafB.RundataParams.dqShallow G) :=
  QMCLeafB.LdltCertM5.pivPsdMargin_of_tolerance (s := jOf G t k)
    (jlen G t k) (jDpos G t k) (jsymm G t k) hbox (jPivAns_false hint k hok)
    (QMCLeafB.InitDq.dqOf_pos G) hgrid

/-- **`Hpsd` at the campaign program's own init (`InitDq.init0`), from the two gates.** -/
theorem jHpsd_of_gates
    (hgrid : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (jOf G t k) = true →
      JGridGate G t k)
    (hbox : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (jOf G t k) = true →
      JBoxGate G t k) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (jOf G t k) = true →
      ∀ x : Fin G.n → ℚ,
        -(QMCLeafB.RundataParams.dqShallow G / 2) * (∑ i, x i ^ 2)
          ≤ QMCLeafB.SepOracle.qf (QMCLeafB.StateDiag.stMat G.n (stX (jOf G t k))) x := by
  intro G t k hn hint hk hok
  have hm := jPivPsdMargin_of_gates hint k hok (hgrid G t k hn hint hk hok)
    (hbox G t k hn hint hk hok)
  have hN : stN (jOf G t k) = G.n := jN G t k
  have key : ∀ x : Fin (stN (jOf G t k)) → ℚ,
      -(QMCLeafB.RundataParams.dqShallow G / 2) * (∑ i, x i ^ 2)
        ≤ QMCLeafB.SepOracle.qf
            (QMCLeafB.StateDiag.stMat (stN (jOf G t k)) (stX (jOf G t k))) x := by
    intro x
    rw [stMat_eq_toMatrix]
    exact hm x
  exact hN ▸ key

/-! ### 11a.  `roundWG`'s orbit is `roundW`'s on the interior -/

theorem roundWG_eq_roundW_of_normalised (s : RSt)
    (hreg : ¬ (0 ≤ stT s + QMCLeafB.RoundT.epsOf s))
    (hn : (stX s).length = stN s * stN s) :
    QMCLeafB.LedgerW.roundWG s = QMCLeafB.OkLower.roundW s := by
  rw [QMCLeafB.LedgerW.roundWG_of_interior_normalised s hreg hn]
  unfold QMCLeafB.OkLower.roundW
  rw [if_neg hreg]

theorem roundWG_iterate_eq_roundW (s : RSt)
    (hreg : ¬ (0 ≤ stT s + QMCLeafB.RoundT.epsOf s))
    (hn : (stX s).length = stN s * stN s) :
    ∀ k : ℕ, QMCLeafB.LedgerW.roundWG^[k] s = QMCLeafB.OkLower.roundW^[k] s := by
  intro k
  induction k with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      have hreg' : ¬ (0 ≤ stT (QMCLeafB.OkLower.roundW^[j] s)
          + QMCLeafB.RoundT.epsOf (QMCLeafB.OkLower.roundW^[j] s)) := by
        rw [EAudit2M7.stT_orbitW,
          QMCLeafB.HtopFinish.epsOf_congr (EAudit2M7.stA_orbitW s j)]
        exact hreg
      have hn' : (stX (QMCLeafB.OkLower.roundW^[j] s)).length
          = stN (QMCLeafB.OkLower.roundW^[j] s) * stN (QMCLeafB.OkLower.roundW^[j] s) :=
        EAudit2M7.stX_length_orbitW s hn j
      exact roundWG_eq_roundW_of_normalised _ hreg' hn'

/-- The regime at the campaign program's init, strictly below the slack. -/
theorem kreg (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hint : AsmM8.Interior G t) :
    ¬ (0 ≤ stT (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t))
      + QMCLeafB.RoundT.epsOf (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t))) := by
  rw [QMCLeafB.InitDq.stT_init0, jeps_init]
  intro hcon
  have hR : (((t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
      = (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by push_cast; ring
  have h4 : (0 : ℝ) ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
    rw [← hR]
    exact_mod_cast hcon
  have h2 := hint.2
  linarith

/-- **`Hpsd` at the leaf stroke's program — `InitDq.init0` with `LedgerW.roundWG`** — from the two
gates at that program's `ok` states.  This is the statement `MechM6.leaf_of_hok_and_complete`'s
`hok` slot consumes (up to the `∃`-witness assembly in `hok_of_psd`). -/
theorem kHpsd_of_gates
    (hgrid : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t →
      QMCLeafB.OkLower.okW
        (QMCLeafB.LedgerW.roundWG^[k] (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)))
        = true →
      JGridGate G t k)
    (hbox : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t →
      QMCLeafB.OkLower.okW
        (QMCLeafB.LedgerW.roundWG^[k] (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)))
        = true →
      JBoxGate G t k) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t →
      QMCLeafB.OkLower.okW
        (QMCLeafB.LedgerW.roundWG^[k] (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)))
        = true →
      ∀ x : Fin G.n → ℚ,
        -(QMCLeafB.RundataParams.dqShallow G / 2) * (∑ i, x i ^ 2)
          ≤ QMCLeafB.SepOracle.qf
              (QMCLeafB.StateDiag.stMat G.n
                (stX (QMCLeafB.LedgerW.roundWG^[k]
                  (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t))))) x := by
  intro G t k hn hint hk hok
  have hgrid' : ∀ (G' : QuantumMaxCutEnergy.Input) (t' : ℚ) (k' : ℕ), 2 ≤ G'.n →
      AsmM8.Interior G' t' → k' < AsmM8.Tbc2 G' t' →
      QMCLeafB.OkLower.okW (jOf G' t' k') = true → JGridGate G' t' k' := by
    intro G' t' k' hn' hint' hk' hok'
    have hw := roundWG_iterate_eq_roundW
      (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G' t'))
      (kreg G' t' hint') (QMCLeafB.InitDq.init_normalised _) k'
    simp only [jOf] at hok'
    rw [← hw] at hok'
    exact hgrid G' t' k' hn' hint' hk' hok'
  have hbox' : ∀ (G' : QuantumMaxCutEnergy.Input) (t' : ℚ) (k' : ℕ), 2 ≤ G'.n →
      AsmM8.Interior G' t' → k' < AsmM8.Tbc2 G' t' →
      QMCLeafB.OkLower.okW (jOf G' t' k') = true → JBoxGate G' t' k' := by
    intro G' t' k' hn' hint' hk' hok'
    have hw := roundWG_iterate_eq_roundW
      (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G' t'))
      (kreg G' t' hint') (QMCLeafB.InitDq.init_normalised _) k'
    simp only [jOf] at hok'
    rw [← hw] at hok'
    exact hbox G' t' k' hn' hint' hk' hok'
  have hmain := jHpsd_of_gates hgrid' hbox' G t k hn hint hk
  have hw := roundWG_iterate_eq_roundW
    (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t))
    (kreg G t hint) (QMCLeafB.InitDq.init_normalised _) k
  rw [hw] at hok ⊢
  exact hmain hok

/-! ## 12.  The `∃`-witness half of `hok` at the leaf's own program

`HokRedM7.relaxMem_at_stateW` turns "the pivot test answers `false` at a visited `ok` state" into the
`∃`-certificate.  This section ports it to `InitDq.init0`, which is the initial state
`MechM6.leaf_of_hok_and_complete` uses: the argument is the same, and the only new inputs are the
`InitDq` reads (`massV`, the weight matrix `A`, `dqOf`).  Composed with the assembler's
bit→ok-round extraction this is the literal `hok` slot at `bit0`. -/

theorem jmassV (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.RoundT.massV (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t))
      = QMCLeafB.EngineRuntime.Rq G := by
  have h : QMCLeafB.RoundProgram.stA (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t))
      = QMCLeafB.RoundProgram.stA
          (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) := rfl
  have h2 := EAudit2M7.massV_orbitW (QMCLeafB.FinalStroke.noTape G t) 0
  simp only [Function.iterate_zero] at h2
  unfold QMCLeafB.RoundT.massV at h2 ⊢
  rw [h]
  exact h2

theorem jmassV_orbit (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.RoundT.massV (jOf G t k) = QMCLeafB.EngineRuntime.Rq G := by
  have h : QMCLeafB.RoundT.massV (jOf G t k)
      = QMCLeafB.RoundT.massV (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)) := by
    unfold QMCLeafB.RoundT.massV
    rw [EAudit2M7.stA_orbitW]
  rw [h, jmassV]

theorem jdqOf (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ)
    (hRq : QMCLeafB.EngineRuntime.Rq G ≠ 0) :
    QMCLeafB.OkLower.dqOf (jOf G t k) = QMCLeafB.RundataParams.dqShallow G := by
  have hm : QMCLeafB.RoundT.massV (jOf G t k) = QMCLeafB.EngineRuntime.Rq G := jmassV_orbit G t k
  have he : QMCLeafB.RoundT.epsOf (jOf G t k) = QMCLeafB.EngineRuntime.Rq G / 40000 := jeps G t k
  unfold QMCLeafB.OkLower.dqOf QMCLeafB.RundataParams.dqShallow
    QMCLeafB.RundataParams.dqShallowCore QMCLeafB.RundataCert.eps
  rw [he, hm, if_neg hRq]

theorem jA_toMatrix (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.StateDiag.stMat G.n (stA (jOf G t k)) = QMCLeafB.Finalization.wMatrixQ G := by
  have hA : stA (jOf G t k) = stA (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)) :=
    EAudit2M7.stA_orbitW _ k
  rw [hA]
  show MatQ.toMatrix G.n (stA (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)))
    = QMCLeafB.Finalization.wMatrixQ G
  rw [((MatQ.correct_iff).mp (QMCLeafB.InitDq.stA_correct_noTape G t)).2]
  rfl

theorem jA_length (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    G.n ≤ (stA (jOf G t k)).length := by
  have hA : stA (jOf G t k) = stA (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)) :=
    EAudit2M7.stA_orbitW _ k
  rw [hA, (QMCLeafB.InitDq.stA_correct_noTape G t).1]
  exact Nat.le_mul_self _

theorem jfvR (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.RoundProgram.fvR (jOf G t k)
      = QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G)
          (QMCLeafB.StateDiag.stMat G.n (stX (jOf G t k))) := by
  have hN : stN (jOf G t k) = G.n := jN G t k
  have hlenG : G.n ≤ (stX (jOf G t k)).length := by
    rw [← hN]
    exact jlen G t k
  rw [QMCLeafB.StateDiag.fvR_eq_frob hN (jA_length G t k) hlenG]
  rw [jA_toMatrix]

/-- **The `∃`-certificate at a visited `ok` state of the leaf's own program**, from the PSD clause
at that state. -/
theorem jrelaxMem_at_stateW {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hint : AsmM8.Interior G t) (k : ℕ)
    (hok : QMCLeafB.OkLower.okW (jOf G t k) = true)
    (hpsd : ∀ x : Fin G.n → ℚ,
      -(QMCLeafB.RundataParams.dqShallow G / 2) * (∑ i, x i ^ 2)
        ≤ QMCLeafB.SepOracle.qf (QMCLeafB.StateDiag.stMat G.n (stX (jOf G t k))) x) :
    ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G) := by
  have hN : stN (jOf G t k) = G.n := jN G t k
  have hpos : 0 < QMCLeafB.RoundT.massV (jOf G t k) := by
    rw [jmassV_orbit]
    exact Asm2M8.Rq_pos_of_interior hint
  have hV : (QMCLeafB.OkLower.oracleV (jOf G t k)).1 = false := by
    have hreg : ¬ (0 ≤ stT (jOf G t k) + QMCLeafB.RoundT.epsOf (jOf G t k)) := by
      rw [jT, jeps]
      intro hcon
      have hR : (((t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
          = (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by push_cast; ring
      have h3 : (0 : ℝ) ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
        rw [← hR]
        exact_mod_cast hcon
      have h2 := hint.2
      linarith
    have h1 := QMCLeafB.OkLower.okW_eq_engine (jOf G t k) 0 hreg
    have h2 : QMCLeafB.OkLower.okW (jOf G t k)
        = !((QMCLeafB.OkLower.oracleV (jOf G t k)).1) := by simpa using h1
    rw [h2] at hok
    simpa using hok
  have hRqne : QMCLeafB.EngineRuntime.Rq G ≠ 0 := ne_of_gt (Asm2M8.Rq_pos_of_interior hint)
  have hlenG : G.n ≤ (stX (jOf G t k)).length := by
    rw [← hN]
    exact jlen G t k
  have hpsd' : ∀ x : Fin G.n → ℚ,
      -(QMCLeafB.OkLower.dqOf (jOf G t k) / 2) * (∑ i, x i ^ 2)
        ≤ QMCLeafB.SepOracle.qf
            (QMCLeafB.StateDiag.stMat G.n (stX (jOf G t k))) x := by
    intro x
    rw [jdqOf G t k hRqne]
    exact hpsd x
  have hR := QMCLeafB.StateDiag.relaxMem_of_oracleV_ok_state (n := G.n) hN hlenG
    (jfvR G t k) hV hpos hpsd'
  refine ⟨QMCLeafB.StateDiag.stMat G.n (stX (jOf G t k)), ?_, ?_⟩
  · rw [stMat_eq_toMatrix]
    exact Symm31M7.toMatrix_symm (hN ▸ jCodeSymm G t k)
  · have hlevel : (t - QMCLeafB.RundataCert.eps G)
        = (stT (jOf G t k) - QMCLeafB.RoundT.epsOf (jOf G t k)) := by
      rw [jT, jeps]
      rfl
    have hdqe : QMCLeafB.RundataParams.dqShallow G = QMCLeafB.OkLower.dqOf (jOf G t k) := by
      rw [jdqOf G t k hRqne]
    rw [hlevel, hdqe]
    exact hR

/-- **The `hok` slot's conclusion at the leaf's program, from the two gates plus an `ok` round.** -/
theorem jHok_of_gates
    (hgrid : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (jOf G t k) = true →
      JGridGate G t k)
    (hbox : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n →
      AsmM8.Interior G t → k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (jOf G t k) = true →
      JBoxGate G t k) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      (∃ k, k < AsmM8.Tbc2 G t ∧ QMCLeafB.OkLower.okW (jOf G t k) = true) →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G) := by
  intro G t hn hint hk
  obtain ⟨k, hklt, hok⟩ := hk
  exact jrelaxMem_at_stateW hn hint k hok
    (jHpsd_of_gates hgrid hbox G t k hn hint hklt hok)

end Hpsd32M1

/-! ## Axiom audit (part 3) -/

#print axioms Hpsd32M1.jmassV
#print axioms Hpsd32M1.jmassV_orbit
#print axioms Hpsd32M1.jdqOf
#print axioms Hpsd32M1.jA_toMatrix
#print axioms Hpsd32M1.jA_length
#print axioms Hpsd32M1.jfvR
#print axioms Hpsd32M1.jrelaxMem_at_stateW
#print axioms Hpsd32M1.jHok_of_gates


