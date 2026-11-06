-- Prove2me | Definitions.Def_QMCLeafB_hcb32
-- name    : QMCLeafB_hcb32
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:09:09.293221+00:00
-- url     : https://prove2.me/theorems/753345ff-8acc-4c65-abee-25297c080bf9
-- title:
--   QMCLeafB hcb32
-- statement:
--   # leaf B phase 32 — member m3, direction `hcomplete-ball` (d3)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_mech31
import Definitions.Def_QMCLeafB_bitdec
import Definitions.Def_QMCLeafB_crux_m1
import Definitions.Def_QMCLeafB_dreg
import Definitions.Def_QMCLeafB_traj_m3
/-
# leaf B phase 32 — member m3, direction `hcomplete-ball` (d3)

The phase-31 residual at the campaign program is ONE signature,
`MechM6.leaf_of_hok_and_complete (hok) (hcomplete) : <verbatim d9f601e5>`, with

  `hcomplete : ∀ G t, 2 ≤ G.n → Interior G t → ¬ EmptyBody G t (paramsKbc2 G) → bit0 G t = true`.

This file is the **ball half** of `hcomplete`, delivered separately so that the residual splits
cleanly, together with the two things that make the split honest:

* **§1–§2 the read-out**: `bit0` is *literally* `anyOk` of the flag stream `okW` along the orbit
  `roundW^[k]` of the starting state (`bit0_eq_anyOk`), and on the interior bracket that flag is the
  lower-body oracle's answer, `okW = !(oracleV).1` (`okW_orbit_eq_engine`).  So

    `bit0 G t = false  ⟺  every round below the horizon answers `viol` `

  and `bit0 G t = true ⟺ some round's state carries the three ledger facts
  `dvR = 0`, `fvR ≤ levelOf`, `¬pivAns` — at a level and tolerance that are **constant along the
  orbit** (§2: `levelOf_orbit`, `dqOf_orbit`).  This is the program's own `ok`-semantics, in the
  shape `TrajM3.TestRun.htest` consumes.

* **§3 the split** (`hcomplete_iff_split`): `hcomplete ⟺ HcompleteBall ∧ HcompleteBf`, and the leaf
  verbatim from `hok` + the two halves (`leaf_of_hok_and_split`).

* **§4 falsify-first — the record route is VOID at a ball-bearing body**: on the ball stratum
  `hC` (`bit false ⟹ RunParts`) is *equivalent* to `bit0 G t = true` (`hC_at_ball_iff`), because
  `BallM2.no_runParts_of_ball` turns any record into a true bit.  So the ball half cannot be
  discharged through the thin-band record machinery: it is the program's own reach, and nothing else.

* **§5 both strata are INHABITED** (`split_both_inhabited`): the sliver `(G₁, t₁)` is ball-bearing
  (`sliver_ballBearing`, from `BallM2.sliver_ball_campaign`) and the dreg band `(G₁, tStar + Δ)` is
  ball-free with a nonempty body (`band_ballFree`, from `DregM6.no_ball` + `DregM6.not_bodyEmpty`).
  So the split is two-sided, not a vacuity trick.

* **§6 the ball half's exact remaining content** (`bit_true_at_ball_of_cutslots`): at a ball-bearing
  body, a false bit together with the round's own cut-data slots (`CutSlots`, the nine engine slots
  of `CruxM1.allFalseParts`) is contradictory.  So `hcomplete` on the ball stratum is exactly the
  **transcript identification** — that the states of the run, read as cut data, satisfy the engine's
  ellipsoid recursion — and no search-reach statement at all.

Discipline: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; `#print axioms` at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace Hcb32M3

open QuantumMaxCutEnergy

/-! ## 0.  Notation -/

/-- The program's bit at the campaign program `(RSt, InitDq.init0, LedgerW.roundWG,
RoundProgram.verdict, Tbc2)` — `MechM6.bit0`, spelled again so this file stands alone in its cone. -/
abbrev camBit : QuantumMaxCutEnergy.Input → ℚ → Bool := QMCLeafB.MechM6.bit0

/-- The tape-free starting state at `(G,t)`. -/
def s0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) : QMCLeafB.RoundProgram.RSt :=
  QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)

/-- The campaign parameter family. -/
abbrev Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G :=
  QMCLeafB.UnionShallow.paramsKbc2

/-! ## 1.  `bit0` is `anyOk` of the `okW` stream along the orbit -/

theorem stOks_s0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.RoundProgram.stOks (s0 G t) = [] :=
  QMCLeafB.InitDq.stOks_init0 _

theorem normalised_s0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    (QMCLeafB.RoundProgram.stX (s0 G t)).length
      = QMCLeafB.RoundProgram.stN (s0 G t) * QMCLeafB.RoundProgram.stN (s0 G t) :=
  QMCLeafB.InitDq.init_normalised _

theorem stT_s0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.RoundProgram.stT (s0 G t) = t :=
  QMCLeafB.InitDq.stT_init0 _

theorem epsOf_s0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.RoundT.epsOf (s0 G t) = QMCLeafB.EngineRuntime.Rq G / 40000 :=
  QMCLeafB.AssemblyM5.epsOf_init0_any _

theorem massV_s0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.RoundT.massV (s0 G t) = QMCLeafB.EngineRuntime.Rq G := by
  have h := QMCLeafB.AssemblyM5.epsOf_init0_any (QMCLeafB.FinalStroke.noTape G t)
  have h' : QMCLeafB.RoundT.massV (s0 G t) * (1 / 40000)
      = QMCLeafB.EngineRuntime.Rq G / 40000 := by
    simpa [s0, QMCLeafB.RoundT.epsOf] using h
  linarith

theorem dqOf_s0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.OkLower.dqOf (s0 G t)
      = (QMCLeafB.EngineRuntime.Rq G / 40000) / (9 * QMCLeafB.EngineRuntime.Rq G + 1) := by
  unfold QMCLeafB.OkLower.dqOf
  rw [QMCLeafB.RoundT.epsOf, massV_s0]
  ring

theorem levelOf_s0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.OkLower.levelOf (s0 G t)
      = t - QMCLeafB.EngineRuntime.Rq G / 40000
          + ((QMCLeafB.EngineRuntime.Rq G / 40000) / (9 * QMCLeafB.EngineRuntime.Rq G + 1)) / 2 := by
  unfold QMCLeafB.OkLower.levelOf
  rw [stT_s0, epsOf_s0, dqOf_s0]

/-- The campaign round is `roundW` on the whole orbit from a normalised start. -/
theorem roundWG_iterate_s0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.LedgerW.roundWG^[k] (s0 G t) = QMCLeafB.OkLower.roundW^[k] (s0 G t) :=
  QMCLeafB.LedgerW.roundWG_iterate_eq_roundW (s0 G t) (normalised_s0 G t) k

/-- **The verdict is the `anyOk` of the `okW` stream** at the orbit of `s0`. -/
theorem bit0_eq_verdict_orbit (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    camBit G t
      = QMCLeafB.RoundProgram.verdict
          (QMCLeafB.OkLower.roundW^[AsmM8.Tbc2 G t] (s0 G t)) := by
  show QMCLeafB.MechM6.bit0 G t = _
  unfold QMCLeafB.MechM6.bit0 QMCLeafB.FinalStroke.loopBit QMCLeafB.MechM6.verdict0
    QMCLeafB.MechM6.init0 QMCLeafB.MechM6.round0 s0
  exact congrArg QMCLeafB.RoundProgram.verdict (roundWG_iterate_s0 G t _)

/-- **`bit0` is `anyOk` of the flag stream along the orbit.** -/
theorem bit0_eq_anyOk (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    camBit G t
      = QMCLeafB.SimLoop.anyOk
          (fun k => QMCLeafB.OkLower.okW (QMCLeafB.OkLower.roundW^[k] (s0 G t)))
          (AsmM8.Tbc2 G t) := by
  rw [bit0_eq_verdict_orbit]
  exact QMCLeafB.OkLower.verdict_iterate_eq_anyOk_W (s0 G t) (stOks_s0 G t) (AsmM8.Tbc2 G t)

theorem bit0_eq_true_iff (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    camBit G t = true ↔
      ∃ k, k < AsmM8.Tbc2 G t ∧ QMCLeafB.OkLower.okW (QMCLeafB.OkLower.roundW^[k] (s0 G t)) = true := by
  rw [bit0_eq_anyOk, QMCLeafB.SimLoop.anyOk_eq_true_iff]

theorem bit0_eq_false_iff (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    camBit G t = false ↔
      ∀ k, k < AsmM8.Tbc2 G t → QMCLeafB.OkLower.okW (QMCLeafB.OkLower.roundW^[k] (s0 G t)) = false := by
  rw [bit0_eq_anyOk, QMCLeafB.SimLoop.anyOk_eq_false_iff]

/-! ## 2.  On the interior bracket the flag is the lower-body oracle's answer -/

theorem not_guard_s0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hint : AsmM8.Interior G t) :
    ¬ (0 ≤ QMCLeafB.RoundProgram.stT (s0 G t) + QMCLeafB.RoundT.epsOf (s0 G t)) := by
  rw [stT_s0, epsOf_s0]
  have h2 : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := hint.2
  have h2' : t < -(QMCLeafB.EngineRuntime.Rq G / 40000) := by exact_mod_cast h2
  linarith

/-- **The flag is `ok` at a round exactly when the lower-body oracle does not refute there.** -/
theorem okW_orbit_true_iff (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hint : AsmM8.Interior G t)
    (k : ℕ) :
    QMCLeafB.OkLower.okW (QMCLeafB.OkLower.roundW^[k] (s0 G t)) = true ↔
      (QMCLeafB.OkLower.oracleV (QMCLeafB.OkLower.roundW^[k] (s0 G t))).1 = false := by
  rw [QMCLeafB.OkLower.okW_eq_engine (s0 G t) k (not_guard_s0 G t hint)]
  cases hb : (QMCLeafB.OkLower.oracleV (QMCLeafB.OkLower.roundW^[k] (s0 G t))).1 with
  | false => simp
  | true => simp

/-- **The flag is `false` at a round exactly when the lower-body oracle refutes there.** -/
theorem okW_orbit_false_iff (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hint : AsmM8.Interior G t)
    (k : ℕ) :
    QMCLeafB.OkLower.okW (QMCLeafB.OkLower.roundW^[k] (s0 G t)) = false ↔
      (QMCLeafB.OkLower.oracleV (QMCLeafB.OkLower.roundW^[k] (s0 G t))).1 = true := by
  rw [QMCLeafB.OkLower.okW_eq_engine (s0 G t) k (not_guard_s0 G t hint)]
  cases hb : (QMCLeafB.OkLower.oracleV (QMCLeafB.OkLower.roundW^[k] (s0 G t))).1 with
  | false => simp
  | true => simp

/-- **`bit0` true ⟺ some round answers `ok` at its own centre.** -/
theorem bit0_eq_true_iff_engine (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hint : AsmM8.Interior G t) :
    camBit G t = true ↔
      ∃ k, k < AsmM8.Tbc2 G t ∧
        (QMCLeafB.OkLower.oracleV (QMCLeafB.OkLower.roundW^[k] (s0 G t))).1 = false := by
  rw [bit0_eq_true_iff]
  constructor
  · rintro ⟨k, hk, hok⟩
    exact ⟨k, hk, (okW_orbit_true_iff G t hint k).mp hok⟩
  · rintro ⟨k, hk, hok⟩
    exact ⟨k, hk, (okW_orbit_true_iff G t hint k).mpr hok⟩

/-- **`bit0` false ⟺ every round answers `viol` at its own centre.** -/
theorem bit0_eq_false_iff_all_viol (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hint : AsmM8.Interior G t) :
    camBit G t = false ↔
      ∀ k, k < AsmM8.Tbc2 G t →
        (QMCLeafB.OkLower.oracleV (QMCLeafB.OkLower.roundW^[k] (s0 G t))).1 = true := by
  rw [bit0_eq_false_iff]
  exact ⟨fun h k hk => (okW_orbit_false_iff G t hint k).mp (h k hk),
    fun h k hk => (okW_orbit_false_iff G t hint k).mpr (h k hk)⟩

/-! ### 2b.  The level and the tolerance are constant along the orbit -/

theorem epsOf_orbit (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.RoundT.epsOf (QMCLeafB.OkLower.roundW^[k] (s0 G t))
      = QMCLeafB.EngineRuntime.Rq G / 40000 := by
  rw [QMCLeafB.HtopFinish.epsOf_congr (QMCLeafB.OkLower.stA_iterateW (s0 G t) k)]
  exact epsOf_s0 G t

theorem massV_orbit (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.RoundT.massV (QMCLeafB.OkLower.roundW^[k] (s0 G t))
      = QMCLeafB.EngineRuntime.Rq G := by
  have hA := QMCLeafB.OkLower.stA_iterateW (s0 G t) k
  have h : QMCLeafB.RoundT.massV (QMCLeafB.OkLower.roundW^[k] (s0 G t))
      = QMCLeafB.RoundT.massV (s0 G t) := by
    unfold QMCLeafB.RoundT.massV
    rw [hA]
  rw [h]
  exact massV_s0 G t

theorem stT_orbit (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.RoundProgram.stT (QMCLeafB.OkLower.roundW^[k] (s0 G t)) = t := by
  rw [QMCLeafB.OkLower.stT_iterateW]
  exact stT_s0 G t

theorem dqOf_orbit (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.OkLower.dqOf (QMCLeafB.OkLower.roundW^[k] (s0 G t))
      = QMCLeafB.OkLower.dqOf (s0 G t) := by
  unfold QMCLeafB.OkLower.dqOf
  rw [epsOf_orbit G t k, massV_orbit G t k, epsOf_s0 G t, massV_s0 G t]

theorem levelOf_orbit (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) :
    QMCLeafB.OkLower.levelOf (QMCLeafB.OkLower.roundW^[k] (s0 G t))
      = QMCLeafB.OkLower.levelOf (s0 G t) := by
  unfold QMCLeafB.OkLower.levelOf
  rw [stT_orbit G t k, epsOf_orbit G t k, dqOf_orbit G t k, stT_s0, epsOf_s0]

/-- **The ok round's state carries the three ledger facts, at the FIXED level of the start.** -/
theorem bit0_true_gives_ledger (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hint : AsmM8.Interior G t) (hb : camBit G t = true) :
    ∃ k, k < AsmM8.Tbc2 G t ∧
      QMCLeafB.RoundProgram.dvR (QMCLeafB.OkLower.roundW^[k] (s0 G t)) = 0 ∧
      QMCLeafB.RoundProgram.fvR (QMCLeafB.OkLower.roundW^[k] (s0 G t))
        ≤ QMCLeafB.OkLower.levelOf (s0 G t) ∧
      (QMCLeafB.RoundProgram.pivAns (QMCLeafB.OkLower.roundW^[k] (s0 G t))).1 = false := by
  obtain ⟨k, hk, hok⟩ := (bit0_eq_true_iff_engine G t hint).mp hb
  obtain ⟨hdv, hfv, hpiv⟩ := QMCLeafB.OkLower.oracleV_ok _ hok
  exact ⟨k, hk, hdv, by rwa [levelOf_orbit G t k] at hfv, hpiv⟩

/-! ## 3.  The split of `hcomplete`, and the leaf from the two halves -/

/-- **The ball half**: `hcomplete` at ball-bearing bodies. -/
def HcompleteBall : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
    ¬ AsmM8.EmptyBody G t (Pfam G) →
    BitdecM4.BallBearing G t (Pfam G) → camBit G t = true

/-- **The thin half**: `hcomplete` at ball-free bodies (the dreg band). -/
def HcompleteBf : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
    ¬ AsmM8.EmptyBody G t (Pfam G) →
    ¬ BitdecM4.BallBearing G t (Pfam G) → camBit G t = true

/-- `hcomplete` itself, spelled out. -/
def Hcomplete : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
    ¬ AsmM8.EmptyBody G t (Pfam G) → camBit G t = true

/-- **THE SPLIT**: `hcomplete` is exactly its ball half and its thin half. -/
theorem hcomplete_iff_split : Hcomplete ↔ HcompleteBall ∧ HcompleteBf := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro G t hn hint hne _; exact h G t hn hint hne
    · intro G t hn hint hne _; exact h G t hn hint hne
  · rintro ⟨hb, hf⟩ G t hn hint hne
    by_cases hB : BitdecM4.BallBearing G t (Pfam G)
    · exact hb G t hn hint hne hB
    · exact hf G t hn hint hne hB

/-- **The leaf from the split** — verbatim `d9f601e5`, from `hok` + the two halves. -/
theorem leaf_of_hok_and_split
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      camBit G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hball : HcompleteBall) (hbf : HcompleteBf) :
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
  QMCLeafB.MechM6.leaf_of_hok_and_complete hok (hcomplete_iff_split.mpr ⟨hball, hbf⟩)

/-! ## 4.  Falsify-first: the record route is void at a ball-bearing body

`BallM2.no_runParts_of_ball` says a `RunParts` record at a ball-bearing relaxation forces a TRUE bit.
So on the ball stratum the slot `hC` (`bit false ⟹ RunParts`) is not a weaker obligation than the
bit itself — no record exists there at a false bit at all.  The ball half is the program's own reach;
the thin-band record machinery cannot touch it. -/

/-- **A ball-bearing point reads `true` given `hC`** (the volume obstruction, consumed). -/
theorem bit_true_at_ball_campaign
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (Pfam G) → camBit G t = false →
      QMCLeafB.FinalStroke.RunParts camBit G t (Pfam G))
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n) (hint : AsmM8.Interior G t)
    (hB : BitdecM4.BallBearing G t (Pfam G)) : camBit G t = true := by
  obtain ⟨X₀, hball⟩ := hB
  by_contra hcon
  have hbf : camBit G t = false := by
    cases h : camBit G t with
    | false => rfl
    | true => exact absurd h hcon
  refine absurd (QMCLeafB.BallM2.no_runParts_of_ball hn hball
    (hC G t hn hint (BitdecM4.not_emptyBody_of_ballBearing ⟨X₀, hball⟩) hbf)) hcon

/-- **No `RunParts` record exists at a ball-bearing body with a false bit.**  Hence `hC` there is
*equivalent* to `camBit G t = true`, and the records cannot discharge the ball half. -/
theorem no_runParts_at_ball_of_false_bit {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hB : BitdecM4.BallBearing G t (Pfam G)) (hbf : camBit G t = false) :
    ¬ Nonempty (QMCLeafB.FinalStroke.RunParts camBit G t (Pfam G)) := by
  rintro ⟨B⟩
  obtain ⟨X₀, hball⟩ := hB
  exact absurd (QMCLeafB.BallM2.no_runParts_of_ball hn hball B) (by rw [hbf]; simp)

/-! ## 5.  Both strata are inhabited: the split is two-sided -/

/-- `AsmM8.EmptyBody` and `ThriceM3.BodyEmpty` are the same predicate (same definition). -/
theorem emptyBody_iff_thrice (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) :
    AsmM8.EmptyBody G t P ↔ QMCLeafB.ThriceM3.BodyEmpty G t P := by
  unfold AsmM8.EmptyBody QMCLeafB.ThriceM3.BodyEmpty
  rfl

/-- The sliver `(G₁, t₁)` is a ball-bearing interior point with a nonempty body. -/
theorem sliver_ballBearing :
    AsmM8.Interior QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ ∧
      ¬ AsmM8.EmptyBody QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁
        (Pfam QMCLeafB.AnchorFactsM2.G₁) ∧
      BitdecM4.BallBearing QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁
        (Pfam QMCLeafB.AnchorFactsM2.G₁) := by
  have hB : BitdecM4.BallBearing QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁
      (Pfam QMCLeafB.AnchorFactsM2.G₁) :=
    ⟨QMCLeafB.BallM2.Xs, QMCLeafB.BallM2.sliver_ball_campaign⟩
  exact ⟨QMCLeafB.EmptyBodyM5.t₁_mem_bracket, BitdecM4.not_emptyBody_of_ballBearing hB, hB⟩

/-- The dreg band is ball-free with a nonempty body, at every `Δ ∈ [0, dq/24)`. -/
theorem band_ballFree (Δ : ℚ) (h0 : 0 ≤ (Δ : ℝ)) (h1 : (Δ : ℝ) < 1 / 9120000) :
    ¬ BitdecM4.BallBearing QMCLeafB.DregM6.G₁ (QMCLeafB.DregM6.tStar + Δ)
      (Pfam QMCLeafB.DregM6.G₁) := by
  rintro ⟨X₀, hball⟩
  refine QMCLeafB.DregM6.no_ball Δ h0 ?_ X₀ hball
  rw [show (1 / 380000 : ℝ) / 24 = 1 / 9120000 by norm_num]
  exact h1

/-- **Both halves of the split are inhabited** — one at the sliver, one in the dreg band. -/
theorem split_both_inhabited :
    (∃ (G : QuantumMaxCutEnergy.Input) (t : ℚ), AsmM8.Interior G t ∧
        ¬ AsmM8.EmptyBody G t (Pfam G) ∧ BitdecM4.BallBearing G t (Pfam G)) ∧
      (∃ (G : QuantumMaxCutEnergy.Input) (t : ℚ), AsmM8.Interior G t ∧
        ¬ AsmM8.EmptyBody G t (Pfam G) ∧ ¬ BitdecM4.BallBearing G t (Pfam G)) := by
  refine ⟨⟨QMCLeafB.AnchorFactsM2.G₁, QMCLeafB.AnchorFactsM2.t₁,
      sliver_ballBearing.1, sliver_ballBearing.2.1, sliver_ballBearing.2.2⟩,
    ⟨QMCLeafB.DregM6.G₁, QMCLeafB.DregM6.tStar + 1 / 18240000, ?_, ?_, ?_⟩⟩
  · exact QMCLeafB.DregM6.dreg_interior _ (by norm_num) (by norm_num)
  · intro he
    exact QMCLeafB.DregM6.not_bodyEmpty _
      (by norm_num : (0 : ℝ) ≤ ((1 / 18240000 : ℚ) : ℝ))
      (by norm_num : ((1 / 18240000 : ℚ) : ℝ) ≤ 2 + 3 * (1 / 380000 : ℝ) / 2)
      ((emptyBody_iff_thrice _ _ _).mp he)
  · exact band_ballFree _ (by norm_num) (by norm_num)

/-! ## 6.  The ball half's exact content: the round's own cut-data slots

`CruxM1.allFalseParts` builds a `RunParts` record out of nine engine slots.  Composed with
`BallM2.no_runParts_of_ball`, that turns the ball half of `hcomplete` into a statement about the
**transcript** — the cut data read off the rounds — and not about search reach. -/

/-- The engine's cut-data slots, at the campaign's own `RunParams`. -/
structure CutSlots {G : QuantumMaxCutEnergy.Input} (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (del : ℕ → ℚ) : Prop where
  hwit : ∀ k, k < P.K * P.m →
    (QMCLeafB.EngineIterates.Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) cd k) *ᵥ (cd k).p = (cd k).c
  hrho : ∀ k, k < P.K * P.m → 0 ≤ (cd k).rho
  hcne : ∀ k, k < P.K * P.m → (cd k).c ≠ 0
  hdel0 : ∀ k, k < P.K * P.m → 0 ≤ del k
  hcheck : ∀ k, k < P.K * P.m →
    (del k) ^ 2 ≤ ((cd k).rho) ^ 2 * QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p
  hle : ∀ k, k < P.K * P.m → (cd k).rho ≤ P.rmax
  hcut : ∀ k, k < P.K * P.m → ∀ z, z ∈ QMCLeafB.BallM2.runBall G t P →
    -(((del k : ℚ)) : ℝ) ≤ QMCLeafB.EngineIterates.cutCR cd k ⬝ᵥ
      (z - QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k)

/-- **The ball half, reduced to the transcript**: at a ball-bearing body, a false bit contradicts the
rounds' own cut-data slots.  So `hcomplete` there is the *transcript identification* — no search
content is left. -/
theorem bit_true_at_ball_of_cutslots {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hn : 2 ≤ G.n) (hB : BitdecM4.BallBearing G t (Pfam G))
    (hT : camBit G t = false →
      ∃ (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (del : ℕ → ℚ),
        CutSlots t (Pfam G) cd del) :
    camBit G t = true := by
  obtain ⟨X₀, hball⟩ := hB
  by_contra hcon
  have hbf : camBit G t = false := by
    cases h : camBit G t with
    | false => rfl
    | true => exact absurd h hcon
  obtain ⟨cd, del, hs⟩ := hT hbf
  refine absurd (QMCLeafB.BallM2.no_runParts_of_ball hn hball
    (QMCLeafB.CruxM1.allFalseParts hbf cd del hs.hwit hs.hrho hs.hcne hs.hdel0 hs.hcheck hs.hle
      hs.hcut)) hcon

/-- **The ball half of `hcomplete` from the transcript**: the exact residual shape at ball bodies. -/
theorem hcomplete_ball_of_cutslots
    (hT : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (Pfam G) → camBit G t = false →
      ∃ (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (del : ℕ → ℚ),
        CutSlots t (Pfam G) cd del) :
    HcompleteBall := by
  intro G t hn hint hne hB
  exact bit_true_at_ball_of_cutslots hn hB (hT G t hn hint hne)

/-! ## 7.  The residual in the orbit language (what is actually attackable)

`bit0_eq_true_iff_engine` turns each half of the split into a statement about the **engine's own
read-out along the orbit**: some round below the horizon answers `ok` at its own centre, at a level
and tolerance that do not change from round to round.  This is the form in which the descent's
reachability can be argued (and the form `TrajM3.TestRun.htest` speaks). -/

theorem hcomplete_iff_orbit :
    Hcomplete ↔
      ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
        ¬ AsmM8.EmptyBody G t (Pfam G) →
        ∃ k, k < AsmM8.Tbc2 G t ∧
          (QMCLeafB.OkLower.oracleV (QMCLeafB.OkLower.roundW^[k] (s0 G t))).1 = false := by
  constructor
  · intro h G t hn hint hne
    exact (bit0_eq_true_iff_engine G t hint).mp (h G t hn hint hne)
  · intro h G t hn hint hne
    exact (bit0_eq_true_iff_engine G t hint).mpr (h G t hn hint hne)

theorem hcompleteBf_iff_orbit :
    HcompleteBf ↔
      ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
        ¬ AsmM8.EmptyBody G t (Pfam G) → ¬ BitdecM4.BallBearing G t (Pfam G) →
        ∃ k, k < AsmM8.Tbc2 G t ∧
          (QMCLeafB.OkLower.oracleV (QMCLeafB.OkLower.roundW^[k] (s0 G t))).1 = false := by
  constructor
  · intro h G t hn hint hne hB'
    exact (bit0_eq_true_iff_engine G t hint).mp (h G t hn hint hne hB')
  · intro h G t hn hint hne hB'
    exact (bit0_eq_true_iff_engine G t hint).mpr (h G t hn hint hne hB')

/-- **The visit theorem's horizon is the campaign's own round count** — so a member-visit below
`K·m` is below `Tbc2`, with no count mismatch. -/
theorem paramsKbc2_horizon (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    (Pfam G).K * (Pfam G).m = AsmM8.Tbc2 G t := rfl

/-! ## 8.  Falsification of the visit route at the ball stratum

The honest negative receipt of this direction.  `TrajM3.exists_member_of_ball` (the visit theorem)
consumes a `TrajM3.TestRun`, and a `TestRun` **bundles a `RunParts` record** (`TestRun.toParts`) whose
verdict is the campaign's own bit.  At a ball-bearing body no such record exists at a false bit
(§4).  So the visit theorem is *unavailable* exactly where the ball half must be proved, and it
cannot discharge it: what it yields is a restatement of an already-true bit, not a route to it.

(The two modules DO co-load here — the phase-31 hazard `f12` is a `Check_`-cone artefact; in the
published `Definitions` cone `Def_QMCLeafB_mech31` and `Def_QMCLeafB_traj_m3` live together.  That is
why the falsification can be machine-checked at all.) -/

/-- **No test-run exists at a ball-bearing body with a false bit** — the record it bundles does not
exist there (§4). -/
theorem no_testRun_at_ball_of_false_bit {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hB : BitdecM4.BallBearing G t (Pfam G)) (hbf : camBit G t = false) :
    ¬ Nonempty (QMCLeafB.TrajM3.TestRun camBit G t (Pfam G)) := by
  rintro ⟨T⟩
  exact no_runParts_at_ball_of_false_bit hn hB hbf ⟨T.toParts⟩

/-- **A test-run at a ball-bearing body already forces the true bit** — so the visit theorem
`TrajM3.exists_member_of_ball` presupposes the ball half rather than proving it. -/
theorem testRun_at_ball_forces_true_bit {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hT : Nonempty (QMCLeafB.TrajM3.TestRun camBit G t (Pfam G)))
    (hB : BitdecM4.BallBearing G t (Pfam G)) : camBit G t = true := by
  by_contra hcon
  have hbf : camBit G t = false := by
    cases h : camBit G t with
    | false => rfl
    | true => exact absurd h hcon
  obtain ⟨X₀, hball⟩ := hB
  obtain ⟨T⟩ := hT
  exact absurd (QMCLeafB.BallM2.no_runParts_of_ball hn hball T.toParts) hcon

end Hcb32M3

/-! ## 7.  Axiom audit -/

#print axioms Hcb32M3.bit0_eq_anyOk
#print axioms Hcb32M3.bit0_eq_true_iff
#print axioms Hcb32M3.bit0_eq_false_iff
#print axioms Hcb32M3.okW_orbit_true_iff
#print axioms Hcb32M3.bit0_eq_true_iff_engine
#print axioms Hcb32M3.bit0_eq_false_iff_all_viol
#print axioms Hcb32M3.levelOf_orbit
#print axioms Hcb32M3.dqOf_orbit
#print axioms Hcb32M3.bit0_true_gives_ledger
#print axioms Hcb32M3.hcomplete_iff_split
#print axioms Hcb32M3.leaf_of_hok_and_split
#print axioms Hcb32M3.bit_true_at_ball_campaign
#print axioms Hcb32M3.no_runParts_at_ball_of_false_bit
#print axioms Hcb32M3.sliver_ballBearing
#print axioms Hcb32M3.band_ballFree
#print axioms Hcb32M3.split_both_inhabited
#print axioms Hcb32M3.bit_true_at_ball_of_cutslots
#print axioms Hcb32M3.hcomplete_ball_of_cutslots
#print axioms Hcb32M3.hcomplete_iff_orbit
#print axioms Hcb32M3.hcompleteBf_iff_orbit
#print axioms Hcb32M3.paramsKbc2_horizon
#print axioms Hcb32M3.no_testRun_at_ball_of_false_bit
#print axioms Hcb32M3.testRun_at_ball_forces_true_bit


