-- Prove2me | Definitions.Def_QMCLeafB_eaudit
-- name    : QMCLeafB_eaudit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:51:08.775603+00:00
-- url     : https://prove2.me/theorems/3e7e16e5-bb08-43bc-9ef0-6dfe9f9d81c6
-- title:
--   QMCLeafB eaudit
-- statement:
--   `Check_eaudit_m7` — phase 31, member m7, direction `engine-audit`.
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_RStInit
import Definitions.Def_QMCLeafB_htop_oklower_m7
import Definitions.Def_QMCLeafB_hemptyR
import Definitions.Def_QMCLeafB_asm2
/-
  `Check_eaudit_m7` — phase 31, member m7, direction `engine-audit`.

  QUESTION.  `Asm2M8.solution_of_residual` (the phase-30 composite) asks for seven slots.
  Which of them does the existing engine/library already discharge, at what exact statement,
  and which are NOT stated at the current interface?

  ANSWER (machine-checked below, slot by slot).

  ## The pinned program

      σ        := QMCLeafB.RoundProgram.RSt
      init     := QMCLeafB.RStInit.init0        (m1, `Check_initpoly_m1` / `Def_QMCLeafB_RStInit`)
      round    := QMCLeafB.OkLower.roundW       (m7/ph16, `Check_htop_oklower_m7`)
      verdict  := QMCLeafB.RoundProgram.verdict (m3, `Check_round_program_m3`)
      T0       := AsmM8.Tbc2

  ## Slot table

  | slot          | status | receipt |
  |---------------|--------|---------|
  | `Poly init`   | DONE   | `RStInit.poly_init0` (§1) |
  | `Poly round`  | DONE   | `OkLower.poly_roundW` — hypothesis-free (§1) |
  | `Poly verdict`| DONE   | `RoundProgram.poly_verdict` (§1) |
  | `hinitTape`   | DONE   | `RStInit.init0_tape` — verbatim (§2) |
  | `htop`        | DONE   | `OkLower.htop_roundW` + `stOks/stT/epsOf_init0` + `one_le_Kbc2_mul` (§3) |
  | `hstepLen`    | **NOT at the interface** (§6c) — proved only for `RoundProgram.round` as a *size cap* (`RoundsizeM6.Msz`), never as a one-step length bound |
  | `hbit`        | **DERIVED**: `hbit = hok + hcomp` (§4); `hC` is then vacuous |
  | `hok`         | **NOT at the interface** — the run invariants it needs are §6a |
  | `hC`          | **VACUOUS** given `hbit` (§4, `hC_of_hbit`) |

  So the residual is **two** program obligations, not seven: `hok` (soundness of the `ok`
  test) and `hcomp` (`¬EmptyBody ⟹ bit true`, completeness).  §7 is the numeric finding that
  blocks the cheapest route to `hok` at the shelf's own initial state.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

noncomputable section

namespace EAuditM7

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

local instance instRequestCodingEAudit : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 0.  The pinned program -/

/-- The initial state program (m1). -/
def ProgInit : QMCLeafB.FuelWire.Pkg → QMCLeafB.RoundProgram.RSt :=
  QMCLeafB.RStInit.init0

/-- The reported round (m7/ph16): `ok`-and-freeze above the campaign slack, the lower-body engine
round below it. -/
def ProgRound : QMCLeafB.RoundProgram.RSt → QMCLeafB.RoundProgram.RSt :=
  QMCLeafB.OkLower.roundW

/-- The verdict bit (m3). -/
def ProgVerdict : QMCLeafB.RoundProgram.RSt → Bool :=
  QMCLeafB.RoundProgram.verdict

/-- The program's own bit. -/
def Bit : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  QMCLeafB.FinalStroke.loopBit ProgInit ProgRound ProgVerdict AsmM8.Tbc2

/-! ## 1.  The three `Poly` slots — all three are already proved -/

theorem poly_init : Poly ProgInit :=
  QMCLeafB.RStInit.poly_init0

theorem poly_round : Poly ProgRound :=
  QMCLeafB.OkLower.poly_roundW

theorem poly_verdict : Poly ProgVerdict :=
  QMCLeafB.RoundProgram.poly_verdict

/-! ## 2.  `hinitTape` — verbatim -/

theorem hinitTape_pinned : ∀ p : QMCLeafB.FuelWire.Pkg,
    ProgInit p = ProgInit (QMCLeafB.FinalStroke.noTape p.1.1 p.2) :=
  QMCLeafB.RStInit.init0_tape

/-! ## 3.  `htop` — `OkLower.htop_roundW` at the pinned initial state

Above the campaign slack `roundW` is `roundOk` on the whole orbit, which appends `true` for ever, so
the verdict is `true`.  Everything the theorem asks of `init` is a field read-back of `init0`. -/

theorem one_le_Tbc2 (G : QuantumMaxCutEnergy.Input) (t : ℚ) : 1 ≤ AsmM8.Tbc2 G t :=
  QMCLeafB.UnionShallow.one_le_Kbc2_mul G

theorem htop_pinned : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
    Bit G t = true := by
  intro G t _ h1 h2
  exact QMCLeafB.OkLower.htop_roundW ProgInit
    (fun p => QMCLeafB.RStInit.stOks_init0 p)
    (fun p => QMCLeafB.RStInit.stT_init0 p)
    (fun p => QMCLeafB.HtopFinish.epsOf_init0 p)
    AsmM8.Tbc2 one_le_Tbc2 G t h1 h2

/-! ## 4.  The collapse: `hbit` is a theorem given `hok` + `hcomp`; `hC` is then vacuous

`Asm2M8.solution_of_residual`'s three semantic slots are not independent.

* `hok` (bit `true` ⟹ a symmetric `RelaxMem` at the loop's own centre) **already gives**
  `EmptyBody ⟹ bit = false`: a `RelaxMem` casts to a real body point
  (`HemptyR_M3.relaxBodyLE_of_relaxMem`), so an empty body admits no `ok` round, so the any-`ok`
  bit is `false`.
* the only other direction of `hbit` is **completeness**, `¬EmptyBody ⟹ bit = true` (`hcomp`).
* with `hbit` in hand `hC` has contradictory hypotheses and is discharged by `absurd`.

So the composite fires from `{k, hk, init, round, verdict, Poly×3, c, hstepLen, hinitTape, htop,
hok, hcomp}`: **two** semantic obligations, not three. -/

/-- **A `RelaxMem` at the campaign's numbers contradicts an empty body.**  The cast bridge
(`HemptyR_M3.relaxBodyLE_of_relaxMem`) is the only content; no symmetry is needed. -/
theorem emptyBody_absurd {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (he : AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G))
    {cX : Matrix (Fin G.n) (Fin G.n) ℚ}
    (hM : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
      (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)) : False := by
  have hlev : ((t - QMCLeafB.RundataCert.eps G : ℚ) : ℝ)
      = (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
    rw [QMCLeafB.RundataCert.eps]
    push_cast
    ring
  have h := QMCLeafB.HemptyR_M3.relaxBodyLE_of_relaxMem hM
  rw [QMCLeafB.HemptyR_M3.castMat_wMatrixQ, hlev] at h
  exact he (QMCLeafB.SepOracle.castMat cX) h

section Collapse

variable {σ : Type} [Coding σ]
variable (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)

/-- The program's own bit, generically. -/
abbrev GBit : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2

/-- **`hbit` from `hok` + `hcomp`.** -/
theorem hbit_of_hok_hcomp
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      GBit init round verdict G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hcomp : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      GBit init round verdict G t = true) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      (GBit init round verdict G t = false ↔
        AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G)) := by
  intro G t hn hint
  constructor
  · intro hbf
    by_contra hne
    have htrue := hcomp G t hn hint hne
    rw [hbf] at htrue
    exact Bool.noConfusion htrue
  · intro he
    cases hb : GBit init round verdict G t with
    | false => rfl
    | true =>
        obtain ⟨cX, -, hM⟩ := hok G t hn hint hb
        exact absurd hM (fun h => emptyBody_absurd he h)

/-- **The converse**: `hbit` gives `hcomp`.  So at the interior the two formulations are the same
obligation, and `hbit + hok` is *equivalent* to `hcomp + hok` — the composite at `hok`+`hcomp` is a
re-aiming, not a weakening. -/
theorem hcomp_of_hbit
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      (GBit init round verdict G t = false ↔
        AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G))) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      GBit init round verdict G t = true := by
  intro G t hn hint hne
  cases h : GBit init round verdict G t with
  | true => rfl
  | false => exact absurd ((hbit G t hn hint).mp h) hne

/-- **`hC` is vacuous given `hbit`.**  Its hypotheses (body non-empty, bit `false`) are exactly the
negation of `hbit`'s left-to-right direction at an interior point. -/
noncomputable def hC_of_hbit
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      (GBit init round verdict G t = false ↔
        AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G))) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      GBit init round verdict G t = false →
      QMCLeafB.FinalStroke.RunParts (GBit init round verdict) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  intro G t hn hint hne hbf
  exact absurd ((hbit G t hn hint).mp hbf) hne

/-- **The composite, at two semantic obligations.**  Verbatim
`Asm2M8.solution_of_residual` with `hbit`/`hC` deleted (they are §4's theorems). -/
theorem solution_of_two
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (hinit : Poly init) (hr : Poly round) (hv : Poly verdict)
    (c : ℕ)
    (hstepLen : ∀ s : σ, (enc (round s)).length ≤ (enc s).length + c)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      GBit init round verdict G t = true)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      GBit init round verdict G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hcomp : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      GBit init round verdict G t = true) :
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
  Asm2M8.solution_of_residual k hk init round verdict hinit hr hv c hstepLen hinitTape htop
    (hbit_of_hok_hcomp init round verdict hok hcomp)
    hok
    (hC_of_hbit init round verdict (hbit_of_hok_hcomp init round verdict hok hcomp))

end Collapse

/-! ## 5.  The `ok` read-out: a `true` bit names an `ok` round, and an `ok` round is `RelaxMem`

This is the whole *entry point* of `hok`: `OkLower.verdict_iterate_eq_anyOk_W` +
`SimLoop.anyOk_eq_true_iff` + `OkLower.relaxMem_of_oracleV_ok`.  `hok` = the read-out below plus the
**five state clauses at the visited state**, and the two test clauses — every one of them a
*run invariant*, listed in §6a. -/

theorem okround_of_bit {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hb : Bit G t = true) :
    ∃ k, k < AsmM8.Tbc2 G t ∧
      QMCLeafB.OkLower.okW
        (QMCLeafB.OkLower.roundW^[k] (ProgInit (QMCLeafB.FinalStroke.noTape G t))) = true := by
  have hv : Bit G t = QMCLeafB.SimLoop.anyOk
      (fun k => QMCLeafB.OkLower.okW
        (QMCLeafB.OkLower.roundW^[k] (ProgInit (QMCLeafB.FinalStroke.noTape G t))))
      (AsmM8.Tbc2 G t) :=
    QMCLeafB.OkLower.verdict_iterate_eq_anyOk_W _ (QMCLeafB.RStInit.stOks_init0 _) _
  rw [hv] at hb
  exact (QMCLeafB.SimLoop.anyOk_eq_true_iff _ _).mp hb

/-- **An `ok` round of `roundW` is a `RelaxMem` at the state's own centre**, with the two test
clauses exposed exactly as the engine's data supplies them. -/
theorem relaxMem_of_okW {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ}
    {s : QMCLeafB.RoundProgram.RSt}
    (hF : QMCLeafB.RoundProgram.fvR s = QMCLeafB.SepOracle.frob A cX)
    (hok : QMCLeafB.OkLower.okW s = true)
    (hreg : ¬ (0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s))
    (hpos : 0 < QMCLeafB.RoundT.massV s)
    (hpsd : ∀ x : Fin n → ℚ,
      -(QMCLeafB.OkLower.dqOf s / 2) * (∑ i, x i ^ 2) ≤ QMCLeafB.SepOracle.qf cX x)
    (hdiag : ∀ i, |cX i i - 1| ≤ QMCLeafB.OkLower.dqOf s / 4) :
    QMCLeafB.RelaxOracle.RelaxMem A cX
      (QMCLeafB.RoundProgram.stT s - QMCLeafB.RoundT.epsOf s) (QMCLeafB.OkLower.dqOf s) := by
  have hV : (QMCLeafB.OkLower.oracleV s).1 = false := by
    have h1 := QMCLeafB.OkLower.okW_eq_engine s 0 hreg
    have h2 : QMCLeafB.OkLower.okW s = !((QMCLeafB.OkLower.oracleV s).1) := by
      simpa using h1
    rw [h2] at hok
    simpa using hok
  exact QMCLeafB.OkLower.relaxMem_of_oracleV_ok hF hV hpos hpsd hdiag

/-! ## 6.  What is NOT at the interface (the program lane's real work list)

**(6a) `hok`'s five state clauses at a visited ok state `s = roundW^[k] (init0 (noTape G t))`.**
Only `stT`/`stA` invariance exists (`OkLower.stT_roundW`, `stA_roundW`) plus
`RoundProgram.stN_round`, `stX_round_ok`, `stX_round_cut : stX (round s) = snapY s`; the
*run invariants* `stN s = G.n`, `stN s ≤ (stX s).length`, `0 < stD s`, `hsym` (the coded matrix is
symmetric) and `hbox` (`LdltCertM5.BoxRun`) are **not stated anywhere for `roundW`** — the
phase-23/24/25 board records them as the "run records", and they are what
`LdltCertM5.pivPsdMargin_of_boxRun` consumes.  `hdiag` (`|Xᵢᵢ − 1| ≤ dq/4` at a visited state) is
the `OkLower`-side analogue of `hdiagc`, and the phase-21 audit established it **cannot** be had
from `RelaxMem.diag_near` alone.

**(6b) `hcomp`** — `¬EmptyBody ⟹ bit true` at the interior.  Nothing in the library states it: the
banked positive results are `TrajM3.exists_member_of_ball` (ball-bearing bodies: the run *visits* a
member) and `BallM2`/`VolKillM3` (`no_runParts_of_ball`), both of which need the campaign ball and
say nothing at the ball-free thin band of `DregM6`.

**(6c) `hstepLen`** — the one-step length bound, `∀ s, (enc (round s)).length ≤ (enc s).length + c`.
NOT proved for `roundW`, and I do not believe it is *true*.  Reading the definitions
(`RoundsizeM6.enc_decomp : (enc s).length = skel s + 4·aX s + 6·|stOks s| + aRec s`, with
`aX = (encodeList (enc : ℚ → List Bool) (stX s)).length` and `aRec` the same for `stRec`):

* a cut round sets `stX (round s) = snapY s`, whose every entry has denominator exactly `stD s` and
  numerator `≤ stD s · stMu s` — so *every* entry's height jumps to `log (stD·stMu)`, while the
  incoming code's entries can be much shorter (at `init0` they have denominator `MOf n ≈ n²`, i.e.
  height `≈ log n`, against the grid's `(n+1)⁴`).  `aX` therefore jumps by `Θ(n² · log n)`;
* and `stRec (roundCut s) = (oracleR s).2` records ONE normal, of length `|idxs|² = n²` on the
  diagonal/pivot branches — again `Θ(n²)` bits.

Both are unbounded in `n` while `c` is a single numeral, so `hstepLen` fails for large `n` (the
`+6` from the appended `ok` flag is the harmless part).  **Consequence for the composite:**
`Fal30.solution_of_step_le`'s collapse of the ledger to `hstepLen` is not instantiable at `RSt`;
the ledger must be carried in its *cap* form — m6's `RoundsizeM6.Msz`
(`enc s ≤ Msz s`, `Msz (round s) ≤ Msz s + c`, `Msz s ≤ C₀·(enc s + 1)^kr`), which is what
`UnionShallow.solution_union_shallow_final` / `AsmM8.solution_of_classes` take — or in the
orbit-indexed form (`LoopRestate.boundedRun_loopBody_orbit`).  `Fal30.not_ledger_monomial` does not
block this: its `hgrowth` hypothesis (`(enc s).length + 1 ≤ (enc (round s)).length` at every state)
fails at a capped state.  **This is argued from the definitions, NOT machine-checked** — the
counterexample family needs a `runPivL` evaluation at a state with `|stX| = n²` and large `n`; d3/m6's
size lane should settle it, and it is the one place where the composite's hypothesis list looks
unsound rather than merely unproved.
-/

#check @QMCLeafB.RStInit.stN_round
#check @QMCLeafB.RStInit.stX_round_of_cut
#check @QMCLeafB.RStInit.stX_round_of_ok
#check @QMCLeafB.OkLower.stT_roundW
#check @QMCLeafB.OkLower.stA_roundW
#check @QMCLeafB.OkLower.oracleV_ok
#check @QMCLeafB.OkLower.relaxMem_of_oracleV_ok
#check @QMCLeafB.OkLower.dqOf_init0
#check @QMCLeafB.LdltCertM5.pivPsdMargin_of_tolerance
#check @QMCLeafB.HemptyR_M3.relaxBodyLE_of_relaxMem
#check @QMCLeafB.HemptyR_M3.hemptyR_campaign
/-! Present in the `Solutions/` sources but **not mirrored as a `Definitions/` bundle** (so not
`#check`-able from a published-only import cone): `RelaxApiM3.relaxMem_at_campaign_of_grid`,
`RelaxApiM3.hcert_of_campaign_grid`, `CruxM1.allFalseParts`, `CruxM1.allFalsePartsOfCuts`,
`TrajM3.exists_member_of_ball`, `RoundsizeM6.Msz`.  Their exact signatures are quoted in the prose
above; a program-lane file that needs them must import the `Solutions/` source (which is why the
mirror wave should include `relaxapi_m3` / `crux_m1` / `traj_m3`). -/

/-! ## 7.  The numeric finding: the certified-grid route to `hok` is closed at `init0`'s grid

`RelaxApiM3.relaxMem_at_campaign_of_grid` — the route the phase-30 brief names for `hok` — needs

    hgrid : 4·n² ≤ dqShallow G · stD s .

The campaign tolerance is bounded: `dqShallow G = eps G/(9·Rq G + 1) < 1/360000` for **every** `G`
(§7.1).  Hence `hgrid` forces

    stD s > 1440000 · n²                                                       (§7.2)

a grid of order `n²·10⁶`, while m1's `init0` sets `stD = ((n+1)²)²` (`RStInit.stD_init0_eq`), which
is `81` at `n = 2` (§7.3).  So the certified-grid bridge is **unavailable at the shelf's initial
state**, and `hok`'s PSD clause must come from the *exact* descent instead (an exact
`pivAns = false` certifies PSD with margin `0`, and `psd_margin` at `−dq/2` is then free) — a
**program-side decision**: `init` must either set `stD` from the request (a `Poly` function of it,
admissible) or run the exact descent.  §7.2 is the machine-checked necessary condition either
way.

**Prior art, stated plainly.**  The *refutation* of this route at `gridOf` is already banked by m2's
phase-30 lane (`Check_prog_m2`: "the shelf's `gridOf n = (n+1)^4` is refuted at the campaign
tolerance (`ContractM7.pivFSpec_false_campaign`); the state's grid register must be chosen from the
request"), and m2's `prog_m2` already carries the program-lane receipts at the *campaign* init
`QMCLeafB.InitDq.init0` (`poly_initP`, `initP_tape`, `massV_initP`/`epsOf_initP`/`dqOf_initP`,
`stN_iterateP`, `hcert_of_okW`, `hverdict_prog`, `htop_prog`, `hd_of_strata`).  §1–§3 here are an
independent assembly at `RStInit.init0` (the receipts are init-agnostic: `htop_roundW` reads back only
`stOks`, `stT`, `epsOf`); §7 adds the *arithmetic* necessary condition, which is the part a program
lane needs in order to size the grid register: `stD > 1440000·n²`. -/

/-- **7.1  The campaign tolerance is bounded by `1/360000`** (at `Rq > 0`, which the interior
bracket forces: `Asm2M8.Rq_pos_of_interior`; at `Rq = 0` the definition falls back to `1`, and the
bracket is empty there). -/
theorem dqShallow_lt {G : QuantumMaxCutEnergy.Input}
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RundataParams.dqShallow G < 1 / 360000 := by
  have hRq0 : QMCLeafB.EngineRuntime.Rq G ≠ 0 := ne_of_gt hRq
  unfold QMCLeafB.RundataParams.dqShallow
  rw [if_neg hRq0]
  unfold QMCLeafB.RundataParams.dqShallowCore
  have hpos : (0 : ℚ) < 9 * QMCLeafB.EngineRuntime.Rq G + 1 := by linarith
  rw [div_lt_iff₀ hpos]
  have heps : QMCLeafB.RundataCert.eps G = QMCLeafB.EngineRuntime.Rq G / 40000 := rfl
  rw [heps]
  nlinarith

/-- **7.2  Any state whose grid satisfies the campaign `hgrid` has `stD > 1440000·n²`.** -/
theorem grid_route_needs_fine_grid {G : QuantumMaxCutEnergy.Input} (hn : 1 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) {d : ℕ}
    (hgrid : 4 * (G.n : ℚ) * (G.n : ℚ)
      ≤ QMCLeafB.RundataParams.dqShallow G * (d : ℚ)) :
    1440000 * (G.n : ℚ) * (G.n : ℚ) < (d : ℚ) := by
  have hlt := dqShallow_lt hRq
  have hd : (0 : ℚ) ≤ (d : ℚ) := Nat.cast_nonneg d
  have hnpos : (0 : ℚ) < (G.n : ℚ) := by exact_mod_cast hn
  rcases eq_or_lt_of_le hd with h | h
  · rw [← h, mul_zero] at hgrid
    nlinarith
  · have h1 : QMCLeafB.RundataParams.dqShallow G * (d : ℚ)
        < (1 / 360000) * (d : ℚ) :=
      mul_lt_mul_of_pos_right hlt h
    nlinarith

/-- **7.3  `hgrid` is unsatisfiable at `init0` at `n = 2`.**  m1's grid is
`stD = ((n+1)²)² = 81`, while 7.2 demands `> 5760000`.  So the certified-grid bridge
(`RelaxApiM3.relaxMem_at_campaign_of_grid`) cannot be the route to `hok` at the shelf's own initial
state: the PSD clause must come from the exact descent, or `init` must set `stD` from the request. -/
theorem m1_grid_fails (p : QMCLeafB.FuelWire.Pkg) (hn : p.1.1.n = 2)
    (hint : AsmM8.Interior p.1.1 p.2) :
    ¬ (4 * (p.1.1.n : ℚ) * (p.1.1.n : ℚ)
        ≤ QMCLeafB.RundataParams.dqShallow p.1.1
            * (QMCLeafB.RoundProgram.stD (QMCLeafB.RStInit.init0 p) : ℚ)) := by
  intro hgrid
  have hRq : 0 < QMCLeafB.EngineRuntime.Rq p.1.1 := Asm2M8.Rq_pos_of_interior hint
  have h1 : 1440000 * (p.1.1.n : ℚ) * (p.1.1.n : ℚ)
      < (QMCLeafB.RoundProgram.stD (QMCLeafB.RStInit.init0 p) : ℚ) :=
    grid_route_needs_fine_grid (by rw [hn]; norm_num) hRq hgrid
  rw [QMCLeafB.RStInit.stD_init0_eq, hn] at h1
  unfold QMCLeafB.InitVerdict.gridOf at h1
  norm_num at h1

end EAuditM7

/-! ## Axiom audit -/

#print axioms EAuditM7.poly_init
#print axioms EAuditM7.poly_round
#print axioms EAuditM7.poly_verdict
#print axioms EAuditM7.hinitTape_pinned
#print axioms EAuditM7.htop_pinned
#print axioms EAuditM7.emptyBody_absurd
#print axioms EAuditM7.hbit_of_hok_hcomp
#print axioms EAuditM7.hcomp_of_hbit
#print axioms EAuditM7.hC_of_hbit
#print axioms EAuditM7.solution_of_two
#print axioms EAuditM7.okround_of_bit
#print axioms EAuditM7.relaxMem_of_okW
#print axioms EAuditM7.dqShallow_lt
#print axioms EAuditM7.grid_route_needs_fine_grid
#print axioms EAuditM7.m1_grid_fails


