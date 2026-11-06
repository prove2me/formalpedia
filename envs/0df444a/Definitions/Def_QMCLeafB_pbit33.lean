-- Prove2me | Definitions.Def_QMCLeafB_pbit33
-- name    : QMCLeafB_pbit33
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:46:10.793649+00:00
-- url     : https://prove2.me/theorems/60915f78-a10b-4ac4-9c7a-93fc54438feb
-- title:
--   QMCLeafB pbit33
-- statement:
--   # leaf B phase 33 — `pbit33` (swarm `smw3f5rk6`, member m6, direction d3)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_conformance_m8
import Definitions.Def_QMCLeafB_asm_m8
import Definitions.Def_QMCLeafB_topSlice
import Definitions.Def_QMCLeafB_asm2
/-
# leaf B phase 33 — `pbit33` (swarm `smw3f5rk6`, member m6, direction d3)

**The Poly bit of the campaign program, proved; the leaf reduced to ONE record family.**

`QMCLeafB.Sound31.solution_of_runPartsFamily` says the whole leaf is

    a Poly bit  +  a `RunParts` family at that bit.

This file fixes the *concrete* bit and the *concrete* parameter family — the campaign program's own
verdict bit at m2's `4·Kbc` round factor, a factor at which the campaign's count side condition is a
theorem (`ConformanceM8.budgetRounds_le_Kf4`) so no count hypothesis survives — and discharges the
Poly half:

    T33 G  := Kbc4 (mHalve (n²)) G · mHalve (n²)          (`= Kf4 G · mHalve (n²)`, definitional)
    o33 G t    := verdict (roundGT^[T33 G] (init0 (G, [], t)))
    P33 G      := paramsShallowKf Kf4 budgetRounds_le_Kf4 G       (so `(P33 G).K·(P33 G).m = T33 G`)

Contents:

* §1 the bit and the family, plus the definitional identity `(P33 G).K·(P33 G).m = T33 G` — the
  number `RunParts.hverdict` compares the verdict bit against, so records live at `o33`/`P33` with no
  transport;
* §2 **`ho33` — THE POLY BIT**, `Automatic.Poly (fun p => o33 p.1.1 p.2)`, from the banked Poly slots
  (`RStInit.poly_init0`, `ConformanceM8.poly_roundGT`, `RoundProgram.poly_verdict`,
  `FuelWire.poly_fuelOfProd` at `LoopClose.poly_Kbc4_mHalve_mul`) via
  `LoopRestate.ho_of_loop_bounded`, the orbit envelope being `IntegrateM6.orbit_envelope` at
  `CapGuard.MszG`, `c = 6`, cap `11448595·(X+1)^6` (`ConformanceM8.ledgerGT_MszG`);
* §3 the top slice of the bracket is a FREE record: `htop_roundGT` makes the bit `true` there and the
  identity is a witness with trace `0 ≤ t + Rq/40000`, so `AsmM8.runParts_of_member` applies
  (`runParts33_top`);
* §4 soundness on the driver's bracket from the INTERIOR family alone
  (`TopSliceRange.soundEpsOnBracket_of_runData_interior_hn`), and `SoundAt` at every bracketed point;
* §4b/§4c `Hd33` split by the bit's value into the two slots the record provers own — the `true`
  slot in `MemberAt` form, in the `EmptyBody` form of `RefutedM3`, and in m3's own `hok` form
  (`∃ cX, cXᵀ = cX ∧ RelaxMem (wMatrixQ G) cX (t - eps) dqShallow`, bridged by
  `Asm2M8.memberAt_of_relaxMem`);
* §4d the phase-33 interface in the PUBLISHED cone: `soundAt_of_runParts` (Sound31's lemma, which is
  `VerdictSound.soundAt_of_runData ∘ RunParts.toRunData`) and `solution_of_runPartsFamily_bracket`
  (`SolutionStatement` from a Poly bit + a bit-true top slice + an interior record family, at an
  ARBITRARY `(o, P)`);
* §5 **`solution33`**: the verbatim `d9f601e5` sentence from **`Hd33` alone** — no count hypothesis,
  no ledger, no `htop`, no test coherence — cross-checked against the banked endgame
  (`ConformanceM8.endgame_leaf_of_hd`), so the bit proved here is the bit the shelf runs.

Residual: exactly one type-valued family,

    Hd33 := ∀ G t, 2 ≤ G.n → -Rq G ≤ t → (t : ℝ) < -Rq G/40000 → RunParts o33 G t (P33 G)

i.e. precisely the object phase 33's lemmas (A) (rounding: a relaxed member supplies `hcert`) and (B)
(the all-cut record) build.

**Cone warning (load-bearing for the submission file).**  `Solutions/Check_sound31.lean` lives in the
`Solutions/Check_EngineIterates` cone; it CANNOT be imported together with the published
`Definitions.Def_QMCLeafB_*` bundles (`Definitions.Def_QMCLeafB_EngineIterates` clashes on
`QMCLeafB.EngineIterates.Aat.match_1`).  The submission file must import published Definitions only,
so it must go through this file's route (which needs no `Sound31` import), not through
`Check_sound31`.

Every theorem below is audited at the end of the file: its closure is exactly
[propext, Classical.choice, Quot.sound].
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Pbit33

open Matrix
open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

/-- The request coding of the leaf (local, so it does not collide with the sheets'). -/
local instance instRequestCodingPbit33 : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The bit and its parameter family -/

/-- **The round count of the campaign program** at m2's `4·Kbc` factor — a factor at which the
count side condition is a theorem (`ConformanceM8.budgetRounds_le_Kf4`). -/
def T33 (G : QuantumMaxCutEnergy.Input) : ℕ :=
  QMCLeafB.LoopClose.Kbc4 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
    * QMCLeafB.HalvePerG.mHalve (G.n * G.n)

/-- **The campaign's parameter family**: `dq = dqShallow`, `rmax = rmaxOf (n·n)`, `m = mHalve (n·n)`,
`K = 4·Kbc`, its `hbudget` discharged. -/
def P33 : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G :=
  QMCLeafB.UnionShallow.paramsShallowKf _ QMCLeafB.ConformanceM8.budgetRounds_le_Kf4

/-- **The campaign program's verdict bit**: `T33 G` rounds of the guarded slack round from brick 1's
init, then the flag read-out.  This is the `o` of `Sound31.solution_of_runPartsFamily`. -/
def o33 : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.ConformanceM8.roundGT
    QMCLeafB.RoundProgram.verdict (fun G _ => T33 G)

/-- The run count of `RunParts` at `P33` is `T33`, definitionally. -/
theorem P33_K_mul_m (G : QuantumMaxCutEnergy.Input) :
    (P33 G).K * (P33 G).m = T33 G := rfl

/-- The record count is positive: `1 ≤ Kf4·mHalve`. -/
theorem one_le_T33 (G : QuantumMaxCutEnergy.Input) : 1 ≤ T33 G :=
  QMCLeafB.ConformanceM8.one_le_Kf4_mul G

/-- `0 < P33.K · P33.m` — the `hKm` slot of the interface. -/
theorem hKm33 (G : QuantumMaxCutEnergy.Input) : 0 < (P33 G).K * (P33 G).m := by
  rw [P33_K_mul_m]
  exact lt_of_lt_of_le Nat.zero_lt_one (one_le_T33 G)

/-- `T33` at the fuel's own shape (definitional). -/
theorem T33_eq (G : QuantumMaxCutEnergy.Input) :
    T33 G = QMCLeafB.LoopClose.Kbc4 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
      * QMCLeafB.HalvePerG.mHalve (G.n * G.n) := rfl

/-! ### 1b.  Reading the family back — the numbers the record provers need

All four are `rfl`: `P33` is `paramsK` at `dq = dqShallow`, `rmax = rmaxOf (n·n)`, `m = mHalve (n·n)`,
`K = Kf4`, so the record statements (`hcert` at `t + Rq/40000`, `hcut` at the ball of radius
`dq/(8(c_A+1))`, `hcheck` at `del ≤ rmax·√σ`) can be written with the campaign's own constants. -/

theorem P33_dq (G : QuantumMaxCutEnergy.Input) :
    (P33 G).dq = QMCLeafB.RundataParams.dqShallow G := rfl

theorem P33_rmax (G : QuantumMaxCutEnergy.Input) :
    (P33 G).rmax = QMCLeafB.RundataHalving.rmaxOf (G.n * G.n) := rfl

theorem P33_m (G : QuantumMaxCutEnergy.Input) :
    (P33 G).m = QMCLeafB.HalvePerG.mHalve (G.n * G.n) := rfl

theorem P33_K (G : QuantumMaxCutEnergy.Input) : (P33 G).K = QMCLeafB.ConformanceM8.Kf4 G := rfl

theorem P33_cAq (G : QuantumMaxCutEnergy.Input) :
    (P33 G).cAq = QMCLeafB.EngineRuntime.Rq G := rfl

/-! ## 2.  The Poly bit -/

/-- `T33` is a polynomial-time function of the request. -/
theorem poly_T33 : Automatic.Poly (fun p : QMCLeafB.FuelWire.Pkg => T33 p.1.1) :=
  QMCLeafB.LoopClose.poly_Kbc4_mHalve_mul

/-- `f p * 1` is `Poly` when `f` is. -/
theorem poly_mul_one {f : QMCLeafB.FuelWire.Pkg → ℕ}
    (hf : Automatic.Poly f) : Automatic.Poly (fun p => f p * 1) := by
  have h := Automatic.Poly.comp (f := fun x : ℕ × ℕ => x.1 * x.2)
    (g := fun p : QMCLeafB.FuelWire.Pkg => (f p, 1)) Automatic.Poly.nat_mul
    (Automatic.Poly.pair hf
      (Automatic.Poly.const (α := QMCLeafB.FuelWire.Pkg) (β := ℕ) 1))
  simpa using h

/-- **`ho33` — the Poly bit of the campaign program.**  The verbatim Poly slot of
`Sound31.solution_of_runPartsFamily` at the concrete `o33`: the five banked Poly inputs, the orbit
envelope from the banked size ledger, and tape-freeness (`hspec`) to pass from the fuelled loop to
`o33`. -/
theorem ho33 (k : ℕ) (hk : 21 ≤ 2 ^ k) :
    Automatic.Poly (fun p : QMCLeafB.FuelWire.Pkg => o33 p.1.1 p.2) := by
  have hfuel : Automatic.Poly
      (QMCLeafB.FuelWire.fuelOfProd k (fun G => T33 G) (fun _ => (1 : ℕ))) :=
    QMCLeafB.FuelWire.poly_fuelOfProd k _ _ (poly_mul_one poly_T33)
  have hseed : ∀ p : QMCLeafB.FuelWire.Pkg,
      (fun G => T33 G) p.1.1 * (fun _ => (1 : ℕ)) p.1.1
        ≤ QMCLeafB.FuelWire.seedLen p ^ (2 ^ k) :=
    fun p => by
      have h := QMCLeafB.LoopClose.Kbc4_mHalve_le_seed k hk p
      show T33 p.1.1 * 1 ≤ QMCLeafB.FuelWire.seedLen p ^ (2 ^ k)
      rw [T33_eq, Nat.mul_one]
      exact h
  have hfuelLen : ∀ p : QMCLeafB.FuelWire.Pkg,
      (QMCLeafB.FuelWire.fuelOfProd k (fun G => T33 G) (fun _ => (1 : ℕ)) p).length
        = T33 p.1.1 :=
    fun p => by
      rw [QMCLeafB.FuelWire.fuelOfProd_length k _ _ hseed p, Nat.mul_one]
  refine QMCLeafB.FinishLine.poly_of_pointwise (α := QMCLeafB.FuelWire.Pkg) (β := Bool)
    (f := fun a : QMCLeafB.FuelWire.Pkg =>
      QMCLeafB.RoundProgram.verdict
        (Nat.iterate QMCLeafB.ConformanceM8.roundGT
          (QMCLeafB.FuelWire.fuelOfProd k (fun G => T33 G) (fun _ => (1 : ℕ)) a).length
          (QMCLeafB.RStInit.init0 a))) ?_ ?_
  · exact QMCLeafB.LoopRestate.ho_of_loop_bounded (α := QMCLeafB.FuelWire.Pkg)
      QMCLeafB.RStInit.init0 _ QMCLeafB.ConformanceM8.roundGT QMCLeafB.RoundProgram.verdict
      QMCLeafB.RStInit.poly_init0 hfuel QMCLeafB.ConformanceM8.poly_roundGT
      QMCLeafB.RoundProgram.poly_verdict _
      (QMCLeafB.IntegrateM6.orbit_envelope QMCLeafB.ConformanceM8.roundGT
        QMCLeafB.CapGuard.MszG 11448595 6 6 (by norm_num)
        (QMCLeafB.ConformanceM8.ledgerGT_of_ledgerGT
          QMCLeafB.ConformanceM8.ledgerGT_MszG).1
        (QMCLeafB.ConformanceM8.ledgerGT_of_ledgerGT
          QMCLeafB.ConformanceM8.ledgerGT_MszG).2
        QMCLeafB.CapGuard.MszG_le_pow)
  · intro p
    exact QMCLeafB.FinalStroke.hspec_of_tape_free QMCLeafB.RStInit.init0 _
      QMCLeafB.ConformanceM8.roundGT QMCLeafB.RoundProgram.verdict (fun G _ => T33 G)
      QMCLeafB.RStInit.init0_tape hfuelLen p

/-! ## 3.  The top slice of the bracket is a free record

At `t ≥ -Rq/40000` the program's bit is `true` (`htop_roundGT`), and the identity is a unit-diagonal
PSD point with trace `0 ≤ t + Rq/40000`, so the all-`ok` record of `AsmM8.runParts_of_member`
applies.  Nothing is owed there. -/

/-- The identity is a member at any top-slice point. -/
theorem memberAt_top {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hlo : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) :
    AsmM8.MemberAt G t := by
  refine ⟨1, QMCLeafB.AnswerProducer.isUnitDiagPSD_one, ?_⟩
  rw [QMCLeafB.FinishLine.one_trace_eq_zero]
  linarith

/-- **The top slice of the record family is free.** -/
noncomputable def runParts33_top {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hlo : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) (hhi : t ≤ 0) :
    QMCLeafB.FinalStroke.RunParts o33 G t (P33 G) :=
  AsmM8.runParts_of_member (P33 G) hn (P33_K_mul_m G ▸ one_le_T33 G)
    (QMCLeafB.ConformanceM8.htop_roundGT (fun G => T33 G) one_le_T33 G t hlo hhi)
    (memberAt_top hlo)

/-! ## 4.  Soundness on the bracket from the INTERIOR family alone -/

/-- **The one open family.**  The interior record family at the campaign bit — the object phase 33's
lemmas (A) and (B) build.  No condition on the bit, no emptiness, no test coherence. -/
abbrev Hd33 : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    QMCLeafB.FinalStroke.RunParts o33 G t (P33 G)

/-- **`SoundεOnBracket o33` from `Hd33`.**  The top slice is `htop_roundGT` (the bit is `true` and
the identity witnesses), the interior is the family, and `n ≤ 1` is the degenerate bracket. -/
theorem sound33 (hd : Hd33) : QMCLeafB.FinishLine.SoundεOnBracket o33 :=
  QMCLeafB.TopSliceRange.soundEpsOnBracket_of_runData_interior_hn o33
    (fun G t _ hlo hhi =>
      QMCLeafB.ConformanceM8.htop_roundGT (fun G => T33 G) one_le_T33 G t hlo hhi)
    (fun G t hn hlo hlt => (hd G t hn hlo hlt).toRunData)

/-- The same in `SoundAt` form at every bracketed `(G, t)`. -/
theorem soundAt33 (hd : Hd33) (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t) (hhi : t ≤ 0) :
    QMCLeafB.VerdictSound.SoundAt o33 G t :=
  (QMCLeafB.VerdictSound.soundEpsOnBracket_iff o33).1 (sound33 hd) G t hlo hhi


/-! ## 4b.  `Hd33` split by the bit's value — the two slots the record provers fill

`Hd33` is *one* family, but at a fixed `(G, t)` the bit has a value, and the record is built by a
different route on each side.  These two decompositions give the record provers exactly the slots
they own:

* `Hd33_of_classes` — {bit true ⟹ a genuine unit-diagonal PSD point at `t + Rq/40000`} and
  {bit false ⟹ a record}: the first is phase 33's lemma (A) (a relaxed member rounded to a witness),
  the second is lemma (B) (the all-cut record).  Nothing else.
* `Hd33_of_hok_hempty` — the same with the false side in the *banked* shape `EmptyBody` (empty
  relaxation), discharged by `RefutedM3.runParts_of_emptyBody`.  So the thin band's records are the
  only new work, exactly as the phase-33 charter says.
-/

/-- **`Hd33` from the two bit classes.**  The `true` class is any supplier of a primal witness at
`t + Rq/40000` (phase 33's lemma (A) delivers one from a relaxed member); the `false` class is the
all-cut record (phase 33's lemma (B)). -/
noncomputable def Hd33_of_classes
    (hwit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o33 G t = true → AsmM8.MemberAt G t)
    (hfalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o33 G t = false → QMCLeafB.FinalStroke.RunParts o33 G t (P33 G)) :
    Hd33 := by
  intro G t hn hlo hlt
  by_cases hb : o33 G t = true
  · exact AsmM8.runParts_of_member (P33 G) hn (P33_K_mul_m G ▸ one_le_T33 G) hb
      (hwit G t hn hlo hlt hb)
  · refine hfalse G t hn hlo hlt ?_
    cases h : o33 G t with
    | false => rfl
    | true => exact absurd h hb

/-- **`Hd33` with the false side in the banked empty-body shape.**  Only the `true` class (lemma (A))
and the emptiness certificate at false points remain; the records themselves are
`RefutedM3.runParts_of_emptyBody`. -/
noncomputable def Hd33_of_hok_hempty
    (hwit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o33 G t = true → AsmM8.MemberAt G t)
    (hempty : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o33 G t = false → ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) ((P33 G).dq : ℝ) X) :
    Hd33 :=
  Hd33_of_classes hwit
    (fun G t hn hlo hlt hf =>
      QMCLeafB.RefutedM3.runParts_of_emptyBody G t (P33 G) hn hf (hempty G t hn hlo hlt hf))



/-- **A strict-below point IS the witness at `t + Rq/40000`.**  So the `true` class of `Hd33` is free
wherever a unit-diagonal PSD point sits strictly below `t - Rq/40000`: lemma (A)'s rounding is owed
only on the region where no such point exists. -/
theorem memberAt_of_strict_below {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {Z : Matrix (Fin G.n) (Fin G.n) ℝ} (hZ : QMCLeafB.AnswerProducer.IsUnitDiagPSD Z)
    (htr : (QMCLeafB.wMatrix G * Z).trace
      < (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    AsmM8.MemberAt G t := by
  refine ⟨Z, hZ, ?_⟩
  have hε : (0 : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) :=
    QMCLeafB.VerdictSound.eps_nonneg G
  linarith

/-- **`Hd33` FORCES bit-completeness at the strict-below level.**  At a bit-false interior point no
unit-diagonal PSD point can sit strictly below `t - Rq/40000`: such a point carries the campaign ball
into the relaxation (`Boundary.strictBody_ball_relaxBall`), and a nonzero cut with a finite margin
cannot dominate a ball (`BallM2.no_runParts_of_ball`), so no record — hence no family — could exist.

Consequence: the bit may read `false` only where the strict body is empty.  That is phase 32's
`hcomplete` content, and here it is *implied by the family* rather than assumed: (B)'s domain is the
empty-strict-body region, and (A)'s domain is its bit-true part. -/
theorem no_strict_below_of_bit_false (hd : Hd33) {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hn : 2 ≤ G.n) (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hlt : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) (hf : o33 G t = false) :
    ∀ Z : Matrix (Fin G.n) (Fin G.n) ℝ, QMCLeafB.AnswerProducer.IsUnitDiagPSD Z →
      (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (QMCLeafB.wMatrix G * Z).trace := by
  have h0 : (t : ℝ) < 0 := by
    have hε : (0 : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) :=
      QMCLeafB.VerdictSound.eps_nonneg G
    linarith
  have hhi : t ≤ 0 := by exact_mod_cast h0.le
  exact (soundAt33 hd G t hlo hhi).2 hf

/-- **`Hd33` with the true class in the RELAXED-MEMBER shape of phase 33's lemma (A).**  The slot is
verbatim `Check_inst31_m3`'s `hok`: a symmetric rational member of the ball relaxation at
`(t - eps, dqShallow)` at every bit-true interior point.  `Asm2M8.memberAt_of_relaxMem` turns it into
the primal witness (`hcert`), so lemma (A) — "round a relaxed member to a real unit-diagonal PSD
point at `t + eps`" — plus lemma (B) (the all-false record on the false side) is the whole leaf. -/
noncomputable def Hd33_of_relaxMem
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o33 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hfalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o33 G t = false → QMCLeafB.FinalStroke.RunParts o33 G t (P33 G)) :
    Hd33 :=
  Hd33_of_classes
    (fun G t hn hlo hlt hb =>
      Asm2M8.memberAt_of_relaxMem (G := G) (t := t) hn ⟨hlo, hlt⟩ (hok G t hn hlo hlt hb))
    hfalse


/-! ## 4d.  The phase-33 interface itself, in the published cone

`Solutions/Check_sound31.lean` cannot be imported next to the published `Definitions/` bundles, but
its two load-bearing lemmas are *already published* in equivalent form:

* `Sound31.soundAt_of_runParts` IS `VerdictSound.soundAt_of_runData` composed with
  `FinalStroke.RunParts.toRunData` — same content (upper clause `hcert`, lower clause the ball/volume
  contradiction), and it is `soundAt_of_runParts` below;
* hence `Sound31.solution_of_runPartsFamily`, with the family asked only on the strict interior plus
  the free bit-true top slice, is `solution_of_runPartsFamily_bracket` below — at an ARBITRARY bit
  `o` and ARBITRARY parameter family `P`, not just the campaign's.

So a record prover may state its result at any bit it likes, in the submission's own cone.
-/

/-- **`SoundAt` from ONE record, at an arbitrary bit.**  No emptiness, no thin-body analysis. -/
theorem soundAt_of_runParts {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (B : QMCLeafB.FinalStroke.RunParts o G t P) :
    QMCLeafB.VerdictSound.SoundAt o G t :=
  QMCLeafB.VerdictSound.soundAt_of_runData o G t hn B.toRunData

/-- **The phase-33 stroke in the published cone.**  `d9f601e5` from

* a Poly bit `o` and any parameter family `P`;
* the bit reading `true` on the top slice `[-Rq/40000, 0]` (where the identity is a witness);
* one `RunParts` per STRICT-interior point.

No count hypothesis, no ledger, no emptiness, no test coherence. -/
theorem solution_of_runPartsFamily_bracket
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (ho : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 → o G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts o G t (P G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinishLine.solution_of_bracket_verdict o
    (QMCLeafB.TopSliceRange.soundEpsOnBracket_of_runData_interior_hn o htop
      (fun G t hn hlo hlt => (hd G t hn hlo hlt).toRunData))
    ho

/-! ## 5.  The leaf -/

/-- **THE LEAF at the campaign program, from ONE family.**  `d9f601e5` (as
`FinishLine.SolutionStatement`) from `k, hk` (the fuel exponent, `k = 5` works) and `Hd33`.

The Poly bit is proved here (`ho33`); the count side is a theorem (`budgetRounds_le_Kf4`); the top
slice is free (§3).  The record family on the strict interior is the entire remaining obligation. -/
theorem solution33 (k : ℕ) (hk : 21 ≤ 2 ^ k) (hd : Hd33) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinishLine.solution_of_bracket_verdict o33 (sound33 hd) (ho33 k hk)

/-- **The leaf from the two bit classes.** -/
theorem solution33_of_classes (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hwit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o33 G t = true → AsmM8.MemberAt G t)
    (hfalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o33 G t = false → QMCLeafB.FinalStroke.RunParts o33 G t (P33 G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution33 k hk (Hd33_of_classes hwit hfalse)

/-- **The leaf at the concrete fuel exponent `k = 5`.** -/
theorem solution33_five (hd : Hd33) : QMCLeafB.FinishLine.SolutionStatement :=
  solution33 5 (by norm_num) hd

/-- **Cross-check against the banked endgame.**  `ConformanceM8.endgame_leaf_of_hd` is the shelf's
own closure at this exact bit and family; it fires on the same `Hd33`, which certifies that the bit
proved `Poly` in §2 is the bit the shelf runs (no drift between the Poly slot and the record slot). -/
theorem solution33_via_endgame (k : ℕ) (hk : 21 ≤ 2 ^ k) (hd : Hd33) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.ConformanceM8.endgame_leaf_of_hd k hk hd

/-- The same in the platform's own type (the `d9f601e5` sentence, written out). -/
theorem solution33_statement (k : ℕ) (hk : 21 ≤ 2 ^ k) (hd : Hd33) :
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
  QMCLeafB.FinishLine.solutionStatement_iff_wMatrix.1 (solution33 k hk hd)

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.Pbit33.P33_dq
#print axioms QMCLeafB.Pbit33.P33_cAq
#print axioms QMCLeafB.Pbit33.poly_T33
#print axioms QMCLeafB.Pbit33.ho33
#print axioms QMCLeafB.Pbit33.memberAt_top
#print axioms QMCLeafB.Pbit33.runParts33_top
#print axioms QMCLeafB.Pbit33.sound33
#print axioms QMCLeafB.Pbit33.soundAt33
#print axioms QMCLeafB.Pbit33.Hd33_of_classes
#print axioms QMCLeafB.Pbit33.Hd33_of_hok_hempty
#print axioms QMCLeafB.Pbit33.solution33_of_classes
#print axioms QMCLeafB.Pbit33.memberAt_of_strict_below
#print axioms QMCLeafB.Pbit33.no_strict_below_of_bit_false
#print axioms QMCLeafB.Pbit33.Hd33_of_relaxMem
#print axioms QMCLeafB.Pbit33.soundAt_of_runParts
#print axioms QMCLeafB.Pbit33.solution_of_runPartsFamily_bracket
#print axioms QMCLeafB.Pbit33.solution33_five
#print axioms QMCLeafB.Pbit33.solution33
#print axioms QMCLeafB.Pbit33.solution33_via_endgame
#print axioms QMCLeafB.Pbit33.solution33_statement

end QMCLeafB.Pbit33


