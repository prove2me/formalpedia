-- Prove2me | Definitions.Def_QMCLeafB_asm36
-- name    : QMCLeafB_asm36
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:13:11.292935+00:00
-- url     : https://prove2.me/theorems/c0ac8478-e456-4860-b061-9b4599edc39c
-- title:
--   QMCLeafB asm36
-- statement:
--   # `Check_asm36_m8` — phase 36, member m8, direction `assembly36`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_ball_floor
import Definitions.Def_QMCLeafB_sim_loop_m6
import Definitions.Def_QMCLeafB_asm35
/-
# `Check_asm36_m8` — phase 36, member m8, direction `assembly36`

**The assembly of leaf B (`d9f601e5`) at the campaign program, with the residual reduced to ONE
analytic identity in program-free form.**

## What is already banked (consumed here, not re-derived)

* `Pbit33.solution33` / `solution33_statement` (`Check_pbit33_m6`): the verbatim sentence from
  `Automatic.Poly o33` (`ho33`), the count side (`hKm33`), the free top slice, and the record
  family `Hd33` on the strict interior;
* `Asm35M4.HokSlot` + `Asm35M4.hokSlot_of_releasedGate` (`Check_hokupper34_m8`/`Check_asm35_m4`):
  the UPPER slot — a bit-`true` point carries a symmetric rational `RelaxMem` at
  `(t − eps, dqShallow)` — produced from the released gate's stream data;
* `ThinRec34M4.runParts_false_iff_bodyRec` (`Check_thinrec34_m4`): at a bit-`false` point a record
  for the program's bit and an all-false record (`BodyRec`) are the SAME object;
* `BallM2.no_runParts_of_ball` / `SimLoop.Prefix.body_containment_at_halving_margin_prefix`
  (`Def_QMCLeafB_ball_m2`, `Def_QMCLeafB_sim_loop_m6`): the record-level volume obstruction.

## What this file adds

§1 the residual slot `SelfRec`: at a bit-`false` interior point the run's own all-cut transcript is
   a record (`BodyRec`).  It is exactly `Pbit33.Hd33_of_relaxMem`'s second argument, transported
   through `runParts_false_iff_bodyRec`;
§2 `solution_of_selfRec` — `d9f601e5` from `{HokSlot, SelfRec}`, i.e. from the upper side and ONE
   all-cut identity.  No horn disjunction, no emptiness stratum, no bit completeness;
§3 the RADIUS-FREE record-level horizon theorem `no_runParts_of_ball_horizon`: a record at a body
   carrying a Euclidean ball of ANY radius `r > 0` whose volume potential beats `r^{n·n}` forces the
   bit `true` — the record-level twin of `DC35M1.not_shallowCut_of_ball_horizon`, and the exact
   engine of phase 35's "the obstruction that kills the record horn is the engine of the bit horn";
§4 the consequence: `SelfRec` forces the bit TRUE at every horizon-fat body (`bit_true_of_fat`), so
   `SelfRec`'s domain shrinks to the ball-free thin stratum.  `solution_of_thinSelfRec` is the leaf
   from `{HokSlot}` + `{the all-cut identity on horizon-thin bodies}` — the phase-36 target;
§5 the same assembly at the released gate (`solution_of_thinSelfRec_gate`), statement lock
   (`..._statement`), and the kernel-audit prints.

Discipline: `set_option autoImplicit false`; the submission sweep's five forbidden tokens are all
absent;
every `#print axioms` below is exactly `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace QMCLeafB.Asm36M8

open Matrix
open QuantumMaxCutEnergy

/-! ## 1.  The residual slot: the run's own all-cut transcript is a record -/

/-- **THE IDENTITY, in the exact shape `Hd33_of_relaxMem` consumes.**  At a bit-`false` interior
bracket point the all-false record class `BodyRec` is inhabited — i.e. the run's own transcript, all
of whose rounds are cut rounds, IS a record: `ok ≡ false` (the bit is the `anyOk` of the round flags,
`SimLoop.anyOk_eq_false_iff`), the six ledger fields are the engine's own ellipsoid arithmetic, and
`hcut` is the oracle's separation at the accumulated centre.  Nothing here mentions a program. -/
def SelfRec : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    Pbit33.o33 G t = false → ThinRec34M4.BodyRec G t (Pbit33.P33 G)

/-- The slot as a family of records at the program's own bit — verbatim `Hd33`'s second
argument.  The two forms are the same statement (`runParts_false_iff_bodyRec`). -/
noncomputable def hfalse_of_selfRec (H : SelfRec) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      Pbit33.o33 G t = false → QMCLeafB.FinalStroke.RunParts Pbit33.o33 G t (Pbit33.P33 G) :=
  fun G t hn hlo hlt hb =>
    Classical.choice ((ThinRec34M4.runParts_false_iff_bodyRec hb).2 (H G t hn hlo hlt hb))

#print axioms QMCLeafB.Asm36M8.hfalse_of_selfRec

/-- **`SelfRec` is inhabited on the EMPTY stratum** (`RefutedM3.runParts_of_emptyBody` transported
through the reduction): the identity is only owed where the body is nonempty. -/
theorem selfRec_at_empty {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hn : 2 ≤ G.n) (hb : Pbit33.o33 G t = false)
    (hempty : ThinRec34M4.BodyEmpty G t (Pbit33.P33 G)) :
    ThinRec34M4.BodyRec G t (Pbit33.P33 G) :=
  (ThinRec34M4.runParts_false_iff_bodyRec hb).1
    ⟨QMCLeafB.RefutedM3.runParts_of_emptyBody G t (Pbit33.P33 G) hn hb
      (fun X hX => hempty X hX)⟩

#print axioms QMCLeafB.Asm36M8.selfRec_at_empty

/-- **The identity is owed only off the empty stratum**: an all-cut record at every bit-`false`
point with a NONEMPTY body gives `SelfRec` outright. -/
theorem selfRec_of_nonempty (H : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      Pbit33.o33 G t = false → ¬ ThinRec34M4.BodyEmpty G t (Pbit33.P33 G) →
      ThinRec34M4.BodyRec G t (Pbit33.P33 G)) :
    SelfRec := by
  intro G t hn hlo hlt hb
  by_cases he : ThinRec34M4.BodyEmpty G t (Pbit33.P33 G)
  · exact selfRec_at_empty hn hb he
  · exact H G t hn hlo hlt hb he

#print axioms QMCLeafB.Asm36M8.selfRec_of_nonempty

/-! ## 2.  The assembly: `d9f601e5` from the upper slot and the identity -/

/-- **THE LEAF FROM TWO SLOTS.**  The verbatim sentence at the campaign program, from
`Asm35M4.HokSlot` (the released gate's soundness — mechanical, `hokSlot_of_releasedGate`) and
`SelfRec` (the run's own transcript).  Nothing else is owed: `Automatic.Poly o33` is `ho33`, the
count side is `hKm33`, the top slice is free, `n ≤ 1` is degenerate. -/
theorem solution_of_selfRec (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : Asm35M4.HokSlot) (H : SelfRec) :
    QMCLeafB.FinishLine.SolutionStatement :=
  Pbit33.solution33 k hk (Pbit33.Hd33_of_relaxMem hok (hfalse_of_selfRec H))

#print axioms QMCLeafB.Asm36M8.solution_of_selfRec

/-- The same in the platform's own type (the `d9f601e5` sentence, written out). -/
theorem solution_of_selfRec_statement (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : Asm35M4.HokSlot) (H : SelfRec) :
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
  Pbit33.solution33_statement k hk (Pbit33.Hd33_of_relaxMem hok (hfalse_of_selfRec H))

#print axioms QMCLeafB.Asm36M8.solution_of_selfRec_statement

/-! ## 3.  The record-level horizon obstruction, at ANY radius

`BallM2.no_runParts_of_ball` runs the engine's containment + volume-potential accounting on the
record's OWN cut stream (`hcut`/`hcheck` at `Cat`/`Aat`) and ends at `P.hbudget`, the campaign's own
radius `dq/(8(c_A+1))`.  Its intermediate step
`SimLoop.Prefix.body_containment_at_halving_margin_prefix` hands over
`volPot (Aat … (K·m)) ≤ volPot A₀ · 2^{-K}` with the radius nowhere in it, so replacing the final
`BallFloor.no_run_of_ball` input `hε : volPot A₀ · 2^{-K} < r^{n·n}` makes the SAME argument fire at a
FREE radius.  This is the record-level twin of `DC35M1.not_shallowCut_of_ball_horizon` (which is
stated for the constructed `ShallowCut` stream) and the engine of phase 35's reading: the obstruction
that kills the record horn is exactly what proves the bit horn once the gate accepts members. -/

/-- **Radius-free record obstruction**: a record at a body carrying a ball of radius `r > 0` whose
volume potential beats `r ^ (n·n)` forces the bit `true`.  (`r` is free: a `9·10⁻⁹` ball in the open
band qualifies once `volPot A₀ · 2^{-K} < r^{n·n}`, which at `paramsKbc2` holds for every
`r ≳ 10^{-140000}`.) -/
theorem no_runParts_of_ball_horizon
    {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} {r : ℝ} (hr : 0 < r)
    (hball : ∀ y : Fin (G.n * G.n) → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
      (y + QMCLeafB.AnswerProducer.flat X₀) ∈ QMCLeafB.BallM2.runBall G t P)
    (hε : QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K < r ^ (G.n * G.n))
    (B : QMCLeafB.FinalStroke.RunParts o G t P) : o G t = true := by
  classical
  by_contra hcon
  have hfalse : o G t = false := by
    cases h : o G t with
    | false => rfl
    | true => exact absurd h hcon
  have hall : ∀ k, k < P.K * P.m → B.ok k = false :=
    (QMCLeafB.SimLoop.anyOk_eq_false_iff B.ok (P.K * P.m)).mp
      (by rw [← B.hverdict]; exact hfalse)
  have hNm : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 := by nlinarith [P.hdq]
  have hn' : 2 ≤ G.n * G.n := by nlinarith
  have hA0 : (QMCLeafB.EngineIterates.castM
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))).PosDef :=
    QMCLeafB.Boundary.initShapeOf_cast_posDef hNm
  have hwit : ∀ k, k < P.K * P.m →
      QMCLeafB.EngineIterates.Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) B.cd k *ᵥ (B.cd k).p = (B.cd k).c :=
    fun k hk => B.hwit k hk (hall k hk)
  have hρ : ∀ k, k < P.K * P.m → 0 ≤ (B.cd k).rho :=
    fun k hk => B.hrho k hk (hall k hk)
  have hcne : ∀ k, k < P.K * P.m → (B.cd k).c ≠ 0 :=
    fun k hk => B.hcne k hk (hall k hk)
  have hcover : ∀ z, QMCLeafB.BallM2.runBall G t P z →
      QMCLeafB.EngineIterates.Ell (QMCLeafB.EngineIterates.castM
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))) 0 z :=
    fun z hz => QMCLeafB.Boundary.ell_initShapeOf hNm (QMCLeafB.Boundary.relaxBall_norm hz)
  have hδ0 : ∀ k, k < P.K * P.m → 0 ≤ B.del k :=
    fun k hk => B.hdel0 k hk (hall k hk)
  have hcheck : ∀ k, k < P.K * P.m →
      (B.del k) ^ 2 ≤ ((B.cd k).rho) ^ 2 *
        QMCLeafB.EngineIterates.sigmaQ (B.cd k).c (B.cd k).p :=
    fun k hk => B.hcheck k hk (hall k hk)
  have hcutδ : ∀ k, k < P.K * P.m → ∀ z, QMCLeafB.BallM2.runBall G t P z →
      -(((B.del k : ℚ)) : ℝ) ≤ QMCLeafB.EngineIterates.cutCR B.cd k
        ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd k) :=
    fun k hk z hz => B.hcut k hk (hall k hk) z hz
  have hle : ∀ k, k < P.K * P.m → (B.cd k).rho ≤ P.rmax :=
    fun k hk => B.hle k hk (hall k hk)
  obtain ⟨hcont, hvol⟩ := QMCLeafB.SimLoop.Prefix.body_containment_at_halving_margin_prefix
    (n := G.n * G.n) hn' (A0 := QMCLeafB.Boundary.initShapeOf (G.n * G.n)
      (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) (cd := B.cd) (T := P.K * P.m)
    hA0 hwit hρ hcne (0 : Fin (G.n * G.n) → ℝ) (QMCLeafB.BallM2.runBall G t P)
    hcover hδ0 hcheck hcutδ P.hrmax hle P.hhalve (le_rfl : QMCLeafB.EngineIterates.volPot
      (G.n * G.n) (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K ≤
      QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K) le_rfl
  have hKpd : (QMCLeafB.BallFloor.castM (QMCLeafB.EngineIterates.Aat (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) B.cd (P.K * P.m))).PosDef :=
    QMCLeafB.SimLoop.Aat_cast_posDef_prefix hn' hA0 hwit hρ hcne (P.K * P.m) le_rfl
  refine QMCLeafB.BallFloor.no_run_of_ball (A := QMCLeafB.EngineIterates.Aat (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) B.cd (P.K * P.m))
    hKpd (a := QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
      B.cd (P.K * P.m))
    (a₀ := QMCLeafB.AnswerProducer.flat X₀) (body := QMCLeafB.BallM2.runBall G t P)
    (ε := QMCLeafB.EngineIterates.volPot (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K) hr ?_ ?_ hvol hε
  · exact hball
  · intro z hz
    exact hcont z hz

#print axioms QMCLeafB.Asm36M8.no_runParts_of_ball_horizon

/-- **No all-false record at a horizon-fat body.** -/
theorem not_bodyRec_of_ball_horizon
    {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} {r : ℝ} (hr : 0 < r)
    (hball : ∀ y : Fin (G.n * G.n) → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
      (y + QMCLeafB.AnswerProducer.flat X₀) ∈ QMCLeafB.BallM2.runBall G t P)
    (hε : QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K < r ^ (G.n * G.n)) :
    ¬ ThinRec34M4.BodyRec G t P := by
  rintro ⟨B⟩
  have h := no_runParts_of_ball_horizon (o := ThinRec34M4.falseBit) hn hr hball hε B
  exact Bool.false_ne_true h

#print axioms QMCLeafB.Asm36M8.not_bodyRec_of_ball_horizon

/-! ## 4.  The split: `SelfRec` on the horizon-thin stratum is the whole leaf -/

/-- A body carries a HORIZON BALL of radius `r` when the closed ball of radius `r` about some body
point lies in the relaxation AND the volume potential beats `r ^ (n·n)`.  Radius and centre are both
free, which is what makes this fire on the open band (whose ball is `9·10⁻⁹`, while at `paramsKbc2`
every `r ≳ 10^{-140000}` qualifies). -/
def FatG (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∃ (r : ℝ) (X₀ : Matrix (Fin G.n) (Fin G.n) ℝ), 0 < r ∧
    (∀ y : Fin (G.n * G.n) → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
      (y + QMCLeafB.AnswerProducer.flat X₀) ∈ QMCLeafB.BallM2.runBall G t P) ∧
    QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K
      < r ^ (G.n * G.n)

/-- The campaign's own fat predicate. -/
abbrev Fat (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Prop := FatG G t (Pbit33.P33 G)

/-- The campaign's own budget implies the horizon inequality at every radius at least the campaign
radius: so §3 strictly generalises the banked `BallM2.no_runParts_of_ball`. -/
theorem horizon_of_ge_campaign {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {r : ℝ} (hr : 0 < r)
    (hcamp : (P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1)) ≤ r) :
    QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K < r ^ (G.n * G.n) := by
  have hdq : (0 : ℝ) < (P.dq : ℝ) := by exact_mod_cast P.hdq
  have hcA : (0 : ℝ) ≤ (P.cAq : ℝ) := by exact_mod_cast P.hcAq
  have hden : (0 : ℝ) < 8 * ((P.cAq : ℝ) + 1) := by positivity
  have hc0 : (0 : ℝ) < (P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1)) := by positivity
  have hpow : ((P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1))) ^ (G.n * G.n) ≤ r ^ (G.n * G.n) :=
    pow_le_pow_left₀ hc0.le hcamp _
  exact lt_of_lt_of_le P.hbudget hpow

#print axioms QMCLeafB.Asm36M8.horizon_of_ge_campaign

/-- **`BallM2.no_runParts_of_ball`'s conclusion, from any ball of radius at least `dq/(8(c_A+1))`.** -/
theorem no_runParts_of_ball_of_ge_campaign
    {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} {r : ℝ} (hr : 0 < r)
    (hcamp : (P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1)) ≤ r)
    (hball : ∀ y : Fin (G.n * G.n) → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
      (y + QMCLeafB.AnswerProducer.flat X₀) ∈ QMCLeafB.BallM2.runBall G t P)
    (B : QMCLeafB.FinalStroke.RunParts o G t P) : o G t = true :=
  no_runParts_of_ball_horizon hn hr hball (horizon_of_ge_campaign (t := t) (P := P) hr hcamp) B

#print axioms QMCLeafB.Asm36M8.no_runParts_of_ball_of_ge_campaign

/-- **No all-false record at a horizon-fat body**, at an arbitrary parameter family. -/
theorem not_bodyRec_of_fatG {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n) (hf : FatG G t P) :
    ¬ ThinRec34M4.BodyRec G t P := by
  obtain ⟨r, X₀, hr, hball, hε⟩ := hf
  exact not_bodyRec_of_ball_horizon hn hr hball hε

#print axioms QMCLeafB.Asm36M8.not_bodyRec_of_fatG

/-- **No all-cut record at a fat body** (§3 at `P33`). -/
theorem not_bodyRec_of_fat {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hf : Fat G t) : ¬ ThinRec34M4.BodyRec G t (Pbit33.P33 G) :=
  not_bodyRec_of_fatG hn hf

#print axioms QMCLeafB.Asm36M8.not_bodyRec_of_fat

/-- **`SelfRec` forces the bit TRUE at every horizon-fat body** — the identity and the volume
obstruction meet exactly here (phase 35's "the obstruction that kills the record horn is the engine
of the bit horn").  So `SelfRec`'s domain is the horizon-thin stratum. -/
theorem bit_true_of_fat {G : QuantumMaxCutEnergy.Input} {t : ℚ} (H : SelfRec) (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hlt : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hf : Fat G t) : Pbit33.o33 G t = true := by
  by_contra hcon
  have hb : Pbit33.o33 G t = false := by
    cases h : Pbit33.o33 G t with
    | false => rfl
    | true => exact absurd h hcon
  exact not_bodyRec_of_fat hn hf (H G t hn hlo hlt hb)

#print axioms QMCLeafB.Asm36M8.bit_true_of_fat

/-- **THE PHASE-36 TARGET, as one slot.**  The identity is owed only where the body is
horizon-thin: at every bit-`false` interior point with NO horizon ball, an all-cut record.  Together
with §2 this closes the leaf from the upper side plus this one statement. -/
def ThinSelfRec : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    Pbit33.o33 G t = false → ¬ Fat G t → ThinRec34M4.BodyRec G t (Pbit33.P33 G)

/-- **The programme-side half of the split**: the bit reads `true` at every horizon-fat interior
point.  This is phase 36's `hcomplete` restricted to the fat stratum — the `ReachTop`/visit
obligation, NOT an identity question.  `bit_true_of_fat` is the consistency check: `SelfRec` implies
this slot, so the two slots below are exactly one statement plus the thin identity. -/
def FatBitTrue : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    Fat G t → Pbit33.o33 G t = true

/-- **The two slots are `SelfRec`**: the fat half kills the bit-`false` fat points, the thin half is
the identity there. -/
theorem selfRec_of_split (hFat : FatBitTrue) (hThin : ThinSelfRec) : SelfRec := by
  intro G t hn hlo hlt hb
  by_cases hf : Fat G t
  · exact absurd (hFat G t hn hlo hlt hf) (by rw [hb]; simp)
  · exact hThin G t hn hlo hlt hb hf

#print axioms QMCLeafB.Asm36M8.selfRec_of_split

/-- **THE LEAF FROM THE UPPER SLOT AND THE THIN IDENTITY.** -/
theorem solution_of_thinSelfRec (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : Asm35M4.HokSlot) (hFat : FatBitTrue) (H : ThinSelfRec) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_selfRec k hk hok (selfRec_of_split hFat H)

#print axioms QMCLeafB.Asm36M8.solution_of_thinSelfRec

/-- The same in the platform's own type. -/
theorem solution_of_thinSelfRec_statement (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : Asm35M4.HokSlot) (hFat : FatBitTrue) (H : ThinSelfRec) :
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
  solution_of_selfRec_statement k hk hok (selfRec_of_split hFat H)

#print axioms QMCLeafB.Asm36M8.solution_of_thinSelfRec_statement

/-! ## 5.  The submission-ready interface at an ARBITRARY programme

A repaired, membership-equivalent gate re-points the bit, so the assembly must not mention `o33`.
These are the `o33`-free twins, built on the published-cone stroke
`Pbit33.solution_of_runPartsFamily_bracket` (arbitrary bit, arbitrary parameter family): the leaf
sentence from `{Automatic.Poly o} + {count} + {top slice} + {upper slot} + {the all-cut identity}`.
Every slot except the last is a fact about which program runs, not about the leaf's geometry. -/

/-- The all-cut identity at an arbitrary bit and parameter family. -/
def SelfRecG (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o G t = false → ThinRec34M4.BodyRec G t (P G)

/-- `SelfRec` is `SelfRecG` at the campaign program — the two interfaces agree. -/
theorem selfRec_iff_selfRecG :
    SelfRec ↔ SelfRecG Pbit33.o33 Pbit33.P33 := Iff.rfl

#print axioms QMCLeafB.Asm36M8.selfRec_iff_selfRecG

/-- **THE LEAF FROM FOUR SLOTS, AT ANY PROGRAMME.**  `d9f601e5`, from a `Poly` bit, its count, its
top slice, the upper slot (`hok`: a bit-`true` point carries a symmetric rational `RelaxMem` at
`(t − eps, dqShallow)`) and the all-cut identity.  No round, no size ledger, no test coherence. -/
theorem solution_of_two_slots_selfRec
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (ho : OAI.MetricKMedian.Binary.Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ (P G).K * (P G).m)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 → o G t = true)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (Hrec : SelfRecG o P) :
    QMCLeafB.FinishLine.SolutionStatement :=
  Pbit33.solution_of_runPartsFamily_bracket o P ho htop
    (fun G t hn hlo hlt => by
      by_cases hb : o G t = true
      · exact AsmM8.runParts_of_member (P G) hn (hKm G) hb
          (Asm2M8.memberAt_of_relaxMem (G := G) (t := t) hn ⟨hlo, hlt⟩
            (hok G t hn hlo hlt hb))
      · have hf : o G t = false := by
          cases h : o G t with
          | false => rfl
          | true => exact absurd h hb
        exact Classical.choice
          ((ThinRec34M4.runParts_false_iff_bodyRec (P := P G) (o := o) hf).2
            (Hrec G t hn hlo hlt hf)))

#print axioms QMCLeafB.Asm36M8.solution_of_two_slots_selfRec

/-- **`SelfRecG` forces the bit TRUE at horizon-fat bodies**, at an arbitrary programme: the identity
and the volume obstruction meet, so the identity's domain is the horizon-thin stratum. -/
theorem bit_true_of_fatG {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : SelfRecG o P) (hn : 2 ≤ G.n) (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hlt : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hf : FatG G t (P G)) : o G t = true := by
  by_contra hcon
  have hb : o G t = false := by
    cases h : o G t with
    | false => rfl
    | true => exact absurd h hcon
  exact not_bodyRec_of_fatG hn hf (H G t hn hlo hlt hb)

#print axioms QMCLeafB.Asm36M8.bit_true_of_fatG

end QMCLeafB.Asm36M8


