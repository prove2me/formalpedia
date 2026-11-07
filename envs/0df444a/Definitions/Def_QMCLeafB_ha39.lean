-- Prove2me | Definitions.Def_QMCLeafB_ha39
-- name    : QMCLeafB_ha39
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:39:31.064675+00:00
-- url     : https://prove2.me/theorems/edfcf184-3f03-4b2b-9b29-03a7ea262ad9
-- title:
--   QMCLeafB ha39
-- statement:
--   # `Check_ha39_m3` — phase 39, member m3, direction d8 (`corpus-harvest`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_ball_m2
import Definitions.Def_QMCLeafB_thinrec34
import Definitions.Def_QMCLeafB_by35
import Definitions.Def_QMCLeafB_anchorfacts
import Definitions.Def_QMCLeafB_parts_m2
import Definitions.Def_QMCLeafB_aud36
import Definitions.Def_QMCLeafB_asm36_m8
import Definitions.Def_QMCLeafB_pinch_m1
import Definitions.Def_QMCLeafB_emptybottom
import Definitions.Def_QMCLeafB_rf38
/-
# `Check_ha39_m3` — phase 39, member m3, direction d8 (`corpus-harvest`)

**Task.** Nothing so far had searched the live corpus for what it *already* decides about
leaf B's last object

    `Rf38M1.SepStream P c hc`  :  forall (G) (t) (hn : 2 <= G.n), forall k < (P G).K * (P G).m,
      forall z in relaxBallP G t (P G),  c_k . Cat_k  <=  c_k . z.

This file is the search's verdict, machine-checked.  Three live bundles carry the whole answer:

* `Def_QMCLeafB_by35`  — `shallowCut_of_separating` : one point of `SepStream` IS a `ShallowCut`.
  `round_zero_separation` : the round-0 point of `SepStream` is provable at EVERY body.
* `Def_QMCLeafB_thinrec34` — `bodyRec_of_shallowCut` : a `ShallowCut` IS the all-false record.
* `Def_QMCLeafB_ball_m2` / `Def_QMCLeafB_aud36` — `no_runParts_of_ball_gen` : a ball inside the
  relaxation whose volume beats the horizon kills EVERY record (any `del`, any normals, any `rho`).

Chaining live lemmas only — no new geometry — gives:

1. **POSITIVE (§1).** `SepStream`'s **round-0 slice is a theorem at every body** (`sep_round_zero`),
   ball-bearing or not.  So the question is decided strictly at rounds `k >= 1`.
2. **SCOPE (§2).** `SepStream` is a statement about **ball-freeness**, not about normals: at any body
   carrying a ball of radius `r > 0` with `volPot A0 * 2^{-K} < r ^ (n*n)` no record exists, hence no
   `ShallowCut`, hence **no `SepStream` for ANY normal stream** (`not_sepStream_of_ball`).  The
   corpus's sliver `(G1,t1)` carries the campaign's own `dq/24` ball (`BallM2.sliver_ball_campaign`),
   so `SepStream paramsKbc2 c hc` is **uninhabited, for every `c`** (`sep_false_paramsKbc2`, an
   independent receipt of d6/m4's refutation, from the banked bundles only).
3. **THE FORCED PROGRAMME CHANGE (§2, criterion form).**  The refutation is a **horizon/radius**
   statement: `SepStream` *forces*, at every body of the family and for every ball the relaxation
   contains, `r ^ (n*n) <= volPot A0 * 2^{-K}`.  No change of `rho`, of the constraint-selection
   rule, of the ledger's `del`, or of the normals can repair it — only `K` (the horizon) or the
   relaxation's ball radius `dq/(8(c_A+1))` can.

**THE HARVEST MAP — banked vs not banked (the deliverable d8 promised).**

MACHINE-CHECKED in the live bundles, no gap, reused verbatim here (no new geometry):
`Bypass35M6.shallowCut_of_separating`, `Bypass35M6.round_zero_separation`,
`Bypass35M6.trace_floor_of_mem`, `Bypass35M6.trF_Cat_succ_traceStream`,
`ThinRec34M4.bodyRec_of_shallowCut`, `ThinRec34M4.not_bodyRec_of_ball`,
`BallM2.runBall`/`sliver_ball`/`sliver_ball_campaign`/`sliver_bit_true`/`sliver_ball_sharp`/
`sliver_hcert_witness`/`residParts_bit_true_of_ball`, `Aud36M6.no_runParts_of_ball_gen`,
`PinchM1.exists_mem_htrc_iff_pinned`/`no_runParts_at_sliver_of_campaign_oklane`/
`not_thirdStratum_campaign`, `ThriceM3.bit_false_at_exemplar`, `PartsM2.ResidParts`,
`FinalZipM7.solution_of_parts`/`solution_of_bit_split`.

NOT BANKED anywhere in the 531-file corpus (searched by type, not name) — the swarm's live residual:
1. separation at the stratum where the record is actually owed (§3 says that stratum is ball-free, so
   §2's mechanism is silent there, but nothing proves separation on it);
2. a gate that reads `true` at every ball-bearing body — the campaign's own pinned-centre ok lane is
   forced `false` at the sliver (§4), and `sliver_hcert_witness` shows only that the `true` reading
   is *reachable* by other data;
3. an inhabitant of `FinalZipM7.PartsData` / `PartsM2.ResidParts` at any gate — §4 shows the
   campaign's own lane does not supply one.

**Where this leaves the leaf.**  `SepStream` is dead as stated; the live residual is the *scoped*
separation of d2/d6 (separation only where a record is actually owed), and the corpus already
contains the scoping device: a record at a ball-bearing body forces its bit TRUE
(`BallM2.no_runParts_of_ball`, hence `BallM2.residParts_bit_true_of_ball`), so the false-bit stratum
— the only stratum on which
`SelfRecG` owes anything — is exactly the ball-free stratum, where the mechanism of §2 is silent.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every theorem, each exactly `[propext, Classical.choice, Quot.sound]`.
Imports are the live `Definitions.*` bundles plus the live `Solutions.Check_rf38_m1` (the definition
of `SepStream` itself); no other member's Check file is loaded.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Ha39M3

open QuantumMaxCutEnergy
open QMCLeafB.EngineIterates

/-! ## 0.  The transport used by §1 and §2: one point of `SepStream` is one record

This is `shallowCut_of_separating` composed with `bodyRec_of_shallowCut`, both live.  It is the hinge
of the whole harvest: `SepStream`'s per-point content is *exactly*
`Bypass35M6.shallowCut_of_separating`'s hypothesis, and its conclusion is `ThinRec34M4.BodyRec`. -/

/-- **One point of `SepStream` is the all-false record at that point.** -/
theorem bodyRec_of_sep {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0)
    (hsep : ∀ k, k < P.K * P.m → ∀ z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P,
      (fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ
          Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.ThinRec34M4.NormalCut G P hn c hc) k
        ≤ (fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ z) :
    QMCLeafB.ThinRec34M4.BodyRec G t P :=
  QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn
    (QMCLeafB.Bypass35M6.shallowCut_of_separating (P := P) hn c hc hsep)

#print axioms QMCLeafB.Ha39M3.bodyRec_of_sep

/-- **`SepStream` is an all-body assertion about records**: it names the record at EVERY `(G,t)` with
`2 ≤ G.n`, with no bit, no bracket and no body condition.  This unscoped `∀` is what §2 refutes. -/
theorem bodyRec_of_sepStream
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : QMCLeafB.Rf38M1.SepStream P c hc)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n) :
    QMCLeafB.ThinRec34M4.BodyRec G t (P G) :=
  bodyRec_of_sep hn (c G t) (hc G t) (hsep G t hn)

#print axioms QMCLeafB.Ha39M3.bodyRec_of_sepStream

/-! ## 1.  POSITIVE: `SepStream`'s round-0 slice is a theorem at EVERY body

`Cat_0 = 0` and the trace normal is nonnegative on the whole relaxation (`trace_floor_of_mem`), so
the round-0 condition holds with the rational, everywhere-nonzero trace stream `traceStream`.  This
is `Bypass35M6.round_zero_separation` read in `SepStream`'s own normal/Cat shape: the object is
NOT empty at round 0, at any body — including the ball-bearing sliver.  So every obstruction lives at
rounds `k ≥ 1`. -/

/-- **The round-0 slice of `SepStream`, at every body.** -/
theorem sep_round_zero {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hdq : P.dq ≤ 4)
    {z : Fin (G.n * G.n) → ℝ} (hz : z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P) :
    (fun i => ((QMCLeafB.Bypass35M6.traceStream G.n 0 i : ℚ) : ℝ)) ⬝ᵥ
        Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (QMCLeafB.ThinRec34M4.NormalCut G P hn (QMCLeafB.Bypass35M6.traceStream G.n)
            (QMCLeafB.Bypass35M6.traceStream_ne_zero (by omega))) 0
      ≤ (fun i => ((QMCLeafB.Bypass35M6.traceStream G.n 0 i : ℚ) : ℝ)) ⬝ᵥ z := by
  have h0 : Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
      (QMCLeafB.ThinRec34M4.NormalCut G P hn (QMCLeafB.Bypass35M6.traceStream G.n)
        (QMCLeafB.Bypass35M6.traceStream_ne_zero (by omega))) 0
      = (0 : Fin (G.n * G.n) → ℝ) := rfl
  rw [h0]
  exact QMCLeafB.Bypass35M6.round_zero_separation (G := G) (t := t) (P := P) hdq hz

#print axioms QMCLeafB.Ha39M3.sep_round_zero

/-! ## 2.  SCOPE: `SepStream` is a ball-freeness statement

`Aud36M6.no_runParts_of_ball_gen`: a Euclidean ball inside `runBall G t P` of radius `r > 0` with
`volPot A0 * 2^{-K} < r ^ (n*n)` kills every record at `(G,t)`.  Contrapositive: ANY record forces
`r ^ (n*n) <= volPot A0 * 2^{-K}` for EVERY ball in the body.  Because `SepStream` produces a record
at every body of the family, it forces that bound at every body — a property of `(K, dq, c_A)`
alone, untouched by the choice of normals, of `rho`, or of `del`. -/

/-- **The record-level radius bound (unconditional, no bit).**  If a record exists at `(G,t,P)` then
every ball inside the relaxation has `r ^ (n*n) <= volPot A0 * 2^{-K}`. -/
theorem record_ball_radius_bound {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (H : QMCLeafB.ThinRec34M4.BodyRec G t P)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} {r : ℝ} (hr : 0 < r)
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀) r
      ⊆ QMCLeafB.BallM2.runBall G t P) :
    r ^ (G.n * G.n)
      ≤ QMCLeafB.EngineIterates.volPot (G.n * G.n)
          (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
            (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K := by
  obtain ⟨B⟩ := H
  by_contra hcon
  exact Bool.false_ne_true
    (QMCLeafB.Aud36M6.no_runParts_of_ball_gen hn hr hball (not_le.1 hcon) B)

#print axioms QMCLeafB.Ha39M3.record_ball_radius_bound

/-- **The criterion form of the refutation.**  One ball-bearing body with the campaign's volume
inequality refutes `SepStream` for EVERY normal stream.  This is the exact statement of what the
programme must change: not the normals, but `K` or the ball radius. -/
theorem not_sepStream_of_ball
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} {r : ℝ} (hr : 0 < r)
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀) r
      ⊆ QMCLeafB.ThinRec34M4.relaxBallP G t (P G))
    (hR : QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * (P G).dq ^ 2)) * (1 / 2) ^ (P G).K < r ^ (G.n * G.n)) :
    ¬ QMCLeafB.Rf38M1.SepStream P c hc := by
  intro hsep
  have hb := record_ball_radius_bound hn (bodyRec_of_sepStream P c hc hsep G t hn) hr hball
  exact absurd hb (not_le.2 hR)

#print axioms QMCLeafB.Ha39M3.not_sepStream_of_ball

/-- **THE REFUTATION AT THE CAMPAIGN FAMILY, harvested from the banked bundles.**
`BallM2.sliver_ball_campaign` puts the campaign's own `dq/24` ball inside `runBall G1 t1 P1`, at
`G1.n = 2`; `BallM2.no_runParts_of_ball` then forbids every record there for every bit.  So no
nonzero rational normal stream separates the accumulated centres from the campaign's own family:
`SepStream` is uninhabited at `paramsKbc2`.  (Independent receipt of d6/m4's refutation: no other
member's Check file is imported; only the live bundles.) -/
theorem sep_false_paramsKbc2
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) :
    ¬ QMCLeafB.Rf38M1.SepStream QMCLeafB.UnionShallow.paramsKbc2 c hc := by
  intro hsep
  have hB : QMCLeafB.ThinRec34M4.BodyRec QMCLeafB.AnchorFactsM2.G₁
      QMCLeafB.AnchorFactsM2.t₁ QMCLeafB.AnchorFactsM2.P₁ :=
    bodyRec_of_sepStream QMCLeafB.UnionShallow.paramsKbc2 c hc hsep
      QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ QMCLeafB.AnchorFactsM2.hn₁
  obtain ⟨B⟩ := hB
  exact Bool.false_ne_true
    (QMCLeafB.BallM2.no_runParts_of_ball QMCLeafB.AnchorFactsM2.hn₁
      QMCLeafB.BallM2.sliver_ball_campaign B)

#print axioms QMCLeafB.Ha39M3.sep_false_paramsKbc2

/-! ## 3.  The scoping device the corpus already owns

The refutation fires at every body that carries a ball whose volume beats the horizon.  The leaf's
`SelfRecG` owes a record only where the campaign bit is `false`.  The corpus pins the two together:
a record at a ball-bearing body forces its bit TRUE (`BallM2.residParts_bit_true_of_ball`), so the
false-bit stratum cannot be a ball-bearing stratum.  Hence the repaired hypothesis — separation at
the points where the record is owed — is never evaluated at a body the refutation of §2 can reach. -/

/-- **On the leaf's residual, a false bit is incompatible with a ball-bearing body.**  So the
false-bit stratum of `ResidParts` is exactly a stratum on which §2's mechanism is silent. -/
theorem false_bit_ball_free {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : QMCLeafB.PartsM2.ResidParts o Pfam)
    {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {t : ℚ}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hbody : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((Pfam G).dq : ℚ) : ℝ) X)
    (hbit : o G t = false)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
      ((Pfam G).dq / (8 * ((Pfam G).cAq + 1))) ⊆ QMCLeafB.BallM2.runBall G t (Pfam G)) :
    False := by
  have htrue := QMCLeafB.BallM2.residParts_bit_true_of_ball H hn hlo hhi hbody hball
  rw [hbit] at htrue
  exact Bool.false_ne_true htrue

#print axioms QMCLeafB.Ha39M3.false_bit_ball_free

/-! ## 4.  The residual itself, harvested: at the sliver the leaf's own record is forced `true`

§3 scopes the repair.  This section records what the corpus already decides about the leaf's **live
residual** `PartsM2.ResidParts` (the interface `FinalZipM7.solution_of_parts` consumes) at the
campaign's own gate:

* `residual_bit_true_at_sliver` : `ResidParts` forces the bit `true` at `(G₁,t₁)`, for EVERY bit `o`
  (the pointwise form of `BallM2.campaign_bit_true_at_sliver`, which is stated only for
  `Audit2M5.campaignBit`).
* `residual_refuted_of_oklane` : with the campaign's pinned-centre ok-lane data at the sliver
  (`ThriceM3.bit_false_at_exemplar`'s hypotheses; `PinchM1.exists_mem_htrc_iff_pinned` is what makes
  a trace-tight ok-lane witness pinned, hence supplies `hdia`), the bit there is forced `false` — so
  `ResidParts` itself is refuted.  The leaf's residual is then
  inconsistent with the campaign's gate, and no separation hypothesis can rescue it.

So both live routes (phase-38's `SepStream` and phase-36's bit-split `ResidParts`) die at the SAME
point, for the SAME reason: a record at `(G₁,t₁)` must read `true`, and the campaign's ok lane reads
`false`.  The programme change that fixes both is one change: release the pinning at the sliver so
that the gate's `anyOk` can read `true` there — `BallM2.sliver_hcert_witness` exhibits the ok-round
certificate `!![1,-1;-1,1]` showing that reading is reachable. -/

/-- **`ResidParts` forces the campaign bit `true` at the sliver** — for every bit. -/
theorem residual_bit_true_at_sliver {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (H : QMCLeafB.PartsM2.ResidParts o QMCLeafB.UnionShallow.paramsKbc2) :
    o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ = true := by
  exact QMCLeafB.BallM2.residParts_bit_true_of_ball
    (X₀ := QMCLeafB.BallM2.Xs) (Pfam := QMCLeafB.UnionShallow.paramsKbc2) H
    QMCLeafB.AnchorFactsM2.hn₁
    QMCLeafB.EmptyBodyM5.t₁_mem_bracket.1 QMCLeafB.EmptyBodyM5.t₁_mem_bracket.2
    QMCLeafB.AnchorFactsM2.realBody_G₁ QMCLeafB.BallM2.sliver_ball_campaign

#print axioms QMCLeafB.Ha39M3.residual_bit_true_at_sliver

/-- **The leaf's live residual is REFUTED by the campaign's own ok-lane data.**  With the pinned
centres `cX` and the ok-lane membership at the sliver, `ThriceM3.bit_false_at_exemplar` forces the bit
`false`, while any record forces it `true`; `PartsM2.ResidParts` demands the record.  So the residual
`FinalZipM7.solution_of_parts` consumes is uninhabited at `paramsKbc2` for that gate. -/
theorem residual_refuted_of_oklane (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (rb : ℕ → Bool) (cX : ℕ → Matrix (Fin 2) (Fin 2) ℚ)
    (hbit : o QMCLeafB.EmptyBodyM5.G₁ QMCLeafB.AnchorFactsM2.t₁
      = QMCLeafB.SimLoop.anyOk rb
        (QMCLeafB.AnchorFactsM2.P₁.K * QMCLeafB.AnchorFactsM2.P₁.m))
    (hok : ∀ k, rb k = true →
      QMCLeafB.RelaxOracle.RelaxMem
        (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁) (cX k)
        (QMCLeafB.AnchorFactsM2.t₁ - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁)
        QMCLeafB.AnchorFactsM2.P₁.dq)
    (hdia : ∀ (k : ℕ) (i : Fin 2), cX k i i = 1 - QMCLeafB.AnchorFactsM2.P₁.dq / 4) :
    QMCLeafB.PartsM2.ResidParts o QMCLeafB.UnionShallow.paramsKbc2 → False := by
  intro H
  exact QMCLeafB.PinchM1.no_runParts_at_sliver_of_campaign_oklane o rb cX hbit hok hdia
    ⟨H QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ QMCLeafB.AnchorFactsM2.hn₁
      QMCLeafB.EmptyBodyM5.t₁_mem_bracket.1 QMCLeafB.EmptyBodyM5.t₁_mem_bracket.2
      QMCLeafB.AnchorFactsM2.realBody_G₁⟩

#print axioms QMCLeafB.Ha39M3.residual_refuted_of_oklane

end QMCLeafB.Ha39M3


